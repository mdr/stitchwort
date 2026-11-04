//! The journal: the undo logs of a session's [`Logged`] tables, and the
//! checkpoints they can be put back to (docs/proposals/elaborator-state.md
//! §4.8.2).
//!
//! Each [`Logged`] table keeps its own log, typed by its rows; the
//! [`Journal`] knows only positions in them, as one value of the type `P`
//! that the tables, taken together, give ([`Logs`]). It holds a stack of
//! open checkpoints of two kinds:
//!
//! - a [`Checkpoint`] is retained: it can be rewound to any number of
//!   times, and stays open until it is released, or until a rewind to an
//!   older one drops it;
//! - a [`Transaction`] is short-lived and must be ended, by
//!   [`Journal::commit`] (its changes stay, and belong to whatever is still
//!   open) or [`Journal::abort`] (they are undone).
//!
//! A handle names its place in the stack and the serial it was given, never
//! reused, so a handle that a rewind to an older checkpoint dropped is
//! found out in O(1) and its use panics, rather than putting the tables in
//! a state no checkpoint had. A [`Transaction`] dropped without being ended
//! fails a debug assertion.
//!
//! The tables log only while something is open, and when the stack empties
//! their logs are dropped: the first checkpoint is always taken with empty
//! logs, so the logs hold exactly what the oldest open checkpoint needs.
//!
//! Which changes are logged: a write logs a key's old value the first time
//! the key is written in a *generation*, which every checkpoint, transaction
//! and rewind starts anew. A row records the generation it was last logged
//! in, so finding out costs a comparison and a mark costs O(number of
//! tables), whatever the size of the tables. (A set of the keys written
//! since the last mark costs O(its capacity) to clear: §4.8.1.) A write to
//! a key with no row always logs, which logs a removal and a re-insertion
//! twice in one generation: harmless, as the older entry is undone last.
//!
//! One journal per session, with one writer: nothing in it is shared
//! (§4.9).
//!
//! **Segments by unit** (§4.8.3). While something is open, the journal
//! notes where the logs were each time the unit being elaborated changes
//! ([`Journal::set_unit`]: a project namespace or a file begins, a nested
//! load enters or leaves) and at each checkpoint and transaction, with the
//! unit then current, and starts a new generation there, so that each
//! segment logs every key it writes. A unit's write-set since a
//! transaction began is what its own segments logged
//! ([`Journal::segments_since`], [`Logged::changed_in`]): a check cache
//! entry is made from it, and a library file loaded in the middle of a
//! namespace is in its own write-set, not the namespace's.
//!
//! Step 6a of the note's migration (§7) built this and put navigation's
//! maps on it; 6b put the scope's, the instances, the helpers' keys and
//! the session's maps on it, and releases a language server's marks; 6c
//! made the check cache's entries from write-sets.

use std::hash::Hash;

use stitchwort_core::collections::{HashMap, HashSet};

use super::owners::UnitId;

/// A generation of the journal: a row whose key has been logged in the
/// current one isn't logged again. 0 is never current.
type Generation = u32;

/// The tables a journal's checkpoints cover, taken together: what the
/// [`Journal`] asks of them. Built by naming every [`Logged`] table, so a
/// new one isn't left out.
pub(crate) trait Logs {
    /// Where each table's log is.
    type Positions;
    fn positions(&self) -> Self::Positions;
    /// Undoes every change logged since `at`, newest first; gives how many
    /// log entries that undid.
    fn undo_to(&mut self, at: &Self::Positions) -> usize;
    /// Logging from now on in generation `g`; with `None`, not logging, and
    /// every log emptied.
    fn set_generation(&mut self, g: Option<Generation>);
    /// How many entries the logs hold.
    fn entries(&self) -> usize;
    /// How many bytes the logs hold (their entries' own size, not what
    /// the keys and values point to).
    fn bytes(&self) -> usize;
    /// How many keys the logs hold an entry for.
    fn distinct_keys(&self) -> usize;
}

/// A map whose changes can be undone back to a checkpoint of the session's
/// [`Journal`], without a copy of it: what each change replaced is logged.
/// Reads go through to the map itself.
///
/// Every write goes through its methods (§4.8.5): nothing gives out a
/// `&mut V`. A row type mustn't have interior mutability (no `Cell`,
/// `RefCell` or `Rc<RefCell<_>>` in it), or a shared reference could change
/// a row without the log knowing.
#[derive(Clone)]
pub(crate) struct Logged<K, V> {
    /// Each row, with the generation its key was last logged in.
    map: HashMap<K, (V, Generation)>,
    /// Each change logged, oldest first: its key, and the value it
    /// replaced (`None`: there was none).
    undo: Vec<(K, Option<V>)>,
    /// The journal's generation while something is open; `None` while
    /// nothing is, when nothing is logged.
    generation: Option<Generation>,
}

impl<K, V> Default for Logged<K, V> {
    fn default() -> Self {
        Logged {
            map: HashMap::default(),
            undo: Vec::new(),
            generation: None,
        }
    }
}

impl<K: Hash + Eq + Clone, V> Logged<K, V> {
    /// Sets `key`'s row to `value`.
    pub(crate) fn insert(&mut self, key: K, value: V) {
        let Some(g) = self.generation else {
            self.map.insert(key, (value, 0));
            return;
        };
        match self.map.get_mut(&key) {
            Some(row) => {
                let (old, stamp) = std::mem::replace(row, (value, g));
                if stamp != g {
                    self.undo.push((key, Some(old)));
                }
            }
            None => {
                self.map.insert(key.clone(), (value, g));
                self.undo.push((key, None));
            }
        }
    }

    /// Inserts `value` unless `key` has one already.
    pub(crate) fn insert_absent(&mut self, key: K, value: V) {
        if !self.map.contains_key(&key) {
            self.insert(key, value);
        }
    }

    /// Keeps only the rows `keep` picks, logging the others' removal.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&K, &V) -> bool) {
        if self.generation.is_none() {
            self.map.retain(|k, (v, _)| keep(k, v));
            return;
        }
        let gone: Vec<K> = (self.map.iter())
            .filter(|(k, (v, _))| !keep(k, v))
            .map(|(k, _)| k.clone())
            .collect();
        for k in &gone {
            self.remove(k);
        }
    }

    /// Removes `key`'s row; whether there was one.
    pub(crate) fn remove<Q>(&mut self, key: &Q) -> bool
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let Some((key, (old, stamp))) = self.map.remove_entry(key) else {
            return false;
        };
        if let Some(g) = self.generation
            && stamp != g
        {
            self.undo.push((key, Some(old)));
        }
        true
    }

    pub(crate) fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(key).map(|(v, _)| v)
    }

    /// The key as stored, with its row.
    pub(crate) fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get_key_value(key).map(|(k, (v, _))| (k, v))
    }

    pub(crate) fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.contains_key(key)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub(crate) fn keys(&self) -> impl Iterator<Item = &K> {
        self.map.keys()
    }

    /// The rows, in no particular order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.map.iter().map(|(k, (v, _))| (k, v))
    }

    pub(crate) fn values(&self) -> impl Iterator<Item = &V> {
        self.map.values().map(|(v, _)| v)
    }

    /// Where the log is, for [`Logs::positions`].
    pub(crate) fn position(&self) -> usize {
        self.undo.len()
    }

    /// The keys changed since position `at` of the log, each with its
    /// value there (`None`: it had no row): the write-set since a
    /// checkpoint or transaction (§4.8.3). A key may be written and put
    /// back as it was, so a caller compares the value with the current one.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn changed_since(&self, at: usize) -> Vec<(&K, Option<&V>)> {
        self.changed_in(&[(at, None)])
    }

    /// The keys changed in these parts of the log, each `(start, end)` (to
    /// the end of the log for `None`), oldest first: each key once, with
    /// its value where the first part that logged it starts. A unit's
    /// write-set, from its segments ([`Journal::segments_since`]).
    pub(crate) fn changed_in(&self, parts: &[(usize, Option<usize>)]) -> Vec<(&K, Option<&V>)> {
        let mut seen: HashSet<&K> = HashSet::default();
        (parts.iter())
            .flat_map(|&(start, end)| &self.undo[start..end.unwrap_or(self.undo.len())])
            .filter(|(k, _)| seen.insert(k))
            .map(|(k, old)| (k, old.as_ref()))
            .collect()
    }
}

impl<K: Hash + Eq + Clone, V: Clone> Logged<K, V> {
    /// Changes `key`'s row, if it has one, by `f`; whether it had one.
    pub(crate) fn update<Q>(&mut self, key: &Q, f: impl FnOnce(&mut V)) -> bool
    where
        K: std::borrow::Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        if let Some(g) = self.generation {
            let Some((k, (value, stamp))) = self.map.get_key_value(key) else {
                return false;
            };
            if *stamp != g {
                self.undo.push((k.clone(), Some(value.clone())));
            }
        }
        let Some((value, stamp)) = self.map.get_mut(key) else {
            return false;
        };
        if let Some(g) = self.generation {
            *stamp = g;
        }
        f(value);
        true
    }
}

/// Whether a log or map with room for `capacity` holding `len` has much
/// more room than it uses: a quarter or less used, and not small.
fn roomy(capacity: usize, len: usize) -> bool {
    capacity > 1024 && len < capacity / 4
}

/// A set whose changes can be undone, as [`Logged`].
pub(crate) type LoggedSet<K> = Logged<K, ()>;

impl<K: Hash + Eq + Clone> Logged<K, ()> {
    /// Adds `key`; whether it was new.
    pub(crate) fn add(&mut self, key: K) -> bool {
        if self.map.contains_key(&key) {
            return false;
        }
        self.insert(key, ());
        true
    }
}

impl<K: Hash + Eq + Clone, V> Logs for Logged<K, V> {
    type Positions = usize;

    fn positions(&self) -> usize {
        self.undo.len()
    }

    fn undo_to(&mut self, at: &usize) -> usize {
        assert!(*at <= self.undo.len(), "a checkpoint from after a rewind");
        let undone = self.undo.len() - at;
        for (key, old) in self.undo.drain(*at..).rev() {
            match old {
                Some(value) => self.map.insert(key, (value, 0)),
                None => self.map.remove(&key),
            };
        }
        // A language server's first check grows the log and the map to the
        // whole project, and its first edit rewinds most of that: give the
        // room back (SW-1179), keeping twice what is left so that a recheck
        // doesn't regrow it a doubling at a time.
        if roomy(self.undo.capacity(), self.undo.len()) {
            self.undo.shrink_to(2 * self.undo.len());
        }
        if roomy(self.map.capacity(), self.map.len()) {
            self.map.shrink_to(2 * self.map.len());
        }
        undone
    }

    fn set_generation(&mut self, g: Option<Generation>) {
        if g.is_none() {
            self.undo = Vec::new();
        }
        self.generation = g;
    }

    fn entries(&self) -> usize {
        self.undo.len()
    }

    fn bytes(&self) -> usize {
        self.undo.capacity() * std::mem::size_of::<(K, Option<V>)>()
    }

    fn distinct_keys(&self) -> usize {
        let keys: HashSet<&K> = self.undo.iter().map(|(k, _)| k).collect();
        keys.len()
    }
}

/// What the journal has done in a session
/// (docs/proposals/elaborator-state.md §4.8.7). Counters, which add up
/// across sessions ([`JournalStats::add`]), except `held`, `bytes_held`,
/// `distinct_keys` and `open`, which are what the journal holds when the
/// statistics are read (`Elaborator::journal_stats`), and `peak_entries`, a maximum.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JournalStats {
    /// Log entries written.
    pub entries: usize,
    /// The most entries the logs have held at once (sampled at each of the
    /// journal's operations, between which the logs only grow).
    pub peak_entries: usize,
    /// Entries the logs hold now.
    pub held: usize,
    /// The bytes the logs hold now: their entries' own size, not what the
    /// keys and values point to.
    pub bytes_held: usize,
    /// Keys the logs hold an entry for now.
    pub distinct_keys: usize,
    /// Checkpoints open now: a language server's base and one before each
    /// namespace it keeps checked, if each is released when done with.
    pub open: usize,
    /// Rewinds, an abort's included.
    pub rewinds: usize,
    /// Entries undone by them: per rewind, `undone / rewinds`.
    pub undone: usize,
    pub checkpoints: usize,
    pub transactions: usize,
}

impl JournalStats {
    /// Adds `other`'s counters to these (a maximum for `peak_entries`).
    pub fn add(&mut self, other: &JournalStats) {
        let JournalStats {
            entries,
            peak_entries,
            held,
            bytes_held,
            distinct_keys,
            open,
            rewinds,
            undone,
            checkpoints,
            transactions,
        } = other;
        self.entries += entries;
        self.peak_entries = self.peak_entries.max(*peak_entries);
        self.held += held;
        self.bytes_held += bytes_held;
        self.distinct_keys += distinct_keys;
        self.open += open;
        self.rewinds += rewinds;
        self.undone += undone;
        self.checkpoints += checkpoints;
        self.transactions += transactions;
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Retained,
    Transaction,
}

struct Open<P> {
    serial: u64,
    kind: Kind,
    at: P,
    /// The segment it began, in [`Journal`]'s `segments`.
    segment: usize,
}

/// Where the logs were when a unit's part of the work began, and the unit.
struct Segment<P> {
    unit: UnitId,
    at: P,
}

/// The open checkpoints of a session's [`Logged`] tables, whose positions
/// are a `P` (see the module's comment).
pub(crate) struct Journal<P> {
    /// Oldest first.
    open: Vec<Open<P>>,
    /// Never reused.
    next_serial: u64,
    /// The last generation started.
    generation: Generation,
    /// How many entries the logs held at the last operation: what they
    /// gained since is what was logged in between.
    last_entries: usize,
    stats: JournalStats,
    /// The unit being elaborated (as `Owners` says).
    unit: UnitId,
    /// While something is open: where each unit's part began, oldest first.
    segments: Vec<Segment<P>>,
}

impl<P> Default for Journal<P> {
    fn default() -> Self {
        Journal {
            open: Vec::new(),
            next_serial: 0,
            generation: 0,
            last_entries: 0,
            stats: JournalStats::default(),
            unit: UnitId::default(),
            segments: Vec::new(),
        }
    }
}

/// A retained checkpoint (a language server's base, its mark before each
/// namespace): may be rewound to any number of times. Not `Clone`: one
/// handle per checkpoint.
#[derive(Debug)]
pub(crate) struct Checkpoint {
    serial: u64,
    depth: usize,
}

/// A transaction (a check cache entry's unit, or another short-lived
/// checkpoint): ended by [`Journal::commit`] or [`Journal::abort`], which
/// consume it.
#[must_use = "a transaction is ended by `commit` or `abort`"]
#[derive(Debug)]
pub(crate) struct Transaction {
    serial: u64,
    depth: usize,
    ended: bool,
}

impl Drop for Transaction {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            debug_assert!(self.ended, "a transaction dropped without commit or abort");
        }
    }
}

const STALE: &str = "a checkpoint used after a rewind to an older one";

impl<P> Journal<P> {
    /// A retained checkpoint where the tables are now.
    pub(crate) fn checkpoint<L: Logs<Positions = P>>(&mut self, logs: &mut L) -> Checkpoint {
        self.stats.checkpoints += 1;
        let (serial, depth) = self.push(Kind::Retained, logs);
        Checkpoint { serial, depth }
    }

    /// A transaction from where the tables are now.
    pub(crate) fn begin<L: Logs<Positions = P>>(&mut self, logs: &mut L) -> Transaction {
        self.stats.transactions += 1;
        let (serial, depth) = self.push(Kind::Transaction, logs);
        Transaction {
            serial,
            depth,
            ended: false,
        }
    }

    /// Puts the tables back as they were at `c`, which stays open; the
    /// checkpoints opened after it are dropped, and their handles become
    /// invalid. Panics if `c` is invalid, or if a transaction is open
    /// after it (end it first).
    pub(crate) fn rewind<L: Logs<Positions = P>>(&mut self, c: &Checkpoint, logs: &mut L) {
        self.check(c.serial, c.depth);
        self.rewind_to(c.depth, logs);
    }

    /// Closes `c`, the newest open checkpoint (an older one is closed by
    /// rewinding to one older still). Its changes stay.
    pub(crate) fn release<L: Logs<Positions = P>>(&mut self, c: Checkpoint, logs: &mut L) {
        self.check(c.serial, c.depth);
        assert!(
            c.depth + 1 == self.open.len(),
            "a checkpoint released with others open after it"
        );
        self.pop(logs);
    }

    /// Ends `t`, the newest open checkpoint, keeping its changes: they
    /// belong to whatever is still open.
    pub(crate) fn commit<L: Logs<Positions = P>>(&mut self, mut t: Transaction, logs: &mut L) {
        t.ended = true;
        self.check(t.serial, t.depth);
        assert!(
            t.depth + 1 == self.open.len(),
            "a transaction committed with others open after it"
        );
        self.pop(logs);
    }

    /// Ends `t`, undoing its changes: the checkpoints opened after it are
    /// dropped. Panics if a transaction is open after it.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn abort<L: Logs<Positions = P>>(&mut self, mut t: Transaction, logs: &mut L) {
        t.ended = true;
        self.check(t.serial, t.depth);
        self.rewind_to(t.depth, logs);
        self.pop(logs);
    }

    /// Where the tables were when `t` began: what its write-set is read
    /// from ([`Logged::changed_since`]).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn began_at(&self, t: &Transaction) -> &P {
        self.check(t.serial, t.depth);
        &self.open[t.depth].at
    }

    /// `unit` is now the one being elaborated: while something is open, a
    /// new segment begins (§4.8.3).
    pub(crate) fn set_unit<L: Logs<Positions = P>>(&mut self, unit: UnitId, logs: &mut L) {
        self.unit = unit;
        if self.is_open() {
            self.sample(logs);
            self.segments.push(Segment {
                unit,
                at: logs.positions(),
            });
            self.new_generation(logs);
        }
    }

    /// The parts of the logs written since `t` began while a unit `own`
    /// picks was being elaborated: each segment's start, and the next one's
    /// (`None`: the logs' end). What its write-set is read from
    /// ([`Logged::changed_in`]).
    pub(crate) fn segments_since(
        &self,
        t: &Transaction,
        own: impl Fn(UnitId) -> bool,
    ) -> Vec<(&P, Option<&P>)> {
        self.check(t.serial, t.depth);
        let first = self.open[t.depth].segment;
        let segments = &self.segments[first..];
        (segments.iter().enumerate())
            .filter(|(_, s)| own(s.unit))
            .map(|(i, s)| (&s.at, segments.get(i + 1).map(|n| &n.at)))
            .collect()
    }

    /// How many segments there are: [`Journal::units_from`] the next.
    pub(crate) fn segments(&self) -> usize {
        self.segments.len()
    }

    /// The units of the segments from the `n`th on.
    pub(crate) fn units_from(&self, n: usize) -> impl Iterator<Item = UnitId> + '_ {
        self.segments[n.min(self.segments.len())..]
            .iter()
            .map(|s| s.unit)
    }

    /// Whether anything is open, so that the tables log.
    pub(crate) fn is_open(&self) -> bool {
        !self.open.is_empty()
    }

    /// The statistics, with what `logs` hold now.
    pub(crate) fn stats<L: Logs<Positions = P>>(&self, logs: &L) -> JournalStats {
        let held = logs.entries();
        JournalStats {
            entries: self.stats.entries + held.saturating_sub(self.last_entries),
            peak_entries: self.stats.peak_entries.max(held),
            held,
            bytes_held: logs.bytes(),
            distinct_keys: logs.distinct_keys(),
            open: self.open.len(),
            ..self.stats
        }
    }

    fn check(&self, serial: u64, depth: usize) {
        assert!(
            self.open.get(depth).is_some_and(|o| o.serial == serial),
            "{STALE}"
        );
    }

    fn push<L: Logs<Positions = P>>(&mut self, kind: Kind, logs: &mut L) -> (u64, usize) {
        self.sample(logs);
        let serial = self.next_serial;
        self.next_serial += 1;
        let depth = self.open.len();
        self.open.push(Open {
            serial,
            kind,
            at: logs.positions(),
            segment: self.segments.len(),
        });
        self.segments.push(Segment {
            unit: self.unit,
            at: logs.positions(),
        });
        self.new_generation(logs);
        (serial, depth)
    }

    /// Back to the checkpoint at `depth`, dropping those after it.
    fn rewind_to<L: Logs<Positions = P>>(&mut self, depth: usize, logs: &mut L) {
        assert!(
            self.open[depth + 1..]
                .iter()
                .all(|o| o.kind == Kind::Retained),
            "a rewind past an open transaction (commit or abort it first)"
        );
        self.sample(logs);
        self.open.truncate(depth + 1);
        let undone = logs.undo_to(&self.open[depth].at);
        // The checkpoint's own segment goes on, in the unit it was taken in.
        let segment = self.open[depth].segment;
        self.segments.truncate(segment + 1);
        self.unit = self.segments[segment].unit;
        self.stats.rewinds += 1;
        self.stats.undone += undone;
        self.last_entries = logs.entries();
        self.new_generation(logs);
    }

    fn pop<L: Logs<Positions = P>>(&mut self, logs: &mut L) {
        self.sample(logs);
        self.open.pop();
        if self.open.is_empty() {
            logs.set_generation(None);
            self.last_entries = 0;
            self.segments = Vec::new();
        }
    }

    fn new_generation<L: Logs<Positions = P>>(&mut self, logs: &mut L) {
        self.generation = self
            .generation
            .checked_add(1)
            .expect("fewer than 2^32 checkpoints and rewinds in a session");
        logs.set_generation(Some(self.generation));
    }

    /// Notes what was logged since the last operation.
    fn sample<L: Logs<Positions = P>>(&mut self, logs: &L) {
        let held = logs.entries();
        self.stats.entries += held.saturating_sub(self.last_entries);
        self.stats.peak_entries = self.stats.peak_entries.max(held);
        self.last_entries = held;
    }
}

#[cfg(test)]
mod tests;
