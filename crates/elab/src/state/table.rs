//! The kinds of table [`super::Tables`] is made of
//! (docs/proposals/elaborator-state.md §4.2). A table states its kind once,
//! where it is declared, and the kind supplies how it is marked and rewound,
//! which rows a check cache entry holds and how they are replayed, and the
//! dump of the whole table ([`Table`]). Only a row's bytes ([`Codec`],
//! `cache/rows.rs`) and its text ([`Dump`], `cache/dump.rs`) are written by
//! hand, each independently of the other, so the differential tests compare
//! two things written separately.
//!
//! - [`GrowVec`]: rows are only pushed, in load order. Marked by its length,
//!   rewound by cutting back to it; an entry holds the rows pushed since.
//! - [`OwnedBy`]: rows keyed by a declaration, each written only while the
//!   unit that declared it is elaborated, which [`OwnedBy::insert`]
//!   asserts. Rewound by dropping the rows of declarations made since; an
//!   entry holds the rows of the unit's own declarations, and writing it
//!   checks no older row was added.
//!
//! The note's other two kinds aren't types here: the tables any of whose
//! rows may change (`Logged`, §7 step 6) are still copied at a mark, and
//! the derived ones are [`super::Caches`].

use std::hash::Hash;
use std::ops::Deref;

use stitchwort_core::collections::HashMap;
use stitchwort_core::{DataId, DefId};

use crate::cache::{Body, Encoding, Read};

/// A row's bytes in a check cache entry: declarations by path and hash
/// (through [`Encoding`]'s references), never by load-order id.
pub(crate) trait Codec: Sized {
    fn encode(&self, e: &mut Encoding<'_>);
    fn decode(b: &mut Body<'_>) -> Read<Self>;
}

/// A row's text in the canonical dump, written independently of [`Codec`].
pub(crate) trait Dump {
    fn dump(&self, out: &mut String);
}

/// How many declarations there are: what a mark cuts the tables keyed by
/// declaration at.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Ids {
    pub(crate) defs: usize,
    pub(crate) datas: usize,
}

/// How a table of one kind serves each mechanism.
pub(crate) trait Table {
    type Mark;
    /// What a check cache entry holds of the table, read back.
    type Rows;
    /// Where the table is, with `ids` declarations made so far.
    fn mark(&self, ids: Ids) -> Self::Mark;
    /// Back to `m` (stack order: no older mark has been rewound to since).
    fn rewind(&mut self, m: &Self::Mark);
    /// What the unit being encoded added since `m`; an error if it changed
    /// what was there before in a way an entry can't hold.
    fn encode_since(&self, m: &Self::Mark, e: &mut Encoding<'_>) -> Result<(), String>;
    fn decode(b: &mut Body<'_>) -> Read<Self::Rows>;
    /// Adds an entry's rows, read back.
    fn replay(&mut self, rows: Self::Rows);
    /// The whole table, one line per row, each starting with `name`.
    fn dump(&self, name: &str, out: &mut String);
}

/// A table that only grows, in load order (see the module's comment).
pub(crate) struct GrowVec<T> {
    rows: Vec<T>,
}

impl<T> Default for GrowVec<T> {
    fn default() -> Self {
        GrowVec { rows: Vec::new() }
    }
}

impl<T> Deref for GrowVec<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        &self.rows
    }
}

impl<T> GrowVec<T> {
    pub(crate) fn push(&mut self, row: T) {
        self.rows.push(row);
    }

    /// The rows pushed since `m`.
    pub(crate) fn since(&self, m: usize) -> &[T] {
        &self.rows[m..]
    }

    /// Puts the rows pushed since `from` in order. Only within the unit
    /// that pushed them: a mark is never taken inside a unit.
    pub(crate) fn sort_since_by_key<K: Ord>(&mut self, from: usize, key: impl FnMut(&T) -> K) {
        self.rows[from..].sort_by_key(key);
    }
}

impl<T: Dump> GrowVec<T> {
    /// [`Table::dump`] with the lines sorted, for a table whose order no
    /// reader depends on: a cached run may push its rows in another order.
    pub(crate) fn dump_sorted(&self, name: &str, out: &mut String) {
        let mut lines: Vec<String> = self.rows.iter().map(|row| line(name, row)).collect();
        lines.sort();
        lines.iter().for_each(|l| out.push_str(l));
    }
}

fn line(name: &str, row: &impl Dump) -> String {
    let mut s = format!("{name} ");
    row.dump(&mut s);
    s.push('\n');
    s
}

impl<T: Codec + Dump> Table for GrowVec<T> {
    type Mark = usize;
    type Rows = Vec<T>;

    fn mark(&self, _: Ids) -> usize {
        self.rows.len()
    }

    fn rewind(&mut self, m: &usize) {
        self.rows.truncate(*m);
    }

    fn encode_since(&self, m: &usize, e: &mut Encoding<'_>) -> Result<(), String> {
        let rows = self.since(*m);
        e.count(rows.len());
        rows.iter().for_each(|row| row.encode(e));
        Ok(())
    }

    fn decode(b: &mut Body<'_>) -> Read<Vec<T>> {
        let n = b.count()?;
        (0..n).map(|_| T::decode(b)).collect()
    }

    fn replay(&mut self, rows: Vec<T>) {
        self.rows.extend(rows);
    }

    fn dump(&self, name: &str, out: &mut String) {
        self.rows
            .iter()
            .for_each(|row| out.push_str(&line(name, row)));
    }
}

/// A declaration's id, as a key of an [`OwnedBy`] table.
pub(crate) trait Id: Copy + Eq + Hash + Codec + Dump {
    fn index(self) -> usize;
    /// The ids there are of this kind.
    fn count(ids: Ids) -> usize;
}

impl Id for DataId {
    fn index(self) -> usize {
        self.0
    }
    fn count(ids: Ids) -> usize {
        ids.datas
    }
}

impl Id for DefId {
    fn index(self) -> usize {
        self.0
    }
    fn count(ids: Ids) -> usize {
        ids.defs
    }
}

/// A table keyed by declaration, whose rows only the declaring unit writes
/// (see the module's comment).
pub(crate) struct OwnedBy<I, V> {
    rows: HashMap<I, V>,
    /// The first id of the unit being elaborated: rows below it are
    /// another unit's.
    floor: usize,
}

impl<I, V> Default for OwnedBy<I, V> {
    fn default() -> Self {
        OwnedBy {
            rows: HashMap::default(),
            floor: 0,
        }
    }
}

impl<I, V> Deref for OwnedBy<I, V> {
    type Target = HashMap<I, V>;
    fn deref(&self) -> &HashMap<I, V> {
        &self.rows
    }
}

/// Where an [`OwnedBy`] table is.
pub(crate) struct OwnedMark {
    /// Rows for ids from here on are newer.
    cut: usize,
    /// How many rows there were (all below `cut`).
    rows: usize,
    floor: usize,
}

impl<I: Id, V> OwnedBy<I, V> {
    pub(crate) fn insert(&mut self, id: I, row: V) -> Option<V> {
        self.owned(id);
        self.rows.insert(id, row)
    }

    pub(crate) fn remove(&mut self, id: &I) -> Option<V> {
        self.owned(*id);
        self.rows.remove(id)
    }

    fn owned(&self, id: I) {
        assert!(
            id.index() >= self.floor,
            "a row for declaration {} written by a later unit (its first is {})",
            id.index(),
            self.floor,
        );
    }

    /// The rows sorted by id.
    fn sorted(&self) -> Vec<(&I, &V)> {
        let mut rows: Vec<(&I, &V)> = self.rows.iter().collect();
        rows.sort_by_key(|(id, _)| id.index());
        rows
    }
}

impl<I: Id, V: Codec + Dump> Table for OwnedBy<I, V> {
    type Mark = OwnedMark;
    type Rows = Vec<(I, V)>;

    fn mark(&self, ids: Ids) -> OwnedMark {
        OwnedMark {
            cut: I::count(ids),
            rows: self.rows.len(),
            floor: self.floor,
        }
    }

    fn rewind(&mut self, m: &OwnedMark) {
        self.rows.retain(|id, _| id.index() < m.cut);
        self.floor = m.floor;
    }

    fn encode_since(&self, m: &OwnedMark, e: &mut Encoding<'_>) -> Result<(), String> {
        let (old, new): (Vec<_>, Vec<_>) = self
            .sorted()
            .into_iter()
            .partition(|(id, _)| id.index() < m.cut);
        if old.len() != m.rows {
            return Err("a row for an older declaration changed".to_string());
        }
        e.count(new.len());
        for (id, row) in new {
            id.encode(e);
            row.encode(e);
        }
        Ok(())
    }

    fn decode(b: &mut Body<'_>) -> Read<Vec<(I, V)>> {
        let n = b.count()?;
        (0..n).map(|_| Ok((I::decode(b)?, V::decode(b)?))).collect()
    }

    fn replay(&mut self, rows: Vec<(I, V)>) {
        for (id, row) in rows {
            self.insert(id, row);
        }
    }

    fn dump(&self, name: &str, out: &mut String) {
        for (id, row) in self.sorted() {
            let mut s = format!("{name} ");
            id.dump(&mut s);
            s.push(' ');
            row.dump(&mut s);
            s.push('\n');
            out.push_str(&s);
        }
    }
}

impl<I: Id, V> OwnedBy<I, V> {
    /// Says which ids the unit being elaborated starts at.
    pub(crate) fn set_floor(&mut self, start: Ids) {
        self.floor = I::count(start);
    }
}
