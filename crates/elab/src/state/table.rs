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
//!   unit that declared it is elaborated ([`super::owners`]), which
//!   [`OwnedBy::insert`] and [`OwnedBy::remove`] assert. Rewound by
//!   dropping the rows of declarations made since; an entry holds the rows
//!   of the unit's own declarations.
//!
//! The note's other two kinds aren't here: the tables any of whose rows may
//! change are [`super::journal::Logged`] (though `Tables`' own are still
//! copied at a mark until §7 step 6b), and the derived ones are
//! [`super::Caches`].

use std::hash::Hash;
use std::ops::Deref;

use stitchwort_core::collections::HashMap;
use stitchwort_core::{DataId, DefId};

use super::owners::{Owners, UnitId};
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
    /// Adds an entry's rows, read back, in the unit replaying it.
    fn replay(&mut self, rows: Self::Rows, owners: &Owners);
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

    fn replay(&mut self, rows: Vec<T>, _: &Owners) {
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
    /// The unit that made it.
    fn owner(self, owners: &Owners) -> UnitId;
}

impl Id for DataId {
    fn index(self) -> usize {
        self.0
    }
    fn count(ids: Ids) -> usize {
        ids.datas
    }
    fn owner(self, owners: &Owners) -> UnitId {
        owners.of_data(self.0)
    }
}

impl Id for DefId {
    fn index(self) -> usize {
        self.0
    }
    fn count(ids: Ids) -> usize {
        ids.defs
    }
    fn owner(self, owners: &Owners) -> UnitId {
        owners.of_def(self.0)
    }
}

/// A table keyed by declaration, whose rows only the declaring unit writes
/// (see the module's comment).
pub(crate) struct OwnedBy<I, V> {
    rows: HashMap<I, V>,
}

impl<I, V> Default for OwnedBy<I, V> {
    fn default() -> Self {
        OwnedBy {
            rows: HashMap::default(),
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
}

impl<I: Id, V> OwnedBy<I, V> {
    /// Sets `id`'s row; `owners` say which unit is being elaborated, and
    /// it must be the one that made `id`.
    pub(crate) fn insert(&mut self, owners: &Owners, id: I, row: V) -> Option<V> {
        owned(owners, id);
        self.rows.insert(id, row)
    }

    /// Removes `id`'s row, as [`OwnedBy::insert`].
    pub(crate) fn remove(&mut self, owners: &Owners, id: &I) -> Option<V> {
        owned(owners, *id);
        self.rows.remove(id)
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
        }
    }

    fn rewind(&mut self, m: &OwnedMark) {
        self.rows.retain(|id, _| id.index() < m.cut);
    }

    fn encode_since(&self, m: &OwnedMark, e: &mut Encoding<'_>) -> Result<(), String> {
        let (old, new): (Vec<_>, Vec<_>) = self
            .sorted()
            .into_iter()
            .partition(|(id, _)| id.index() < m.cut);
        // Only the unit that made a declaration writes its row, and a
        // unit's entry is written against a mark taken once the library
        // files it needs have loaded: no row below the cut is the unit's.
        // (Still refused in a build without debug assertions.)
        debug_assert_eq!(
            old.len(),
            m.rows,
            "a row for an older declaration was added"
        );
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

    fn replay(&mut self, rows: Vec<(I, V)>, owners: &Owners) {
        for (id, row) in rows {
            self.insert(owners, id, row);
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

fn owned<I: Id>(owners: &Owners, id: I) {
    let (owner, current) = (id.owner(owners), owners.current());
    assert!(
        owner == current,
        "a row for declaration {} written by unit {current:?}, not by its own, {owner:?}",
        id.index(),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(defs: usize, datas: usize) -> Ids {
        Ids { defs, datas }
    }

    /// A unit can't write a row for a declaration of a unit nested in it,
    /// even one made after the unit began (F9): the floor the tag replaced
    /// allowed it.
    #[test]
    fn a_row_is_written_by_its_unit_only() {
        let mut owners = Owners::default();
        let mut t: OwnedBy<DataId, u32> = OwnedBy::default();
        // Unit A begins with 100 data types, and a library file B loads
        // inside it, declaring the 101st.
        owners.begin(ids(0, 100));
        let a = owners.enter(ids(0, 100));
        t.insert(&owners, DataId(100), 1);
        owners.leave(ids(0, 101), a);
        // A overwriting B's row, or removing it, is refused.
        let overwrite = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            t.insert(&owners, DataId(100), 2)
        }));
        assert!(overwrite.is_err());
        let remove = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            t.remove(&owners, &DataId(100))
        }));
        assert!(remove.is_err());
        assert_eq!(t.get(&DataId(100)), Some(&1));
        // A's own, made after B, and an older unit's.
        t.insert(&owners, DataId(101), 3);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                t.insert(&owners, DataId(5), 4)
            }))
            .is_err()
        );
    }

    /// The tags survive a rewind as they were at the mark, and declarations
    /// made again after it belong to the unit current then.
    #[test]
    fn a_rewind_puts_the_owners_back() {
        let mut owners = Owners::default();
        let a = owners.begin(ids(3, 0));
        let m = owners.mark();
        let outer = owners.enter(ids(4, 0));
        owners.leave(ids(6, 0), outer);
        assert_ne!(owners.of_def(5), a);
        owners.rewind(&m);
        assert_eq!(owners.current(), a);
        assert_eq!(owners.of_def(3), a);
        assert_eq!(owners.of_def(5), a, "made again by A");
        assert_ne!(owners.of_def(2), a);
    }
}
