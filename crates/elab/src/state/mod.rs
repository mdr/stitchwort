//! The elaborator's state, by lifetime (docs/proposals/elaborator-state.md).
//!
//! Each component holds the fields of one lifetime, and each mechanism that
//! walks the state (undoing an attempt, per-declaration cleanup, rewinding,
//! the check cache, the canonical dump) is a method that destructures its
//! component exhaustively: a new field doesn't compile until it says what
//! each mechanism does with it.
//!
//! The components planned (§4.1), of which [`Options`], [`Session`],
//! [`Unit`], [`Decl`], [`Attempt`], [`Caches`] and [`Tables`] exist so far (§7
//! steps 1 to 5); the rest of the state is still fields of the `Elaborator`
//! and of `Globals`:
//!
//! - [`Options`]: settings and test switches, and the cache key;
//! - `Kernel`: the kernel's half of `Globals` (definitions, data types,
//!   builtins);
//! - [`Tables`]: what later units read (records, instances, tests, ...),
//!   each table of a kind that says how it is marked, rewound, encoded and
//!   dumped ([`table`]); the scope joins them in step 6;
//! - [`Session`]: project and cache bookkeeping, statistics;
//! - [`Unit`]: the unit being elaborated, set aside whole while a library
//!   file is loaded inside one;
//! - [`Decl`]: per-declaration scratch, rebuilt by `Default`;
//! - [`Attempt`]: the inference state a failed attempt takes back;
//! - [`Caches`]: tables that can be emptied at any time;
//! - `Presentation`: navigation, goals shown, logs.

mod attempt;
mod caches;
mod decl;
mod options;
mod session;
mod table;
mod tables;
mod unit;

pub(crate) use attempt::Attempt;
pub(crate) use attempt::Mark as AttemptMark;
pub(crate) use caches::Caches;
pub(crate) use caches::Mark as CachesMark;
pub(crate) use decl::Decl;
pub use options::Options;
pub(crate) use session::Mark as SessionMark;
pub use session::Session;
pub(crate) use session::Stats;
pub(crate) use table::{Codec, Dump, Ids};
pub(crate) use tables::Delta as TablesDelta;
pub(crate) use tables::Mark as TablesMark;
pub(crate) use tables::Tables;
pub(crate) use unit::Mark as UnitMark;
pub(crate) use unit::Unit;

use std::cell::{Cell, RefCell};

/// A value put in a [`RefCell`] for the dynamic extent of a call: the
/// previous value is put back when this is dropped, or by
/// [`Scoped::finish`], which also gives the value the cell then held.
pub(crate) struct Scoped<'a, T> {
    cell: &'a RefCell<T>,
    old: Option<T>,
}

impl<'a, T> Scoped<'a, T> {
    pub(crate) fn set(cell: &'a RefCell<T>, value: T) -> Self {
        let old = cell.replace(value);
        Scoped {
            cell,
            old: Some(old),
        }
    }

    /// Puts the previous value back, and gives the one the cell held.
    pub(crate) fn finish(mut self) -> T {
        let old = self.old.take().expect("put back only once");
        self.cell.replace(old)
    }
}

impl<T> Drop for Scoped<'_, T> {
    fn drop(&mut self) {
        if let Some(old) = self.old.take()
            && let Ok(mut cell) = self.cell.try_borrow_mut()
        {
            *cell = old;
        }
    }
}

/// [`Scoped`] for a [`Cell`].
pub(crate) struct ScopedCell<'a, T: Copy> {
    cell: &'a Cell<T>,
    old: T,
}

impl<'a, T: Copy> ScopedCell<'a, T> {
    pub(crate) fn set(cell: &'a Cell<T>, value: T) -> Self {
        let old = cell.replace(value);
        ScopedCell { cell, old }
    }
}

impl<T: Copy> Drop for ScopedCell<'_, T> {
    fn drop(&mut self) {
        self.cell.set(self.old);
    }
}
