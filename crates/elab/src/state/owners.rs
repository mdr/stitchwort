//! Which unit made each declaration (docs/proposals/elaborator-state.md
//! §4.8.4): what [`super::table::OwnedBy`] checks a write against.
//!
//! A unit is a library file, a project namespace, a file loaded on its own,
//! or the equations made on demand for a library file's definition; the
//! core and the prelude are unit 0. Its [`UnitId`] is a counter of the
//! session, never written to a check cache entry, so entries don't depend
//! on it.
//!
//! A declaration belongs to the unit that was current when it was made.
//! Rather than a tag pushed by every place that makes one (the kernel,
//! the check cache's replay), the tags are filled in each time the current
//! unit changes ([`Owners::begin`], [`Owners::enter`], [`Owners::leave`]):
//! the declarations made since the last change are the outgoing unit's.
//! Those made since are the current unit's, untagged until the next change.
//! That relies on nothing about the order ids are given out in.

use super::table::Ids;

/// A unit of elaboration (see the module's comment).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct UnitId(u32);

#[derive(Default)]
pub(crate) struct Owners {
    /// The unit being elaborated.
    current: UnitId,
    /// The last unit given out. Never reused, so a rewind leaves it.
    last: u32,
    /// The unit of each definition and data type, by id, up to the last
    /// change of unit.
    defs: Vec<UnitId>,
    datas: Vec<UnitId>,
}

/// Where [`Owners`] are, for a rewind.
pub(crate) struct Mark {
    current: UnitId,
    defs: usize,
    datas: usize,
}

impl Owners {
    pub(crate) fn current(&self) -> UnitId {
        self.current
    }

    pub(crate) fn of_def(&self, id: usize) -> UnitId {
        self.defs.get(id).copied().unwrap_or(self.current)
    }

    pub(crate) fn of_data(&self, id: usize) -> UnitId {
        self.datas.get(id).copied().unwrap_or(self.current)
    }

    /// A new unit, with `ids` the declarations made so far, which are the
    /// unit current until now's.
    pub(crate) fn begin(&mut self, ids: Ids) -> UnitId {
        self.tag(ids);
        self.last += 1;
        self.current = UnitId(self.last);
        self.current
    }

    /// A unit nested in the current one ([`Owners::begin`]); gives the
    /// current one, to [`Owners::leave`] back to.
    pub(crate) fn enter(&mut self, ids: Ids) -> UnitId {
        let outer = self.current;
        self.begin(ids);
        outer
    }

    /// Back to unit `outer` once the nested one is done, with `ids` the
    /// declarations made so far.
    pub(crate) fn leave(&mut self, ids: Ids, outer: UnitId) {
        self.tag(ids);
        self.current = outer;
    }

    /// Forgets the tags of the declarations from `ids` on, which have been
    /// removed (their ids will be given out again).
    pub(crate) fn truncate(&mut self, ids: Ids) {
        self.defs.truncate(ids.defs);
        self.datas.truncate(ids.datas);
    }

    pub(crate) fn mark(&self) -> Mark {
        Mark {
            current: self.current,
            defs: self.defs.len(),
            datas: self.datas.len(),
        }
    }

    /// Back to `m`. The declarations made after it are removed too, and
    /// those between the last change of unit and `m` are `m`'s current
    /// unit's, untagged as they were.
    pub(crate) fn rewind(&mut self, m: &Mark) {
        self.defs.truncate(m.defs);
        self.datas.truncate(m.datas);
        self.current = m.current;
    }

    /// Tags the declarations made since the last change as the current
    /// unit's.
    fn tag(&mut self, ids: Ids) {
        let current = self.current;
        self.defs.resize(ids.defs.max(self.defs.len()), current);
        self.datas.resize(ids.datas.max(self.datas.len()), current);
    }
}
