//! Rewinding (docs/proposals/language-server.md §5.1, stage 0b): a
//! [`Mark`] notes where the elaborator is, and [`Elaborator::rewind`] puts
//! it back there, forgetting everything checked since, so that a language
//! server can check a namespace again from its new text without starting a
//! new session.
//!
//! A mark is taken between loads (no declaration being checked, no library
//! file loading), where every per-declaration table is empty. Rewinding
//! restores each table in one of three ways:
//!
//! - **Grows only, indexed by load order** (definitions, data types, the
//!   library files loaded, and `state::Tables`' `GrowVec`s: abilities,
//!   lifted helpers, tests): cut back to its length at the mark.
//! - **Keyed by declaration** (`state::Tables`' `OwnedBy` tables: records,
//!   interfaces, owners, why `==`, `show` and `compare` aren't derived): the
//!   rows for declarations made since are removed. A declaration's rows are
//!   only ever written while its own unit is checked, which writing one
//!   asserts.
//! - **Anything else that can change** (the names, instances, the module
//!   state, the project's tables, the dot-call caches): a copy
//!   taken at the mark is put back. These are the tables in which a later
//!   load can change an older row (`check-cache.md` stage 1, point 3), so
//!   lengths aren't enough. Copying them costs a few milliseconds per
//!   mark (measured in the note's "As built").
//! - **Navigation**, which grows with every namespace checked: its maps
//!   log what each change replaced, which rewinding takes back
//!   ([`nav::Logged`]); a copy at each of a language server's marks made
//!   them quadratic in the project (SW-1052).
//!
//! The per-declaration state is emptied: the inference state
//! (`state::Attempt`; after a cancelled check it may be half-full) and the
//! declaration's scratch (`state::Decl`, empty at every mark, which
//! asserts it). The unit's state (`state::Unit`) is put back as it was at
//! the mark: a unit's module and namespace outlive it. The project and cache
//! bookkeeping a later load can change is put back too (`state::Session`);
//! its counters and the settings (`state::Options`: limits, test switches,
//! the check cache's store) stay as they are: they say how to check, not
//! what was checked.
//!
//! [`Elaborator::rewind`] names every field of the elaborator, so a new
//! field doesn't compile until it says how it rewinds; the differential test
//! (`crates/driver/tests/rewind.rs`) catches a field that rewinds wrongly.

use stitchwort_core::globals::GlobalsMark;

use crate::{Elaborator, nav, scope};

/// A point an [`Elaborator`] can be rewound to ([`Elaborator::mark`]). It
/// stays valid, and can be rewound to any number of times, until the
/// elaborator is rewound to an earlier mark.
pub struct Mark {
    globals: GlobalsMark,
    unit: crate::state::UnitMark,
    session: crate::state::SessionMark,
    tables: crate::state::TablesMark,
    scope: scope::Scope,
    caches: crate::state::CachesMark,
    nav: Option<nav::NavMark>,
}

impl Mark {
    /// How many definitions there were.
    pub fn defs(&self) -> usize {
        self.globals.defs()
    }
}

impl Elaborator {
    /// Where the elaborator is now, to [`Elaborator::rewind`] to later.
    /// Only between loads: not while a declaration is checked or a library
    /// file loads.
    pub fn mark(&self) -> Mark {
        assert!(
            self.globals.metas.borrow().is_empty() && self.library_stack_is_empty(),
            "a mark in the middle of checking"
        );
        if let Some(field) = self.decl.leftover() {
            panic!("a mark in the middle of a declaration: `Decl::{field}` isn't empty");
        }
        Mark {
            globals: self.globals.mark(),
            unit: self.unit.mark(),
            session: self.session.mark(),
            tables: self.tables.mark(self.ids()),
            scope: self.scope.clone(),
            caches: self.caches.mark(),
            nav: self.nav.as_ref().map(|n| n.borrow_mut().mark()),
        }
    }

    /// Puts the elaborator back as it was at `mark`: everything declared,
    /// named, recorded or loaded since is forgotten (see the module's
    /// comment). Also after a check that stopped part way, cancelled or
    /// not.
    pub fn rewind(&mut self, mark: &Mark) {
        let Elaborator {
            globals,
            tables,
            scope,
            attempt,
            decl,
            unit,
            // Settings: they say how to check, not what was checked.
            options: _,
            session,
            caches,
            goals,
            goal_snapshots,
            nav,
        } = self;
        let defs = mark.globals.defs();
        globals.rewind(&mark.globals);
        tables.rewind(&mark.tables);
        *scope = mark.scope.clone();
        attempt.rewind();
        *decl = crate::state::Decl::default();
        unit.rewind(&mark.unit);
        session.rewind(&mark.session);
        caches.rewind(&mark.caches, defs);
        *goals.get_mut() = Default::default();
        // Their terms may name what is forgotten.
        goal_snapshots.get_mut().clear();
        if let (Some(nav), Some(at_mark)) = (nav.as_mut(), &mark.nav) {
            nav.get_mut().rewind(at_mark);
        }
    }
}
