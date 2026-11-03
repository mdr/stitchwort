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
//! - **Grows only, indexed by load order** (definitions, data types,
//!   abilities, lifted helpers, tests, the per-definition caches, the
//!   library files loaded): cut back to its length at the mark.
//! - **Keyed by data type** (records, interfaces, owners, why `==`, `show`
//!   and `compare` aren't derived): the rows for types declared since are
//!   removed. A type's rows are only ever written while its own module is
//!   checked.
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

use std::collections::BTreeMap;

use stitchwort_core::DataId;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::GlobalsMark;

use crate::{Elaborator, interfaces, nav, scope};

/// A point an [`Elaborator`] can be rewound to ([`Elaborator::mark`]). It
/// stays valid, and can be rewound to any number of times, until the
/// elaborator is rewound to an earlier mark.
pub struct Mark {
    globals: GlobalsMark,
    unit: crate::state::UnitMark,
    session: crate::state::SessionMark,
    tests: usize,
    scope: scope::Scope,
    namespace_defs: BTreeMap<String, std::ops::Range<usize>>,
    prelude_defs: usize,
    abilities: usize,
    caches: crate::state::CachesMark,
    lifted: usize,
    helper_keys: HashSet<String>,
    instances: HashMap<(DataId, DataId), interfaces::InstanceInfo>,
    nav: Option<nav::NavMark>,
    equations_done: usize,
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
            tests: self.tests.len(),
            scope: self.scope.clone(),
            namespace_defs: self.namespace_defs.clone(),
            prelude_defs: self.prelude_defs,
            abilities: self.abilities.len(),
            caches: self.caches.mark(),
            lifted: self.lifted.len(),
            helper_keys: self.helper_keys.clone(),
            instances: self.instances.clone(),
            nav: self.nav.as_ref().map(|n| n.borrow_mut().mark()),
            equations_done: self.equations_done.len(),
        }
    }

    /// Puts the elaborator back as it was at `mark`: everything declared,
    /// named, recorded or loaded since is forgotten (see the module's
    /// comment). Also after a check that stopped part way, cancelled or
    /// not.
    pub fn rewind(&mut self, mark: &Mark) {
        let Elaborator {
            globals,
            tests,
            scope,
            namespace_defs,
            prelude_defs,
            attempt,
            decl,
            unit,
            // Settings: they say how to check, not what was checked.
            options: _,
            session,
            abilities,
            caches,
            records,
            no_eq,
            no_show,
            no_ord,
            no_finite,
            no_decide,
            generated_alls,
            lifted,
            match_columns,
            helper_keys,
            goals,
            goal_snapshots,
            total_rows,
            interfaces,
            instances,
            data_owners,
            nav,
            equation_skips,
            equations_done,
        } = self;
        equations_done.truncate(mark.equations_done);
        equation_skips.retain(|(id, _, _)| id.0 < mark.globals.defs());
        let defs = mark.globals.defs();
        let datas = mark.globals.datas();
        globals.rewind(&mark.globals);
        tests.truncate(mark.tests);
        *scope = mark.scope.clone();
        *namespace_defs = mark.namespace_defs.clone();
        *prelude_defs = mark.prelude_defs;
        attempt.rewind();
        *decl = crate::state::Decl::default();
        unit.rewind(&mark.unit);
        session.rewind(&mark.session);
        abilities.truncate(mark.abilities);
        caches.rewind(&mark.caches, defs);
        records.retain(|d, _| d.0 < datas);
        no_eq.retain(|d, _| d.0 < datas);
        no_show.retain(|d, _| d.0 < datas);
        no_ord.retain(|d, _| d.0 < datas);
        no_finite.retain(|d, _| d.0 < datas);
        no_decide.retain(|d, _| d.0 < datas);
        generated_alls.retain(|d, id| d.0 < datas && id.0 < defs);
        interfaces.retain(|d, _| d.0 < datas);
        data_owners.retain(|d, _| d.0 < datas);
        lifted.truncate(mark.lifted);
        match_columns.retain(|id, _| id.0 < defs);
        *helper_keys = mark.helper_keys.clone();
        *goals.get_mut() = Default::default();
        // Their terms may name what is forgotten.
        goal_snapshots.get_mut().clear();
        total_rows.get_mut().retain(|id, _| id.0 < defs);
        *instances = mark.instances.clone();
        if let (Some(nav), Some(at_mark)) = (nav.as_mut(), &mark.nav) {
            nav.get_mut().rewind(at_mark);
        }
    }
}
