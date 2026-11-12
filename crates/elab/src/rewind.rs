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
//! - **Maps in which a later load can change an older row** (the names,
//!   the instances, the helpers' keys, the keys of the project's
//!   namespaces and where its files are; `check-cache.md` stage 1, point
//!   3), so lengths aren't enough, and **navigation**, which grows with
//!   every namespace checked: each map logs what its changes replaced
//!   (`state::Logged`), and the session's journal takes them back. A mark
//!   is a checkpoint of the journal (`state::Journal`,
//!   docs/proposals/elaborator-state.md §4.8.2), which costs O(number of
//!   tables), not a copy: copies at each of a language server's marks
//!   made them quadratic in the project (SW-1052; the scope's cost 3 MB a
//!   mark on the AoC project).
//! - **What is left** is copied: the module state and its imports, the
//!   library files' states, the ranges of the project's namespaces, all
//!   small between namespaces. What the host sets whole (the project's
//!   namespaces and their names, their sources' keys) is shared with the
//!   mark. The caches (`state::Caches`) are cut or emptied, the dot-call
//!   ones included: copying those cost 2 MB a mark on the AoC project
//!   (SW-1179).
//!
//! A mark that is no longer wanted is released ([`Elaborator::release`]),
//! newest first, or dropped by rewinding to an older one; one only dropped
//! keeps the journal logging, for nothing, until then.
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
//! (`crates/driver/tests/projects/rewind.rs`) catches a field that rewinds wrongly.

use stitchwort_core::globals::KernelMark;

use crate::state::{
    Checkpoint, Journal, Logs, SessionLogs, SessionPositions, Tables, TablesPositions,
};
use crate::{Elaborator, nav, scope};

/// A point an [`Elaborator`] can be rewound to ([`Elaborator::mark`]). It
/// stays valid, and can be rewound to any number of times, until the
/// elaborator is rewound to an earlier mark; a rewind to it after that
/// panics. Released by [`Elaborator::release`] when no longer wanted.
pub struct Mark {
    checkpoint: Checkpoint,
    kernel: KernelMark,
    unit: crate::state::UnitMark,
    session: crate::state::SessionMark,
    tables: crate::state::TablesMark,
    scope: scope::Mark,
    caches: crate::state::CachesMark,
    present: crate::state::PresentationMark,
}

impl Mark {
    /// How many definitions there were.
    pub fn defs(&self) -> usize {
        self.kernel.defs()
    }
}

impl Elaborator {
    /// Where the elaborator is now, to [`Elaborator::rewind`] to later.
    /// Only between loads: not while a declaration is checked or a library
    /// file loads.
    pub fn mark(&mut self) -> Mark {
        assert!(
            self.attempt.store.metas.borrow().is_empty() && self.library_stack_is_empty(),
            "a mark in the middle of checking"
        );
        if let Some(field) = self.decl.leftover() {
            panic!("a mark in the middle of a declaration: `Decl::{field}` isn't empty");
        }
        let checkpoint = self.with_journal(|journal, logs| journal.checkpoint(logs));
        Mark {
            checkpoint,
            kernel: self.kernel.mark(),
            unit: self.unit.mark(),
            session: self.session.mark(),
            tables: self.tables.mark(self.ids()),
            scope: self.scope.mark(),
            caches: self.caches.mark(),
            present: self.present.mark(),
        }
    }

    /// Puts the elaborator back as it was at `mark`: everything declared,
    /// named, recorded or loaded since is forgotten (see the module's
    /// comment). Also after a check that stopped part way, cancelled or
    /// not.
    pub fn rewind(&mut self, mark: &Mark) {
        let Elaborator {
            kernel,
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
            present,
            // The library's files stay loaded, and their warnings with them.
            library_warnings: _,
        } = self;
        let (journal, session_logs) = session.logged();
        journal.rewind(
            &mark.checkpoint,
            &mut LoggedTables {
                nav: present.logged(),
                scope,
                tables,
                session: session_logs,
            },
        );
        let defs = mark.kernel.defs();
        kernel.rewind(&mark.kernel);
        tables.rewind(&mark.tables);
        scope.rewind(&mark.scope);
        attempt.rewind();
        decl.rewind();
        unit.rewind(&mark.unit);
        session.rewind(&mark.session);
        caches.rewind(&mark.caches, defs);
        *goals.get_mut() = Default::default();
        present.rewind(&mark.present);
    }
}

impl Elaborator {
    /// Closes `mark`'s checkpoint: what was done since it stays, and the
    /// journal stops logging for it. Only the newest mark still open
    /// (an older one is dropped by rewinding to one older still, which
    /// makes those after it unusable); panics otherwise.
    pub fn release(&mut self, mark: Mark) {
        let Mark { checkpoint, .. } = mark;
        self.with_journal(|journal, logs| journal.release(checkpoint, logs));
    }

    /// Tells the journal the unit being elaborated has changed (`Owners`
    /// says which it is now): a new segment begins (§4.8.3).
    pub(crate) fn unit_changed(&mut self) {
        let unit = self.session.owners.current();
        self.with_journal(|journal, logs| journal.set_unit(unit, logs));
    }

    /// `f` with the session's journal and the tables it covers.
    pub(crate) fn with_journal<T>(
        &mut self,
        f: impl FnOnce(&mut Journal<LogPositions>, &mut LoggedTables<'_>) -> T,
    ) -> T {
        let Elaborator {
            scope,
            tables,
            session,
            present,
            ..
        } = self;
        let (journal, session) = session.logged();
        f(
            journal,
            &mut LoggedTables {
                nav: present.logged(),
                scope,
                tables,
                session,
            },
        )
    }
}

/// The tables a [`Mark`]'s checkpoint covers: those that log their changes
/// rather than being copied (docs/proposals/elaborator-state.md §4.8.2).
/// Navigation's, while it is on, the scope's, two of [`Tables`]' and two
/// of the session's.
pub(crate) struct LoggedTables<'a> {
    nav: Option<&'a mut nav::Recorder>,
    scope: &'a mut scope::Scope,
    tables: &'a mut Tables,
    session: SessionLogs<'a>,
}

/// Where [`LoggedTables`]' logs are.
pub(crate) struct LogPositions {
    nav: Option<nav::Positions>,
    scope: scope::Positions,
    tables: TablesPositions,
    session: SessionPositions,
}

impl LogPositions {
    pub(crate) fn scope(&self) -> &scope::Positions {
        &self.scope
    }

    pub(crate) fn tables(&self) -> &TablesPositions {
        &self.tables
    }
}

impl Logs for LoggedTables<'_> {
    type Positions = LogPositions;

    fn positions(&self) -> LogPositions {
        let LoggedTables {
            nav,
            scope,
            tables,
            session,
        } = self;
        LogPositions {
            nav: nav.as_ref().map(|n| n.positions()),
            scope: scope.positions(),
            tables: tables.positions(),
            session: session.positions(),
        }
    }

    fn undo_to(&mut self, at: &LogPositions) -> usize {
        let LoggedTables {
            nav,
            scope,
            tables,
            session,
        } = self;
        let nav = match (nav, &at.nav) {
            (Some(n), Some(at)) => n.undo_to(at),
            // Turned on since: as for a mark taken without it, nothing to
            // undo.
            _ => 0,
        };
        nav + scope.undo_to(&at.scope) + tables.undo_to(&at.tables) + session.undo_to(&at.session)
    }

    fn set_generation(&mut self, g: Option<u32>) {
        let LoggedTables {
            nav,
            scope,
            tables,
            session,
        } = self;
        if let Some(n) = nav {
            n.set_generation(g);
        }
        scope.set_generation(g);
        tables.set_generation(g);
        session.set_generation(g);
    }

    fn entries(&self) -> usize {
        self.nav.as_ref().map_or(0, |n| n.entries())
            + self.scope.entries()
            + self.tables.entries()
            + self.session.entries()
    }

    fn bytes(&self) -> usize {
        self.nav.as_ref().map_or(0, |n| n.bytes())
            + self.scope.bytes()
            + self.tables.bytes()
            + self.session.bytes()
    }

    fn distinct_keys(&self) -> usize {
        self.nav.as_ref().map_or(0, |n| n.distinct_keys())
            + self.scope.distinct_keys()
            + self.tables.distinct_keys()
            + self.session.distinct_keys()
    }
}

impl Elaborator {
    /// What the session's journal has done, and holds now
    /// (docs/proposals/elaborator-state.md §4.8.7).
    pub fn journal_stats(&mut self) -> crate::state::JournalStats {
        self.with_journal(|journal, logs| journal.stats(logs))
    }
}
