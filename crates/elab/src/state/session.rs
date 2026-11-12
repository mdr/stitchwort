//! [`Session`]: project and cache bookkeeping, and statistics. What the
//! host tells the elaborator about the project (its namespaces, where
//! `include` reads from), what the check cache keeps track of, and what
//! the session counts.
//!
//! A rewind puts back the bookkeeping that later loads can change
//! ([`Session::mark`], [`Session::rewind`]); the rest only grows or counts,
//! and a rewind leaves it. What the host sets whole is shared, so a mark
//! keeps a pointer to it; the maps a load adds to are [`Logged`], put back
//! by the journal ([`Session::logged`]); the rest is small and copied.

use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_syntax::FileId;

use super::journal::{Logged, Logs};
use crate::{cache, library, project};

#[derive(Default)]
pub struct Session {
    /// The project's namespaces (`project::set_project_namespaces`). Set
    /// whole, never changed: shared with the marks.
    pub(crate) project_namespaces: Arc<BTreeSet<String>>,
    /// Every prefix of a project namespace's name, the namespace included.
    pub(crate) project_prefixes: Arc<BTreeSet<String>>,
    /// What `import N (..)` brings from each project namespace whose files
    /// parsed (`project::set_project_names`).
    pub(crate) project_names: Arc<BTreeMap<String, BTreeSet<String>>>,
    /// For each project namespace with syntax errors, where the first one is
    /// (`project::set_project_syntax_errors`): an import from it that names
    /// a declaration it no longer has says so, instead of that the name is
    /// unknown (docs/proposals/tests-with-errors.md §4.2). Set whole.
    pub(crate) project_syntax_errors: Arc<BTreeMap<String, Option<stitchwort_syntax::Span>>>,
    /// Where `include` reads from, and where each source file is in it
    /// (`project::read_include`). Without them `include` is
    /// `E-INCLUDE-UNAVAILABLE`. The host sets it as it loads a project or
    /// a file on its own, so it is put back by a rewind.
    pub(crate) include_files: Option<Rc<dyn project::IncludeFiles>>,
    pub(crate) include_locations: Logged<FileId, String>,
    /// The standard library's files, once the core is loaded
    /// (`library.rs`).
    pub(crate) library: Option<library::LibraryState>,
    /// While the core is checked, the library's names, so a doc link in the
    /// core may name a library declaration, which isn't loaded yet
    /// (`set_core_link_names`, SW-1046). Set by the host around the core's
    /// load only, so empty at every mark.
    pub(crate) core_link_names: Option<Arc<library::LibraryIndex>>,
    /// Counts the stretches of compiler-generated source, which is freed
    /// once checked so its addresses can be reused: dot calls are only
    /// remembered within one (`dot::CallKey`). Never reused, so a rewind
    /// leaves it.
    pub(crate) source_epoch: Cell<usize>,
    /// How many expressions have been elaborated standalone (the REPL's,
    /// `eval`'s): a `match` in one is lifted to a helper owned by
    /// `<input N>`, which keeps the helpers of different inputs apart.
    pub(crate) standalone_inputs: usize,
    /// For tests: how many times finding an instance has had to wait
    /// (`auto.rs`), in this session.
    pub instance_waits: Cell<usize>,
    /// What the check cache has done in this session.
    pub(crate) cache_stats: cache::Stats,
    /// For the check cache: each project namespace's sources, hashed by
    /// the host (`cache::Elaborator::set_namespace_sources`), and each
    /// namespace's key once worked out (the keys of its dependencies are
    /// part of it). The sources are set whole, and shared with the marks.
    pub(crate) namespace_sources: Arc<HashMap<String, cache::Key>>,
    pub(crate) namespace_keys: Logged<String, cache::Key>,
    /// The project namespaces whose last check had an error. A namespace
    /// that uses one is checked but not stored: its key would be keyed to
    /// the broken source, and writing it would evict the healthy entry, so
    /// restoring that source would find nothing to replay.
    pub(crate) failed_namespaces: Logged<String, ()>,
    /// The names a failed replay declared (as failures) before it failed:
    /// the namespace's first pass claims them again rather than finding
    /// them taken (`cache`, `new_module_name`). One namespace's, emptied
    /// as the next begins: a mark copies it.
    pub(crate) replayed_names: HashSet<String>,
    /// Each project namespace checked or replayed: the library files its
    /// module needs, with those of the namespaces it depends on, as
    /// `ModuleState::library_reach` (`auto`). Shared with the marks.
    pub(crate) library_reach: Rc<BTreeMap<String, Rc<BTreeSet<usize>>>>,
    /// What every unit's key holds of the library besides the text of the
    /// files it loads (`cache::Elaborator::library_interface`). Computed
    /// once.
    pub(crate) library_interface_digest: OnceCell<cache::Key>,
    /// What the postponement queue and the unifier counted.
    pub(crate) stats: Arc<Stats>,
    /// Which unit made each declaration, and which is being elaborated
    /// (docs/proposals/elaborator-state.md §4.8.4).
    pub(crate) owners: super::owners::Owners,
    /// Which declaration has each path, for the check cache. Filled in
    /// when read, cut by a rewind.
    pub(crate) paths: RefCell<super::paths::DeclPaths>,
    /// The checkpoints of the tables that log their changes (§4.8.2).
    pub(crate) journal: super::journal::Journal<crate::rewind::LogPositions>,
    /// Where the open goals' assumptions start (`assume.rs`).
    pub(crate) assumed: crate::assume::Assumed,
    /// For a declaration left unfinished because a computation it needs is
    /// stuck on open goals' assumptions: those assumptions (`assume.rs`,
    /// `Elaborator::blocked_on`). Read only for declarations the tables
    /// mark unfinished, whose row is rewritten whenever they're marked, so
    /// a rewind needn't cut it.
    pub(crate) blocked: RefCell<
        stitchwort_core::collections::HashMap<stitchwort_core::DefId, Rc<[stitchwort_core::DefId]>>,
    >,
    /// The same for a declaration whose signature waited, so it has no
    /// definition: its open goals' assumptions, by key. A namespace's names
    /// are rewritten here whenever it is checked (`fail_unchecked_names`),
    /// so a rewind needn't cut it.
    pub(crate) waiting_names: RefCell<BTreeMap<String, Rc<[stitchwort_core::DefId]>>>,
    /// For each declaration of a project namespace that has an error, or
    /// can't be checked because something it uses has one, by key: the
    /// declaration the error is in (its name, for messages) and where it
    /// is reported. Read only for a key the scope says failed, by the
    /// namespaces that use it (`E-USES-FAILED`); a namespace's keys are
    /// rewritten whenever it is checked, so a rewind needn't cut it.
    pub(crate) failed_sources: BTreeMap<String, (String, Option<stitchwort_syntax::Span>)>,
    /// The tests that couldn't be checked because they use a declaration
    /// with an error, in the order the namespaces were checked
    /// ([`crate::BrokenTest`]). A log for the host to read after a load,
    /// which clears it first; a rewind leaves it.
    pub(crate) broken_tests: Vec<crate::BrokenTest>,
    /// The declarations with errors, or waiting for one, in the same order
    /// ([`crate::FailedDecl`]); a log for the host, cleared with
    /// `broken_tests`.
    pub(crate) failed_decls: Vec<crate::FailedDecl>,
}

/// What a rewind mark keeps of a [`Session`]: the bookkeeping a later load
/// can change.
pub(crate) struct Mark {
    project_namespaces: Arc<BTreeSet<String>>,
    project_prefixes: Arc<BTreeSet<String>>,
    project_names: Arc<BTreeMap<String, BTreeSet<String>>>,
    project_syntax_errors: Arc<BTreeMap<String, Option<stitchwort_syntax::Span>>>,
    include_files: Option<Rc<dyn project::IncludeFiles>>,
    library: Option<library::LibraryState>,
    namespace_sources: Arc<HashMap<String, cache::Key>>,
    replayed_names: HashSet<String>,
    library_reach: Rc<BTreeMap<String, Rc<BTreeSet<usize>>>>,
    owners: super::owners::Mark,
    paths: super::paths::Mark,
}

impl Session {
    pub(crate) fn mark(&self) -> Mark {
        let Session {
            project_namespaces,
            project_prefixes,
            project_names,
            project_syntax_errors,
            include_files,
            library,
            namespace_sources,
            replayed_names,
            library_reach,
            owners,
            paths,
            // Its own checkpoints (`rewind.rs`), and the maps it puts back.
            journal: _,
            include_locations: _,
            namespace_keys: _,
            failed_namespaces: _,
            // Set around the core's load, so `None` here.
            core_link_names: _,
            // Counted, never reused or taken back.
            source_epoch: _,
            standalone_inputs: _,
            instance_waits: _,
            cache_stats: _,
            library_interface_digest: _,
            stats: _,
            // Checked on use (`assume.rs`).
            assumed: _,
            blocked: _,
            waiting_names: _,
            failed_sources: _,
            broken_tests: _,
            failed_decls: _,
        } = self;
        Mark {
            project_namespaces: project_namespaces.clone(),
            project_prefixes: project_prefixes.clone(),
            project_names: project_names.clone(),
            project_syntax_errors: project_syntax_errors.clone(),
            include_files: include_files.clone(),
            library: library.clone(),
            namespace_sources: namespace_sources.clone(),
            replayed_names: replayed_names.clone(),
            library_reach: library_reach.clone(),
            owners: owners.mark(),
            paths: paths.borrow().mark(),
        }
    }

    pub(crate) fn rewind(&mut self, mark: &Mark) {
        let Session {
            project_namespaces,
            project_prefixes,
            project_names,
            project_syntax_errors,
            include_files,
            library,
            namespace_sources,
            replayed_names,
            library_reach,
            owners,
            paths,
            journal: _,
            include_locations: _,
            namespace_keys: _,
            failed_namespaces: _,
            core_link_names: _,
            source_epoch: _,
            standalone_inputs: _,
            instance_waits: _,
            cache_stats: _,
            library_interface_digest: _,
            stats: _,
            // Checked on use (`assume.rs`).
            assumed: _,
            blocked: _,
            waiting_names: _,
            failed_sources: _,
            broken_tests: _,
            failed_decls: _,
        } = self;
        *project_namespaces = mark.project_namespaces.clone();
        *project_prefixes = mark.project_prefixes.clone();
        *project_names = mark.project_names.clone();
        *project_syntax_errors = mark.project_syntax_errors.clone();
        *include_files = mark.include_files.clone();
        *library = mark.library.clone();
        *namespace_sources = mark.namespace_sources.clone();
        *replayed_names = mark.replayed_names.clone();
        *library_reach = mark.library_reach.clone();
        owners.rewind(&mark.owners);
        paths.get_mut().rewind(&mark.paths);
    }
}

/// Where [`Session`]'s logged maps' logs are.
pub(crate) struct Positions {
    include_locations: usize,
    namespace_keys: usize,
    failed_namespaces: usize,
}

/// The maps of a [`Session`] its journal puts back: split from it, as the
/// journal is in the session too.
pub(crate) struct SessionLogs<'a> {
    include_locations: &'a mut Logged<FileId, String>,
    namespace_keys: &'a mut Logged<String, cache::Key>,
    failed_namespaces: &'a mut Logged<String, ()>,
}

impl Session {
    /// The journal, and the session's maps it puts back.
    pub(crate) fn logged(
        &mut self,
    ) -> (
        &mut super::journal::Journal<crate::rewind::LogPositions>,
        SessionLogs<'_>,
    ) {
        let Session {
            journal,
            include_locations,
            namespace_keys,
            failed_namespaces,
            ..
        } = self;
        (
            journal,
            SessionLogs {
                include_locations,
                namespace_keys,
                failed_namespaces,
            },
        )
    }
}

impl Logs for SessionLogs<'_> {
    type Positions = Positions;

    fn positions(&self) -> Positions {
        Positions {
            include_locations: self.include_locations.position(),
            namespace_keys: self.namespace_keys.position(),
            failed_namespaces: self.failed_namespaces.position(),
        }
    }

    fn undo_to(&mut self, at: &Positions) -> usize {
        let Positions {
            include_locations,
            namespace_keys,
            failed_namespaces,
        } = at;
        self.include_locations.undo_to(include_locations)
            + self.namespace_keys.undo_to(namespace_keys)
            + self.failed_namespaces.undo_to(failed_namespaces)
    }

    fn set_generation(&mut self, g: Option<u32>) {
        self.include_locations.set_generation(g);
        self.namespace_keys.set_generation(g);
        self.failed_namespaces.set_generation(g);
    }

    fn entries(&self) -> usize {
        self.include_locations.entries()
            + self.namespace_keys.entries()
            + self.failed_namespaces.entries()
    }

    fn bytes(&self) -> usize {
        self.include_locations.bytes()
            + self.namespace_keys.bytes()
            + self.failed_namespaces.bytes()
    }

    fn distinct_keys(&self) -> usize {
        self.include_locations.distinct_keys()
            + self.namespace_keys.distinct_keys()
            + self.failed_namespaces.distinct_keys()
    }
}

/// The queue's and the unifier's counters, attempts undone included, for
/// `STITCHWORT_TIMINGS` (`timings.rs`) and the stages after this one
/// (docs/proposals/postponement.md, "As built (stage 1)" to "(stage 3)"):
/// items queued, resumed, defaulted and reported stuck; items that reached
/// the end of their application still waiting (`crossed W1`, the stage-6
/// trigger); comparisons that failed at an unfilled placeholder (`met
/// unfilled`, its other half, `Stats::met_unfilled`); fills whose
/// placeholder unification had solved first (`solved first`), and of
/// those, solved by comparing two calls' arguments (`lossy`, the caveat to
/// D2016's P1); fills that disagreed with that solution; fills whose term
/// couldn't be written as a call of the placeholder, so zonking reads the
/// solution back (`read back`); resumptions that met another unknown and
/// waited again (`requeued`); and `.field`s queued with their receiver
/// kept as a term (`kept`), of which those whose receiver made a choice
/// from an unknown (`kept chose`, invariant 6; 0 expected); and
/// elaborations run a second time with number literals last (`retried`,
/// `check::retrying`, which K4 makes unneeded); and comparisons queued to
/// wait for unknowns the queue still has to settle (`waited`, stage 6); and
/// generalising `match`es that waited for an unknown their generalisation
/// would read (`match waited`, step 4.0 of stage 4), and motive checks left
/// for lifting (`motive later`); and, step 4.2, `rewrite` rules whose own
/// checks still waited after resuming (`rule settled`) and the defaults
/// applied to them (`rule defaulted`), `rewrite`s and `cases` that waited
/// (`tactic waited`), and runs of `omega`, `ring` and `auto` on a goal
/// holding an unknown the declaration will still settle, and of those the
/// failures (`… on pending`, `… failed on pending`); and, for stage 5, the
/// "infer the other side" catch it keeps (`leaf uninferred`).
///
/// Per session; `STITCHWORT_TIMINGS` adds up the sessions of the process,
/// each when it is dropped (`timings::add_queue_counts`). The counters are in
/// the order [`Stats::counts`] lists (the order printed).
#[derive(Default)]
pub(crate) struct Stats {
    pub(crate) queued: AtomicUsize,
    pub(crate) resumed: AtomicUsize,
    pub(crate) defaulted: AtomicUsize,
    pub(crate) stuck: AtomicUsize,
    pub(crate) crossed: AtomicUsize,
    /// Comparisons that failed at a pair one side of which is headed by an
    /// unfilled placeholder (stuck there, or put aside on it): the second
    /// half of the stage-6 trigger (docs/proposals/postponement.md §5.13).
    pub(crate) met_unfilled: AtomicUsize,
    pub(crate) solved_first: AtomicUsize,
    pub(crate) lossy: AtomicUsize,
    pub(crate) disagreed: AtomicUsize,
    pub(crate) read_back: AtomicUsize,
    pub(crate) requeued: AtomicUsize,
    pub(crate) kept: AtomicUsize,
    pub(crate) kept_chose: AtomicUsize,
    pub(crate) retried: AtomicUsize,
    pub(crate) leaf_uninferred: AtomicUsize,
    pub(crate) waited: AtomicUsize,
    pub(crate) match_waited: AtomicUsize,
    pub(crate) motive_later: AtomicUsize,
    pub(crate) rule_settled: AtomicUsize,
    pub(crate) rule_defaulted: AtomicUsize,
    pub(crate) tactic_waited: AtomicUsize,
    pub(crate) omega_pending: AtomicUsize,
    pub(crate) omega_pending_failed: AtomicUsize,
    pub(crate) ring_pending: AtomicUsize,
    pub(crate) ring_pending_failed: AtomicUsize,
    pub(crate) auto_pending: AtomicUsize,
    pub(crate) auto_pending_failed: AtomicUsize,
}

/// How many counters [`Stats`] has.
pub(crate) const STAT_COUNT: usize = 27;

impl Stats {
    /// One more of `counter`.
    pub(crate) fn bump(counter: &AtomicUsize) {
        counter.fetch_add(1, Ordering::Relaxed);
    }

    /// Every counter with its name, in the order `STITCHWORT_TIMINGS`
    /// prints them.
    pub(crate) fn counts(&self) -> [(&'static str, usize); STAT_COUNT] {
        let Stats {
            queued,
            resumed,
            defaulted,
            stuck,
            crossed,
            met_unfilled,
            solved_first,
            lossy,
            disagreed,
            read_back,
            requeued,
            kept,
            kept_chose,
            retried,
            leaf_uninferred,
            waited,
            match_waited,
            motive_later,
            rule_settled,
            rule_defaulted,
            tactic_waited,
            omega_pending,
            omega_pending_failed,
            ring_pending,
            ring_pending_failed,
            auto_pending,
            auto_pending_failed,
        } = self;
        [
            ("queued", queued.load(Ordering::Relaxed)),
            ("resumed", resumed.load(Ordering::Relaxed)),
            ("defaulted", defaulted.load(Ordering::Relaxed)),
            ("stuck", stuck.load(Ordering::Relaxed)),
            ("crossed W1", crossed.load(Ordering::Relaxed)),
            ("met unfilled", met_unfilled.load(Ordering::Relaxed)),
            ("solved first", solved_first.load(Ordering::Relaxed)),
            ("lossy", lossy.load(Ordering::Relaxed)),
            ("disagreed", disagreed.load(Ordering::Relaxed)),
            ("read back", read_back.load(Ordering::Relaxed)),
            ("requeued", requeued.load(Ordering::Relaxed)),
            ("kept", kept.load(Ordering::Relaxed)),
            ("kept chose", kept_chose.load(Ordering::Relaxed)),
            ("retried", retried.load(Ordering::Relaxed)),
            ("leaf uninferred", leaf_uninferred.load(Ordering::Relaxed)),
            ("waited", waited.load(Ordering::Relaxed)),
            ("match waited", match_waited.load(Ordering::Relaxed)),
            ("motive later", motive_later.load(Ordering::Relaxed)),
            ("rule settled", rule_settled.load(Ordering::Relaxed)),
            ("rule defaulted", rule_defaulted.load(Ordering::Relaxed)),
            ("tactic waited", tactic_waited.load(Ordering::Relaxed)),
            ("omega on pending", omega_pending.load(Ordering::Relaxed)),
            (
                "omega failed on pending",
                omega_pending_failed.load(Ordering::Relaxed),
            ),
            ("ring on pending", ring_pending.load(Ordering::Relaxed)),
            (
                "ring failed on pending",
                ring_pending_failed.load(Ordering::Relaxed),
            ),
            ("auto on pending", auto_pending.load(Ordering::Relaxed)),
            (
                "auto failed on pending",
                auto_pending_failed.load(Ordering::Relaxed),
            ),
        ]
    }
}
