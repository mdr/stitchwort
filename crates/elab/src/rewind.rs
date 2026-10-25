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
//!   state, the project's tables, navigation, the dot-call caches): a copy
//!   taken at the mark is put back. These are the tables in which a later
//!   load can change an older row (`check-cache.md` stage 1, point 3), so
//!   lengths aren't enough. Copying them costs a few milliseconds per
//!   mark (measured in the note's "As built").
//!
//! The per-declaration state is emptied (after a cancelled check it may be
//! half-full). Settings (limits, test switches, the check cache's store and
//! its statistics) stay as they are: they say how to check, not what was
//! checked.
//!
//! [`Elaborator::rewind`] names every field of the elaborator, so a new
//! field doesn't compile until it says how it rewinds; the differential test
//! (`crates/driver/tests/rewind.rs`) catches a field that rewinds wrongly.

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::GlobalsMark;
use stitchwort_core::{DataId, DefId};
use stitchwort_syntax::{Diagnostic, FileId, Span};

use crate::{Elaborator, cache, dot, effects, interfaces, library, module, nav, project, scope};

/// A point an [`Elaborator`] can be rewound to ([`Elaborator::mark`]). It
/// stays valid, and can be rewound to any number of times, until the
/// elaborator is rewound to an earlier mark.
pub struct Mark {
    globals: GlobalsMark,
    tests: usize,
    scope: scope::Scope,
    namespace_root: String,
    project_namespaces: BTreeSet<String>,
    project_prefixes: BTreeSet<String>,
    project_names: BTreeMap<String, BTreeSet<String>>,
    namespace_defs: BTreeMap<String, std::ops::Range<usize>>,
    prelude_defs: usize,
    file_mode: Option<project::FileModeContext>,
    include_files: Option<std::rc::Rc<dyn project::IncludeFiles>>,
    include_locations: HashMap<FileId, String>,
    next_include_location: Option<String>,
    loading_prelude: bool,
    library: Option<library::LibraryState>,
    abilities: usize,
    module: module::ModuleState,
    warnings: Vec<Diagnostic>,
    dot_heads: HashMap<dot::CallKey, (dot::TyHead, DefId)>,
    dot_failed: HashSet<(dot::CallKey, usize, usize)>,
    recursion: Option<effects::Recursion>,
    lifted: usize,
    local_helpers: Vec<(String, DefId, Span)>,
    helper_keys: HashSet<String>,
    instances: HashMap<(DataId, DataId), interfaces::InstanceInfo>,
    nav: Option<nav::Recorder>,
    namespace_sources: HashMap<String, cache::Key>,
    namespace_keys: HashMap<String, cache::Key>,
    replayed_names: HashSet<String>,
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
        Mark {
            globals: self.globals.mark(),
            tests: self.tests.len(),
            scope: self.scope.clone(),
            namespace_root: self.namespace_root.clone(),
            project_namespaces: self.project_namespaces.clone(),
            project_prefixes: self.project_prefixes.clone(),
            project_names: self.project_names.clone(),
            namespace_defs: self.namespace_defs.clone(),
            prelude_defs: self.prelude_defs,
            file_mode: self.file_mode.clone(),
            include_files: self.include_files.clone(),
            include_locations: self.include_locations.clone(),
            next_include_location: self.next_include_location.clone(),
            loading_prelude: self.loading_prelude,
            library: self.library.clone(),
            abilities: self.abilities.len(),
            module: self.module.clone(),
            warnings: self.warnings.clone(),
            dot_heads: self.dot_heads.borrow().clone(),
            dot_failed: self.dot_failed.borrow().clone(),
            recursion: self.recursion.clone(),
            lifted: self.lifted.len(),
            local_helpers: self.local_helpers.clone(),
            helper_keys: self.helper_keys.clone(),
            instances: self.instances.clone(),
            nav: self.nav.as_ref().map(|n| n.borrow().clone()),
            namespace_sources: self.namespace_sources.clone(),
            namespace_keys: self.namespace_keys.clone(),
            replayed_names: self.replayed_names.clone(),
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
            sides_capture,
            scope,
            namespace_root,
            project_namespaces,
            project_prefixes,
            project_names,
            namespace_defs,
            prelude_defs,
            file_mode,
            include_files,
            include_locations,
            next_include_location,
            obligations,
            row_metas,
            row_constraints,
            defaulted,
            char_patterns,
            char_proofs,
            loading_prelude,
            rewrite_budget: _,
            library,
            library_tests: _,
            abilities,
            limits: _,
            numbers_as_succ: _,
            module,
            warnings,
            lambda_warnings,
            branch_errors,
            arm_reach,
            no_propagation,
            bare_rows_pure,
            late_literals,
            dot_heads,
            dot_failed,
            condition,
            app_expected,
            decreasing,
            recursion,
            records,
            no_eq,
            no_show,
            no_ord,
            drafts,
            standalone_inputs: _,
            glue: _,
            arounds,
            lifted,
            owner,
            body_type,
            local_keys,
            preadmitted,
            local_helpers,
            helper_keys,
            local_metas,
            goals,
            proof_holes,
            hole_log: _,
            cong_candidates,
            result_heads,
            performs,
            interfaces,
            instances,
            data_owners,
            instance_steps,
            instance_budget: _,
            uniform_operators: _,
            instance_waits: _,
            in_instance_signature,
            nav,
            check_cache: _,
            cache_stats: _,
            namespace_sources,
            namespace_keys,
            namespace_capture,
            skip_navigation_walk,
            replayed_names,
            fail_replays_late: _,
            recheck_namespaces: _,
            include_trace,
            library_digest: _,
            // Settings, and a log that only grows.
            counterexample_runner: _,
            no_counterexamples: _,
            untimed_counterexamples: _,
            counterexample_log: _,
        } = self;
        let defs = mark.globals.defs();
        let datas = mark.globals.datas();
        globals.rewind(&mark.globals);
        tests.truncate(mark.tests);
        *sides_capture.get_mut() = Default::default();
        *scope = mark.scope.clone();
        *namespace_root = mark.namespace_root.clone();
        *project_namespaces = mark.project_namespaces.clone();
        *project_prefixes = mark.project_prefixes.clone();
        *project_names = mark.project_names.clone();
        *namespace_defs = mark.namespace_defs.clone();
        *prelude_defs = mark.prelude_defs;
        *file_mode = mark.file_mode.clone();
        *include_files = mark.include_files.clone();
        *include_locations = mark.include_locations.clone();
        *next_include_location = mark.next_include_location.clone();
        obligations.get_mut().clear();
        row_metas.get_mut().clear();
        row_constraints.get_mut().clear();
        defaulted.get_mut().clear();
        char_patterns.get_mut().clear();
        char_proofs.get_mut().clear();
        *loading_prelude = mark.loading_prelude;
        *library = mark.library.clone();
        abilities.truncate(mark.abilities);
        *module = mark.module.clone();
        *warnings = mark.warnings.clone();
        lambda_warnings.get_mut().clear();
        branch_errors.get_mut().clear();
        *arm_reach.get_mut() = Default::default();
        no_propagation.set(0);
        bare_rows_pure.set(false);
        late_literals.set(0);
        *dot_heads.get_mut() = mark.dot_heads.clone();
        *dot_failed.get_mut() = mark.dot_failed.clone();
        condition.set(0);
        *app_expected.get_mut() = None;
        *decreasing.get_mut() = None;
        *recursion = mark.recursion.clone();
        records.retain(|d, _| d.0 < datas);
        no_eq.retain(|d, _| d.0 < datas);
        no_show.retain(|d, _| d.0 < datas);
        no_ord.retain(|d, _| d.0 < datas);
        interfaces.retain(|d, _| d.0 < datas);
        data_owners.retain(|d, _| d.0 < datas);
        drafts.get_mut().clear();
        *arounds.get_mut() = Default::default();
        lifted.truncate(mark.lifted);
        owner.get_mut().clear();
        *body_type.get_mut() = None;
        local_keys.get_mut().clear();
        preadmitted.get_mut().clear();
        *local_helpers = mark.local_helpers.clone();
        *helper_keys = mark.helper_keys.clone();
        local_metas.get_mut().clear();
        *goals.get_mut() = Default::default();
        proof_holes.get_mut().clear();
        cong_candidates.get_mut().clear();
        result_heads.get_mut().truncate(defs);
        performs.get_mut().retain(|(id, ..), _| id.0 < defs);
        *instances = mark.instances.clone();
        instance_steps.get_mut().clear();
        in_instance_signature.set(false);
        if let (Some(nav), Some(at_mark)) = (nav.as_mut(), &mark.nav) {
            *nav.get_mut() = at_mark.clone();
        }
        *namespace_sources = mark.namespace_sources.clone();
        *namespace_keys = mark.namespace_keys.clone();
        *namespace_capture = None;
        *skip_navigation_walk = false;
        *replayed_names = mark.replayed_names.clone();
        include_trace.get_mut().clear();
    }
}
