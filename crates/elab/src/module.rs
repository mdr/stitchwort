//! Whole-module scope (docs/proposals/mutual-recursion.md §8.1): every
//! top-level name is visible throughout its module, whatever the order of
//! the declarations.
//!
//! [`Elaborator::elaborate_module`] works in three steps:
//!
//! 1. **Names.** Every top-level name (definitions, data types and their
//!    constructors, abilities and their operations) is entered in the name
//!    table first, as [`Global::Unchecked`], reporting duplicates. Names
//!    without a qualifier first, then the library's imports, then qualified
//!    names (whose qualifier may need the others), then imports of the
//!    module's own namespaces (docs/proposals/namespaces.md §5).
//! 2. **Dependencies.** For each declaration, the module declarations it
//!    refers to: its *free* names, so a pattern variable, a lambda or `let`
//!    binder or an implicit parameter called `f` doesn't make a dependency on
//!    a top-level `f`. A constructor depends on its data type, an operation
//!    on its ability. An `auto` argument is no reference (the procedure that
//!    proves it isn't known yet); a procedure passed explicitly is.
//! 3. **Order.** The declarations are split into strongly connected
//!    components, and checked in dependency order, earliest in the source
//!    first among those whose dependencies are checked. So a module with no
//!    forward references is checked in source order, as before. A component
//!    of several definitions (or one that calls itself) is a group of
//!    definitions that call each other: all their signatures are checked,
//!    then all their bodies, and the kernel admits them together
//!    (`define_group`). A component of several data types is a group of data
//!    types whose constructors mention each other: all their headers are
//!    checked, then all their constructors, and the kernel admits them
//!    together (`define_data_group`). A cycle mixing data types (or
//!    abilities) with definitions, or including an ability, is refused.
//!
//! Instances (docs/proposals/interfaces.md §5.6) are found by type, not by
//! name, so no reference says what uses one. Every other definition and
//! test of the module is checked after every instance of it that doesn't
//! itself depend on that declaration ([`Elaborator::instance_edges`]); and
//! an instance after another one of the module whose interface it mentions
//! or has as a superclass.
//!
//! Untrusted: the kernel refuses a group that refers to an unfinished
//! declaration outside it, so a mistake here can't split a cycle.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::State;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, ResourceError};
use stitchwort_syntax::ast::{self, BinOp, Clause, Decl, Expr, Module, Pattern};
use stitchwort_syntax::{Diagnostic, FileId, Severity, Span};

use crate::project::SourceUnit;
use crate::{BrokenTest, Elaborator, Global, error, goals, interfaces};

/// What a declaration of the module is.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Kind {
    Data,
    Ability,
    Def,
    Test,
}

/// Where a declaration is in being checked.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Status {
    /// Not checked yet.
    Waiting,
    Checked,
    Failed,
    /// Failed without an error: it has an open goal (`?`), or uses
    /// something that has (docs/proposals/lsp-goal-holes.md, D636). To the
    /// kernel it's failed like any other.
    Unfinished,
}

impl Status {
    /// Failed, with errors or unfinished: not checked by the kernel.
    pub(crate) fn failed(self) -> bool {
        matches!(self, Status::Failed | Status::Unfinished)
    }
}

/// What part of a declaration is being elaborated, which decides what a
/// reference to an unchecked declaration of the same component means.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(crate) enum Phase {
    /// A data type's parameters and universe.
    Header,
    /// A data type's constructors.
    Fields,
    /// A definition's signature.
    Signature,
    /// A definition's equations, a test, or anything else.
    #[default]
    Body,
}

/// A reference from one declaration to another.
#[derive(Clone, Debug)]
pub(crate) struct Dep {
    pub item: usize,
    /// Where the name is used.
    pub span: Span,
    /// In a definition's signature, or a data type's parameters or universe.
    pub in_header: bool,
    /// For dot notation, which may not mean this declaration: why it might.
    pub speculative: Option<String>,
}

/// A declaration of the module being elaborated.
#[derive(Clone)]
pub(crate) struct ItemInfo {
    /// Its name, for messages (a test's is its label).
    pub name: String,
    /// Where it's declared: the name.
    pub span: Span,
    /// The index of its first declaration in the module.
    pub position: usize,
    /// Which of the module's files it's in (an index into
    /// [`ModuleState::files`]).
    pub file: usize,
    pub kind: Kind,
    /// `type Name = …`, which may not be recursive (`E-SYNONYM-CYCLE`).
    pub synonym: bool,
    pub deps: Vec<Dep>,
    /// Its strongly connected component.
    pub component: usize,
    pub status: Status,
    /// A definition whose type ends in `Decidable …`: something `auto`
    /// might have used.
    pub decides: bool,
    /// A definition whose written type is a function type, which `W-LAMBDA-SHADOW`
    /// needs to know before the definition is checked.
    pub function: bool,
    /// Declared with `instance`.
    pub instance: bool,
    /// For an instance: what the head of its type names, as far as names
    /// tell before anything is checked (its interface).
    pub interface: Option<Global>,
    /// For an instance: what the head of the type it's for names (`Item` in
    /// `DecEq Item`), the same way.
    pub head: Option<Global>,
    /// It failed by running out of resources, or by using a declaration
    /// that did.
    pub ran_out: bool,
}

/// One file of the module being elaborated.
#[derive(Clone)]
pub(crate) struct FileInfo {
    pub id: Option<FileId>,
    /// Its display name, for messages.
    pub name: String,
}

/// The module being elaborated, and what's being checked in it.
#[derive(Clone, Default)]
pub(crate) struct ModuleState {
    pub items: Vec<ItemInfo>,
    /// The module's files, sorted by display name.
    pub files: Vec<FileInfo>,
    /// The file whose imports name lookup uses while no item is being
    /// elaborated (registering names, the dependency pre-pass).
    pub file: Option<usize>,
    /// The module's namespace, if it has one.
    pub namespace: Option<String>,
    /// In a project: the namespaces this one depends on, in canonical order.
    /// `None` in file mode.
    pub closure: Option<Vec<String>>,
    /// The library files this module's references need, with the files
    /// those need, worked out from the references alone, never from what
    /// happens to be loaded: the files whose decision procedures `auto`
    /// tries (`auto::earlier_candidates`). `None` without a library.
    pub library_reach: Option<std::rc::Rc<std::collections::BTreeSet<usize>>>,
    /// The first definition and test the module declares.
    pub first_def: usize,
    pub first_test: usize,
    /// The items of the component being checked.
    pub current: Vec<usize>,
    /// The item being elaborated.
    pub item: Option<usize>,
    pub phase: Phase,
    /// The item that declared each definition of this module
    /// ([`ModuleState::note_def`]).
    pub def_items: HashMap<DefId, usize>,
    /// The definitions each item declared: [`Self::def_items`] the other
    /// way round.
    pub item_defs: HashMap<usize, Vec<DefId>>,
    /// The key of every name the module declares.
    pub names: HashSet<String>,
    /// The open goals' assumptions each unfinished item waits for: it
    /// wasn't checked, because something it computes with is stuck on
    /// them, or it uses what waits for them.
    pub waiting: HashMap<usize, Rc<[DefId]>>,
    /// For each item that failed with errors: the declaration the errors
    /// come from (itself, or what it uses, maybe in another namespace), by
    /// name, and where the first one is reported
    /// ([`Elaborator::note_error_source`]).
    pub error_sources: HashMap<usize, (String, Option<Span>)>,
    /// The key each item declares under, by item.
    pub item_keys: HashMap<usize, String>,
    /// The names of the module's declarations that didn't parse
    /// (`Module::failed`), by key: the name, and where its syntax error is.
    pub parse_failed: HashMap<String, (String, Option<Span>)>,
    /// The items that weren't checked because they use a declaration of
    /// another namespace that failed, directly or through an item that
    /// waits for one: that declaration's key (`E-USES-FAILED`).
    pub waits_elsewhere: HashMap<usize, String>,
    /// Data types (by item) whose `Ord` is derived once their module's own
    /// `DecEq` instance is checked.
    pub ord_after_dec_eq: HashMap<usize, DataId>,
    /// For navigation: the names written in the library's tests, which
    /// aren't elaborated (they run under the library test target), with
    /// their files; noted as references once the module is checked.
    pub test_names: Vec<(usize, ast::Name)>,
}

impl ModuleState {
    /// Notes that `item` declared definition `id`.
    pub fn note_def(&mut self, id: DefId, item: usize) {
        if let Some(old) = self.def_items.insert(id, item) {
            if old == item {
                return;
            }
            if let Some(defs) = self.item_defs.get_mut(&old) {
                defs.retain(|d| *d != id);
            }
        }
        self.item_defs.entry(item).or_default().push(id);
    }

    /// Whether `item` is in the component being checked.
    pub fn in_current(&self, item: usize) -> bool {
        self.current.contains(&item)
    }
}

/// A declaration, with its equations if it's a signature.
struct Item<'m> {
    decl: &'m Decl,
    equations: &'m [Decl],
    position: usize,
}

/// Whether an `E-RESOURCE` message is for running out of evaluation steps
/// or of recursion depth.
fn is_steps_or_depth(message: &str) -> bool {
    [ResourceError::Work, ResourceError::Depth]
        .iter()
        .any(|e| message.ends_with(&e.to_string()))
}

impl Elaborator {
    /// Elaborates and checks every declaration of one file, continuing past
    /// errors. Declarations may refer to each other in any order.
    pub fn elaborate_module(&mut self, module: &Module) -> Vec<Diagnostic> {
        let namespace = match &module.namespace {
            Some(decl) if !self.unit.loading_prelude => {
                if let Err(d) = self.check_namespace_name(decl) {
                    return vec![d];
                }
                Some(decl.path.text.as_str())
            }
            _ => None,
        };
        let unit = SourceUnit {
            file: None,
            name: "",
            module,
        };
        self.elaborate_namespace(namespace, &[unit], None)
    }

    /// Elaborates the files of namespace `namespace` as one module
    /// (docs/proposals/multi-file.md §4.4). `files` must be sorted by
    /// display name and all have `namespace` as their namespace line.
    /// `closure` is `None` in file mode; in a project, the namespaces this
    /// one depends on, in canonical order.
    pub fn elaborate_namespace(
        &mut self,
        namespace: Option<&str>,
        files: &[SourceUnit],
        closure: Option<&[String]>,
    ) -> Vec<Diagnostic> {
        // Its declarations' rows in the tables are its own to write.
        self.session.owners.begin(self.ids());
        self.unit_changed();
        // A project namespace may come from the check cache (`cache`).
        let cached = self.namespace_cache_key(namespace, closure);
        let run = |e: &mut Self| match (&cached, namespace, closure) {
            (Some((unit, key)), Some(ns), Some(closure)) => {
                e.elaborate_namespace_cached(ns, files, closure, unit, key)
            }
            _ => (
                e.elaborate_namespace_untimed(namespace, files, closure),
                false,
            ),
        };
        if !crate::timings::enabled() {
            return run(self).0;
        }
        crate::timings::begin(&self.ev());
        let (diagnostics, hit) = run(self);
        let label = namespace
            .map(str::to_string)
            .or_else(|| files.first().map(|f| f.name.to_string()))
            .filter(|l| !l.is_empty())
            .unwrap_or_else(|| {
                if self.unit.loading_prelude {
                    "core"
                } else {
                    "(file)"
                }
                .to_string()
            });
        let label = if hit {
            format!("{label} (cached)")
        } else {
            label
        };
        crate::timings::end(&self.ev(), label);
        diagnostics
    }

    pub(crate) fn elaborate_namespace_untimed(
        &mut self,
        namespace: Option<&str>,
        files: &[SourceUnit],
        closure: Option<&[String]>,
    ) -> Vec<Diagnostic> {
        // A namespace has its own scope, so its own congruence lemmas.
        self.caches.cong_candidates.borrow_mut().clear();
        // User code is elaborated only once every built-in is bound
        // (docs/proposals/namespaces.md §4.7).
        if !self.unit.loading_prelude
            && let Err(d) = stitchwort_core::registry::check_complete_core(&self.ev())
        {
            return vec![d];
        }
        match namespace {
            Some(ns) if !self.unit.loading_prelude => {
                self.unit.namespace_root = format!("{ns}.");
                self.unit.module_path = "".into();
            }
            _ => {
                self.unit.namespace_root = String::new();
                self.unit.module_path = if self.unit.loading_prelude {
                    "Std"
                } else {
                    "Main"
                }
                .into();
            }
        }
        for f in files {
            self.probe_declaration(f.module);
        }
        let mut diagnostics: Vec<(usize, Diagnostic)> = Vec::new();
        let mut first_test = self.tables.tests.len();
        self.unit.module = ModuleState {
            files: files
                .iter()
                .map(|f| FileInfo {
                    id: f.file,
                    name: f.name.to_string(),
                })
                .collect(),
            namespace: namespace.map(str::to_string),
            closure: closure.map(<[String]>::to_vec),
            first_def: self.kernel.env.defs().len(),
            first_test,
            ..ModuleState::default()
        };
        // Until set below, after the loads: not the last module's.
        self.unit.omega_for_auto = false;
        self.scope.clear_imports();
        if !std::mem::take(&mut self.unit.skip_navigation_walk) {
            self.walk_for_navigation(&files.iter().map(|f| f.module).collect::<Vec<_>>());
        }
        let (items, decl_spans) = self.collect(files, &mut diagnostics);
        // Claimed again by now, if this follows a failed replay.
        self.session.replayed_names.clear();
        let needs = self.dependencies(&items);
        self.set_library_reach(&needs);
        // For the check cache: the names collected, before the library
        // files load (`cache`).
        self.capture_before_needs(&needs);
        // Library files this module uses load first, so what it names is
        // checked before it is (docs/proposals/std-library.md §4.3).
        // The core's equations a library file names (`equations.rs`).
        // (Failing here, a name is unknown where it's used.)
        if !self.library_stack_is_empty() {
            let _ = self.ensure_equations(&needs.equations);
        }
        if !needs.files.is_empty() || !needs.dots.is_empty() || !needs.equations.is_empty() {
            let loaded = if self.library_stack_is_empty() {
                self.load_needs(&needs)
            } else {
                // A library file's own files load before it does, so this
                // is a cycle, or a reference the analysis missed. (Its dot
                // calls' files are among its edges, worked out when the
                // index was built; one missed is reported where it's used.)
                match self.unloaded_needs(&needs.files) {
                    errors if errors.is_empty() => Ok(()),
                    errors => Err(errors),
                }
            };
            if let Err(errors) = loaded {
                self.fail_unchecked_names();
                return errors;
            }
            // Not the definitions and tests the files made.
            self.unit.module.first_def = self.kernel.env.defs().len();
            first_test = self.tables.tests.len();
            self.unit.module.first_test = first_test;
        }
        self.capture_after_needs();
        // After the loads: each library file loaded sets its own.
        self.unit.omega_for_auto = self.needs_reach_omega(&needs);
        // The core and the library are written in an order that works,
        // instances after what the rest of them uses: their uses of syntax
        // (`if`, `<=`) refer to declarations no name does.
        if !self.unit.loading_prelude {
            self.instance_edges(&items);
        }
        let order = self.components();

        let skipped_theorems = namespace.and_then(|ns| self.options.skip_theorems.get(ns).cloned());
        for component in order {
            // A theorem nothing being checked needs (`check --only`).
            if let Some(skip) = &skipped_theorems
                && component.iter().all(|&i| {
                    matches!(
                        items[i].decl,
                        Decl::Signature { name, theorem: true, .. } if skip.contains(&name.text)
                    )
                })
            {
                continue;
            }
            // Each component is one operation, with its own resource limits.
            let saved = self.kernel.machine.budget.start(self.options.limits);
            self.unit.module.current = component.clone();
            let before = diagnostics.len();
            let (defs_before, datas_before) =
                (self.kernel.env.defs().len(), self.kernel.env.datas().len());
            // Goals from before (an expression typed in) aren't this
            // component's.
            self.clear_goals();
            self.decl.failed_mentioned.set(false);
            self.decl.stuck_on_goal.take();
            goals::take_used_unfinished();
            take_failed_used();
            let timed = crate::timings::enabled();
            if timed {
                crate::timings::decl_begin(&self.ev());
            }
            self.glued(|e| e.check_component(&items, &component, &mut diagnostics));
            self.kernel.machine.budget.restore(saved);
            if timed {
                let label = self.component_label(&items, &component);
                crate::timings::decl_end(&self.ev(), label);
            }
            let ran_out = diagnostics[before..]
                .iter()
                .any(|(_, d)| d.code == "E-RESOURCE");
            self.blame_failed_dependency(&component, before, diagnostics.as_mut_slice());
            let ran_out = ran_out || self.blamed_on_ran_out(&component, &diagnostics[before..]);
            for &i in &component {
                self.unit.module.items[i].ran_out = ran_out;
            }
            // The open goals, printed while their metavariables are solved.
            let goals = self.take_goals();
            let errors: Vec<&str> = diagnostics[before..]
                .iter()
                .filter(|(_, d)| d.severity == Severity::Error)
                .map(|(_, d)| d.code)
                .collect();
            let failed = !errors.is_empty()
                || component
                    .iter()
                    .any(|i| self.unit.module.items[*i].status.failed());
            // Unfinished, not wrong: the only errors stand for open goals
            // (`goals::UNFINISHED`), which aren't reported as errors (D636).
            let unfinished = !errors.is_empty() && errors.iter().all(|c| *c == goals::UNFINISHED);
            // Checked by the kernel assuming its goals, or those of what it
            // uses, hold: still not finished (`assume.rs`).
            let relying = !failed && self.mark_relying(&component, defs_before, datas_before);
            for &i in &component {
                self.unit.module.items[i].status = match (failed, unfinished) {
                    (false, _) if relying => Status::Unfinished,
                    (false, _) => Status::Checked,
                    (true, true) => Status::Unfinished,
                    (true, false) => Status::Failed,
                };
            }
            let rest = diagnostics.split_off(before);
            diagnostics.extend(
                rest.into_iter()
                    .filter(|(_, d)| d.code != goals::UNFINISHED),
            );
            let used_failed = take_failed_used();
            if failed && !unfinished {
                self.note_error_source(&items, &component, &diagnostics[before..], &used_failed);
                // Waiting for another namespace's error, which is reported
                // there, and once per file here (`E-USES-FAILED`).
                if component
                    .iter()
                    .all(|i| self.unit.module.waits_elsewhere.contains_key(i))
                {
                    let rest = diagnostics.split_off(before);
                    diagnostics.extend(
                        rest.into_iter()
                            .filter(|(_, d)| d.severity != Severity::Error),
                    );
                }
            }
            let position = items[component[0]].position;
            diagnostics.extend(goals.into_iter().map(|d| (position, d)));
            let used_unfinished = goals::take_used_unfinished();
            if unfinished {
                // Stuck on a goal, or using what waits for one: waiting
                // for the same goals, so a chain of uses names the goal at
                // its end.
                let mut blocked = self.decl.stuck_on_goal.borrow().clone();
                for id in used_unfinished {
                    if self.kernel.def(id).assumption().is_some() {
                        blocked.push(id);
                    } else {
                        blocked.extend(self.blocked_on(id));
                    }
                }
                blocked.sort_by_key(|id| id.0);
                blocked.dedup();
                // Waiting for another namespace's declaration with an error,
                // reported there: said once per file here (`E-USES-FAILED`),
                // as for one with no stand-in.
                // (A stand-in made before this module is another
                // namespace's, whose path is its key.)
                let elsewhere = (blocked.iter())
                    .find(|id| id.0 < self.unit.module.first_def && self.is_error_stand_in(**id))
                    .map(|id| self.kernel.def(*id).path().to_string());
                if let Some(key) = elsewhere {
                    for &i in &component {
                        self.unit.module.waits_elsewhere.insert(i, key.clone());
                    }
                }
                let blocked: Rc<[DefId]> = blocked.into();
                if !blocked.is_empty() {
                    for &i in &component {
                        self.unit.module.waiting.insert(i, blocked.clone());
                    }
                }
                self.mark_unfinished(&component, defs_before, datas_before, &blocked);
            }
            // A component that failed leaves nothing behind for the next,
            // and anything it left declared is failed, so later uses fail
            // too.
            if failed {
                self.clear_metas();
                kernel::abandon_pending(&mut self.kernel);
                // Running out of resources is reported where it happened
                // only as precisely as the declaration.
                let too_large = self.kernel.machine.budget.take_too_large();
                let ran_out_in = self.kernel.machine.budget.take_ran_out_in();
                for (position, d) in &mut diagnostics[before..] {
                    if d.code == "E-RESOURCE" {
                        d.notes.push(self.while_checking_note(&component));
                    }
                    if d.code == "E-RESOURCE" && d.message.ends_with("too large to show") {
                        for note in self.too_large_notes(&component, too_large) {
                            d.notes.push(note);
                        }
                    }
                    if d.code == "E-RESOURCE"
                        && is_steps_or_depth(&d.message)
                        && let Some(note) = self.ran_out_note(ran_out_in)
                    {
                        d.notes.push(note);
                    }
                    if d.labels.is_empty() {
                        let span = decl_spans[*position];
                        *d = d.clone().with_label(span, "while checking this");
                    }
                }
                // A theorem whose statement checked but whose proof didn't
                // (or is wholly `?`): is the statement false? Said as a note
                // on its first error, or on its goal (D1154, D1158).
                // Not one that ran out of resources, or used what did:
                // nothing found on a spent budget says anything about its
                // statement, and the reader needs the resource error, not a
                // search (SW-1730).
                if component.len() == 1 && !ran_out {
                    self.note_counterexample(&items[component[0]], &mut diagnostics[before..]);
                }
                if !unfinished {
                    self.stand_in_for_failed(&items, &component, &diagnostics[before..]);
                }
            } else if relying && component.len() == 1 && !ran_out {
                // A proof that is wholly `?`, checked assuming its goal.
                self.note_counterexample(&items[component[0]], &mut diagnostics[before..]);
            }
            // A data type's `Ord`, waiting for its module's own `DecEq`
            // instance, once that instance is checked.
            if !self.unit.module.ord_after_dec_eq.is_empty() {
                let saved = self.kernel.machine.budget.start(self.options.limits);
                if let Err(d) = self.glued(|e| e.derive_pending_ord(&component)) {
                    diagnostics.push((position, d));
                }
                self.kernel.machine.budget.restore(saved);
                self.clear_metas();
            }
        }
        self.clear_metas();
        self.unit.module.current.clear();
        self.unit.module.item = None;
        self.unit.module.phase = Phase::Body;
        if let (Some(ns), Some(_)) = (namespace, closure) {
            self.tables.namespace_defs.insert(
                ns.to_string(),
                self.unit.module.first_def..self.kernel.env.defs().len(),
            );
        }
        // Names that were never checked now just name failures.
        self.fail_unchecked_names();
        self.note_failed_sources(files);
        diagnostics.extend(self.uses_failed(files));
        // The names in the library's tests are references too, so that an
        // editor can navigate there; they are noted from the written names
        // alone (a dot call on a local needs its receiver's type, and
        // isn't).
        for (file, name) in std::mem::take(&mut self.unit.module.test_names) {
            self.unit.module.file = Some(file);
            self.note_name(&name);
        }
        self.unit.module.file = None;
        // Tests run by file, then in source order, whatever order they were
        // checked in.
        let ranks: HashMap<FileId, usize> = self
            .unit
            .module
            .files
            .iter()
            .enumerate()
            .filter_map(|(i, f)| f.id.map(|id| (id, i)))
            .collect();
        self.tables.tests.sort_since_by_key(first_test, |t| {
            (ranks.get(&t.span.file).copied().unwrap_or(0), t.span.start)
        });
        // Reported in source order, whatever order things were checked in.
        diagnostics.sort_by_key(|(position, _)| *position);
        let mut diagnostics: Vec<Diagnostic> = diagnostics.into_iter().map(|(_, d)| d).collect();
        // The names of an import that failed (and was reported) aren't
        // reported again where they're used.
        if !self.scope.import_failed.is_empty() {
            let failed = &self.scope.import_failed;
            diagnostics.retain(|d| {
                d.code != "E-UNKNOWN-NAME"
                    || !failed
                        .iter()
                        .any(|n| d.message == format!("unknown name `{n}`"))
            });
        }
        // The same for the names a failed `(..)` import would have brought.
        if !self.scope.wildcard_failed.is_empty() {
            let files: Vec<Option<FileId>> = self
                .scope
                .wildcard_failed
                .iter()
                .filter_map(|i| self.unit.module.files.get(*i).map(|f| f.id))
                .collect();
            diagnostics.retain(|d| {
                d.code != "E-UNKNOWN-NAME"
                    || d.message.contains('.')
                    || !d
                        .labels
                        .first()
                        .is_some_and(|l| files.iter().any(|f| f.is_none_or(|id| id == l.span.file)))
            });
        }
        // Failing because something used failed goes without saying when
        // that failure is reported too.
        if diagnostics
            .iter()
            .any(|d| d.severity == Severity::Error && d.code != "E-FAILED-DEPENDENCY")
        {
            diagnostics.retain(|d| d.code != "E-FAILED-DEPENDENCY");
        }
        // Doc links last, once everything the files declare is checked
        // (documentation.md §7); not in a namespace with errors, whose
        // names may be missing for another reason.
        if !diagnostics.iter().any(|d| d.severity == Severity::Error) {
            diagnostics.extend(self.doc_link_warnings(files));
        }
        // The parser reported these.
        diagnostics.retain(|d| d.code != UNPARSED_BODY);
        diagnostics
    }

    /// Stand-ins (docs/proposals/tests-with-errors.md §3.3, D3527) for the
    /// definitions and theorems of `component`, which failed with `found`:
    /// each whose statement the kernel declared is named by an assumption
    /// of that statement from now on, so what uses it is checked against
    /// the statement and relies on it. Not for a component whose only
    /// errors are what it uses failing (it waits, and so do its users), nor
    /// for a type, synonym, instance, opaque or `decreasing` definition, or
    /// one with parameter defaults: those keep failing their users, which
    /// would otherwise be refused for what a stand-in lacks (an instance's
    /// registration, an `unfolding` body, a default's helper).
    fn stand_in_for_failed(
        &mut self,
        items: &[Item],
        component: &[usize],
        found: &[(usize, Diagnostic)],
    ) {
        let errors = || found.iter().filter(|(_, d)| d.severity == Severity::Error);
        let own = errors().any(|(_, d)| !matches!(d.code, "E-FAILED-DEPENDENCY" | "E-USES-FAILED"));
        if !own {
            return;
        }
        for &i in component {
            let Decl::Signature {
                name,
                synonym: false,
                instance: false,
                opaque: false,
                decreasing: None,
                defaults,
                ..
            } = items[i].decl
            else {
                continue;
            };
            if defaults.iter().any(Option::is_some) {
                continue;
            }
            let Ok(key) = self.declaration_key(name) else {
                continue;
            };
            let Some(&(Global::Def(failed), _)) = self.scope.stored(&key) else {
                continue;
            };
            let at = (errors().find(|(p, _)| *p == items[i].position))
                .or_else(|| errors().next())
                .and_then(|(_, d)| d.primary_span())
                .unwrap_or(name.span);
            let saved = self.kernel.machine.budget.start(self.options.limits);
            let made = self.stand_in(failed, at);
            self.kernel.machine.budget.restore(saved);
            if let Some(id) = made {
                self.scope
                    .set_global(&key, |global| *global = Global::Def(id));
            }
        }
    }

    /// Whether `diagnostics` blame a declaration of `component`'s that
    /// failed by running out of resources, and nothing else.
    fn blamed_on_ran_out(&self, component: &[usize], diagnostics: &[(usize, Diagnostic)]) -> bool {
        let errors = || {
            diagnostics
                .iter()
                .filter(|(_, d)| d.severity == Severity::Error)
        };
        errors().next().is_some()
            && errors().all(|(_, d)| d.code == "E-FAILED-DEPENDENCY")
            && component
                .iter()
                .flat_map(|i| &self.unit.module.items[*i].deps)
                .filter(|d| d.speculative.is_none() && !component.contains(&d.item))
                .any(|d| {
                    let used = &self.unit.module.items[d.item];
                    used.status.failed() && used.ran_out
                })
    }

    /// After the single declaration `item` failed, with `diagnostics`: if
    /// it's a theorem whose statement checked, a note on its first error
    /// (or the goal of a proof that's wholly `?`) with a counterexample to
    /// the statement, if the search finds one (`counterexample.rs`).
    fn note_counterexample(&mut self, item: &Item, diagnostics: &mut [(usize, Diagnostic)]) {
        let Decl::Signature {
            theorem: true,
            span,
            ..
        } = item.decl
        else {
            return;
        };
        // An error, or else the goal of a proof that is wholly `?` (a `?`
        // inside a proof is a later stage).
        let wanted = if diagnostics
            .iter()
            .any(|(_, d)| d.severity == Severity::Error)
        {
            Severity::Error
        } else if !item.equations.is_empty()
            && item.equations.iter().all(|eq| {
                // `:= ?`, under the lambdas a header's parameters make.
                let Decl::Equation { rhs: Some(rhs), .. } = eq else {
                    return false;
                };
                let mut rhs = rhs;
                while let Expr::Lam(_, body, _) | Expr::TypedLam(_, _, _, body, _) = rhs {
                    rhs = &**body;
                }
                matches!(rhs, Expr::Goal(_))
            })
        {
            Severity::Goal
        } else {
            return;
        };
        // The theorem's own definition, declared once its statement checked.
        let Some(def) = (self.unit.module.first_def..self.kernel.env.defs().len())
            .rev()
            .map(DefId)
            .find(|id| {
                let def = self.kernel.def(*id);
                def.theorem() && def.span() == *span
            })
        else {
            return;
        };
        if !diagnostics.iter().any(|(_, d)| d.severity == wanted) {
            return;
        }
        let Some((note, log)) = self.counterexample_note(def) else {
            return;
        };
        // The note as data, for the index: the search's log has its bindings.
        let data = log.found.as_ref().map(|found| {
            Box::new(stitchwort_syntax::Counterexample {
                verdict: "false",
                types: (log.found_types.iter())
                    .map(|a| (a.clone(), "Nat".to_string()))
                    .collect(),
                bindings: (found.iter())
                    .filter_map(|b| b.split_once(" = "))
                    .map(|(name, value)| (name.to_string(), value.to_string()))
                    .collect(),
            })
        });
        if let Some((_, d)) = diagnostics.iter_mut().find(|(_, d)| d.severity == wanted) {
            // Splitting a case won't prove a false statement.
            d.notes.retain(|n| !crate::check::is_stuck_side_note(n));
            d.notes.push(note);
            d.detail_mut().counterexample = data.map(|b| *b);
        }
    }

    /// Names the definition being unfolded when checking ran out of steps or
    /// frames; a function the compiler made is named by the definition it
    /// was made for.
    fn ran_out_note(&self, definition: Option<usize>) -> Option<String> {
        let name = &self.kernel.env.defs().get(definition?)?.name();
        let shown = crate::scope::display(name);
        Some(match shown.split_once(".%") {
            None if !shown.contains('%') => format!("it ran out while unfolding `{shown}`"),
            Some((owner, _)) if !owner.contains('%') => format!(
                "it ran out while unfolding a function the compiler made for `{owner}`, \
                 such as an inner `match`"
            ),
            _ => return None,
        })
    }

    /// Names the declaration(s) of `component`, so a check that ran out of
    /// resources says where, whatever it ran out of (SW-843).
    fn while_checking_note(&self, component: &[usize]) -> String {
        let names: Vec<String> = component
            .iter()
            .map(|i| format!("`{}`", self.unit.module.items[*i].name))
            .collect();
        format!("it happened while checking {}", names.join(", "))
    }

    /// Notes for "a value was too large to show" while checking `component`:
    /// the definition the value was a call of (`head`, an
    /// index recorded where the reading-back gave up), and the opaque
    /// definitions the declaration unfolds, whose bodies were computed with.
    fn too_large_notes(&self, component: &[usize], head: Option<usize>) -> Vec<String> {
        let g = &self.ev();
        let mut notes = Vec::new();
        if let Some(head) = head.filter(|h| *h < g.env.defs().len()) {
            let name = g.env.defs()[head].name();
            if !name.contains('%') {
                notes.push(format!(
                    "the value being shown was a call of `{name}`, computed far enough to be \
                     very large"
                ));
            }
        }
        let mut unfolded: Vec<String> = Vec::new();
        for i in component {
            if let Some((Global::Def(id), _)) = self.named(&self.unit.module.items[*i].name) {
                for u in g.def(*id).unfolding().iter() {
                    let name = g.def(*u).name();
                    if !name.contains('%') && !unfolded.contains(&format!("`{name}`")) {
                        unfolded.push(format!("`{name}`"));
                    }
                }
            }
        }
        if !unfolded.is_empty() {
            let (bodies, were) = if unfolded.len() == 1 {
                ("its opaque body was", "it")
            } else {
                ("their opaque bodies were", "they")
            };
            notes.push(format!(
                "it unfolds {}, so {bodies} computed here, and {were} may produce the large \
                 value; a statement about a smaller part of the result, or a lemma proved \
                 once and rewritten with, avoids computing the whole value",
                unfolded.join(", ")
            ));
        }
        notes
    }

    /// Notes the declarations of `component`, unfinished, as such for the
    /// kernel's refusals of what uses them (`goals::unfinished_dependency`):
    /// those its items declared, and the ones made while checking it (from
    /// definition `defs` and data type `datas` on) that aren't final: failed,
    /// or pending until the component is abandoned.
    ///
    /// `blocked` are the assumptions of the open goals it is stuck on, if
    /// that is why (`Elaborator::blocked_on`).
    fn mark_unfinished(
        &mut self,
        component: &[usize],
        defs: usize,
        datas: usize,
        blocked: &Rc<[DefId]>,
    ) {
        let g = &self.ev();
        let mut def_ids: Vec<DefId> = (component.iter())
            .flat_map(|i| self.unit.module.item_defs.get(i).into_iter().flatten())
            .filter(|id| g.def(**id).state() != State::Final)
            .copied()
            .collect();
        def_ids.extend(
            (defs..g.env.defs().len())
                .filter(|&id| g.env.defs()[id].state() != State::Final)
                .map(DefId),
        );
        let data_ids: Vec<DataId> = (datas..g.env.datas().len())
            .filter(|&d| g.env.datas()[d].state() != State::Final)
            .map(DataId)
            .collect();
        let owners = &self.session.owners;
        for id in def_ids {
            self.tables.unfinished_defs.insert(owners, id, ());
            self.session
                .blocked
                .borrow_mut()
                .insert(id, blocked.clone());
        }
        for d in data_ids {
            self.tables.unfinished_datas.insert(owners, d, ());
        }
    }

    /// When a message of this component showed a term that uses a failed
    /// definition (`Decl::failed_mentioned`, decided from the terms, not
    /// the text: messages elide), its errors are fallout of that failure (a
    /// failed definition is stuck, so a proof about it won't check): they
    /// become one saying the failed declaration has errors, which goes
    /// without saying when that failure is reported too. When one showed a
    /// term stuck on an open goal's assumption (`Decl::stuck_on_goal`), from
    /// this module or another, they can't be decided until the goal is
    /// filled, so they are unfinished. Unknown names stay, and so does
    /// everything when no message showed either.
    fn blame_failed_dependency(
        &self,
        component: &[usize],
        before: usize,
        diagnostics: &mut [(usize, Diagnostic)],
    ) {
        let failed: Vec<(&Dep, &str)> = component
            .iter()
            .flat_map(|i| &self.unit.module.items[*i].deps)
            .filter(|d| {
                d.speculative.is_none()
                    && !component.contains(&d.item)
                    && self.unit.module.items[d.item].status.failed()
            })
            .map(|d| (d, self.unit.module.items[d.item].name.as_str()))
            .collect();
        let blamed = !failed.is_empty() && self.decl.failed_mentioned.get();
        // Fallout of another namespace's failure: what's shown uses a
        // declaration of its that failed, and nothing here did.
        let elsewhere = (failed.is_empty() && self.decl.failed_mentioned.get())
            .then(|| {
                let used = FAILED_USED.with(|u| u.borrow().clone());
                used.into_iter()
                    .find(|k| !self.unit.module.names.contains(k))
            })
            .flatten();
        if let Some(key) = elsewhere {
            let text = key.rsplit('.').next().unwrap_or(&key).to_string();
            for (_, d) in &mut diagnostics[before..] {
                if d.severity == Severity::Error && d.code != "E-UNKNOWN-NAME" {
                    *d = match d.primary_span() {
                        Some(span) => failed_name(&ast::Name {
                            text: text.clone(),
                            span,
                        }),
                        None => {
                            Diagnostic::error("E-FAILED-DEPENDENCY", format!("`{text}` has errors"))
                        }
                    };
                }
            }
            return;
        }
        if !blamed && self.decl.stuck_on_goal.borrow().is_empty() {
            return;
        }
        // Blamed on a declaration with errors if there is one; if they're
        // all unfinished, or it is stuck on a goal, so is this (D636).
        let errored = (failed.iter())
            .position(|(d, _)| self.unit.module.items[d.item].status == Status::Failed)
            .filter(|_| blamed);
        for (_, d) in &mut diagnostics[before..] {
            if d.severity != Severity::Error
                || d.code == "E-UNKNOWN-NAME"
                || d.code == "E-FAILED-DEPENDENCY"
            {
                continue;
            }
            let Some(errored) = errored else {
                for (dep, _) in &failed {
                    self.note_waits_for(dep.item);
                }
                *d = goals::uses_unfinished(d.primary_span());
                continue;
            };
            let (dep, name) = failed[errored];
            let name = ast::Name {
                text: name.to_string(),
                span: dep.span,
            };
            *d = failed_name(&name);
        }
    }

    /// Notes where the errors of this module's failed declarations are, for
    /// the namespaces that use them (`Session::failed_sources`).
    fn note_failed_sources(&mut self, files: &[SourceUnit]) {
        let parse_failed: Vec<(String, (String, Option<Span>))> = (files.iter())
            .flat_map(|unit| &unit.module.failed)
            .filter_map(|failed| {
                let key = self.declaration_key(&failed.name).ok()?;
                Some((key, (failed.name.text.clone(), failed.error_at)))
            })
            .collect();
        let module = &self.unit.module;
        let sources = &mut self.session.failed_sources;
        sources.retain(|key, _| !module.names.contains(key));
        let namespace = module.namespace.clone().unwrap_or_default();
        for (key, source) in parse_failed {
            if module.names.contains(&key) {
                let log = &mut self.session.failed_decls;
                log.retain(|f| (&f.namespace, &f.name) != (&namespace, &source.0));
                log.push(crate::FailedDecl {
                    namespace: namespace.clone(),
                    name: source.0.clone(),
                    theorem: false,
                    test: false,
                    root: source.0.clone(),
                    error_at: source.1,
                    own: true,
                });
                sources.insert(key, source);
            }
        }
        for (item, source) in &module.error_sources {
            if let Some(key) = module.item_keys.get(item) {
                sources.insert(key.clone(), source.clone());
            }
        }
    }

    /// `E-USES-FAILED`: for each declaration of another namespace that
    /// failed and each file whose declarations wait for it, one error,
    /// on the file's import of it if it has one, listing what waits. The
    /// waiting declarations report nothing themselves, so a broken name
    /// costs a file one error however often it is used.
    fn uses_failed(&self, files: &[SourceUnit]) -> Vec<(usize, Diagnostic)> {
        let module = &self.unit.module;
        let short = |key: &str| key.rsplit('.').next().unwrap_or(key).to_string();
        // The declaration with the error, which may be behind the one used.
        let source = |key: &str| {
            (self.session.failed_sources.get(key).cloned()).unwrap_or_else(|| (short(key), None))
        };
        let mut waiting: Vec<(&str, usize, usize)> = (module.waits_elsewhere.iter())
            .map(|(item, key)| (key.as_str(), module.items[*item].file, *item))
            .collect();
        waiting.sort_by_key(|(key, file, item)| (*file, module.items[*item].position, *key));
        // By the declaration with the error and the file.
        type Group<'k> = ((String, Option<Span>), usize, Vec<&'k str>, Vec<usize>);
        let mut groups: Vec<Group> = Vec::new();
        for (key, file, item) in waiting {
            let root = source(key);
            match (groups.iter_mut()).find(|(r, f, _, _)| *r == root && *f == file) {
                Some((_, _, keys, items)) => {
                    if !keys.contains(&key) {
                        keys.push(key);
                    }
                    items.push(item);
                }
                None => groups.push((root, file, vec![key], vec![item])),
            }
        }
        let mut out = Vec::new();
        for ((broken, error_at), file, keys, items) in groups {
            let shown = |i: &usize| {
                let item = &module.items[*i];
                match item.kind {
                    // Its name is `test "…"` already.
                    Kind::Test => item.name.clone(),
                    _ => format!("`{}`", item.name),
                }
            };
            let message = match items.as_slice() {
                [one] => format!(
                    "`{broken}` has an error, so {} can't be checked until it's fixed",
                    shown(one)
                ),
                _ => format!(
                    "`{broken}` has an error, so {} declarations here can't be checked until \
                     it's fixed",
                    items.len()
                ),
            };
            // On the file's import of what it uses, if it names it.
            let imported = (files.get(file)).and_then(|unit| {
                (keys.iter()).find_map(|k| Some((*k, import_of(&unit.module.imports, k)?)))
            });
            let label = |key: &str| match short(key) {
                used if used == broken => format!("`{broken}` has an error"),
                used => format!("`{used}` depends on `{broken}`, which has an error"),
            };
            let (at, label) = match imported {
                Some((key, at)) => (at, label(key)),
                None => (module.items[items[0]].span, label(keys[0])),
            };
            let mut d = Diagnostic::error("E-USES-FAILED", message).with_label(at, label);
            if let Some(error_at) = error_at {
                d = d.with_label(error_at, "the error is here");
            }
            if items.len() > 1 {
                let names: Vec<String> = items.iter().map(shown).collect();
                d = d.with_note(format!("waiting for it: {}", names.join(", ")));
            }
            out.push((module.items[items[0]].position, d));
        }
        out
    }

    /// Records where the errors of `component`, which failed with `found`,
    /// come from, and, if it is a test that only failed because of what it
    /// uses, that it is a broken test (D3523). `used_failed` are the keys
    /// of the failed declarations it was refused for using, as noted where
    /// it was refused: if nothing else is wrong with it and one is another
    /// namespace's, it waits for that one.
    fn note_error_source(
        &mut self,
        items: &[Item],
        component: &[usize],
        found: &[(usize, Diagnostic)],
        used_failed: &[String],
    ) {
        let errors: Vec<&Diagnostic> = found
            .iter()
            .map(|(_, d)| d)
            .filter(|d| d.severity == Severity::Error)
            .collect();
        let Some(first) = errors.first() else {
            return;
        };
        let only_dependencies = errors.iter().all(|d| d.code == "E-FAILED-DEPENDENCY");
        let module = &self.unit.module;
        // What it uses that failed: (its name, the source of its error,
        // and the key of the other namespace's declaration it waits for).
        type Used = (String, (String, Option<Span>), Option<String>);
        let used: Option<Used> = if !only_dependencies {
            None
        } else if let Some(key) = (used_failed.iter()).find(|k| !module.names.contains(*k)) {
            let short = key.rsplit('.').next().unwrap_or(key).to_string();
            let source = (self.session.failed_sources.get(key).cloned())
                .unwrap_or_else(|| (short.clone(), None));
            Some((short, source, Some(key.clone())))
        } else {
            // What it names, or else what the refusal found (a dot call is
            // only a speculative dependency).
            let noted = used_failed.iter().filter_map(|k| {
                (module.item_keys.iter())
                    .find(|(_, key)| *key == k)
                    .map(|(i, _)| *i)
            });
            (component.iter())
                .flat_map(|i| &module.items[*i].deps)
                .filter(|d| d.speculative.is_none() && !component.contains(&d.item))
                .map(|d| d.item)
                .chain(noted)
                .find(|i| {
                    !component.contains(i)
                        && module.items[*i].status == Status::Failed
                        && module.error_sources.contains_key(i)
                })
                .and_then(|i| {
                    let source = module.error_sources.get(&i)?.clone();
                    let waits = module.waits_elsewhere.get(&i).cloned();
                    Some((module.items[i].name.clone(), source, waits))
                })
                // A declaration of this module's that didn't parse.
                .or_else(|| {
                    let source = used_failed
                        .iter()
                        .find_map(|k| module.parse_failed.get(k))?;
                    Some((source.0.clone(), source.clone(), None))
                })
        };
        let source = match &used {
            Some((_, source, _)) => source.clone(),
            None => (
                module.items[component[0]].name.clone(),
                first.primary_span(),
            ),
        };
        let own = !only_dependencies || used.is_none();
        let namespace = self.unit.module.namespace.clone().unwrap_or_default();
        for &i in component {
            self.unit.module.error_sources.insert(i, source.clone());
            if let Some((_, _, Some(key))) = &used {
                self.unit.module.waits_elsewhere.insert(i, key.clone());
            }
            let info = &self.unit.module.items[i];
            let failed = crate::FailedDecl {
                namespace: namespace.clone(),
                name: info.name.clone(),
                theorem: matches!(items[i].decl, Decl::Signature { theorem: true, .. }),
                test: info.kind == Kind::Test,
                root: source.0.clone(),
                error_at: source.1,
                own,
            };
            let log = &mut self.session.failed_decls;
            log.retain(|f| (&f.namespace, &f.name) != (&failed.namespace, &failed.name));
            log.push(failed);
        }
        let [i] = component else {
            return;
        };
        let Decl::Test { name, span, .. } = items[*i].decl else {
            return;
        };
        let uses = match used {
            Some((uses, _, _)) => uses,
            None => name.to_string(),
        };
        let broken = BrokenTest {
            name: name.to_string(),
            namespace,
            span: *span,
            uses,
            broken: source.0,
            error_at: source.1,
            own,
        };
        self.session.broken_tests.push(broken);
    }

    /// Step 1: the module's declarations, with every name they declare
    /// entered as unchecked. A declaration whose own name is taken is
    /// reported and left out; one with a constructor or operation whose name
    /// is taken is reported and fails.
    fn collect<'m>(
        &mut self,
        files: &[SourceUnit<'m>],
        diagnostics: &mut Vec<(usize, Diagnostic)>,
    ) -> (Vec<Item<'m>>, Vec<Span>) {
        let mut items = Vec::new();
        let mut decl_spans: Vec<Span> = Vec::new();
        // The position of each file's first declaration.
        let mut file_starts = Vec::new();
        let mut test_names: HashMap<&str, Span> = HashMap::default();
        for (file, unit) in files.iter().enumerate() {
            let decls: &'m [Decl] = &unit.module.decls;
            let base = decl_spans.len();
            file_starts.push(base);
            decl_spans.extend(decls.iter().map(Decl::span));
            let mut i = 0;
            while i < decls.len() {
                let equations_for = |name: &str, from: usize| {
                    let mut j = from;
                    while let Some(Decl::Equation { name: n, .. }) = decls.get(j)
                        && n.text == name
                    {
                        j += 1;
                    }
                    j
                };
                let local = i;
                let position = base + local;
                let (decl, equations) = match &decls[i] {
                    Decl::Signature { name, .. } => {
                        let end = equations_for(&name.text, i + 1);
                        i = end;
                        (&decls[local], &decls[local + 1..end])
                    }
                    // A `def` header always carries its type, so the parser
                    // never produces an arm without its signature in front.
                    Decl::Equation { .. } => unreachable!("an equation without a signature"),
                    decl => {
                        i += 1;
                        (decl, &decls[..0])
                    }
                };
                // The core's and the library files' tests run under the
                // library test target (`library_tests`), and are skipped
                // otherwise.
                if self.unit.loading_prelude
                    && !self.options.library_tests
                    && matches!(decl, Decl::Test { .. })
                {
                    if self.present.nav.is_some() {
                        self.unit.module.test_names.extend(
                            decl_refs(decl, &[])
                                .into_iter()
                                .filter_map(|(r, _)| match r {
                                    // Not the names the compiler adds for
                                    // syntax (`∈`, literals), which are
                                    // written nowhere.
                                    Ref::Name(n) if n.span.start != n.span.end => {
                                        Some((file, n.clone()))
                                    }
                                    _ => None,
                                }),
                        );
                    }
                    continue;
                }
                if let Decl::Test { name, span, .. } = decl {
                    if let Some(earlier) = test_names.get(name.as_str()) {
                        diagnostics.push((
                            position,
                            error(
                                "E-DUPLICATE",
                                *span,
                                format!("there's already a test called \"{name}\""),
                            )
                            .with_label(*earlier, "first defined here"),
                        ));
                        continue;
                    }
                    test_names.insert(name, *span);
                }
                let status = Status::Waiting;
                let instance = matches!(decl, Decl::Signature { instance: true, .. });
                let (kind, name, span, synonym) = match decl {
                    Decl::Data { name, .. } => (Kind::Data, name.text.clone(), name.span, false),
                    Decl::Ability { name, .. } => {
                        (Kind::Ability, name.text.clone(), name.span, false)
                    }
                    Decl::Signature { name, synonym, .. } => {
                        (Kind::Def, name.text.clone(), name.span, *synonym)
                    }
                    Decl::Test { name, span, .. } => {
                        (Kind::Test, format!("test \"{name}\""), *span, false)
                    }
                    Decl::Equation { .. } => unreachable!("equations go with signatures"),
                };
                // Worked out once the names are registered.
                let decides = false;
                self.unit.module.items.push(ItemInfo {
                    name,
                    span,
                    position,
                    file,
                    kind,
                    synonym,
                    deps: Vec::new(),
                    component: 0,
                    status,
                    decides,
                    function: false,
                    instance,
                    interface: None,
                    head: None,
                    ran_out: false,
                });
                items.push(Item {
                    decl,
                    equations,
                    position,
                });
            }
        }
        // Names without a qualifier, then each file's imports of the library's,
        // then qualified names, then each file's imports of the module's own
        // namespaces. Imports are per file (docs/proposals/multi-file.md
        // §4.4); an import error is reported at its file's first declaration.
        let mut import_errors: Vec<(usize, Diagnostic)> = Vec::new();
        let mut left_out = HashSet::default();
        for qualified in [false, true] {
            if qualified {
                self.add_file_imports(files, &file_starts, false, &mut import_errors);
            }
            for (index, item) in items.iter().enumerate() {
                let main = declared_names(item.decl).0;
                self.unit.module.file = Some(self.unit.module.items[index].file);
                if main.as_ref().is_some_and(|m| m.text.contains('.')) == qualified
                    && let Err(d) = self.register(index, item.decl)
                {
                    let (d, fatal) = *d;
                    diagnostics.push((item.position, d));
                    if fatal {
                        left_out.insert(index);
                    } else {
                        self.unit.module.items[index].status = Status::Failed;
                    }
                }
            }
        }
        self.add_file_imports(files, &file_starts, true, &mut import_errors);
        // Functions for other namespaces' types, found now that the imports
        // that name the types are in place. Each was registered under the
        // key it has as an extension (`P.Spec.Grid.probe`).
        for (index, item) in items.iter().enumerate() {
            if left_out.contains(&index) {
                continue;
            }
            let Some(main) = declared_names(item.decl).0 else {
                continue;
            };
            self.unit.module.file = Some(self.unit.module.items[index].file);
            let Some(target) = self.extension_target(&main) else {
                continue;
            };
            match self.check_extension(item.decl, &main, &target) {
                Ok(()) => match self.declaration_key(&main) {
                    Ok(key) => self.scope.add_extension(&key, &target),
                    Err(d) => {
                        diagnostics.push((item.position, d));
                        self.unit.module.items[index].status = Status::Failed;
                    }
                },
                Err(d) => {
                    diagnostics.push((item.position, d));
                    self.unit.module.items[index].status = Status::Failed;
                }
            }
        }
        // Whether a signature's result is the library's `Decidable`, by what
        // its head means here, not how it's spelt.
        let decidable = self.kernel.env.registry().data(Builtin::Decidable);
        for (index, item) in items.iter().enumerate() {
            self.unit.module.file = Some(self.unit.module.items[index].file);
            if let Decl::Signature {
                ty, instance: true, ..
            } = item.decl
                && let Some(head) = result_head(ty)
            {
                self.unit.module.items[index].decides = decidable.is_some()
                    && matches!(self.named(&head.text), Some((Global::Data(d), _)) if Some(*d) == decidable);
            }
        }
        for (index, item) in items.iter().enumerate() {
            if let Decl::Signature { ty, .. } = item.decl {
                self.unit.module.items[index].function = is_function_type(ty);
            }
        }
        for (index, item) in items.iter().enumerate() {
            if let Decl::Signature {
                ty, instance: true, ..
            } = item.decl
                && let Some(head) = result_head(ty)
            {
                self.unit.module.file = Some(self.unit.module.items[index].file);
                self.unit.module.items[index].interface = self.named(&head.text).map(|(g, _)| *g);
                self.unit.module.items[index].head = instance_head(ty)
                    .and_then(|n| self.named(&n.text))
                    .map(|(g, _)| *g);
            }
        }
        self.unit.module.file = None;
        self.declare_parse_failed(files);
        diagnostics.extend(import_errors);
        // A declaration whose own name is taken is left out.
        if !left_out.is_empty() {
            let mut kept = Vec::new();
            let mut infos = Vec::new();
            let old = std::mem::take(&mut self.unit.module.items);
            let mut renumber = HashMap::default();
            for (index, (item, info)) in items.into_iter().zip(old).enumerate() {
                if !left_out.contains(&index) {
                    renumber.insert(index, kept.len());
                    kept.push(item);
                    infos.push(info);
                }
            }
            // The interface and head of an instance were looked up before
            // the declarations were left out, so they name the old indices.
            for info in &mut infos {
                for global in [&mut info.interface, &mut info.head] {
                    if let Some(Global::Unchecked(i)) = global {
                        // Looked up by name, so it's the declaration that
                        // kept the name, never one left out.
                        if let Some(&new) = renumber.get(i) {
                            *i = new;
                        } else {
                            *global = None;
                        }
                    }
                }
            }
            self.unit.module.items = infos;
            for key in &self.unit.module.names {
                if let Some((Global::Unchecked(i), _)) = self.scope.stored(key)
                    && let Some(&new) = renumber.get(i)
                {
                    self.scope.set_global(key, |g| *g = Global::Unchecked(new));
                }
            }
            return (kept, decl_spans);
        }
        (items, decl_spans)
    }

    /// The names of declarations that failed to parse are declared as
    /// failed (unless something else already declared them), so a use of
    /// one is `E-FAILED-DEPENDENCY` (which goes without saying, the syntax
    /// error having been reported) rather than `E-UNKNOWN-NAME`.
    fn declare_parse_failed(&mut self, files: &[SourceUnit]) {
        for unit in files {
            for failed in &unit.module.failed {
                let name = &failed.name;
                let Ok(key) = self.declaration_key(name) else {
                    continue;
                };
                if self.scope.has(&key) {
                    continue;
                }
                self.scope.insert(&key, Global::Failed, name.span, false);
                if let Some(target) = self.extension_target(name) {
                    self.scope.add_extension(&key, &target);
                }
                (self.unit.module.parse_failed)
                    .insert(key.clone(), (name.text.clone(), failed.error_at));
                self.unit.module.names.insert(key);
            }
        }
    }

    /// Adds each file's imports to its own table (`own` as in
    /// [`Elaborator::add_imports`]); errors are positioned at the file's
    /// first declaration.
    fn add_file_imports(
        &mut self,
        files: &[SourceUnit],
        file_starts: &[usize],
        own: bool,
        errors: &mut Vec<(usize, Diagnostic)>,
    ) {
        for (file, unit) in files.iter().enumerate() {
            self.unit.module.file = Some(file);
            let mut found = Vec::new();
            self.add_imports(&unit.module.imports, own, &mut found);
            errors.extend(found.into_iter().map(|d| (file_starts[file], d)));
        }
        self.unit.module.file = None;
    }

    /// The file whose imports name lookup uses: the one the item being
    /// elaborated is in, or the one being registered; file 0 when nothing is
    /// (so `eval`, the REPL and `main` see a single file's imports).
    pub(crate) fn current_file(&self) -> usize {
        self.unit
            .module
            .file
            .or_else(|| {
                self.unit
                    .module
                    .item
                    .map(|i| self.unit.module.items[i].file)
            })
            .unwrap_or(0)
    }

    /// Enters the names declaration `index` declares as unchecked. The error
    /// is fatal (the declaration is left out) when its own name can't be
    /// registered.
    fn register(&mut self, index: usize, decl: &Decl) -> Result<(), Box<(Diagnostic, bool)>> {
        let (main, members) = declared_names(decl);
        let Some(main) = main else {
            return Ok(());
        };
        let key = self
            .declaration_key(&main)
            .map_err(|d| Box::new((d, true)))?;
        self.new_module_name(&key, &main)
            .map_err(|d| Box::new((d, true)))?;
        self.scope
            .insert(&key, Global::Unchecked(index), main.span, false);
        self.unit.module.names.insert(key.clone());
        self.unit.module.item_keys.insert(index, key.clone());
        let mut result = Ok(());
        for (k, (member, follower)) in members.iter().enumerate() {
            let within = members[..k].iter().find(|(o, _)| o.text == member.text);
            let member_key = Self::member_key(&key, &member.text);
            let checked = match within {
                Some((earlier, _)) => Err(error(
                    "E-DUPLICATE",
                    member.span,
                    format!("`{}` is already defined", member.text),
                )
                .with_label(earlier.span, "first defined here")),
                None => self.new_module_name(&member_key, member),
            };
            match checked {
                Ok(()) => {
                    self.scope.insert(
                        &member_key,
                        Global::Unchecked(index),
                        member.span,
                        *follower,
                    );
                    self.unit.module.names.insert(member_key);
                }
                Err(d) => {
                    if result.is_ok() {
                        result = Err(Box::new((d, false)));
                    }
                }
            }
        }
        result
    }

    /// A name a module declaration claims: not built in, and not already
    /// taken (by an earlier module or earlier in this one).
    fn new_module_name(&self, key: &str, n: &ast::Name) -> crate::Result<()> {
        if self.is_reserved(&n.text) {
            return Err(error(
                "E-DUPLICATE",
                n.span,
                format!("`{}` is built in and can't be redefined", n.text),
            ));
        }
        if let Some(previous) = self.taken(key) {
            return Err(error(
                "E-DUPLICATE",
                n.span,
                format!("`{}` is already defined", n.text),
            )
            .with_label(previous, "first defined here"));
        }
        Ok(())
    }

    /// Where `key` is declared already, if it is. Not a name a cache replay
    /// that failed part way declared for this namespace (as a failure),
    /// which elaborating the namespace claims again in the same place
    /// (`cache`).
    fn taken(&self, key: &str) -> Option<Span> {
        let (global, span) = self.scope.get(key)?;
        if matches!(global, Global::Failed) && self.session.replayed_names.contains(key) {
            return None;
        }
        Some(span)
    }

    /// Step 2: what each declaration refers to. Also the library files the
    /// module uses (`library.rs`).
    fn dependencies(&mut self, items: &[Item]) -> crate::library::Needs {
        let mut needs = crate::library::Needs::default();
        let own = self.scope.loading;
        let library = self.library_index();
        // `D.All` for a data type `D` of this module that doesn't declare it:
        // generated with the nested types that hold `D` (`derive_induct.rs`).
        let mut alls: Vec<(usize, usize, Span)> = Vec::new();
        for (index, item) in items.iter().enumerate() {
            self.unit.module.file = Some(self.unit.module.items[index].file);
            let mut deps = Vec::new();
            let names = &self.unit.module.names;
            let mut add = |r: Ref<'_>, in_header: bool| {
                let mut namespace = None;
                let (n, mut fields) = match r {
                    Ref::Name(n) => (n, Vec::new()),
                    Ref::Dot(n, field, receiver) => {
                        namespace = receiver
                            .and_then(|r| self.receiver_head(r, index, items))
                            .and_then(|head| self.dot_namespace(head));
                        (n, vec![field])
                    }
                };
                if fields.is_empty()
                    && let crate::scope::Resolved::Found { global, rest, .. } =
                        self.resolve(&n.text)
                {
                    if let Global::Unchecked(j) = global {
                        deps.push(Dep {
                            item: j,
                            span: n.span,
                            in_header,
                            speculative: None,
                        });
                        if rest.len() == 1 && rest[0] == "All" {
                            alls.push((index, j, n.span));
                        }
                    }
                    fields = rest;
                }
                // Dot notation: its target isn't known until the receiver's
                // type is, so every declaration of this module that it
                // could mean (§5).
                for field in fields {
                    let suffix = format!(".{field}");
                    // A receiver of a written data type `T` means a method of
                    // `T`, which may be declared in any namespace (`Path.extend`
                    // in a proofs namespace beside `Path`'s): a key ending in
                    // `T.field`, with `T` the type's simple name.
                    let method = namespace
                        .as_ref()
                        .map(|ns| format!("{}{suffix}", ns.rsplit('.').next().unwrap_or(ns)));
                    for key in names.iter().filter(|k| match &method {
                        Some(method) => *k == method || k.ends_with(&format!(".{method}")),
                        None => k.ends_with(&suffix),
                    }) {
                        if let Some((Global::Unchecked(j), _)) = self.scope.get(key) {
                            deps.push(Dep {
                                item: j,
                                span: n.span,
                                in_header,
                                // Not a guess when the receiver's type is known.
                                speculative: namespace.is_none().then(|| {
                                    format!(
                                        "`.{field}` might mean `{}`",
                                        crate::scope::display(key)
                                    )
                                }),
                            });
                        }
                    }
                }
            };
            for (r, in_header) in decl_refs(item.decl, item.equations) {
                if matches!(r, Ref::Name(n) if std::ptr::eq(n, &*REWRITE_MARKER)) {
                    if let Some(index) = &library
                        && own.is_none()
                    {
                        for name in crate::omega::LIBRARY_NAMES.iter() {
                            self.note_library_use(index, &Ref::Name(name), &mut needs);
                        }
                    }
                    continue;
                }
                if let Some(index) = &library {
                    self.note_library_use(index, &r, &mut needs);
                }
                add(r, in_header);
            }
            self.unit.module.items[index].deps = deps;
        }
        for (index, d, span) in alls {
            if self.unit.module.items[d].kind != Kind::Data {
                continue;
            }
            let holders: Vec<usize> = (0..self.unit.module.items.len())
                .filter(|&x| {
                    x != d
                        && x != index
                        && self.unit.module.items[x].kind == Kind::Data
                        && self.unit.module.items[x]
                            .deps
                            .iter()
                            .any(|dep| dep.item == d)
                })
                .collect();
            let name = self.unit.module.items[d].name.clone();
            for x in holders {
                self.unit.module.items[index].deps.push(Dep {
                    item: x,
                    span,
                    in_header: false,
                    speculative: Some(format!(
                        "`{name}.All` is generated with a type that holds `{name}`"
                    )),
                });
            }
        }
        self.unit.module.file = None;
        if let Some(f) = own {
            needs.files.remove(&f);
        }
        needs
    }

    /// The name at the head of the type of a dot call's receiver, where the
    /// declarations written say what it is. A variable a constructor
    /// pattern binds has the type its field is written with, when the
    /// constructor is one of a data type of this module, in the same file as
    /// the declaration `index` (so a name means the same in both), and the
    /// type's head is a name no parameter or field of the constructor can
    /// stand for. Anything less certain is `None`: the dot call is then
    /// linked to every method of that name.
    fn receiver_head<'i>(
        &self,
        receiver: Receiver<'i>,
        index: usize,
        items: &[Item<'i>],
    ) -> Option<&'i ast::Name> {
        let (ctor, slot) = match receiver {
            Receiver::Type(head) => return Some(head),
            Receiver::Field(ctor, slot) => (ctor, slot),
        };
        let crate::scope::Resolved::Found {
            global: Global::Unchecked(j),
            rest,
            key,
            ..
        } = self.resolve(&ctor.text)
        else {
            return None;
        };
        let modules = &self.unit.module.items;
        if !rest.is_empty()
            || modules[j].kind != Kind::Data
            || modules[j].file != modules[index].file
        {
            return None;
        }
        let Decl::Data {
            name,
            params,
            indices,
            ctors,
            interface: false,
            ..
        } = items[j].decl
        else {
            return None;
        };
        let data_key = self.declaration_key(name).ok()?;
        // A constructor named like its type is found by the type's name.
        let decl = ctors.iter().find(|c| {
            Self::member_key(&data_key, &c.name.text) == key
                || key == data_key && c.name.text == name.text
        })?;
        // Braces after a constructor declared with brackets are a record
        // pattern, not its fields.
        if matches!(slot, CtorSlot::Named(_)) && !decl.braced {
            return None;
        }
        // The explicit fields, one per name.
        let explicit: Vec<(&ast::Name, &Expr)> = decl
            .fields
            .iter()
            .enumerate()
            .filter(|(i, _)| !decl.implicit.get(*i).copied().unwrap_or(false))
            .flat_map(|(_, b)| b.names.iter().map(move |n| (n, &b.ty)))
            .collect();
        let (_, ty) = match slot {
            CtorSlot::Position(k) => *explicit.get(k)?,
            CtorSlot::Named(field) => *explicit.iter().find(|(n, _)| n.text == field)?,
        };
        let head = type_head(ty)?;
        let variable = head_variable(&head.text);
        let bound_in_decl = params
            .iter()
            .chain(decl.fields.iter())
            .flat_map(|b| &b.names)
            .chain(indices.iter().filter_map(|(n, _)| n.as_ref()))
            .any(|n| n.text == variable);
        (!bound_in_decl).then_some(head)
    }

    /// The key of the data type `head` names, if it is one (of this module
    /// or the library): the namespace a dot call on a value of that type
    /// looks in. `None` for anything else (a synonym, say), which dot calls
    /// may unfold.
    fn dot_namespace(&self, head: &ast::Name) -> Option<String> {
        match self.resolve(&head.text) {
            crate::scope::Resolved::Found {
                global: Global::Unchecked(j),
                rest,
                key,
                ..
            } if rest.is_empty() => {
                let item = &self.unit.module.items[j];
                (item.kind == Kind::Data && !item.synonym).then(|| key.to_string())
            }
            _ => self.data_namespace(head),
        }
    }

    /// Instances are found by type, so nothing names them where they're
    /// used: every definition and test is made to depend on every instance
    /// of the module that doesn't depend on it (so it's checked after
    /// them), and an instance on another one whose interface it mentions,
    /// or whose interface its own contains as a superclass (as far as the
    /// names say). An edge that would close a cycle is left out, so this
    /// never makes a cycle; an instance needed where it isn't checked yet is
    /// an error that says so (`interfaces.rs`). The instances are taken in
    /// source order.
    fn instance_edges(&mut self, items: &[Item]) {
        // Decision procedures keep their own rule (D9): only those checked
        // and above the use.
        let decidable = self
            .kernel
            .env
            .registry()
            .data(Builtin::Decidable)
            .map(Global::Data);
        let instances: Vec<usize> = (0..self.unit.module.items.len())
            .filter(|i| {
                let item = &self.unit.module.items[*i];
                item.instance
                    && item.interface != decidable
                    && match item.interface {
                        Some(Global::Unchecked(j)) => matches!(
                            items[j].decl,
                            Decl::Data {
                                interface: true,
                                ..
                            }
                        ),
                        _ => true,
                    }
            })
            .collect();
        if instances.is_empty() {
            return;
        }
        let add = |this: &mut Self, reached: &HashSet<usize>, from: usize, to: usize| {
            if from == to || reached.contains(&from) {
                return;
            }
            let span = this.unit.module.items[to].span;
            this.unit.module.items[from].deps.push(Dep {
                item: to,
                span,
                in_header: false,
                speculative: Some("it may use instances".to_string()),
            });
        };
        // A data type's own `DecEq` instance, without an own `Ord` one: its
        // `Ord` is derived once the instance is checked.
        let dec_eq = interfaces::dec_eq(self).map(Global::Data);
        let ord = interfaces::ord(self).map(Global::Data);
        let derives_ord: Vec<usize> = instances
            .iter()
            .copied()
            .filter(|&y| {
                let item = &self.unit.module.items[y];
                dec_eq.is_some()
                    && item.interface == dec_eq
                    && matches!(item.head, Some(Global::Unchecked(_)))
                    && !self.unit.module.items.iter().any(|other| {
                        other.instance && other.interface == ord && other.head == item.head
                    })
            })
            .collect();
        // Between instances: by the interfaces their declarations mention,
        // and their interfaces' superclasses.
        for &y in &instances {
            let Some(wanted) = self.unit.module.items[y].interface else {
                continue;
            };
            let reached = self.reachable(y);
            for &x in &instances {
                if x == y || self.unit.module.items[x].interface == Some(wanted) {
                    continue;
                }
                let mentions = self.mentions_global(x, &items[x], wanted)
                    || self.is_super_of(self.unit.module.items[x].interface, wanted, items)
                    || derives_ord.contains(&y)
                        && ord.is_some_and(|ord| self.mentions_global(x, &items[x], ord));
                if mentions {
                    add(self, &reached, x, y);
                }
            }
        }
        // Everything else that may use one.
        for &y in &instances {
            let reached = self.reachable(y);
            for x in 0..self.unit.module.items.len() {
                let kind = self.unit.module.items[x].kind;
                if self.unit.module.items[x].instance || !matches!(kind, Kind::Def | Kind::Test) {
                    continue;
                }
                add(self, &reached, x, y);
            }
        }
    }

    /// The items item `from` depends on, directly or not, itself included.
    /// (Adding edges into `from` never changes it, unless they close a
    /// cycle, which `instance_edges` doesn't do.)
    fn reachable(&self, from: usize) -> HashSet<usize> {
        let mut seen = HashSet::default();
        let mut pending = vec![from];
        while let Some(i) = pending.pop() {
            if !seen.insert(i) {
                continue;
            }
            pending.extend(self.unit.module.items[i].deps.iter().map(|d| d.item));
        }
        seen
    }

    /// Whether `item`'s declaration names `wanted` (or something in its
    /// namespace).
    fn mentions_global(&mut self, index: usize, item: &Item, wanted: Global) -> bool {
        self.unit.module.file = Some(self.unit.module.items[index].file);
        // A checked interface's methods are definitions in its namespace.
        let members = match wanted {
            Global::Data(d) => Some(format!("{}.", self.data_key(d))),
            _ => None,
        };
        let mut found = false;
        for (r, _) in decl_refs(item.decl, item.equations) {
            let n = match r {
                Ref::Name(n) | Ref::Dot(n, _, _) => n,
            };
            if let crate::scope::Resolved::Found { global, key, .. } = self.resolve(&n.text)
                && (global == wanted || members.as_ref().is_some_and(|m| key.starts_with(m)))
            {
                found = true;
                break;
            }
        }
        self.unit.module.file = None;
        found
    }

    /// Whether interface `parent` (a module item or a checked interface) is
    /// a superclass of interface `of`, directly or not, as far as the names
    /// in the module's interface declarations say.
    fn is_super_of(&self, of: Option<Global>, parent: Global, items: &[Item]) -> bool {
        let mut pending: Vec<Global> = of.into_iter().collect();
        let mut seen = Vec::new();
        while let Some(i) = pending.pop() {
            if seen.contains(&i) {
                continue;
            }
            seen.push(i);
            let parents: Vec<Global> = match i {
                Global::Data(d) => match self.tables.interfaces.get(&d) {
                    Some(info) => info.supers.iter().map(|(_, p)| Global::Data(*p)).collect(),
                    None => Vec::new(),
                },
                Global::Unchecked(j) => match items.get(j).map(|it| it.decl) {
                    Some(Decl::Data {
                        interface: true,
                        ctors,
                        ..
                    }) => ctors
                        .iter()
                        .flat_map(|c| &c.fields)
                        .filter_map(|b| crate::module::type_head(&b.ty))
                        .filter_map(|n| self.named(&n.text).map(|(g, _)| *g))
                        .collect(),
                    _ => Vec::new(),
                },
                _ => Vec::new(),
            };
            if parents.contains(&parent) {
                return true;
            }
            pending.extend(parents);
        }
        false
    }

    /// Names that were declared but never checked now just name failures:
    /// the module's own. Those waiting for open goals are noted as such
    /// (`Session::waiting_names`).
    fn fail_unchecked_names(&mut self) {
        let module = &self.unit.module;
        let mut waiting = self.session.waiting_names.borrow_mut();
        for key in &module.names {
            if let Some((Global::Unchecked(item), _)) = self.scope.stored(key) {
                match module.waiting.get(item) {
                    Some(goals) if module.items[*item].status == Status::Unfinished => {
                        waiting.insert(key.clone(), goals.clone());
                    }
                    _ => {
                        waiting.remove(key);
                    }
                }
                self.scope
                    .set_global(key, |global| *global = Global::Failed);
            } else {
                waiting.remove(key);
            }
        }
    }

    /// Step 3: the strongly connected components, in the order to check
    /// them: each after everything it depends on, and of those ready, the
    /// one starting earliest *in its file* first, ties by name. (Not by
    /// position in the module, which would follow the files' names and so
    /// let them decide what `auto` can use: docs/proposals/multi-file.md
    /// §4.9.5. With one file, this is source order.)
    fn components(&mut self) -> Vec<Vec<usize>> {
        let edges: Vec<Vec<usize>> = self
            .unit
            .module
            .items
            .iter()
            .map(|item| {
                let mut targets: Vec<usize> = item.deps.iter().map(|d| d.item).collect();
                targets.sort_unstable();
                targets.dedup();
                targets
            })
            .collect();
        // Where each file's declarations start.
        let mut file_start = vec![usize::MAX; self.unit.module.files.len()];
        for item in &self.unit.module.items {
            file_start[item.file] = file_start[item.file].min(item.position);
        }
        let components = tarjan(&edges);
        for (c, members) in components.iter().enumerate() {
            for &i in members {
                self.unit.module.items[i].component = c;
            }
        }
        // Kahn's algorithm over the components.
        let mut waiting_on = vec![0usize; components.len()];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); components.len()];
        for (i, targets) in edges.iter().enumerate() {
            let c = self.unit.module.items[i].component;
            for &j in targets {
                let d = self.unit.module.items[j].component;
                if d != c {
                    waiting_on[c] += 1;
                    dependents[d].push(c);
                }
            }
        }
        let start = |c: usize| {
            components[c]
                .iter()
                .map(|i| {
                    let item = &self.unit.module.items[*i];
                    (item.position - file_start[item.file], item.name.clone())
                })
                .min()
                .unwrap_or_default()
        };
        let mut ready: BinaryHeap<Reverse<((usize, String), usize)>> = (0..components.len())
            .filter(|c| waiting_on[*c] == 0)
            .map(|c| Reverse((start(c), c)))
            .collect();
        let mut order = Vec::new();
        while let Some(Reverse((_, c))) = ready.pop() {
            let mut members = components[c].clone();
            members.sort_by_key(|i| self.unit.module.items[*i].position);
            order.push(members);
            for &d in &dependents[c] {
                waiting_on[d] -= 1;
                if waiting_on[d] == 0 {
                    ready.push(Reverse((start(d), d)));
                }
            }
        }
        order
    }

    /// Checks one component, adding its errors (by source position).
    fn check_component(
        &mut self,
        items: &[Item],
        component: &[usize],
        diagnostics: &mut Vec<(usize, Diagnostic)>,
    ) {
        let first = &items[component[0]];
        if component
            .iter()
            .any(|i| self.unit.module.items[*i].status.failed())
        {
            // Already reported (a constructor or operation name taken).
            return;
        }
        let recursive = component.len() > 1
            || self.unit.module.items[component[0]]
                .deps
                .iter()
                .any(|d| d.item == component[0]);
        let kinds: Vec<Kind> = component
            .iter()
            .map(|i| self.unit.module.items[*i].kind)
            .collect();
        if recursive && component.iter().all(|i| self.unit.module.items[*i].synonym) {
            diagnostics.push((first.position, self.synonym_cycle(component)));
            return;
        }
        let all_data = kinds.iter().all(|k| *k == Kind::Data);
        if component.len() > 1 && kinds.iter().any(|k| *k != Kind::Def) && !all_data {
            diagnostics.push((first.position, self.mixed_cycle(component)));
            return;
        }
        if component.len() > 1 && all_data {
            // A header (parameters or universe) may only mention what's
            // finished before the group.
            let mut refused = false;
            for &i in component {
                let mut reported = Vec::new();
                for dep in self.unit.module.items[i].deps.clone() {
                    if dep.in_header
                        && dep.speculative.is_none()
                        && self.unit.module.in_current(dep.item)
                        && !reported.contains(&dep.item)
                    {
                        reported.push(dep.item);
                        diagnostics
                            .push((items[i].position, self.mutual_header(i, dep.item, dep.span)));
                        refused = true;
                    }
                }
            }
            if refused {
                return;
            }
            let members: Vec<(Option<usize>, &Decl)> = component
                .iter()
                .map(|i| (Some(*i), items[*i].decl))
                .collect();
            let found = self.data_group(&members);
            diagnostics.extend(
                found
                    .into_iter()
                    .map(|(i, d)| (items[i.unwrap_or(component[0])].position, d)),
            );
            return;
        }
        if kinds[0] == Kind::Def && recursive {
            // A signature may only mention what's finished before it.
            let mut refused = false;
            for &i in component {
                let mut reported = Vec::new();
                for dep in self.unit.module.items[i].deps.clone() {
                    // Once for each sibling, at its first use.
                    if dep.in_header
                        && dep.speculative.is_none()
                        && self.unit.module.in_current(dep.item)
                        && !reported.contains(&dep.item)
                    {
                        reported.push(dep.item);
                        let d = if in_default(items[i].decl, dep.span) {
                            let names = &self.unit.module.items;
                            default_uses(&names[i].name, &names[dep.item].name, dep.span)
                        } else {
                            self.mutual_signature(i, dep.item, dep.span)
                        };
                        diagnostics.push((items[i].position, d));
                        refused = true;
                    }
                }
            }
            if refused {
                return;
            }
            let members: Vec<(usize, &Decl, &[Decl])> = component
                .iter()
                .map(|i| (*i, items[*i].decl, items[*i].equations))
                .collect();
            let found = self.group(&members, true);
            diagnostics.extend(
                found
                    .into_iter()
                    .map(|(i, d)| (items[i].position, self.explain_lifted(d))),
            );
            return;
        }
        let index = component[0];
        let item = &items[index];
        self.unit.module.item = Some(index);
        let result = match item.decl {
            decl @ Decl::Data { .. } => self.data(decl),
            decl @ Decl::Ability { .. } => self.ability(decl),
            Decl::Test { name, expr, span } => self.test(name, expr, *span),
            decl @ Decl::Signature { .. } => {
                let found = self.group(&[(index, decl, item.equations)], false);
                diagnostics.extend(
                    found
                        .into_iter()
                        .map(|(i, d)| (items[i].position, self.explain_lifted(d))),
                );
                return;
            }
            Decl::Equation { .. } => unreachable!("equations go with signatures"),
        };
        diagnostics.extend(self.unit.warnings.drain(..).map(|w| (item.position, w)));
        diagnostics.extend(
            self.attempt
                .lambda_warnings
                .take()
                .into_iter()
                .map(|w| (item.position, w)),
        );
        if let Err(d) = result {
            diagnostics.push((item.position, self.explain_lifted(d)));
        }
    }

    /// The full names of a component's declarations, for `STITCHWORT_TIMINGS`.
    fn component_label(&self, items: &[Item], component: &[usize]) -> String {
        let prefix = if self.unit.namespace_root.is_empty() {
            format!("{}.", self.unit.module_path)
        } else {
            self.unit.namespace_root.clone()
        };
        let names: Vec<String> = component
            .iter()
            .map(|&i| match items[i].decl {
                Decl::Test { name, .. } => format!("{prefix}test {name:?}"),
                decl => match declared_names(decl).0 {
                    Some(n) => format!("{prefix}{}", n.text),
                    None => format!("{prefix}?"),
                },
            })
            .collect();
        names.join(", ")
    }

    /// A path of references from `from` to `to`, through the component
    /// being checked: the items along it, starting with `from` and ending
    /// with `to`.
    fn path_within(&self, from: usize, to: usize) -> Vec<usize> {
        let mut parent: HashMap<usize, usize> = HashMap::default();
        let mut queue = std::collections::VecDeque::from([from]);
        while let Some(i) = queue.pop_front() {
            for dep in &self.unit.module.items[i].deps {
                let j = dep.item;
                if !self.unit.module.in_current(j) || parent.contains_key(&j) || j == from {
                    continue;
                }
                parent.insert(j, i);
                if j == to {
                    let mut path = vec![to];
                    let mut at = to;
                    while let Some(&p) = parent.get(&at) {
                        path.push(p);
                        at = p;
                        if p == from {
                            break;
                        }
                    }
                    path.reverse();
                    return path;
                }
                queue.push_back(j);
            }
        }
        vec![from, to]
    }

    /// "`a` uses `b`, which uses `c`".
    fn describe_path(&self, path: &[usize]) -> String {
        let quoted = |i: &usize| format!("`{}`", self.unit.module.items[*i].name);
        let mut out = quoted(&path[0]);
        for (k, i) in path[1..].iter().enumerate() {
            out.push_str(if k == 0 { " uses " } else { ", which uses " });
            out.push_str(&quoted(i));
        }
        out
    }

    /// The error for a cycle among type synonyms: they stand for each other,
    /// so none of them has a type to stand for.
    fn synonym_cycle(&self, component: &[usize]) -> Diagnostic {
        let items = &self.unit.module.items;
        let first = component[0];
        let back = items[first]
            .deps
            .iter()
            .map(|d| d.item)
            .find(|&j| j != first && self.unit.module.in_current(j));
        let cycle = match back {
            Some(back) => {
                let mut cycle = vec![first];
                cycle.extend(self.path_within(back, first));
                cycle
            }
            None => vec![first, first],
        };
        let what = match component {
            [only] => format!(
                "the type synonym `{}` is defined in terms of itself, so it has no meaning",
                items[*only].name
            ),
            [a, b] => format!(
                "the type synonyms `{}` and `{}` are defined in terms of each other, so neither \
                 has a meaning",
                items[*a].name, items[*b].name
            ),
            _ => format!(
                "the type synonyms {} are defined in terms of each other, so none has a meaning",
                listed(component.iter().map(|i| &items[*i].name))
            ),
        };
        let trail: Vec<&str> = cycle.iter().map(|&i| items[i].name.as_str()).collect();
        Diagnostic::error("E-SYNONYM-CYCLE", what)
            .with_label(
                items[first].span,
                format!("`{}` is defined here", items[first].name),
            )
            .with_note(format!("the cycle is `{}`", trail.join(" -> ")))
            .with_note(
                "a type synonym stands for its definition, so a cycle never reaches a type; \
                 break the cycle by defining at least one of them as a data type with \
                 constructors",
            )
    }

    /// The error for a cycle that mixes data types and definitions, or
    /// includes an ability.
    fn mixed_cycle(&self, component: &[usize]) -> Diagnostic {
        let items = &self.unit.module.items;
        let first = component[0];
        let back = items[first]
            .deps
            .iter()
            .find(|d| d.item != first && self.unit.module.in_current(d.item))
            .map_or(first, |d| d.item);
        let mut cycle = vec![first];
        cycle.extend(self.path_within(back, first));
        let names = listed(component.iter().map(|i| &items[*i].name));
        let ability = component.iter().any(|i| items[*i].kind == Kind::Ability);
        let mut d = if ability {
            Diagnostic::error(
                "E-MUTUAL-KIND",
                format!(
                    "{names} refer to each other, but an ability can't be defined together with \
                     what it uses"
                ),
            )
        } else {
            Diagnostic::error(
                "E-MUTUAL-KIND",
                format!(
                    "{names} refer to each other, but data types and definitions can't be defined \
                     together"
                ),
            )
        };
        for &i in component {
            d = d.with_label(
                items[i].span,
                format!("`{}` is defined here", items[i].name),
            );
        }
        d = d.with_note(self.describe_path(&cycle));
        if let Some(note) = self.speculative_note(component) {
            return d.with_note(note).with_note(
                "the dependency may be artificial: dot notation can only be resolved once types \
                 are known, so this program may not really be defining a type and a function \
                 together",
            );
        }
        if ability {
            d.with_note(
                "an ability's operations can't mention a type or definition that uses the ability: \
                 a stored computation could then call itself forever (Landin's knot)",
            )
        } else {
            d.with_note(
                "a data type's constructors can't use a definition that's being defined with \
                 it, and a definition can't use a data type before its constructors are finished",
            )
        }
    }

    /// Why a component may exist only because of dot notation: the first
    /// speculative reference between its members, as a note.
    pub(crate) fn speculative_note(&self, component: &[usize]) -> Option<String> {
        let items = &self.unit.module.items;
        component.iter().find_map(|&i| {
            items[i].deps.iter().find_map(|d| {
                let why = d.speculative.as_ref()?;
                component.contains(&d.item).then(|| {
                    format!(
                        "in `{}`, {why}, so `{}` and `{}` are checked together; write the full \
                         name, as in `T.f x`, or write the receiver's type, to say which function \
                         is meant",
                        items[i].name, items[i].name, items[d.item].name
                    )
                })
            })
        })
    }

    /// The error for a data type's header (of `item`) that mentions
    /// `other`, in the same group, at `span`.
    fn mutual_header(&self, item: usize, other: usize, span: Span) -> Diagnostic {
        let items = &self.unit.module.items;
        let (name, other_name) = (&items[item].name, &items[other].name);
        let path = self.path_within(other, item);
        let mut d = Diagnostic::error(
            "E-MUTUAL-SIGNATURE",
            format!(
                "`{name}`'s parameters or universe mention `{other_name}`, which is defined \
                 together with it"
            ),
        )
        .with_label(
            span,
            format!("`{other_name}` is used here, in `{name}`'s header"),
        );
        if item != other {
            d = d
                .with_label(items[other].span, format!("`{other_name}` is defined here"))
                .with_note(format!(
                    "they're checked together because {}",
                    self.describe_path(&path)
                ));
        }
        d.with_note(
            "a data type's parameters can only use declarations that are finished before it, and \
             data types that refer to each other are finished together",
        )
    }

    /// The error for a signature (of `item`) that mentions `other`, in the
    /// same group, at `span`.
    fn mutual_signature(&self, item: usize, other: usize, span: Span) -> Diagnostic {
        let items = &self.unit.module.items;
        let (name, other_name) = (&items[item].name, &items[other].name);
        if item == other {
            return Diagnostic::error(
                "E-MUTUAL-SIGNATURE",
                format!("`{name}`'s type mentions `{name}` itself"),
            )
            .with_label(span, format!("`{name}` is used here, in its own type"))
            .with_note("a definition's type can only mention definitions that are finished");
        }
        let path = self.path_within(other, item);
        Diagnostic::error(
            "E-MUTUAL-SIGNATURE",
            format!("`{name}`'s type mentions `{other_name}`, which is defined together with it"),
        )
        .with_label(
            span,
            format!("`{other_name}` is used here, in `{name}`'s type"),
        )
        .with_label(items[other].span, format!("`{other_name}` is defined here"))
        .with_note(format!(
            "they're checked together because {}",
            self.describe_path(&path)
        ))
        .with_note(
            "a definition's type can only mention definitions that are finished before it, and \
             definitions that call each other are finished together; move what the type needs \
             out of the cycle",
        )
    }

    /// Notes that the declaration being checked uses `item` of this
    /// module, so waits for the goals it waits for, if any.
    fn note_waits_for(&self, item: usize) {
        for id in self
            .unit
            .module
            .waiting
            .get(&item)
            .into_iter()
            .flat_map(|g| g.iter())
        {
            goals::note_used_unfinished(*id);
        }
    }

    /// The error for using `name`, which names a failed declaration: one
    /// that is waiting for open goals (`Session::waiting_names`) is
    /// unfinished, and its user waits for the same goals.
    pub(crate) fn failed_global(&self, name: &ast::Name) -> Diagnostic {
        let waits = match self.resolve(&name.text) {
            crate::scope::Resolved::Found { key, .. } => {
                if !self.unit.module.names.contains(key)
                    || self.unit.module.parse_failed.contains_key(key)
                {
                    note_failed_used(key);
                }
                self.session.waiting_names.borrow().get(key).cloned()
            }
            _ => None,
        };
        let Some(waits) = waits else {
            return failed_name(name);
        };
        for id in waits.iter() {
            goals::note_used_unfinished(*id);
        }
        goals::uses_unfinished(Some(name.span))
    }

    /// The error for using `name`, which declaration `item` of this module
    /// declares, before it's checked.
    pub(crate) fn unchecked(&self, name: &ast::Name, item: usize) -> Diagnostic {
        let info = &self.unit.module.items[item];
        if info.status == Status::Failed {
            return failed_name(name);
        }
        if info.status == Status::Unfinished {
            self.note_waits_for(item);
            return goals::uses_unfinished(Some(name.span));
        }
        if self.unit.module.in_current(item) {
            let current = self.unit.module.item.unwrap_or(item);
            let owner = &self.unit.module.items[current].name;
            return match self.unit.module.phase {
                Phase::Signature => self.mutual_signature(current, item, name.span),
                Phase::Header => Diagnostic::error(
                    "E-MUTUAL-SIGNATURE",
                    format!("`{}` can't be used in `{owner}`'s parameters", name.text),
                )
                .with_label(name.span, "used here")
                .with_note("a data type's parameters can only use declarations that are finished"),
                Phase::Fields if item == current => Diagnostic::error(
                    "E-MUTUAL-CONSTRUCTOR",
                    format!(
                        "`{}` can't be used in the constructors of `{owner}`, which declares it",
                        name.text
                    ),
                )
                .with_label(name.span, "used here")
                .with_note(
                    "a data type's fields can mention the type itself, but not its constructors: \
                     they don't exist until the fields are finished",
                ),
                Phase::Fields => Diagnostic::error(
                    "E-MUTUAL-CONSTRUCTOR",
                    format!(
                        "`{}` can't be used in the constructors of `{owner}`, which is defined \
                         together with `{}`",
                        name.text, info.name
                    ),
                )
                .with_label(name.span, "used here")
                .with_label(info.span, format!("`{}` is defined here", info.name))
                .with_note(format!(
                    "the fields of data types defined together can mention the types, like \
                     `{}`, but not their constructors: those don't exist until all the fields \
                     are finished",
                    info.name
                )),
                Phase::Body if item == current && info.kind == Kind::Ability => Diagnostic::error(
                    "E-ABILITY",
                    format!(
                        "`{}` can't be used in the types of `{owner}`'s operations",
                        name.text
                    ),
                )
                .with_label(name.span, "used here")
                .with_note(
                    "an ability's operations don't exist until all of their types are \
                         finished",
                ),
                Phase::Body => internal_order(name),
            };
        }
        internal_order(name)
    }

    /// Notes for `E-AUTO-NONE`: decision procedures in this module that
    /// `auto` couldn't use where it's being elaborated, and why.
    pub(crate) fn auto_hints(&self) -> Vec<String> {
        let Some(current) = self.unit.module.item else {
            return Vec::new();
        };
        let items = &self.unit.module.items;
        let here = &items[current];
        let mut hints = Vec::new();
        for (j, item) in items.iter().enumerate() {
            if !item.decides {
                continue;
            }
            let name = &item.name;
            if self.unit.module.in_current(j) {
                hints.push(format!(
                    "`{name}` is checked together with `{}` (they refer to each other), so it \
                     can't run while they're being checked: move the proof out of the cycle",
                    here.name
                ));
            } else if item.status == Status::Failed {
                hints.push(format!("`{name}` has errors, so `auto` can't use it"));
            } else if item.status == Status::Unfinished {
                hints.push(format!(
                    "`{name}` isn't finished (it has an open goal, `?`), so `auto` can't use it"
                ));
            } else if item.file != here.file {
                let namespace = self.current_namespace().unwrap_or("this namespace");
                hints.push(format!(
                    "`{name}` is in another file of `{namespace}` (`{}`): `auto` only uses \
                     decision procedures from the same file, above the use, so pass it explicitly",
                    self.unit.module.files[item.file].name
                ));
            } else if item.position > here.position {
                hints.push(format!(
                    "`auto` only uses decision procedures defined above where it's used, and \
                     `{name}` is below: move it above `{}`, or pass it explicitly",
                    here.name
                ));
            } else if item.status == Status::Waiting {
                hints.push(format!(
                    "`{name}` is above `{}`, but isn't checked yet: {}. Pass it explicitly, so \
                     it's checked first",
                    here.name,
                    self.why_waiting(j)
                ));
            }
        }
        hints
    }

    /// Why `item`, which isn't checked, isn't: the chain of declarations it
    /// waits for.
    fn why_waiting(&self, item: usize) -> String {
        let items = &self.unit.module.items;
        let mut parent: HashMap<usize, usize> = HashMap::default();
        let mut queue = std::collections::VecDeque::from([item]);
        let mut end = None;
        while let Some(i) = queue.pop_front() {
            let waiting: Vec<usize> = items[i]
                .deps
                .iter()
                .map(|d| d.item)
                .filter(|j| *j != i && items[*j].status == Status::Waiting)
                .collect();
            if i != item && (waiting.is_empty() || self.unit.module.in_current(i)) {
                end = Some(i);
                break;
            }
            for j in waiting {
                if j != item && !parent.contains_key(&j) {
                    parent.insert(j, i);
                    queue.push_back(j);
                }
            }
        }
        let Some(end) = end else {
            return format!("`{}` waits for other declarations", items[item].name);
        };
        let mut path = vec![end];
        let mut at = end;
        while let Some(&p) = parent.get(&at) {
            path.push(p);
            at = p;
        }
        path.reverse();
        let current = self
            .unit
            .module
            .item
            .map(|c| items[c].name.clone())
            .unwrap_or_default();
        if self.unit.module.in_current(end) {
            format!(
                "{}, so it's checked after `{current}`",
                self.describe_path(&path)
            )
        } else {
            format!(
                "{}, which is checked after `{current}`",
                self.describe_path(&path)
            )
        }
    }

    /// Whether `auto` may use definition `id` where it's being elaborated:
    /// it's final, and (if it's from this module) declared above.
    pub(crate) fn auto_eligible(&self, id: DefId) -> bool {
        if self.kernel.def(id).body().is_none() {
            return false; // not finished checking (e.g. one being defined)
        }
        match (self.unit.module.def_items.get(&id), self.unit.module.item) {
            (Some(item), Some(current)) => {
                let (item, current) = (
                    &self.unit.module.items[*item],
                    &self.unit.module.items[current],
                );
                item.file == current.file && item.position < current.position
            }
            _ => true,
        }
    }
}

/// "`a`, `b` and `c`".
fn listed<'a>(names: impl Iterator<Item = &'a String>) -> String {
    let names: Vec<String> = names.map(|n| format!("`{n}`")).collect();
    match names.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => names.join(""),
    }
}

thread_local! {
    /// The keys of the failed declarations the component being checked was
    /// refused for using, as found where the refusal is made: by name
    /// lookup ([`Elaborator::failed_global`]), or by the kernel, whose
    /// refusals are reworded where only the environment is at hand
    /// ([`note_failed_in`]). The module empties it at the start of each
    /// component and reads it at the end, keeping those another namespace
    /// declares: the component waits for them (`E-USES-FAILED`).
    static FAILED_USED: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// The code of the error that fails a definition whose body didn't parse
/// (`Decl::Signature`'s `body_error`): its own error, so it gets a stand-in
/// and is the declaration its users' messages name, but never reported,
/// since the parser reported the syntax error at the same place.
pub(crate) const UNPARSED_BODY: &str = "E-UNPARSED-BODY";

/// The error failing a definition whose body has a syntax error at `at`
/// (`UNPARSED_BODY`).
pub(crate) fn unparsed_body(at: Span) -> Diagnostic {
    Diagnostic::error(UNPARSED_BODY, "this body didn't parse")
        .with_label(at, "the syntax error is here")
}

/// Notes that the declaration being checked was refused for using failed
/// declaration `key` (`FAILED_USED`).
pub(crate) fn note_failed_used(key: &str) {
    FAILED_USED.with(|u| u.borrow_mut().push(key.to_string()));
}

/// The failed declarations noted since the last call, emptying the list.
fn take_failed_used() -> Vec<String> {
    FAILED_USED.with(|u| std::mem::take(&mut *u.borrow_mut()))
}

/// Notes the failed definitions and data types `terms` refer to, other
/// than `own` (`FAILED_USED`): the kernel refused them for it. Each by its
/// name from the root, which is its key in the scope (its path has the
/// module's prefix, `Main.` for a single file, which no key has).
pub(crate) fn note_failed_in(
    g: &stitchwort_core::Ev,
    terms: &[&stitchwort_core::Term],
    own: &[stitchwort_core::globals::HashKey],
) {
    use stitchwort_core::Term;
    use stitchwort_core::globals::HashKey;
    for term in terms {
        for (t, _) in term.subterms() {
            let (key, state, path) = match t {
                Term::Def(id) if id.0 < g.env.defs().len() => {
                    let def = g.def(*id);
                    (HashKey::Def(*id), def.state(), def.name().to_string())
                }
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _)
                    if d.0 < g.env.datas().len() =>
                {
                    let data = g.data(*d);
                    (HashKey::Data(*d), data.state(), data.name().to_string())
                }
                _ => continue,
            };
            if state == State::Failed && !own.contains(&key) {
                note_failed_used(&path);
            }
        }
    }
}

/// Where `imports` import the declaration `key` by name, if they do: the
/// name in the import.
fn import_of(imports: &[ast::Import], key: &str) -> Option<Span> {
    imports.iter().find_map(|import| {
        let path = import.path.text.as_str();
        import.items.iter().find_map(|item| {
            let ns = key
                .strip_suffix(item.name.text.as_str())?
                .strip_suffix('.')?;
            (ns == path || ns.ends_with(&format!(".{path}"))).then_some(item.name.span)
        })
    })
}

/// The error for using a declaration that failed.
pub(crate) fn failed_name(name: &ast::Name) -> Diagnostic {
    Diagnostic::error("E-FAILED-DEPENDENCY", format!("`{}` has errors", name.text))
        .with_label(name.span, format!("`{}` has errors", name.text))
        .with_note(format!(
            "this can't be accepted until the errors in `{}` are fixed",
            name.text
        ))
}

fn internal_order(name: &ast::Name) -> Diagnostic {
    Diagnostic::error(
        "E-INTERNAL",
        format!(
            "internal error: `{}` is used before it's checked",
            name.text
        ),
    )
    .with_label(name.span, "here")
    .with_note("this is a bug in the compiler, not in your program")
}

/// The names a declaration declares: its own (none for a test), and those
/// of its constructors or operations (and what an ability generates).
/// Each other name is in the declaration's namespace, and is a constructor
/// or operation (visible wherever the type or ability is) or not.
pub(crate) fn declared_names(decl: &Decl) -> (Option<ast::Name>, Vec<(ast::Name, bool)>) {
    match decl {
        // An interface's methods are named in its namespace from the start,
        // so they can be imported (docs/proposals/interfaces.md §5.1).
        Decl::Data {
            name,
            ctors,
            interface: true,
            ..
        } => (
            Some(name.clone()),
            ctors
                .iter()
                .map(|c| (c.name.clone(), true))
                .chain(
                    ctors
                        .iter()
                        .flat_map(|c| &c.fields)
                        .flat_map(|b| &b.names)
                        .map(|n| (n.clone(), false)),
                )
                .collect(),
        ),
        Decl::Data { name, ctors, .. } => (
            Some(name.clone()),
            ctors.iter().map(|c| (c.name.clone(), true)).collect(),
        ),
        Decl::Ability {
            name, ops, span, ..
        } => {
            let generated = |text: String| (ast::Name { text, span: *span }, false);
            let mut others: Vec<(ast::Name, bool)> =
                ops.iter().map(|(op, _)| (op.clone(), true)).collect();
            others.extend(ops.iter().map(|(op, _)| generated(format!("%{}", op.text))));
            others.push(generated("%res".into()));
            others.push(generated("%elim".into()));
            (Some(name.clone()), others)
        }
        // A definition with `decreasing` has its equation, `f.unfold`
        // (docs/proposals/well-founded-recursion.md §6.2).
        Decl::Signature {
            name,
            decreasing: Some(measure),
            theorem: false,
            ..
        } => (
            Some(name.clone()),
            vec![(
                ast::Name {
                    text: "unfold".into(),
                    span: measure.span(),
                },
                false,
            )],
        ),
        // So has an opaque definition without an `unfolding` clause
        // (docs/proposals/opaque-definitions.md §6.3); one with a clause has
        // none (`E-NO-UNFOLD-EQUATION`, `opaque.rs`).
        Decl::Signature {
            name,
            opaque: true,
            theorem: false,
            unfolding,
            ..
        } if unfolding.is_empty() => (
            Some(name.clone()),
            vec![(
                ast::Name {
                    text: "unfold".into(),
                    span: name.span,
                },
                false,
            )],
        ),
        Decl::Signature { name, .. } => (Some(name.clone()), Vec::new()),
        Decl::Test { .. } | Decl::Equation { .. } => (None, Vec::new()),
    }
}

/// The name at the head of a signature's result, after its parameters.
/// Whether a written type is a function type with an explicit argument a
/// lambda could take (after any implicit parameters): `def entry(): T`
/// takes none, so `W-LAMBDA-SHADOW` doesn't ask about it.
pub(crate) fn is_function_type(ty: &Expr) -> bool {
    let mut ty = ty;
    loop {
        match ty {
            Expr::Arrow(dom, _)
            | Expr::Pi {
                dom,
                implicit: false,
                ..
            } => {
                return !matches!(**dom, Expr::Unit(_));
            }
            Expr::Pi { cod, .. } => ty = cod,
            _ => return false,
        }
    }
}

impl Elaborator {
    /// Whether the module's item `item`, not checked yet, is declared with a
    /// function type.
    pub(crate) fn item_is_function(&self, item: usize) -> bool {
        self.unit.module.items[item].function
    }
}

/// For an instance's type, the name at the head of the type it's for:
/// `List` in `[a: Type] -> DecEq (List a)`.
pub(crate) fn instance_head(ty: &Expr) -> Option<&ast::Name> {
    let mut ty = ty;
    while let Expr::Pi { cod, .. } | Expr::Arrow(_, cod) = ty {
        ty = cod;
    }
    match ty {
        Expr::App(_, arg) => type_head(arg),
        _ => None,
    }
}

/// The name at the head of a type expression: `Ord` in `Ord a`.
pub(crate) fn type_head(ty: &Expr) -> Option<&ast::Name> {
    let mut ty = ty;
    while let Expr::App(f, _) = ty {
        ty = f;
    }
    match ty {
        Expr::Var(n) => Some(n),
        _ => None,
    }
}

pub(crate) fn result_head(ty: &Expr) -> Option<&ast::Name> {
    let mut ty = ty;
    while let Expr::Pi { cod, .. } | Expr::Arrow(_, cod) = ty {
        ty = cod;
    }
    while let Expr::App(f, _) = ty {
        ty = f;
    }
    match ty {
        Expr::Var(n) => Some(n),
        _ => None,
    }
}

/// The names a definition's equations can use for its implicit parameters,
/// as the elaborator binds them: every implicit parameter along the
/// signature, until the explicit ones the equations' patterns match have
/// been passed.
fn body_binders<'a>(ty: &'a Expr, equations: &[Decl]) -> Vec<&'a str> {
    let arity = match equations.first() {
        Some(Decl::Equation { patterns, .. }) => patterns.len(),
        _ => 0,
    };
    let mut names = Vec::new();
    let mut explicit = 0;
    let mut ty = ty;
    loop {
        match ty {
            Expr::Pi {
                names: ns,
                implicit: true,
                cod,
                ..
            } => {
                names.extend(ns.iter().map(|n| n.text.as_str()));
                ty = cod;
            }
            Expr::Pi { names: ns, cod, .. } if explicit + ns.len() <= arity => {
                explicit += ns.len();
                ty = cod;
            }
            Expr::Arrow(_, cod) if explicit < arity => {
                explicit += 1;
                ty = cod;
            }
            _ => break,
        }
    }
    names
}

/// The types as written of a signature's explicit parameters that its
/// equations' patterns stand for, in order: `None` where a type has one of
/// the signature's own binders at its head, since an equation may name that
/// binder differently.
fn explicit_param_types<'a>(ty: &'a Expr, equations: &[Decl]) -> Vec<Option<&'a Expr>> {
    let arity = match equations.first() {
        Some(Decl::Equation { patterns, .. }) => patterns.len(),
        _ => 0,
    };
    let mut binders: Vec<&str> = Vec::new();
    let mut types = Vec::new();
    let known = |dom: &'a Expr, binders: &[&str]| {
        type_head(dom)
            .filter(|head| !binders.contains(&head_variable(&head.text)))
            .map(|_| dom)
    };
    let mut ty = ty;
    loop {
        match ty {
            Expr::Pi {
                names: ns,
                implicit: true,
                cod,
                ..
            } => {
                binders.extend(ns.iter().map(|n| n.text.as_str()));
                ty = cod;
            }
            Expr::Pi {
                names: ns,
                dom,
                cod,
                ..
            } if types.len() + ns.len() <= arity => {
                types.extend(ns.iter().map(|_| known(dom, &binders)));
                binders.extend(ns.iter().map(|n| n.text.as_str()));
                ty = cod;
            }
            Expr::Arrow(dom, cod) if types.len() < arity => {
                types.push(known(dom, &binders));
                ty = cod;
            }
            _ => break,
        }
    }
    types
}

/// An equation's patterns as walk steps: a variable in the place of a
/// parameter whose type is written is bound with that type.
fn equation_patterns<'a>(patterns: &'a [Pattern], types: &[Option<&'a Expr>]) -> Vec<Work<'a>> {
    patterns
        .iter()
        .enumerate()
        .map(
            |(k, pattern)| match (pattern, types.get(k).copied().flatten()) {
                (Pattern::Var(x), Some(ty)) => Work::BindTyped(&x.text, ty),
                _ => Work::Pattern(pattern),
            },
        )
        .collect()
}

/// The variable a name starts with: `p` in `p.name`.
fn head_variable(name: &str) -> &str {
    name.split_once('.').map_or(name, |(first, _)| first)
}

/// The error for a default of `name`'s that uses `other`: itself, or one
/// defined together with it.
pub(crate) fn default_uses(name: &str, other: &str, span: Span) -> Diagnostic {
    Diagnostic::error(
        "E-MUTUAL-SIGNATURE",
        format!("`{name}`'s default uses `{other}`"),
    )
    .with_label(span, format!("`{other}` is used here"))
    .with_note(
        "a parameter's default is checked from the header, before the body, so it can't use \
         the definition, or one defined together with it",
    )
}

/// Whether `span` is inside one of signature `decl`'s default values.
fn in_default(decl: &Decl, span: Span) -> bool {
    let Decl::Signature { defaults, .. } = decl else {
        return false;
    };
    defaults.iter().flatten().any(|d| {
        let at = d.span();
        at.file == span.file && at.start <= span.start && span.end <= at.end
    })
}

/// The walk of a header's default values, each with the parameters before
/// it bound.
fn defaults_work<'a>(ty: &'a Expr, defaults: &'a [Option<Expr>]) -> Vec<Work<'a>> {
    let mut names: Vec<&str> = Vec::new();
    let mut ty = ty;
    while names.len() < defaults.len() {
        match ty {
            Expr::Pi { names: ns, cod, .. } => {
                names.extend(ns.iter().map(|n| n.text.as_str()));
                ty = cod;
            }
            Expr::Arrow(_, cod) => {
                names.push("_");
                ty = cod;
            }
            _ => break,
        }
    }
    let mut work = Vec::new();
    for (k, default) in defaults.iter().enumerate() {
        let Some(default) = default else { continue };
        let before = &names[..k.min(names.len())];
        work.extend(before.iter().map(|x| Work::Bind(x)));
        work.push(Work::Expr(default));
        work.extend(before.iter().rev().map(|x| Work::Unbind(x)));
    }
    work
}

/// One step of the walk in [`free_names`].
#[derive(Clone)]
enum Work<'a> {
    Expr(&'a Expr),
    /// A pattern: its constructors are references, its variables binders
    /// (for the rest of the walk).
    Pattern(&'a Pattern),
    Bind(&'a str),
    /// A variable bound with its type as written.
    BindTyped(&'a str, &'a Expr),
    /// A variable bound as an argument of a constructor pattern.
    BindField(&'a str, &'a ast::Name, CtorSlot<'a>),
    Unbind(&'a str),
    /// A name that's a reference.
    Name(&'a ast::Name),
}

/// The free names of a declaration, in order, each with whether it's in the
/// declaration's header (a signature, or a data type's parameters and
/// universe). The dependency pre-pass and project analysis both read a
/// declaration through this, so they see the names checking resolves.
pub(crate) fn decl_refs<'a>(decl: &'a Decl, equations: &'a [Decl]) -> Vec<(Ref<'a>, bool)> {
    let mut out: Vec<(Ref<'a>, bool)> = Vec::new();
    let mut add = |refs: Vec<Ref<'a>>, in_header: bool| {
        out.extend(refs.into_iter().map(|r| (r, in_header)));
    };
    match decl {
        Decl::Signature {
            name,
            ty,
            unfolding,
            defaults,
            decreasing,
            ..
        } => {
            add(free_names(vec![Work::Expr(ty)]), true);
            // Defaults are checked before the body, from the header alone
            // (docs/proposals/signature-defaults.md §5.2).
            add(free_names(defaults_work(ty, defaults)), true);
            // What it unfolds is used by its body
            // (docs/proposals/opaque-definitions.md §6.11, rule 2).
            add(
                free_names(unfolding.iter().map(Work::Name).collect()),
                false,
            );
            let binders = body_binders(ty, equations);
            // The measure is checked with the header's parameters in scope,
            // before the body.
            if let Some(measure) = decreasing {
                let mut work: Vec<Work> = binders.iter().map(|x| Work::Bind(x)).collect();
                work.push(Work::Expr(measure));
                add(free_names(work), false);
            }
            let param_types = explicit_param_types(ty, equations);
            let mut body = Vec::new();
            for eq in equations {
                let Decl::Equation {
                    patterns,
                    guard,
                    rhs,
                    ..
                } = eq
                else {
                    continue;
                };
                let mut work: Vec<Work> = binders.iter().map(|x| Work::Bind(x)).collect();
                work.extend(equation_patterns(patterns, &param_types));
                if let Some(guard) = guard {
                    work.push(Work::Expr(&guard.cond));
                    work.extend(GUARD_LEMMAS.iter().map(Work::Name));
                    if let Some(h) = &guard.binder {
                        work.push(Work::Bind(&h.text));
                    }
                }
                work.extend(rhs.iter().map(Work::Expr));
                if let Some(h) = guard.as_ref().and_then(|g| g.binder.as_ref()) {
                    work.push(Work::Unbind(&h.text));
                }
                body.extend(names_and_proofs(work));
            }
            // A recursive call with no `[decreasing := …]` is proved by
            // `auto`, which tries `omega` when nothing else proves it.
            if decreasing.is_some() && unproved_recursive_call(name, &body) {
                body.push(Ref::Name(&REWRITE_MARKER));
            }
            body.retain(|r| !is_decreasing_proof(r));
            add(body, false);
        }
        Decl::Data {
            params,
            indices,
            sort,
            ctors,
            ..
        } => {
            let mut header = Vec::new();
            let mut bind_params = Vec::new();
            for binder in params {
                header.push(Work::Expr(&binder.ty));
                for n in &binder.names {
                    header.push(Work::Bind(&n.text));
                    bind_params.push(Work::Bind(&n.text));
                }
            }
            add(free_names(header), true);
            // The index telescope (`type T: Q -> Type`) is a header too. A
            // named index is bound in the later ones.
            let mut index_work = bind_params.clone();
            for (name, ty) in indices {
                index_work.push(Work::Expr(ty));
                if let Some(n) = name {
                    index_work.push(Work::Bind(&n.text));
                }
            }
            add(free_names(index_work), true);
            if let Some(sort) = sort {
                add(free_names(vec![Work::Expr(sort)]), true);
            }
            for ctor in ctors {
                let mut work = bind_params.clone();
                for (k, binder) in ctor.fields.iter().enumerate() {
                    work.push(Work::Expr(&binder.ty));
                    // A default sees the earlier fields
                    // (docs/proposals/named-arguments.md §5.1).
                    if let Some(Some(default)) = ctor.defaults.get(k) {
                        work.push(Work::Expr(default));
                    }
                    work.extend(binder.names.iter().map(|n| Work::Bind(&n.text)));
                }
                // The result type (`: Box a (Succ n)`) sees the fields.
                work.extend(ctor.result.iter().map(Work::Expr));
                add(free_names(work), false);
            }
        }
        Decl::Ability { params, ops, .. } => {
            let mut bind_params = Vec::new();
            let mut header = Vec::new();
            for binder in params {
                header.push(Work::Expr(&binder.ty));
                for n in &binder.names {
                    header.push(Work::Bind(&n.text));
                    bind_params.push(Work::Bind(&n.text));
                }
            }
            add(free_names(header), true);
            for (_, ty) in ops {
                let mut work = bind_params.clone();
                work.push(Work::Expr(ty));
                add(free_names(work), false);
            }
        }
        Decl::Test { expr, .. } => add(free_names(vec![Work::Expr(expr)]), false),
        Decl::Equation { .. } => {}
    }
    out
}

/// The references an expression makes (for `eval` and the REPL).
pub(crate) fn expr_refs(expr: &Expr) -> Vec<Ref<'_>> {
    free_names(vec![Work::Expr(expr)])
}

/// The names a header's default values use, other than its parameters.
pub(crate) fn default_refs<'a>(ty: &'a Expr, defaults: &'a [Option<Expr>]) -> Vec<Ref<'a>> {
    free_names(defaults_work(ty, defaults))
}

/// The library's `Float`, which a decimal literal refers to.
pub(crate) static FLOAT_TYPE: std::sync::LazyLock<ast::Name> =
    std::sync::LazyLock::new(|| ast::Name {
        text: "Std.Float".to_string(),
        span: stitchwort_syntax::Span::NOWHERE,
    });

/// A reference the pre-pass finds: a name, or dot notation's `.field`
/// (with where it's written, and the name at the head of the receiver's
/// type where that is known: `List` for `xs.length` with `(xs: List a)`).
pub(crate) enum Ref<'a> {
    Name(&'a ast::Name),
    Dot(&'a ast::Name, String, Option<Receiver<'a>>),
}

/// What the pre-pass knows of a dot call's receiver before anything is
/// elaborated.
#[derive(Clone, Copy)]
pub(crate) enum Receiver<'a> {
    /// The name at the head of its written type.
    Type(&'a ast::Name),
    /// A variable a pattern binds as a constructor's argument; its type is
    /// the field's, if that is written ([`Elaborator::receiver_head`]).
    Field(&'a ast::Name, CtorSlot<'a>),
}

/// Which argument of a constructor pattern.
#[derive(Clone, Copy)]
pub(crate) enum CtorSlot<'a> {
    /// The `k`th explicit field, in `Jmp offset`.
    Position(usize),
    /// A named field, in `Jmp { offset = o }`.
    Named(&'a str),
}

impl<'a> Receiver<'a> {
    /// The written type's head, when that is all there is to know.
    pub(crate) fn written(self) -> Option<&'a ast::Name> {
        match self {
            Receiver::Type(head) => Some(head),
            Receiver::Field(..) => None,
        }
    }
}

/// A reference no declaration can have: a `rewrite` is here, or another
/// proof that may be `omega`'s (a `cases`, or a recursive call of a
/// definition with `decreasing` that gives no proof). A program's module
/// loads `omega`'s library for it ([`Elaborator::dependencies`]);
/// a library file doesn't, since `omega`'s library is built on files that
/// use `rewrite` (an edge back would be a cycle), so there a premise is
/// proved by `omega` only where the file loads it anyway.
pub(crate) static REWRITE_MARKER: std::sync::LazyLock<ast::Name> =
    std::sync::LazyLock::new(|| ast::Name {
        text: "%rewrite".to_string(),
        span: Span::NOWHERE,
    });

/// What a guarded arm's generated equations refer to, written nowhere: a
/// guard on a decided proposition tested by its `Bool` is stated as the
/// proposition, and its proofs go between the two with these
/// (`equations.rs`, `BranchLib::to_bool_lemmas`); so does a conjunction of
/// them (decided by `Decidable.and`).
pub(crate) static GUARD_LEMMAS: std::sync::LazyLock<[ast::Name; 5]> =
    std::sync::LazyLock::new(|| {
        [
            "Std.Decidable.toBoolOfNot",
            "Std.Decidable.refute",
            "Std.Bool.decTrue",
            "Std.Decidable.notNotOf",
            "Std.Decidable.not",
        ]
        .map(|text| ast::Name {
            text: text.to_string(),
            span: Span::NOWHERE,
        })
    });

/// What `x in c` refers to, written nowhere: the proposition on lists and
/// its decision, and `contains` (on sets and maps) as a dot call.
pub(crate) static MEMBERSHIP: std::sync::LazyLock<[ast::Name; 2]> =
    std::sync::LazyLock::new(|| {
        [crate::membership::LIST_MEM, crate::membership::LIST_DEC_MEM].map(|text| ast::Name {
            text: text.to_string(),
            span: Span::NOWHERE,
        })
    });

/// What `a ..< b` and `a ..= b` refer to, written nowhere.
pub(crate) static RANGE: std::sync::LazyLock<ast::Name> = std::sync::LazyLock::new(|| ast::Name {
    text: "Std.List.range".to_string(),
    span: Span::NOWHERE,
});

/// The variables a pattern binds.
fn pattern_binders<'a>(pattern: &'a Pattern, out: &mut Vec<&'a str>) {
    match pattern {
        Pattern::Var(x) => out.push(&x.text),
        Pattern::Ctor(_, args, _) => args.iter().for_each(|p| pattern_binders(p, out)),
        Pattern::Tuple(a, b, _) => {
            pattern_binders(a, out);
            pattern_binders(b, out);
        }
        Pattern::Cons(a, b, _) => {
            pattern_binders(a, out);
            pattern_binders(b, out);
        }
        Pattern::Record { fields, .. } | Pattern::CtorFields { fields, .. } => {
            fields.iter().for_each(|(_, p)| pattern_binders(p, out))
        }
        Pattern::Named(_, p, _) => pattern_binders(p, out),
        Pattern::Or(alternatives, _) => alternatives.iter().for_each(|p| pattern_binders(p, out)),
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => {}
    }
}

/// A reference no declaration can have: a `[decreasing := …]` argument is
/// here. Only [`names_and_proofs`] gives it.
static DECREASING_PROOF: std::sync::LazyLock<ast::Name> = std::sync::LazyLock::new(|| ast::Name {
    text: "%decreasing".to_string(),
    span: Span::NOWHERE,
});

fn is_decreasing_proof(r: &Ref<'_>) -> bool {
    matches!(r, Ref::Name(n) if std::ptr::eq(*n, &*DECREASING_PROOF))
}

/// Whether a body whose references, with its `[decreasing := …]`
/// arguments, are `refs` names `name` more often than it gives such a proof.
fn unproved_recursive_call(name: &ast::Name, refs: &[Ref<'_>]) -> bool {
    let short = name.text.rsplit('.').next().unwrap_or(&name.text);
    let calls = refs
        .iter()
        .filter(|r| match r {
            Ref::Name(n) => n.text == name.text || n.text == short,
            Ref::Dot(_, field, _) => field == short,
        })
        .count();
    let proofs = refs.iter().filter(|r| is_decreasing_proof(r)).count();
    calls > proofs
}

/// The name at the head of the written type `ty`, unless it is a local
/// variable.
fn written_head<'a>(
    bound: &HashMap<&str, Vec<Option<Receiver<'a>>>>,
    ty: &'a Expr,
) -> Option<&'a ast::Name> {
    type_head(ty).filter(|head| {
        !bound
            .get(head_variable(&head.text))
            .is_some_and(|bindings| !bindings.is_empty())
    })
}

/// The free names in `work`, in order: names used that aren't bound by a
/// binder around them.
fn free_names(work: Vec<Work<'_>>) -> Vec<Ref<'_>> {
    let mut out = names_and_proofs(work);
    out.retain(|r| !is_decreasing_proof(r));
    out
}

/// The free names of the expression `e`, in order.
pub(crate) fn free_names_of(e: &Expr) -> Vec<Ref<'_>> {
    free_names(vec![Work::Expr(e)])
}

/// [`free_names`], with [`DECREASING_PROOF`] where a `[decreasing := …]`
/// argument is. A work list rather than recursion, since expressions can
/// nest more deeply than recursion could follow.
fn names_and_proofs(work: Vec<Work<'_>>) -> Vec<Ref<'_>> {
    let mut stack: Vec<Work> = work;
    stack.reverse();
    // Each variable's bindings in scope, innermost last, with the name at the
    // head of its type where that's written and isn't itself a variable.
    let mut bound: HashMap<&str, Vec<Option<Receiver<'_>>>> = HashMap::default();
    let mut out = Vec::new();
    // Pushes steps to run in the order given.
    fn then<'a>(stack: &mut Vec<Work<'a>>, steps: Vec<Work<'a>>) {
        stack.extend(steps.into_iter().rev());
    }
    while let Some(step) = stack.pop() {
        let expr = match step {
            Work::Bind(x) => {
                bound.entry(x).or_default().push(None);
                continue;
            }
            Work::BindTyped(x, ty) => {
                let head = type_head(ty).filter(|head| {
                    !bound
                        .get(head_variable(&head.text))
                        .is_some_and(|bindings| !bindings.is_empty())
                });
                bound.entry(x).or_default().push(head.map(Receiver::Type));
                continue;
            }
            Work::BindField(x, ctor, slot) => {
                bound
                    .entry(x)
                    .or_default()
                    .push(Some(Receiver::Field(ctor, slot)));
                continue;
            }
            Work::Unbind(x) => {
                if let Some(bindings) = bound.get_mut(x) {
                    bindings.pop();
                }
                continue;
            }
            Work::Name(n) => {
                let binding = |x: &str| bound.get(x).and_then(|bindings| bindings.last().copied());
                if binding(&n.text).is_some() {
                    continue;
                }
                // `p.name`, with `p` local: dot notation. Only the first
                // field's receiver has a written type.
                match n
                    .text
                    .split_once('.')
                    .and_then(|(first, rest)| Some((binding(first)?, rest)))
                {
                    Some((head, rest)) => {
                        out.extend(
                            rest.split('.')
                                .enumerate()
                                .map(|(k, f)| Ref::Dot(n, f.to_string(), head.filter(|_| k == 0))),
                        );
                    }
                    None => out.push(Ref::Name(n)),
                }
                continue;
            }
            Work::Pattern(p) => {
                match p {
                    Pattern::Var(x) => bound.entry(&x.text).or_default().push(None),
                    Pattern::Ctor(n, args, _) => {
                        out.push(Ref::Name(n));
                        then(
                            &mut stack,
                            args.iter()
                                .scan(0, |k, arg| {
                                    // `[n := p]` names an implicit field; it
                                    // takes no position.
                                    if matches!(arg, Pattern::Named(..)) {
                                        return Some(Work::Pattern(arg));
                                    }
                                    *k += 1;
                                    Some(match arg {
                                        Pattern::Var(x) => {
                                            Work::BindField(&x.text, n, CtorSlot::Position(*k - 1))
                                        }
                                        _ => Work::Pattern(arg),
                                    })
                                })
                                .collect(),
                        );
                    }
                    Pattern::Tuple(a, b, _) => {
                        then(&mut stack, vec![Work::Pattern(a), Work::Pattern(b)]);
                    }
                    Pattern::Cons(a, b, _) => {
                        then(&mut stack, vec![Work::Pattern(a), Work::Pattern(b)]);
                    }
                    Pattern::Named(_, p, _) => then(&mut stack, vec![Work::Pattern(p)]),
                    Pattern::Or(alternatives, _) => {
                        then(&mut stack, alternatives.iter().map(Work::Pattern).collect());
                    }
                    Pattern::CtorFields { ctor, fields, .. } => {
                        out.push(Ref::Name(ctor));
                        then(
                            &mut stack,
                            fields
                                .iter()
                                .map(|(field, p)| match p {
                                    Pattern::Var(x) => {
                                        Work::BindField(&x.text, ctor, CtorSlot::Named(&field.text))
                                    }
                                    _ => Work::Pattern(p),
                                })
                                .collect(),
                        );
                    }
                    Pattern::Record { fields, .. } => {
                        then(
                            &mut stack,
                            fields.iter().map(|(_, p)| Work::Pattern(p)).collect(),
                        );
                    }
                    Pattern::Wildcard(_)
                    | Pattern::Absurd(_)
                    | Pattern::Nil(_)
                    | Pattern::Num(..)
                    | Pattern::NegNum(..)
                    | Pattern::Char(..) => {}
                }
                continue;
            }
            Work::Expr(e) => e,
        };
        match expr {
            Expr::Var(n) => stack.push(Work::Name(n)),
            // A decimal literal is a `Float`: it needs the library's.
            Expr::Float(..) => out.push(Ref::Name(&FLOAT_TYPE)),
            Expr::Num(..)
            | Expr::Str(..)
            | Expr::Include(..)
            | Expr::Char(..)
            | Expr::Type(..)
            | Expr::Prop(_)
            | Expr::Hole(_)
            | Expr::Goal(_)
            | Expr::Unit(_) => {}
            Expr::Binary(BinOp::In(_), a, b) => {
                out.extend(MEMBERSHIP.iter().map(Ref::Name));
                out.push(Ref::Dot(&MEMBERSHIP[0], "contains".to_string(), None));
                then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]);
            }
            Expr::Binary(BinOp::Range | BinOp::RangeThrough, a, b) => {
                out.push(Ref::Name(&RANGE));
                then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]);
            }
            Expr::App(a, b)
            | Expr::Arrow(a, b)
            | Expr::Binary(_, a, b)
            | Expr::Pipe(a, b)
            | Expr::Seq(a, b) => {
                then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]);
            }
            Expr::Neg(a, _, _) | Expr::Bracketed(a, _) | Expr::Interpolated(a, _) => {
                stack.push(Work::Expr(a))
            }
            Expr::Lam(names, body, _) => {
                let (bind, unbind) = binds(names);
                let mut steps = bind;
                steps.push(Work::Expr(body));
                steps.extend(unbind);
                then(&mut stack, steps);
            }
            Expr::TypedLam(name, _, ty, body, _) => {
                let (bind, unbind) = typed_binds(std::slice::from_ref(name), ty);
                let mut steps = vec![Work::Expr(ty)];
                steps.extend(bind);
                steps.push(Work::Expr(body));
                steps.extend(unbind);
                then(&mut stack, steps);
            }
            Expr::Pi {
                names, dom, cod, ..
            } => {
                let (bind, unbind) = typed_binds(names, dom);
                let mut steps = vec![Work::Expr(dom)];
                steps.extend(bind);
                steps.push(Work::Expr(cod));
                steps.extend(unbind);
                then(&mut stack, steps);
            }
            Expr::NamedArg(name, value, _, _) => {
                if name.text == "decreasing" {
                    out.push(Ref::Name(&DECREASING_PROOF));
                }
                stack.push(Work::Expr(value));
            }
            Expr::If {
                binder,
                cond,
                then: yes,
                otherwise,
                ..
            } => {
                let mut steps = vec![Work::Expr(cond)];
                steps.extend(binder.iter().map(|b| Work::Bind(&b.text)));
                steps.extend([Work::Expr(yes), Work::Expr(otherwise)]);
                steps.extend(binder.iter().map(|b| Work::Unbind(&b.text)));
                then(&mut stack, steps);
            }
            Expr::Ann(e, t, _) | Expr::Tuple(e, t, _) => {
                then(&mut stack, vec![Work::Expr(e), Work::Expr(t)]);
            }
            Expr::List(items, _) => then(&mut stack, items.iter().map(Work::Expr).collect()),
            Expr::Spread(e, _) => then(&mut stack, vec![Work::Expr(e)]),
            Expr::Record { base, fields, .. } => {
                let mut steps: Vec<Work> = base.iter().map(|b| Work::Expr(b)).collect();
                steps.extend(fields.iter().map(|(_, e)| Work::Expr(e)));
                then(&mut stack, steps);
            }
            Expr::CtorFields { ctor, fields, .. } => {
                stack.push(Work::Name(ctor));
                then(
                    &mut stack,
                    fields.iter().map(|(_, e)| Work::Expr(e)).collect(),
                );
            }
            Expr::Field(e, field) => {
                // A local variable's written type, when `e` is just that.
                let receiver = match &**e {
                    Expr::Var(n) => bound
                        .get(n.text.as_str())
                        .and_then(|bindings| bindings.last().copied().flatten()),
                    // `(e: T).f`
                    Expr::Ann(_, ty, _) => written_head(&bound, ty).map(Receiver::Type),
                    Expr::Bracketed(inner, _) => match &**inner {
                        Expr::Ann(_, ty, _) => written_head(&bound, ty).map(Receiver::Type),
                        _ => None,
                    },
                    _ => None,
                };
                out.push(Ref::Dot(field, field.text.clone(), receiver));
                // `f.eq2`, read as a field of `f`: the equations of `f`, which
                // the library and the core make on demand (`equations.rs`).
                if let Expr::Var(owner) = &**e
                    && (field.text == "induct"
                        || crate::equations::is_equation_name(&format!("f.{}", field.text)))
                {
                    out.push(Ref::Dot(owner, field.text.clone(), None));
                }
                stack.push(Work::Expr(e));
            }
            // What the proof `omega` writes refers to (crates/elab/src/omega.rs).
            Expr::Omega { facts, .. } => {
                out.extend(crate::omega::LIBRARY_NAMES.iter().map(Ref::Name));
                then(&mut stack, facts.iter().map(Work::Expr).collect());
            }
            // `cases` closes cases by `omega` (crates/elab/src/cases.rs): as
            // for `rewrite`, a program's `cases` loads its library.
            Expr::Cases { body, .. } => {
                out.push(Ref::Name(&REWRITE_MARKER));
                then(&mut stack, body.iter().map(|b| Work::Expr(b)).collect());
            }
            // And `ring` (crates/elab/src/ring.rs).
            Expr::Ring { facts, .. } => {
                out.extend(crate::ring::LIBRARY_NAMES.iter().map(Ref::Name));
                then(&mut stack, facts.iter().map(Work::Expr).collect());
            }
            Expr::Calc { first, steps, .. } => {
                let mut steps_work = vec![Work::Expr(first)];
                for step in steps {
                    steps_work.push(Work::Expr(&step.rhs));
                    steps_work.extend(step.proof.iter().map(Work::Expr));
                }
                then(&mut stack, steps_work);
            }
            Expr::Rewrite {
                rules,
                target,
                body,
                ..
            } => {
                // `rewrite` proves a rule's premises by `omega` (rewrite.rs,
                // `discharge`): a program's `rewrite` loads its library
                // ([`REWRITE_MARKER`]).
                out.push(Ref::Name(&REWRITE_MARKER));
                let mut steps_work: Vec<Work> =
                    rules.iter().map(|r| Work::Expr(&r.proof)).collect();
                steps_work.extend(target.iter().map(|t| Work::Expr(t)));
                steps_work.extend(body.iter().map(|b| Work::Expr(b)));
                then(&mut stack, steps_work);
            }
            Expr::Effect(row, ty) => {
                let mut steps: Vec<Work> = row.abilities.iter().map(Work::Expr).collect();
                steps.extend(row.tail.iter().map(Work::Name));
                steps.push(Work::Expr(ty));
                then(&mut stack, steps);
            }
            Expr::Let {
                name,
                ty,
                value,
                body,
                ..
            } => {
                let mut steps: Vec<Work> = ty.iter().map(|t| Work::Expr(t)).collect();
                steps.extend([
                    Work::Expr(value),
                    match ty {
                        Some(ty) => Work::BindTyped(&name.text, ty),
                        None => Work::Bind(&name.text),
                    },
                    Work::Expr(body),
                    Work::Unbind(&name.text),
                ]);
                then(&mut stack, steps);
            }
            Expr::Match {
                scrutinees, alts, ..
            } => {
                let mut steps: Vec<Work> = scrutinees.iter().map(|s| Work::Expr(&s.expr)).collect();
                for alt in alts {
                    // The patterns' constructors are references; their
                    // variables are bound in the body only.
                    let mut vars = Vec::new();
                    for p in &alt.patterns {
                        pattern_binders(p, &mut vars);
                        steps.push(Work::Pattern(p));
                    }
                    if let Some(guard) = &alt.guard {
                        steps.push(Work::Expr(&guard.cond));
                        steps.extend(GUARD_LEMMAS.iter().map(Work::Name));
                        if let Some(h) = &guard.binder {
                            steps.push(Work::Bind(&h.text));
                            vars.push(&h.text);
                        }
                    }
                    steps.extend(alt.body.as_ref().map(Work::Expr));
                    steps.extend(vars.into_iter().map(Work::Unbind));
                }
                then(&mut stack, steps);
            }
            // The definitions' names are bound in all of them and the rest
            // of the block.
            Expr::LocalDefs { defs, body, .. } => {
                let names: Vec<&str> = defs.iter().filter_map(local_name).collect();
                let mut steps: Vec<Work> = names.iter().map(|x| Work::Bind(x)).collect();
                for def in defs {
                    steps.extend(local_def_work(def));
                }
                steps.push(Work::Expr(body));
                steps.extend(names.iter().map(|x| Work::Unbind(x)));
                then(&mut stack, steps);
            }
            Expr::Induct { call, alts, .. } => {
                let mut steps = vec![Work::Expr(call)];
                for alt in alts {
                    steps.extend(alt.binders.iter().map(|b| Work::Bind(&b.text)));
                    steps.push(Work::Expr(&alt.body));
                    steps.extend(alt.binders.iter().map(|b| Work::Unbind(&b.text)));
                }
                then(&mut stack, steps);
            }
            Expr::Handle { body, clauses, .. }
            | Expr::Reify {
                thunk: body,
                clauses,
                ..
            } => {
                let mut steps = vec![Work::Expr(body)];
                for clause in clauses {
                    match clause {
                        Clause::Return { var, body } => steps.extend([
                            Work::Bind(&var.text),
                            Work::Expr(body),
                            Work::Unbind(&var.text),
                        ]),
                        Clause::Op { op, arg, k, body } => {
                            steps.push(Work::Name(op));
                            let arg_var = match arg {
                                Pattern::Var(x) => Some(x.text.as_str()),
                                _ => None,
                            };
                            let mut arg_vars = Vec::new();
                            if arg_var.is_none() {
                                pattern_binders(arg, &mut arg_vars);
                                steps.push(Work::Pattern(arg));
                            }
                            steps.extend(arg_var.map(Work::Bind));
                            steps.extend([
                                Work::Bind(&k.text),
                                Work::Expr(body),
                                Work::Unbind(&k.text),
                            ]);
                            steps.extend(arg_var.map(Work::Unbind));
                            steps.extend(arg_vars.into_iter().map(Work::Unbind));
                        }
                    }
                }
                then(&mut stack, steps);
            }
        }
    }
    out
}

/// A local definition's name.
fn local_name(def: &ast::LocalDef) -> Option<&str> {
    match &def.signature {
        Decl::Signature { name, .. } => Some(&name.text),
        _ => None,
    }
}

/// The walk of a local definition: its type, then each equation with its
/// variables bound.
fn local_def_work(def: &ast::LocalDef) -> Vec<Work<'_>> {
    let Decl::Signature { ty, defaults, .. } = &def.signature else {
        return Vec::new();
    };
    let mut work = vec![Work::Expr(ty)];
    work.extend(defaults_work(ty, defaults));
    let binders = body_binders(ty, &def.equations);
    let param_types = explicit_param_types(ty, &def.equations);
    for eq in &def.equations {
        let Decl::Equation {
            patterns,
            guard,
            rhs,
            ..
        } = eq
        else {
            continue;
        };
        let mut vars = Vec::new();
        for p in patterns {
            pattern_binders(p, &mut vars);
        }
        work.extend(binders.iter().map(|x| Work::Bind(x)));
        work.extend(equation_patterns(patterns, &param_types));
        if let Some(guard) = guard {
            work.push(Work::Expr(&guard.cond));
            work.extend(GUARD_LEMMAS.iter().map(Work::Name));
            if let Some(h) = &guard.binder {
                work.push(Work::Bind(&h.text));
            }
        }
        work.extend(rhs.iter().map(Work::Expr));
        if let Some(h) = guard.as_ref().and_then(|g| g.binder.as_ref()) {
            work.push(Work::Unbind(&h.text));
        }
        work.extend(vars.into_iter().map(Work::Unbind));
        work.extend(binders.iter().map(|x| Work::Unbind(x)));
    }
    work
}

/// The names a local definition refers to (and doesn't bind itself).
pub(crate) fn local_refs(def: &ast::LocalDef) -> Vec<String> {
    free_names(local_def_work(def))
        .into_iter()
        .filter_map(|r| match r {
            Ref::Name(n) => Some(n.text.clone()),
            Ref::Dot(..) => None,
        })
        .collect()
}

/// Binding `names`, all of type `ty` as written, around a part of an
/// expression: the steps before it and after it.
fn typed_binds<'a>(names: &'a [ast::Name], ty: &'a Expr) -> (Vec<Work<'a>>, Vec<Work<'a>>) {
    (
        names.iter().map(|n| Work::BindTyped(&n.text, ty)).collect(),
        names.iter().map(|n| Work::Unbind(&n.text)).collect(),
    )
}

/// Binding `names` around a part of an expression: the steps before it and
/// after it.
fn binds(names: &[ast::Name]) -> (Vec<Work<'_>>, Vec<Work<'_>>) {
    (
        names.iter().map(|n| Work::Bind(&n.text)).collect(),
        names.iter().map(|n| Work::Unbind(&n.text)).collect(),
    )
}

/// Tarjan's strongly connected components of a graph given by adjacency
/// lists, without recursion. Each component's members, components in no
/// particular order.
pub(crate) fn tarjan(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut index = vec![usize::MAX; n];
    let mut low = vec![0; n];
    let mut on_stack = vec![false; n];
    let mut stack = Vec::new();
    let mut components = Vec::new();
    let mut next = 0;
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        // (node, how many of its edges have been followed)
        let mut calls = vec![(root, 0)];
        index[root] = next;
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (v, ref mut e)) = calls.last_mut() {
            if let Some(&w) = edges[v].get(*e) {
                *e += 1;
                if index[w] == usize::MAX {
                    index[w] = next;
                    low[w] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w] = true;
                    calls.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            calls.pop();
            if let Some(&(parent, _)) = calls.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                let mut component = Vec::new();
                loop {
                    let w = stack.pop().expect("v is on the stack");
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                components.push(component);
            }
        }
    }
    components
}

#[cfg(test)]
mod tests {
    use super::tarjan;

    #[test]
    fn finds_components() {
        // 0 → 1 → 2 → 0, 2 → 3, 3 → 3, 4 alone.
        let edges = vec![vec![1], vec![2], vec![0, 3], vec![3], vec![]];
        let mut found: Vec<Vec<usize>> = tarjan(&edges)
            .into_iter()
            .map(|mut c| {
                c.sort();
                c
            })
            .collect();
        found.sort();
        assert_eq!(found, vec![vec![0, 1, 2], vec![3], vec![4]]);
    }
}
