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

use crate::kernel;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::{HashKey, State};
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId};
use stitchwort_syntax::ast::{self, BinOp, Clause, Decl, Expr, Module, Pattern};
use stitchwort_syntax::{Diagnostic, FileId, Severity, Span};

use crate::project::SourceUnit;
use crate::{Elaborator, Global, RESERVED, error, goals};

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
    /// The first definition and test the module declares.
    pub first_def: usize,
    pub first_test: usize,
    /// The items of the component being checked.
    pub current: Vec<usize>,
    /// The item being elaborated.
    pub item: Option<usize>,
    pub phase: Phase,
    /// The item that declared each definition of this module.
    pub def_items: HashMap<DefId, usize>,
    /// The key of every name the module declares.
    pub names: HashSet<String>,
}

impl ModuleState {
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

impl Elaborator {
    /// Elaborates and checks every declaration of one file, continuing past
    /// errors. Declarations may refer to each other in any order.
    pub fn elaborate_module(&mut self, module: &Module) -> Vec<Diagnostic> {
        let namespace = match &module.namespace {
            Some(decl) if !self.loading_prelude => {
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
        crate::timings::begin(&self.globals);
        let (diagnostics, hit) = run(self);
        let label = namespace
            .map(str::to_string)
            .or_else(|| files.first().map(|f| f.name.to_string()))
            .filter(|l| !l.is_empty())
            .unwrap_or_else(|| {
                if self.loading_prelude {
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
        crate::timings::end(&self.globals, label);
        diagnostics
    }

    pub(crate) fn elaborate_namespace_untimed(
        &mut self,
        namespace: Option<&str>,
        files: &[SourceUnit],
        closure: Option<&[String]>,
    ) -> Vec<Diagnostic> {
        // A namespace has its own scope, so its own congruence lemmas.
        self.cong_candidates.borrow_mut().clear();
        // User code is elaborated only once every built-in is bound
        // (docs/proposals/namespaces.md §4.7).
        if !self.loading_prelude
            && let Err(d) = stitchwort_core::registry::check_complete_core(&self.globals)
        {
            return vec![d];
        }
        match namespace {
            Some(ns) if !self.loading_prelude => {
                self.namespace_root = format!("{ns}.");
                self.globals.module = "".into();
            }
            _ => {
                self.namespace_root = String::new();
                self.globals.module = if self.loading_prelude { "Std" } else { "Main" }.into();
            }
        }
        let mut diagnostics: Vec<(usize, Diagnostic)> = Vec::new();
        let mut first_test = self.tests.len();
        self.module = ModuleState {
            files: files
                .iter()
                .map(|f| FileInfo {
                    id: f.file,
                    name: f.name.to_string(),
                })
                .collect(),
            namespace: namespace.map(str::to_string),
            closure: closure.map(<[String]>::to_vec),
            first_def: self.globals.defs.len(),
            first_test,
            ..ModuleState::default()
        };
        self.scope.clear_imports();
        if !std::mem::take(&mut self.skip_navigation_walk) {
            self.walk_for_navigation(&files.iter().map(|f| f.module).collect::<Vec<_>>());
        }
        let (items, decl_spans) = self.collect(files, &mut diagnostics);
        // Claimed again by now, if this follows a failed replay.
        self.replayed_names.clear();
        let needs = self.dependencies(&items);
        // For the check cache: the names collected, before the library
        // files load (`cache`).
        self.capture_before_needs(&needs);
        // Library files this module uses load first, so what it names is
        // checked before it is (docs/proposals/std-library.md §4.3).
        if !needs.files.is_empty() || !needs.dots.is_empty() {
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
            self.module.first_def = self.globals.defs.len();
            first_test = self.tests.len();
            self.module.first_test = first_test;
        }
        self.capture_after_needs();
        // The core and the library are written in an order that works,
        // instances after what the rest of them uses: their uses of syntax
        // (`if`, `<=`) refer to declarations no name does.
        if !self.loading_prelude {
            self.instance_edges(&items);
        }
        let order = self.components();

        for component in order {
            // Each component is one operation, with its own resource limits.
            let saved = self.globals.budget.start(self.limits);
            self.module.current = component.clone();
            let before = diagnostics.len();
            let (defs_before, datas_before) = (self.globals.defs.len(), self.globals.datas.len());
            // Goals from before (an expression typed in) aren't this
            // component's.
            self.clear_goals();
            self.globals.failed_mentioned.set(false);
            let timed = crate::timings::enabled();
            if timed {
                crate::timings::decl_begin(&self.globals);
            }
            self.glued(|e| e.check_component(&items, &component, &mut diagnostics));
            self.globals.budget.restore(saved);
            if timed {
                let label = self.component_label(&items, &component);
                crate::timings::decl_end(&self.globals, label);
            }
            self.blame_failed_dependency(&component, before, diagnostics.as_mut_slice());
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
                    .any(|i| self.module.items[*i].status.failed());
            // Unfinished, not wrong: the only errors stand for open goals
            // (`goals::UNFINISHED`), which aren't reported as errors (D636).
            let unfinished = !errors.is_empty() && errors.iter().all(|c| *c == goals::UNFINISHED);
            for &i in &component {
                self.module.items[i].status = match (failed, unfinished) {
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
            let position = items[component[0]].position;
            diagnostics.extend(goals.into_iter().map(|d| (position, d)));
            if unfinished {
                self.mark_unfinished(&component, defs_before, datas_before);
            }
            // A component that failed leaves nothing behind for the next,
            // and anything it left declared is failed, so later uses fail
            // too.
            if failed {
                self.clear_metas();
                kernel::abandon_pending(&mut self.globals);
                // Running out of resources is reported where it happened
                // only as precisely as the declaration.
                for (position, d) in &mut diagnostics[before..] {
                    if d.labels.is_empty() {
                        let span = decl_spans[*position];
                        *d = d.clone().with_label(span, "while checking this");
                    }
                }
                // A theorem whose statement checked but whose proof didn't
                // (or is wholly `?`): is the statement false? Said as a note
                // on its first error, or on its goal (D1154, D1158).
                if component.len() == 1 {
                    self.note_counterexample(&items[component[0]], &mut diagnostics[before..]);
                }
            }
        }
        self.clear_metas();
        self.module.current.clear();
        self.module.item = None;
        self.module.phase = Phase::Body;
        if let (Some(ns), Some(_)) = (namespace, closure) {
            self.namespace_defs.insert(
                ns.to_string(),
                self.module.first_def..self.globals.defs.len(),
            );
        }
        // Names that were never checked now just name failures.
        self.fail_unchecked_names();
        // Tests run by file, then in source order, whatever order they were
        // checked in.
        let ranks: HashMap<FileId, usize> = self
            .module
            .files
            .iter()
            .enumerate()
            .filter_map(|(i, f)| f.id.map(|id| (id, i)))
            .collect();
        self.tests[first_test..]
            .sort_by_key(|t| (ranks.get(&t.span.file).copied().unwrap_or(0), t.span.start));
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
                .filter_map(|i| self.module.files.get(*i).map(|f| f.id))
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
        diagnostics
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
        let Some(def) = (self.module.first_def..self.globals.defs.len())
            .rev()
            .map(DefId)
            .find(|id| {
                let def = self.globals.def(*id);
                def.theorem && def.span == *span
            })
        else {
            return;
        };
        if !diagnostics.iter().any(|(_, d)| d.severity == wanted) {
            return;
        }
        let Some(note) = self.counterexample_note(def) else {
            return;
        };
        if let Some((_, d)) = diagnostics.iter_mut().find(|(_, d)| d.severity == wanted) {
            d.notes.push(note);
        }
    }

    /// Notes the declarations of `component`, unfinished, as such for the
    /// kernel's refusals of what uses them (`goals::unfinished_dependency`):
    /// those its items declared, and the ones made while checking it (from
    /// definition `defs` and data type `datas` on) that aren't final: failed,
    /// or pending until the component is abandoned.
    fn mark_unfinished(&self, component: &[usize], defs: usize, datas: usize) {
        let g = &self.globals;
        let mut unfinished = g.unfinished.borrow_mut();
        for (id, item) in &self.module.def_items {
            if component.contains(item) && g.def(*id).state() != State::Final {
                unfinished.insert(HashKey::Def(*id));
            }
        }
        for id in defs..g.defs.len() {
            if g.defs[id].state() != State::Final {
                unfinished.insert(HashKey::Def(DefId(id)));
            }
        }
        for d in datas..g.datas.len() {
            if g.datas[d].state() != State::Final {
                unfinished.insert(HashKey::Data(DataId(d)));
            }
        }
    }

    /// When a message of this component showed a term that uses a failed
    /// definition (`Globals::failed_mentioned`, decided from the terms, not
    /// the text: messages elide), its errors are fallout of that failure (a
    /// failed definition is stuck, so a proof about it won't check): they
    /// become one saying the failed declaration has errors, which goes
    /// without saying when that failure is reported too. Unknown names stay,
    /// and so does everything when no message showed a failed definition.
    fn blame_failed_dependency(
        &self,
        component: &[usize],
        before: usize,
        diagnostics: &mut [(usize, Diagnostic)],
    ) {
        let failed: Vec<(&Dep, &str)> = component
            .iter()
            .flat_map(|i| &self.module.items[*i].deps)
            .filter(|d| {
                d.speculative.is_none()
                    && !component.contains(&d.item)
                    && self.module.items[d.item].status.failed()
            })
            .map(|d| (d, self.module.items[d.item].name.as_str()))
            .collect();
        if failed.is_empty() || !self.globals.failed_mentioned.get() {
            return;
        }
        // Blamed on a declaration with errors if there is one; if they're
        // all unfinished, so is this (D636).
        let errored = failed
            .iter()
            .position(|(d, _)| self.module.items[d.item].status == Status::Failed);
        for (_, d) in &mut diagnostics[before..] {
            if d.severity != Severity::Error
                || d.code == "E-UNKNOWN-NAME"
                || d.code == "E-FAILED-DEPENDENCY"
            {
                continue;
            }
            let Some(errored) = errored else {
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
                if self.loading_prelude && !self.library_tests && matches!(decl, Decl::Test { .. })
                {
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
                self.module.items.push(ItemInfo {
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
                self.module.file = Some(self.module.items[index].file);
                if main.as_ref().is_some_and(|m| m.text.contains('.')) == qualified
                    && let Err(d) = self.register(index, item.decl)
                {
                    let (d, fatal) = d;
                    diagnostics.push((item.position, d));
                    if fatal {
                        left_out.insert(index);
                    } else {
                        self.module.items[index].status = Status::Failed;
                    }
                }
            }
        }
        self.add_file_imports(files, &file_starts, true, &mut import_errors);
        // Whether a signature's result is the library's `Decidable`, by what
        // its head means here, not how it's spelt.
        let decidable = self.globals.registry.data(Builtin::Decidable);
        for (index, item) in items.iter().enumerate() {
            self.module.file = Some(self.module.items[index].file);
            if let Decl::Signature {
                ty, instance: true, ..
            } = item.decl
                && let Some(head) = result_head(ty)
            {
                self.module.items[index].decides = decidable.is_some()
                    && matches!(self.named(&head.text), Some((Global::Data(d), _)) if Some(*d) == decidable);
            }
        }
        for (index, item) in items.iter().enumerate() {
            if let Decl::Signature { ty, .. } = item.decl {
                self.module.items[index].function = is_function_type(ty);
            }
        }
        for (index, item) in items.iter().enumerate() {
            if let Decl::Signature {
                ty, instance: true, ..
            } = item.decl
                && let Some(head) = result_head(ty)
            {
                self.module.file = Some(self.module.items[index].file);
                self.module.items[index].interface = self.named(&head.text).map(|(g, _)| *g);
                self.module.items[index].head = instance_head(ty)
                    .and_then(|n| self.named(&n.text))
                    .map(|(g, _)| *g);
            }
        }
        self.module.file = None;
        self.declare_parse_failed(files);
        diagnostics.extend(import_errors);
        // A declaration whose own name is taken is left out.
        if !left_out.is_empty() {
            let mut kept = Vec::new();
            let mut infos = Vec::new();
            let old = std::mem::take(&mut self.module.items);
            let mut renumber = HashMap::default();
            for (index, (item, info)) in items.into_iter().zip(old).enumerate() {
                if !left_out.contains(&index) {
                    renumber.insert(index, kept.len());
                    kept.push(item);
                    infos.push(info);
                }
            }
            self.module.items = infos;
            for key in &self.module.names {
                if let Some((Global::Unchecked(i), _)) = self.scope.entries.get_mut(key)
                    && let Some(&new) = renumber.get(i)
                {
                    *i = new;
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
            for name in &unit.module.failed {
                let Ok(key) = self.declaration_key(name) else {
                    continue;
                };
                if self.scope.entries.contains_key(&key) {
                    continue;
                }
                self.scope.insert(&key, Global::Failed, name.span, false);
                self.module.names.insert(key);
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
            self.module.file = Some(file);
            let mut found = Vec::new();
            self.add_imports(&unit.module.imports, own, &mut found);
            errors.extend(found.into_iter().map(|d| (file_starts[file], d)));
        }
        self.module.file = None;
    }

    /// The file whose imports name lookup uses: the one the item being
    /// elaborated is in, or the one being registered; file 0 when nothing is
    /// (so `eval`, the REPL and `main` see a single file's imports).
    pub(crate) fn current_file(&self) -> usize {
        self.module
            .file
            .or_else(|| self.module.item.map(|i| self.module.items[i].file))
            .unwrap_or(0)
    }

    /// Enters the names declaration `index` declares as unchecked. The error
    /// is fatal (the declaration is left out) when its own name can't be
    /// registered.
    fn register(&mut self, index: usize, decl: &Decl) -> Result<(), (Diagnostic, bool)> {
        let (main, members) = declared_names(decl);
        let Some(main) = main else {
            return Ok(());
        };
        let key = self.declaration_key(&main).map_err(|d| (d, true))?;
        self.new_module_name(&key, &main).map_err(|d| (d, true))?;
        self.scope
            .insert(&key, Global::Unchecked(index), main.span, false);
        self.module.names.insert(key.clone());
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
                    self.module.names.insert(member_key);
                }
                Err(d) => {
                    if result.is_ok() {
                        result = Err((d, false));
                    }
                }
            }
        }
        result
    }

    /// A name a module declaration claims: not built in, and not already
    /// taken (by an earlier module or earlier in this one).
    fn new_module_name(&self, key: &str, n: &ast::Name) -> crate::Result<()> {
        if RESERVED.contains(&n.text.as_str()) {
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
        if matches!(global, Global::Failed) && self.replayed_names.contains(key) {
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
        for (index, item) in items.iter().enumerate() {
            self.module.file = Some(self.module.items[index].file);
            let mut deps = Vec::new();
            let names = &self.module.names;
            let mut add = |r: Ref<'_>, in_header: bool| {
                let (n, mut fields) = match r {
                    Ref::Name(n) => (n, Vec::new()),
                    Ref::Dot(n, field) => (n, vec![field]),
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
                    }
                    fields = rest;
                }
                // Dot notation: its target isn't known until the receiver's
                // type is, so every declaration of this module that it
                // could mean (§5).
                for field in fields {
                    let suffix = format!(".{field}");
                    for key in names.iter().filter(|k| k.ends_with(&suffix)) {
                        if let Some((Global::Unchecked(j), _)) = self.scope.get(key) {
                            deps.push(Dep {
                                item: j,
                                span: n.span,
                                in_header,
                                speculative: Some(format!(
                                    "`.{field}` might mean `{}`",
                                    crate::scope::display(key)
                                )),
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
            self.module.items[index].deps = deps;
        }
        self.module.file = None;
        if let Some(f) = own {
            needs.files.remove(&f);
        }
        needs
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
            .globals
            .registry
            .data(Builtin::Decidable)
            .map(Global::Data);
        let instances: Vec<usize> = (0..self.module.items.len())
            .filter(|i| {
                let item = &self.module.items[*i];
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
            let span = this.module.items[to].span;
            this.module.items[from].deps.push(Dep {
                item: to,
                span,
                in_header: false,
                speculative: Some("it may use instances".to_string()),
            });
        };
        // Between instances: by the interfaces their declarations mention,
        // and their interfaces' superclasses.
        for &y in &instances {
            let Some(wanted) = self.module.items[y].interface else {
                continue;
            };
            let reached = self.reachable(y);
            for &x in &instances {
                if x == y || self.module.items[x].interface == Some(wanted) {
                    continue;
                }
                let mentions = self.mentions_global(x, &items[x], wanted)
                    || self.is_super_of(self.module.items[x].interface, wanted, items);
                if mentions {
                    add(self, &reached, x, y);
                }
            }
        }
        // Everything else that may use one.
        for &y in &instances {
            let reached = self.reachable(y);
            for x in 0..self.module.items.len() {
                let kind = self.module.items[x].kind;
                if self.module.items[x].instance || !matches!(kind, Kind::Def | Kind::Test) {
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
            pending.extend(self.module.items[i].deps.iter().map(|d| d.item));
        }
        seen
    }

    /// Whether `item`'s declaration names `wanted` (or something in its
    /// namespace).
    fn mentions_global(&mut self, index: usize, item: &Item, wanted: Global) -> bool {
        self.module.file = Some(self.module.items[index].file);
        // A checked interface's methods are definitions in its namespace.
        let members = match wanted {
            Global::Data(d) => Some(format!("{}.", self.data_key(d))),
            _ => None,
        };
        let mut found = false;
        for (r, _) in decl_refs(item.decl, item.equations) {
            let n = match r {
                Ref::Name(n) | Ref::Dot(n, _) => n,
            };
            if let crate::scope::Resolved::Found { global, key, .. } = self.resolve(&n.text)
                && (global == wanted || members.as_ref().is_some_and(|m| key.starts_with(m)))
            {
                found = true;
                break;
            }
        }
        self.module.file = None;
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
                Global::Data(d) => match self.interfaces.get(&d) {
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
    /// the module's own.
    fn fail_unchecked_names(&mut self) {
        for key in &self.module.names {
            if let Some((global, _)) = self.scope.entries.get_mut(key)
                && let Global::Unchecked(_) = global
            {
                *global = Global::Failed;
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
        let mut file_start = vec![usize::MAX; self.module.files.len()];
        for item in &self.module.items {
            file_start[item.file] = file_start[item.file].min(item.position);
        }
        let components = tarjan(&edges);
        for (c, members) in components.iter().enumerate() {
            for &i in members {
                self.module.items[i].component = c;
            }
        }
        // Kahn's algorithm over the components.
        let mut waiting_on = vec![0usize; components.len()];
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); components.len()];
        for (i, targets) in edges.iter().enumerate() {
            let c = self.module.items[i].component;
            for &j in targets {
                let d = self.module.items[j].component;
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
                    let item = &self.module.items[*i];
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
            members.sort_by_key(|i| self.module.items[*i].position);
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
            .any(|i| self.module.items[*i].status.failed())
        {
            // Already reported (a constructor or operation name taken).
            return;
        }
        let recursive = component.len() > 1
            || self.module.items[component[0]]
                .deps
                .iter()
                .any(|d| d.item == component[0]);
        let kinds: Vec<Kind> = component
            .iter()
            .map(|i| self.module.items[*i].kind)
            .collect();
        if recursive && component.iter().all(|i| self.module.items[*i].synonym) {
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
                for dep in self.module.items[i].deps.clone() {
                    if dep.in_header
                        && dep.speculative.is_none()
                        && self.module.in_current(dep.item)
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
                for dep in self.module.items[i].deps.clone() {
                    // Once for each sibling, at its first use.
                    if dep.in_header
                        && dep.speculative.is_none()
                        && self.module.in_current(dep.item)
                        && !reported.contains(&dep.item)
                    {
                        reported.push(dep.item);
                        diagnostics.push((
                            items[i].position,
                            self.mutual_signature(i, dep.item, dep.span),
                        ));
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
        self.module.item = Some(index);
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
        diagnostics.extend(self.warnings.drain(..).map(|w| (item.position, w)));
        diagnostics.extend(
            self.lambda_warnings
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
        let prefix = if self.namespace_root.is_empty() {
            format!("{}.", self.globals.module)
        } else {
            self.namespace_root.clone()
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
            for dep in &self.module.items[i].deps {
                let j = dep.item;
                if !self.module.in_current(j) || parent.contains_key(&j) || j == from {
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
        let quoted = |i: &usize| format!("`{}`", self.module.items[*i].name);
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
        let items = &self.module.items;
        let first = component[0];
        let back = items[first]
            .deps
            .iter()
            .map(|d| d.item)
            .find(|&j| j != first && self.module.in_current(j));
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
        let items = &self.module.items;
        let first = component[0];
        let back = items[first]
            .deps
            .iter()
            .find(|d| d.item != first && self.module.in_current(d.item))
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
    fn speculative_note(&self, component: &[usize]) -> Option<String> {
        let items = &self.module.items;
        component.iter().find_map(|&i| {
            items[i].deps.iter().find_map(|d| {
                let why = d.speculative.as_ref()?;
                component.contains(&d.item).then(|| {
                    format!(
                        "in `{}`, {why}, so `{}` and `{}` are checked together; write the full \
                         name, as in `T.f x`, to say which function is meant",
                        items[i].name, items[i].name, items[d.item].name
                    )
                })
            })
        })
    }

    /// The error for a data type's header (of `item`) that mentions
    /// `other`, in the same group, at `span`.
    fn mutual_header(&self, item: usize, other: usize, span: Span) -> Diagnostic {
        let items = &self.module.items;
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
        let items = &self.module.items;
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

    /// The error for using `name`, which declaration `item` of this module
    /// declares, before it's checked.
    pub(crate) fn unchecked(&self, name: &ast::Name, item: usize) -> Diagnostic {
        let info = &self.module.items[item];
        if info.status == Status::Failed {
            return failed_name(name);
        }
        if info.status == Status::Unfinished {
            return goals::uses_unfinished(Some(name.span));
        }
        if self.module.in_current(item) {
            let current = self.module.item.unwrap_or(item);
            let owner = &self.module.items[current].name;
            return match self.module.phase {
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
                Phase::Body => internal_order(name),
            };
        }
        internal_order(name)
    }

    /// Notes for `E-AUTO-NONE`: decision procedures in this module that
    /// `auto` couldn't use where it's being elaborated, and why.
    pub(crate) fn auto_hints(&self) -> Vec<String> {
        let Some(current) = self.module.item else {
            return Vec::new();
        };
        let items = &self.module.items;
        let here = &items[current];
        let mut hints = Vec::new();
        for (j, item) in items.iter().enumerate() {
            if !item.decides {
                continue;
            }
            let name = &item.name;
            if self.module.in_current(j) {
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
                    self.module.files[item.file].name
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
        let items = &self.module.items;
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
            if i != item && (waiting.is_empty() || self.module.in_current(i)) {
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
            .module
            .item
            .map(|c| items[c].name.clone())
            .unwrap_or_default();
        if self.module.in_current(end) {
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
        if self.globals.def(id).body().is_none() {
            return false; // not finished checking (e.g. one being defined)
        }
        match (self.module.def_items.get(&id), self.module.item) {
            (Some(item), Some(current)) => {
                let (item, current) = (&self.module.items[*item], &self.module.items[current]);
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
        Decl::Signature { name, .. } => (Some(name.clone()), Vec::new()),
        Decl::Test { .. } | Decl::Equation { .. } => (None, Vec::new()),
    }
}

/// The name at the head of a signature's result, after its parameters.
/// Whether a written type is a function type (after any implicit parameters).
pub(crate) fn is_function_type(ty: &Expr) -> bool {
    let mut ty = ty;
    loop {
        match ty {
            Expr::Arrow(..) => return true,
            Expr::Pi {
                implicit: false, ..
            } => return true,
            Expr::Pi { cod, .. } => ty = cod,
            _ => return false,
        }
    }
}

impl Elaborator {
    /// Whether the module's item `item`, not checked yet, is declared with a
    /// function type.
    pub(crate) fn item_is_function(&self, item: usize) -> bool {
        self.module.items[item].function
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

/// One step of the walk in [`free_names`].
#[derive(Clone)]
enum Work<'a> {
    Expr(&'a Expr),
    /// A pattern: its constructors are references, its variables binders
    /// (for the rest of the walk).
    Pattern(&'a Pattern),
    Bind(&'a str),
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
        Decl::Signature { ty, .. } => {
            add(free_names(vec![Work::Expr(ty)]), true);
            let binders = body_binders(ty, equations);
            for eq in equations {
                let Decl::Equation { patterns, rhs, .. } = eq else {
                    continue;
                };
                let mut work: Vec<Work> = binders.iter().map(|x| Work::Bind(x)).collect();
                work.extend(patterns.iter().map(Work::Pattern));
                work.extend(rhs.iter().map(Work::Expr));
                add(free_names(work), false);
            }
        }
        Decl::Data {
            params,
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

/// The library's `Float`, which a decimal literal refers to.
pub(crate) static FLOAT_TYPE: std::sync::LazyLock<ast::Name> =
    std::sync::LazyLock::new(|| ast::Name {
        text: "Std.Float".to_string(),
        span: stitchwort_syntax::Span::NOWHERE,
    });

/// A reference the pre-pass finds: a name, or dot notation's `.field`
/// (with where it's written).
pub(crate) enum Ref<'a> {
    Name(&'a ast::Name),
    Dot(&'a ast::Name, String),
}

/// A reference no declaration can have: a `rewrite` is here. A program's
/// module loads `omega`'s library for it ([`Elaborator::dependencies`]);
/// a library file doesn't, since `omega`'s library is built on files that
/// use `rewrite` (an edge back would be a cycle), so there a premise is
/// proved by `omega` only where the file loads it anyway.
pub(crate) static REWRITE_MARKER: std::sync::LazyLock<ast::Name> =
    std::sync::LazyLock::new(|| ast::Name {
        text: "%rewrite".to_string(),
        span: Span::NOWHERE,
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
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => {}
    }
}

/// The free names in `work`, in order: names used that aren't bound by a
/// binder around them. A work list rather than recursion, since expressions
/// can nest more deeply than recursion could follow.
fn free_names(work: Vec<Work<'_>>) -> Vec<Ref<'_>> {
    let mut stack: Vec<Work> = work;
    stack.reverse();
    let mut bound: HashMap<&str, usize> = HashMap::default();
    let mut out = Vec::new();
    // Pushes steps to run in the order given.
    fn then<'a>(stack: &mut Vec<Work<'a>>, steps: Vec<Work<'a>>) {
        stack.extend(steps.into_iter().rev());
    }
    while let Some(step) = stack.pop() {
        let expr = match step {
            Work::Bind(x) => {
                *bound.entry(x).or_default() += 1;
                continue;
            }
            Work::Unbind(x) => {
                if let Some(count) = bound.get_mut(x) {
                    *count = count.saturating_sub(1);
                }
                continue;
            }
            Work::Name(n) => {
                let is_bound = |x: &str| bound.get(x).copied().unwrap_or(0) > 0;
                if is_bound(&n.text) {
                    continue;
                }
                match n.text.split_once('.') {
                    // `p.name`, with `p` local: dot notation.
                    Some((first, rest)) if is_bound(first) => {
                        out.extend(rest.split('.').map(|f| Ref::Dot(n, f.to_string())));
                    }
                    _ => out.push(Ref::Name(n)),
                }
                continue;
            }
            Work::Pattern(p) => {
                match p {
                    Pattern::Var(x) => *bound.entry(&x.text).or_default() += 1,
                    Pattern::Ctor(n, args, _) => {
                        out.push(Ref::Name(n));
                        then(&mut stack, args.iter().map(Work::Pattern).collect());
                    }
                    Pattern::Tuple(a, b, _) => {
                        then(&mut stack, vec![Work::Pattern(a), Work::Pattern(b)]);
                    }
                    Pattern::Cons(a, b, _) => {
                        then(&mut stack, vec![Work::Pattern(a), Work::Pattern(b)]);
                    }
                    Pattern::Named(_, p, _) => then(&mut stack, vec![Work::Pattern(p)]),
                    Pattern::CtorFields { ctor, fields, .. } => {
                        out.push(Ref::Name(ctor));
                        then(
                            &mut stack,
                            fields.iter().map(|(_, p)| Work::Pattern(p)).collect(),
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
                out.push(Ref::Dot(&MEMBERSHIP[0], "contains".to_string()));
                then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]);
            }
            Expr::App(a, b)
            | Expr::Arrow(a, b)
            | Expr::Binary(_, a, b)
            | Expr::Pipe(a, b)
            | Expr::Seq(a, b) => {
                then(&mut stack, vec![Work::Expr(a), Work::Expr(b)]);
            }
            Expr::Neg(a, _) => stack.push(Work::Expr(a)),
            Expr::Lam(names, body, _) => {
                let (bind, unbind) = binds(names);
                let mut steps = bind;
                steps.push(Work::Expr(body));
                steps.extend(unbind);
                then(&mut stack, steps);
            }
            Expr::TypedLam(name, _, ty, body, _) => {
                let (bind, unbind) = binds(std::slice::from_ref(name));
                let mut steps = vec![Work::Expr(ty)];
                steps.extend(bind);
                steps.push(Work::Expr(body));
                steps.extend(unbind);
                then(&mut stack, steps);
            }
            Expr::Pi {
                names, dom, cod, ..
            } => {
                let (bind, unbind) = binds(names);
                let mut steps = vec![Work::Expr(dom)];
                steps.extend(bind);
                steps.push(Work::Expr(cod));
                steps.extend(unbind);
                then(&mut stack, steps);
            }
            Expr::NamedArg(_, value, _, _) => stack.push(Work::Expr(value)),
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
                out.push(Ref::Dot(field, field.text.clone()));
                stack.push(Work::Expr(e));
            }
            // What the proof `omega` writes refers to (crates/elab/src/omega.rs).
            Expr::Omega { facts, .. } => {
                out.extend(crate::omega::LIBRARY_NAMES.iter().map(Ref::Name));
                then(&mut stack, facts.iter().map(Work::Expr).collect());
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
                    Work::Bind(&name.text),
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
                    steps.push(Work::Expr(&alt.body));
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
                            if arg_var.is_none() {
                                steps.push(Work::Pattern(arg));
                            }
                            steps.extend(arg_var.map(Work::Bind));
                            steps.extend([
                                Work::Bind(&k.text),
                                Work::Expr(body),
                                Work::Unbind(&k.text),
                            ]);
                            steps.extend(arg_var.map(Work::Unbind));
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
    let Decl::Signature { ty, .. } = &def.signature else {
        return Vec::new();
    };
    let mut work = vec![Work::Expr(ty)];
    let binders = body_binders(ty, &def.equations);
    for eq in &def.equations {
        let Decl::Equation { patterns, rhs, .. } = eq else {
            continue;
        };
        let mut vars = Vec::new();
        for p in patterns {
            pattern_binders(p, &mut vars);
        }
        work.extend(binders.iter().map(|x| Work::Bind(x)));
        work.extend(patterns.iter().map(Work::Pattern));
        work.extend(rhs.iter().map(Work::Expr));
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
