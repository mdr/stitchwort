//! Runs source files through the compiler pipeline.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;

use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{Globals, Limits, ResourceError, Term, Value};
use stitchwort_elab::project::{FileModeContext, SourceUnit};
use stitchwort_elab::{Elaborator, PRELUDE};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::{
    Diagnostic, FileId, Severity, SourceMap, parse_expression_within, parse_module_within,
};

/// A compiler session: the prelude plus whatever has been loaded since.
pub struct Session {
    pub sources: SourceMap,
    pub elab: Elaborator,
    /// Warnings from files loaded without errors. (A file with errors
    /// returns its warnings with them.)
    pub warnings: Vec<Diagnostic>,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

/// Runs `f` on a new thread with `stack` bytes of stack, for a session whose
/// limits are [`Limits::for_stack`] of the same size.
pub fn with_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(stack)
            .spawn_scoped(scope, f)
            .expect("can't start a thread")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

impl Session {
    /// A session for a thread with `stack` bytes of stack.
    pub fn for_stack(stack: usize) -> Self {
        let mut session = Session::new();
        session.elab.limits = Limits::for_stack(stack);
        session
    }

    pub fn new() -> Self {
        Session::with_prelude(PRELUDE)
    }

    /// A session whose prelude is the given text: for tests that change a
    /// prelude definition.
    #[doc(hidden)]
    pub fn with_prelude(prelude: &str) -> Self {
        Self::try_with_prelude(prelude).unwrap_or_else(|report| panic!("{report}"))
    }

    /// Like [`Session::with_prelude`], but a prelude that doesn't check gives
    /// its diagnostics rendered with file, line and labels (what an author of
    /// the prelude needs), not a panic.
    #[doc(hidden)]
    pub fn try_with_prelude(prelude: &str) -> Result<Self, String> {
        let mut session = Session {
            sources: SourceMap::new(),
            elab: Elaborator::new(),
            warnings: Vec::new(),
        };
        session.elab.loading_prelude = true;
        if let Err(diagnostics) = session.load("<prelude>", prelude) {
            let mut report = String::from("internal error: the prelude doesn't check:\n");
            for d in &diagnostics {
                report.push_str(&crate::render::render(&session.sources, d, false));
            }
            return Err(report);
        }
        if let Err(missing) = session.elab.finish_prelude() {
            return Err(format!("internal error: {}", missing.message));
        }
        Ok(session)
    }

    /// Parses, elaborates and checks a file, and checks that its exports can
    /// cross the JS boundary.
    pub fn load(&mut self, name: &str, text: &str) -> Result<FileId, Vec<Diagnostic>> {
        self.load_file(name, text, None)
    }

    /// [`Session::load`] for a file named on its own that lives inside a
    /// project: with `context`, a use of one of the project's namespaces is
    /// `E-FILE-MODE`, which says what to do instead.
    pub fn load_file(
        &mut self,
        name: &str,
        text: &str,
        context: Option<FileModeContext>,
    ) -> Result<FileId, Vec<Diagnostic>> {
        let file = self.sources.add(name, text);
        let module = parse_module_within(file, text, self.elab.limits.stack)?;
        let first_new_def = self.elab.globals.defs.len();
        self.elab.file_mode = context;
        let diagnostics = self.elab.elaborate_module(&module);
        self.elab.file_mode = None;
        self.finish_load(first_new_def, diagnostics)?;
        Ok(file)
    }

    /// Loads several files of one namespace as one module: for tests, until
    /// projects load (`docs/proposals/multi-file.md` §4.4). Each file is
    /// `(name, text)`, and all must start with the same namespace line.
    #[doc(hidden)]
    pub fn load_namespace(&mut self, files: &[(&str, &str)]) -> Result<(), Vec<Diagnostic>> {
        let mut sorted: Vec<(&str, &str)> = files.to_vec();
        sorted.sort_by_key(|(name, _)| *name);
        let ids: Vec<FileId> = sorted
            .iter()
            .map(|&(name, text)| self.sources.add(name, text))
            .collect();
        let mut modules = Vec::new();
        let mut errors = Vec::new();
        for (id, (_, text)) in ids.iter().zip(&sorted) {
            match parse_module_within(*id, text, self.elab.limits.stack) {
                Ok(module) => modules.push(module),
                Err(parse_errors) => errors.extend(parse_errors),
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }
        let internal = |message: &str| vec![Diagnostic::error("E-INTERNAL", message)];
        let Some(first) = modules.first().and_then(|m| m.namespace.as_ref()) else {
            return Err(internal("every file of a namespace needs a namespace line"));
        };
        let namespace = first.path.text.clone();
        if modules
            .iter()
            .any(|m| m.namespace.as_ref().map(|n| &n.path.text) != Some(&namespace))
        {
            return Err(internal("the files must all be in the same namespace"));
        }
        if let Err(d) = self.elab.check_namespace_name(first) {
            return Err(vec![d]);
        }
        let units: Vec<SourceUnit> = sorted
            .iter()
            .zip(&ids)
            .zip(&modules)
            .map(|(((name, _), id), module)| SourceUnit {
                file: Some(*id),
                name,
                module,
            })
            .collect();
        let first_new_def = self.elab.globals.defs.len();
        let diagnostics = self
            .elab
            .elaborate_namespace(Some(&namespace), &units, None);
        self.finish_load(first_new_def, diagnostics)
    }

    /// What `load` does once the elaborator is done: checks that the new
    /// definitions' exports can cross the JS boundary, keeps the warnings,
    /// and returns the errors if there are any.
    fn finish_load(
        &mut self,
        first_new_def: usize,
        mut diagnostics: Vec<Diagnostic>,
    ) -> Result<(), Vec<Diagnostic>> {
        self.check_exports(first_new_def, false, &mut diagnostics);
        if diagnostics.iter().any(|d| d.severity == Severity::Error) {
            Err(diagnostics)
        } else {
            self.warnings.extend(diagnostics);
            Ok(())
        }
    }

    /// If `diagnostics` has no errors, checks that the exports of the
    /// definitions from `first_new_def` on can cross the JS boundary, and
    /// can be named together: with every export of the session (a file), or
    /// with only these (`among`: one namespace of a project).
    pub(crate) fn check_exports(
        &self,
        first_new_def: usize,
        among: bool,
        diagnostics: &mut Vec<Diagnostic>,
    ) {
        let errors = |ds: &[Diagnostic]| ds.iter().any(|d| d.severity == Severity::Error);
        if errors(diagnostics) {
            return;
        }
        let g = &self.elab.globals;
        let _op = g
            .budget
            .operation(Limits::stack_only(self.elab.limits.stack));
        for id in first_new_def..g.defs.len() {
            let id = stitchwort_core::DefId(id);
            if g.def(id).export
                && let Err(d) = stitchwort_js::exportable(g, id)
            {
                diagnostics.push(d);
            }
        }
        if errors(diagnostics) {
            return;
        }
        let fit = if among {
            stitchwort_js::exports_fit_together_among(
                g,
                (first_new_def..g.defs.len()).map(stitchwort_core::DefId),
            )
        } else {
            stitchwort_js::exports_fit_together(g)
        };
        if let Err(d) = fit {
            diagnostics.push(d);
        }
    }

    /// Parses an expression typed in (for `eval` or the REPL), within this
    /// session's stack limit.
    pub fn parse_expression(&mut self, name: &str, text: &str) -> Result<Expr, Diagnostic> {
        let file = self.sources.add(name, text);
        parse_expression_within(file, text, self.elab.limits.stack)
    }

    /// Parses an expression the driver wrote itself.
    pub(crate) fn parse_internal(&mut self, name: &str, text: &str) -> Result<Expr, Diagnostic> {
        self.parse_expression(name, text)
    }

    /// Generates JavaScript for the exports loaded so far.
    pub fn extract(&self) -> Result<stitchwort_js::Output, Diagnostic> {
        stitchwort_js::generate(&self.elab.globals, self.elab.limits)
    }

    /// Generates JavaScript for the exports of namespace `namespace` of the
    /// project loaded, and no others'.
    pub fn extract_namespace(&self, namespace: &str) -> Result<stitchwort_js::Output, Diagnostic> {
        let g = &self.elab.globals;
        let ids: Vec<stitchwort_core::DefId> = self
            .elab
            .namespace_def_range(namespace)
            .map(stitchwort_core::DefId)
            .filter(|id| g.def(*id).export)
            .collect();
        stitchwort_js::generate_exports(
            g,
            self.elab.limits,
            stitchwort_js::Options::default(),
            &ids,
        )
    }

    /// Generates the JavaScript program that runs `main` under Node
    /// (`stitchwort run --js`).
    pub fn extract_program(
        &self,
        main: &crate::run::Main,
    ) -> Result<stitchwort_js::run::Program, Diagnostic> {
        stitchwort_js::run::generate_program(&self.elab.globals, self.elab.limits, main.term())
    }
}

/// Whether a test's expression evaluated to `True`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Passed,
    Failed,
    /// It ran out of resources before finishing: neither passed nor failed.
    /// Never cached.
    OutOfResources(ResourceError),
}

pub struct TestResult {
    pub name: String,
    /// The namespace its module is in; empty if it has none.
    pub namespace: String,
    pub outcome: Outcome,
    /// Whether the outcome came from the cache, rather than running the test.
    pub cached: bool,
    /// `None` if hashing the test ran out of resources.
    pub hash: Option<ContentHash>,
}

/// Test results, stored by the test's content hash (DESIGN.md §11). A test's
/// hash covers everything it depends on, so a cached result stays valid until
/// something the test uses changes. The local cache is trusted. Results live
/// in a directory, or in memory for hosts without a file system.
///
/// The key also has the compiler that ran it: its version, a fingerprint of
/// its source ([`FINGERPRINT`]), and the modes that change how programs are
/// evaluated ([`modes`]). So a result is never reused by a different build,
/// or by a run with natives or compact text switched off.
pub struct Cache {
    dir: Option<PathBuf>,
    memory: Option<RefCell<Memory>>,
}

/// A cache's results when it has no directory to keep them in: the ones it
/// started with, and the ones added since (which the host can save).
struct Memory {
    known: HashMap<String, Outcome>,
    added: Vec<(String, Outcome)>,
}

/// Part of every cache key, so results from another version of the compiler
/// aren't reused.
const COMPILER: &str = concat!("stitchwort-", env!("CARGO_PKG_VERSION"));

/// A hash of the source of the syntax, the core, the elaborator (with the
/// prelude) and this crate, made by `build.rs`: part of every cache key, so
/// results from another build of the compiler aren't reused, even with the
/// same version number.
pub const FINGERPRINT: &str = env!("STITCHWORT_FINGERPRINT");

/// The effective modes of evaluation, for the cache key: whether the native
/// implementations are used (`n1`) or not (`n0`), and whether text literals
/// are compact (`c1`) or constructors (`c0`).
pub fn modes(g: &Globals) -> String {
    format!(
        "n{}c{}",
        u8::from(!g.builtins.disable_natives),
        u8::from(g.builtins.compact_literals().is_some())
    )
}

impl Cache {
    pub fn at(dir: impl Into<PathBuf>) -> Self {
        Cache {
            dir: Some(dir.into()),
            memory: None,
        }
    }

    /// A cache kept in memory, for hosts without a file system: it starts
    /// with `known`, and [`Cache::added`] gives the results added since.
    pub fn memory(known: impl IntoIterator<Item = (String, Outcome)>) -> Self {
        Cache {
            dir: None,
            memory: Some(RefCell::new(Memory {
                known: known.into_iter().collect(),
                added: Vec::new(),
            })),
        }
    }

    pub fn disabled() -> Self {
        Cache {
            dir: None,
            memory: None,
        }
    }

    /// The key of the result of the test with `hash`, when run with `modes`:
    /// the file name in a directory cache.
    pub fn key(hash: &ContentHash, modes: &str) -> String {
        format!("{COMPILER}-{FINGERPRINT}-{modes}-{}", hash.hex())
    }

    /// Where the result of the test with `hash` is kept, when run with
    /// `modes`.
    pub fn path(&self, hash: &ContentHash, modes: &str) -> Option<PathBuf> {
        Some(
            self.dir
                .as_ref()?
                .join("tests")
                .join(Self::key(hash, modes)),
        )
    }

    /// The results added by [`Cache::put`] during this run: only `Passed` and
    /// `Failed`, like the ones on disk. Empty for a cache without memory.
    pub fn added(&self) -> Vec<(String, Outcome)> {
        self.memory
            .as_ref()
            .map_or_else(Vec::new, |memory| memory.borrow().added.clone())
    }

    fn get(&self, hash: &ContentHash, modes: &str) -> Option<Outcome> {
        if let Some(memory) = &self.memory {
            return memory.borrow().known.get(&Self::key(hash, modes)).copied();
        }
        match std::fs::read_to_string(self.path(hash, modes)?)
            .ok()?
            .trim()
        {
            "passed" => Some(Outcome::Passed),
            "failed" => Some(Outcome::Failed),
            _ => None,
        }
    }

    /// Best effort: a cache that can't be written just means re-running later.
    fn put(&self, hash: &ContentHash, modes: &str, outcome: Outcome) {
        // Not a result: running it again with other limits may finish.
        if matches!(outcome, Outcome::OutOfResources(_)) {
            return;
        }
        let key = Self::key(hash, modes);
        if let Some(memory) = &self.memory {
            let mut memory = memory.borrow_mut();
            memory.known.insert(key.clone(), outcome);
            memory.added.push((key, outcome));
            return;
        }
        let Some(path) = self.path(hash, modes) else {
            return;
        };
        let text = match outcome {
            Outcome::Passed => "passed",
            Outcome::Failed => "failed",
            Outcome::OutOfResources(_) => unreachable!(),
        };
        if let Some(parent) = path.parent() {
            let _ = std::fs::create_dir_all(parent);
        }
        let _ = std::fs::write(path, text);
    }
}

impl Session {
    /// Runs every test loaded so far, using cached results where possible.
    pub fn run_tests(&self, cache: &Cache) -> Vec<TestResult> {
        let g = &self.elab.globals;
        let modes = modes(g);
        self.elab
            .tests
            .iter()
            .map(|test| {
                // Each test is one operation, with its own resource limits:
                // hashing it, then running it unless its result is cached.
                let _op = g.budget.operation(self.elab.limits);
                let hash = match def_hash(g, test.def) {
                    Ok(hash) => hash.expect("tests are checked before they run"),
                    Err(e) => {
                        return TestResult {
                            name: test.name.clone(),
                            namespace: test.namespace.clone(),
                            outcome: Outcome::OutOfResources(e),
                            cached: false,
                            hash: None,
                        };
                    }
                };
                if let Some(outcome) = cache.get(&hash, &modes) {
                    return TestResult {
                        name: test.name.clone(),
                        namespace: test.namespace.clone(),
                        outcome,
                        cached: true,
                        hash: Some(hash),
                    };
                }
                // Proofs and types aren't computed (`erase.rs`).
                let erasing = g.erasure.running();
                let result = eval(g, &[], &Term::Def(test.def)).and_then(|v| force(g, v));
                drop(erasing);
                let outcome = match result {
                    // `Bool` is `False | True`: constructor 1 is `True`.
                    Ok(Value::Ctor(_, 1, _)) => Outcome::Passed,
                    Ok(_) => Outcome::Failed,
                    Err(e) => Outcome::OutOfResources(e),
                };
                cache.put(&hash, &modes, outcome);
                TestResult {
                    name: test.name.clone(),
                    namespace: test.namespace.clone(),
                    outcome,
                    cached: false,
                    hash: Some(hash),
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn session() -> Session {
        let mut session = Session::new();
        session
            .load(
                "cache-test.sw",
                "test \"passes\" := True\ntest \"fails\" := False\n",
            )
            .expect("the tests check");
        session
    }

    #[test]
    fn a_memory_cache_starts_empty_and_records_what_it_adds() {
        let session = session();
        let cache = Cache::memory([]);
        let results = session.run_tests(&cache);
        assert_eq!(results.len(), 2);
        assert!(!results.iter().any(|r| r.cached));
        let added = cache.added();
        assert_eq!(added.len(), 2);
        let modes = modes(&session.elab.globals);
        for (result, (key, outcome)) in results.iter().zip(&added) {
            assert_eq!(key, &Cache::key(&result.hash.expect("a hash"), &modes));
            assert_eq!(*outcome, result.outcome);
        }
        assert_eq!(added[0].1, Outcome::Passed);
        assert_eq!(added[1].1, Outcome::Failed);
    }

    #[test]
    fn a_memory_cache_reuses_known_results() {
        let session = session();
        let first = Cache::memory([]);
        let ran = session.run_tests(&first);
        let second = Cache::memory(first.added());
        let cached = session.run_tests(&second);
        assert!(cached.iter().all(|r| r.cached));
        assert_eq!(cached[0].outcome, ran[0].outcome);
        assert_eq!(cached[1].outcome, ran[1].outcome);
        assert!(second.added().is_empty());
    }

    #[test]
    fn a_key_for_another_modes_string_is_not_used() {
        let session = session();
        let results = session.run_tests(&Cache::disabled());
        let other: Vec<_> = results
            .iter()
            .map(|r| {
                (
                    Cache::key(&r.hash.expect("a hash"), "n0c0-other"),
                    r.outcome,
                )
            })
            .collect();
        let cache = Cache::memory(other);
        let results = session.run_tests(&cache);
        assert!(!results.iter().any(|r| r.cached));
        assert_eq!(cache.added().len(), 2);
    }
}
