//! Runs source files through the compiler pipeline.

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{Globals, Limits, ResourceError, Term, Value};
use stitchwort_elab::project::{FileModeContext, SourceUnit};
use stitchwort_elab::shown::{SHOWN_NODES, cut, first_difference};
use stitchwort_elab::{Elaborator, LibraryIndex, PRELUDE};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::{
    Diagnostic, FileId, Severity, SourceMap, parse_expression_within, parse_module_recovering,
    parse_module_within,
};

/// Which library files a session knows.
#[derive(Clone, Copy)]
enum Library<'a> {
    /// The standard library, `std/`.
    Standard,
    /// None: the core alone.
    None,
    /// These instead, for tests.
    Files(&'a [(&'a str, &'a str)]),
}

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

/// How many worker threads the tests' per-file loops use: the machine's
/// parallelism capped at 8 (each session holds tens of MB), or
/// `STITCHWORT_TEST_THREADS` if set.
#[doc(hidden)]
pub fn test_threads() -> usize {
    std::env::var("STITCHWORT_TEST_THREADS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|n| *n > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(1, |n| n.get().min(8)))
}

/// Maps `f` over `items` on up to [`test_threads`] threads, each with `stack`
/// bytes of stack, and returns the results in the order of `items`. A panic
/// in `f` is held until every item has run, then the one for the earliest
/// item is re-raised, so failures are reported deterministically.
#[doc(hidden)]
pub fn par_map<T: Sync, R: Send>(stack: usize, items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<Option<std::thread::Result<R>>>> =
        Mutex::new((0..items.len()).map(|_| None).collect());
    let workers = test_threads().min(items.len()).max(1);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            std::thread::Builder::new()
                .stack_size(stack)
                .spawn_scoped(scope, || {
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        let Some(item) = items.get(i) else { break };
                        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(item)));
                        results.lock().unwrap_or_else(|e| e.into_inner())[i] = Some(r);
                    }
                })
                .expect("can't start a thread");
        }
    });
    results
        .into_inner()
        .unwrap_or_else(|e| e.into_inner())
        .into_iter()
        .map(|r| match r.expect("every item ran") {
            Ok(v) => v,
            Err(panic) => std::panic::resume_unwind(panic),
        })
        .collect()
}

/// Whether the slow tier of tests is on: the exhaustive and differential
/// ones that take over ~20 s. `dev/t slow` and the full gate set
/// `STITCHWORT_SLOW=1`.
#[doc(hidden)]
pub fn slow_tier_on() -> bool {
    std::env::var("STITCHWORT_SLOW").is_ok_and(|v| !v.is_empty() && v != "0")
}

/// [`slow_tier_on`], for a test that does nothing otherwise: it says so.
#[doc(hidden)]
pub fn slow_tier(test: &str) -> bool {
    let on = slow_tier_on();
    if !on {
        eprintln!("skipped {test}: slow tier (run `dev/t slow`, or the full gate)");
    }
    on
}

impl Session {
    /// A session for a thread with `stack` bytes of stack.
    pub fn for_stack(stack: usize) -> Self {
        let mut session = Session::new();
        session.elab.limits = Limits::for_stack(stack);
        session
    }

    /// [`Session::navigable`], for a thread with `stack` bytes of stack.
    pub fn navigable_for_stack(stack: usize) -> Self {
        let mut session = Session::navigable();
        session.elab.limits = Limits::for_stack(stack);
        session
    }

    /// [`Session::eager`], for a thread with `stack` bytes of stack.
    #[doc(hidden)]
    pub fn eager_for_stack(stack: usize) -> Self {
        let mut session = Session::eager();
        session.elab.limits = Limits::for_stack(stack);
        session
    }

    pub fn new() -> Self {
        Session::with_prelude(PRELUDE)
    }

    /// A session recording what code navigation needs (the index of
    /// `nav::index_json`), from the core on: recording turned on after the
    /// session was made would miss the names in the core (`std/core/`).
    pub fn navigable() -> Self {
        Self::start(PRELUDE, Library::Standard, false, false, true)
            .unwrap_or_else(|report| panic!("{report}"))
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
        Self::start(prelude, Library::Standard, false, false, false)
    }

    /// A session with every library file loaded up front, in canonical
    /// order, instead of on demand: for tests that compare it with the lazy
    /// one (docs/proposals/std-library.md §4.0).
    #[doc(hidden)]
    pub fn eager() -> Self {
        Self::start(PRELUDE, Library::Standard, true, false, false)
            .unwrap_or_else(|report| panic!("{report}"))
    }

    /// A session with the core only: the library's names aren't known, and
    /// nothing loads. For a test that the core stands on its own.
    #[doc(hidden)]
    pub fn core_alone() -> Self {
        Self::start(PRELUDE, Library::None, false, false, false)
            .unwrap_or_else(|report| panic!("{report}"))
    }

    /// A session whose library is the given files `(path, text)`, after the
    /// real core: for tests of the loader. The files load on demand, or all
    /// of them now with `eager`; with `library_tests` their `test`s are
    /// checked too.
    #[doc(hidden)]
    pub fn with_library_files(
        files: &[(&str, &str)],
        eager: bool,
        library_tests: bool,
    ) -> Result<Self, String> {
        Self::start(PRELUDE, Library::Files(files), eager, library_tests, false)
    }

    /// A session with every library file loaded, and the `test`s of the core
    /// and the library files checked: what [`Session::run_library_tests`]
    /// runs.
    #[doc(hidden)]
    pub fn with_library_tests() -> Self {
        Self::start(PRELUDE, Library::Standard, true, true, false)
            .unwrap_or_else(|report| panic!("{report}"))
    }

    /// Loads the core (the prelude text given), then makes the library's
    /// names known, and loads its files too if `eager`.
    fn start(
        prelude: &str,
        library: Library,
        eager: bool,
        library_tests: bool,
        navigation: bool,
    ) -> Result<Self, String> {
        let mut session = Session {
            sources: SourceMap::new(),
            elab: Elaborator::new(),
            warnings: Vec::new(),
        };
        if navigation {
            session.elab.enable_navigation();
        }
        // Counterexample searches run on the fast runtime (D1154).
        session.elab.counterexample_runner = Some(crate::counterexample::run_fast);
        let stack = session.elab.limits.stack;
        let index = match library {
            Library::Standard | Library::None => LibraryIndex::standard(stack),
            Library::Files(files) => LibraryIndex::build(PRELUDE, files, stack).map(Arc::new),
        }
        .map_err(|e| format!("internal error: the standard library: {e}"))?;
        let report = |sources: &SourceMap, what: &str, diagnostics: &[Diagnostic]| {
            let mut report = format!("internal error: {what}:\n");
            for d in diagnostics {
                report.push_str(&crate::render::render(sources, d, false));
            }
            report
        };
        session.elab.loading_prelude = true;
        session.elab.library_tests = library_tests;
        let file = session.sources.add("<prelude>", prelude);
        // The library's files follow the core in the source map, in the
        // index's order, so the spans the index parsed are this session's.
        for lib in index.files.iter().skip(1) {
            let id = session.sources.add(format!("std/{}", lib.path), &lib.text);
            assert_eq!(
                id, lib.id,
                "the library's files are numbered as the index's"
            );
        }
        // The index has parsed the core, unless a test changed its text.
        let parsed;
        let module = if prelude == index.files[0].text {
            &index.files[0].module
        } else {
            parsed = parse_module_within(file, prelude, stack)
                .map_err(|ds| report(&session.sources, "the prelude doesn't parse", &ds))?;
            &parsed
        };
        let diagnostics = session.elab.elaborate_module(module);
        if let Err(diagnostics) = session.finish_load(0, diagnostics) {
            return Err(report(
                &session.sources,
                "the prelude doesn't check",
                &diagnostics,
            ));
        }
        if let Err(missing) = session.elab.finish_core() {
            return Err(format!("internal error: {}", missing.message));
        }
        if !matches!(library, Library::None) {
            session.elab.install_library(index);
        }
        if eager && let Err(diagnostics) = session.elab.load_all_libraries() {
            return Err(report(
                &session.sources,
                "the standard library doesn't check",
                &diagnostics,
            ));
        }
        Ok(session)
    }

    /// Loads library files and project namespaces from, and keeps them in,
    /// the check cache in the cache directory `dir`
    /// (docs/proposals/check-cache.md). Off unless
    /// this is called: tests, snapshots and the benchmark never use it.
    pub fn use_check_cache(&mut self, dir: &std::path::Path) {
        self.elab
            .set_check_cache(std::rc::Rc::new(crate::check_cache::CheckCache::at(dir)));
    }

    /// Lets `include` read the files of a project: from `files`, where the
    /// project's files are found by their path in it.
    pub fn include_from(&mut self, files: std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>) {
        self.elab.set_include_files(files);
    }

    /// For the next [`Session::load_file`] of a file on its own: `include`
    /// reads from `files`, the file's own folder, and the file is called
    /// `name` in it.
    pub fn include_in_folder(
        &mut self,
        files: std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>,
        name: &str,
    ) {
        self.elab.set_include_files(files);
        self.elab.set_next_include_location(name.to_string());
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
        if let Some(location) = self.elab.take_next_include_location() {
            self.elab.set_include_location(file, location);
        }
        // A syntax error doesn't stop the declarations that parsed from
        // being checked, so one run reports every error; the file never
        // loads as a success, though.
        let (module, parse_errors) = parse_module_recovering(file, text, self.elab.limits.stack);
        let first_new_def = self.elab.globals.defs.len();
        self.elab.file_mode = context;
        let diagnostics =
            if module.namespace.is_none() && module.decls.is_empty() && !parse_errors.is_empty() {
                Vec::new()
            } else {
                self.elab.elaborate_module(&module)
            };
        self.elab.file_mode = None;
        if parse_errors.is_empty() {
            self.finish_load(first_new_def, diagnostics)?;
            Ok(file)
        } else {
            Err(merge_recovered(parse_errors, diagnostics))
        }
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
        let expr = parse_expression_within(file, text, self.elab.limits.stack)?;
        // The library files it uses load now: checking it needs them.
        self.elab.prepare_expr(&expr)?;
        Ok(expr)
    }

    /// Adds `import` lines typed in (the REPL, the playground's Evaluate
    /// tab) to the imports that expressions see; they accumulate. Returns
    /// the errors and warnings, as a file's imports give.
    pub fn add_imports(&mut self, name: &str, text: &str) -> Vec<Diagnostic> {
        let file = self.sources.add(name, text);
        let module = match parse_module_within(file, text, self.elab.limits.stack) {
            Ok(module) => module,
            Err(diagnostics) => return diagnostics,
        };
        if !module.decls.is_empty() || module.namespace.is_some() {
            return vec![Diagnostic::error(
                "E-PARSE",
                "only `import` lines and expressions can be entered here, not declarations",
            )];
        }
        self.elab.add_session_imports(&module.imports)
    }

    /// Parses an expression the driver wrote itself.
    pub(crate) fn parse_internal(&mut self, name: &str, text: &str) -> Result<Expr, Diagnostic> {
        self.parse_expression(name, text)
    }

    /// Generates JavaScript for the exports loaded so far.
    pub fn extract(&self) -> Result<stitchwort_js::Output, Diagnostic> {
        let g = &self.elab.globals;
        self.refuse_unfinished((0..g.defs.len()).map(stitchwort_core::DefId))?;
        stitchwort_js::generate(g, self.elab.limits)
    }

    /// An error if any of the exports among `ids` is unfinished (it, or
    /// something it uses, has an open goal, `?`): it has no body to
    /// generate, and only checked code is built (D636).
    fn refuse_unfinished(
        &self,
        ids: impl Iterator<Item = stitchwort_core::DefId>,
    ) -> Result<(), Diagnostic> {
        let g = &self.elab.globals;
        for id in ids {
            let def = g.def(id);
            if def.export && self.elab.is_unfinished(id) {
                return Err(Diagnostic::error(
                    "E-UNFINISHED",
                    format!(
                        "`{}` can't be built: it, or something it uses, has an open goal (`?`)",
                        def.name
                    ),
                )
                .with_label(def.span, "fill in every goal it needs first"));
            }
        }
        Ok(())
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
        self.refuse_unfinished(ids.iter().copied())?;
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

/// What a load that had syntax errors reports: those, then what checking
/// the declarations that did parse found, in file order. Uses of
/// declarations that failed to parse (`E-FAILED-DEPENDENCY`) go without
/// saying: the syntax error is the cause.
pub(crate) fn merge_recovered(
    parse_errors: Vec<Diagnostic>,
    checked: Vec<Diagnostic>,
) -> Vec<Diagnostic> {
    let mut all = parse_errors;
    all.extend(
        checked
            .into_iter()
            .filter(|d| d.code != "E-FAILED-DEPENDENCY"),
    );
    all.sort_by_key(|d| {
        d.labels.first().map_or((usize::MAX, u32::MAX), |l| {
            (l.span.file.index(), l.span.start)
        })
    });
    all
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
    /// For a failed test, what can be said about why (D601).
    pub detail: Option<Failure>,
}

/// Why a test failed, as far as it can be told: the part of the test that is
/// false, and for a comparison, the values of its two sides. Found by running
/// parts of the test again when it fails, also for a cached failure: the
/// cache keeps only the outcome, so a passing test never pays for this. It's
/// only a presentation: the test failed because the kernel found `False`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    /// Which part of the test is false, when it isn't the whole expression
    /// (the last of some `let`s, or the first false operand of `&&`).
    pub part: Option<Part>,
    /// If that part is a comparison, its two sides.
    pub comparison: Option<Comparison>,
}

/// `range` in `text`, widened over the round brackets the parser leaves out
/// of an expression's span (it has no node for a bracketed expression): an
/// unmatched closer in the range pulls the start back to its opener, and an
/// unmatched opener pushes the end on to its closer. Unchanged if the
/// brackets don't pair up.
fn balanced_range(text: &str, range: std::ops::Range<usize>) -> std::ops::Range<usize> {
    let Some(inside) = text.get(range.clone()) else {
        return range;
    };
    let (mut closers, mut openers) = (0usize, 0usize);
    for c in inside.chars() {
        match c {
            '(' => openers += 1,
            ')' if openers > 0 => openers -= 1,
            ')' => closers += 1,
            _ => {}
        }
    }
    let mut start = range.start;
    let mut need = closers;
    for (i, c) in text[..range.start].char_indices().rev() {
        if need == 0 {
            break;
        }
        match c {
            ')' => need += 1,
            '(' => {
                need -= 1;
                start = i;
            }
            _ => {}
        }
    }
    let mut end = range.end;
    let mut want = openers;
    for (i, c) in text[range.end..].char_indices() {
        if want == 0 {
            break;
        }
        match c {
            '(' => want += 1,
            ')' => {
                want -= 1;
                end = range.end + i + 1;
            }
            _ => {}
        }
    }
    if need > 0 || want > 0 {
        return range;
    }
    start..end
}

/// A part of a test's expression: its text (on one line, cut off with `…` if
/// long) and where it starts (`line` and `column` count from 1).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Part {
    pub text: String,
    pub file: String,
    pub line: usize,
    pub column: usize,
}

/// The two sides of a failed comparison, printed (short ones whole, long ones
/// cut off with `…`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comparison {
    /// The operator as written: `==`, `!=`, `=`, `<`, `<=`, `>` or `>=`.
    pub op: &'static str,
    pub left: String,
    pub right: String,
    /// For two lists or two texts that aren't equal, where they first differ.
    pub difference: Option<String>,
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
///
/// In a directory, each result is a file named by its key and the test it
/// is for ([`Cache::unit`]). Writing a result deletes that test's other
/// results from the same build and modes, and the first write of a run
/// deletes results of other builds more than a day old (D283, as for the
/// check cache).
pub struct Cache {
    dir: Option<PathBuf>,
    memory: Option<RefCell<Memory>>,
    /// Whether this run has written yet (the first write sweeps).
    written: std::cell::Cell<bool>,
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

/// [`FINGERPRINT`] without the toolchain and target: the same in a native
/// and a WebAssembly build of the same sources, so a test can tell whether
/// the playground's bundle is up to date (`stitchwort_web::source_fingerprint`).
pub const SOURCE_FINGERPRINT: &str = env!("STITCHWORT_SOURCE_FINGERPRINT");

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
            written: std::cell::Cell::new(false),
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
            written: std::cell::Cell::new(false),
        }
    }

    pub fn disabled() -> Self {
        Cache {
            dir: None,
            memory: None,
            written: std::cell::Cell::new(false),
        }
    }

    /// The test named `name` in namespace `namespace`, as a directory
    /// cache's file names have it: a short hash.
    pub fn unit(namespace: &str, name: &str) -> String {
        let mut h = blake3::Hasher::new();
        h.update(namespace.as_bytes());
        h.update(&[0]);
        h.update(name.as_bytes());
        h.finalize().as_bytes()[..8]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    /// The key of the result of the test with `hash`, when run with `modes`:
    /// the file name in a directory cache.
    pub fn key(hash: &ContentHash, modes: &str) -> String {
        format!("{COMPILER}-{FINGERPRINT}-{modes}-{}", hash.hex())
    }

    /// Where the result of test `unit` ([`Cache::unit`]) with `hash` is
    /// kept, when run with `modes`.
    pub fn path(&self, unit: &str, hash: &ContentHash, modes: &str) -> Option<PathBuf> {
        Some(self.dir.as_ref()?.join("tests").join(format!(
            "{}-{unit}-{}",
            Self::build(modes),
            hash.hex()
        )))
    }

    /// The start of the file names of this build's results with `modes`.
    fn build(modes: &str) -> String {
        format!("{COMPILER}-{FINGERPRINT}-{modes}")
    }

    /// After writing `keep`, the result of test `unit`: deletes the test's
    /// other results for this build and modes, and on the first write of a
    /// run, other builds' results older than a day.
    fn evict(&self, unit: &str, modes: &str, keep: &std::path::Path) {
        let first = !self.written.replace(true);
        let Some(dir) = keep.parent() else {
            return;
        };
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        let own = format!("{}-{unit}-", Self::build(modes));
        let this_build = format!("{COMPILER}-{FINGERPRINT}-");
        let now = std::time::SystemTime::now();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if path == keep {
                continue;
            }
            let stale = name.starts_with(&own)
                || (first
                    && !name.starts_with(&this_build)
                    && entry
                        .metadata()
                        .and_then(|m| m.modified())
                        .ok()
                        .and_then(|t| now.duration_since(t).ok())
                        .is_some_and(|age| age > crate::check_cache::GRACE));
            if stale {
                let _ = std::fs::remove_file(&path);
            }
        }
    }

    /// The results added by [`Cache::put`] during this run: only `Passed` and
    /// `Failed`, like the ones on disk. Empty for a cache without memory.
    pub fn added(&self) -> Vec<(String, Outcome)> {
        self.memory
            .as_ref()
            .map_or_else(Vec::new, |memory| memory.borrow().added.clone())
    }

    fn get(&self, unit: &str, hash: &ContentHash, modes: &str) -> Option<Outcome> {
        if let Some(memory) = &self.memory {
            return memory.borrow().known.get(&Self::key(hash, modes)).copied();
        }
        match std::fs::read_to_string(self.path(unit, hash, modes)?)
            .ok()?
            .trim()
        {
            "passed" => Some(Outcome::Passed),
            "failed" => Some(Outcome::Failed),
            _ => None,
        }
    }

    /// Best effort: a cache that can't be written just means re-running later.
    fn put(&self, unit: &str, hash: &ContentHash, modes: &str, outcome: Outcome) {
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
        let Some(path) = self.path(unit, hash, modes) else {
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
        if std::fs::write(&path, text).is_ok() {
            self.evict(unit, modes, &path);
        }
    }
}

/// The most characters of a part of a test shown to say where it failed.
const SHOWN_PART: usize = 100;

/// Which evaluator runs a test.
#[derive(Clone, Copy)]
enum Runner {
    /// The reference evaluator, the type checker's own.
    Reference,
    /// The machine of `stitchwort-rt`, falling back to the reference
    /// evaluator.
    Machine,
}

/// Which of the session's tests to run.
type Selection<'a> = dyn Fn(&stitchwort_elab::TestDecl) -> bool + 'a;

/// Tests lowered for the machine.
struct TestMachine {
    program: stitchwort_rt::Program,
}

impl TestMachine {
    /// The outcome of the test `def` on `machine`, if it was lowered and
    /// finished there: running out of resources is left to the reference
    /// evaluator, whose limits a test's result is reported against.
    fn run(
        &self,
        machine: &mut stitchwort_rt::Machine,
        def: stitchwort_core::DefId,
    ) -> Option<Outcome> {
        let global = self.program.globals.iter().position(|g| g.def == def)?;
        let global = stitchwort_rt::ir::GlobalId(u32::try_from(global).ok()?);
        machine.reset_steps();
        match machine.global(global) {
            Ok(stitchwort_rt::value::Value::Tag(tag)) => {
                Some(if tag == self.program.shapes.true_ {
                    Outcome::Passed
                } else {
                    Outcome::Failed
                })
            }
            _ => None,
        }
    }
}

impl Session {
    /// Runs every test of the program loaded so far, using cached results
    /// where possible. The core's and the library's tests aren't the
    /// program's (docs/proposals/std-library.md §4.7): see
    /// [`Session::run_library_tests`].
    pub fn run_tests(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| !test.library, Runner::Reference)
    }

    /// [`Session::run_tests`], for only the tests `keep` keeps.
    pub fn run_tests_where(
        &self,
        cache: &Cache,
        keep: impl Fn(&stitchwort_elab::TestDecl) -> bool,
    ) -> Vec<TestResult> {
        self.run_selected(
            cache,
            &|test| !test.library && keep(test),
            Runner::Reference,
        )
    }

    /// [`Session::run_tests`], on the machine of `stitchwort-rt`
    /// (docs/proposals/fast-runtime.md) where it can: a test it can't lower
    /// or finish runs on the reference evaluator, which also still explains
    /// a failure (SW-412).
    pub fn run_tests_fast(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| !test.library, Runner::Machine)
    }

    /// Runs the tests of the core and of the library files loaded (all of
    /// them, in [`Session::with_library_tests`]).
    pub fn run_library_tests(&self, cache: &Cache) -> Vec<TestResult> {
        self.run_selected(cache, &|test| test.library, Runner::Reference)
    }

    /// The tests `selected` that `cache` has no result for, lowered together
    /// for the machine, if they can be. One that can't be lowered with the
    /// others is left out (and runs on the reference evaluator).
    fn lower_tests(&self, cache: &Cache, selected: &Selection, modes: &str) -> Option<TestMachine> {
        let g = &self.elab.globals;
        let wanted: Vec<stitchwort_core::DefId> = self
            .elab
            .tests
            .iter()
            .filter(|test| selected(test))
            .filter(|test| {
                let _op = g.budget.operation(self.elab.limits);
                match def_hash(g, test.def) {
                    Ok(Some(hash)) => cache
                        .get(&Cache::unit(&test.namespace, &test.name), &hash, modes)
                        .is_none(),
                    _ => false,
                }
            })
            .map(|test| test.def)
            .collect();
        if wanted.is_empty() {
            return None;
        }
        let lower = |ids: &[stitchwort_core::DefId]| {
            stitchwort_rt::lower_definitions(g, self.elab.limits, ids).ok()
        };
        // Together, so what they share is lowered once; one at a time only
        // if some test can't be lowered.
        let program = lower(&wanted).or_else(|| {
            let lowerable: Vec<_> = wanted
                .iter()
                .copied()
                .filter(|id| lower(&[*id]).is_some())
                .collect();
            lower(&lowerable)
        })?;
        Some(TestMachine { program })
    }

    fn run_selected(&self, cache: &Cache, selected: &Selection, runner: Runner) -> Vec<TestResult> {
        let g = &self.elab.globals;
        // A result is kept per runner: the two are only differentially
        // tested to agree (docs/proposals/fast-runtime.md).
        let modes = match runner {
            Runner::Reference => modes(g),
            Runner::Machine => format!("{}m", modes(g)),
        };
        let lowered = match runner {
            Runner::Reference => None,
            Runner::Machine => self.lower_tests(cache, selected, &modes),
        };
        let mut machine = lowered.as_ref().map(|lowered| {
            stitchwort_rt::Machine::new(
                &lowered.program,
                stitchwort_rt::Limits::from_core(self.elab.limits),
            )
        });
        self.elab
            .tests
            .iter()
            .filter(|test| selected(test))
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
                            detail: None,
                        };
                    }
                };
                let unit = Cache::unit(&test.namespace, &test.name);
                if let Some(outcome) = cache.get(&unit, &hash, &modes) {
                    return TestResult {
                        name: test.name.clone(),
                        namespace: test.namespace.clone(),
                        outcome,
                        cached: true,
                        hash: Some(hash),
                        detail: self.failure(test, outcome),
                    };
                }
                let on_machine = match (&lowered, &mut machine) {
                    (Some(lowered), Some(machine)) => lowered.run(machine, test.def),
                    _ => None,
                };
                let outcome = on_machine.unwrap_or_else(|| {
                    // Proofs and types aren't computed (`erase.rs`).
                    let _erasing = g.erasure.running();
                    match eval(g, &[], &Term::Def(test.def)).and_then(|v| force(g, v)) {
                        // `Bool` is `False | True`: constructor 1 is `True`.
                        Ok(Value::Ctor(_, 1, _)) => Outcome::Passed,
                        Ok(_) => Outcome::Failed,
                        Err(e) => Outcome::OutOfResources(e),
                    }
                });
                cache.put(&unit, &hash, &modes, outcome);
                TestResult {
                    name: test.name.clone(),
                    namespace: test.namespace.clone(),
                    outcome,
                    cached: false,
                    hash: Some(hash),
                    detail: self.failure(test, outcome),
                }
            })
            .collect()
    }

    /// Why `test` failed, if it did and that can be told (D601): walks down
    /// its probe to the first false operand of each `&&`, then shows the sides
    /// of the comparison it ends at. Every step runs a closed term of its own,
    /// so what's wrong with one never changes the outcome.
    fn failure(&self, test: &stitchwort_elab::TestDecl, outcome: Outcome) -> Option<Failure> {
        use stitchwort_elab::ProbeKind;
        if outcome != Outcome::Failed {
            return None;
        }
        let mut probe = test.probe.as_ref()?;
        while let ProbeKind::And(a, b) = &probe.kind {
            // `a && b` is false when `a` is, and otherwise when `b` is.
            match self.holds(a) {
                Some(true) => probe = b,
                Some(false) => probe = a,
                None => break,
            }
        }
        let part = if probe.whole {
            None
        } else {
            self.part(probe.span)
        };
        let comparison = match &probe.kind {
            ProbeKind::Compare { op, left, right } => Some(self.compare(op, left, right)),
            _ => None,
        };
        if part.is_none() && comparison.is_none() {
            return None;
        }
        Some(Failure { part, comparison })
    }

    /// Whether the operand `probe` is `True`, if it can be told.
    fn holds(&self, probe: &stitchwort_elab::Probe) -> Option<bool> {
        let g = &self.elab.globals;
        let term = probe.truth.as_ref()?;
        let _op = g.budget.operation(self.elab.limits);
        let _erasing = g.erasure.running();
        match eval(g, &[], term).and_then(|v| force(g, v)) {
            Ok(Value::Ctor(_, c, _)) => Some(c == 1),
            _ => None,
        }
    }

    /// The text and place of the expression at `span`.
    fn part(&self, span: stitchwort_syntax::Span) -> Option<Part> {
        if span.file.index() >= self.sources.len() {
            return None;
        }
        let file = self.sources.get(span.file);
        let range = balanced_range(&file.text, span.range());
        let text = file.text.get(range.clone())?;
        let before = file.text.get(..range.start)?;
        let line = before.matches('\n').count() + 1;
        let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
        let one_line = text.split_whitespace().collect::<Vec<_>>().join(" ");
        let shown: String = if one_line.chars().count() > SHOWN_PART {
            let mut cut: String = one_line.chars().take(SHOWN_PART).collect();
            cut.push('…');
            cut
        } else {
            one_line
        };
        Some(Part {
            text: shown,
            file: file.name.clone(),
            line,
            column,
        })
    }

    /// The values of the sides of a comparison.
    fn compare(&self, op: &'static str, left: &Term, right: &Term) -> Comparison {
        let g = &self.elab.globals;
        // Each side is shown in an operation of its own, with a small limit
        // on the size of the value: a value too big to show is a marker, and
        // never a crash (quoting a very long list nests as deep as it is
        // long, which overflows the WebAssembly stack).
        let limits = Limits {
            size: SHOWN_NODES,
            ..self.elab.limits
        };
        let show = |term: &Term| -> (String, Option<Term>) {
            let _op = g.budget.operation(limits);
            let _erasing = g.erasure.running();
            let Ok(v) = eval(g, &[], term) else {
                return ("…".to_string(), None);
            };
            match stitchwort_core::value::quote(g, 0, &v) {
                Ok(t) => (cut(&stitchwort_core::pretty::term(g, &[], &t)), Some(t)),
                Err(_) => ("… (too large to show)".to_string(), None),
            }
        };
        let (left, left_term) = show(left);
        let (right, right_term) = show(right);
        let difference = match (op, &left_term, &right_term) {
            ("==" | "=", Some(l), Some(r)) => first_difference(g, l, r),
            _ => None,
        };
        Comparison {
            op,
            left,
            right,
            difference,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_part_keeps_the_brackets_the_parser_left_out_of_its_span() {
        let text = "a && (f x).y == 2 && g (z) == 1";
        // `f x).y == 2` is the span the parser gives; `g (z` likewise.
        let first = text.find("f x").unwrap();
        let range = first..text.find(" &&").map(|_| 17).unwrap();
        assert_eq!(&text[balanced_range(text, range)], "(f x).y == 2");
        let second = text.find("g (z").unwrap();
        assert_eq!(&text[balanced_range(text, second..second + 4)], "g (z)");
        assert_eq!(&text[balanced_range(text, 0..4)], "a &&");
    }

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
