//! Runs source files through the compiler pipeline.

use std::path::PathBuf;

use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{Limits, ResourceError, Term, Value};
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
        let mut session = Session {
            sources: SourceMap::new(),
            elab: Elaborator::new(),
            warnings: Vec::new(),
        };
        session.elab.loading_prelude = true;
        if let Err(diagnostics) = session.load("<prelude>", PRELUDE) {
            panic!("internal error: the prelude doesn't check: {diagnostics:#?}");
        }
        session.elab.loading_prelude = false;
        session
    }

    /// Parses, elaborates and checks a file, and checks that its exports can
    /// cross the JS boundary.
    pub fn load(&mut self, name: &str, text: &str) -> Result<FileId, Vec<Diagnostic>> {
        let file = self.sources.add(name, text);
        let module = parse_module_within(file, text, self.elab.limits.stack)?;
        let first_new_def = self.elab.globals.defs.len();
        let mut diagnostics = self.elab.elaborate_module(&module);
        let errors = |ds: &[Diagnostic]| ds.iter().any(|d| d.severity == Severity::Error);
        if !errors(&diagnostics) {
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
        }
        if errors(&diagnostics) {
            Err(diagnostics)
        } else {
            self.warnings.extend(diagnostics);
            Ok(file)
        }
    }

    /// Parses an expression typed in (for `eval` or the REPL), within this
    /// session's stack limit.
    pub fn parse_expression(&mut self, name: &str, text: &str) -> Result<Expr, Diagnostic> {
        let file = self.sources.add(name, text);
        parse_expression_within(file, text, self.elab.limits.stack)
    }

    /// Generates JavaScript for the exports loaded so far.
    pub fn extract(&self) -> Result<stitchwort_js::Output, Diagnostic> {
        stitchwort_js::generate(&self.elab.globals, self.elab.limits)
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
    pub outcome: Outcome,
    /// Whether the outcome came from the cache, rather than running the test.
    pub cached: bool,
    /// `None` if hashing the test ran out of resources.
    pub hash: Option<ContentHash>,
}

/// Test results, stored by the test's content hash (DESIGN.md §11). A test's
/// hash covers everything it depends on, so a cached result stays valid until
/// something the test uses changes. The local cache is trusted.
pub struct Cache {
    dir: Option<PathBuf>,
}

/// Part of every cache key, so results from another version of the compiler
/// aren't reused. (While developing the compiler itself, use `--no-cache`.)
const COMPILER: &str = concat!("stitchwort-", env!("CARGO_PKG_VERSION"));

impl Cache {
    pub fn at(dir: impl Into<PathBuf>) -> Self {
        Cache {
            dir: Some(dir.into()),
        }
    }

    pub fn disabled() -> Self {
        Cache { dir: None }
    }

    fn path(&self, hash: &ContentHash) -> Option<PathBuf> {
        Some(
            self.dir
                .as_ref()?
                .join("tests")
                .join(format!("{COMPILER}-{}", hash.hex())),
        )
    }

    fn get(&self, hash: &ContentHash) -> Option<Outcome> {
        match std::fs::read_to_string(self.path(hash)?).ok()?.trim() {
            "passed" => Some(Outcome::Passed),
            "failed" => Some(Outcome::Failed),
            _ => None,
        }
    }

    /// Best effort: a cache that can't be written just means re-running later.
    fn put(&self, hash: &ContentHash, outcome: Outcome) {
        let Some(path) = self.path(hash) else {
            return;
        };
        let text = match outcome {
            Outcome::Passed => "passed",
            Outcome::Failed => "failed",
            // Not a result: running it again with other limits may finish.
            Outcome::OutOfResources(_) => return,
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
                            outcome: Outcome::OutOfResources(e),
                            cached: false,
                            hash: None,
                        };
                    }
                };
                if let Some(outcome) = cache.get(&hash) {
                    return TestResult {
                        name: test.name.clone(),
                        outcome,
                        cached: true,
                        hash: Some(hash),
                    };
                }
                let outcome = match eval(g, &[], &Term::Def(test.def)).and_then(|v| force(g, v)) {
                    // `Bool` is `False | True`: constructor 1 is `True`.
                    Ok(Value::Ctor(_, 1, _)) => Outcome::Passed,
                    Ok(_) => Outcome::Failed,
                    Err(e) => Outcome::OutOfResources(e),
                };
                cache.put(&hash, outcome);
                TestResult {
                    name: test.name.clone(),
                    outcome,
                    cached: false,
                    hash: Some(hash),
                }
            })
            .collect()
    }
}
