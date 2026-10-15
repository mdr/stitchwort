//! Runs source files through the compiler pipeline.

use std::path::PathBuf;

use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{Term, Value};
use stitchwort_elab::{Elaborator, PRELUDE};
use stitchwort_syntax::{Diagnostic, FileId, SourceMap, parse_module};

/// A compiler session: the prelude plus whatever has been loaded since.
pub struct Session {
    pub sources: SourceMap,
    pub elab: Elaborator,
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    pub fn new() -> Self {
        let mut session = Session {
            sources: SourceMap::new(),
            elab: Elaborator::new(),
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
        let module = parse_module(file, text)?;
        let first_new_def = self.elab.globals.defs.len();
        let mut diagnostics = self.elab.elaborate_module(&module);
        if diagnostics.is_empty() {
            for id in first_new_def..self.elab.globals.defs.len() {
                let id = stitchwort_core::DefId(id);
                if self.elab.globals.def(id).export
                    && let Err(d) = stitchwort_js::exportable(&self.elab.globals, id)
                {
                    diagnostics.push(d);
                }
            }
        }
        if diagnostics.is_empty() {
            Ok(file)
        } else {
            Err(diagnostics)
        }
    }
}

/// Whether a test's expression evaluated to `True`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Passed,
    Failed,
}

pub struct TestResult {
    pub name: String,
    pub outcome: Outcome,
    /// Whether the outcome came from the cache, rather than running the test.
    pub cached: bool,
    pub hash: ContentHash,
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
                let hash = def_hash(g, test.def).expect("tests are checked before they run");
                if let Some(outcome) = cache.get(&hash) {
                    return TestResult {
                        name: test.name.clone(),
                        outcome,
                        cached: true,
                        hash,
                    };
                }
                // `Bool` is `False | True`: constructor 1 is `True`.
                let outcome = match force(g, eval(g, &[], &Term::Def(test.def))) {
                    Value::Ctor(_, 1, _) => Outcome::Passed,
                    _ => Outcome::Failed,
                };
                cache.put(&hash, outcome);
                TestResult {
                    name: test.name.clone(),
                    outcome,
                    cached: false,
                    hash,
                }
            })
            .collect()
    }
}
