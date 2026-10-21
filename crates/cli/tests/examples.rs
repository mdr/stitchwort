//! Runs every example program under `examples/` through the compiler.
//!
//! - `accept/` and `extract/`: must check without errors, and their tests must pass.
//! - `reject/` and `soundness/`: must fail with the error code declared on a
//!   `-- expect-error: <CODE>` line at the top of the file. Failing with any other
//!   code (or panicking) is a test failure. The rendered errors are snapshot-tested.
//! - In `soundness/`, a file whose first line starts with `-- known-gap` documents
//!   a soundness hole we haven't fixed: it's expected to be (wrongly) accepted,
//!   and the test fails once it's rejected so the marker gets removed.
//!
//! See `examples/README.md`.

use std::path::{Path, PathBuf};

use stitchwort_cli::driver::{Cache, Outcome, Session, par_map};
use stitchwort_cli::project::{DiskFiles, Target};
use stitchwort_cli::render::render;
use stitchwort_syntax::{Diagnostic, SourceMap};

const KNOWN_GAP: &str = "-- known-gap";
const EXPECT_ERROR: &str = "-- expect-error:";

struct Example {
    /// Path relative to `examples/`, e.g. `reject/non-positive.sw`.
    name: String,
    text: String,
}

impl Example {
    /// The error code declared in the file's leading comment lines.
    fn expected_error(&self) -> Option<&str> {
        self.text
            .lines()
            .take_while(|line| line.starts_with("--"))
            .find_map(|line| line.strip_prefix(EXPECT_ERROR))
            .map(str::trim)
    }
}

/// Whether the example called `name` should run: `EXAMPLES` unset or empty
/// means every example, otherwise only those whose name contains it.
fn wanted(name: &str) -> bool {
    std::env::var("EXAMPLES").map_or(true, |filter| filter.is_empty() || name.contains(&filter))
}

fn examples(dir: &str) -> Vec<Example> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .map(|entry| entry.expect("readable directory entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "sw"))
        .filter(|path| wanted(&path.file_name().unwrap().to_string_lossy()))
        .collect();
    paths.sort();

    paths
        .into_iter()
        .map(|path| Example {
            name: format!("{dir}/{}", path.file_name().unwrap().to_string_lossy()),
            text: std::fs::read_to_string(&path).expect("readable example"),
        })
        .collect()
}

fn check(example: &Example) -> (SourceMap, Result<(), Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load(&example.name, &example.text).map(|_| ());
    (session.sources, result)
}

fn rendered(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|diagnostic| render(sources, diagnostic, false))
        .collect()
}

fn snapshot_name(example: &Example) -> String {
    example.name.trim_end_matches(".sw").replace('/', "__")
}

/// Examples run with this much stack (and the matching resource limits), as
/// they would from the command line, rather than a test thread's 2 MiB.
const STACK: usize = 16 * 1024 * 1024;

#[test]
fn accepted_examples_check() {
    let all: Vec<Example> = examples("accept")
        .into_iter()
        .chain(examples("extract"))
        .collect();
    let failures: Vec<String> = par_map(STACK, &all, accepted_example)
        .into_iter()
        .flatten()
        .collect();
    assert!(
        failures.is_empty(),
        "these examples should check but don't:\n\n{}",
        failures.join("\n")
    );
}

/// The failures (if any) of one accepted example, rendered.
fn accepted_example(example: &Example) -> Vec<String> {
    let mut failures = Vec::new();
    let mut session = Session::for_stack(STACK);
    if let Err(diagnostics) = session.load(&example.name, &example.text) {
        failures.push(format!(
            "{}:\n{}",
            example.name,
            rendered(&session.sources, &diagnostics)
        ));
        return failures;
    }
    // Their tests must pass too.
    for result in session.run_tests(&Cache::disabled()) {
        if result.outcome != Outcome::Passed {
            failures.push(format!(
                "{}: test \"{}\" failed\n",
                example.name, result.name
            ));
        }
    }
    failures
}

#[test]
fn rejected_examples_fail_for_the_expected_reason() {
    par_map(STACK, &examples("reject"), assert_rejected);
}

#[test]
fn soundness_examples_fail_for_the_expected_reason() {
    par_map(STACK, &examples("soundness"), |example| {
        if example.text.starts_with(KNOWN_GAP) {
            if let (sources, Err(diagnostics)) = check(example) {
                panic!(
                    "{} is marked `{KNOWN_GAP}` but is now rejected. Remove the marker!\n\n{}",
                    example.name,
                    rendered(&sources, &diagnostics)
                );
            }
        } else {
            assert_rejected(example);
        }
    });
}

/// The project folders under `examples/projects/<dir>/`, sorted.
fn projects(dir: &str) -> Vec<(String, PathBuf)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects");
    let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
        return Vec::new();
    };
    let mut found: Vec<(String, PathBuf)> = entries
        .map(|entry| entry.expect("readable directory entry").path())
        .filter(|path| path.is_dir())
        .filter(|path| wanted(&path.file_name().unwrap().to_string_lossy()))
        .map(|path| {
            (
                path.file_name().unwrap().to_string_lossy().to_string(),
                path,
            )
        })
        .collect();
    found.sort();
    found
}

fn load_project(name: &str, path: &Path, session: &mut Session) -> Result<(), Vec<Diagnostic>> {
    let files = DiskFiles {
        root: path.to_path_buf(),
    };
    session
        .load_project(&files, name, &Target::Everything)
        .map(|_| ())
}

#[test]
fn accepted_projects_check() {
    let all = projects("accept");
    if std::env::var("EXAMPLES").map_or(true, |v| v.is_empty()) {
        assert!(!all.is_empty());
    }
    let failures: Vec<String> = par_map(STACK, &all, |(name, path)| {
        let mut failures = Vec::new();
        let mut session = Session::for_stack(STACK);
        if let Err(diagnostics) = load_project(name, path, &mut session) {
            failures.push(format!(
                "{name}:\n{}",
                rendered(&session.sources, &diagnostics)
            ));
            return failures;
        }
        for result in session.run_tests(&Cache::disabled()) {
            if result.outcome != Outcome::Passed {
                failures.push(format!(
                    "{name}: test \"{}\" in {} failed\n",
                    result.name, result.namespace
                ));
            }
        }
        failures
    })
    .into_iter()
    .flatten()
    .collect();
    assert!(
        failures.is_empty(),
        "these projects should check but don't:\n\n{}",
        failures.join("\n")
    );
}

#[test]
fn rejected_projects_fail_for_the_expected_reason() {
    let all = projects("reject");
    if std::env::var("EXAMPLES").map_or(true, |v| v.is_empty()) {
        assert!(!all.is_empty());
    }
    par_map(STACK, &all, |(name, path)| {
        let config = std::fs::read_to_string(path.join("stitchwort.yaml"))
            .expect("a project has a stitchwort.yaml");
        let Some(expected) = config
            .lines()
            .take_while(|line| line.starts_with('#'))
            .find_map(|line| line.strip_prefix("# expect-error:"))
            .map(str::trim)
        else {
            panic!(
                "projects/reject/{name} must declare the error it expects, e.g. `# expect-error: E-NAMESPACE-CYCLE`"
            );
        };
        let mut session = Session::for_stack(STACK);
        match load_project(name, path, &mut session) {
            Ok(()) => panic!("projects/reject/{name} should be rejected but checks"),
            Err(diagnostics) => {
                let output = rendered(&session.sources, &diagnostics);
                assert!(
                    diagnostics.iter().any(|d| d.code == expected),
                    "projects/reject/{name} was rejected, but not with {expected}:\n\n{output}"
                );
                insta::assert_snapshot!(format!("projects__reject__{name}"), output);
            }
        }
    });
}

fn assert_rejected(example: &Example) {
    let Some(expected) = example.expected_error() else {
        panic!(
            "{} must declare the error it expects, e.g. `{EXPECT_ERROR} E-POSITIVITY`",
            example.name
        );
    };
    match check(example) {
        (_, Ok(())) => panic!("{} should be rejected but checks", example.name),
        (sources, Err(diagnostics)) => {
            let output = rendered(&sources, &diagnostics);
            assert!(
                diagnostics.iter().any(|d| d.code == expected),
                "{} was rejected, but not with {expected}:\n\n{output}",
                example.name
            );
            insta::assert_snapshot!(snapshot_name(example), output);
        }
    }
}
