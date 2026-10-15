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

use stitchwort_cli::driver::{Cache, Outcome, Session, with_stack};
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

fn examples(dir: &str) -> Vec<Example> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .map(|entry| entry.expect("readable directory entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "sw"))
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
    with_stack(STACK, accepted_examples)
}

fn accepted_examples() {
    let mut failures = Vec::new();
    for example in examples("accept").into_iter().chain(examples("extract")) {
        let mut session = Session::for_stack(STACK);
        if let Err(diagnostics) = session.load(&example.name, &example.text) {
            failures.push(format!(
                "{}:\n{}",
                example.name,
                rendered(&session.sources, &diagnostics)
            ));
            continue;
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
    }
    assert!(
        failures.is_empty(),
        "these examples should check but don't:\n\n{}",
        failures.join("\n")
    );
}

#[test]
fn rejected_examples_fail_for_the_expected_reason() {
    for example in examples("reject") {
        assert_rejected(&example);
    }
}

#[test]
fn soundness_examples_fail_for_the_expected_reason() {
    for example in examples("soundness") {
        if example.text.starts_with(KNOWN_GAP) {
            if let (sources, Err(diagnostics)) = check(&example) {
                panic!(
                    "{} is marked `{KNOWN_GAP}` but is now rejected. Remove the marker!\n\n{}",
                    example.name,
                    rendered(&sources, &diagnostics)
                );
            }
        } else {
            assert_rejected(&example);
        }
    }
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
