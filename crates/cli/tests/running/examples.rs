//! Runs every example program under `examples/` through the compiler.
//!
//! - `accept/` and `extract/`: must check without errors, and their tests must pass.
//!   One that declares a warning on a `-- expect-warning: <CODE>` line at the
//!   top of the file must report it, and its rendered warnings are
//!   snapshot-tested.
//! - `reject/` and `soundness/`: must fail with the error code declared on a
//!   `-- expect-error: <CODE>` line at the top of the file. Failing with any other
//!   code (or panicking) is a test failure. The rendered errors are snapshot-tested.
//! - In `soundness/`, a file whose first line starts with `-- known-gap` documents
//!   a soundness hole we haven't fixed: it's expected to be (wrongly) accepted,
//!   and the test fails once it's rejected so the marker gets removed.
//! - `goals/` (and `projects/goals/`): must report open goals (`?`), and no
//!   errors unless the file declares one with `-- expect-error:`; their tests
//!   must pass, unless the file names one on an `-- expect-test-failure:` line
//!   that must fail because it reaches an open goal. The rendered goals (and
//!   errors) are snapshot-tested.
//!
//! See `examples/README.md`.

use std::path::{Path, PathBuf};

use crate::common;

use stitchwort_cli::driver::{
    Cache, Outcome, Session, Tier, daily_tier_sample, daily_tier_sample_at, par_map_labelled,
    par_map_sessions, tier,
};
use stitchwort_cli::project::{DiskFiles, Target};
use stitchwort_cli::render::{render, with_repeated_generic_notes_cut};
use stitchwort_syntax::{Diagnostic, Severity, SourceMap};

const KNOWN_GAP: &str = "-- known-gap";
const EXPECT_ERROR: &str = "-- expect-error:";
const EXPECT_WARNING: &str = "-- expect-warning:";
const EXPECT_TEST_FAILURE: &str = "-- expect-test-failure:";
const EXPECT_METRICS: &str = "-- metrics:";

struct Example {
    /// Path relative to `examples/`, e.g. `reject/non-positive.sw`.
    name: String,
    text: String,
}

impl Example {
    /// The error code declared in the file's leading comment lines.
    fn expected_error(&self) -> Option<&str> {
        self.declared(EXPECT_ERROR)
    }

    /// The warning code declared in the file's leading comment lines.
    fn expected_warning(&self) -> Option<&str> {
        self.declared(EXPECT_WARNING)
    }

    /// The test declared to fail, in the file's leading comment lines, because
    /// its code reaches an open goal.
    fn expected_test_failure(&self) -> Option<&str> {
        self.declared(EXPECT_TEST_FAILURE)
    }

    /// The metrics outcomes declared in the file's leading comment lines
    /// (`-- metrics: guard-as-written: unchecked`, one per line): each must
    /// happen at least once while the example elaborates.
    fn expected_metrics(&self) -> Vec<&str> {
        self.text
            .lines()
            .take_while(|line| line.starts_with("--"))
            .filter_map(|line| line.strip_prefix(EXPECT_METRICS))
            .map(str::trim)
            .collect()
    }

    fn declared(&self, prefix: &str) -> Option<&str> {
        self.text
            .lines()
            .take_while(|line| line.starts_with("--"))
            .find_map(|line| line.strip_prefix(prefix))
            .map(str::trim)
    }
}

/// Whether `name` matches `filter`: unset or empty means every one, otherwise
/// only those whose name contains one of its comma-separated substrings.
fn matches(filter: &str, name: &str) -> bool {
    filter.is_empty()
        || filter
            .split(',')
            .map(str::trim)
            .any(|part| !part.is_empty() && name.contains(part))
}

/// Whether the example called `name` should run: `EXAMPLES` unset or empty
/// means every example, otherwise only those whose name contains one of its
/// comma-separated substrings.
fn wanted(name: &str) -> bool {
    std::env::var("EXAMPLES").map_or(true, |filter| matches(&filter, name))
}

#[test]
fn examples_filter_takes_a_comma_separated_list() {
    assert!(matches("parse", "parse-basics.sw"));
    assert!(!matches("parse", "safe-fields.sw"));
    assert!(matches("parse,safe-fields", "safe-fields.sw"));
    assert!(matches("safe-fields, parse", "parse-basics.sw"));
    assert!(!matches("other,none", "parse-basics.sw"));
    assert!(
        matches("", "anything.sw"),
        "an empty filter keeps everything"
    );
}

/// A part that matches nothing fails, and a part that matches still counts
/// beside one that needs no match.
#[test]
fn a_filter_part_that_matches_nothing_is_an_error() {
    let names = vec!["parse-basics.sw".to_string(), "safe-fields.sw".to_string()];
    assert!(common::filter_error("parse,safe-fields", &names, "example file name").is_none());
    assert!(common::filter_error("", &names, "example file name").is_none());
    let message = common::filter_error("examples", &names, "example file name").unwrap();
    assert!(
        message.contains("EXAMPLES=examples matches no example (did you mean"),
        "{message}"
    );
    assert!(
        message.contains("EXAMPLES filters by example file name"),
        "{message}"
    );
    let message = common::filter_error("parse,examples", &names, "example file name").unwrap();
    assert!(
        message.contains("part that matches no example: `examples`"),
        "{message}"
    );
}

/// Whether `EXAMPLES` is filtering the examples.
fn filtering() -> bool {
    std::env::var("EXAMPLES").is_ok_and(|filter| !filter.is_empty())
}

/// A sweep's share of the examples or projects of one folder: all of them
/// when `EXAMPLES` picks some by name, otherwise this tier's sample
/// (`daily_tier_sample`): every one in the broad and all tiers, every fourth
/// in the quick and lane tiers, from a place that moves on daily
/// (`EXAMPLES_SEED` pins it, and the seed is printed).
fn share<T>(items: Vec<T>) -> Vec<T> {
    if filtering() {
        items
    } else {
        match tier() {
            Tier::Broad | Tier::All => items,
            Tier::Quick | Tier::Lane => daily_tier_sample(items, 1, "EXAMPLES_SEED"),
        }
    }
}

/// Four consecutive days' quick samples take every example exactly once
/// (stride 4, which is `broad_stride` 1 in the quick tier): no example is
/// always left out, whether or not the count divides by four. A list
/// shorter than the stride yields one example a day (never an empty sample),
/// and as many consecutive days as it has examples take every one once.
#[test]
fn four_consecutive_days_cover_every_example_once() {
    for len in [4, 5, 12, 13, 17] {
        let indices: Vec<usize> = (0..len).collect();
        let mut seen = vec![0; len];
        for day in 0..4 {
            for index in daily_tier_sample_at(indices.clone(), 1, day, Tier::Quick) {
                seen[index] += 1;
            }
        }
        assert!(
            seen.iter().all(|count| *count == 1),
            "{len} examples over four days: {seen:?}"
        );
    }
    for len in 1..4usize {
        let indices: Vec<usize> = (0..len).collect();
        for day in 0..4u64 {
            let sample = daily_tier_sample_at(indices.clone(), 1, day, Tier::Quick);
            assert!(
                !sample.is_empty(),
                "{len} examples on day {day}: the sample is empty"
            );
        }
        for start in 0..4u64 {
            let mut seen = vec![0; len];
            for day in start..start + len as u64 {
                for index in daily_tier_sample_at(indices.clone(), 1, day, Tier::Quick) {
                    seen[index] += 1;
                }
            }
            assert!(
                seen.iter().all(|count| *count == 1),
                "{len} examples over {len} days from {start}: {seen:?}"
            );
        }
    }
    assert!(
        daily_tier_sample_at(Vec::<usize>::new(), 1, 0, Tier::Quick).is_empty(),
        "no examples: the sample is empty"
    );
}

fn examples(dir: &str) -> Vec<Example> {
    // A part that matched in another folder or a project still counts: only
    // one that matches nothing anywhere is a mistake.
    common::check_examples_env(
        &common::all_names(),
        "example file name (or project folder name)",
    );
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

    share(paths)
        .into_iter()
        .map(|path| Example {
            name: format!("{dir}/{}", path.file_name().unwrap().to_string_lossy()),
            text: std::fs::read_to_string(&path).expect("readable example"),
        })
        .collect()
}

/// `session`, its counterexample searches stopping at their count of inputs
/// and never at their 200 ms time limit. Snapshots include a failing proof's
/// counterexample note, and a timed search under machine load finds nothing
/// in time, so the rendering differed (the flaky
/// `rejected_examples_fail_for_the_expected_reason`, 26 Oct 2026).
///
/// The library loads through the test std cache (in every tier but the full
/// one): it's the examples that are checked here.
fn untimed(mut session: Session) -> Session {
    session.use_test_std_cache();
    session.elab.options.untimed_counterexamples = true;
    session
}

/// A session for checking examples in: [`untimed`], with `stack`.
fn example_session(stack: usize) -> Session {
    untimed(Session::for_stack(stack))
}

/// Checks one example in `session`, rewound as new ([`par_map_sessions`]):
/// whether it loaded. A panic says which example led there when the sweep
/// re-raises it.
fn check(session: &mut Session, example: &Example) -> Result<(), Vec<Diagnostic>> {
    session.load(&example.name, &example.text).map(|_| ())
}

/// The command line's text output for one run: a generic note is printed in
/// full the first time only.
fn rendered(sources: &SourceMap, diagnostics: &[Diagnostic]) -> String {
    let mut seen = stitchwort_core::collections::HashSet::default();
    diagnostics
        .iter()
        .map(|diagnostic| {
            let diagnostic = with_repeated_generic_notes_cut(diagnostic, &mut seen);
            render(sources, &diagnostic, false)
        })
        .collect()
}

fn snapshot_name(example: &Example) -> String {
    example.name.trim_end_matches(".sw").replace('/', "__")
}

/// Whether the snapshot named `name` (the part after `running__examples__`)
/// has no example file or project folder behind it.
fn example_snapshot_is_orphaned(name: &str, examples: &Path) -> bool {
    let exists = if let Some(project) = name.strip_prefix("projects__") {
        // `projects__goals__NAME` (or `projects__reject__NAME`).
        project
            .split_once("__")
            .is_some_and(|(kind, name)| examples.join("projects").join(kind).join(name).is_dir())
    } else {
        // `<category>__<file stem>`.
        name.split_once("__").is_some_and(|(category, stem)| {
            examples.join(category).join(format!("{stem}.sw")).is_file()
        })
    };
    !exists
}

/// The mapping catches a name whose example or project is gone, not just the
/// current set's empty result.
#[test]
fn an_example_snapshot_without_its_example_is_orphaned() {
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    assert!(!example_snapshot_is_orphaned(
        "accept__abbreviation-meets-call",
        &examples
    ));
    assert!(!example_snapshot_is_orphaned(
        "projects__goals__across-namespaces",
        &examples
    ));
    assert!(example_snapshot_is_orphaned(
        "reject__no-such-example",
        &examples
    ));
    assert!(example_snapshot_is_orphaned(
        "projects__reject__no-such-project",
        &examples
    ));
}

/// Fails listing every `running__examples__*.snap` whose example or project
/// no longer exists. Insta only notices snapshots a test asked for, so a
/// renamed or deleted example would leave its snapshot behind silently; this
/// maps each name back the way [`snapshot_name`] and the project tests write
/// them (`projects__<kind>__<name>`).
#[test]
fn no_example_snapshots_are_orphaned() {
    let snapshots = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/running/snapshots");
    let examples = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut orphans = Vec::new();
    let mut checked = 0;
    for entry in std::fs::read_dir(&snapshots).expect("readable snapshots folder") {
        let path = entry.expect("readable directory entry").path();
        let Some(file) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        let Some(name) = file
            .strip_prefix("running__examples__")
            .and_then(|name| name.strip_suffix(".snap"))
        else {
            continue;
        };
        checked += 1;
        if example_snapshot_is_orphaned(name, &examples) {
            orphans.push(file.to_string());
        }
    }
    assert!(
        checked > 0,
        "found no example snapshots in {}",
        snapshots.display()
    );
    orphans.sort();
    assert!(
        orphans.is_empty(),
        "these example snapshots name no example or project (delete them):\n{}",
        orphans.join("\n")
    );
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
    let results = par_map_sessions(
        STACK,
        &all,
        |example| example.name.clone(),
        example_session,
        accepted_example,
    );
    let mut failures = Vec::new();
    for (example, (failed, warnings)) in all.iter().zip(results) {
        failures.extend(failed);
        if let Some(warnings) = warnings {
            insta::assert_snapshot!(snapshot_name(example), warnings);
        }
    }
    assert!(
        failures.is_empty(),
        "these examples should check but don't:\n\n{}",
        failures.join("\n")
    );
}

/// The failures (if any) of one accepted example, rendered, and its rendered
/// warnings if it declares one.
fn accepted_example(session: &mut Session, example: &Example) -> (Vec<String>, Option<String>) {
    let mut failures = Vec::new();
    let expected_metrics = example.expected_metrics();
    if !expected_metrics.is_empty() {
        stitchwort_elab::metrics::start_collecting();
    }
    let loaded = session.load(&example.name, &example.text);
    if !expected_metrics.is_empty() {
        let mut seen = stitchwort_elab::metrics::finish_collecting();
        seen.sort();
        seen.dedup();
        for expected in &expected_metrics {
            if !seen.iter().any(|line| line == expected) {
                failures.push(format!(
                    "{} never reaches `{expected}` (its `-- metrics:` header); seen: {}\n",
                    example.name,
                    if seen.is_empty() {
                        "nothing".to_string()
                    } else {
                        seen.join("; ")
                    }
                ));
            }
        }
    }
    if let Err(diagnostics) = loaded {
        failures.push(format!(
            "{}:\n{}",
            example.name,
            rendered(&session.sources, &diagnostics)
        ));
        return (failures, None);
    }
    let warnings = example.expected_warning().map(|expected| {
        if !session.warnings.iter().any(|d| d.code == expected) {
            failures.push(format!("{} doesn't warn {expected}\n", example.name));
        }
        rendered(&session.sources, &session.warnings)
    });
    // An open goal (`?`) isn't an error, but what has one isn't checked.
    let goals: Vec<Diagnostic> = session
        .warnings
        .iter()
        .filter(|d| d.severity == Severity::Goal)
        .cloned()
        .collect();
    if !goals.is_empty() {
        failures.push(format!(
            "{} has open goals:\n{}",
            example.name,
            rendered(&session.sources, &goals)
        ));
        return (failures, warnings);
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
    (failures, warnings)
}

/// Everything a load reported (errors, warnings and goals), and whether
/// it loaded.
fn reported(session: &mut Session, loaded: Result<(), Vec<Diagnostic>>) -> (bool, Vec<Diagnostic>) {
    match loaded {
        Ok(()) => (true, std::mem::take(&mut session.warnings)),
        Err(diagnostics) => (false, diagnostics),
    }
}

/// A `goals/` example or project, checked: it reports at least one goal;
/// no errors, or some with the code it declares; and its tests pass, except
/// one it declares must fail at an open goal. Gives the rendered goals and
/// errors, to snapshot.
fn assert_goals(
    name: &str,
    expected: Option<&str>,
    expected_test_failure: Option<&str>,
    session: &mut Session,
    loaded: Result<(), Vec<Diagnostic>>,
) -> String {
    let (ok, diagnostics) = reported(session, loaded);
    let output = rendered(&session.sources, &diagnostics);
    let errors: Vec<&Diagnostic> = diagnostics
        .iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    assert!(
        diagnostics.iter().any(|d| d.severity == Severity::Goal),
        "{name} should report an open goal:\n\n{output}"
    );
    match expected {
        None => assert!(
            errors.is_empty(),
            "{name} should report only goals:\n\n{output}"
        ),
        Some(code) => assert!(
            errors.iter().any(|d| d.code == code),
            "{name} should report {code}:\n\n{output}"
        ),
    }
    if ok {
        let results = session.run_tests(&Cache::disabled());
        if let Some(test) = expected_test_failure {
            let result = results
                .iter()
                .find(|result| result.name == test)
                .unwrap_or_else(|| panic!("{name}: no test named \"{test}\" to fail"));
            assert!(
                result.outcome == Outcome::Failed,
                "{name}: test \"{test}\" was expected to fail, but it passed"
            );
            // Not run for a gap, or run and stopped at a `?` (D3777).
            assert!(
                result.unfinished.is_some() || result.stopped.is_some(),
                "{name}: test \"{test}\" failed, but not because it reaches an open goal"
            );
        }
        for result in &results {
            if expected_test_failure == Some(result.name.as_str()) {
                continue;
            }
            assert!(
                result.outcome == Outcome::Passed,
                "{name}: test \"{}\" failed",
                result.name
            );
        }
    }
    assert_no_compiler_names(name, &output);
    output
}

/// No goal or rejection shows a name the compiler made (`%mark`,
/// `half.%step`): source can't write one. There are no deliberate
/// exceptions. A `%` is one where a name follows it directly after a
/// space, bracket or dot; `n % 2` and `n%2` are the modulo operator.
fn assert_no_compiler_names(name: &str, output: &str) {
    let chars: Vec<char> = output.chars().collect();
    for (i, pair) in chars.windows(2).enumerate() {
        let before = i.checked_sub(1).map(|j| chars[j]);
        if pair[0] == '%'
            && pair[1].is_ascii_alphabetic()
            && before.is_some_and(|c| c == ' ' || c == '(' || c == '.')
        {
            let from = i.saturating_sub(40);
            let around: String = chars[from..(i + 40).min(chars.len())].iter().collect();
            panic!("{name}: the output shows a compiler-made name, near `{around}`");
        }
    }
}

#[test]
fn goal_examples_report_their_goals() {
    let all = examples("goals");
    if !filtering() {
        assert!(!all.is_empty());
    }
    par_map_sessions(
        STACK,
        &all,
        |example| example.name.clone(),
        example_session,
        |session, example| {
            let loaded = check(session, example);
            let output = assert_goals(
                &example.name,
                example.expected_error(),
                example.expected_test_failure(),
                session,
                loaded,
            );
            insta::assert_snapshot!(snapshot_name(example), output);
        },
    );
}

#[test]
fn goal_projects_report_their_goals() {
    let all = projects("goals");
    if !filtering() {
        assert!(!all.is_empty());
    }
    par_map_labelled(
        STACK,
        &all,
        |(name, _)| format!("projects/goals/{name}"),
        |(name, path)| {
            let mut session = untimed(Session::for_stack(STACK));
            let loaded = load_project(name, path, &mut session);
            let output = assert_goals(
                &format!("projects/goals/{name}"),
                None,
                None,
                &mut session,
                loaded,
            );
            insta::assert_snapshot!(format!("projects__goals__{name}"), output);
        },
    );
}

#[test]
fn rejected_examples_fail_for_the_expected_reason() {
    par_map_sessions(
        STACK,
        &examples("reject"),
        |example| example.name.clone(),
        example_session,
        |session, example| assert_rejected_with(session, example, true),
    );
}

#[test]
fn soundness_examples_fail_for_the_expected_reason() {
    // Every test evaluation starts is checked to start above its values'
    // variables (SW-4914).
    stitchwort_core::value::check_levels::set(true);
    par_map_sessions(
        STACK,
        &examples("soundness"),
        |example| example.name.clone(),
        example_session,
        |session, example| {
            if example.text.starts_with(KNOWN_GAP) {
                if let Err(diagnostics) = check(session, example) {
                    panic!(
                        "{} is marked `{KNOWN_GAP}` but is now rejected. Remove the marker!\n\n{}",
                        example.name,
                        rendered(&session.sources, &diagnostics)
                    );
                }
            } else {
                assert_rejected(session, example);
            }
        },
    );
}

/// The project folders under `examples/projects/<dir>/`, sorted.
fn projects(dir: &str) -> Vec<(String, PathBuf)> {
    common::check_examples_env(
        &common::all_names(),
        "example file name (or project folder name)",
    );
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects");
    let Ok(entries) = std::fs::read_dir(root.join(dir)) else {
        return Vec::new();
    };
    let mut found: Vec<(String, PathBuf)> = entries
        .map(|entry| entry.expect("readable directory entry").path())
        .filter(|path| path.is_dir())
        // `.stitchwort/` (the cache `stitchwort check` keeps) is not a project.
        .filter(|path| !path.file_name().unwrap().to_string_lossy().starts_with('.'))
        .filter(|path| wanted(&path.file_name().unwrap().to_string_lossy()))
        .map(|path| {
            (
                path.file_name().unwrap().to_string_lossy().to_string(),
                path,
            )
        })
        .collect();
    found.sort();
    share(found)
}

fn load_project(name: &str, path: &Path, session: &mut Session) -> Result<(), Vec<Diagnostic>> {
    let files = DiskFiles {
        root: path.to_path_buf(),
    };
    session
        .load_project(&files, name, &Target::Everything)
        .map(|_| ())
}

/// What's wrong with accepted project `name`: errors, open goals or failed
/// tests.
fn accepted_project_failures(name: &str, path: &Path) -> Vec<String> {
    let mut failures = Vec::new();
    let mut session = untimed(Session::for_stack(STACK));
    if let Err(diagnostics) = load_project(name, path, &mut session) {
        failures.push(format!(
            "{name}:\n{}",
            rendered(&session.sources, &diagnostics)
        ));
        return failures;
    }
    if session
        .warnings
        .iter()
        .any(|d| d.severity == Severity::Goal)
    {
        failures.push(format!(
            "{name} has open goals:\n{}",
            rendered(&session.sources, &session.warnings)
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
}

#[test]
fn accepted_projects_check() {
    let all = projects("accept");
    if !filtering() {
        assert!(!all.is_empty());
    }
    let failures: Vec<String> = par_map_labelled(
        STACK,
        &all,
        |(name, _)| name.clone(),
        |(name, path)| accepted_project_failures(name, path),
    )
    .into_iter()
    .flatten()
    .collect();
    assert!(
        failures.is_empty(),
        "these projects should check but don't:\n\n{}",
        failures.join("\n")
    );
}

/// `trip-journal` in every tier, whatever the sample: its proofs read back
/// `Float` sums of unknowns under binders, which record eta once computed
/// into `Float.Model`'s bit arithmetic, too large to show (SW-1744, D2551).
#[test]
fn the_trip_journal_checks() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept/trip-journal");
    let failures = par_map_labelled(
        STACK,
        &[path],
        |_| "trip-journal".to_string(),
        |path| accepted_project_failures("trip-journal", path),
    )
    .into_iter()
    .flatten()
    .collect::<Vec<_>>();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn rejected_projects_fail_for_the_expected_reason() {
    let all = projects("reject");
    if !filtering() {
        assert!(!all.is_empty());
    }
    par_map_labelled(
        STACK,
        &all,
        |(name, _)| name.clone(),
        |(name, path)| {
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
            let mut session = untimed(Session::for_stack(STACK));
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
        },
    );
}

/// The reject examples whose messages may print an unknown as `?N`: none
/// (SW-3548). An unknown prints as `_name` after its parameter, or `_`, and
/// an unknown a waiting check stands for or waits on is never printed (D2091;
/// docs/proposals/postponement.md, "Stage 4: design for the third attempt",
/// rule 3): the placeholder prints as the source it stands for.
const PRINTS_UNKNOWNS: &[&str] = &[];

/// Whether `text` shows an unknown: a `?` followed by a digit.
fn shows_unknown(text: &str) -> bool {
    text.as_bytes()
        .windows(2)
        .any(|w| w[0] == b'?' && w[1].is_ascii_digit())
}

/// Whether one of `diagnostics` shows an unknown in its words (its
/// message, labels or notes; not the source lines it quotes).
fn prints_unknown(diagnostics: &[Diagnostic]) -> bool {
    diagnostics.iter().any(|d| {
        shows_unknown(&d.message)
            || d.labels.iter().any(|l| shows_unknown(&l.message))
            || d.notes.iter().any(|n| shows_unknown(n))
    })
}

/// A rejected example's messages print an unknown only if it is on
/// [`PRINTS_UNKNOWNS`], and one on it still does.
fn assert_unknowns_allowed(example: &Example, diagnostics: &[Diagnostic], output: &str) {
    let allowed = PRINTS_UNKNOWNS.contains(&example.name.as_str());
    let prints = prints_unknown(diagnostics);
    assert!(
        !prints || allowed,
        "{} prints an unknown (`?N`), which only the files on `PRINTS_UNKNOWNS` may (D2091): \
         a waiting check's placeholder prints as its source, and what reads a waiting check's \
         type waits:\n\n{output}",
        example.name
    );
    assert!(
        prints || !allowed,
        "{} no longer prints an unknown: take it off `PRINTS_UNKNOWNS`\n\n{output}",
        example.name
    );
}

#[test]
fn unknowns_are_found_in_messages() {
    assert!(shows_unknown("expected `?0 n`"));
    assert!(!shows_unknown("`?` is an open goal; `?x` too"));
}

/// SW-1027: `E-NONEXHAUSTIVE` lists the cases a `match` leaves out as arms,
/// and they paste in as they are. For each `reject/missing-cases-*.sw` (the
/// match is the end of the file): its message and `missing` list the same
/// cases, in the order of the constructors; the listed arms appended to the
/// match leave no error, only an open goal for each (and when the list is
/// cut at its cap, the arms of the next round are those it left out).
#[test]
fn listed_missing_arms_paste_in_and_check_as_holes() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/reject");
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|p| {
            let name = p.file_name().unwrap().to_string_lossy();
            name.starts_with("missing-cases-") && name.ends_with(".sw")
        })
        .collect();
    paths.sort();
    assert!(paths.len() >= 5, "the missing-cases examples: {paths:?}");
    let all: Vec<Example> = paths
        .into_iter()
        .map(|path| Example {
            name: format!("reject/{}", path.file_name().unwrap().to_string_lossy()),
            text: std::fs::read_to_string(&path).unwrap(),
        })
        .collect();
    let rounds = par_map_labelled(
        STACK,
        &all,
        |example| example.name.clone(),
        paste_listed_arms,
    );
    // The cap: 23 cases are missing, 20 listed, then the other 3.
    for (example, rounds) in all.iter().zip(rounds) {
        let expected: &[usize] = if example.name.ends_with("-cap.sw") {
            &[20, 3]
        } else {
            &[rounds[0]]
        };
        assert_eq!(rounds, expected, "{}: arms pasted per round", example.name);
    }
}

/// Pastes the arms the checker lists into `example`, round after round,
/// until it checks: how many arms each round listed.
fn paste_listed_arms(example: &Example) -> Vec<usize> {
    let mut text = example.text.trim_end().to_string();
    let indent: String = (text.lines().last().unwrap().chars())
        .take_while(|c| c.is_whitespace())
        .collect();
    let mut rounds = Vec::new();
    for _ in 0..4 {
        let mut session = untimed(Session::for_stack(STACK));
        let diagnostics = match session.load(&example.name, &text) {
            Ok(_) => {
                let goals = (session.warnings.iter())
                    .filter(|d| d.severity == Severity::Goal)
                    .count();
                let pasted: usize = rounds.iter().sum();
                assert_eq!(goals, pasted, "{}: one open goal per arm", example.name);
                // The example's own `Opt` hides Option's constructors.
                let others = (session.warnings.iter())
                    .filter(|d| d.severity != Severity::Goal && d.code != "W-CTOR-HIDES")
                    .count();
                assert_eq!(
                    others,
                    0,
                    "{}: only goals remain:\n{}",
                    example.name,
                    rendered(&session.sources, &session.warnings)
                );
                return rounds;
            }
            Err(diagnostics) => diagnostics,
        };
        let output = rendered(&session.sources, &diagnostics);
        let errors: Vec<_> = (diagnostics.iter())
            .filter(|d| d.severity == Severity::Error)
            .collect();
        let [d] = errors.as_slice() else {
            panic!("{}: one error expected:\n{output}", example.name);
        };
        assert_eq!(d.code, "E-NONEXHAUSTIVE", "{}:\n{output}", example.name);
        let missing = d.missing_data().expect("lists the cases");
        // The message has an arm line for each pattern listed, in order.
        let lines: Vec<&str> = d.message.lines().filter(|l| l.starts_with("| ")).collect();
        let arms: Vec<String> = (missing.shown().iter())
            .map(|p| format!("| {p} => ?"))
            .collect();
        assert_eq!(lines, arms, "{}: the message lists the arms", example.name);
        assert_eq!(
            d.message.lines().last().unwrap().starts_with("and "),
            missing.more() > 0,
            "{}: `and N more` only when cut",
            example.name
        );
        rounds.push(arms.len());
        for arm in arms {
            text.push_str(&format!("\n{indent}{arm}"));
        }
    }
    panic!("{}: still not exhaustive after pasting", example.name);
}

fn assert_rejected(session: &mut Session, example: &Example) {
    assert_rejected_with(session, example, false);
}

/// [`assert_rejected`]; with `names_checked`, the output may not show a
/// compiler-made name ([`assert_no_compiler_names`]). The `reject/` folder
/// is checked; `soundness/` is not yet.
fn assert_rejected_with(session: &mut Session, example: &Example, names_checked: bool) {
    let Some(expected) = example.expected_error() else {
        panic!(
            "{} must declare the error it expects, e.g. `{EXPECT_ERROR} E-POSITIVITY`",
            example.name
        );
    };
    match check(session, example) {
        Ok(()) => panic!("{} should be rejected but checks", example.name),
        Err(diagnostics) => {
            let output = rendered(&session.sources, &diagnostics);
            assert!(
                diagnostics.iter().any(|d| d.code == expected),
                "{} was rejected, but not with {expected}:\n\n{output}",
                example.name
            );
            assert_unknowns_allowed(example, &diagnostics, &output);
            if names_checked {
                assert_no_compiler_names(&example.name, &output);
            }
            insta::assert_snapshot!(snapshot_name(example), output);
        }
    }
}

/// Examples of every kind, some with warnings, tests, open goals, failed
/// declarations and the library files they load, for
/// [`a_rewound_session_reports_what_a_new_one_does`].
const REWIND_SAMPLE: &[&str] = &[
    "accept/abilities.sw",
    "accept/abbreviation-meets-call.sw",
    "accept/arrow-forall-warning.sw",
    "accept/as-written-unconfirmed.sw",
    "accept/facts-long-test.sw",
    "goals/arm-as-written-error.sw",
    "goals/test-hole.sw",
    "reject/attribute-on-test.sw",
    "reject/decidable-not-instance.sw",
    "reject/derive-field-instance-failed.sw",
    "reject/derive-field-instance-deceq.sw",
    "soundness/absurd-without-proof.sw",
    "soundness/alternating-growth.sw",
];

/// Everything checking `example` in `session` reports: whether it loaded,
/// its rendered errors or warnings and goals, and its tests' outcomes. Not
/// its step count: what the memo tables keep about the core across a
/// rewind only saves work, so a rewound session may take a few percent
/// fewer steps.
fn everything_reported(session: &mut Session, example: &Example) -> String {
    let loaded = check(session, example);
    let ok = loaded.is_ok();
    let (_, diagnostics) = reported(session, loaded);
    let mut out = format!(
        "{} loaded {ok}\n{}",
        example.name,
        rendered(&session.sources, &diagnostics)
    );
    if ok {
        let results = session.run_tests(&Cache::disabled());
        for result in session.with_broken_tests(results, |_| true) {
            out.push_str(&format!(
                "test {} {:?} {:?}\n",
                result.name, result.outcome, result.detail
            ));
        }
    }
    out
}

/// The sweeps check each example in a session rewound to just after it was
/// made ([`par_map_sessions`]): that must report exactly what a new session
/// does, whichever examples the session checked before (SW-4624). The
/// sample, forwards and backwards through one session, against a new
/// session each.
#[test]
fn a_rewound_session_reports_what_a_new_one_does() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let sample: Vec<Example> = (REWIND_SAMPLE.iter())
        .map(|name| Example {
            name: name.to_string(),
            text: std::fs::read_to_string(root.join(name)).expect("a sample example"),
        })
        .collect();
    stitchwort_cli::driver::with_stack(STACK, || {
        let fresh: Vec<String> = (sample.iter())
            .map(|example| everything_reported(&mut example_session(STACK), example))
            .collect();
        let mut session = example_session(STACK);
        let mark = session.mark_fresh();
        let mut rewound = |example: &Example| {
            session.rewind_fresh(&mark);
            everything_reported(&mut session, example)
        };
        let forwards: Vec<String> = sample.iter().map(&mut rewound).collect();
        let mut backwards: Vec<String> = sample.iter().rev().map(&mut rewound).collect();
        backwards.reverse();
        for ((new, forwards), backwards) in fresh.iter().zip(&forwards).zip(&backwards) {
            assert_eq!(forwards, new, "checked first to last in one session");
            assert_eq!(backwards, new, "checked last to first in one session");
        }
    });
}
