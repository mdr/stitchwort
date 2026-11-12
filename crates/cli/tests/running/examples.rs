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

use stitchwort_cli::driver::{Cache, Outcome, Session, Tier, par_map, tier, tier_sample};
use stitchwort_cli::project::{DiskFiles, Target};
use stitchwort_cli::render::render;
use stitchwort_syntax::{Diagnostic, Severity, SourceMap};

const KNOWN_GAP: &str = "-- known-gap";
const EXPECT_ERROR: &str = "-- expect-error:";
const EXPECT_WARNING: &str = "-- expect-warning:";
const EXPECT_TEST_FAILURE: &str = "-- expect-test-failure:";

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
/// (`tier_sample`: every one in the daily and full tiers, every fourth in
/// the merge and lane tiers).
fn share<T>(items: Vec<T>) -> Vec<T> {
    if filtering() {
        items
    } else {
        tier_sample(items, 1)
    }
}

/// Rejected examples that run a resource limit out (a value of 10 million
/// nodes) and so peak at 1.3 to 2.4 GB each. A merge-tier sample that picks
/// one or two, on different threads, passed the merge tier's 4 GB cap
/// (SW-2996); they run in the daily and full tiers, and by name.
const HEAVY: &[&str] = &[
    "as-written-unconfirmed-copy.sw",
    "as-written-unconfirmed-slow-check.sw",
    "as-written-unconfirmed-wrong.sw",
    "rewrite-solution-too-large.sw",
    "rewrite-value-too-large.sw",
];

/// Whether this run leaves out the [`HEAVY`] examples: in the merge and lane
/// tiers, unless `EXAMPLES` names some.
fn skips_heavy() -> bool {
    !filtering() && matches!(tier(), Tier::Merge | Tier::Lane)
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
        .filter(|path| {
            !(skips_heavy()
                && HEAVY.contains(&path.file_name().unwrap().to_string_lossy().as_ref()))
        })
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

fn check(example: &Example) -> (SourceMap, Result<(), Vec<Diagnostic>>) {
    let mut session = untimed(Session::new());
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
    let results = par_map(STACK, &all, accepted_example);
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
fn accepted_example(example: &Example) -> (Vec<String>, Option<String>) {
    let mut failures = Vec::new();
    let mut session = untimed(Session::for_stack(STACK));
    if let Err(diagnostics) = session.load(&example.name, &example.text) {
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
            assert!(
                result.unfinished.is_some(),
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
    output
}

#[test]
fn goal_examples_report_their_goals() {
    let all = examples("goals");
    if !filtering() {
        assert!(!all.is_empty());
    }
    par_map(STACK, &all, |example| {
        let mut session = untimed(Session::for_stack(STACK));
        let loaded = session.load(&example.name, &example.text).map(|_| ());
        let output = assert_goals(
            &example.name,
            example.expected_error(),
            example.expected_test_failure(),
            &mut session,
            loaded,
        );
        insta::assert_snapshot!(snapshot_name(example), output);
    });
}

#[test]
fn goal_projects_report_their_goals() {
    let all = projects("goals");
    if !filtering() {
        assert!(!all.is_empty());
    }
    par_map(STACK, &all, |(name, path)| {
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
    });
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
    let failures: Vec<String> = par_map(STACK, &all, |(name, path)| {
        accepted_project_failures(name, path)
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

/// `trip-journal` in every tier, whatever the sample: its proofs read back
/// `Float` sums of unknowns under binders, which record eta once computed
/// into `Float.Model`'s bit arithmetic, too large to show (SW-1744, D2551).
#[test]
fn the_trip_journal_checks() {
    let path =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept/trip-journal");
    let failures = par_map(STACK, &[path], |path| {
        accepted_project_failures("trip-journal", path)
    })
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
    });
}

/// The reject examples whose messages print an unknown (`?N`), the only ones
/// allowed to (D2091; docs/proposals/postponement.md, "Stage 4: design for
/// the third attempt", rule 3). An unknown a waiting check stands for or
/// waits on is never printed: the placeholder prints as the source it
/// stands for, and whatever would print a waiting check's type waits too.
/// Each of these prints an ordinary unknown left unsolved where its error
/// is found (an implicit argument, a hole, a row, a rewrite rule's
/// argument). The design counted 15 on 31 October 2026;
/// `unify-last-arguments-types-differ.sw` (SW-919) came the same day,
/// after it. A file added here needs the same reading first.
const PRINTS_UNKNOWNS: &[&str] = &[
    "reject/case-tree-chains-meta.sw",
    "reject/eqeq-nil-nil.sw",
    "reject/fin-literal-unknown-bound.sw",
    "reject/instance-stuck.sw",
    "reject/instance-unknown-type.sw",
    "reject/lambda-after-expected-instance-nested.sw",
    "reject/lambda-pattern-annotation-shape.sw",
    "reject/match-equation-leaves-solution.sw",
    "reject/match-equation-unknown-motive-unnamed.sw",
    "reject/match-equation-unknown-motive.sw",
    "reject/match-equation-unknown-motive2-unnamed.sw",
    "reject/match-equation-unknown-motive2.sw",
    "reject/not-unfolded-argument.sw",
    "reject/parser-count-differs-from-lemma-with-unknown.sw",
    "reject/pipe-wrong-type.sw",
    "reject/plus-unknown-against-itself.sw",
    "reject/plus-unknown-against-zero.sw",
    "reject/reads-weaken-over-map-implicits.sw",
    "reject/rewrite-inside-function-no-lemma.sw",
    "reject/rewrite-under-binder.sw",
    "reject/row-defaulted.sw",
    "reject/section-minus-is-negation.sw",
    "reject/unify-bool-argument.sw",
    "reject/unify-last-arguments-types-differ.sw",
];

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
    let rounds = par_map(STACK, &all, paste_listed_arms);
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
                assert_eq!(
                    session.warnings.len(),
                    goals,
                    "{}: only goals remain:\n{}",
                    example.name,
                    rendered(&session.sources, &session.warnings)
                );
                return rounds;
            }
            Err(diagnostics) => diagnostics,
        };
        let output = rendered(&session.sources, &diagnostics);
        let [d] = diagnostics.as_slice() else {
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
            assert_unknowns_allowed(example, &diagnostics, &output);
            insta::assert_snapshot!(snapshot_name(example), output);
        }
    }
}
