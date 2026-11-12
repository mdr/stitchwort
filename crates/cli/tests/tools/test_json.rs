//! `stitchwort test --json` and `--only`, which the editor's run icons and
//! Testing panel use (SW-1121): one JSON object, a result per test with
//! where it is declared, and the same exit status as the text output.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

const SOURCE: &str = r#"def part1 (n: Nat): Nat := n + 1

test "passes" := part1 1 == 2
test "bad one" := part1 1 == 3
test "second part" := 1 < 2 && part1 1 == 5
"#;

fn folder(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-json-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("t.sw"), SOURCE).unwrap();
    dir
}

/// Standard output (parsed as JSON if it is), standard error, and success.
fn run(dir: &Path, args: &[&str]) -> (String, String, bool) {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("test")
        .arg("t.sw")
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
        output.status.success(),
    )
}

fn json(dir: &Path, args: &[&str]) -> (Value, bool) {
    let (out, _, ok) = run(dir, args);
    (serde_json::from_str(&out).expect(&out), ok)
}

#[test]
fn json_has_a_result_per_test_with_its_place() {
    let dir = folder("all");
    let (v, ok) = json(&dir, &["--json", "--no-cache"]);
    assert!(!ok);
    assert_eq!(v["ok"], false);
    let tests = v["tests"].as_array().unwrap();
    let outcomes: Vec<_> = tests
        .iter()
        .map(|t| {
            (
                t["name"].as_str().unwrap(),
                t["outcome"].as_str().unwrap(),
                t["line"].as_u64().unwrap(),
            )
        })
        .collect();
    assert_eq!(
        outcomes,
        [
            ("passes", "passed", 3),
            ("bad one", "failed", 4),
            ("second part", "failed", 5)
        ]
    );
    assert_eq!(tests[1]["file"], "t.sw");
    assert_eq!(tests[1]["column"], 1);
    assert_eq!(tests[1]["message"], "`==` is False");
    assert_eq!(tests[1]["failure"]["comparison"]["left"], "2");
    assert_eq!(tests[1]["failure"]["comparison"]["right"], "3");
    // The false part of an `&&`, where it is.
    assert_eq!(tests[2]["failure"]["part"]["text"], "part1 1 == 5");
    assert_eq!(tests[2]["failure"]["part"]["line"], 5);
    assert_eq!(tests[0]["message"], Value::Null);
}

#[test]
fn only_runs_the_one_test_named() {
    let dir = folder("only");
    let (v, ok) = json(&dir, &["--json", "--only", "bad one"]);
    assert!(!ok);
    let tests = v["tests"].as_array().unwrap();
    assert_eq!(tests.len(), 1);
    assert_eq!(tests[0]["name"], "bad one");

    let (v, ok) = json(&dir, &["--json", "--only", "passes"]);
    assert!(ok);
    assert_eq!(v["ok"], true);
    assert_eq!(v["tests"].as_array().unwrap().len(), 1);
}

#[test]
fn json_says_when_a_result_came_from_the_cache() {
    let dir = folder("cached");
    let (first, _) = json(&dir, &["--json"]);
    assert_eq!(first["tests"][0]["cached"], false);
    let (second, _) = json(&dir, &["--json"]);
    assert_eq!(second["tests"][0]["cached"], true);
    assert_eq!(second["tests"][1]["cached"], true);
    assert_eq!(second["tests"][1]["failure"]["comparison"]["right"], "3");
}

#[test]
fn only_with_no_such_test_fails_and_says_so() {
    let dir = folder("none");
    let (out, err, ok) = run(&dir, &["--only", "nope"]);
    assert!(!ok);
    assert!(err.contains("no test is called 'nope'"), "{err}");
    assert!(out.contains("0 test(s)"), "{out}");
    let (v, ok) = json(&dir, &["--json", "--only", "nope"]);
    assert!(!ok);
    assert_eq!(v["ok"], false);
    assert_eq!(v["tests"].as_array().unwrap().len(), 0);
}

#[test]
fn only_leaves_the_text_output_as_it_was() {
    let dir = folder("text");
    let (all, _, _) = run(&dir, &["--no-cache"]);
    let (one, _, _) = run(&dir, &["--no-cache", "--only", "bad one"]);
    assert!(all.contains("✓ passes"), "{all}");
    assert!(one.contains("✗ bad one"), "{one}");
    assert!(!one.contains("passes"), "{one}");
    assert!(one.contains("1 test(s): 0 passed, 1 failed"), "{one}");
}

/// A declaration with an error (`broken`, which doesn't type check) and a
/// theorem `rfl` can't prove, with tests that don't touch them, one that
/// uses `broken`, and one that uses `twice`, which uses it (D3523).
const WITH_ERRORS: &str = r#"namespace Demo

def good (n: Nat): Nat := n + 1

def broken (n: Nat): Nat := "oops"

def twice (n: Nat): Nat := broken n + broken n

theorem wrongSum: good 1 = 3 := rfl

test "independent passes" := good 1 == 2
test "independent fails" := good 1 == 3
test "uses a broken def" := broken 1 == 2
test "uses it indirectly" := twice 1 == 4
"#;

fn project_with_errors(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-json-errors-{}-{name}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/a.sw"), WITH_ERRORS).unwrap();
    dir
}

#[test]
fn tests_that_dont_use_a_declaration_with_an_error_still_run() {
    let dir = project_with_errors("json");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["test", "--json", "--no-cache"])
        .current_dir(&dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    // The errors are still reported, and the run fails.
    assert!(!output.status.success(), "{stdout}{stderr}");
    assert!(
        stderr.contains("`wrongSum`") || stderr.contains("rfl"),
        "{stderr}"
    );
    let v: Value = serde_json::from_str(&stdout).expect(&stdout);
    assert_eq!(v["ok"], false);
    let tests: Vec<(&str, &str, Option<&str>, Option<u64>)> = v["tests"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| {
            (
                t["name"].as_str().unwrap(),
                t["outcome"].as_str().unwrap(),
                t["message"].as_str(),
                t["line"].as_u64(),
            )
        })
        .collect();
    let (passes, fails, direct, indirect) = (tests[0], tests[1], tests[2], tests[3]);
    assert_eq!(tests.len(), 4, "{tests:?}");
    assert_eq!((passes.0, passes.1), ("independent passes", "passed"));
    assert_eq!((fails.0, fails.1), ("independent fails", "failed"));
    assert_eq!(fails.2, Some("`==` is False"));
    assert_eq!((direct.0, direct.1), ("uses a broken def", "failed"));
    let message = direct.2.unwrap();
    assert!(
        message.starts_with("it uses `broken`, which has an error (")
            && message.ends_with("src/a.sw:5:29)"),
        "{message}"
    );
    assert_eq!((indirect.0, indirect.1), ("uses it indirectly", "failed"));
    let message = indirect.2.unwrap();
    assert!(
        message.starts_with("it uses `twice`, which depends on `broken`, which has an error (")
            && message.ends_with("src/a.sw:5:29)"),
        "{message}"
    );
    // Where each test is, the broken ones too.
    assert_eq!(
        tests.iter().map(|t| t.3).collect::<Vec<_>>(),
        [Some(11), Some(12), Some(13), Some(14)]
    );
}

#[test]
fn a_run_with_an_error_prints_the_tests_and_fails() {
    let dir = project_with_errors("text");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["test", "--no-cache"])
        .current_dir(&dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(output.status.code(), Some(1), "{stdout}");
    assert!(stdout.contains("✓ independent passes"), "{stdout}");
    assert!(
        stdout.contains("✗ uses a broken def   not run  (it uses `broken`, which has an error ("),
        "{stdout}"
    );
    assert!(
        stdout.contains(
            "✗ uses it indirectly  not run  (it uses `twice`, which depends on `broken`, \
             which has an error ("
        ),
        "{stdout}"
    );
    assert!(stdout.contains("4 test(s): 1 passed, 3 failed"), "{stdout}");
}

#[test]
fn a_file_with_an_error_still_runs_the_tests_that_dont_use_it() {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-json-errors-{}-file",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("t.sw"),
        WITH_ERRORS.replace("namespace Demo\n\n", ""),
    )
    .unwrap();
    let (v, ok) = json(&dir, &["--json", "--no-cache"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert_eq!(v["ok"], false);
    let outcomes: Vec<_> = v["tests"]
        .as_array()
        .unwrap()
        .iter()
        .map(|t| t["outcome"].as_str().unwrap())
        .collect();
    assert_eq!(outcomes, ["passed", "failed", "failed", "failed"]);
}

const LIB_WITH_AN_ERROR: &str = r#"namespace A

def double (n: Nat): Nat := n + n

def broken (n: Nat): Nat := "oops"

test "double works" := double 2 == 4
"#;

const IMPORTER: &str = r#"namespace B

import A (double, broken)

def quad (n: Nat): Nat := double (double n)

def quadBroken (n: Nat): Nat := broken (double n)

def again (n: Nat): Nat := broken n + broken n

theorem quadOne: quad 1 = 4 := rfl

theorem brokenOne: broken 1 = 1 := rfl

test "quad works" := quad 1 == 4
test "quad of broken" := quadBroken 1 == 4
"#;

/// `A` has a syntax error in `beats`' header, so that declaration is lost
/// (SW-2945).
const LIB_WITH_A_SYNTAX_ERROR: &str = r#"namespace A

def double (n: Nat): Nat := n + n

def [beats] (n: Nat): Nat := n
"#;

const SYNTAX_IMPORTER: &str = r#"namespace B

import A (beats)

def use (n: Nat): Nat := beats n

def good (n: Nat): Nat := n + 1

test "good works" := good 1 == 2
"#;

/// A declaration whose error is late in its body, so its name is not where
/// the error is reported (SW-2944).
const LIB_WITH_A_LATE_TYPE_ERROR: &str = r#"namespace A

def bad (n: Nat): Nat := n + True
"#;

/// The same for a syntax error after the declaration's name.
const LIB_WITH_A_LATE_SYNTAX_ERROR: &str = r#"namespace A

def bad (n: Nat): Nat := n +
"#;

const ONE_IMPORTER: &str = r#"namespace B

import A (bad)

def use (n: Nat): Nat := bad n

theorem useOne: bad 1 = 1 := rfl
"#;

/// A project whose namespace `B` imports a healthy and a broken name from
/// `A`, with `A`'s text `lib`.
fn importer_project(name: &str, lib: &str) -> PathBuf {
    source_project(name, lib, IMPORTER)
}

/// A project of two files, `A`'s text and `B`'s.
fn source_project(name: &str, a: &str, b: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-json-importer-{}-{name}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/a.sw"), a).unwrap();
    std::fs::write(dir.join("src/b.sw"), b).unwrap();
    dir
}

/// The places (`line`, `column`) in `stderr`'s excerpts that name `file`, in
/// the order they're printed.
fn excerpt_positions(stderr: &str, file: &str) -> Vec<(usize, usize)> {
    stderr
        .lines()
        .filter_map(|line| {
            let rest = line
                .trim_start()
                .strip_prefix("╭─[ ")
                .or_else(|| line.trim_start().strip_prefix("├─[ "))?;
            let place = rest.split(" ]").next()?;
            let (name, rest) = place.rsplit_once(':')?;
            let (name, line) = name.rsplit_once(':')?;
            if !name.ends_with(file) {
                return None;
            }
            Some((line.parse().ok()?, rest.parse().ok()?))
        })
        .collect()
}

/// A test's (namespace, name, outcome, message).
type Row = (String, String, String, String);

/// `test --json` in `dir` with `args`: the tests, standard error, and
/// success.
fn project_tests(dir: &Path, args: &[&str]) -> (Vec<Row>, String, bool) {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["test", "--json"])
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let stdout = String::from_utf8(output.stdout).unwrap();
    let stderr = String::from_utf8(output.stderr).unwrap();
    let v: Value = serde_json::from_str(&stdout).expect(&stdout);
    assert_eq!(v["ok"], output.status.success());
    let tests = (v["tests"].as_array().unwrap().iter())
        .map(|t| {
            let text = |k: &str| t[k].as_str().unwrap_or_default().to_string();
            (
                text("namespace"),
                text("name"),
                text("outcome"),
                text("message"),
            )
        })
        .collect();
    (tests, stderr, output.status.success())
}

#[test]
fn an_importer_of_a_namespace_with_an_error_is_checked_and_its_tests_run() {
    let dir = importer_project("checked", LIB_WITH_AN_ERROR);
    let (tests, stderr, ok) = project_tests(&dir, &["--no-cache"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok, "{stderr}");
    let outcomes: Vec<(&str, &str, &str)> = (tests.iter())
        .map(|(ns, name, outcome, _)| (ns.as_str(), name.as_str(), outcome.as_str()))
        .collect();
    assert_eq!(
        outcomes,
        [
            ("A", "double works", "passed"),
            ("B", "quad works", "passed"),
            ("B", "quad of broken", "failed"),
        ]
    );
    let message = &tests[2].3;
    assert!(
        message
            .starts_with("it uses `quadBroken`, which depends on `broken`, which has an error (")
            && message.ends_with("src/a.sw:5:29)"),
        "{message}"
    );
    // `broken` is reported where it is. Its statement stands in for it
    // (D3527), so the two declarations and the test that only call it are
    // checked against that, and rely on it; the theorem that must compute
    // `broken 1` waits, said once in `b.sw`, on the import.
    assert_eq!(stderr.matches("[E-TYPE-MISMATCH]").count(), 1, "{stderr}");
    assert_eq!(stderr.matches("[E-USES-FAILED]").count(), 1, "{stderr}");
    assert!(
        stderr.contains("`broken` has an error, so `brokenOne` can't be checked until it's fixed"),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "3 declarations rely on a declaration with an error, checked assuming its statement"
        ),
        "{stderr}"
    );
    assert!(stderr.contains("B.brokenOne  needs `broken` ("), "{stderr}");
    assert!(stderr.contains("b.sw:3:19"), "{stderr}");
    assert!(!stderr.contains("E-NAMESPACE-FAILED"), "{stderr}");
    assert!(!stderr.contains("E-FAILED-DEPENDENCY"), "{stderr}");
}

/// SW-2945: `A`'s syntax error loses `beats`, so `B`'s import of it says why
/// once, on the import, rather than `beats` being unknown where it is used
/// (docs/proposals/tests-with-errors.md §4.2). The rest of `B` is checked.
#[test]
fn an_import_of_a_name_lost_to_a_syntax_error_says_so_once() {
    let dir = source_project("syntax", LIB_WITH_A_SYNTAX_ERROR, SYNTAX_IMPORTER);
    let (tests, stderr, ok) = project_tests(&dir, &["--no-cache"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok, "{stderr}");
    assert_eq!(stderr.matches("[E-PARSE]").count(), 1, "{stderr}");
    assert_eq!(stderr.matches("[E-USES-FAILED]").count(), 1, "{stderr}");
    assert!(
        stderr.contains("`A` has a syntax error, so `beats` can't be found"),
        "{stderr}"
    );
    // On the import, and at `A`'s syntax error.
    assert!(stderr.contains("b.sw:3:11"), "{stderr}");
    assert!(stderr.contains("a.sw:5:5"), "{stderr}");
    assert!(!stderr.contains("E-UNKNOWN-NAME"), "{stderr}");
    assert!(!stderr.contains("E-IMPORT-UNKNOWN"), "{stderr}");
    // The declaration that uses `beats` waits; `B`'s other declaration and
    // its test are checked and run.
    let outcomes: Vec<(&str, &str, &str)> = (tests.iter())
        .map(|(ns, name, outcome, _)| (ns.as_str(), name.as_str(), outcome.as_str()))
        .collect();
    assert_eq!(outcomes, [("B", "good works", "passed")]);
}

/// SW-2944: the import's "the error is here" label is exactly where the
/// failed declaration's first error is reported, not at the declaration's
/// name. Covers a type error late in the body and a syntax error there.
#[test]
fn the_imports_error_label_is_where_the_error_is_reported() {
    let cases = [
        ("late-type", LIB_WITH_A_LATE_TYPE_ERROR, "[E-TYPE-MISMATCH]"),
        ("late-syntax", LIB_WITH_A_LATE_SYNTAX_ERROR, "[E-PARSE]"),
    ];
    for (name, lib, code) in cases {
        let dir = source_project(name, lib, ONE_IMPORTER);
        let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .arg("check")
            .current_dir(&dir)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort");
        let _ = std::fs::remove_dir_all(&dir);
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(!output.status.success(), "{stderr}");
        assert_eq!(stderr.matches(code).count(), 1, "{stderr}");
        assert_eq!(stderr.matches("[E-USES-FAILED]").count(), 1, "{stderr}");
        // `A`'s own error, and the label under it.
        let positions = excerpt_positions(&stderr, "a.sw");
        assert_eq!(positions.len(), 2, "{stderr}");
        assert_eq!(positions[0], positions[1], "{stderr}");
    }
}

/// The check cache never serves an importer as it was before the namespace
/// it imports broke or was fixed: the importer's key covers what it
/// imports, and a namespace with errors is never stored.
#[test]
fn an_importer_follows_its_dependency_through_the_cache() {
    let dir = importer_project("cache", LIB_WITH_AN_ERROR);
    let cache = dir.join("cache");
    let cache = cache.to_str().unwrap();
    let args = ["--cache-dir", cache];
    let without = |tests: Vec<Row>| -> Vec<(String, String, String)> {
        tests
            .into_iter()
            .map(|(_, name, o, m)| (name, o, m))
            .collect()
    };
    let (first, first_err, ok) = project_tests(&dir, &args);
    assert!(!ok);
    let (second, second_err, ok) = project_tests(&dir, &args);
    assert!(!ok);
    assert_eq!(without(first.clone()), without(second));
    assert_eq!(first_err, second_err);
    // Fixed: `B` has no error, and its test runs on its merits.
    std::fs::write(
        dir.join("src/a.sw"),
        LIB_WITH_AN_ERROR.replace("\"oops\"", "n"),
    )
    .unwrap();
    for _ in 0..2 {
        let (fixed, stderr, ok) = project_tests(&dir, &args);
        assert!(!ok, "a test fails");
        assert!(!stderr.contains("[E-"), "{stderr}");
        assert_eq!(fixed[2].1, "quad of broken");
        assert_eq!(fixed[2].3, "`==` is False");
    }
    // Broken again: not the fixed answer from the cache.
    std::fs::write(dir.join("src/a.sw"), LIB_WITH_AN_ERROR).unwrap();
    let (broken, stderr, ok) = project_tests(&dir, &args);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(!ok);
    assert_eq!(stderr.matches("[E-USES-FAILED]").count(), 1, "{stderr}");
    assert_eq!(without(broken), without(first));
}

/// Stand-ins (docs/proposals/tests-with-errors.md §3.3, D3527, D3525):
/// `doubleTwo`'s statement checks but its proof doesn't, so it stands in for
/// its statement; `badSig`'s statement doesn't check, so what uses it
/// waits.
const STAND_INS: &str = r#"namespace A

def double (n: Nat): Nat := n + n

def broken (n: Nat): Nat := "oops"

theorem doubleTwo: double 2 = 5 := rfl

theorem usesTwo: double 2 + 0 = 5 := doubleTwo

theorem ownMistake: double 3 = 5 := doubleTwo

theorem needsBody: broken 0 = 0 := rfl

def badSig (n: Nat): Missing := n

def callsBadSig (n: Nat): Nat := badSig n

def check2 (h: double 2 = 5): Bool := double 1 == 2

test "cites doubleTwo" := check2 doubleTwo
test "calls broken" := broken 1 == 1
test "calls callsBadSig" := callsBadSig 1 == 1
"#;

/// `stitchwort check` and `stitchwort test`, both `--no-cache`, on
/// [`STAND_INS`] as a project: (check's stderr, check's success, test's
/// JSON, test's text stdout, test's success).
fn stand_ins(name: &str) -> (String, bool, Value, String, bool) {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-json-stand-ins-{}-{name}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/a.sw"), STAND_INS).unwrap();
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(args)
            .current_dir(&dir)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort")
    };
    let check = run(&["check", "--no-cache"]);
    let json = run(&["test", "--json", "--no-cache"]);
    let text = run(&["test", "--no-cache"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8(json.stdout).unwrap();
    assert_eq!(json.status.success(), text.status.success());
    (
        String::from_utf8(check.stderr).unwrap(),
        check.status.success(),
        serde_json::from_str(&stdout).expect(&stdout),
        String::from_utf8(text.stdout).unwrap(),
        text.status.success(),
    )
}

/// A theorem that cites one whose proof has an error is checked against its
/// statement: its own mistakes are reported now, and it is counted as
/// relying on the broken theorem, never as checked. One that must compute
/// through a broken definition waits, and so does what uses a declaration
/// whose statement is broken. `check` still fails.
#[test]
fn a_theorem_with_a_broken_proof_stands_in_for_its_statement() {
    let (stderr, ok, _, _, _) = stand_ins("check");
    assert!(!ok, "{stderr}");
    // The three errors of their own, `ownMistake`'s found only because
    // `doubleTwo` stands in for its statement.
    assert_eq!(stderr.matches("[E-TYPE-MISMATCH]").count(), 2, "{stderr}");
    assert_eq!(stderr.matches("[E-REFL]").count(), 1, "{stderr}");
    assert!(stderr.contains("[E-UNKNOWN-NAME]"), "{stderr}");
    assert!(stderr.contains("double 3 = 5"), "{stderr}");
    assert!(!stderr.contains("E-FAILED-DEPENDENCY"), "{stderr}");
    // `usesTwo` and the test that cites `doubleTwo` rely on it; the test
    // that calls `broken` relies on `broken`.
    assert!(
        stderr.contains(
            "3 declarations rely on a declaration with an error, checked assuming its statement"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("1 declaration can't be checked until an error is fixed:"),
        "{stderr}"
    );
    assert!(stderr.contains("A.needsBody  needs `broken` ("), "{stderr}");
    // Not counted as goals.
    assert!(!stderr.contains("goal"), "{stderr}");
}

/// D3525: a test that only cites a broken theorem as a proof runs and says
/// what it assumed; one whose code calls a broken definition fails without
/// running; one that uses a declaration whose statement is broken fails
/// without running. The run fails while any error stands.
#[test]
fn a_test_that_only_cites_a_broken_theorem_runs() {
    let (_, _, v, stdout, ok) = stand_ins("test");
    assert!(!ok, "{stdout}");
    assert_eq!(v["ok"], false);
    let tests = v["tests"].as_array().unwrap();
    let row = |i: usize| {
        (
            tests[i]["name"].as_str().unwrap(),
            tests[i]["outcome"].as_str().unwrap(),
            tests[i]["message"].as_str().unwrap_or_default(),
        )
    };
    assert_eq!(tests.len(), 3, "{v}");
    assert_eq!(row(0), ("cites doubleTwo", "passed", ""));
    let assuming = tests[0]["assuming"].as_array().unwrap();
    assert_eq!(assuming.len(), 1, "{v}");
    assert_eq!(assuming[0]["name"], "doubleTwo");
    assert_eq!(assuming[0]["kind"], "error");
    assert_eq!(assuming[0]["line"], 7);
    assert!(
        stdout.contains("✓ cites doubleTwo    ran  (assuming `doubleTwo`, which has an error ("),
        "{stdout}"
    );
    let (name, outcome, message) = row(1);
    assert_eq!((name, outcome), ("calls broken", "failed"));
    assert!(
        message.starts_with("it uses `broken`, which has an error (")
            && message.ends_with("src/a.sw:5:29)"),
        "{message}"
    );
    let (name, outcome, message) = row(2);
    assert_eq!((name, outcome), ("calls callsBadSig", "failed"));
    assert!(
        message.starts_with("it uses `callsBadSig`, which depends on `badSig`, which has an error"),
        "{message}"
    );
}
