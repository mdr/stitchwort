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
    assert!(stdout.contains("✗ uses a broken def"), "{stdout}");
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
