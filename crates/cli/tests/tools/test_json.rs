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
