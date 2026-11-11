//! `stitchwort goal --at FILE:LINE[:COL]` (SW-2779, docs/proposals/
//! goal-at-any-point.md stage 2), end to end with the built command: the
//! goal at a proof point, the expected type at a program point, no answer,
//! the JSON object, and a file of a project.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

const FILE: &str = "\
import Std (Nat)

def bump (n: Nat): Nat :=
  let m := n + 1
  m + 2

-- a comment
theorem swap (a: Nat) (b: Nat): a + b = b + a :=
  rewrite Nat.addComm a b in rfl
";

/// A fresh folder for one test.
fn folder(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-goal-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs `stitchwort goal ARGS` in `cwd`: (exit code, stdout, stderr).
fn goal(cwd: &Path, args: &[&str]) -> (i32, String, String) {
    let cache = Path::new(env!("CARGO_TARGET_TMPDIR")).join("goal-cache");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("goal")
        .args(args)
        .arg("--cache-dir")
        .arg(&cache)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// A proof point shows `⊢`, a program point `expected`, a comment nothing;
/// a line without a column is its first character; JSON has the same.
#[test]
fn goal_at() {
    let dir = folder("file");
    std::fs::write(dir.join("t.sw"), FILE).unwrap();
    let (code, out, err) = goal(&dir, &["--at", "t.sw:9"]);
    assert_eq!(code, 0, "{out}{err}");
    assert_eq!(out, "t.sw:9:3\n  a: Nat\n  b: Nat\n  ⊢ a + b = b + a\n");
    // Inside the rewrite's body: the goal after the rule.
    let (code, out, _) = goal(&dir, &["--at", "t.sw:9:30"]);
    assert_eq!(code, 0);
    assert!(out.ends_with("  ⊢ b + a = b + a\n"), "{out}");
    let (code, out, err) = goal(&dir, &["--at", "t.sw:5"]);
    assert_eq!(code, 0, "{out}{err}");
    assert_eq!(
        out,
        "t.sw:5:3\n  n: Nat\n  m: Nat := n + 1\n  expected Nat\n"
    );
    let (code, out, err) = goal(&dir, &["--at", "t.sw:7"]);
    assert_eq!(code, 2, "{out}");
    assert!(err.contains("no goal at t.sw:7:1"), "{err}");
    let (code, out, _) = goal(&dir, &["--at", "t.sw:7", "--json"]);
    assert_eq!(code, 2);
    let none: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(none["context"], Value::Null);
    assert_eq!(none["at"]["line"], 7);
    let (code, out, _) = goal(&dir, &["--at", "t.sw:9", "--json"]);
    assert_eq!(code, 0);
    let answer: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(answer["version"], 1);
    assert_eq!(
        answer["at"],
        serde_json::json!({"file": "t.sw", "line": 9, "column": 3})
    );
    let context = &answer["context"];
    assert_eq!(context["kind"], "proof");
    assert_eq!(context["target"], "a + b = b + a");
    assert_eq!(context["checked"], true);
    assert_eq!(
        context["locals"][1],
        serde_json::json!({"name": "b", "type": "Nat"})
    );
    assert_eq!(context["range"]["line"], 9);
    let (_, out, _) = goal(&dir, &["--at", "t.sw:5", "--json"]);
    let answer: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(answer["context"]["kind"], "program");
    assert_eq!(answer["context"]["locals"][1]["value"], "n + 1");
    let _ = std::fs::remove_dir_all(&dir);
}

/// Bad arguments exit 2, a file that doesn't parse 1.
#[test]
fn goal_at_errors() {
    let dir = folder("errors");
    std::fs::write(dir.join("t.sw"), FILE).unwrap();
    std::fs::write(dir.join("bad.sw"), "theorem t (: := \n").unwrap();
    for at in ["t.sw", "t.sw:0", "t.sw:99", "missing.sw:1"] {
        let (code, _, err) = goal(&dir, &["--at", at]);
        assert_eq!(code, 2, "{at}: {err}");
        assert!(err.starts_with("error:"), "{at}: {err}");
    }
    let (code, out, _) = goal(&dir, &["--at", "t.sw:99", "--json"]);
    assert_eq!(code, 2);
    let error: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(error["error"]["code"], "E-GOAL-AT");
    let (code, _, err) = goal(&dir, &["--at", "bad.sw:1"]);
    assert_eq!(code, 1, "{err}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A file of a small project is read in the project, from any folder.
#[test]
fn goal_at_in_a_project() {
    let dir = folder("project").join("tiny");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "# for the goal --at tests\n").unwrap();
    std::fs::write(
        dir.join("src/tiny.sw"),
        "namespace Tiny\n\nimport Std (Nat)\n\n\
         theorem swap (a: Nat) (b: Nat): a + b = b + a :=\n  rewrite Nat.addComm a b in rfl\n",
    )
    .unwrap();
    let (code, out, err) = goal(dir.parent().unwrap(), &["--at", "tiny/src/tiny.sw:6"]);
    assert_eq!(code, 0, "{out}{err}");
    assert!(
        out.ends_with("  a: Nat\n  b: Nat\n  ⊢ a + b = b + a\n"),
        "{out}"
    );
    let (code, out, _) = goal(&dir, &["--at", "src/tiny.sw:1"]);
    assert_eq!(code, 2, "{out}");
    let _ = std::fs::remove_dir_all(dir.parent().unwrap());
}
