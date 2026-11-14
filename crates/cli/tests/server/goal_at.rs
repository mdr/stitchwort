//! `stitchwort goal --at FILE:LINE[:COL]` (SW-2779, docs/proposals/
//! goal-at-any-point.md stages 2 and 3), end to end with the built command:
//! the goal at a proof point, the steps of a proof (SW-2780), the expected
//! type at a program point, no answer,
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
    assert_eq!(
        out,
        "t.sw:9:3\nin `swap`, rule 1 of 1 of `rewrite`\n  a: Nat\n  b: Nat\n  before ⊢ a + b = b + a\n  rule   a + b = b + a\n  after  ⊢ b + a = b + a\n"
    );
    // Inside the rewrite's body: the goal after the rule.
    let (code, out, _) = goal(&dir, &["--at", "t.sw:9:30"]);
    assert_eq!(code, 0);
    assert!(out.ends_with("  ⊢ b + a = b + a\n"), "{out}");
    let (code, out, err) = goal(&dir, &["--at", "t.sw:5"]);
    assert_eq!(code, 0, "{out}{err}");
    assert_eq!(
        out,
        "t.sw:5:3\nin `bump`\n  n: Nat\n  m: Nat := n + 1\n  has type Nat\n"
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
    assert_eq!(answer["version"], 2);
    assert_eq!(answer["context"]["targetComputed"], Value::Null);
    assert_eq!(
        answer["at"],
        serde_json::json!({"file": "t.sw", "line": 9, "column": 3})
    );
    let context = &answer["context"];
    assert_eq!(context["kind"], "proof");
    assert_eq!(context["target"], "b + a = b + a");
    assert_eq!(context["checked"], true);
    assert_eq!(
        context["locals"][1],
        serde_json::json!({"name": "b", "type": "Nat"})
    );
    assert_eq!(context["range"]["line"], 9);
    assert_eq!(answer["declaration"], "swap");
    // Line 9 starts at `rewrite`, whose keyword shows its rule's step (SW-2930).
    assert_ne!(context["step"], Value::Null);
    let (_, out, _) = goal(&dir, &["--at", "t.sw:5", "--json"]);
    let answer: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(answer["context"]["kind"], "program");
    assert_eq!(answer["context"]["locals"][1]["value"], "n + 1");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A goal is printed as written, and under it what it computes to when that
/// prints differently (D3522), in the text and as `targetComputed`.
#[test]
fn goal_at_prints_as_written_then_computes_to() {
    let dir = folder("computes");
    let file = "\
import Std (Nat)

def double: Nat → Nat
  | 0 => 0
  | Succ k => Succ (Succ (double k))

theorem dbl (n: Nat): double (Succ n) = Succ (Succ (double n)) := ?
";
    std::fs::write(dir.join("c.sw"), file).unwrap();
    let (code, out, err) = goal(&dir, &["--at", "c.sw:7:65"]);
    assert_eq!(code, 0, "{out}{err}");
    assert_eq!(
        out,
        "c.sw:7:65\nin `dbl`, the statement\n  n: Nat\n  ⊢ double (Succ n) = Succ (Succ (double n))\n  \
         computes to Succ (Succ (double n)) = Succ (Succ (double n))\n"
    );
    let (_, out, _) = goal(&dir, &["--at", "c.sw:7:65", "--json"]);
    let answer: Value = serde_json::from_str(&out).unwrap();
    let context = &answer["context"];
    assert_eq!(
        context["target"],
        "double (Succ n) = Succ (Succ (double n))"
    );
    assert_eq!(
        context["targetComputed"],
        "Succ (Succ (double n)) = Succ (Succ (double n))"
    );
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
        out.ends_with(
            "  before ⊢ a + b = b + a\n  rule   a + b = b + a\n  after  ⊢ b + a = b + a\n"
        ),
        "{out}"
    );
    let (code, out, _) = goal(&dir, &["--at", "src/tiny.sw:1"]);
    assert_eq!(code, 2, "{out}");
    let _ = std::fs::remove_dir_all(dir.parent().unwrap());
}

const STEPS: &str = "\
import Std (Nat)

theorem multN0M0 (p q: Nat): p * 0 + q * 0 = 0 :=
  rewrite Nat.mulZero p, Nat.mulZero q in rfl

theorem addZeroLeft (n: Nat): 0 + n = n :=
  match n with
    | Zero => rfl
    | Succ k => rfl

theorem chain (a b c: Nat) (h1: a = b) (h2: b = c): a = c :=
  calc a
    _ = b := h1
    _ = c := h2

theorem swap (p q: Prop): p ∧ q → q ∧ p :=
  pq =>
    let left := And.left pq
    Both (And.right pq) left

def pick (b: Bool) (n: Nat): Nat :=
  if h: b then n else 0

theorem atH (a b c: Nat) (h1: a = b) (h2: b = c): a = c :=
  rewrite h2 at h1 in h1

theorem broken (n: Nat): n + 1 = Succ n :=
  Nat.nope n

def widen (n: Nat): Int := n

theorem addZero (n: Nat): n + 0 = n := rfl

theorem middle (a b: Nat) (h1: a = b) (h2: b = 2): a = 2 :=
  calc a
    _ = b := h1
    _ = 1 + 1 := h2
    _ = 2
";

/// `goal --at` at `at` in [`STEPS`], as text, less its first line (the
/// point).
fn step_at(dir: &Path, at: &str) -> String {
    let (code, out, err) = goal(dir, &["--at", &format!("s.sw:{at}")]);
    assert_eq!(code, 0, "{at}: {out}{err}");
    out.split_once('\n').unwrap().1.to_string()
}

/// Each form of step (docs/proposals/goal-at-any-point.md §3.1): the goal
/// before it, what it adds, and the goal after it.
#[test]
fn goal_at_steps() {
    let dir = folder("steps");
    std::fs::write(dir.join("s.sw"), STEPS).unwrap();
    // Each rule of a chain: the goal it rewrote, the rule as used, the goal
    // it left.
    assert_eq!(
        step_at(&dir, "4:26"),
        "in `multN0M0`, rule 2 of 2 of `rewrite`\n  p: Nat\n  q: Nat\n  \
         before ⊢ q * 0 = 0\n  rule   q * 0 = 0\n  after  ⊢ 0 = 0\n"
    );
    // An arm's pattern: the `match`'s goal, the pattern's variables, the
    // arm's goal.
    assert_eq!(
        step_at(&dir, "9:7"),
        "in `addZeroLeft`, arm 2 of 2, `| Succ k`\n  + k: Nat\n  \
         before ⊢ n = n\n  after  ⊢ Succ k = Succ k\n"
    );
    assert!(
        step_at(&dir, "7:3").starts_with("in `addZeroLeft`, `match` with 2 arms\n"),
        "on `match`"
    );
    // A calc line: what the lines before prove, and the line's statement.
    assert_eq!(
        step_at(&dir, "14:5"),
        "in `chain`, line 2 of 2 of `calc`, `_ = c`\n  a: Nat\n  b: Nat\n  c: Nat\n  \
         h1: a = b\n  h2: b = c\n  so far a = b\n  line   ⊢ b = c\n"
    );
    // In the line's proof, the expression's own goal.
    assert!(step_at(&dir, "13:14").starts_with("in `chain`\n"));
    assert!(
        step_at(&dir, "17:3")
            .ends_with("  + pq: p ∧ q\n  before ⊢ p ∧ q → q ∧ p\n  after  ⊢ q ∧ p\n"),
        "a lambda's parameter"
    );
    assert!(
        step_at(&dir, "18:9").contains("in `swap`, `let left`\n")
            && step_at(&dir, "18:9").contains("  + left: p := pq.left\n"),
        "a `let`"
    );
    assert!(
        step_at(&dir, "22:20")
            .starts_with("in `pick`, `else` of `if`\n  b: Bool\n  n: Nat\n  + h: ¬b\n")
    );
    // `rewrite … at h` rewrites `h`'s type.
    assert!(
        step_at(&dir, "25:11")
            .ends_with("  before h1: a = b\n  rule   b = c\n  after  h1: a = c\n"),
        "at h"
    );
    // In a signature: the statement, with the parameters in scope.
    assert_eq!(
        step_at(&dir, "6:10"),
        "in `addZeroLeft`, the statement\n  n: Nat\n  ⊢ n = n\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A `calc` line with a `:=` shows its own statement, not the chain's end:
/// the previous value is computed (`_` stands for it) but the line's own
/// right side stays as written, even when it computes to something else
/// (SW-2942).
#[test]
fn goal_at_calc_middle_line() {
    let dir = folder("calc-middle");
    std::fs::write(dir.join("s.sw"), STEPS).unwrap();
    assert_eq!(
        step_at(&dir, "37:5"),
        "in `middle`, line 2 of 3 of `calc`, `_ = 1 + 1`\n  a: Nat\n  b: Nat\n  \
         h1: a = b\n  h2: b = 2\n  so far a = b\n  line   ⊢ b = 1 + 1\n         computes to b = 2\n"
    );
    // The last line still computes the previous value: `1 + 1` is `2`.
    assert_eq!(
        step_at(&dir, "38:5"),
        "in `middle`, line 3 of 3 of `calc`, `_ = 2`\n  a: Nat\n  b: Nat\n  \
         h1: a = b\n  h2: b = 2\n  so far a = 2\n  line   ⊢ 2 = 2\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A failing expression has the goal it was checked against; a program
/// point whose type differs from the one expected shows both (D3499);
/// `rfl` shows its goal as a `?` there would.
#[test]
fn goal_at_failing_and_has_type() {
    let dir = folder("failing");
    std::fs::write(dir.join("s.sw"), STEPS).unwrap();
    assert_eq!(
        step_at(&dir, "28:3"),
        "in `broken`\n  n: Nat\n  ⊢ n + 1 = Succ n\n"
    );
    assert_eq!(
        step_at(&dir, "30:28"),
        "in `widen`\n  n: Nat\n  expected Int\n  has type Nat\n"
    );
    // `n + 0` computes as it is elaborated, so the goal reads `n = n`, as
    // `?` in place of `rfl` reads it (SW-2791).
    assert_eq!(
        step_at(&dir, "32:41"),
        "in `addZero`\n  n: Nat\n  ⊢ n = n\n"
    );
    let (code, out, _) = goal(&dir, &["--at", "s.sw:30:28", "--json"]);
    assert_eq!(code, 0);
    let answer: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(answer["context"]["target"], "Int");
    assert_eq!(answer["context"]["hasType"], "Nat");
    let (_, out, _) = goal(&dir, &["--at", "s.sw:4:26", "--json"]);
    let answer: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(answer["declaration"], "multN0M0");
    let step = &answer["context"]["step"];
    assert_eq!(step["form"], "rewriteRule");
    assert_eq!(
        (&step["index"], &step["of"]),
        (&Value::from(2), &Value::from(2))
    );
    assert_eq!(step["before"], "q * 0 = 0");
    assert_eq!(step["rule"], "q * 0 = 0");
    assert_eq!(step["after"], "0 = 0");
    assert_eq!(step["range"]["column"], 26);
    let _ = std::fs::remove_dir_all(&dir);
}
