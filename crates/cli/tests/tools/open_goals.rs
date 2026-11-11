//! `check: open-goals:` in `stitchwort.yaml` (SW-2762, D3489, D3494), end to
//! end: `check` reports open goals as warnings under `warn`, `audit` doesn't
//! change, `test` skips tests that use an unfinished declaration (D3500), and
//! a bad value is a project-file error. What uses an open goal is checked
//! assuming it holds, and stays unfinished (SW-2805).

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn stitchwort(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .arg("--no-cache")
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// A project whose `yaml` is `stitchwort.yaml`, with one finished theorem, one
/// with an open goal, and a test that uses the open one.
fn project(name: &str, yaml: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-goals-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), yaml).unwrap();
    std::fs::write(
        dir.join("src/a.sw"),
        "namespace Book\n\n\
         theorem done (n: Nat): n + 0 = n := omega\n\n\
         theorem exercise (n: Nat): 0 + n = n := ?\n\n\
         def two: Nat := ?\n",
    )
    .unwrap();
    dir
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).to_string()
}

#[test]
fn warn_reports_open_goals_as_warnings_and_passes() {
    let dir = project("warn", "check:\n  open-goals: warn\n");
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    assert!(stderr.contains("[GOAL] Warning: in `exercise`"), "{stderr}");
    assert!(stderr.contains("[GOAL] Warning: in `two`"), "{stderr}");
    assert!(stderr.contains("⊢ n = n"), "{stderr}");
    assert!(
        stderr.contains("2 goals open, allowed by `check: open-goals: warn`"),
        "{stderr}"
    );
}

#[test]
fn without_the_setting_or_with_fail_open_goals_fail_the_check() {
    for (name, yaml) in [
        ("default", "sources: [src]\n"),
        ("fail", "check:\n  open-goals: fail\n"),
    ] {
        let dir = project(name, yaml);
        let out = stitchwort(&dir, &["check"]);
        let _ = std::fs::remove_dir_all(&dir);
        let stderr = text(&out.stderr);
        assert_eq!(out.status.code(), Some(1), "{name}: {stderr}");
        assert!(stderr.contains("[GOAL] Goal: in `exercise`"), "{stderr}");
        assert!(stderr.contains("2 goals open\n"), "{stderr}");
    }
}

#[test]
fn audit_still_fails_unfinished_theorems_under_warn() {
    let dir = project("audit", "check:\n  open-goals: warn\n");
    let out = stitchwort(&dir, &["audit", "--no-search"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "{stdout}{}", text(&out.stderr));
    assert!(stdout.contains("✗ Book.exercise"), "{stdout}");
}

#[test]
fn a_test_that_reaches_an_open_goal_is_skipped_under_warn() {
    let dir = project("test-warn", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/t.sw"),
        "namespace Book\n\n\
         test \"one is one\" := 1 == 1\n\n\
         test \"two is two\" := two == 2\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["test"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{stderr}");
    assert!(stdout.contains("✓ one is one"), "{stdout}");
    assert!(
        stdout.contains("skipped: relies on `two`'s goal ("),
        "{stdout}"
    );
    assert!(stdout.contains("1 passed, 0 failed, 1 skipped"), "{stdout}");
    assert!(
        stderr.contains("2 goals open, allowed by `check: open-goals: warn`"),
        "{stderr}"
    );
}

#[test]
fn without_the_setting_a_test_that_reaches_an_open_goal_still_fails() {
    let dir = project("test-fail", "sources: [src]\n");
    std::fs::write(
        dir.join("src/t.sw"),
        "namespace Book\n\n\
         test \"one is one\" := 1 == 1\n\n\
         test \"two is two\" := two == 2\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["test"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{stderr}");
    assert!(stderr.contains("2 goals open\n"), "{stderr}");
}

#[test]
fn a_bad_value_is_a_project_file_error() {
    let dir = project("bad", "check:\n  open-goals: maybe\n");
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("`check: open-goals:` is `maybe`, which isn't a setting"),
        "{stderr}"
    );
    assert!(
        stderr.contains("the settings are `warn` and `fail` (the default)"),
        "{stderr}"
    );
}

#[test]
fn an_unknown_key_under_check_names_the_known_one() {
    let dir = project("key", "check:\n  open-goal: warn\n");
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("the known key under `check:` is `open-goals`"),
        "{stderr}"
    );
}

/// What uses an open goal is checked by the kernel assuming the goal holds
/// (docs/proposals/using-unfinished-proofs.md, SW-2805): a proof that goes
/// round in circles is an error now, not when the goal is filled. What
/// relies on a goal is still unfinished: `audit` fails it, and a use that
/// has to compute through a `?` is unfinished rather than an error.
#[test]
fn users_of_an_open_goal_are_checked_and_stay_unfinished() {
    let dir = project("users", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/u.sw"),
        "namespace Book\n\n\
         theorem uses (n: Nat): 0 + n = n := exercise n\n\n\
         theorem twoIsTwo: two = two := rfl\n\n\
         theorem twoIsThree: two = 3 := rfl\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check"]);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    let audit = stitchwort(&dir, &["audit", "--no-search"]);
    let stdout = text(&audit.stdout);
    assert_eq!(audit.status.code(), Some(1), "{stdout}");
    for name in ["Book.uses", "Book.twoIsTwo"] {
        assert!(
            stdout.contains(&format!("✗ {name}\n    fail: relies on an open goal: ")),
            "{stdout}"
        );
    }
    assert!(
        stdout.contains("✗ Book.twoIsThree\n    fail: can't be checked until `two`'s goal ("),
        "{stdout}"
    );
    // `check` says which are checked assuming goals hold and which aren't
    // checked at all.
    assert!(
        stderr.contains("declarations rely on open goals, checked assuming they hold"),
        "{stderr}"
    );
    assert!(
        stderr.contains("1 declaration can't be checked until a goal is filled"),
        "{stderr}"
    );
    assert!(
        stderr.contains("Book.twoIsThree  needs `two`'s goal ("),
        "{stderr}"
    );
    std::fs::write(
        dir.join("src/u.sw"),
        "namespace Book\n\n\
         theorem circular (n: Nat): 0 + n = n := let _ := exercise n; circular n\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("can't show that `Book.circular` terminates"),
        "{stderr}"
    );
}

/// `check --counterexamples` on a false statement left as `?`: it is
/// checked only assuming its goal holds, so a counterexample says the goal
/// is false, not that the checker is wrong (SW-2837).
#[test]
fn a_counterexample_to_an_assumed_goal_is_not_a_checked_theorem() {
    let dir = project("counterexample", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/w.sw"),
        "namespace Book\n\ntheorem wrong (n: Nat): n + 1 = n := ?\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check", "--counterexamples"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = text(&out.stdout);
    assert!(stdout.contains("✗ Book.wrong"), "{stdout}");
    assert!(!stdout.contains("this theorem checked"), "{stdout}");
}

/// A use of a definition whose only `?` is in a proof argument computes as
/// usual, so a mistake in it is reported; one that is stuck on a goal can't
/// be decided until the goal is filled, from this namespace or another
/// (SW-2837).
#[test]
fn only_a_use_stuck_on_a_goal_waits_for_it() {
    let dir = project("stuck", "check:\n  open-goals: warn\n");
    let double = "namespace Book\n\n\
                  def keep (n: Nat) (h: n = n): Nat := n\n\n\
                  def double (n: Nat): Nat := keep (n + n) ?\n";
    let check = |book: &str, other: &str| {
        std::fs::write(dir.join("src/d.sw"), book).unwrap();
        std::fs::write(
            dir.join("src/o.sw"),
            format!("namespace Other\n\n{other}\n"),
        )
        .unwrap();
        let out = stitchwort(&dir, &["check"]);
        (out.status.code(), text(&out.stderr))
    };
    let (code, stderr) = check(double, "theorem twoIsThree: Book.two = 3 := rfl");
    assert_eq!(code, Some(0), "{stderr}");
    let wrong = format!("{double}\ntheorem doubleWrong: double 2 = 5 := rfl\n");
    let (code, stderr) = check(&wrong, "");
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("`double 2` and `5` aren't equal"),
        "{stderr}"
    );
    let (code, stderr) = check(double, "theorem doubleWrong: Book.double 2 = 5 := rfl");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(code, Some(1), "{stderr}");
    assert!(
        stderr.contains("`Book.double 2` and `5` aren't equal"),
        "{stderr}"
    );
}

/// `goal` without `--at` lists every open goal, what relies on it and what
/// waits for it (D3505), and `axioms` names the goals instead of refusing.
#[test]
fn goal_lists_every_open_goal_with_what_relies_on_it() {
    let dir = project("goal-list", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/u.sw"),
        "namespace Book\n\n\
         theorem uses (n: Nat): 0 + n = n := exercise n\n\n\
         theorem twoIsThree: two = 3 := rfl\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["goal"]);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
    assert!(stdout.starts_with("2 goals open\n"), "{stdout}");
    assert!(stdout.contains("`Book.exercise`  "), "{stdout}");
    assert!(
        stdout.contains("  ⊢ n = n\n  relied on by: Book.uses\n"),
        "{stdout}"
    );
    assert!(
        stdout.contains("can't be checked until it is filled: Book.twoIsThree"),
        "{stdout}"
    );
    let json = stitchwort(&dir, &["goal", "--json"]);
    let json: serde_json::Value = serde_json::from_slice(&json.stdout).expect("one JSON object");
    assert_eq!(json["open"], 2);
    let goals = json["goals"].as_array().unwrap();
    let exercise = goals
        .iter()
        .find(|g| g["declaration"] == "Book.exercise")
        .unwrap();
    assert_eq!(exercise["reliedOnBy"], serde_json::json!(["Book.uses"]));
    assert_eq!(exercise["blocking"], serde_json::json!([]));
    let axioms = stitchwort(&dir, &["axioms", "Book.uses"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = text(&axioms.stdout);
    assert_eq!(axioms.status.code(), Some(0), "{stdout}");
    assert!(
        stdout.contains("open goal in `Book.exercise` ("),
        "{stdout}"
    );
}

/// A goal that mentions an earlier `?` shows it as `?`, not as the name of
/// the assumption made for it (SW-2837, N3); a `decreasing` obligation and
/// a test are named by the declaration the reader wrote (N4, N5).
#[test]
fn goals_show_earlier_holes_as_question_marks_and_owners_as_written() {
    let dir = project("names", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/n.sw"),
        "namespace Book\n\n\
         def pick (n: Nat): Nat :=\n  let x: Nat := ?\n  let y: Nat := x + n\n  ?\n\n\
         def gcd2 (a: Nat) (b: Nat): Nat\n    decreasing b\n:=\n  \
         if h: b = 0 then a else gcd2 b (a % b) [decreasing := ?]\n\n\
         test \"never\" := ?\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["goal", "--json"]);
    let shown = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&shown.stderr);
    assert!(stderr.contains("x: Nat := ?\n"), "{stderr}");
    assert!(stderr.contains("y: Nat := ? + n"), "{stderr}");
    let json: serde_json::Value = serde_json::from_slice(&out.stdout).expect("one JSON object");
    let names: Vec<&str> = json["goals"]
        .as_array()
        .unwrap()
        .iter()
        .map(|g| g["declaration"].as_str().unwrap())
        .collect();
    assert!(names.contains(&"Book.gcd2"), "{names:?}");
    assert!(names.contains(&"Book.test \"never\""), "{names:?}");
}
