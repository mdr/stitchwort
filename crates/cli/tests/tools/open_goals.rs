//! `check: open-goals:` in `stitchwort.yaml` (SW-2762, D3489, D3494), end to
//! end: `check` reports open goals as warnings under `warn`, `audit` doesn't
//! change, `test` runs tests that rely on an open goal (D3507), and a bad
//! value is a project-file error. What uses an open goal is checked assuming
//! it holds, and stays unfinished (SW-2805); `run` and `build` run and build
//! it, after a warning, and a run stops at a `?` it reaches (D3507).

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
        assert!(
            stderr.contains("2 goals open: the declarations"),
            "{stderr}"
        );
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

/// Under `warn`, a test that relies on an open goal runs (D3507): one that
/// doesn't reach it passes as usual, and one that reaches a `?` standing for
/// data fails, naming the goal.
#[test]
fn a_test_that_reaches_an_open_goal_fails_naming_it_under_warn() {
    let dir = project("test-warn", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/t.sw"),
        "namespace Book\n\n\
         def orTwo (b: Bool): Nat := if b then 1 else two\n\n\
         test \"one is one\" := 1 == 1\n\n\
         test \"orTwo True\" := orTwo True == 1\n\n\
         test \"two is two\" := two == 2\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["test"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "{stdout}{stderr}");
    assert!(stdout.contains("✓ one is one"), "{stdout}");
    assert!(stdout.contains("✓ orTwo True"), "{stdout}");
    assert!(
        stdout.contains("✗ two is two  ran  (reached `two`'s goal ("),
        "{stdout}"
    );
    assert!(
        stdout.contains("src/a.sw:7), which has no value to run)"),
        "{stdout}"
    );
    assert!(stdout.contains("2 passed, 1 failed"), "{stdout}");
    assert!(
        stderr.contains("2 goals open, allowed by `check: open-goals: warn`"),
        "{stderr}"
    );
}

/// `run` runs a program that relies on open goals, after a warning naming
/// them (D3507); a `?` standing for data that the run reaches stops it,
/// naming the goal, on every backend.
#[test]
fn run_warns_and_stops_at_an_open_goal_it_reaches() {
    let dir = project("run", "sources: [src]\n");
    std::fs::write(
        dir.join("src/m.sw"),
        "namespace Book\n\n\
         import Std (Nat)\n\n\
         def main(): {IO} () :=\n  \
           IO.print \"start\"\n  \
           IO.print (if 1 == 1 then \"one\" else Nat.toText two)\n  \
           IO.print (Nat.toText two)\n",
    )
    .unwrap();
    let mut runs = vec![
        vec!["run", "Book.main"],
        vec!["run", "--reference", "Book.main"],
    ];
    if cfg!(feature = "native") {
        runs.push(vec!["run", "--native", "Book.main"]);
    }
    if Command::new("node").arg("--version").output().is_ok() {
        runs.push(vec!["run", "--js", "Book.main"]);
    }
    for args in runs {
        let out = stitchwort(&dir, &args);
        let stderr = text(&out.stderr);
        let stdout = text(&out.stdout);
        assert_eq!(out.status.code(), Some(2), "{args:?}: {stdout}{stderr}");
        // JS computes a module's constants as it loads, so `two` stops it
        // before `main` prints.
        if !args.contains(&"--js") {
            assert_eq!(stdout, "start\none\n", "{args:?}: {stderr}");
        }
        assert!(
            stderr
                .contains("warning: running with 1 open goal; results rely on it: `two`'s goal ("),
            "{args:?}: {stderr}"
        );
        assert!(
            stderr.contains("[E-UNREACHABLE] Error: the program reached `two`'s goal ("),
            "{args:?}: {stderr}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A false proof left as `?` lets a run reach a branch its types rule out;
/// the run stops there with an error that names the goals it relies on,
/// rather than an internal error (F1, docs/reviews/SW-2804-assumptions-review.md).
#[test]
fn run_stops_at_an_impossible_branch_reached_through_a_false_goal() {
    let dir = project("impossible", "sources: [src]\n");
    std::fs::write(
        dir.join("src/m.sw"),
        "namespace Book\n\n\
         import Std (Nat, List)\n\n\
         theorem inRange: 5 < List.length [10, 20, 30] := ?\n\n\
         def main(): {IO} () := IO.print (Nat.toText (List.getLt [10, 20, 30] 5 [ok := inRange]))\n",
    )
    .unwrap();
    // The evaluator's own stop is `indexed::running_into_an_impossible_branch_stops_the_run`
    // in the core's tests: here, the compiled runners.
    let mut runs = vec![vec!["run", "Book.main"]];
    if cfg!(feature = "native") {
        runs.push(vec!["run", "--native", "Book.main"]);
    }
    if Command::new("node").arg("--version").output().is_ok() {
        runs.push(vec!["run", "--js", "Book.main"]);
    }
    for args in runs {
        let out = stitchwort(&dir, &args);
        let stderr = text(&out.stderr);
        assert_eq!(out.status.code(), Some(2), "{args:?}: {stderr}");
        assert!(
            stderr.contains("the program reached a branch that can't be reached"),
            "{args:?}: {stderr}"
        );
        assert!(
            stderr.contains("one of the open goals it relies on is false"),
            "{args:?}: {stderr}"
        );
        assert!(stderr.contains("`inRange`'s goal ("), "{args:?}: {stderr}");
        assert!(stderr.contains("src/m.sw:5)"), "{args:?}: {stderr}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `build --js` builds exports that rely on open goals, after a warning; a
/// call that reaches one throws an `Error` named `Unreachable`.
#[test]
fn build_js_builds_with_open_goals_after_a_warning() {
    let dir = project("build", "sources: [src]\n");
    std::fs::write(
        dir.join("src/e.sw"),
        "namespace Book\n\nexport def twice: Nat := two + two\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["build", "--js", "Book", "-o", "out"]);
    let stderr = text(&out.stderr);
    let js = std::fs::read_to_string(dir.join("out/Book.js")).unwrap_or_default();
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    assert!(
        stderr.contains("warning: building with 1 open goal; results rely on it: `two`'s goal"),
        "{stderr}"
    );
    assert!(js.contains("name: \"Unreachable\""), "{js}");
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
    assert!(
        stderr.contains("2 goals open: the declarations"),
        "{stderr}"
    );
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
    for name in ["Book.uses", "Book.twoIsTwo", "Book.twoIsThree"] {
        assert!(
            stdout.contains(&format!("✗ {name}\n    fail: unfinished")),
            "{stdout}"
        );
    }
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
