//! `check: open-goals:` in `stitchwort.yaml` (SW-2762, D3489, D3494), end to
//! end: `check` reports open goals as warnings under `warn`, `audit` doesn't
//! change, `test` fails tests that reach an unfinished declaration (SW-2909), and
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
fn a_test_that_reaches_an_open_goal_fails_under_warn() {
    let dir = project("test-warn", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/t.sw"),
        "namespace Book\n\n\
         test \"one is one\" := 1 == 1\n\n\
         test \"two is two\" := two == 2\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["test"]);
    let json = stitchwort(&dir, &["test", "--json"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(1), "{stdout}{stderr}");
    assert!(stdout.contains("✓ one is one"), "{stdout}");
    assert!(
        stdout.contains("✗ two is two  not run  (`two` isn't written yet: its body is `?` (")
            && stdout.contains("src/a.sw:7:17))"),
        "{stdout}"
    );
    assert!(stdout.contains("2 test(s): 1 passed, 1 failed"), "{stdout}");
    assert!(
        stderr.contains("2 goals open, allowed by `check: open-goals: warn`"),
        "{stderr}"
    );
    let json = text(&json.stdout);
    assert_eq!(json_status(&json), Some(1), "{json}");
    assert!(json.contains(r#""outcome":"failed""#), "{json}");
    assert!(
        json.contains("`two` isn't written yet: its body is `?` ("),
        "{json}"
    );
}

/// A test that only mentions a theorem with an open goal, which is erased
/// when the test runs, isn't affected.
#[test]
fn a_test_that_mentions_an_unfinished_theorem_still_runs() {
    let dir = project("test-theorem", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/t.sw"),
        "namespace Book\n\n\
         def next (n: Nat) (h: 0 + n = n): Nat := n + 1\n\n\
         test \"uses a proof\" := next 1 (exercise 1) == 2\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["test"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
    assert!(
        stdout.contains("✓ uses a proof  ran  (assuming `exercise`)"),
        "{stdout}"
    );
}

/// A passing test that relies on several unfinished proofs names each it
/// assumes, the first three and then how many more; `--json` lists them all
/// (SW-2939).
#[test]
fn a_passing_test_lists_every_open_goal_it_assumes() {
    let dir = project("test-assuming", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/t.sw"),
        "namespace Book\n\n\
         theorem g1 (n: Nat): n = n := ?\n\n\
         theorem g2 (n: Nat): n = n := ?\n\n\
         theorem g3 (n: Nat): n = n := ?\n\n\
         theorem g4 (n: Nat): n = n := ?\n\n\
         def pick (n: Nat) (h1: n = n) (h2: n = n) (h3: n = n) (h4: n = n): Nat := n\n\n\
         test \"uses four\" := pick 0 (g1 0) (g2 0) (g3 0) (g4 0) == 0\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["test"]);
    let json = stitchwort(&dir, &["test", "--json"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
    assert!(
        stdout.contains("✓ uses four  ran  (assuming `g1`, `g2`, `g3`, and 1 more)"),
        "{stdout}"
    );
    let json = text(&json.stdout);
    let v: serde_json::Value = serde_json::from_str(&json).expect(&json);
    let assuming = v["tests"][0]["assuming"].as_array().expect(&json);
    let named: Vec<(&str, &str)> = (assuming.iter())
        .map(|a| (a["name"].as_str().unwrap(), a["kind"].as_str().unwrap()))
        .collect();
    assert_eq!(
        named,
        [
            ("g1", "goal"),
            ("g2", "goal"),
            ("g3", "goal"),
            ("g4", "goal")
        ],
        "{json}"
    );
    assert_eq!(assuming[0]["line"], 3, "{json}");
}

fn json_status(json: &str) -> Option<i32> {
    // `"ok":false` is what a nonzero exit says.
    json.contains(r#""ok":false"#).then_some(1)
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

/// `goal --summary` counts the open goals per namespace, in the project's
/// order, saying which are done, and the total: a reader working through a
/// book sees their progress chapter by chapter (SW-2897, book gap G6).
#[test]
fn goal_summary_counts_each_namespace_and_lists_the_done_ones() {
    let dir = project("goal-summary", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/z.sw"),
        "namespace Other\n\ntheorem quiet (n: Nat): n + 0 = n := omega\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["goal", "--summary"]);
    let stdout = text(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{stdout}{}", text(&out.stderr));
    assert_eq!(
        stdout,
        "Book: 2 open\nOther: done\n2 goals open in 1 of 2 namespaces\n"
    );
    let json = stitchwort(&dir, &["goal", "--summary", "--json"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(json.status.code(), Some(0), "{}", text(&json.stderr));
    let json: serde_json::Value = serde_json::from_slice(&json.stdout).expect("one JSON object");
    assert_eq!(json["open"], 2);
    assert_eq!(
        json["namespaces"],
        serde_json::json!([
            {"name": "Book", "open": 2},
            {"name": "Other", "open": 0},
        ])
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

/// A use of a declaration that waits for a goal waits for the same goal,
/// down a chain of uses and across namespaces, and is named with it; one
/// whose signature waited, so has no definition, too. A real error beside
/// such a use is still reported (SW-2855).
#[test]
fn a_use_of_what_waits_for_a_goal_waits_for_it_too() {
    let dir = project("transitive", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/h.sw"),
        "namespace Book\n\n\
         def half: Nat -> Nat\n  | Zero => 0\n  | Succ k => ?\n\n\
         theorem halfOne: half 1 = 0 := rfl\n\n\
         theorem usesHalfOne: halfOne = halfOne := rfl\n\n\
         theorem usesUses: usesHalfOne = usesHalfOne := rfl\n\n\
         theorem sigWaits: (rfl: half 1 = 0) = rfl := rfl\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/o.sw"),
        "namespace Other\n\n\
         theorem otherUses: Book.usesHalfOne = Book.usesHalfOne := rfl\n\n\
         theorem otherSig: Book.sigWaits = Book.sigWaits := rfl\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check"]);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    assert!(!stderr.contains("E-FAILED-DEPENDENCY"), "{stderr}");
    for name in [
        "Book.halfOne ",
        "Book.usesHalfOne ",
        "Book.usesUses ",
        "Book.sigWaits ",
        "Other.otherUses ",
        "Other.otherSig ",
    ] {
        let line = stderr.lines().find(|l| l.trim_start().starts_with(name));
        assert!(
            line.is_some_and(|l| l.contains("needs `half`'s goal")),
            "{name}: {stderr}"
        );
    }
    let goal = text(&stitchwort(&dir, &["goal"]).stdout);
    assert!(
        goal.contains("Book.usesUses") && goal.contains("Other.otherSig"),
        "{goal}"
    );
    let audit = text(&stitchwort(&dir, &["audit"]).stdout);
    assert!(
        audit.contains("✗ Other.otherUses\n    fail: can't be checked until `half`'s goal"),
        "{audit}"
    );
    std::fs::write(
        dir.join("src/b.sw"),
        "namespace Book\n\ntheorem bad (h: halfOne = halfOne): 1 = 2 := rfl\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{stderr}");
    assert!(stderr.contains("`1` and `2` aren't equal"), "{stderr}");
}

/// A declaration with two messages, each showing a term stuck on a
/// different goal, waits for both (SW-2856).
#[test]
fn a_use_stuck_on_goals_in_several_messages_waits_for_all_of_them() {
    let dir = project("several", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/s.sw"),
        "namespace Book\n\n\
         def a: Nat -> Nat\n  | Zero => 0\n  | Succ k => ?\n\n\
         def b: Nat -> Nat\n  | Zero => 0\n  | Succ k => ?\n\n\
         def pick: Nat -> Bool\n\
         \x20 | Zero => (rfl: a 1 = 5) = rfl\n\
         \x20 | Succ k => (rfl: b 1 = 5) = rfl\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    let line = stderr
        .lines()
        .find(|l| l.trim_start().starts_with("Book.pick "));
    assert!(
        line.is_some_and(|l| l.contains("`a`'s goal") && l.contains("`b`'s goal")),
        "{stderr}"
    );
}

/// What the compiler made for a written declaration isn't a theorem the
/// reader wrote: not `gcd2.unfold`, nor a recursive type's `induct` (found
/// by its span, which is its type's), SW-2856.
#[test]
fn what_the_compiler_made_is_not_counted_as_written() {
    let dir = project("generated", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/g.sw"),
        "namespace Book\n\n\
         def half (n: Nat): Nat := ?\n\n\
         def gcd2 (a b: Nat): Nat\n    decreasing b\n:=\n\
         \x20 let r := a % b\n\
         \x20 if r < b then (if b = 0 then half a else gcd2 b r) else a\n\n\
         theorem viaUnfold (a b: Nat): gcd2 a b = gcd2 a b := rewrite gcd2.unfold a b in rfl\n\n\
         type Rose = | Node (xs: List Rose) (n: Std.Vec Nat (half 2))\n",
    )
    .unwrap();
    let goal = text(&stitchwort(&dir, &["goal"]).stdout);
    let _ = std::fs::remove_dir_all(&dir);
    let line = goal
        .lines()
        .find(|l| l.contains("relied on by:"))
        .unwrap_or_else(|| panic!("{goal}"));
    assert_eq!(
        line.trim(),
        "relied on by: Book.gcd2, Book.viaUnfold",
        "{goal}"
    );
}

/// A goal whose statement steps at once, many times (`countDown 100000 []`),
/// is stated as written, without computing it: it becomes an assumption the
/// next theorem relies on, rather than running out or falling back (SW-2843).
#[test]
fn a_goal_that_would_compute_deeply_is_assumed_as_written() {
    let dir = project("deep", "check:\n  open-goals: warn\n");
    std::fs::write(
        dir.join("src/a.sw"),
        "namespace Book\n\n\
         def countDown (n: Nat) (acc: List Nat): List Nat := match n with\n  \
         | Zero => acc\n  \
         | Succ k => countDown k [k, ..acc]\n\n\
         theorem opening: countDown 100000 [] = [] := ?\n\n\
         theorem user: countDown 100000 [] = [] := opening\n",
    )
    .unwrap();
    let out = stitchwort(&dir, &["check"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "{stderr}");
    assert!(!stderr.contains("E-RESOURCE"), "{stderr}");
    assert!(
        stderr.contains("1 declaration relies on open goals"),
        "{stderr}"
    );
}
