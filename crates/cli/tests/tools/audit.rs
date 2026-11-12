//! `stitchwort audit` (SW-912, D2040; docs/research/agentic-proving.md T1
//! stage 1, T2), end to end with the built command: each verdict, the
//! allowlist from a flag and from `stitchwort.yaml`, `--strict` and
//! `--json`; and `check --counterexamples` printing the vacuity verdict
//! without `--verbose`.

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

/// A fresh folder for one test.
fn folder(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-audit-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Audits `source` as a file `a.sw`, with `args`: (exit code, stdout).
fn audit_file(name: &str, source: &str, args: &[&str]) -> (i32, String) {
    let dir = folder(name);
    std::fs::write(dir.join("a.sw"), source).unwrap();
    let mut all = vec!["audit", "a.sw"];
    all.extend(args);
    let output = stitchwort(&dir, &all);
    let _ = std::fs::remove_dir_all(&dir);
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8(output.stdout).unwrap(),
    )
}

const CLEAN: &str = "theorem clean (n: Nat): n + 0 = n := omega\n";

/// The probe of §7.2: it checks, but no input satisfies its hypothesis.
const VACUOUS: &str = "theorem vacuous (n: Nat) (h: n + 1 = 0): n = 42 := omega\n";

const QUOT: &str = "def AllTrue (x: Bool) (y: Bool): Prop := Unit\n\
                    def Q: Type := Quot Bool AllTrue\n\n\
                    theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial\n";

#[test]
fn a_clean_theorem_passes() {
    let (code, out) = audit_file("clean", CLEAN, &[]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(
        out,
        "audited 1 theorem: 0 failed, 0 with warnings, 1 passed\n"
    );
    let (code, out) = audit_file("clean-verbose", CLEAN, &["--verbose"]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(
        out,
        "✓ clean\n    axioms: none\n    search: none in 1500 cases (sizes up to 100; evidence, \
         not a proof)\naudited 1 theorem: 0 failed, 0 with warnings, 1 passed\n"
    );
}

/// `Quot.sound` is allowed by default, and fails when the allowlist is
/// empty.
#[test]
fn an_axiom_beyond_the_allowlist_fails() {
    let (code, out) = audit_file("quot-default", QUOT, &["--no-search"]);
    assert_eq!(code, 0, "{out}");
    let (code, out) = audit_file("quot-none", QUOT, &["--allowed-axioms", ""]);
    assert_eq!(code, 1, "{out}");
    assert_eq!(
        out,
        "✗ same\n    fail: uses Quot.sound beyond the allowed axioms (none)\n\
         audited 1 theorem: 1 failed, 0 with warnings, 0 passed\n"
    );
}

#[test]
fn an_unknown_axiom_in_the_allowlist_is_an_error() {
    let dir = folder("unknown-axiom");
    std::fs::write(dir.join("a.sw"), CLEAN).unwrap();
    let output = stitchwort(&dir, &["audit", "a.sw", "--allowed-axioms", "propext"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("`propext` isn't an axiom: the axioms are Quot.sound"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// A `?` in the theorem, or in a lemma it uses.
#[test]
fn an_unfinished_theorem_fails_directly_or_through_what_it_uses() {
    let source = "theorem step (n: Nat): n = n := ?\n\n\
                  theorem uses (n: Nat): n = n := step n\n\n\
                  theorem fine (n: Nat): n = n := rfl\n";
    let (code, out) = audit_file("unfinished", source, &["--no-search"]);
    assert_eq!(code, 1, "{out}");
    let place = "a.sw:1:33";
    assert_eq!(
        out,
        format!(
            "✗ step\n    fail: has an open goal ({place})\n\
             ✗ uses\n    fail: relies on an open goal: `step`'s ({place}); checked assuming it \
             holds\n\
             audited 3 theorems: 2 failed, 0 with warnings, 1 passed (2 rely on open goals)\n"
        )
    );
    // Named, the one that uses the lemma fails on its own.
    let (code, out) = audit_file("unfinished-named", source, &["--no-search", "uses"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.starts_with("✗ uses\n"), "{out}");
}

/// A theorem whose hypotheses held for no input warns, which doesn't fail
/// unless `--strict`.
#[test]
fn vacuous_hypotheses_warn_and_fail_only_with_strict() {
    let (code, out) = audit_file("vacuous", VACUOUS, &[]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(
        out,
        "! vacuous\n    warn: no input made the hypotheses true (0 of 1500 cases): if they \
         contradict each other, the theorem is vacuous\n\
         audited 1 theorem: 0 failed, 1 with warnings, 0 passed\n"
    );
    let (code, out) = audit_file("vacuous-strict", VACUOUS, &["--strict"]);
    assert_eq!(code, 1, "{out}");
    assert!(
        out.ends_with(
            "audited 1 theorem: 0 failed, 1 with warnings (--strict: warnings fail), 0 passed\n"
        ),
        "{out}"
    );
    // Without the search, there's nothing to warn about.
    let (code, out) = audit_file("vacuous-no-search", VACUOUS, &["--strict", "--no-search"]);
    assert_eq!(code, 0, "{out}");
}

/// A theorem that concludes `Void`, or a `Not`, claims its hypotheses
/// contradict each other: their never holding is no warning.
#[test]
fn a_theorem_concluding_void_doesnt_warn() {
    let source = "theorem impossible (n: Nat) (h: n + 1 = 0): Void := omega\n\n\
                  theorem notZero (n: Nat): Not (n + 1 = 0) := h => omega\n";
    let (code, out) = audit_file("refutes", source, &["--strict", "--verbose"]);
    assert_eq!(code, 0, "{out}");
    let line = "    search: gave up: the hypotheses held in 0 of 1500 cases (as it claims: it \
                concludes that they contradict each other)\n";
    assert_eq!(
        out,
        format!(
            "✓ impossible\n    axioms: none\n{line}✓ notZero\n    axioms: none\n{line}\
             audited 2 theorems: 0 failed, 0 with warnings, 2 passed\n"
        )
    );
}

#[test]
fn json_gives_every_theorem_and_its_findings() {
    let source = format!("{CLEAN}\n{VACUOUS}\n{QUOT}");
    let (code, out) = audit_file("json", &source, &["--json", "--allowed-axioms", ""]);
    assert_eq!(code, 1, "{out}");
    let json: serde_json::Value = serde_json::from_str(&out).expect("one JSON object");
    assert_eq!(json["version"], 2);
    assert_eq!(json["ok"], false);
    assert_eq!(json["allowed_axioms"], serde_json::json!([]));
    assert_eq!(
        json["summary"],
        serde_json::json!({
            "theorems": 3,
            "generated": 0,
            "failed": 1,
            "warned": 1,
            "passed": 1,
            "assuming": 0,
            "unfinished": 0
        })
    );
    let theorems = json["theorems"].as_array().unwrap();
    let names: Vec<&str> = theorems
        .iter()
        .map(|t| t["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["clean", "vacuous", "same"]);
    assert_eq!(theorems[0]["findings"], serde_json::json!([]));
    assert_eq!(theorems[0]["search"]["verdict"], "none-found");
    assert_eq!(theorems[1]["findings"][0]["check"], "vacuous");
    assert_eq!(theorems[1]["findings"][0]["severity"], "warn");
    assert_eq!(theorems[1]["search"]["verdict"], "never-held");
    assert_eq!(theorems[1]["search"]["held"], 0);
    assert_eq!(theorems[2]["axioms"], serde_json::json!(["Quot.sound"]));
    assert_eq!(theorems[2]["findings"][0]["check"], "axioms");
    assert_eq!(theorems[2]["findings"][0]["severity"], "fail");
    assert_eq!(theorems[2]["status"], "checked");
    assert_eq!(theorems[2]["openGoals"], serde_json::json!([]));
}

/// A theorem that relies on an open goal is `assuming`, and names the goal;
/// one that can't be checked until a goal is filled is `unfinished`, and
/// names it too (D3505).
#[test]
fn json_names_the_goals_a_theorem_relies_on_or_waits_for() {
    let source = "def two: Nat := ?\n\n\
                  theorem step (n: Nat): n = n := ?\n\n\
                  theorem uses (n: Nat): n = n := step n\n\n\
                  theorem blocked: two = 3 := rfl\n";
    let (code, out) = audit_file("json-goals", source, &["--json", "--no-search"]);
    assert_eq!(code, 1, "{out}");
    let json: serde_json::Value = serde_json::from_str(&out).expect("one JSON object");
    let by_name = |name: &str| {
        json["theorems"]
            .as_array()
            .unwrap()
            .iter()
            .find(|t| t["name"] == name)
            .unwrap_or_else(|| panic!("{name} in {out}"))
            .clone()
    };
    let uses = by_name("uses");
    assert_eq!(uses["status"], "assuming");
    assert_eq!(uses["findings"][0]["check"], "unfinished");
    assert_eq!(uses["openGoals"][0]["declaration"], "Main.step");
    assert_eq!(uses["openGoals"][0]["line"], 3);
    let blocked = by_name("blocked");
    assert_eq!(blocked["status"], "unfinished");
    assert_eq!(blocked["openGoals"][0]["declaration"], "Main.two");
    assert!(
        (blocked["findings"][0]["message"].as_str().unwrap()).contains("can't be checked until"),
        "{out}"
    );
    assert_eq!(json["summary"]["assuming"], 2);
    assert_eq!(json["summary"]["unfinished"], 1);
}

/// Generated declarations are counted apart from the theorems written in
/// source: a record's `T.ext`, and a variant's shared-field update lemmas.
#[test]
fn generated_lemmas_are_counted_apart_from_written_theorems() {
    let source = "type Grade = { letter: Nat, modifier: Nat }\n\n\
                  type Change =\n  | Set (letter: Nat) (modifier: Nat)\n  | Keep (letter: Nat) (modifier: Nat)\n\n\
                  theorem gradeRefl (g: Grade): g = g := rfl\n";
    let (code, out) = audit_file("generated", source, &["--no-search"]);
    assert_eq!(code, 0, "{out}");
    // The record's `Grade.ext`, and Change's four update lemmas.
    assert_eq!(
        out,
        "audited 1 theorem and 5 generated lemmas: 0 failed, 0 with warnings, 6 passed\n"
    );
}

/// A generated declaration's failure is counted too, not printed as
/// `0 failed`: these equations inherit `Quot.sound` from the definition
/// they unfold.
#[test]
fn a_failing_generated_declaration_is_counted_and_fails() {
    let source = "def AllTrue (x: Bool) (y: Bool): Prop := Unit\n\
                  def Q: Type := Quot Bool AllTrue\n\n\
                  def q (n: Nat): Nat :=\n  let e: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial\n  n\n\n\
                  def f: Nat → Nat\n  | 0 => q 0\n  | Succ k => q k\n\n\
                  theorem clean (n: Nat): n = n := rfl\n";
    let (code, out) = audit_file(
        "generated-fail",
        source,
        &["--no-search", "--allowed-axioms", ""],
    );
    assert_eq!(code, 1, "{out}");
    let fail = "    fail: uses Quot.sound beyond the allowed axioms (none)\n";
    assert_eq!(
        out,
        format!(
            "✗ f.eq1\n{fail}✗ f.eq2\n{fail}\
             audited 1 theorem and 2 generated lemmas: 2 failed, 0 with warnings, 1 passed\n"
        )
    );
}

/// A generated record's `T.ext` lemma is marked `generated` in the JSON, and
/// its vacuity warning is suppressed: the compiler wrote its hypotheses, so
/// a random miss says nothing (SW-2765; SW-2760's (c) policy).
#[test]
fn a_generated_ext_lemma_is_marked_generated_and_not_warned_about() {
    // A record big enough that the enumerated inputs don't reach it, and
    // with a `Char` so the random phase runs: its two records are drawn
    // separately, so the hypotheses never hold.
    let source = "type W0 = | Mk0 (n: Nat)\n\
                  type W1 = | Mk1 (w: W0)\n\
                  type W2 = | Mk2 (w: W1)\n\
                  type W3 = | Mk3 (w: W2)\n\n\
                  type R = { w: W3, n0: Nat, n1: Nat, c0: Char, c1: Char }\n\n\
                  theorem refl (x: R): x = x := rfl\n";
    let (code, out) = audit_file("generated-ext", source, &["--json"]);
    assert_eq!(code, 0, "{out}");
    let json: serde_json::Value = serde_json::from_str(&out).expect("one JSON object");
    let ext = json["theorems"]
        .as_array()
        .unwrap()
        .iter()
        .find(|t| t["name"] == "R.ext")
        .expect("the generated ext lemma");
    assert_eq!(ext["generated"], true, "{out}");
    assert_eq!(ext["search"]["verdict"], "never-held", "{out}");
    assert!(
        !ext["findings"]
            .as_array()
            .unwrap()
            .iter()
            .any(|f| f["check"] == "vacuous"),
        "{out}"
    );
}

/// In a project: a namespace, a theorem by its full name, and the
/// allowlist from `stitchwort.yaml`.
#[test]
fn a_project_audits_namespaces_and_names_with_its_own_allowlist() {
    let dir = folder("project");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("stitchwort.yaml"),
        "audit:\n  allowed-axioms: []\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/a.sw"),
        format!("namespace Proof\n\n{CLEAN}\n{QUOT}"),
    )
    .unwrap();
    std::fs::write(
        dir.join("src/b.sw"),
        format!("namespace Other\n\n{VACUOUS}"),
    )
    .unwrap();
    let everything = stitchwort(&dir, &["audit", "--no-search"]);
    let named = stitchwort(&dir, &["audit", "--no-search", "Proof.clean"]);
    let namespace = stitchwort(&dir, &["audit", "Other"]);
    let flag = stitchwort(
        &dir,
        &["audit", "--no-search", "--allowed-axioms", "Quot.sound"],
    );
    std::fs::write(
        dir.join("stitchwort.yaml"),
        "audit:\n  allowed-axioms: [propext]\n",
    )
    .unwrap();
    let bad_config = stitchwort(&dir, &["audit"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = |o: &Output| String::from_utf8_lossy(&o.stdout).to_string();
    assert_eq!(everything.status.code(), Some(1), "{}", stdout(&everything));
    assert_eq!(
        stdout(&everything),
        "✗ Proof.same\n    fail: uses Quot.sound beyond the allowed axioms (none)\n\
         audited 3 theorems: 1 failed, 0 with warnings, 2 passed\n"
    );
    assert_eq!(named.status.code(), Some(0));
    assert_eq!(
        stdout(&named),
        "audited 1 theorem: 0 failed, 0 with warnings, 1 passed\n"
    );
    assert_eq!(namespace.status.code(), Some(0));
    assert!(
        stdout(&namespace).starts_with("! Other.vacuous\n"),
        "{}",
        stdout(&namespace)
    );
    assert_eq!(flag.status.code(), Some(0), "{}", stdout(&flag));
    assert_eq!(bad_config.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&bad_config.stderr)
            .contains("lists `propext`, which isn't an axiom"),
        "{}",
        String::from_utf8_lossy(&bad_config.stderr)
    );
}

#[test]
fn an_unknown_theorem_is_an_error() {
    let dir = folder("unknown-theorem");
    std::fs::write(dir.join("a.sw"), CLEAN).unwrap();
    let output = stitchwort(&dir, &["audit", "a.sw", "nope"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("there's no theorem `nope`"));
}

/// T2: `check --counterexamples` prints a theorem that checked though no
/// input made its hypotheses true, without `--verbose`, and counts it
/// apart; it still succeeds.
#[test]
fn check_counterexamples_prints_never_held_hypotheses_without_verbose() {
    let dir = folder("check");
    std::fs::write(dir.join("a.sw"), format!("{CLEAN}\n{VACUOUS}")).unwrap();
    let output = stitchwort(&dir, &["check", "a.sw", "--counterexamples"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "  ! vacuous  gave up: the hypotheses held in 0 of 10000 cases (if they contradict each \
         other, the theorem is vacuous)\n"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "searched 2 theorems for counterexamples: 0 false, 1 with none found, 1 gave up (1 \
             with the hypotheses true in no case), 0 inconclusive, 0 not applicable"
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// SW-1525: a statement naming a computation too big to read back in normal
/// form is out of scope for the search, not a hang.
#[test]
fn a_statement_naming_a_huge_computation_skips_its_search() {
    let source = "def countdown (acc: Nat): Nat → Nat\n  | 0 => acc\n  | Succ k => countdown (acc + 1) k\n\n\
                  def Big (n: Nat): Prop := n = n\n\n\
                  theorem big (m: Nat): Big (countdown 0 100000000) := rfl\n";
    let (code, out) = audit_file("huge", source, &["--verbose"]);
    assert_eq!(code, 0, "{out}");
    assert!(
        out.contains("search: not applicable: reading the statement back took more than"),
        "{out}"
    );
    assert!(
        out.ends_with(
            "audited 1 theorem and 3 generated lemmas: 0 failed, 0 with warnings, 4 passed\n"
        ),
        "{out}"
    );
}

/// SW-2943 (docs/proposals/tests-with-errors.md §4.5): `A` has an error and
/// a false theorem, and a theorem that waits for the error; `B` is fine.
const ERRORS_IN_A: &str = r#"namespace A

def double (n: Nat): Nat := n + n

def broken (n: Nat): Nat := "oops"

def twice (n: Nat): Nat := broken n + 1

theorem doubleTwo: double 2 = 5 := rfl

theorem twiceOne: twice 1 = 2 := rfl
"#;

const B_USES_A: &str = r#"namespace B

import A (double)

theorem quadOne: double 2 = 4 := rfl
"#;

fn project_with_errors(name: &str) -> PathBuf {
    let dir = folder(name);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/a.sw"), ERRORS_IN_A).unwrap();
    std::fs::write(dir.join("src/b.sw"), B_USES_A).unwrap();
    dir
}

/// The verdicts are printed even though the project has errors, each
/// theorem by what is wrong with it; the one that doesn't touch an error
/// passes, and the run still fails (§4.8).
#[test]
fn audit_gives_a_verdict_per_theorem_in_a_project_with_errors() {
    let dir = project_with_errors("errors");
    let output = stitchwort(&dir, &["audit", "--no-search"]);
    // Places start with the project folder's name.
    let folder = format!("{}/", dir.file_name().unwrap().to_string_lossy());
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8(output.stdout)
        .unwrap()
        .replace(&folder, "");
    assert_eq!(output.status.code(), Some(1), "{stdout}");
    assert_eq!(
        stdout,
        "✗ A.doubleTwo\n    fail: has an error (src/a.sw:9:36)\n\
         ✗ A.twiceOne\n    fail: can't be checked until `broken` is fixed (src/a.sw:5:29)\n\
         audited 3 theorems: 2 failed, 0 with warnings, 1 passed (2 errors in the project)\n"
    );
}

#[test]
fn audit_json_has_a_status_for_a_theorem_with_an_error_or_waiting_for_one() {
    let dir = project_with_errors("errors-json");
    let output = stitchwort(&dir, &["audit", "--no-search", "--json"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(output.status.code(), Some(1));
    let v: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(v["ok"], false);
    assert_eq!(v["summary"]["errors"], 2);
    let rows: Vec<_> = (v["theorems"].as_array().unwrap().iter())
        .map(|t| {
            (
                t["name"].as_str().unwrap(),
                t["status"].as_str().unwrap(),
                t["error"]["declaration"].as_str(),
                t["error"]["line"].as_u64(),
            )
        })
        .collect();
    assert_eq!(
        rows,
        [
            ("A.doubleTwo", "failed", Some("A.doubleTwo"), Some(9)),
            ("A.twiceOne", "waiting", Some("broken"), Some(5)),
            ("B.quadOne", "checked", None, None),
        ]
    );
    assert_eq!(v["theorems"][1]["findings"][0]["check"], "waiting");
}

/// A theorem that passes doesn't make a project with errors succeed.
#[test]
fn audit_fails_for_an_error_elsewhere_even_if_every_theorem_passes() {
    let dir = project_with_errors("errors-elsewhere");
    let output = stitchwort(&dir, &["audit", "--no-search", "B"]);
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(output.status.code(), Some(1), "{stdout}");
    assert!(
        stdout.ends_with("1 passed (2 errors in the project)\n"),
        "{stdout}"
    );
}
