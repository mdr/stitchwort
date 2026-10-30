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
        "✓ clean\n    axioms: none\n    search: none in 10000 cases (sizes up to 100; evidence, \
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
    let unfinished = "    fail: unfinished: it, or something it uses, has an open goal (`?`), so \
                      it isn't checked\n";
    assert_eq!(
        out,
        format!(
            "✗ step\n{unfinished}✗ uses\n{unfinished}\
             audited 3 theorems: 2 failed, 0 with warnings, 1 passed\n"
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
        "! vacuous\n    warn: no input made the hypotheses true (0 of 10000 cases): if they \
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
    let line = "    search: gave up: the hypotheses held in 0 of 10000 cases (as it claims: it \
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
    assert_eq!(json["version"], 1);
    assert_eq!(json["ok"], false);
    assert_eq!(json["allowed_axioms"], serde_json::json!([]));
    assert_eq!(
        json["summary"],
        serde_json::json!({"theorems": 3, "failed": 1, "warned": 1, "passed": 1})
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
