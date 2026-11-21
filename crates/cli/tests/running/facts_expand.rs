//! `check --expand-facts` end to end: the terms it writes for every
//! `byFacts` of `examples/accept/facts-probes.sw`, `facts-forms.sw`,
//! `facts-cases-then.sw` and `facts-long-test.sw`, and of a project's
//! namespaces, check again (docs/syntax.md, "byFacts").

use std::path::Path;
use std::process::{Command, Output, Stdio};

use crate::common;

fn output(mut command: Command, dir: &Path) -> Output {
    command
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("start stitchwort")
}

#[test]
fn facts_expansions_check_again() {
    // `facts-forms.sw`'s `someEqual` and `pairNested` use a constructor
    // equation's field, which has no written form, so two calls stay there;
    // `facts-cases-then.sw`'s is checked in two cases and finds a different
    // term in each, so it stays too. Each is listed.
    for (file, name, kept) in [
        ("facts-probes.sw", "facts_probes_expand", 0),
        ("facts-forms.sw", "facts_forms_expand", 2),
        ("facts-cases-then.sw", "facts_cases_then_expand", 1),
        ("facts-long-test.sw", "facts_long_test_expand", 0),
    ] {
        let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("make the test's folder");
        let source = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../examples/accept")
            .join(file);
        std::fs::copy(&source, dir.join(file)).expect("copy the example");

        let expand = output(common::cli_with("check", &["--expand-facts", file]), &dir);
        let stderr = String::from_utf8_lossy(&expand.stderr);
        assert!(expand.status.success(), "--expand-facts failed:\n{stderr}");
        let expanded = std::fs::read_to_string(dir.join(file)).expect("read the expansion");
        let left = (expanded.lines())
            .filter(|l| !l.trim_start().starts_with("--") && l.contains("byFacts"))
            .count();
        assert_eq!(left, kept, "unexpected byFacts left:\n{expanded}");
        assert_eq!(
            stderr.matches("not expanded").count(),
            kept,
            "each call left is listed:\n{stderr}"
        );
        insta::assert_snapshot!(format!("{name}_text"), expanded);

        let check = output(common::cli_with("check", &["--no-cache", file]), &dir);
        assert!(
            check.status.success(),
            "the expansion of {file} doesn't check:\n{}{}",
            String::from_utf8_lossy(&check.stdout),
            String::from_utf8_lossy(&check.stderr)
        );
    }
}

/// In a project, the expansion is written in each namespace's own file and
/// checks there: with an explicit import list, the names it writes (a std
/// lemma in full, `Witness`, a lemma imported from another namespace)
/// resolve (docs/reviews/SW-4488-byfacts-review.md §18).
#[test]
fn facts_expansions_check_again_in_a_project() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("facts_project_expand");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("make the project's folder");
    let write = |path: &str, text: &str| {
        std::fs::write(dir.join(path), text).expect("write the project");
    };
    write("stitchwort.yaml", "# byFacts expanded across namespaces\n");
    write(
        "src/lib.sw",
        "namespace Lib

type Tag = | Red | Blue

opaque def Good (t: Tag): Prop := t = Red

theorem goodOf ∀ (t: Tag) (h: t = Red): Good t unfolding Good := h
",
    );
    write(
        "src/day.sw",
        "namespace Day

import Lib (Tag, Good, goodOf)

theorem both ∀ (a b: Bool) (x: a = True) (y: b = True): (a && b) = True := byFacts

theorem witnessed ∀ (p q: Nat → Prop) (h: ∃ (k: Nat) => p k ∧ q k): ∃ (k: Nat) => q k := byFacts

theorem viaLib ∀ (t: Tag) (h: t = Red ∧ True): Good t := byFacts [goodOf]
",
    );

    let expand = output(common::cli_with("check", &["--expand-facts"]), &dir);
    let stderr = String::from_utf8_lossy(&expand.stderr);
    assert!(expand.status.success(), "--expand-facts failed:\n{stderr}");
    let day = std::fs::read_to_string(dir.join("src/day.sw")).expect("read the expansion");
    for term in [
        ":= Std.Bool.andIntro x y",
        ":= match h with | Witness k kFact => Witness k kFact.right",
        ":= goodOf t h.left",
    ] {
        assert!(day.contains(term), "no `{term}` in the expansion:\n{day}");
    }
    assert!(!day.contains("byFacts"), "byFacts left:\n{day}");

    let check = output(common::cli_with("check", &["--no-cache"]), &dir);
    assert!(
        check.status.success(),
        "the project's expansion doesn't check:\n{}{}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );
}
