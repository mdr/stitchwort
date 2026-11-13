//! `W-THEOREM-FORALL` (docs/proposals/theorem-binders.md §6, D3470) and
//! `W-ARROW-FORALL` (docs/proposals/forall-style-enforcement.md, D3462): how
//! a statement is written.

use stitchwort_cli::driver::Session;

/// The codes of the warnings of `text`, which must check.
fn warned(text: &str) -> Vec<&'static str> {
    let mut session = Session::new();
    session
        .load("test.sw", text)
        .unwrap_or_else(|e| panic!("{e:#?}"));
    session.warnings.iter().map(|w| w.code).collect()
}

#[test]
fn a_theorem_that_starts_with_forall_warns() {
    let codes =
        warned("theorem addZero: ∀ (n: Nat) => n + 0 = n\n  | Zero => rfl\n  | Succ k => rfl\n");
    assert_eq!(codes, ["W-THEOREM-FORALL"]);
}

#[test]
fn a_forall_after_a_premise_or_a_header_forall_does_not() {
    let codes = warned(
        "theorem after (n: Nat): n < 3 → ∀ (k: Nat) => k + 0 = k := h k => rfl\n\
         theorem header ∀ (n: Nat): n + 0 = n := rfl\n\
         theorem inside (p: Nat → Prop): (∀ (n: Nat) => p n) → p 0 := all => all 0\n",
    );
    assert!(codes.is_empty(), "{codes:?}");
}

#[test]
fn a_named_arrow_over_a_proposition_warns() {
    let codes = warned("theorem addZero: (n: Nat) -> n + 0 = n := n => rfl\n");
    assert_eq!(codes, ["W-ARROW-FORALL"]);
}

#[test]
fn a_file_that_does_not_parse_has_no_arrow_forall_warning() {
    let mut session = Session::new();
    let diagnostics = session
        .load("test.sw", "theorem bad (n: Nat): n = n := (rfl\n")
        .expect_err("the file doesn't parse");
    assert!(
        diagnostics.iter().all(|d| d.code != "W-ARROW-FORALL"),
        "{diagnostics:#?}"
    );
}

#[test]
fn arrows_that_are_not_statements_do_not() {
    let codes = warned(
        "def vector (n: Nat): Type := Nat\n\
         def functionType: (n: Nat) -> Type := n => vector n\n\
         theorem unused (m: Nat): (n: Nat) -> m = m := n => rfl\n\
         theorem namedProof (m: Nat): (h: m = 1) -> m = 1 := h => h\n\
         theorem plain (m: Nat): m = m → m = m := h => h\n\
         theorem header (n: Nat) (m: Nat): n + m = m + n := omega\n",
    );
    assert!(codes.is_empty(), "{codes:?}");
}
