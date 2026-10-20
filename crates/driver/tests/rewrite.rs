//! `rewrite` (docs/proposals/calc-rewrite.md §6, stage 2): what the examples
//! can't say, because it needs a setting of the elaborator or a look at the
//! terms produced.

use stitchwort_driver::driver::Session;

/// The codes of the errors loading `text` gives, with the search budget set
/// (`None`: the default).
fn codes(budget: Option<u64>, text: &str) -> Vec<&'static str> {
    let mut session = Session::new();
    session.elab.rewrite_budget = budget;
    match session.load("test.sw", text) {
        Ok(_) => Vec::new(),
        Err(errors) => errors.iter().map(|e| e.code).collect(),
    }
}

/// Two occurrences that need an unfolding to compare: the second candidate
/// has to be taken apart to be told from the rule's left side.
const NEEDS_COMPARING: &str = "\
theorem t (m: [a: Type] -> a -> a -> a) (h: [a: Type] -> [x: a] -> m x x = x) (q: Bool -> Nat -> Prop)
    (k: q (m False True) 3): q (m False True) (m 3 3) :=
  rewrite h in k
";

#[test]
fn running_out_of_the_search_budget_is_its_own_error() {
    assert_eq!(codes(None, NEEDS_COMPARING), Vec::<&str>::new());
    // The comparisons of one `rewrite` share a budget, and running out of it
    // is neither "no match" (`E-REWRITE-NOTHING`) nor a resource error that
    // stops the declaration: it's `E-REWRITE-BUDGET`.
    assert_eq!(codes(Some(20), NEEDS_COMPARING), vec!["E-REWRITE-BUDGET"]);
}

#[test]
fn the_budget_is_for_one_rewrite_not_for_the_declaration() {
    // A second `rewrite` has the whole budget again.
    let two = format!(
        "{NEEDS_COMPARING}\n{}",
        NEEDS_COMPARING.replacen("theorem t ", "theorem u ", 1)
    );
    assert_eq!(codes(Some(1_000), &two), Vec::<&str>::new());
    // And an exhausted search doesn't poison what comes after it: the next
    // declaration is checked as usual.
    let after = format!("{NEEDS_COMPARING}\ntheorem v (a: Nat): a = a := rfl\n");
    assert_eq!(codes(Some(20), &after), vec!["E-REWRITE-BUDGET"]);
}

#[test]
fn rewrite_is_a_keyword() {
    assert_eq!(codes(None, "def rewrite: Nat := 1\n"), vec!["E-PARSE"]);
    // `in` is not.
    assert_eq!(codes(None, "def f (in: Nat): Nat := in\n"), Vec::<&str>::new());
}

#[test]
fn a_rewrite_is_a_j_term_the_kernel_rechecks() {
    // `rewrite` produces `J`, which the kernel checks again: a rule whose
    // proof doesn't fit is an error in the rule's own elaboration, not a
    // kernel error.
    let text = "\
theorem t (a: Nat) (b: Nat) (h: a = b) (p: b + 1 = 1 + b): a + 1 = 1 + a :=
  rewrite h in p
";
    assert_eq!(codes(None, text), Vec::<&str>::new());
}
