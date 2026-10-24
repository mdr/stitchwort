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

/// A rule whose left side computes to a long term: `sumMap g 40` is
/// `g 40 + (g 39 + …)`.
const LONG_LEFT_SIDE: &str = "\
def sumMap (g: Nat -> Nat): Nat -> Nat
  | Zero => 0
  | Succ n => g (Succ n) + sumMap g n

theorem t (g: Nat -> Nat) (f: Nat -> Nat) (h: (n: Nat) -> f (sumMap g n) = 0) (q: Nat -> Prop) (k: q 0):
    q (f (sumMap g 41)) :=
  rewrite h 40 in k
";

#[test]
fn the_budget_message_shows_both_terms_shortened() {
    let mut session = Session::new();
    session.elab.rewrite_budget = Some(20);
    let Err(errors) = session.load("test.sw", LONG_LEFT_SIDE) else {
        panic!("expected an error");
    };
    let e = &errors[0];
    assert_eq!(e.code, "E-REWRITE-BUDGET");
    // The terms are in notes, not the message, and cut short with a pointer
    // to seeing them whole (SW-207).
    assert_eq!(
        e.message,
        "`rewrite` couldn't decide whether a part of the goal is the rule's left side"
    );
    let note = |start: &str| {
        e.notes
            .iter()
            .find(|n| n.starts_with(start))
            .unwrap_or_else(|| panic!("a note starting `{start}` in {:#?}", e.notes))
    };
    assert!(note("the part of the goal, as it computes: `f (g 41 + ").contains('…'));
    assert!(note("the rule's left side: `f (g 40 + ").contains('…'));
    note("the terms are shortened (`…`); set `STITCHWORT_FULL_TERMS=1`");
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
    assert_eq!(
        codes(None, "def f (in: Nat): Nat := in\n"),
        Vec::<&str>::new()
    );
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
