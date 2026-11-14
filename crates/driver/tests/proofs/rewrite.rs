//! `rewrite` (docs/proposals/calc-rewrite.md §6, stage 2): what the examples
//! can't say, because it needs a setting of the elaborator or a look at the
//! terms produced.

use stitchwort_driver::driver::Session;

/// The codes of the errors loading `text` gives, with the search budget set
/// (`None`: the default).
fn codes(budget: Option<u64>, text: &str) -> Vec<&'static str> {
    let mut session = Session::new();
    session.elab.options.rewrite_budget = budget;
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

theorem t (g: Nat -> Nat) (f: Nat -> Nat) (h: ∀ (n: Nat) => f (sumMap g n) = 0) (q: Nat -> Prop) (k: q 0):
    q (f (sumMap g 41)) :=
  rewrite h 40 in k
";

#[test]
fn the_budget_message_shows_both_terms_shortened() {
    let mut session = Session::new();
    session.elab.options.rewrite_budget = Some(20);
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

/// A motive that doesn't type-check is reported with its body, which is
/// under the motive's two binders: the goal's outermost variable `g` sits
/// past the goal's own context there (SW-2842: an index went below zero
/// printing it).
#[test]
fn a_motive_mentioning_the_outermost_variable_is_reported() {
    let text = "\
theorem bad (g: (d: Nat) → [auto ok: d ≠ 0] → Nat) (d: Nat) (e: Nat) (h: d = e) [auto p: d ≠ 0]:
    g d + 1 = g d + 1 :=
  rewrite h
";
    assert_eq!(codes(None, text), vec!["E-REWRITE-MOTIVE"]);
}

#[test]
fn rewrite_is_a_keyword() {
    assert_eq!(codes(None, "def rewrite: Nat := 1\n"), vec!["E-PARSE"]);
    // So is `in`, since membership (`x in xs`, SW-461); `at` is not.
    assert_eq!(codes(None, "def f (in: Nat): Nat := in\n"), vec!["E-PARSE"]);
    assert_eq!(
        codes(None, "def f (at: Nat): Nat := at\n"),
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

/// `f (sumMap g 40)` is shown in the goal; `hide f g` computes to another
/// `f` of a long sum, which only a comparison tells apart from the rule's
/// left side.
const CHECK_RUNS_OUT: &str = "\
def sumMap (g: Nat -> Nat): Nat -> Nat
  | Zero => 0
  | Succ n => g (Succ n) + sumMap g n

def hide (f: Nat -> Nat) (g: Nat -> Nat): Nat := f (sumMap g 39)

theorem t (g: Nat -> Nat) (f: Nat -> Nat) (h: ∀ (n: Nat) => f (sumMap g n) = 0) (q: Nat -> Nat -> Prop)
    (k: q 0 (hide f g)): q (f (sumMap g 40)) (hide f g) :=
  rewrite h 40 in k
";

/// The codes of the errors and warnings loading `text` gives, with the
/// search budget set.
fn codes_and_warnings(budget: Option<u64>, text: &str) -> (Vec<&'static str>, Vec<&'static str>) {
    let mut session = Session::new();
    session.elab.options.rewrite_budget = budget;
    let errors = match session.load("test.sw", text) {
        Ok(_) => Vec::new(),
        Err(errors) => errors.iter().map(|e| e.code).collect(),
    };
    let warnings = session.warnings.iter().map(|w| w.code).collect();
    (errors, warnings)
}

#[test]
fn a_rewrite_whose_check_runs_out_of_the_budget_is_used_as_written() {
    // With the whole budget, the completeness check finds no hidden copy.
    assert_eq!(codes_and_warnings(None, CHECK_RUNS_OUT), (vec![], vec![]));
    // With a small one (but enough for the search as written, which finds
    // `f (sumMap g 40)` without computing), the check, comparing `hide f g`'s
    // unfolding, and the usual search both run out, where the `rewrite`
    // failed with `E-REWRITE-BUDGET`: the rewrite as written is used, with a
    // warning (goal-as-written.md, stage 4).
    assert_eq!(
        codes_and_warnings(Some(100), CHECK_RUNS_OUT),
        (vec![], vec!["W-REWRITE-UNCONFIRMED"])
    );
}
