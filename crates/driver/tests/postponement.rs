//! The postponement queue's record literals, `.field`s and method sections
//! (K1, K2 and K3, docs/proposals/postponement.md stages 2 and 3), and the
//! decision that waits for them (D2035), and comparisons that wait for
//! their placeholders (stage 6), with the library: §9's must-hold
//! tests for invariants 3, 6 and 8, and the errors a waiting check gives
//! once its type is known. The queue's own tests, on items made
//! by hand and modules without the library, are in `crates/elab/src/queue.rs`.

use std::path::Path;

use stitchwort_core::hash::def_hash;
use stitchwort_driver::driver::Session;
use stitchwort_syntax::Diagnostic;

/// Stack for the thread each source is checked on, so that a debug build
/// has room as a release build does.
const STACK: usize = 64 << 20;

/// Loads `source` in a fresh session, on a thread of its own, and gives
/// what `f` makes of the session, or of the errors.
fn checked<T: Send + 'static>(
    source: &str,
    f: impl FnOnce(std::result::Result<Session, Vec<Diagnostic>>) -> T + Send + 'static,
) -> T {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let mut session = Session::for_stack(STACK);
            f(session.load("test.sw", &source).map(|_| session))
        })
        .unwrap()
        .join()
        .unwrap()
}

/// Loads `source`: its errors, if any.
fn load(source: &str) -> std::result::Result<(), Vec<Diagnostic>> {
    checked(source, |loaded| loaded.map(|_| ()))
}

/// Loads `source`, which must check, and gives the content hash of each of
/// `names`, which says whether their terms are the same, spans and names
/// aside.
fn hashes(source: &str, names: &[&str]) -> Vec<String> {
    let names: Vec<String> = names.iter().map(|n| n.to_string()).collect();
    checked(source, move |loaded| {
        let session = loaded.unwrap_or_else(|e| panic!("{e:#?}"));
        (names.iter())
            .map(|name| {
                let id = session.elab.lookup_def(name).expect("defined");
                def_hash(&session.elab.globals, id).unwrap().unwrap().hex()
            })
            .collect()
    })
}

/// The definitions `name`'s body mentions.
fn mentions(source: &str, name: &str) -> Vec<String> {
    let name = name.to_string();
    checked(source, move |loaded| {
        let session = loaded.unwrap_or_else(|e| panic!("{e:#?}"));
        let id = session.elab.lookup_def(&name).expect("defined");
        let g = &session.elab.globals;
        (g.def(id).body().expect("a body").subterms())
            .filter_map(|(t, _)| match t {
                stitchwort_core::Term::Def(d) => Some(g.def(*d).name.to_string()),
                _ => None,
            })
            .collect()
    })
}

/// The text the first error's first label points at.
fn pointed_at<'a>(source: &'a str, errors: &[Diagnostic]) -> &'a str {
    let span = errors[0].labels[0].span;
    &source[span.start as usize..span.end as usize]
}

/// Invariant 6, must hold (§9): `p => p.row` with `p`'s type fixed only by
/// its use elaborates to the same term as with `p` annotated. The `.row`
/// waits with its receiver kept as syntax (its blocker, `p`'s type, was made
/// before it) and is elaborated again once the type is known.
#[test]
fn a_field_on_a_parameter_fixed_later_is_the_annotated_term() {
    let source = "\
import Std (Int, List)

type Position = { row: Int, column: Int }

def viaLet (start: Position): Int :=
  let row := p => p.row
  row start

def annotated (start: Position): Int :=
  let row := (p: Position) => p.row
  row start

def inList (starts: List Position): List Int := starts.map (p => p.row)

def inListAnnotated (starts: List Position): List Int := starts.map ((p: Position) => p.row)
";
    let h = hashes(
        source,
        &["viaLet", "annotated", "inList", "inListAnnotated"],
    );
    assert_eq!(h[0], h[1]);
    assert_eq!(h[2], h[3]);
}

/// Invariant 6, must hold (§9): Lean's chained case, `((f.x a1).x a2).x a3`
/// with `f`'s type known only later. The first `.x` waits with `f` as
/// syntax; each later one waits on the one before, whose placeholder is its
/// receiver, kept as a term. Accepted, with the term it has with `f`
/// annotated.
#[test]
fn a_chained_field_on_a_parameter_fixed_later_is_the_annotated_term() {
    let source = "\
import Std (Nat)

type Walk = | Start | Step (from: Walk) (by: Nat)

def Walk.x (w: Walk) (n: Nat): Walk := Step w n

def chained (w: Walk): Walk :=
  let go := f => ((f.x 1).x 2).x 3
  go w

def annotated (w: Walk): Walk :=
  let go := (f: Walk) => ((f.x 1).x 2).x 3
  go w

test \"three steps\" := chained Start == Step (Step (Step Start 1) 2) 3
";
    let h = hashes(source, &["chained", "annotated"]);
    assert_eq!(h[0], h[1]);
}

/// Invariant 8, must hold (§9): `rule => rule.before == page` with `rule`'s
/// type fixed only later and `before : Nat` decides with `Nat.decEq`, as
/// with the type annotated, also where `page`'s type is fixed later too
/// (the generic dictionary is projected at the end, §5.10).
#[test]
fn a_comparison_on_a_waiting_field_is_specialised() {
    let source = "\
import Std (Nat, Bool)

type Rule = { before: Nat, after: Nat }

def viaLet (rule: Rule) (page: Nat): Bool :=
  let ok := r => r.before == page
  ok rule

def annotated (rule: Rule) (page: Nat): Bool :=
  let ok := (r: Rule) => r.before == page
  ok rule

def bothLater (rule: Rule) (page: Nat): Bool :=
  let ok := r p => r.before == p
  ok rule page

def bothAnnotated (rule: Rule) (page: Nat): Bool :=
  let ok := (r: Rule) (p: Nat) => r.before == p
  ok rule page
";
    for name in ["viaLet", "annotated", "bothLater", "bothAnnotated"] {
        let defs = mentions(source, name);
        assert!(defs.iter().any(|d| d == "Nat.decEq"), "{name}: {defs:?}");
        assert!(
            !defs.iter().any(|d| d == "DecEq.decide"),
            "{name}: {defs:?}"
        );
    }
    // The same term as annotated. (`bothAnnotated`'s second binder adds an
    // annotation of its own around the inner lambda, so only the decision
    // is compared for that pair, above.)
    let h = hashes(source, &["viaLet", "annotated"]);
    assert_eq!(h[0], h[1]);
}

/// Invariant 8, must hold (§9), the allowed class of §5.10: `x ∈ r.items`
/// with `r`'s type fixed later reads `r.items` as a list, the reading for an
/// unknown container. When `r` turns out to hold a set, that is a mismatch
/// at the waiting `.items`, never an acceptance with a list. (Where a
/// `Bool` is expected instead, the decision waits for the `.items`, D2035:
/// `a_decision_waits_for_a_field_in_its_proposition`.)
#[test]
fn membership_in_a_waiting_field_is_a_mismatch_not_a_list() {
    let base = "\
import Std (Nat, Bool, Set)

type Box = { items: Set Nat }
";
    let annotated = format!(
        "{base}
def has (b: Box): Prop :=
  let check := (r: Box) => 3 ∈ r.items
  check b
"
    );
    if let Err(errors) = load(&annotated) {
        panic!("{errors:#?}");
    }
    let later = format!(
        "{base}
def has (b: Box): Prop :=
  let check := r => 3 ∈ r.items
  check b
"
    );
    let errors = load(&later).expect_err("rejected");
    assert_eq!(errors[0].code, "E-TYPE-MISMATCH", "{errors:#?}");
    assert_eq!(pointed_at(&later, &errors), "r.items");
}

/// Invariant 3, must hold (§9): an item is resumed only within the
/// application it was made in, so `postponed-lambda-second-error.sw` keeps
/// today's error, though with `c.size` resumed inside the attempts of
/// `twice` the program would be accepted.
#[test]
fn a_field_isnt_resumed_inside_another_applications_attempts() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/reject/postponed-lambda-second-error.sw");
    let source = std::fs::read_to_string(path).unwrap();
    let errors = load(&source).expect_err("rejected");
    assert_eq!(errors[0].code, "E-UNKNOWN-FIELD", "{errors:#?}");
    assert_eq!(pointed_at(&source, &errors), "size");
}

/// A waiting check whose type turns out not to fit says so against the type
/// now known, at its own place (§5.9): a `.field` the record hasn't, and a
/// literal whose type is not a record.
#[test]
fn a_resumed_check_reports_against_the_type_now_known() {
    let field = "\
import Std (Int)

type Position = { row: Int, column: Int }

def depth (start: Position): Int :=
  let depth := p => p.depth
  depth start
";
    let errors = load(field).expect_err("rejected");
    assert_eq!(errors[0].code, "E-UNKNOWN-FIELD", "{errors:#?}");
    assert_eq!(pointed_at(field, &errors), "depth");
    let literal = "\
import Std (Nat, List)

def firstOf (x: a) (xs: List a): a := x

def wrong: Nat := firstOf { row = 1 } [2]
";
    let errors = load(literal).expect_err("rejected");
    assert_eq!(errors[0].code, "E-NOT-A-RECORD", "{errors:#?}");
    assert_eq!(pointed_at(literal, &errors), "{ row = 1 }");
}

/// K3, the section's form of invariant 6's must-hold (§9): a section whose
/// argument's type is fixed only by a later argument elaborates to the same
/// term as with that type known from the start: `.snd` is `Pair.snd` itself
/// (D506), not a lambda around it. It waits whole, and is checked once
/// `pairs` has said what it takes.
#[test]
fn a_section_fixed_later_is_the_term_it_is_when_known() {
    let source = "\
import Std (Bool, List, Nat, Pair)

def anyOf (p: a -> Bool) (xs: List a): Bool := xs.any p

def section (pairs: List (Pair Nat Bool)): Bool := anyOf .snd pairs

def written (pairs: List (Pair Nat Bool)): Bool := anyOf Pair.snd pairs

def known (pairs: List (Pair Nat Bool)): Bool := pairs.any .snd

def knownWritten (pairs: List (Pair Nat Bool)): Bool := pairs.any Pair.snd
";
    let h = hashes(source, &["section", "written", "known", "knownWritten"]);
    assert_eq!(h[0], h[1]);
    assert_eq!(h[2], h[3]);
}

/// D2035, invariant 8 (§5.10): where a `Bool` is expected, a proposition
/// holding a waiting `.field` is decided only once the `.field` is filled.
/// With `r`'s type fixed later the decision is the one made with `r`
/// annotated (the same definitions); and if `r` turns out to hold a set,
/// the `.items` read as a list is a mismatch at it, not a decision of
/// something else.
#[test]
fn a_decision_waits_for_a_field_in_its_proposition() {
    let source = "\
import Std (Bool, List, Nat)

type Box = { items: List Nat }

def later (b: Box): Bool :=
  let check := r => 3 ∈ r.items
  check b

def annotated (b: Box): Bool :=
  let check := (r: Box) => 3 ∈ r.items
  check b
";
    let later = mentions(source, "later");
    let annotated = mentions(source, "annotated");
    assert!(later.iter().any(|d| d == "Decidable.toBool"), "{later:?}");
    assert_eq!(later, annotated);
    let set = "\
import Std (Bool, Nat, Set)

type Box = { items: Set Nat }

def has (b: Box): Bool :=
  let check := r => 3 ∈ r.items
  check b
";
    let errors = load(set).expect_err("rejected");
    assert_eq!(errors[0].code, "E-TYPE-MISMATCH", "{errors:#?}");
    assert_eq!(pointed_at(set, &errors), "r.items");
}

/// Stage 6 and D2016's end state: a placeholder is frozen until its check
/// fills it, and a comparison that meets it waits for it. A lambda whose
/// parameter's type comes from a later argument, compared with a statement
/// that mentions it (SW-138's `anyPerm`), was the shape where unification
/// solved a `.field`'s placeholder before its item could; now the
/// comparison waits, and the proof is the term it is with `r` annotated.
#[test]
fn a_comparison_waits_for_a_frozen_placeholder() {
    let source = "\
import Std (List, Nat)

type R = { lo: Nat, hi: Nat }

def R.contains (r: R) (n: Nat): Bool := Nat.leq r.lo n

theorem later (xs: List R) (ys: List R) (h: List.Perm xs ys): List.any xs (r => r.contains 3) = List.any ys (r => r.contains 3) :=
  List.anyPerm xs ys h (r => r.contains 3)

theorem annotated (xs: List R) (ys: List R) (h: List.Perm xs ys): List.any xs (r => r.contains 3) = List.any ys (r => r.contains 3) :=
  List.anyPerm xs ys h ((r: R) => r.contains 3)
";
    let hashes = hashes(source, &["later", "annotated"]);
    assert_eq!(hashes[0], hashes[1]);
}

/// Stage 6: a waiting comparison that is false once the placeholder is
/// filled is its caller's error, against the type now known, where the
/// comparison was: here the proof's type against the statement's, which
/// says `4` where the proof says `3`. Main gives the same message, with
/// the placeholder solved first.
#[test]
fn a_waiting_comparison_that_fails_is_a_mismatch_against_the_type_now_known() {
    let source = "\
import Std (List, Nat)

type R = { lo: Nat, hi: Nat }

def R.contains (r: R) (n: Nat): Bool := Nat.leq r.lo n

theorem wrong (xs: List R) (ys: List R) (h: List.Perm xs ys): List.any xs (r => r.contains 4) = List.any ys (r => r.contains 4) :=
  List.anyPerm xs ys h (r => r.contains 3)
";
    let errors = load(source).expect_err("rejected");
    assert_eq!(errors[0].code, "E-TYPE-MISMATCH", "{errors:#?}");
    let message = format!("{:?}", errors[0]);
    assert!(!message.contains('?'), "no unknown is shown: {message}");
    assert!(message.contains("R.contains r 4") && message.contains("R.contains r 3"));
    assert!(pointed_at(source, &errors).starts_with("List.anyPerm xs ys h"));
}
