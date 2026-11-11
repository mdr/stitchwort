//! A `Bool` test being `True` is printed as the test alone where that text
//! reads back to the same term (docs/proposals/bool-as-proposition.md §4.4):
//! each statement here is printed, the printed text is loaded in its place,
//! and the two definitions must have the same content hash.

use stitchwort_core::hash::def_hash;
use stitchwort_core::pretty;
use stitchwort_driver::driver::Session;

const HEADER: &str = "import Std (Bool, Nat, List)\n\ndef isSmall (n: Nat): Bool := n <= 3\n\n";

/// Loads `def t : {sig} := {body}`, returns its printed body and content
/// hash.
fn printed_and_hash(sig: &str, body: &str) -> (String, String) {
    let mut session = Session::new();
    let source = format!("{HEADER}def t : {sig} := {body}\n");
    if let Err(errors) = session.load("test.sw", &source) {
        panic!("{body}: {errors:#?}");
    }
    let g = &session.elab.ev();
    let (id, def) = g
        .env
        .defs()
        .iter()
        .enumerate()
        .find(|(_, d)| &**d.name() == "t")
        .expect("def t");
    let printed = pretty::term(g, &[], def.body().expect("a body"));
    let hash = def_hash(g, stitchwort_core::DefId(id))
        .unwrap()
        .unwrap()
        .hex();
    (printed, hash)
}

/// `body`, a proposition of type `sig`, prints as `expected` (if given), and
/// that text means the same.
fn round_trip(sig: &str, body: &str, expected: Option<&str>) {
    let (printed, hash) = printed_and_hash(sig, body);
    if let Some(expected) = expected {
        assert_eq!(printed, expected, "printing {body}");
    }
    let (_, again) = printed_and_hash(sig, &printed);
    assert_eq!(hash, again, "{printed} doesn't mean what {body} does");
}

/// [`round_trip`] for a statement about two `Bool`s `a` and `b`, a number
/// `n` and a list `xs`: as a lambda's result where `Prop` is expected (an
/// argument of type `Prop`), and as the body of a `∀` (a type, read by
/// `check_type`; the `∀` prints the binders the body doesn't use as
/// arrows, so only its meaning is compared).
fn statement(body: &str, expected: &str) {
    round_trip(
        "Bool → Bool → Nat → List Nat → Prop",
        &format!("a b n xs => {body}"),
        Some(&format!("a b n xs => {expected}")),
    );
    round_trip(
        "Prop",
        &format!("∀ (a b: Bool) (n: Nat) (xs: List Nat) => {body}"),
        None,
    );
}

#[test]
fn a_variable() {
    statement("a = True", "a");
}

#[test]
fn a_call() {
    statement("isSmall n = True", "isSmall n");
    statement("xs.any (x => x <= n) = True", "xs.any (x => x <= n)");
    statement("Bool.not a = True", "a.not");
}

#[test]
fn equality_test() {
    statement("(n == 3) = True", "(n.decEq 3).holds");
}

#[test]
fn under_the_logical_operators() {
    statement("And (a = True) (b = True)", "a ∧ b");
    statement("Or (a = True) (isSmall n = True)", "a ∨ isSmall n");
    statement("Not (a = True)", "¬a");
    statement("a = True → b = True", "a → b");
    statement(
        "And ((a && b) = True) (isSmall n = True)",
        "(a && b) = True ∧ isSmall n",
    );
}

#[test]
fn under_a_lambda() {
    statement(
        "xs.all (x => x <= n && isSmall x) = True",
        "xs.all (x => x <= n && isSmall x)",
    );
    statement("∀ (m: Nat) => isSmall m = True", "∀ (m: Nat) => isSmall m");
}

#[test]
fn an_if_or_a_match_as_the_test() {
    statement(
        "(if isSmall n then a else b) = True",
        "if isSmall n then a else b",
    );
    // A `match` prints as its lifted helper's call, which can't be read
    // back; what it means bare is still the whole test being `True`.
    let (_, written) = printed_and_hash(
        "Bool → Bool → List Nat → Prop",
        "a b xs => (match xs with | [] => a | [_, .._] => b) = True",
    );
    let (_, bare) = printed_and_hash(
        "Bool → Bool → List Nat → Prop",
        "a b xs => match xs with | [] => a | [_, .._] => b",
    );
    assert_eq!(written, bare);
}

#[test]
fn bool_operators_keep_true() {
    statement("(a && b) = True", "(a && b) = True");
    statement("(a || b) = True", "(a || b) = True");
    statement("(if a then b else False) = True", "(a && b) = True");
    statement("(Bool.not a) = True ∧ b = True", "a.not ∧ b");
}

#[test]
fn false_and_constants_are_written_out() {
    statement("a = False", "a = False");
    statement("False = True", "False = True");
}

#[test]
fn sides_of_an_equation_keep_true() {
    statement("(a = True) = (b = True)", "(a = True) = (b = True)");
}
