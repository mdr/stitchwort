//! The printer's lambdas round-trip (docs/proposals/lambda-syntax.md §8.3,
//! D100): a definition's elaborated body, printed, parses back and elaborates
//! to a definition with the same content hash.

use stitchwort_core::hash::def_hash;
use stitchwort_core::pretty;
use stitchwort_driver::driver::Session;
use stitchwort_syntax::equivalence::parse_shape;

/// Loads `def t : sig := body`, returns its printed body and content hash.
fn printed_and_hash(sig: &str, body: &str) -> (String, String) {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", &format!("def t : {sig} := {body}\n")) {
        panic!("{body}: {errors:#?}");
    }
    let g = &session.elab.globals;
    let (id, def) = g
        .defs
        .iter()
        .enumerate()
        .find(|(_, d)| &*d.name == "t")
        .expect("def t");
    let printed = pretty::term(g, &[], def.body().expect("a body"));
    let hash = def_hash(g, stitchwort_core::DefId(id))
        .unwrap()
        .unwrap()
        .hex();
    (printed, hash)
}

/// Prints `body`, checks the printed text is `expected`, and that it means
/// the same: same hash when it is loaded in place of the original.
fn round_trip(sig: &str, body: &str, expected: &str) {
    let (printed, hash) = printed_and_hash(sig, body);
    assert_eq!(printed, expected, "printing {body}");
    let (_, again) = printed_and_hash(sig, &printed);
    assert_eq!(hash, again, "{printed} doesn't mean what {body} does");
}

#[test]
fn a_lambda_as_an_argument_is_bracketed() {
    round_trip(
        "((Nat -> Nat) -> Nat) -> Nat",
        "f => f (x => x)",
        "f => f (x => x)",
    );
}

#[test]
fn a_lambda_that_is_applied_is_bracketed() {
    // The printer drops the annotation, so the printed text doesn't elaborate
    // again; it must still parse to the bracketed application.
    let (printed, _) = printed_and_hash("Nat -> Nat", "y => ((x: Nat) => x + 1) y");
    assert_eq!(printed, "y => (x => x + 1) y");
    let shape = |body: &str| parse_shape(&format!("def t : Nat -> Nat := {body}\n")).unwrap();
    assert_eq!(shape(&printed), shape("y => (x => x + 1) y"));
    assert_ne!(shape(&printed), shape("y => x => x + 1 y"));
}

#[test]
fn two_lambda_arguments() {
    round_trip(
        "((Nat -> Nat) -> (Nat -> Nat) -> Nat) -> Nat",
        "f => f (x => x) (y => y)",
        "f => f (x => x) (y => y)",
    );
}

#[test]
fn nested_lambdas_are_one_run() {
    round_trip("Nat -> Nat -> Nat", "a b => a", "a b => a");
    round_trip(
        "Nat -> Nat -> Nat -> Nat",
        "a => b => c => a + c",
        "a b c => a + c",
    );
}

#[test]
fn lambdas_in_both_branches_of_an_if_keep_their_brackets() {
    round_trip(
        "Bool -> Nat -> Nat",
        "c => if c then (x => x) else (y => y + 1)",
        "c => if c then (x => x) else (y => y + 1)",
    );
}
