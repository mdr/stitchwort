//! `W-REDUNDANT`: an arm, or an or-pattern alternative, that earlier arms
//! always take first. What `examples/accept/redundant-arms.sw` doesn't pin
//! down: where it must stay quiet.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::Diagnostic;

fn load(text: &str) -> (Session, Result<(), Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load("test.sw", text).map(|_| ());
    (session, result)
}

fn redundant(text: &str) -> Vec<Diagnostic> {
    let (session, result) = load(text);
    result.unwrap();
    (session.warnings.into_iter())
        .filter(|w| w.code == "W-REDUNDANT")
        .collect()
}

#[test]
fn every_arm_needed_is_quiet() {
    let found = redundant(
        "def f: Nat → Nat → Nat\n  | 0, _ => 0\n  | _, 0 => 1\n  | _, _ => 2\n\n\
         def g: Char → Nat\n  | 'a' | 'b' => 1\n  | 'c' => 2\n  | _ => 3\n\n\
         def h: Pair Nat Bool → Nat\n  | (0 | 1, True | False) => 1\n  | (n, _) => n\n",
    );
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn an_arm_dropped_for_its_indices_is_unreachable_not_redundant() {
    let (session, result) = load(
        "type Vec (a: Type): Nat -> Type =\n  | VNil: Vec a 0\n  \
         | VCons (x: a) (xs: Vec a n): Vec a (Succ n)\n\n\
         def head: Vec a (Succ n) -> a\n  | VNil => 0\n  | VCons x _ => x\n",
    );
    result.unwrap();
    let codes: Vec<&str> = session.warnings.iter().map(|w| w.code).collect();
    assert_eq!(codes, ["W-UNREACHABLE"]);
}

#[test]
fn record_updates_and_derived_instances_are_quiet() {
    let found = redundant(
        "type Shape =\n  | Circle (radius: Nat) (tag: Nat)\n  | Square (side: Nat) (tag: Nat)\n\n\
         def retag (shape: Shape): Shape := { shape | tag = 1 }\n\n\
         def same (a: Shape) (b: Shape): Bool := a == b\n",
    );
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn a_redundant_arm_in_a_proof_warns() {
    let found =
        redundant("theorem t (n: Nat): n = n :=\n  match n with\n    | _ => rfl\n    | 0 => rfl\n");
    assert_eq!(found.len(), 1, "{found:#?}");
}

#[test]
fn a_nested_or_pattern_alternative_warns() {
    let found = redundant("def f: Option Nat → Nat\n  | Some (1 | 1) => 1\n  | _ => 0\n");
    let [w] = &found[..] else {
        panic!("{found:#?}")
    };
    assert!(w.message.starts_with("this alternative"), "{w:?}");
    assert_eq!(w.labels.len(), 2, "{w:?}");
}
