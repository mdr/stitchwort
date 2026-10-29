//! Indexed families in the surface language (docs/proposals/indexed-families.md
//! §7): what the examples under `examples/` don't pin down, chiefly
//! warnings, which they don't record, and smaller errors.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::Diagnostic;

const VEC: &str = "type Vec (a: Type): Nat -> Type =\n  \
                   | VNil: Vec a 0\n  \
                   | VCons (x: a) (xs: Vec a n): Vec a (Succ n)\n\n";

fn load(text: &str) -> (Session, Result<(), Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load("test.sw", text).map(|_| ());
    (session, result)
}

fn with_vec(rest: &str) -> String {
    format!("{VEC}{rest}")
}

fn error(text: &str) -> Diagnostic {
    let (_, result) = load(text);
    let errors = result.expect_err("should be rejected");
    errors.into_iter().next().expect("an error")
}

fn unreachable(session: &Session) -> Vec<&Diagnostic> {
    (session.warnings.iter())
        .filter(|w| w.code == "W-UNREACHABLE")
        .collect()
}

#[test]
fn an_arm_that_can_never_match_warns_and_is_dropped() {
    // The `VNil` arm's body isn't even well typed: it's never checked.
    let (session, result) = load(&with_vec(
        "def head: Vec a (Succ n) -> a\n  | VNil => 0\n  | VCons x _ => x\n",
    ));
    result.unwrap();
    let [w] = &unreachable(&session)[..] else {
        panic!("{:#?}", session.warnings);
    };
    assert_eq!(w.message, "this arm can never match");
    assert!(
        w.labels[0].message.contains("would need `Succ n = 0`"),
        "{w:?}"
    );
}

#[test]
fn an_arm_reached_in_another_branch_does_not_warn() {
    // `VNil, _` is dropped where the first vector is `VCons`, but it's the
    // `VNil` branch's arm.
    let (session, result) = load(&with_vec(
        "def f: Vec a n -> Vec a n -> Nat\n  | VNil, _ => 0\n  | VCons _ _, _ => 1\n",
    ));
    result.unwrap();
    assert!(unreachable(&session).is_empty(), "{:#?}", session.warnings);
}

#[test]
fn a_constructor_declared_with_n_plus_one_matches() {
    // `+` computes on its second argument too (SW-787): `n + 1` is `Succ n`.
    let (_, result) = load(
        "type Vec (a: Type): Nat -> Type =\n  | VNil: Vec a 0\n  \
         | VCons (x: a) (xs: Vec a n): Vec a (n + 1)\n\n\
         def head: Vec a (Succ k) -> a\n  | VCons x _ => x\n",
    );
    result.unwrap();
}

#[test]
fn stuck_sums_say_both_sides_are_unknown() {
    let e = error(&with_vec(
        "def lengthOfSum: Vec a (n + m) -> Nat\n  | VNil => 0\n  | VCons _ _ => 1\n",
    ));
    assert_eq!(e.code, "E-INDEX-STUCK");
    assert!(
        e.notes[0]
            .contains("so `n + m` doesn't compute while both are unknown: match on `n` first"),
        "{e:?}"
    );
}

#[test]
fn implicit_fields_by_name() {
    let (_, result) = load(&with_vec(
        "def one: Vec Nat 1 := VCons [n := 0] 5 VNil\n\
         def len: Vec a n -> Nat\n  | VNil => 0\n  | VCons [n := k] _ _ => Succ k\n\
         test \"len\" := len one == 1\n",
    ));
    result.unwrap();
    let e = error(&with_vec("def one: Vec Nat 1 := VCons [m := 0] 5 VNil\n"));
    assert_eq!(e.code, "E-UNKNOWN-NAME");
    let e = error(&with_vec(
        "def len: Vec a n -> Nat\n  | VNil => 0\n  | VCons k _ _ => Succ k\n",
    ));
    assert_eq!(e.code, "E-ARITY");
    assert!(e.notes[0].contains("[n := p]"), "{e:?}");
}

#[test]
fn declarations_need_their_parts() {
    let e = error("type Vec (a: Type): Nat -> Type =\n  | VNil\n");
    assert_eq!(e.code, "E-TYPE-MISMATCH");
    assert!(e.message.contains("needs a result type"), "{e:?}");
    let e = error("type R: Nat -> Type = { x: Nat }\n");
    assert_eq!(e.code, "E-RECORD-INDICES");
    // A type without indices may write its constructors' result types.
    let (_, result) = load("type T (a: Type) =\n  | MkT (x: a): T a\n");
    result.unwrap();
}
