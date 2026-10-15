//! Programs using abilities that must be refused, each with the error code it
//! must be refused with. (examples/reject has the ones worth reading as
//! examples, with their full messages.)

use stitchwort_driver::driver::Session;

const HEADER: &str = "
ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Choose where
  choose : () -> {Choose} Bool

ability Ask where
  ask : () -> {Ask} Nat

PayloadType : Nat -> Type
PayloadType 0        = Nat
PayloadType (Succ n) = Bool

payload : (n : Nat) -> PayloadType n
payload 0        = 0
payload (Succ n) = True
";

/// The error code `source` (after the header) is refused with.
fn refused(source: &str) -> Option<&'static str> {
    let mut session = Session::new();
    let text = format!("{HEADER}\n{source}\n");
    match session.load("test.sw", &text) {
        Ok(_) => None,
        Err(diagnostics) => diagnostics.first().map(|d| d.code),
    }
}

#[track_caller]
fn assert_refused(source: &str, code: &str) {
    assert_eq!(refused(source), Some(code), "{source}");
}

#[test]
fn the_header_checks() {
    assert_eq!(refused(""), None);
}

#[test]
fn rows_must_list_abilities_with_the_right_arguments() {
    assert_refused("f : () -> {Nat} Nat\nf u = 0", "E-ABILITY");
    assert_refused("f : () -> {State} Nat\nf u = 0", "E-ARITY");
    assert_refused(
        "f : () -> {State Nat, State Bool} Nat\nf u = 0",
        "E-DUPLICATE",
    );
    // The result of an effectful function is data: not in a larger universe,
    // and not a proof. (`Prop` itself is fine: it's the type of propositions.)
    assert_refused("f : () -> {Ask} Type\nf u = Nat", "E-UNIVERSE");
    assert_refused("f : () -> {Ask} (1 = 1)\nf u = rfl", "E-UNIVERSE");
    assert_eq!(refused("f : () -> {Ask} Prop\nf u = Unit"), None);
}

#[test]
fn abilities_are_not_types_or_values() {
    assert_refused("f : State Nat -> Nat\nf s = 0", "E-ABILITY");
    // An operation on its own is a function, not a number.
    assert_refused("f : Nat\nf = ask", "E-TYPE-MISMATCH");
    assert_refused("f : () -> {Ask} Nat\nf u = ask () ()", "E-ARITY");
}

#[test]
fn an_ability_is_used_with_one_set_of_arguments() {
    let source =
        "f : () -> {State Bool} Bool\nf u = get ()\n\ng : () -> {State Nat} Bool\ng u = f ()";
    assert_refused(source, "E-TYPE-MISMATCH");
    // Said in terms of the ability, not of the generated types.
    let mut session = Session::new();
    let Err(diagnostics) = session.load("test.sw", &format!("{HEADER}\n{source}\n")) else {
        panic!("accepted");
    };
    assert!(
        diagnostics[0]
            .message
            .contains("`State` is used with different arguments"),
        "{:?}",
        diagnostics[0].message
    );
}

#[test]
fn row_variables_must_match() {
    // `p` may perform whatever `e1` is, but `f`'s result allows only `e2`.
    assert_refused(
        "f : (() -> {e1} Nat) -> (() -> {e2} Nat) -> {e2} Nat\nf p q = p ()",
        "E-ABILITY",
    );
}

#[test]
fn operations_take_one_argument() {
    assert_refused("f : () -> {State Nat} ()\nf u = put 1 2", "E-ARITY");
}

#[test]
fn an_if_proof_cant_perform_operations() {
    assert_refused(
        "f : () -> {Ask} Nat\nf u = if h : ask () = 1 then 1 else 0",
        "E-ABILITY",
    );
}

#[test]
fn a_result_type_cant_depend_on_an_operation() {
    // `payload n : PayloadType n`, for an `n` only known when `ask` runs.
    assert_refused(
        "f : () -> {Ask} Nat\nf u =\n  let x = payload (ask ())\n  0",
        "E-EFFECT-ESCAPE",
    );
}

#[test]
fn operation_types_have_one_shape() {
    assert_refused("ability Bad where\n  op : Nat", "E-ABILITY");
    assert_refused("ability Bad where\n  op : Nat -> Nat", "E-ABILITY");
    // An operation performs just its own ability.
    assert_refused("ability Bad where\n  op : () -> {Ask} Nat", "E-ABILITY");
    // Landin's knot, through the result this time.
    assert_refused(
        "ability Cell where\n  read : () -> {Cell} (() -> {Cell} ())",
        "E-ABILITY",
    );
    // Names are checked like any other.
    assert_refused(
        "ability State where\n  op : () -> {State} Nat",
        "E-DUPLICATE",
    );
}

const HANDLED: &str = "f : (() -> {Choose | e} Nat) -> {e} Nat\nf prog =\n  handle prog () with\n";

#[test]
fn handlers_are_complete_and_unambiguous() {
    let handler = |clauses: &str| format!("{HANDLED}{clauses}");
    assert_refused(
        &handler("    | return x -> x\n    | return y -> y\n    | choose u => k -> k True"),
        "E-DUPLICATE",
    );
    assert_refused(
        &handler(
            "    | return x -> x\n    | choose u => k -> k True\n    | choose v => k -> k False",
        ),
        "E-DUPLICATE",
    );
    assert_refused(
        &handler("    | return x -> x\n    | length u => k -> k True"),
        "E-ABILITY",
    );
    assert_refused(
        &handler("    | return x -> x\n    | choose u => k -> k True\n    | ask u => k -> k 0"),
        "E-ABILITY",
    );
    // A clause's argument is a name, `_` or `()`.
    assert_refused(
        &handler("    | return x -> x\n    | choose (Succ n) => k -> k True"),
        "E-HANDLER",
    );
    // `()` matches only the unit value: `put`'s argument is the state.
    assert_refused(
        "g : (() -> {State Nat | e} Nat) -> {e} Nat\ng prog =\n  handle prog () with\n    | return x -> x\n    | get u => k -> k 0\n    | put () => k -> k ()",
        "E-TYPE-MISMATCH",
    );
}

#[test]
fn a_clause_result_must_have_the_handler_type() {
    assert_refused(
        &format!("{HANDLED}    | return x -> True\n    | choose u => k -> k True"),
        "E-TYPE-MISMATCH",
    );
}

#[test]
fn a_block_ends_with_an_expression() {
    assert_refused("f : () -> {Ask} Nat\nf u =\n  let x = ask ()", "E-PARSE");
}

#[test]
fn pure_code_handles_what_it_performs() {
    assert_refused("f : Nat\nf = ask ()", "E-ABILITY");
    assert_refused("f : (() -> {Ask} Nat) -> Nat\nf p = p ()", "E-ABILITY");
}
