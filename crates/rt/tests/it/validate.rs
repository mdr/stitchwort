//! `Program::validate`: the checks lowering and the codec rely on.

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::ir::{Expr, GlobalKind, Program};
use stitchwort_rt::{Limits, decode, encode, lower_main};

const STACK: usize = 256 * 1024 * 1024;

const SOURCE: &str = r#"import Std (IO, Nat, Text)

type Pair = { a: Nat, b: Nat }

def first: Pair → Nat
  | { a, .. } => a

def main(): {IO} () := IO.print (Nat.toText (first { a = 1, b = 2 }))
"#;

fn lowered() -> (Program, Limits) {
    let mut session = Session::for_stack(STACK);
    session.use_test_std_cache();
    session
        .load("test.sw", SOURCE)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("main");
    let limits = Limits::from_core(session.elab.options.limits);
    let program = lower_main(
        &session.elab.ev(),
        session.elab.options.limits,
        main.term(),
        main.row,
    )
    .expect("lowers");
    (program, limits)
}

/// An arm that binds one field twice is rejected: `Unpack` moves the field
/// into the first slot and the second would read `Erased`.
#[test]
fn a_field_bound_twice_is_rejected() {
    with_stack(STACK, || {
        let (mut program, limits) = lowered();
        assert_eq!(program.validate(), Ok(()));
        let body = program
            .globals
            .iter_mut()
            .find_map(|g| match &mut g.kind {
                GlobalKind::Function { body, .. } => match &body.expr {
                    Expr::Match(_, _, arms) if arms.iter().any(|a| !a.fields.is_empty()) => {
                        Some(body)
                    }
                    _ => None,
                },
                _ => None,
            })
            .expect("a function whose body is a field-binding match");
        let Expr::Match(_, _, arms) = &mut body.expr else {
            unreachable!()
        };
        let arm = arms.first_mut().expect("an arm");
        let field = arm.fields.first().expect("a bound field").0;
        let slot = body.frame;
        body.frame += 1;
        arm.fields.push((field, slot));
        let err = program
            .validate()
            .expect_err("accepted a field bound twice");
        assert!(err.contains(&format!("binds field {field} twice")), "{err}");
        let err = decode(&encode(&program, &limits))
            .err()
            .expect("the codec accepted it");
        assert!(err.to_string().contains("binds field"), "{err}");
    });
}
