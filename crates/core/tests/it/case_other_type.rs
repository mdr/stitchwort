//! A `case` given a constructor of another type (SW-2961). Only an
//! ill-typed term does that, which the kernel never runs; but the
//! elaborator evaluates terms before the kernel checks them, and
//! unification's first-order rule can solve an unknown whose type it
//! doesn't know with a value of another type. The `case` must stay stuck,
//! not take the constructor's index as one of its own type's: `Greater`
//! (index 2 of 3) against a two-constructor type indexed past the end of
//! its branches, and a panic.

use crate::common::*;
use stitchwort_core::term::Term;
use stitchwort_core::value::{Value, conv, eval};
use stitchwort_core::{DataId, DefId, Kernel, Sort, check, reference};

/// `Two := X | Y`, `Three := A | B | C`, and `pick (t: Two): Nat`, which
/// matches `t`.
fn setup() -> (Kernel, DataId, DefId) {
    let mut p = Prelude::new();
    let two = data(&mut p.g, "Two", vec![], Sort::Type(0));
    check::define_ctors(&mut p.g, two, vec![ctor("X", vec![]), ctor("Y", vec![])]).expect("Two");
    let three = data(&mut p.g, "Three", vec![], Sort::Type(0));
    let ctors = vec![ctor("A", vec![]), ctor("B", vec![]), ctor("C", vec![])];
    check::define_ctors(&mut p.g, three, ctors).expect("Three");
    let body = lam(
        "t",
        case(0, two, vec![(vec![], p.num(0)), (vec![], p.num(1))]),
    );
    let ty = arrow(Term::data(two, vec![]), p.nat_ty());
    let pick = define(&mut p.g, "pick", ty, body).expect("pick checks");
    (p.g, three, pick)
}

#[test]
fn a_case_on_another_types_constructor_is_stuck() {
    let (g, three, pick) = setup();
    let ev = &g.ev();
    let env = vec![Value::Ctor(three, 2, Vec::new().into())];
    let call = app(Term::Def(pick), [v(0)]);
    let value = eval(ev, &env, &call).expect("evaluates");
    assert!(
        matches!(&value, Value::Neutral(..) | Value::Call(..)),
        "a stuck call, not a branch: {value:?}"
    );
    assert!(conv(ev, 0, &value, &value).expect("compares"));
    let refr = reference::eval(ev, &env, &call).expect("the reference evaluates");
    assert!(reference::conv(ev, 0, &refr, &refr).expect("the reference compares"));
}
