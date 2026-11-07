//! A definition's inert positions are only its leading applications: an
//! argument after a `J` in the spine applies the `J`'s result, so it's
//! compared, though it sits at an inert position's index
//! (docs/proposals/proof-irrelevance.md §7.2). Well-typed values never
//! have this shape (a `J` needs an equation, and `f x` is a function); the
//! bound is pinned so that no comparison relies on it being absent.

use crate::common::*;
use stitchwort_core::value::{Elim, Head, Value, conv};
use stitchwort_core::{Icit, Sort, check, reference};

#[test]
fn an_argument_after_a_j_is_compared() {
    let mut p = Prelude::new();
    let n_ty = p.nat_ty();
    let q = data(&mut p.g, "Q", vec![], Sort::Prop);
    check::define_ctors(&mut p.g, q, vec![ctor("MkQ", vec![])]).expect("Q");
    let q_ty = stitchwort_core::term::Term::data(q, vec![]);
    let f = define(
        &mut p.g,
        "f",
        pi(
            "n",
            n_ty.clone(),
            pi("k", n_ty.clone(), pi("h", q_ty, n_ty)),
        ),
        lam("n", lam("k", lam("h", v(2)))),
    )
    .expect("f");
    let ev = &p.g.ev();
    assert_eq!(ev.def(f).inert_params(), &[false, false, true]);
    // `x`, `m`, `b`, `p`, `q` at levels 0-4.
    let spine = |last: usize| {
        let elims = vec![
            Elim::App(Value::var(0), Icit::Explicit),
            Elim::J {
                motive: Box::new(Value::var(1)),
                base: Box::new(Value::var(2)),
            },
            Elim::App(Value::var(last), Icit::Explicit),
        ];
        Value::Neutral(Head::Def(f), elims.into())
    };
    let (a, b) = (spine(3), spine(4));
    assert!(!conv(ev, 5, &a, &b).unwrap(), "value::conv");
    assert!(!reference::conv(ev, 5, &a, &b).unwrap(), "reference::conv");
    assert!(conv(ev, 5, &a, &spine(3)).unwrap());
}
