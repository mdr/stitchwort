//! Calls of a definition with no body yet, a member of the group being
//! checked, compared the way they will be once it's admitted
//! (docs/proposals/proof-irrelevance.md §7.10). The call can unfold later,
//! so its arguments are compared in shortcut mode, which compares
//! constructor proof fields: while pending, the kernel must not find equal
//! two calls that the admitted body tells apart.

use crate::common::*;
use stitchwort_core::term::Term;
use stitchwort_core::value::{Value, conv, eval};
use stitchwort_core::{Kernel, Sort, check, reference};

/// `Box (a: Prop) := MkBox (x: a)`, a type with a proof field, and
/// `f (a: Prop) (b: Box a): a`, declared and not yet defined. The body it
/// gets, `match b | MkBox x => x`, returns the proof.
fn setup() -> (Kernel, stitchwort_core::DataId, stitchwort_core::DefId) {
    let mut p = Prelude::new();
    let boxed = data(&mut p.g, "Box", vec![("a", prop())], Sort::Type(0));
    check::define_ctors(&mut p.g, boxed, vec![ctor("MkBox", vec![("x", v(0))])]).expect("Box");
    let f = declare(
        &mut p.g,
        "f",
        pi("a", prop(), arrow(Term::data(boxed, vec![v(0)]), v(0))),
    );
    (p.g, boxed, f)
}

/// `f a (MkBox p)` and `f a (MkBox q)`, with `a`, `p`, `q` at levels 0-2,
/// compared by the kernel and by the reference evaluator.
fn answers(g: &Kernel, boxed: stitchwort_core::DataId, f: stitchwort_core::DefId) -> [bool; 2] {
    let env: Vec<Value> = (0..3).map(Value::var).collect();
    let call = |proof: usize| app(Term::Def(f), [v(2), Term::ctor(boxed, 0, vec![v(proof)])]);
    let ev = &g.ev();
    let (l, r) = (call(1), call(0));
    let kernel = conv(
        ev,
        3,
        &eval(ev, &env, &l).unwrap(),
        &eval(ev, &env, &r).unwrap(),
    );
    let refr = reference::conv(
        ev,
        3,
        &reference::eval(ev, &env, &l).unwrap(),
        &reference::eval(ev, &env, &r).unwrap(),
    );
    [kernel.unwrap(), refr.unwrap()]
}

#[test]
fn a_pending_call_is_compared_as_it_will_be_once_admitted() {
    let (mut g, boxed, f) = setup();
    assert_eq!(answers(&g, boxed, f), [false, false], "pending");
    let body = lam("a", lam("b", case(0, boxed, vec![(vec!["x"], v(0))])));
    check::define_def(&mut g, f, &body).expect("f");
    assert_eq!(answers(&g, boxed, f), [false, false], "admitted");
}
