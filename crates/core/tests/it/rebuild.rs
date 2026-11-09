//! Refining a context (`check::substitute`, `check::reread`) builds most
//! nodes directly rather than reading each value back and evaluating it
//! again (SW-2481). These pin that to what the readback and evaluation make.

use crate::common::*;
use stitchwort_core::check::{reread, substitute};
use stitchwort_core::value::{Value, apply, eval, quote, quote_folded};
use stitchwort_core::{DefId, Kernel, Limits, Term};

const LEVEL: usize = 4;
/// The variable substituted for, at level 1: de Bruijn index 2 at `LEVEL`.
const X: usize = 1;

fn at(level: usize) -> Term {
    v(LEVEL - 1 - level)
}

/// `double n = n + n`, written as recursion so it isn't a native.
fn define_double(p: &mut Prelude) -> DefId {
    let nat = p.nat;
    let nat_ty = p.nat_ty();
    let double = declare(&mut p.g, "double", arrow(nat_ty.clone(), nat_ty));
    let body = lam(
        "n",
        case(
            0,
            nat,
            vec![
                (vec![], Term::Ctor(nat, 0, vec![])),
                (
                    vec!["m"],
                    Term::ctor(
                        nat,
                        1,
                        vec![Term::ctor(nat, 1, vec![app(Term::Def(double), [v(0)])])],
                    ),
                ),
            ],
        ),
    );
    stitchwort_core::check::define_def(&mut p.g, double, &body).expect("double");
    double
}

/// `f` (the variable at level 0) applied to the one before twice, `depth`
/// times, from the variable at `X`: each level's spine holds the last
/// value twice, so the value is a chain of shared spines.
fn shared_spines(g: &Kernel, depth: usize) -> Value {
    let f = Value::var(0);
    let mut t = Value::var(X);
    for _ in 0..depth {
        let once = apply(&g.ev(), f.clone(), t.clone()).unwrap();
        t = apply(&g.ev(), once, t).unwrap();
    }
    t
}

/// The terms the values are made from, at `LEVEL`.
fn terms(p: &Prelude) -> Vec<Term> {
    let nat_ty = p.nat_ty();
    vec![
        at(X),
        at(2),
        p.succ(p.succ(at(X))),
        Term::ctor(p.list, 1, vec![at(X), Term::ctor(p.list, 0, vec![])]),
        eq(Some(nat_ty.clone()), p.plus(at(X), at(2)), p.succ(at(3))),
        Term::data(p.list, vec![nat_ty]),
        app(at(0), [at(X), p.succ(at(X))]),
    ]
}

/// What substituting `value` for `X` should give for `v`: its readback
/// evaluated again, with `X` standing for `value`.
fn expected(g: &Kernel, value: &Value, v: &Value) -> Value {
    let mut env: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    env[X] = value.clone();
    eval(&g.ev(), &env, &quote_folded(&g.ev(), LEVEL, v).unwrap()).unwrap()
}

#[test]
fn substitution_builds_what_readback_and_evaluation_make() {
    let p = Prelude::new();
    let g = &p.g;
    let identity: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let mut values: Vec<Value> = terms(&p)
        .iter()
        .map(|t| eval(&g.ev(), &identity, t).unwrap())
        .collect();
    values.push(shared_spines(g, 6));
    // `X` as a constructor around a variable, and as a number, which makes
    // `Succ (Succ X)` a number too.
    let succ = eval(&g.ev(), &identity, &p.succ(at(3))).unwrap();
    let zero = eval(&g.ev(), &identity, &p.num(0)).unwrap();
    for value in [succ, zero] {
        let got = substitute(&g.ev(), LEVEL, X, &value, &values).unwrap();
        for (v, got) in values.iter().zip(&got) {
            // Node for node: the same structure, numbers and `Apart` facts.
            assert_eq!(
                format!("{got:?}"),
                format!("{:?}", expected(g, &value, v)),
                "substituting {value:?} in {v:?}"
            );
        }
    }
}

#[test]
fn rereading_builds_what_readback_and_evaluation_make() {
    let p = Prelude::new();
    let g = &p.g;
    let identity: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    let mut values: Vec<Value> = terms(&p)
        .iter()
        .map(|t| eval(&g.ev(), &identity, t).unwrap())
        .collect();
    values.push(shared_spines(g, 6));
    let got = reread(&g.ev(), LEVEL, &values).unwrap();
    for (v, got) in values.iter().zip(&got) {
        let want = eval(&g.ev(), &identity, &quote(&g.ev(), LEVEL, v).unwrap()).unwrap();
        assert_eq!(format!("{got:?}"), format!("{want:?}"), "rereading {v:?}");
    }
}

#[test]
fn substitution_keeps_glued_calls_that_dont_change() {
    let mut p = Prelude::new();
    let double = define_double(&mut p);
    let g = &p.g;
    let identity: Vec<Value> = (0..LEVEL).map(Value::var).collect();
    g.machine.glue.set(true);
    // A call stuck on `X`, one on another variable, and one that steps at
    // once, alone and inside a value that changes.
    let stuck = app(Term::Def(double), [at(X)]);
    let other = app(Term::Def(double), [at(2)]);
    let at_once = app(Term::Def(double), [p.num(3)]);
    let terms = [
        stuck.clone(),
        other.clone(),
        at_once.clone(),
        eq(Some(p.nat_ty()), at_once, at(X)),
        eq(Some(p.nat_ty()), other, stuck),
    ];
    let values: Vec<Value> = terms
        .iter()
        .map(|t| eval(&g.ev(), &identity, t).unwrap())
        .collect();
    let value = eval(&g.ev(), &identity, &p.succ(at(3))).unwrap();
    let got = substitute(&g.ev(), LEVEL, X, &value, &values).unwrap();
    assert!(matches!(&got[1], Value::Call(id, ..) if *id == double));
    assert!(
        matches!(&got[2], Value::Call(id, ..) if *id == double),
        "kept"
    );
    for (v, got) in values.iter().zip(&got) {
        // The same term read back folded: a kept call that steps at once
        // is forced by the readback.
        assert_eq!(
            format!("{:?}", quote_folded(&g.ev(), LEVEL, got).unwrap()),
            format!(
                "{:?}",
                quote_folded(&g.ev(), LEVEL, &expected(g, &value, v)).unwrap()
            ),
            "substituting in {v:?}"
        );
    }
    g.machine.glue.set(false);
}

#[test]
fn shared_spines_are_substituted_into_once() {
    let p = Prelude::new();
    let g = &p.g;
    // Walked as a tree, 2^40 nodes; as stored, 40 spines.
    let deep = shared_spines(g, 40);
    let value = eval(
        &g.ev(),
        &(0..LEVEL).map(Value::var).collect::<Vec<_>>(),
        &p.succ(at(3)),
    )
    .unwrap();
    let saved = g.machine.budget.start(Limits {
        work: 10_000,
        ..Limits::default()
    });
    let got = substitute(&g.ev(), LEVEL, X, &value, std::slice::from_ref(&deep));
    let reread_too = reread(&g.ev(), LEVEL, std::slice::from_ref(&deep));
    g.machine.budget.restore(saved);
    assert!(got.is_ok(), "within 10,000 steps");
    assert!(reread_too.is_ok(), "within 10,000 steps");
}
