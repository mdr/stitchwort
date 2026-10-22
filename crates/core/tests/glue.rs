//! Glued evaluation (docs/proposals/folded-calls.md, stage 1): with
//! `Globals::glue` on, a definition applied to all its arguments evaluates to
//! a `Value::Call`, which means exactly its unfolding. Gluing is off
//! everywhere by default, so these tests are what exercises it: everything
//! that looks inside a value must see the same as without gluing.

mod common;

use common::*;
use stitchwort_core::value::{Value, apply, conv, eval, force, quote};
use stitchwort_core::{DefId, Globals, Term};

/// The prelude, with `double n = n + n` written as recursion (so it isn't
/// a native), `isZero : Nat -> Bool`-like `isZero n = case n of Zero -> 1;
/// Succ _ -> 0` (as numbers), and `pick n = case n of Zero -> (y => y);
/// Succ _ -> (y => Zero)`, whose unfolding is a function.
struct Defs {
    p: Prelude,
    double: DefId,
    is_zero: DefId,
    pick: DefId,
}

fn defs() -> Defs {
    let mut p = Prelude::new();
    let nat = p.nat;
    let nat_ty = p.nat_ty();
    let g = &mut p.g;
    let double = declare(g, "double", arrow(nat_ty.clone(), nat_ty.clone()));
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
    stitchwort_core::check::define_def(g, double, &body).expect("double");
    let zero = Term::Ctor(nat, 0, vec![]);
    let one = Term::ctor(nat, 1, vec![zero.clone()]);
    let is_zero = define(
        g,
        "isZero",
        arrow(nat_ty.clone(), nat_ty.clone()),
        lam(
            "n",
            case(0, nat, vec![(vec![], one), (vec!["m"], zero.clone())]),
        ),
    )
    .expect("isZero");
    let pick = define(
        g,
        "pick",
        arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty.clone())),
        lam(
            "n",
            case(
                0,
                nat,
                vec![(vec![], lam("y", v(0))), (vec!["m"], lam("y", zero))],
            ),
        ),
    )
    .expect("pick");
    Defs {
        p,
        double,
        is_zero,
        pick,
    }
}

/// `term`'s value and its read-back, with gluing off and then on: the
/// read-backs must be the same.
fn both_ways(g: &Globals, level: usize, term: &Term) -> (Value, Value) {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    g.glue.set(false);
    let off = eval(g, &env, term).unwrap();
    g.glue.set(true);
    let on = eval(g, &env, term).unwrap();
    g.glue.set(false);
    assert_eq!(
        format!("{:?}", quote(g, level, &off).unwrap()),
        format!("{:?}", quote(g, level, &on).unwrap()),
        "read back the same"
    );
    assert!(conv(g, level, &off, &on).unwrap(), "convertible");
    (off, on)
}

#[test]
fn a_call_with_all_its_arguments_stays_a_call_only_while_gluing() {
    let d = defs();
    let g = &d.p.g;
    let term = app(Term::Def(d.double), [d.p.num(3)]);
    let (off, on) = both_ways(g, 0, &term);
    assert!(matches!(off, Value::Ctor(..)), "unfolded at once");
    assert!(
        matches!(on, Value::Call(id, _, _) if id == d.double),
        "kept as the call"
    );
    assert!(matches!(force(g, on).unwrap(), Value::Ctor(..)));
}

#[test]
fn a_call_stuck_on_a_variable_unfolds_to_the_folded_definition() {
    let d = defs();
    let g = &d.p.g;
    let term = app(Term::Def(d.double), [v(0)]);
    let (off, on) = both_ways(g, 1, &term);
    assert!(matches!(off, Value::Neutral(..)));
    assert!(matches!(on, Value::Call(..)));
    assert!(matches!(force(g, on).unwrap(), Value::Neutral(..)));
}

#[test]
fn copies_share_the_unfolding_until_metavariables_are_taken_back() {
    let d = defs();
    let g = &d.p.g;
    g.glue.set(true);
    let call = eval(g, &[], &app(Term::Def(d.double), [d.p.num(20)])).unwrap();
    g.glue.set(false);
    let copy = call.clone();
    let steps = |v: Value| {
        let before = g.budget.total_work();
        force(g, v).unwrap();
        g.budget.total_work() - before
    };
    let first = steps(call.clone());
    assert!(first > 20, "unfolding runs the definition: {first} steps");
    assert_eq!(steps(copy.clone()), 0, "the copy reuses the unfolding");
    // An unfolding may have used a metavariable solution that's gone.
    g.metas_taken_back();
    assert_eq!(steps(copy), first, "computed again after taking back");
}

#[test]
fn looking_inside_forces_a_call_everywhere() {
    let d = defs();
    let g = &d.p.g;
    // A case on a call (`isZero (double 0)`), and on a call stuck on a
    // variable.
    for (level, arg) in [(0, d.p.num(0)), (1, v(0)), (0, d.p.num(2))] {
        let inner = app(Term::Def(d.double), [arg]);
        both_ways(g, level, &app(Term::Def(d.is_zero), [inner]));
    }
    // Applying a call whose unfolding is a function: `pick 0 5` is `5`.
    let term = app(Term::Def(d.pick), [d.p.num(0), d.p.num(5)]);
    let (off, on) = both_ways(g, 0, &term);
    assert!(conv(g, 0, &off, &eval(g, &[], &d.p.num(5)).unwrap()).unwrap());
    assert!(
        matches!(on, Value::Ctor(..)),
        "applied, so unfolded: {on:?}"
    );
    // And applying a glued call value to an argument afterwards.
    g.glue.set(true);
    let partial = eval(g, &[], &app(Term::Def(d.pick), [d.p.num(1)])).unwrap();
    assert!(matches!(partial, Value::Call(..)));
    let applied = apply(g, partial, eval(g, &[], &d.p.num(5)).unwrap()).unwrap();
    g.glue.set(false);
    assert!(conv(g, 0, &applied, &eval(g, &[], &d.p.num(0)).unwrap()).unwrap());
}

#[test]
fn natives_never_glue() {
    let mut d = defs();
    use stitchwort_core::native::{Native, register_nat, register_native};
    register_nat(&mut d.p.g, d.p.nat).expect("Nat");
    register_native(&mut d.p.g, d.p.add, Native::Add).expect("add");
    let g = &d.p.g;
    // A native computes on numbers at once, as without gluing.
    g.glue.set(true);
    let sum = eval(g, &[], &d.p.plus(d.p.num(2), d.p.num(3))).unwrap();
    g.glue.set(false);
    assert!(!matches!(sum, Value::Call(..)), "{sum:?}");
}
