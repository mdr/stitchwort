//! Glued evaluation (docs/proposals/folded-calls.md, stages 1 and 3): with
//! `Globals::glue` on, a definition applied to all its arguments evaluates to
//! a `Value::Call`, which means exactly its unfolding. Gluing is off
//! everywhere by default, so these tests are what exercises it: everything
//! that looks inside a value must see the same as without gluing.

mod common;

use common::*;
use stitchwort_core::value::{Value, apply, conv, eval, force, quote, quote_folded};
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
    g.machine.glue.set(false);
    let off = eval(g, &env, term).unwrap();
    g.machine.glue.set(true);
    let on = eval(g, &env, term).unwrap();
    g.machine.glue.set(false);
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
    g.machine.glue.set(true);
    let call = eval(g, &[], &app(Term::Def(d.double), [d.p.num(20)])).unwrap();
    g.machine.glue.set(false);
    let copy = call.clone();
    let steps = |v: Value| {
        let before = g.machine.budget.total_work();
        force(g, v).unwrap();
        g.machine.budget.total_work() - before
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
    g.machine.glue.set(true);
    let partial = eval(g, &[], &app(Term::Def(d.pick), [d.p.num(1)])).unwrap();
    assert!(matches!(partial, Value::Call(..)));
    let applied = apply(g, partial, eval(g, &[], &d.p.num(5)).unwrap()).unwrap();
    g.machine.glue.set(false);
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
    g.machine.glue.set(true);
    let sum = eval(g, &[], &d.p.plus(d.p.num(2), d.p.num(3))).unwrap();
    g.machine.glue.set(false);
    assert!(!matches!(sum, Value::Call(..)), "{sum:?}");
}

/// `term` (with `level` variables) evaluated with gluing on and read back
/// folded; checked convertible with its value without gluing.
fn folded(g: &Globals, level: usize, term: &Term) -> Term {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    g.machine.glue.set(true);
    let on = eval(g, &env, term).unwrap();
    let written = quote_folded(g, level, &on).unwrap();
    g.machine.glue.set(false);
    let off = eval(g, &env, term).unwrap();
    let again = eval(g, &env, &written).unwrap();
    assert!(conv(g, level, &off, &again).unwrap(), "convertible");
    // Without gluing there are no calls: folded is the normal form.
    assert_eq!(
        format!("{:?}", quote_folded(g, level, &off).unwrap()),
        format!("{:?}", quote(g, level, &off).unwrap()),
    );
    written
}

/// Whether `term` mentions definition `id`.
fn mentions(term: &Term, id: DefId) -> bool {
    term.subterms()
        .any(|(t, _)| matches!(t, Term::Def(d) if *d == id))
}

#[test]
fn reading_back_folded_writes_the_call() {
    let d = defs();
    let g = &d.p.g;
    // Stuck on a variable: the call, not what it unfolds to.
    let call = app(Term::Def(d.double), [v(0)]);
    assert_eq!(format!("{:?}", folded(g, 1, &call)), format!("{call:?}"));
    // A case on a call stuck on a variable: both calls stay.
    let nested = app(Term::Def(d.is_zero), [call]);
    assert_eq!(
        format!("{:?}", folded(g, 1, &nested)),
        format!("{nested:?}")
    );
}

#[test]
fn a_call_that_matches_at_once_is_written_unfolded() {
    let d = defs();
    let g = &d.p.g;
    // `double 1` takes its `Succ` branch at once: written as its unfolding,
    // the inner `double 0` (also on a constructor) unfolded in turn.
    let term = app(Term::Def(d.double), [d.p.num(1)]);
    let written = folded(g, 0, &term);
    assert!(!mentions(&written, d.double), "{written:?}");
    // `isZero (double (Succ x))`: the inner call matches at once, so the
    // outer one does too, through it; `double x` stays a call.
    let succ_x = Term::ctor(d.p.nat, 1, vec![v(0)]);
    let term = app(Term::Def(d.is_zero), [app(Term::Def(d.double), [succ_x])]);
    let written = folded(g, 1, &term);
    assert!(!mentions(&written, d.is_zero), "{written:?}");
}

/// SW-1154: the occurs check of index unification looks at a glued call's
/// arguments, not its unfolding: `double 2000` mentions no variable, which
/// its arguments show at once, where reading it back took 26,000 steps. Where the arguments mention the variable, the check reads back
/// as before, and answers by the unfolding: `isZero (Succ y)` doesn't
/// mention `y` once unfolded.
#[test]
fn the_occurs_check_looks_at_a_calls_arguments() {
    use stitchwort_core::unify_index::{Scope, occurs};
    let d = defs();
    let g = &d.p.g;
    let nat = eval(g, &[], &d.p.nat_ty()).unwrap();
    let scope = Scope {
        env: vec![Value::var(0)],
        types: vec![nat],
        extra: Vec::new(),
        rigid: Vec::new(),
    };
    g.machine.glue.set(true);
    let big = d.p.num(2_000);
    let closed = eval(g, &[], &app(Term::Def(d.double), [big])).unwrap();
    assert!(matches!(closed, Value::Call(..)));
    let before = g.machine.budget.total_work();
    let found = occurs(g, &scope, 0, &closed).unwrap();
    let steps = g.machine.budget.total_work() - before;
    let env = [Value::var(0)];
    let on_y = eval(g, &env, &app(Term::Def(d.double), [v(0)])).unwrap();
    let succ_y = Term::ctor(d.p.nat, 1, vec![v(0)]);
    let dropped = eval(g, &env, &app(Term::Def(d.is_zero), [succ_y])).unwrap();
    assert!(matches!(dropped, Value::Call(..)));
    let (on_y, dropped) = (
        occurs(g, &scope, 0, &on_y).unwrap(),
        occurs(g, &scope, 0, &dropped).unwrap(),
    );
    g.machine.glue.set(false);
    assert!(!found);
    assert!(steps < 100, "the occurs check took {steps} steps");
    assert!(on_y, "`double y` mentions `y`");
    assert!(!dropped, "`isZero (Succ y)` is `0`");
}
