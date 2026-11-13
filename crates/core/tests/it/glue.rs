//! Glued evaluation (docs/proposals/folded-calls.md, stages 1 and 3): with
//! `Kernel::glue` on, a definition applied to all its arguments evaluates to
//! a `Value::Call`, which means exactly its unfolding. Gluing is off
//! everywhere by default, so these tests are what exercises it: everything
//! that looks inside a value must see the same as without gluing.

use crate::common::*;
use stitchwort_core::value::{Value, apply, conv, eval, force, quote, quote_folded};
use stitchwort_core::{DefId, Kernel, Term};

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
fn both_ways(g: &Kernel, level: usize, term: &Term) -> (Value, Value) {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    g.machine.glue.set(false);
    let off = eval(&g.ev(), &env, term).unwrap();
    g.machine.glue.set(true);
    let on = eval(&g.ev(), &env, term).unwrap();
    g.machine.glue.set(false);
    assert_eq!(
        format!("{:?}", quote(&g.ev(), level, &off).unwrap()),
        format!("{:?}", quote(&g.ev(), level, &on).unwrap()),
        "read back the same"
    );
    assert!(conv(&g.ev(), level, &off, &on).unwrap(), "convertible");
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
    assert!(matches!(force(&g.ev(), on).unwrap(), Value::Ctor(..)));
}

#[test]
fn a_call_stuck_on_a_variable_unfolds_to_the_folded_definition() {
    let d = defs();
    let g = &d.p.g;
    let term = app(Term::Def(d.double), [v(0)]);
    let (off, on) = both_ways(g, 1, &term);
    assert!(matches!(off, Value::Neutral(..)));
    assert!(matches!(on, Value::Call(..)));
    assert!(matches!(force(&g.ev(), on).unwrap(), Value::Neutral(..)));
}

#[test]
fn copies_share_the_unfolding_until_metavariables_are_taken_back() {
    let d = defs();
    let g = &d.p.g;
    let metas = Epoch(std::cell::Cell::new(1));
    let ev = stitchwort_core::Ev {
        metas: &metas,
        ..g.ev()
    };
    g.machine.glue.set(true);
    let call = eval(&ev, &[], &app(Term::Def(d.double), [d.p.num(20)])).unwrap();
    g.machine.glue.set(false);
    let copy = call.clone();
    let steps = |v: Value| {
        let before = g.machine.budget.total_work();
        force(&ev, v).unwrap();
        g.machine.budget.total_work() - before
    };
    let first = steps(call.clone());
    assert!(first > 20, "unfolding runs the definition: {first} steps");
    assert_eq!(steps(copy.clone()), 0, "the copy reuses the unfolding");
    // An unfolding may have used a metavariable solution that's gone.
    metas.0.set(2);
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
    assert!(conv(&g.ev(), 0, &off, &eval(&g.ev(), &[], &d.p.num(5)).unwrap()).unwrap());
    assert!(
        matches!(on, Value::Ctor(..)),
        "applied, so unfolded: {on:?}"
    );
    // And applying a glued call value to an argument afterwards.
    g.machine.glue.set(true);
    let partial = eval(&g.ev(), &[], &app(Term::Def(d.pick), [d.p.num(1)])).unwrap();
    assert!(matches!(partial, Value::Call(..)));
    let applied = apply(&g.ev(), partial, eval(&g.ev(), &[], &d.p.num(5)).unwrap()).unwrap();
    g.machine.glue.set(false);
    assert!(
        conv(
            &g.ev(),
            0,
            &applied,
            &eval(&g.ev(), &[], &d.p.num(0)).unwrap()
        )
        .unwrap()
    );
}

#[test]
fn natives_never_glue() {
    let mut d = defs();
    use stitchwort_core::native::{Native, register_nat, register_native_unpinned};
    register_nat(&mut d.p.g, d.p.nat).expect("Nat");
    register_native_unpinned(&mut d.p.g, d.p.add, Native::Add).expect("add");
    // A second registration is refused.
    assert!(register_native_unpinned(&mut d.p.g, d.p.add, Native::Add).is_err());
    let g = &d.p.g;
    // A native computes on numbers at once, as without gluing.
    g.machine.glue.set(true);
    let sum = eval(&g.ev(), &[], &d.p.plus(d.p.num(2), d.p.num(3))).unwrap();
    g.machine.glue.set(false);
    assert!(!matches!(sum, Value::Call(..)), "{sum:?}");
}

/// A number computed by glued calls nested deep, each giving its argument
/// to a native (`inc (inc (… 0))`, `inc n = n + 1`), is forced in one
/// machine: each call's argument is forced there before its native runs, so
/// the nesting costs frames, not the Rust stack of a machine per level
/// (SW-3132).
#[test]
fn natives_force_a_deep_chain_of_glued_calls_in_one_machine() {
    let mut d = defs();
    use stitchwort_core::native::{Native, as_nat, register_nat, register_native_unpinned};
    register_nat(&mut d.p.g, d.p.nat).expect("Nat");
    register_native_unpinned(&mut d.p.g, d.p.add, Native::Add).expect("add");
    let nat_ty = d.p.nat_ty();
    let body = lam("n", d.p.plus(v(0), d.p.num(1)));
    let inc = define(&mut d.p.g, "inc", arrow(nat_ty.clone(), nat_ty), body).expect("inc");
    let depth = 100_000;
    let term = (0..depth).fold(d.p.num(0), |t, _| app(Term::Def(inc), [t]));
    let g = &d.p.g;
    g.machine.glue.set(true);
    let call = eval(&g.ev(), &[], &term).unwrap();
    assert!(matches!(call, Value::Call(..)), "{call:?}");
    let forced = force(&g.ev(), call);
    g.machine.glue.set(false);
    let n = as_nat(&g.ev(), &forced.unwrap()).unwrap();
    assert_eq!(n.map(|n| n.to_string()), Some(depth.to_string()));
}

/// `term` (with `level` variables) evaluated with gluing on and read back
/// folded; checked convertible with its value without gluing.
fn folded(g: &Kernel, level: usize, term: &Term) -> Term {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    g.machine.glue.set(true);
    let on = eval(&g.ev(), &env, term).unwrap();
    let written = quote_folded(&g.ev(), level, &on).unwrap();
    g.machine.glue.set(false);
    let off = eval(&g.ev(), &env, term).unwrap();
    let again = eval(&g.ev(), &env, &written).unwrap();
    assert!(conv(&g.ev(), level, &off, &again).unwrap(), "convertible");
    // Without gluing there are no calls: folded is the normal form.
    assert_eq!(
        format!("{:?}", quote_folded(&g.ev(), level, &off).unwrap()),
        format!("{:?}", quote(&g.ev(), level, &off).unwrap()),
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
    let nat = eval(&g.ev(), &[], &d.p.nat_ty()).unwrap();
    let scope = Scope {
        env: vec![Value::var(0)],
        types: vec![nat],
        extra: Vec::new(),
        rigid: Vec::new(),
    };
    g.machine.glue.set(true);
    let big = d.p.num(2_000);
    let closed = eval(&g.ev(), &[], &app(Term::Def(d.double), [big])).unwrap();
    assert!(matches!(closed, Value::Call(..)));
    let before = g.machine.budget.total_work();
    let found = occurs(&g.ev(), &scope, 0, &closed).unwrap();
    let steps = g.machine.budget.total_work() - before;
    let env = [Value::var(0)];
    let on_y = eval(&g.ev(), &env, &app(Term::Def(d.double), [v(0)])).unwrap();
    let succ_y = Term::ctor(d.p.nat, 1, vec![v(0)]);
    let dropped = eval(&g.ev(), &env, &app(Term::Def(d.is_zero), [succ_y])).unwrap();
    assert!(matches!(dropped, Value::Call(..)));
    let (on_y, dropped) = (
        occurs(&g.ev(), &scope, 0, &on_y).unwrap(),
        occurs(&g.ev(), &scope, 0, &dropped).unwrap(),
    );
    g.machine.glue.set(false);
    assert!(!found);
    assert!(steps < 100, "the occurs check took {steps} steps");
    assert!(on_y, "`double y` mentions `y`");
    assert!(!dropped, "`isZero (Succ y)` is `0`");
}

/// SW-1782: a call's kept unfolding is used only by a reader in modes it
/// could have been computed in. `outer (Succ x)` steps at once to `Succ
/// (twice x)`, and `twice` doesn't match at once, so read back folded it
/// stays the call. Forced first with gluing off, `outer`'s call kept `Succ
/// (Succ (Succ (double x)))`, with no call left in it, and the folded
/// read-back wrote that.
#[test]
fn a_call_forced_unglued_reads_back_folded_as_if_never_forced() {
    let d = defs();
    let mut p = d.p;
    let nat_ty = p.nat_ty();
    let twice = define(
        &mut p.g,
        "twice",
        arrow(nat_ty.clone(), nat_ty.clone()),
        lam(
            "n",
            app(Term::Def(d.double), [Term::ctor(p.nat, 1, vec![v(0)])]),
        ),
    )
    .expect("twice");
    let outer = define(
        &mut p.g,
        "outer",
        arrow(nat_ty.clone(), nat_ty),
        lam(
            "n",
            case(
                0,
                p.nat,
                vec![
                    (vec![], Term::Ctor(p.nat, 0, vec![])),
                    (
                        vec!["m"],
                        Term::ctor(p.nat, 1, vec![app(Term::Def(twice), [v(0)])]),
                    ),
                ],
            ),
        ),
    )
    .expect("outer");
    let g = &p.g;
    let term = app(Term::Def(outer), [Term::ctor(p.nat, 1, vec![v(0)])]);
    let env = [Value::var(0)];
    let read = |force_unglued_first: bool| {
        g.machine.glue.set(true);
        let call = eval(&g.ev(), &env, &term).unwrap();
        if force_unglued_first {
            g.machine.glue.set(false);
            quote(&g.ev(), 1, &call).unwrap();
            g.machine.glue.set(true);
        }
        let written = quote_folded(&g.ev(), 1, &call).unwrap();
        g.machine.glue.set(false);
        written
    };
    let fresh = read(false);
    assert!(mentions(&fresh, twice), "{fresh:?}");
    assert_eq!(format!("{:?}", read(true)), format!("{fresh:?}"));
}

/// The other way round, an unfolding computed glued serves a reader with
/// gluing off, which forces the calls in it as it meets them.
#[test]
fn an_unfolding_computed_glued_serves_an_unglued_reader() {
    let d = defs();
    let g = &d.p.g;
    let term = app(Term::Def(d.double), [d.p.num(20)]);
    let steps = |v: Value, glue: bool| {
        g.machine.glue.set(glue);
        let before = g.machine.budget.total_work();
        force(&g.ev(), v).unwrap();
        g.machine.glue.set(false);
        g.machine.budget.total_work() - before
    };
    g.machine.glue.set(true);
    let call = eval(&g.ev(), &[], &term).unwrap();
    assert!(steps(call.clone(), true) > 0);
    assert_eq!(steps(call, false), 0, "reused");
    g.machine.glue.set(true);
    let call = eval(&g.ev(), &[], &term).unwrap();
    assert!(steps(call.clone(), false) > 0);
    assert!(steps(call, true) > 0, "computed again, glued");
}

/// An unfolding that used an opaque definition's body, computed while it
/// was visible (in the transparency set, or while a program ran), isn't
/// used once it's hidden again.
#[test]
fn an_unfolding_that_saw_an_opaque_body_isnt_used_once_it_is_hidden() {
    let d = defs();
    let mut p = d.p;
    let nat_ty = p.nat_ty();
    let id = stitchwort_core::check::declare_def(
        &mut p.g,
        &"two".into(),
        &"two".into(),
        &nat_ty,
        false,
        false,
        span(),
    )
    .expect("two");
    stitchwort_core::check::mark_opaque(&mut p.g, id);
    let body = p.num(2);
    stitchwort_core::check::define_def(&mut p.g, id, &body).expect("two");
    let get = define(
        &mut p.g,
        "getTwo",
        arrow(nat_ty.clone(), nat_ty),
        lam("n", Term::Def(id)),
    )
    .expect("getTwo");
    let g = &p.g;
    let term = app(Term::Def(get), [p.num(0)]);
    let hidden = |v: Value| {
        let forced = force(&g.ev(), v).unwrap();
        matches!(forced, Value::Neutral(stitchwort_core::value::Head::Def(i), _) if i == id)
    };
    let call = || {
        g.machine.glue.set(true);
        let call = eval(&g.ev(), &[], &term).unwrap();
        g.machine.glue.set(false);
        assert!(matches!(call, Value::Call(..)));
        call
    };
    let shown = call();
    {
        let _set = g.machine.transparent.set(std::rc::Rc::from([id]));
        assert!(!hidden(shown.clone()), "in the transparency set");
    }
    assert!(hidden(shown), "hidden again");
    let ran = call();
    {
        let _running = g.machine.erasure.running();
        assert!(!hidden(ran.clone()), "while a program runs");
    }
    assert!(hidden(ran), "hidden again");
    // The same with erasure off: a program running is a mode of its own.
    g.machine.erasure.set_disabled(true);
    let ran = call();
    {
        let _running = g.machine.erasure.running();
        assert!(!hidden(ran.clone()), "while a program runs, not erasing");
    }
    g.machine.erasure.set_disabled(false);
    assert!(hidden(ran), "hidden again");
}

/// Metavariables with no solutions, at an epoch the test moves.
struct Epoch(std::cell::Cell<u64>);

impl stitchwort_core::Metas for Epoch {
    fn solution(&self, _m: usize) -> Option<Value> {
        None
    }

    fn epoch(&self) -> u64 {
        self.0.get()
    }
}

/// A native is registered for one definition only, and a definition has one
/// native: each second registration is refused, naming the right thing.
#[test]
fn a_second_registration_is_refused_by_name() {
    use stitchwort_core::native::{Native, register_nat, register_native_unpinned};
    let mut p = Prelude::new();
    let nat_ty = p.nat_ty();
    register_nat(&mut p.g, p.nat).expect("Nat");
    let binary = arrow(nat_ty.clone(), arrow(nat_ty.clone(), nat_ty));
    let other = declare(&mut p.g, "other", binary);
    let body = lam("m", lam("n", v(0)));
    stitchwort_core::check::define_def(&mut p.g, other, &body).expect("other");
    register_native_unpinned(&mut p.g, p.add, Native::Add).expect("add");
    // The native already has a definition.
    let e = register_native_unpinned(&mut p.g, other, Native::Add).unwrap_err();
    assert!(
        e.message.contains("`Nat.add` is bound to a definition"),
        "{}",
        e.message
    );
    // The definition already has a native: the message names the
    // definition and its native, not the one being added.
    let e = register_native_unpinned(&mut p.g, p.add, Native::Mul).unwrap_err();
    assert!(
        e.message.contains("is bound to `Nat.add` already"),
        "{}",
        e.message
    );
    assert!(!e.message.contains("Nat.mul"), "{}", e.message);
}
