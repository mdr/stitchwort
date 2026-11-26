//! `+` computes on its second argument too (`stitchwort_core::nat_add`,
//! SW-787): R3 `m + Zero → m` and R4 `m + Succ n → Succ (m + n)`, beside
//! `Nat.add`'s own R1 and R2. The rules are trusted, so these check them
//! with both evaluators (the machine and the reference), natives on and
//! off: the critical pairs join, stuck sums compute the same everywhere,
//! and the rules are bound only to the library's `Nat.add`.

use crate::common::STACK;
use std::rc::Rc;

use stitchwort_core::nat_add;
use stitchwort_core::native;
use stitchwort_core::reference;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{self, Value};
use stitchwort_core::{BigUint, DefId, Kernel, Term};
use stitchwort_driver::driver::{Session, with_stack};

#[derive(Clone, Copy, Debug)]
enum Evaluator {
    Machine,
    Reference,
}

/// `term` evaluated in `env` by `evaluator`, with the natives as they are.
fn eval(g: &stitchwort_core::Ev, env: &[Value], term: &Term, evaluator: Evaluator) -> Value {
    match evaluator {
        Evaluator::Machine => value::eval(g, env, term).expect("no limits"),
        Evaluator::Reference => reference::eval(g, env, term).expect("no limits"),
    }
}

/// Whether `a` and `b` are convertible, by `evaluator`'s own conversion.
fn conv(g: &stitchwort_core::Ev, level: usize, a: &Value, b: &Value, evaluator: Evaluator) -> bool {
    match evaluator {
        Evaluator::Machine => value::conv(g, level, a, b).expect("no limits"),
        Evaluator::Reference => reference::conv(g, level, a, b).expect("no limits"),
    }
}

/// A normal form, printed by the reference's `quote` (so the machine's
/// quoting can't hide a difference).
fn shown(g: &stitchwort_core::Ev, level: usize, value: &Value) -> String {
    format!(
        "{:?}",
        reference::quote(g, level, value).expect("no limits")
    )
}

/// Each term of `terms`, evaluated in `env` (whose values mention `level`
/// variables) with the natives on and then off: both evaluators give the
/// same normal form, and then `check` gets the values with the evaluator
/// and whether the natives are on.
fn in_every_mode(
    g: &mut Kernel,
    env: &[Value],
    level: usize,
    terms: &[&Term],
    mut check: impl FnMut(&Kernel, &[Value], Evaluator, bool),
) {
    for natives in [true, false] {
        g.env.set_disable_natives(!natives);
        let fast: Vec<Value> = terms
            .iter()
            .map(|t| eval(&g.ev(), env, t, Evaluator::Machine))
            .collect();
        let slow: Vec<Value> = terms
            .iter()
            .map(|t| eval(&g.ev(), env, t, Evaluator::Reference))
            .collect();
        for (f, s) in fast.iter().zip(&slow) {
            assert_eq!(
                shown(&g.ev(), level, f),
                shown(&g.ev(), level, s),
                "the evaluators disagree (natives {natives})"
            );
        }
        check(g, &fast, Evaluator::Machine, natives);
        check(g, &slow, Evaluator::Reference, natives);
        g.env.set_disable_natives(false);
    }
}

fn add_id(g: &stitchwort_core::Ev) -> DefId {
    g.env
        .registry()
        .def(Builtin::Add)
        .expect("`Nat.add` is bound")
}

fn num(n: u64) -> Term {
    Term::Nat(Rc::new(BigUint::from(n)))
}

/// The prelude's `Nat.add` is the one the rules were written for, and they
/// are on. If this fails, the library changed `Nat.add` or `Nat` (the rules
/// are then off, and this prints the new hash): check the rules in
/// crates/core/src/nat_add.rs are still its equations, then pin the hash.
#[test]
fn nat_add_is_the_pinned_declaration() {
    let session = Session::new();
    let g = &session.elab.ev();
    let pin = stitchwort_core::pins::pin(stitchwort_core::registry::Builtin::Add).expect("pinned");
    assert_eq!(nat_add::add_hash(g).as_deref(), Some(pin.hash));
    assert_eq!(g.env.builtins().nat_add_rule, Some(add_id(g)));
}

/// Each critical pair of R1 to R4 joins: the sum and the two terms the
/// overlapping rules rewrite it to are convertible, with each evaluator,
/// natives on and off, with `m` and `n` variables, numbers, or a number
/// plus a variable; and both evaluators give each the same normal form.
#[test]
fn the_critical_pairs_join() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let g = &mut session.elab.kernel;
        let pairs = nat_add::critical_pairs(&g.ev(), add_id(&g.ev())).expect("`Nat` is bound");
        assert_eq!(pairs.len(), 4);
        // `m` and `n` are levels 0 and 1, a number, or `3 + x` with `x` level 2.
        let x = Value::var(2);
        let instances = |own: usize| {
            [
                Value::var(own),
                native::nat_value(BigUint::from(0u32)),
                native::nat_value(BigUint::from(4u32)),
                native::from_view(BigUint::from(3u32), Some(x.clone())),
            ]
        };
        let mut checked = 0;
        for pair in &pairs {
            for m in instances(0) {
                for n in instances(1) {
                    let env = [m.clone(), n.clone()];
                    let terms = [&pair.sum, &pair.left, &pair.right];
                    in_every_mode(g, &env, 3, &terms, |g, v, evaluator, natives| {
                        let what = format!(
                            "{}, m = {m:?}, n = {n:?}, {evaluator:?}, natives {natives}",
                            pair.name
                        );
                        assert!(
                            conv(&g.ev(), 3, &v[1], &v[2], evaluator),
                            "{what}: the two sides"
                        );
                        assert!(conv(&g.ev(), 3, &v[0], &v[1], evaluator), "{what}: the sum");
                        checked += 1;
                    });
                }
            }
        }
        assert_eq!(checked, 4 * 4 * 4 * 4);
    });
}

/// The evaluators reach the right side of the Taming of the Rew's
/// "parallel rule" R5 `Succ m + Succ n → Succ (Succ (m + n))` (its Example
/// 4.3; the proposal's §9.4) without having it as code: `Succ m + Succ n`
/// and its one-step reducts by R2 and R4 are each convertible with R5's
/// right side, with each evaluator, natives on and off, for the instances
/// of `the_critical_pairs_join`. Not always as the same value: with `m` and
/// `n` variables the sum is `NatAdd(2, m + n)`, the compact form of
/// `Succ (Succ (m + n))`, while R5's right side as written stays two
/// `Succ` constructors (`native::ctor` compacts only a `Succ` of a number
/// or a `NatAdd`); conversion identifies the two.
#[test]
fn the_parallel_rule_is_reached() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let g = &mut session.elab.kernel;
        let add = add_id(&g.ev());
        let nat = g.env.builtins().nat.expect("`Nat` is bound");
        let plus = |a: Term, b: Term| Term::app(Term::app(Term::Def(add), a), b);
        let succ = |t: Term| Term::ctor(nat, 1, vec![t]);
        // `m` and `n` are levels 0 and 1: indices 1 and 0.
        let (m, n) = (|| Term::Var(1), || Term::Var(0));
        let sum = plus(succ(m()), succ(n()));
        let by_r2 = succ(plus(m(), succ(n())));
        let by_r4 = succ(plus(succ(m()), n()));
        let r5 = succ(succ(plus(m(), n())));
        let x = Value::var(2);
        let instances = |own: usize| {
            [
                Value::var(own),
                native::nat_value(BigUint::from(0u32)),
                native::nat_value(BigUint::from(4u32)),
                native::from_view(BigUint::from(3u32), Some(x.clone())),
            ]
        };
        let mut checked = 0;
        for mv in instances(0) {
            for nv in instances(1) {
                let env = [mv.clone(), nv.clone()];
                let terms = [&r5, &sum, &by_r2, &by_r4];
                in_every_mode(g, &env, 3, &terms, |g, v, evaluator, natives| {
                    let what = format!("m = {mv:?}, n = {nv:?}, {evaluator:?}, natives {natives}");
                    for (name, value) in [("the sum", &v[1]), ("R2", &v[2]), ("R4", &v[3])] {
                        assert!(conv(&g.ev(), 3, value, &v[0], evaluator), "{what}: {name}");
                    }
                    if matches!((&mv, &nv), (Value::Neutral(..), Value::Neutral(..))) {
                        let two = BigUint::from(2u32);
                        let compact = matches!(&v[1], Value::NatAdd(k, _) if **k == two);
                        assert!(compact, "{what}: {}", shown(&g.ev(), 3, &v[1]));
                        let ctor = matches!(&v[0], Value::Ctor(..));
                        assert!(ctor, "{what}: {}", shown(&g.ev(), 3, &v[0]));
                    }
                    checked += 1;
                });
            }
        }
        assert_eq!(checked, 4 * 4 * 4);
    });
}

/// Sums stuck on their first argument compute on their second, to the same
/// value with each evaluator, natives on and off; and a sum stuck on both
/// stays stuck. `x` and `y` are variables (levels 0 and 1).
#[test]
fn stuck_sums_compute_on_their_second_argument() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let g = &mut session.elab.kernel;
        let add = add_id(&g.ev());
        let nat = g.env.builtins().nat.expect("`Nat` is bound");
        let plus = |a: Term, b: Term| Term::app(Term::app(Term::Def(add), a), b);
        let succ = |t: Term| Term::ctor(nat, 1, vec![t]);
        let (x, y) = (|| Term::Var(1), || Term::Var(0));
        let big = || Term::Nat(Rc::new(BigUint::from(10u32).pow(30)));
        // Each sum, and what it must compute to.
        let cases = [
            ("x + 0", plus(x(), num(0)), x()),
            ("x + Zero", plus(x(), Term::Ctor(nat, 0, Vec::new())), x()),
            ("x + 1", plus(x(), num(1)), succ(x())),
            ("x + 3", plus(x(), num(3)), plus(num(3), x())),
            ("x + 3 = 3 + x", plus(x(), num(3)), plus(num(3), x())),
            ("x + Succ y", plus(x(), succ(y())), succ(plus(x(), y()))),
            (
                "x + (y + 2)",
                plus(x(), plus(y(), num(2))),
                plus(plus(x(), y()), num(2)),
            ),
            (
                "(2 + x) + (3 + y)",
                plus(plus(num(2), x()), plus(num(3), y())),
                plus(num(5), plus(x(), y())),
            ),
            ("0 + x", plus(num(0), x()), x()),
            ("x + y", plus(x(), y()), plus(x(), y())),
        ];
        let env = [Value::var(0), Value::var(1)];
        for (name, sum, expected) in &cases {
            in_every_mode(g, &env, 2, &[sum, expected], |g, v, evaluator, natives| {
                assert!(
                    conv(&g.ev(), 2, &v[0], &v[1], evaluator),
                    "{name}, {evaluator:?}, natives {natives}: {}",
                    shown(&g.ev(), 2, &v[0])
                );
            });
        }
        // Still not by computation: `x + y = y + x`, and `x + 1 = 1 + y`.
        for (name, a, b) in [
            ("x + y = y + x", plus(x(), y()), plus(y(), x())),
            ("x + 1 = 1 + y", plus(x(), num(1)), plus(num(1), y())),
        ] {
            in_every_mode(g, &env, 2, &[&a, &b], |g, v, evaluator, natives| {
                assert!(
                    !conv(&g.ev(), 2, &v[0], &v[1], evaluator),
                    "{name}, {evaluator:?}, natives {natives}"
                );
            });
        }
        // `x + 3` with the natives on is the compact `3 + x`, as `3 + x` is;
        // and so is `x + 10^30`, in one step (with the natives off too, but
        // then `10^30 + x` would count down).
        let value = value::eval(&g.ev(), &env, &plus(x(), num(3))).expect("no limits");
        assert!(matches!(value, Value::NatAdd(..)), "{value:?}");
        let value = value::eval(&g.ev(), &env, &plus(x(), big())).expect("no limits");
        let expected = value::eval(&g.ev(), &env, &plus(big(), x())).expect("no limits");
        assert!(matches!(value, Value::NatAdd(..)), "{value:?}");
        assert!(value::conv(&g.ev(), 2, &value, &expected).expect("no limits"));
    });
}

/// A copy of `Nat.add` is an ordinary definition: only the library's own
/// `Nat.add` (by content hash) computes on its second argument.
#[test]
fn the_rules_are_only_for_the_librarys_add() {
    let mut session = Session::new();
    let ok = session.load(
        "copy.sw",
        "def myAdd: Nat → Nat → Nat\n  | Zero, n => n\n  | Succ m, n => Succ (myAdd m n)\n\n\
         theorem first (x: Nat): myAdd 1 x = Succ x := byComputing\n",
    );
    assert!(ok.is_ok(), "{ok:?}");
    let refused = session.load(
        "copy2.sw",
        "def myAdd2: Nat → Nat → Nat\n  | Zero, n => n\n  | Succ m, n => Succ (myAdd2 m n)\n\n\
         theorem second (x: Nat): myAdd2 x 1 = Succ x := byComputing\n",
    );
    let codes: Vec<&str> = refused
        .err()
        .unwrap_or_default()
        .iter()
        .map(|d| d.code)
        .collect();
    assert_eq!(codes, ["E-REFL"]);
}

/// A stand-in for `Nat.addSucc` (an assumption of its statement) never
/// switches the rules on, even handed to `nat_add::register` directly:
/// they rest on the library's proofs, not on a gap.
#[test]
fn a_stand_in_never_switches_the_rules_on() {
    let mut session = Session::new();
    let g = &mut session.elab.kernel;
    let real = (g.env.registry())
        .def(Builtin::NatAddSucc)
        .expect("`Nat.addSucc` is bound");
    let (ty, span) = (g.def(real).ty().clone(), g.def(real).span());
    let name: stitchwort_core::Name = "Nat.addSucc".into();
    let stand_in = stitchwort_core::check::assume(
        g,
        &name,
        &name,
        &ty,
        stitchwort_core::globals::Assumption::error("Main.addSucc".into()),
        true,
        span,
    )
    .expect("a proposition");
    let refused = nat_add::register(g, stand_in).map_err(|d| d.code);
    assert_eq!(refused, Err("E-BUILTIN"));
    // Paired: the library's own theorem is accepted.
    assert!(nat_add::register(g, real).is_ok());
}

/// The unifier reads the rules backwards for a sum stuck on an unknown
/// (`plus_rule` in crates/elab/src/unify.rs, SW-896): `x + ?d` against a
/// `Succ` peels it. Where a solution needn't have that shape, or peeling
/// might not end, it does nothing, and these stay `E-REFL`.
#[test]
fn the_unifier_peels_succs_off_a_sum_stuck_on_an_unknown() {
    let mut session = Session::new();
    let ok = session.load(
        "peel.sw",
        "def three (x: Nat) (f: (d: Nat) → x + d = x + 3 → Nat): Nat := f _ byComputing\n\
         def left (x: Nat) (t: Nat) (f: (d: Nat) → d + x = Succ (t + x) → Nat): Nat := f _ byComputing\n\
         theorem solved (x: Nat): three x (d p => d) = 3 := byComputing\n",
    );
    assert!(ok.is_ok(), "{ok:?}");
    for (name, source) in [
        // `?d` inside the other side: `?d := Succ ?d'` would go on for ever.
        (
            "occurs",
            "def occurs (x: Nat) (f: (d: Nat) → x + d = Succ d → Nat): Nat := f _ byComputing\n",
        ),
        // Both summands unknown: `?c := Succ ?c'` would do as well.
        (
            "both",
            "def both (x: Nat) (f: (c: Nat) → (d: Nat) → c + d = Succ x → Nat): Nat := f _ _ byComputing\n",
        ),
        // The known summand mentions an unknown, so may yet be a `Succ`.
        (
            "inside",
            "def inside (x: Nat) (f: (c: Nat) → (d: Nat) → (c + x) + d = 3 + x → Nat): Nat := f _ _ byComputing\n",
        ),
        // Nothing to peel: `0` isn't a `Succ`, and `x` alone is left alone.
        (
            "zero",
            "def zero (x: Nat) (f: (d: Nat) → x + d = 0 → Nat): Nat := f _ byComputing\n",
        ),
        (
            "itself",
            "def itself (x: Nat) (f: (d: Nat) → x + d = x → Nat): Nat := f _ byComputing\n",
        ),
    ] {
        let refused = session.load(&format!("{name}.sw"), source);
        let codes: Vec<&str> = refused
            .err()
            .unwrap_or_default()
            .iter()
            .map(|d| d.code)
            .collect();
        assert_eq!(codes, ["E-REFL"], "{name}");
    }
}

/// A stuck sum is printed with its number on the right, as sums are
/// written (SW-895): `x + 1` and `x + 3`, not `Succ x` and `3 + x`; a
/// `Succ` written as one stays `Succ`; a number stays a number. Only the
/// printing readbacks do this: the kernel's `quote` still gives the terms
/// it gave before, `Succ x` and `3 + x`. `x` and `y` are variables (levels
/// 0 and 1).
#[test]
fn stuck_sums_are_printed_as_written() {
    let session = Session::new();
    let g = &session.elab.ev();
    let add = add_id(g);
    let nat = g.env.builtins().nat.expect("`Nat` is bound");
    let plus = |a: Term, b: Term| Term::app(Term::app(Term::Def(add), a), b);
    let succ = |t: Term| Term::ctor(nat, 1, vec![t]);
    let (x, y) = (|| Term::Var(1), || Term::Var(0));
    let names: Vec<stitchwort_core::Name> = vec!["x".into(), "y".into()];
    let env = [Value::var(0), Value::var(1)];
    // Each term, how it's printed, and the kernel's readback of its value.
    let cases = [
        (plus(x(), num(1)), "x + 1", succ(x())),
        (plus(num(1), x()), "x + 1", succ(x())),
        (plus(x(), num(3)), "x + 3", plus(num(3), x())),
        (plus(num(3), x()), "x + 3", plus(num(3), x())),
        (succ(plus(x(), num(2))), "x + 3", plus(num(3), x())),
        (
            plus(x(), plus(y(), num(2))),
            "x + y + 2",
            plus(num(2), plus(x(), y())),
        ),
        (succ(x()), "Succ x", succ(x())),
        (succ(succ(x())), "Succ (Succ x)", succ(succ(x()))),
        (plus(num(2), num(3)), "5", num(5)),
        (plus(x(), y()), "x + y", plus(x(), y())),
    ];
    for (term, printed, kernel) in &cases {
        let v = value::eval(g, &env, term).expect("no limits");
        assert_eq!(stitchwort_core::pretty::value(g, &names, &v), *printed);
        assert_eq!(
            stitchwort_core::pretty::value_for_message(g, &names, &v),
            *printed
        );
        assert_eq!(
            format!("{:?}", value::quote(g, 2, &v).expect("no limits")),
            format!("{kernel:?}"),
            "the kernel's readback of {printed}"
        );
        assert_eq!(
            format!("{:?}", value::quote_folded(g, 2, &v).expect("no limits")),
            format!("{kernel:?}"),
            "the elaborator's readback of {printed}"
        );
    }
}

/// A sum whose second argument is a glued call computing another such sum,
/// 100,000 deep, is read by R3 and R4 in constant stack: the machine forces
/// each link on its own heap stack (`Frame::ReadSecond` in `value.rs`)
/// rather than starting another machine per link, which took about 3 KiB
/// of stack a link (SW-4865; 2021 day 11's proofs have a 100-link chain).
/// `chain` reaches R3 and R4 where `add`'s case tree is stuck on `x`;
/// `succChain`, through `add`'s native, which takes the `Succ` off `x + 1`
/// first (`native::Outcome::AddStuck`).
#[test]
fn reading_a_long_chain_of_sums_takes_constant_stack() {
    const SMALL: usize = 4 << 20;
    with_stack(SMALL, || {
        let mut session = Session::for_stack(SMALL);
        let ok = session.load(
            "chain.sw",
            "def chain: Nat → Nat → Nat\n  | Zero, x => 0\n  | Succ k, x => x + chain k x\n\n\
             theorem long (x: Nat): chain 100000 x + 0 = chain 100000 x := byComputing\n\n\
             theorem longer (x: Nat): x + (chain 100000 x + 1) = Succ (x + chain 100000 x) := byComputing\n\n\
             def succChain: Nat → Nat → Nat\n  | Zero, x => 0\n  | Succ k, x => (x + 1) + succChain k x\n\n\
             theorem succLong (x: Nat): succChain 100000 x + 0 = succChain 100000 x := byComputing\n",
        );
        assert!(ok.is_ok(), "{ok:?}");
    });
}

/// A sum whose first argument is a number with a glued call inside, which
/// computes another such sum, 100,000 deep, takes constant stack: `+`'s
/// native comes to the call `leftChain k x` inside `Succ (leftChain k x)`, and the
/// machine forces it on its own heap stack and runs the native again
/// (`value::run_native`), as a number `case` does with its scrutinee
/// (`viaCase`), rather than starting another machine per link on the Rust
/// stack (SW-4878; both ran out of it about 16,000 deep on the CLI's 64
/// MiB).
#[test]
fn a_long_chain_of_sums_on_the_left_takes_constant_stack() {
    const SMALL: usize = 4 << 20;
    with_stack(SMALL, || {
        let mut session = Session::for_stack(SMALL);
        let ok = session.load(
            "left.sw",
            "def leftChain: Nat → Nat → Nat\n  | Zero, x => x\n  | Succ k, x => Succ (leftChain k x) + 1\n\n\
             theorem long (x: Nat): leftChain 100000 x = x + 200000 := byComputing\n\n\
             def viaCase: Nat → Nat → Nat\n  | Zero, x => x\n  | Succ k, x =>\n    match Succ (viaCase k x) with\n      | 0 => 0\n      | n => n + 0\n\n\
             theorem viaCaseLong (x: Nat): viaCase 100000 x = x + 100000 := byComputing\n",
        );
        assert!(ok.is_ok(), "{ok:?}");
    });
}

/// The chains of the test above, 40 deep: the machine, glued and not,
/// computes what the reference evaluator does.
#[test]
fn a_chain_of_sums_on_the_left_computes_as_the_reference_does() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let ok = session.load(
            "left.sw",
            "def leftChain: Nat → Nat → Nat\n  | Zero, x => x\n  | Succ k, x => Succ (leftChain k x) + 1\n\n\
             def viaCase: Nat → Nat → Nat\n  | Zero, x => x\n  | Succ k, x =>\n    match Succ (viaCase k x) with\n      | 0 => 0\n      | n => n + 0\n",
        );
        assert!(ok.is_ok(), "{ok:?}");
        let g = &session.elab.ev();
        let env = [Value::var(0)];
        for name in ["leftChain", "viaCase"] {
            let body = Term::app(Term::app(Term::Def(find(g, name)), num(40)), Term::Var(0));
            let expected = shown(g, 1, &reference::eval(g, &env, &body).expect("no limits"));
            for glue in [true, false] {
                let was = g.machine.glue.replace(glue);
                let value = value::eval(g, &env, &body).expect("no limits");
                g.machine.glue.set(was);
                assert_eq!(shown(g, 1, &value), expected, "`{name}`, glued {glue}");
            }
        }
    });
}

/// A native whose argument is a solved metavariable, replayed to
/// `Succ (slow x)` with `slow` glued, takes the steps it takes forcing with
/// `force` alone: the machine doesn't force `slow x` for the native and run
/// it again, which would replay the metavariable again and build a fresh
/// `slow x` to force, up to the rerun cap (`value::force_or_ask`, SW-4878).
/// The same for a number `case` on it.
#[test]
fn a_native_reading_a_solved_metavariable_takes_the_steps_force_does() {
    use stitchwort_core::Icit;
    use stitchwort_core::value::{Elim, Head};
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let ok = session.load(
            "meta.sw",
            "def walk: Nat → Nat → Nat\n  | Zero, y => y\n  | Succ k, y => walk k y\n\n\
             def slow (y: Nat): Nat := walk 30 y\n\n\
             def succSlow (y: Nat): Nat := Succ (slow y)\n\n\
             def isTwo (n: Nat): Nat :=\n  match n with\n    | 2 => 1\n    | _ => 0\n",
        );
        assert!(ok.is_ok(), "{ok:?}");
        let g = &session.elab.ev();
        let span =
            stitchwort_syntax::Span::point(stitchwort_syntax::SourceMap::new().add("t", ""), 0);
        let m = session.elab.metas().new_meta(span);
        let solution = value::eval(g, &[], &Term::Def(find(g, "succSlow"))).expect("no limits");
        session.elab.metas().solve_meta(m, solution);
        // `?m x`, for a variable `x`.
        let env = [Value::Neutral(
            Head::Meta(m),
            vec![Elim::App(Value::var(0), Icit::Explicit)].into(),
        )];
        let sum = Term::app(Term::app(Term::Def(add_id(g)), Term::Var(0)), num(1));
        let case = Term::app(Term::Def(find(g, "isTwo")), Term::Var(0));
        for term in [&sum, &case] {
            let run = |never_ask: bool| {
                let was = value::set_never_ask(never_ask);
                let glued = g.machine.glue.replace(true);
                let before = g.machine.budget.total_work();
                let result = value::eval(g, &env, term).expect("no limits");
                let steps = g.machine.budget.total_work() - before;
                g.machine.glue.set(glued);
                value::set_never_ask(was);
                (shown(g, 1, &result), steps)
            };
            assert_eq!(run(false), run(true), "asking, and forcing alone");
        }
    });
}

/// The definition whose name ends in `name`.
fn find(g: &stitchwort_core::Ev, name: &str) -> DefId {
    DefId(
        g.env
            .defs()
            .iter()
            .position(|d| d.name().ends_with(name))
            .unwrap_or_else(|| panic!("no `{name}`")),
    )
}

/// Reading a sum's second argument can stop to force a glued call part way
/// through, with `Succ`s counted already and some taken off the first
/// argument (`outer`): `(x + 1) + g 40 x` reads `g 40 x` as
/// `Succ (wrap (g 39 x) x)` and stops at the glued `wrap` call, which is
/// such a sum in turn. The machine, glued and not, computes what the
/// reference evaluator does.
#[test]
fn a_read_keeps_its_count_across_a_forced_call() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let ok = session.load(
            "wrap.sw",
            "def wrap (r: Nat) (x: Nat): Nat := (x + 1) + r\n\n\
             def g: Nat → Nat → Nat\n  | Zero, x => 0\n  | Succ k, x => Succ (wrap (g k x) x)\n\n\
             def top (x: Nat): Nat := (x + 1) + g 40 x\n",
        );
        assert!(ok.is_ok(), "{ok:?}");
        let g = &session.elab.ev();
        let body = Term::app(Term::Def(find(g, "top")), Term::Var(0));
        let env = [Value::var(0)];
        let expected = shown(g, 1, &reference::eval(g, &env, &body).expect("no limits"));
        for glue in [true, false] {
            let was = g.machine.glue.replace(glue);
            let value = value::eval(g, &env, &body).expect("no limits");
            g.machine.glue.set(was);
            assert_eq!(shown(g, 1, &value), expected, "glued {glue}");
        }
    });
}

/// The depth limit counts a forcing that a read of a sum's second argument
/// waits for on its own, as when that forcing was a machine of its own: a
/// recursion `outer` deep whose innermost sum reads a recursion `count`
/// deep is within a limit that the two together are over.
#[test]
fn a_read_counts_its_forcing_against_the_depth_limit_on_its_own() {
    with_stack(STACK, || {
        let program = |outer: u32, count: u32| {
            format!(
                "def count: Nat → Nat\n  | Zero => 0\n  | Succ k => 1 + count k\n\n\
                 def outer: Nat → Nat → Nat\n  | Zero, x => x + count {count}\n  | Succ k, x => 1 + outer k x\n\n\
                 theorem t (x: Nat): outer {outer} x = x + {} := byComputing\n",
                outer + count
            )
        };
        let first_error = |text: String| {
            let mut session = Session::for_stack(STACK);
            session.elab.options.limits.frames = 3_000;
            session.load("depth.sw", &text).err().map(|ds| ds[0].code)
        };
        assert_eq!(first_error(program(1_000, 1_000)), None);
        // One recursion as deep as the two together is over the limit.
        assert_eq!(first_error(program(2_000, 0)), Some("E-RESOURCE"));
    });
}

/// A chain of stuck sums past `MAX_PENDING_SEGMENTS` (`value.rs`) is refused for depth even
/// where the frame limit allows it, instead of growing without bound.
#[test]
fn a_chain_of_sums_past_the_pending_read_cap_is_refused() {
    const SMALL: usize = 4 << 20;
    with_stack(SMALL, || {
        let mut session = Session::for_stack(SMALL);
        session.elab.options.limits.frames = 100_000_000;
        let first = session
            .load(
                "chain.sw",
                "def chain: Nat → Nat → Nat\n  | Zero, x => 0\n  | Succ k, x => x + chain k x\n\n\
                 theorem long (x: Nat): chain 210000 x + 0 = chain 210000 x := byComputing\n",
            )
            .err()
            .map(|ds| ds[0].code);
        assert_eq!(first, Some("E-RESOURCE"));
    });
}

/// A `case` whose scrutinee is a stuck sum with a call folded by name in
/// its second argument (`wrap`, a `decreasing` definition), whose unfolding
/// is another such `case`: `posOf` on `x + wrap 0 x (foldedChain k x)`, and a
/// number `case`, `smallOf`, through `wrap 1`. Rule E reads each sum
/// (`nat_add::reread`), unfolding `wrap`'s call and forcing what it gives.
const FOLDED_CHAIN: &str = "def posOf (n: Nat): Nat :=\n  match n with\n    | Zero => 0\n    | Succ _ => 1\n\n\
     def smallOf (n: Nat): Nat :=\n  match n with\n    | 0 => 0\n    | _ => 1\n\n\
     def wrap (n: Nat) (x: Nat) (r: Nat): Nat\n    decreasing n\n:=\n  match n with\n    | Zero => posOf (x + r)\n    | Succ m => smallOf (x + wrap m x r [decreasing := arithmetic])\n\n\
     def foldedChain: Nat → Nat → Nat\n  | Zero, x => 1\n  | Succ k, x => wrap 0 x (foldedChain k x)\n\n\
     def foldedChainN: Nat → Nat → Nat\n  | Zero, x => 1\n  | Succ k, x => wrap 1 x (foldedChainN k x)\n";

/// The chains of [`FOLDED_CHAIN`], 100,000 and 90,000 deep, take constant
/// stack: the machine does rule E's forcing and unfolding on its own heap
/// stack (`value::reread_on`), rather than starting a machine for each,
/// which ran out of the CLI's 64 MiB of stack about 16,000 deep (SW-4881).
/// A link of `foldedChainN` leaves two forcings pending, each once a
/// machine of its own, so 100,000 of them would be past
/// `MAX_PENDING_SEGMENTS` (`value.rs`).
#[test]
fn a_long_chain_through_rule_e_takes_constant_stack() {
    const SMALL: usize = 4 << 20;
    with_stack(SMALL, || {
        let mut session = Session::for_stack(SMALL);
        let ok = session.load(
            "folded.sw",
            &format!(
                "{FOLDED_CHAIN}\n\
                 theorem long (x: Nat): posOf (x + foldedChain 100000 x) = 1 := byComputing\n\n\
                 theorem longN (x: Nat): smallOf (x + foldedChainN 90000 x) = 1 := byComputing\n"
            ),
        );
        assert!(ok.is_ok(), "{ok:?}");
    });
}

/// The chains of [`FOLDED_CHAIN`], 40 deep: the machine, glued and not,
/// computes what the reference evaluator does, and takes the steps it
/// takes reading each sum with machines of its own
/// (`value::set_nested_reread`).
#[test]
fn a_chain_through_rule_e_computes_and_steps_as_before() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let ok = session.load("folded.sw", FOLDED_CHAIN);
        assert!(ok.is_ok(), "{ok:?}");
        let g = &session.elab.ev();
        let env = [Value::var(0)];
        for (case, chain) in [("posOf", "foldedChain"), ("smallOf", "foldedChainN")] {
            let sum = Term::app(
                Term::app(Term::Def(add_id(g)), Term::Var(0)),
                Term::app(Term::app(Term::Def(find(g, chain)), num(40)), Term::Var(0)),
            );
            let body = Term::app(Term::Def(find(g, case)), sum);
            let expected = shown(g, 1, &reference::eval(g, &env, &body).expect("no limits"));
            for glue in [true, false] {
                let run = |nested: bool| {
                    let was = value::set_nested_reread(nested);
                    let glued = g.machine.glue.replace(glue);
                    let before = g.machine.budget.total_work();
                    let runs = value::machine_runs();
                    let result = value::eval(g, &env, &body).expect("no limits");
                    let result = value::force(g, result).expect("no limits");
                    let steps = g.machine.budget.total_work() - before;
                    let runs = value::machine_runs() - runs;
                    g.machine.glue.set(glued);
                    value::set_nested_reread(was);
                    ((shown(g, 1, &result), steps), runs)
                };
                let (now, runs_now) = run(false);
                let (nested, runs_nested) = run(true);
                assert_eq!(now.0, expected, "`{case}`, glued {glue}");
                assert_eq!(
                    now, nested,
                    "`{case}`, glued {glue}: on this stack, and nested"
                );
                // Rule E's reads were machines of their own, 40 deep.
                assert!(
                    runs_now + 40 <= runs_nested,
                    "`{case}`, glued {glue}: {runs_now} machines, {runs_nested} nested"
                );
            }
        }
    });
}

/// A float native whose argument is a glued call, `Float.ofNat (slow 0)`,
/// has this machine force the call and then runs again (`value::run_float`),
/// as `+`'s native does: it gives what forcing with `force` alone gives, in
/// the same steps, with one machine fewer (SW-4881).
#[test]
fn a_float_native_forcing_a_glued_call_takes_the_steps_force_does() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        let ok = session.load(
            "float.sw",
            "import Std (Float)\n\n\
             def walk: Nat → Nat → Nat\n  | Zero, y => y\n  | Succ k, y => walk k y\n\n\
             def slow (y: Nat): Nat := walk 30 y\n\n\
             def floated (y: Nat): Float := Float.ofNat (slow y)\n",
        );
        assert!(ok.is_ok(), "{ok:?}");
        let g = &session.elab.ev();
        let body = Term::app(Term::Def(find(g, "floated")), num(7));
        let run = |never_ask: bool| {
            let was = value::set_never_ask(never_ask);
            let glued = g.machine.glue.replace(true);
            let before = g.machine.budget.total_work();
            let runs = value::machine_runs();
            let result =
                value::force(g, value::eval(g, &[], &body).expect("no limits")).expect("no limits");
            let steps = g.machine.budget.total_work() - before;
            let runs = value::machine_runs() - runs;
            g.machine.glue.set(glued);
            value::set_never_ask(was);
            ((shown(g, 0, &result), steps), runs)
        };
        let (asking, runs_asking) = run(false);
        let (forcing, runs_forcing) = run(true);
        assert_eq!(asking, forcing, "asking, and forcing alone");
        assert!(
            runs_asking < runs_forcing,
            "{runs_asking} machines asking, {runs_forcing} forcing"
        );
    });
}
