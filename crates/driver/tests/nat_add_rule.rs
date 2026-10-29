//! `+` computes on its second argument too (`stitchwort_core::nat_add`,
//! SW-787): R3 `m + Zero → m` and R4 `m + Succ n → Succ (m + n)`, beside
//! `Nat.add`'s own R1 and R2. The rules are trusted, so these check them
//! with both evaluators (the machine and the reference), natives on and
//! off: the critical pairs join, stuck sums compute the same everywhere,
//! and the rules are bound only to the library's `Nat.add`.

use std::rc::Rc;

use stitchwort_core::nat_add;
use stitchwort_core::native;
use stitchwort_core::reference;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{self, Value};
use stitchwort_core::{BigUint, DefId, Globals, Term};
use stitchwort_driver::driver::{Session, with_stack};

/// Room for the reference evaluator's recursion.
const STACK: usize = 64 * 1024 * 1024;

#[derive(Clone, Copy, Debug)]
enum Evaluator {
    Machine,
    Reference,
}

/// `term` evaluated in `env` by `evaluator`, with the natives as they are.
fn eval(g: &Globals, env: &[Value], term: &Term, evaluator: Evaluator) -> Value {
    match evaluator {
        Evaluator::Machine => value::eval(g, env, term).expect("no limits"),
        Evaluator::Reference => reference::eval(g, env, term).expect("no limits"),
    }
}

/// Whether `a` and `b` are convertible, by `evaluator`'s own conversion.
fn conv(g: &Globals, level: usize, a: &Value, b: &Value, evaluator: Evaluator) -> bool {
    match evaluator {
        Evaluator::Machine => value::conv(g, level, a, b).expect("no limits"),
        Evaluator::Reference => reference::conv(g, level, a, b).expect("no limits"),
    }
}

/// A normal form, printed by the reference's `quote` (so the machine's
/// quoting can't hide a difference).
fn shown(g: &Globals, level: usize, value: &Value) -> String {
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
    g: &mut Globals,
    env: &[Value],
    level: usize,
    terms: &[&Term],
    mut check: impl FnMut(&Globals, &[Value], Evaluator, bool),
) {
    for natives in [true, false] {
        g.builtins.disable_natives = !natives;
        let fast: Vec<Value> = terms
            .iter()
            .map(|t| eval(g, env, t, Evaluator::Machine))
            .collect();
        let slow: Vec<Value> = terms
            .iter()
            .map(|t| eval(g, env, t, Evaluator::Reference))
            .collect();
        for (f, s) in fast.iter().zip(&slow) {
            assert_eq!(
                shown(g, level, f),
                shown(g, level, s),
                "the evaluators disagree (natives {natives})"
            );
        }
        check(g, &fast, Evaluator::Machine, natives);
        check(g, &slow, Evaluator::Reference, natives);
        g.builtins.disable_natives = false;
    }
}

fn add_id(g: &Globals) -> DefId {
    g.registry.def(Builtin::Add).expect("`Nat.add` is bound")
}

fn num(n: u64) -> Term {
    Term::Nat(Rc::new(BigUint::from(n)))
}

/// The prelude's `Nat.add` is the one the rules were written for, and they
/// are on. If this fails, the library changed `Nat.add` or `Nat` (the load
/// fails with `E-BUILTIN`, printing the new hash): check the rules in
/// crates/core/src/nat_add.rs are still its equations, then pin the hash.
#[test]
fn nat_add_is_the_pinned_declaration() {
    let session = Session::new();
    let g = &session.elab.globals;
    assert_eq!(nat_add::add_hash(g).as_deref(), Some(nat_add::NAT_ADD_HASH));
    assert_eq!(g.builtins.nat_add_rule, Some(add_id(g)));
}

/// Each critical pair of R1 to R4 joins: the sum and the two terms the
/// overlapping rules rewrite it to are convertible, with each evaluator,
/// natives on and off, with `m` and `n` variables, numbers, or a number
/// plus a variable; and both evaluators give each the same normal form.
#[test]
fn the_critical_pairs_join() {
    with_stack(STACK, || {
        let mut session = Session::new();
        let g = &mut session.elab.globals;
        let pairs = nat_add::critical_pairs(g, add_id(g)).expect("`Nat` is bound");
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
                        assert!(conv(g, 3, &v[1], &v[2], evaluator), "{what}: the two sides");
                        assert!(conv(g, 3, &v[0], &v[1], evaluator), "{what}: the sum");
                        checked += 1;
                    });
                }
            }
        }
        assert_eq!(checked, 4 * 4 * 4 * 4);
    });
}

/// Sums stuck on their first argument compute on their second, to the same
/// value with each evaluator, natives on and off; and a sum stuck on both
/// stays stuck. `x` and `y` are variables (levels 0 and 1).
#[test]
fn stuck_sums_compute_on_their_second_argument() {
    with_stack(STACK, || {
        let mut session = Session::new();
        let g = &mut session.elab.globals;
        let add = add_id(g);
        let nat = g.builtins.nat.expect("`Nat` is bound");
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
                    conv(g, 2, &v[0], &v[1], evaluator),
                    "{name}, {evaluator:?}, natives {natives}: {}",
                    shown(g, 2, &v[0])
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
                    !conv(g, 2, &v[0], &v[1], evaluator),
                    "{name}, {evaluator:?}, natives {natives}"
                );
            });
        }
        // `x + 3` with the natives on is the compact `3 + x`, as `3 + x` is;
        // and so is `x + 10^30`, in one step (with the natives off too, but
        // then `10^30 + x` would count down).
        let value = value::eval(g, &env, &plus(x(), num(3))).expect("no limits");
        assert!(matches!(value, Value::NatAdd(..)), "{value:?}");
        let value = value::eval(g, &env, &plus(x(), big())).expect("no limits");
        let expected = value::eval(g, &env, &plus(big(), x())).expect("no limits");
        assert!(matches!(value, Value::NatAdd(..)), "{value:?}");
        assert!(value::conv(g, 2, &value, &expected).expect("no limits"));
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
         theorem first (x: Nat): myAdd 1 x = Succ x := rfl\n",
    );
    assert!(ok.is_ok(), "{ok:?}");
    let refused = session.load(
        "copy2.sw",
        "def myAdd2: Nat → Nat → Nat\n  | Zero, n => n\n  | Succ m, n => Succ (myAdd2 m n)\n\n\
         theorem second (x: Nat): myAdd2 x 1 = Succ x := rfl\n",
    );
    let codes: Vec<&str> = refused
        .err()
        .unwrap_or_default()
        .iter()
        .map(|d| d.code)
        .collect();
    assert_eq!(codes, ["E-REFL"]);
}
