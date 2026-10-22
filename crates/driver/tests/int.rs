//! `Int` (docs/proposals/integers.md, "Testing the definitions (R2)").
//!
//! `Int` is an ordinary prelude data type over `Nat`, with no natives of its
//! own, so its definitions drive the `Nat` natives through shapes the `Nat`
//! tests don't: subtractions whose result picks a constructor, divisions by
//! `Succ n`, decisions wrapped in `Eq.cong`. Each test here evaluates with
//! every native on and with every native off, in both evaluators (the
//! machine and `reference.rs`), and compares the whole normal forms, proofs
//! and stuck terms included, not decoded answers. A theorem stays folded
//! while checking (SW-281), so where natives on give `refl` natives off may
//! give a theorem's call: those two must then be definitionally equal, which
//! unfolds the call.

use num_bigint::{BigInt, Sign};
use num_traits::Zero;
use stitchwort_core::native::{self, as_nat};
use stitchwort_core::reference;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{self, Value};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Term};
use stitchwort_driver::driver::{Session, with_stack};

/// Room for the definitions' unary recursion when natives are off.
const STACK: usize = 64 << 20;

/// The prelude's definition `name` (`Int.add`).
fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .position(|d| &*d.name == name)
            .unwrap_or_else(|| panic!("no `{name}` in the prelude")),
    )
}

fn int_data(g: &Globals) -> DataId {
    g.registry.data(Builtin::Int).expect("`Int` is registered")
}

fn nat(n: u64) -> Value {
    native::nat_value(BigUint::from(n))
}

/// `k + x` for the variable at `level`.
fn plus_var(k: u64, level: usize) -> Value {
    native::from_view(BigUint::from(k), Some(Value::var(level)))
}

fn of_nat(g: &Globals, n: Value) -> Value {
    Value::Ctor(int_data(g), 0, vec![n].into())
}

fn neg_succ(g: &Globals, n: Value) -> Value {
    Value::Ctor(int_data(g), 1, vec![n].into())
}

/// The integer `i`, in its one form.
fn int(g: &Globals, i: i64) -> Value {
    if i >= 0 {
        of_nat(g, nat(i as u64))
    } else {
        neg_succ(g, nat((-1 - i) as u64))
    }
}

/// The integer a closed value is, if it's one.
fn as_int(g: &Globals, v: &Value) -> Option<i64> {
    match value::force(g, v.clone()).ok()? {
        Value::Ctor(d, c, fields) if d == int_data(g) => {
            let n = i64::try_from(as_nat(g, &fields[0]).ok()??).ok()?;
            Some(if c == 0 { n } else { -1 - n })
        }
        _ => None,
    }
}

/// An argument and how it's passed.
#[derive(Clone)]
struct Arg(Value, Icit);

fn ex(v: Value) -> Arg {
    Arg(v, Icit::Explicit)
}

/// The proof of `d != 0` that division takes, as a variable: it's only used
/// in the impossible branch, which a test never reaches with a closed divisor.
fn proof(level: usize) -> Arg {
    Arg(Value::var(level), Icit::Auto)
}

/// `f args` by the machine: its value and normal form.
fn machine(g: &Globals, f: DefId, args: &[Arg], level: usize) -> (Value, String) {
    let mut v = value::eval(g, &[], &Term::Def(f)).expect("no limits");
    for Arg(a, icit) in args {
        v = value::apply_icit(g, v, a.clone(), *icit).expect("no limits");
    }
    let v = value::force(g, v).expect("no limits");
    let nf = format!("{:?}", value::quote(g, level, &v).expect("no limits"));
    (v, nf)
}

/// `f args` by the reference evaluator: its normal form.
fn slow(g: &Globals, f: DefId, args: &[Arg], level: usize) -> String {
    let mut v = reference::eval(g, &[], &Term::Def(f)).expect("no limits");
    for Arg(a, icit) in args {
        v = reference::apply_icit(g, v, a.clone(), *icit).expect("no limits");
    }
    let v = reference::force(g, v).expect("no limits");
    format!("{:?}", reference::quote(g, level, &v).expect("no limits"))
}

/// `f args` four ways (natives on and off, each in both evaluators), which
/// must give the same normal form: the machine's value with natives on, and
/// that normal form. `level` variables are free in `args`.
fn run(g: &mut Globals, f: DefId, args: &[Arg], level: usize) -> (Value, String) {
    let name = g.def(f).name.clone();
    let what = || format!("{name} {:?}", args.iter().map(|a| &a.0).collect::<Vec<_>>());
    let (v, on) = machine(g, f, args, level);
    let on_slow = slow(g, f, args, level);
    g.builtins.disable_natives = true;
    let (v_off, off) = machine(g, f, args, level);
    let off_slow = slow(g, f, args, level);
    g.builtins.disable_natives = false;
    assert_eq!(
        on,
        on_slow,
        "{}: the evaluators disagree, natives on",
        what()
    );
    assert_eq!(
        off,
        off_slow,
        "{}: the evaluators disagree, natives off",
        what()
    );
    if on != off {
        assert!(
            value::conv(g, level, &v, &v_off).expect("no limits"),
            "{}: natives on and off disagree\n  on: {on}\n off: {off}",
            what()
        );
    }
    (v, on)
}

/// `f args` four ways, which must agree, and compute to the integer
/// `expected`.
fn computes(g: &mut Globals, f: &str, args: &[Arg], level: usize, expected: i64) {
    let id = def(g, f);
    let (v, nf) = run(g, id, args, level);
    assert_eq!(as_int(g, &v), Some(expected), "{f}: {nf}");
}

/// `f args` four ways, which must agree, and compute to `expected`, which
/// may have variables in it.
fn computes_to(g: &mut Globals, f: &str, args: &[Arg], level: usize, expected: &Value) {
    let id = def(g, f);
    let (v, nf) = run(g, id, args, level);
    assert!(
        value::conv(g, level, &v, expected).expect("no limits"),
        "{f}: {nf}, expected {:?}",
        value::quote(g, level, expected)
    );
}

/// `f args` four ways, which must agree, and be stuck: not a constructor.
fn stuck(g: &mut Globals, f: &str, args: &[Arg], level: usize) -> String {
    let id = def(g, f);
    let (v, nf) = run(g, id, args, level);
    assert!(matches!(v, Value::Neutral(..)), "{f}: {nf} isn't stuck");
    nf
}

/// R2 test 2: named edge cases, closed.
#[test]
fn edge_cases_agree_in_both_modes() {
    with_stack(STACK, || {
        let mut session = Session::eager();
        let g = &mut session.elab.globals;
        for n in 0..8u64 {
            // `subNatNat 0 n`, `subNatNat n 0`, `subNatNat n n`.
            computes(
                g,
                "Int.subNatNat",
                &[ex(nat(0)), ex(nat(n))],
                0,
                -(n as i64),
            );
            computes(g, "Int.subNatNat", &[ex(nat(n)), ex(nat(0))], 0, n as i64);
            computes(g, "Int.subNatNat", &[ex(nat(n)), ex(nat(n))], 0, 0);
            for m in 0..8u64 {
                let (ni, mi) = (n as i64, m as i64);
                // `subNatNat (Succ n) (Succ m)`, by `Succ` around a number.
                let succ = |k: u64| native::from_view(BigUint::from(1u32), Some(nat(k)));
                computes(g, "Int.subNatNat", &[ex(succ(n)), ex(succ(m))], 0, ni - mi);
                // `OfNat n + NegSucc m`, both orders, with `n` above, equal to
                // and below `m + 1`.
                let (a, b) = (of_nat(g, nat(n)), neg_succ(g, nat(m)));
                computes(
                    g,
                    "Int.add",
                    &[ex(a.clone()), ex(b.clone())],
                    0,
                    ni - mi - 1,
                );
                computes(g, "Int.add", &[ex(b), ex(a)], 0, ni - mi - 1);
            }
        }
        // Division on each side of zero, and by `1` and `-1`.
        for a in -4..=4i64 {
            for d in [-3, -2, -1, 1, 2, 3i64] {
                let args = [ex(int(g, a)), ex(int(g, d)), proof(0)];
                let (q, r) = (a.div_euclid(d), a.rem_euclid(d));
                computes(g, "Int.div", &args, 1, q);
                computes(g, "Int.mod", &args, 1, r);
                computes(g, "Int.tdiv", &args, 1, a / d);
                computes(g, "Int.tmod", &args, 1, a % d);
                let fq = (a as f64 / d as f64).floor() as i64;
                computes(g, "Int.fdiv", &args, 1, fq);
                computes(g, "Int.fmod", &args, 1, a - d * fq);
            }
        }
    });
}

/// R2 test 2: `Int.decEq`'s whole result, proofs included, is the same with
/// natives on and off; and it's `Yes rfl` when the integers are equal.
#[test]
fn decisions_agree_in_both_modes() {
    with_stack(STACK, || {
        let mut session = Session::eager();
        let g = &mut session.elab.globals;
        let dec_eq = def(g, "Int.decEq");
        let (_, yes) = g.registry.ctor(Builtin::Yes).expect("`Yes`");
        for a in -6..=6i64 {
            for b in -6..=6i64 {
                let (v, nf) = run(g, dec_eq, &[ex(int(g, a)), ex(int(g, b))], 0);
                let Value::Ctor(_, c, fields) = &v else {
                    panic!("Int.decEq {a} {b}: {nf}")
                };
                if a == b {
                    assert_eq!(*c, yes, "Int.decEq {a} {b}: {nf}");
                    // A folded theorem's call (`Eq.cong`) that unfolds to
                    // `refl`.
                    let p = fields.last().unwrap();
                    assert!(
                        value::conv(g, 0, p, &Value::Refl).unwrap(),
                        "Int.decEq {a} {b}: {nf}"
                    );
                } else {
                    assert_ne!(*c, yes, "Int.decEq {a} {b}: {nf}");
                }
            }
        }
    });
}

/// R2 test 3: open terms. Rigid variables (levels 0 and 1), and numbers
/// partly known in `k + x` form: what computes in one mode computes to the
/// same thing in the other, and what's stuck is stuck on the same term.
#[test]
fn open_terms_agree_in_both_modes() {
    with_stack(STACK, || {
        let mut session = Session::eager();
        let g = &mut session.elab.globals;
        let (x, y) = (Value::var(0), Value::var(1));

        // `OfNat (x + 5) + NegSucc 2` is `OfNat (x + 2)`; `NegSucc (x + 5) +
        // OfNat 2`, either way round, is `NegSucc (x + 3)`.
        let expected = of_nat(g, plus_var(2, 0));
        let args = [ex(of_nat(g, plus_var(5, 0))), ex(neg_succ(g, nat(2)))];
        computes_to(g, "Int.add", &args, 1, &expected);
        let expected = neg_succ(g, plus_var(3, 0));
        let args = [ex(neg_succ(g, plus_var(5, 0))), ex(of_nat(g, nat(2)))];
        computes_to(g, "Int.add", &args, 1, &expected);
        let args = [ex(of_nat(g, nat(2))), ex(neg_succ(g, plus_var(5, 0)))];
        computes_to(g, "Int.add", &args, 1, &expected);
        // `OfNat (x + 2) + NegSucc 5` depends on whether `x` is at least 4.
        let args = [ex(of_nat(g, plus_var(2, 0))), ex(neg_succ(g, nat(5)))];
        stuck(g, "Int.add", &args, 1);
        // Same constructors: computes, around the variables.
        let args = [ex(of_nat(g, x.clone())), ex(of_nat(g, y.clone()))];
        let (_, nf) = run(g, def(g, "Int.add"), &args, 2);
        assert!(nf.contains("Ctor"), "OfNat x + OfNat y: {nf}");
        // `NegSucc x + NegSucc 0` is `NegSucc (Succ (x + 0))`, where `x + 0`
        // is stuck: `Nat.add` recurses on its first argument.
        let args = [ex(neg_succ(g, x.clone())), ex(neg_succ(g, nat(0)))];
        let (v, nf) = run(g, def(g, "Int.add"), &args, 1);
        assert!(matches!(v, Value::Ctor(..)), "NegSucc x + NegSucc 0: {nf}");

        // `subNatNat` around unknowns: stuck where the subtraction is.
        for args in [
            [ex(nat(0)), ex(x.clone())],
            [ex(x.clone()), ex(nat(0))],
            [ex(x.clone()), ex(x.clone())],
            [ex(plus_var(1, 0)), ex(plus_var(1, 1))],
            [ex(x.clone()), ex(y.clone())],
        ] {
            stuck(g, "Int.subNatNat", &args, 2);
        }
        // `subNatNat (x + 3) 1` is `OfNat (x + 2)`; `subNatNat 1 (x + 3)` is
        // `NegSucc (x + 1)`.
        let expected = of_nat(g, plus_var(2, 0));
        computes_to(
            g,
            "Int.subNatNat",
            &[ex(plus_var(3, 0)), ex(nat(1))],
            1,
            &expected,
        );
        let expected = neg_succ(g, plus_var(1, 0));
        computes_to(
            g,
            "Int.subNatNat",
            &[ex(nat(1)), ex(plus_var(3, 0))],
            1,
            &expected,
        );

        // Negation and multiplication by constructors.
        let expected = neg_succ(g, x.clone());
        let args = [ex(of_nat(g, plus_var(1, 0)))];
        computes_to(g, "Int.neg", &args, 1, &expected);
        stuck(g, "Int.neg", &[ex(of_nat(g, x.clone()))], 1);
        run(
            g,
            def(g, "Int.mul"),
            &[ex(of_nat(g, x.clone())), ex(neg_succ(g, y.clone()))],
            2,
        );

        // Decisions: different constructors decide at once, whatever the
        // fields; the same constructor waits for its fields.
        for args in [
            [ex(of_nat(g, x.clone())), ex(neg_succ(g, y.clone()))],
            [ex(neg_succ(g, x.clone())), ex(of_nat(g, y.clone()))],
        ] {
            let (v, nf) = run(g, def(g, "Int.decEq"), &args, 2);
            assert!(matches!(v, Value::Ctor(..)), "{nf}");
        }
        for args in [
            [ex(neg_succ(g, x.clone())), ex(neg_succ(g, y.clone()))],
            [ex(neg_succ(g, x.clone())), ex(neg_succ(g, x.clone()))],
            [ex(of_nat(g, x.clone())), ex(of_nat(g, nat(3)))],
            [ex(of_nat(g, plus_var(2, 0))), ex(of_nat(g, nat(5)))],
        ] {
            let (v, nf) = run(g, def(g, "Int.decEq"), &args, 2);
            assert!(matches!(v, Value::Neutral(..)), "{nf}");
        }
        // `OfNat (x + 2) = OfNat 1` is decided: `x + 2` isn't `1`.
        let args = [ex(of_nat(g, plus_var(2, 0))), ex(of_nat(g, nat(1)))];
        let (v, nf) = run(g, def(g, "Int.decEq"), &args, 1);
        assert!(matches!(v, Value::Ctor(..)), "{nf}");

        // Division: an unknown divisor is stuck (the zero case needs to see
        // it); an unknown dividend over a known divisor computes to a
        // constructor around a stuck `Nat` division.
        for op in [
            "Int.div", "Int.mod", "Int.tdiv", "Int.tmod", "Int.fdiv", "Int.fmod",
        ] {
            stuck(
                g,
                op,
                &[ex(int(g, 7)), ex(of_nat(g, x.clone())), proof(1)],
                2,
            );
            stuck(g, op, &[ex(int(g, 7)), ex(x.clone()), proof(1)], 2);
            for d in [-3, 3] {
                let args = [ex(of_nat(g, plus_var(1, 0))), ex(int(g, d)), proof(1)];
                run(g, def(g, op), &args, 2);
                let args = [ex(neg_succ(g, x.clone())), ex(int(g, d)), proof(1)];
                run(g, def(g, op), &args, 2);
            }
        }
        stuck(
            g,
            "Int.modNat",
            &[ex(int(g, -18)), ex(x.clone()), proof(1)],
            2,
        );
        let args = [ex(neg_succ(g, x.clone())), ex(nat(100)), proof(1)];
        run(g, def(g, "Int.modNat"), &args, 2);
    });
}

/// Loads `source` after the prelude, with natives on or off: the error
/// codes.
fn load(source: &str, natives: bool) -> Vec<&'static str> {
    let mut session = Session::eager();
    session.elab.globals.builtins.disable_natives = !natives;
    match session.load("int.sw", source) {
        Ok(_) => Vec::new(),
        Err(ds) => ds.iter().map(|d| d.code).collect(),
    }
}

const CHECK4: &str = "\
import Std (Int)

type Tag (n : Nat) : Type =
  | MkTag

def check4 (a : Nat) (p : Int.subNatNat a 1 = Int.OfNat 4) : Unit := Trivial

def checkAuto (a : Nat) [auto ok : Int.subNatNat a 1 = Int.OfNat 4] (t : Tag a) : Unit := Trivial

def tag5 : Tag 5 := MkTag
";

/// R2 test 4: an `Int` operation on a metavariable, before and after it's
/// solved. The elaborator mustn't solve `a` by inverting `subNatNat`.
#[test]
fn metavariables_under_int_operations() {
    with_stack(STACK, || {
        for natives in [true, false] {
            let case = |body: &str| load(&format!("{CHECK4}\n{body}\n"), natives);
            // Solved first: by the argument written before.
            assert_eq!(case("def t : Unit := check4 5 rfl"), Vec::<&str>::new());
            // Never solved: `rfl` fails rather than solving `_` by inverting `subNatNat`.
            assert_eq!(
                case("def t : Unit := check4 _ rfl"),
                ["E-REFL"],
                "natives {natives}"
            );
            // An `==` with an unknown side.
            assert_eq!(
                case("def t : Bool := Int.subNatNat _ 1 == Int.OfNat 4"),
                ["E-UNSOLVED"],
                "natives {natives}"
            );
            // Solved by a later argument, before the `auto` obligation is
            // proved: the obligation is `subNatNat 5 1 = OfNat 4`.
            assert_eq!(case("def t : Unit := checkAuto _ tag5"), Vec::<&str>::new());
            // The same, with a value that doesn't satisfy it.
            assert_eq!(
                case("def tag6 : Tag 6 := MkTag\n\ndef t : Unit := checkAuto _ tag6"),
                ["E-AUTO-FALSE"],
                "natives {natives}"
            );
            // Never solved, with an `auto` obligation waiting on it.
            assert_eq!(
                case("def t : Unit := checkAuto _ MkTag"),
                ["E-AUTO-STUCK"],
                "natives {natives}"
            );
        }
    });
}

/// The operations, with their parameters' kinds: `I` an integer, `N` a
/// natural, `P` the proof that the divisor isn't zero.
const OPS: &[(&str, &str)] = &[
    ("Int.neg", "I"),
    ("Int.add", "II"),
    ("Int.sub", "II"),
    ("Int.mul", "II"),
    ("Int.leq", "II"),
    ("Int.less", "II"),
    ("Int.compare", "II"),
    ("Int.decEq", "II"),
    ("Int.div", "IIP"),
    ("Int.mod", "IIP"),
    ("Int.tdiv", "IIP"),
    ("Int.tmod", "IIP"),
    ("Int.fdiv", "IIP"),
    ("Int.fmod", "IIP"),
    ("Int.modNat", "INP"),
    ("Int.subNatNat", "NN"),
];

/// Flooring division, from Rust's truncating division.
fn floor_div(a: i64, d: i64) -> i64 {
    let q = a / d;
    if a % d != 0 && (a < 0) != (d < 0) {
        q - 1
    } else {
        q
    }
}

/// What `op a b` should be, from Rust's own arithmetic, when it's a number.
fn expected(op: &str, a: i64, b: i64) -> Option<i64> {
    Some(match op {
        "Int.neg" => -a,
        "Int.add" | "Int.subNatNat" => a + if op == "Int.add" { b } else { -b },
        "Int.sub" => a - b,
        "Int.mul" => a * b,
        "Int.div" => a.div_euclid(b),
        "Int.mod" | "Int.modNat" => a.rem_euclid(b),
        "Int.tdiv" => a / b,
        "Int.tmod" => a % b,
        "Int.fdiv" => floor_div(a, b),
        "Int.fmod" => a - b * floor_div(a, b),
        _ => return None,
    })
}

/// R2 test 1: every operation on every argument in `-12..=12` (naturals
/// from 0, divisors not zero), natives on and off, in both evaluators.
#[test]
fn every_operation_agrees_in_both_modes_on_small_arguments() {
    with_stack(STACK, || {
        let mut session = Session::eager();
        let g = &mut session.elab.globals;
        for &(op, kinds) in OPS {
            let id = def(g, op);
            let kinds = kinds.as_bytes();
            let unary = kinds.len() == 1;
            for a in -12..=12i64 {
                for b in if unary { 0..=0 } else { -12..=12 } {
                    let natural = |k: usize, i: i64| kinds.get(k) == Some(&b'N') && i < 0;
                    if natural(0, a) || natural(1, b) || (kinds.len() == 3 && b == 0) {
                        continue;
                    }
                    let arg = |k: usize, i: i64| match kinds[k] {
                        b'I' => ex(int(g, i)),
                        _ => ex(nat(i as u64)),
                    };
                    let mut args = vec![arg(0, a)];
                    if !unary {
                        args.push(arg(1, b));
                    }
                    if kinds.len() == 3 {
                        args.push(proof(0));
                    }
                    let (v, nf) = run(g, id, &args, 1);
                    if let Some(want) = expected(op, a, b) {
                        let got = if op == "Int.modNat" {
                            as_nat(g, &v).unwrap().and_then(|n| i64::try_from(n).ok())
                        } else {
                            as_int(g, &v)
                        };
                        assert_eq!(got, Some(want), "{op} {a} {b}: {nf}");
                    }
                }
            }
        }
    });
}

/// An integer as a value, however big.
fn big_int(g: &Globals, i: &BigInt) -> Value {
    if i.sign() == Sign::Minus {
        neg_succ(g, native::nat_value((-i - 1u32).to_biguint().unwrap()))
    } else {
        of_nat(g, native::nat_value(i.to_biguint().unwrap()))
    }
}

fn as_big_int(g: &Globals, v: &Value) -> Option<BigInt> {
    match value::force(g, v.clone()).ok()? {
        Value::Ctor(d, c, fields) if d == int_data(g) => {
            let n = BigInt::from(as_nat(g, &fields[0]).ok()??);
            Some(if c == 0 { n } else { -n - 1 })
        }
        _ => None,
    }
}

/// R2 test 5: values around `±2^64`, `±2^128`, `±2^256` and seeded random
/// large ones, natives on, against `num_bigint`. Euclidean and flooring
/// division are computed here from `BigInt`'s truncating division
/// (Leijen's formulas), independently of the prelude.
#[test]
fn big_values_agree_with_an_independent_implementation() {
    let mut session = Session::eager();
    let g = &mut session.elab.globals;
    let mut values: Vec<BigInt> = Vec::new();
    for e in [64u32, 128, 256] {
        let p = BigInt::from(2u32).pow(e);
        for k in [-1i32, 0, 1] {
            values.push(&p + k);
            values.push(-(&p + k));
        }
    }
    // A small linear congruential generator, so failures are reproducible.
    let mut state: u64 = 0x1e2d_3c4b_5a69_7887;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        state >> 16
    };
    for _ in 0..12 {
        let digits: Vec<u32> = (0..1 + next() % 8).map(|_| next() as u32).collect();
        let sign = if next() % 2 == 0 {
            Sign::Plus
        } else {
            Sign::Minus
        };
        values.push(BigInt::from_slice(sign, &digits));
    }
    values.extend([-7, -1, 1, 7].map(BigInt::from));
    values.retain(|v| !v.is_zero());
    let names = [
        "Int.add", "Int.sub", "Int.mul", "Int.div", "Int.mod", "Int.tdiv", "Int.tmod", "Int.fdiv",
        "Int.fmod",
    ];
    let ops: Vec<(&str, DefId)> = names.iter().map(|op| (*op, def(g, op))).collect();
    let dec_eq = def(g, "Int.decEq");
    let (_, yes) = g.registry.ctor(Builtin::Yes).unwrap();
    // The largest normal form of a decision seen so far, not counting the
    // digits of the numbers in it: for `Yes`, and for `No` by the signs.
    let mut sizes = [None::<usize>; 5];
    for a in &values {
        for d in &values {
            // Truncating, then Leijen's corrections.
            let (tq, tr) = (a / d, a % d);
            let (fq, fr) = if !tr.is_zero() && tr.sign() != d.sign() {
                (&tq - 1, &tr + d)
            } else {
                (tq.clone(), tr.clone())
            };
            let (eq, er) = match (tr.sign(), d.sign()) {
                (Sign::Minus, Sign::Plus) => (&tq - 1, &tr + d),
                (Sign::Minus, _) => (&tq + 1, &tr - d),
                _ => (tq.clone(), tr.clone()),
            };
            for (op, id) in &ops {
                let want = match *op {
                    "Int.add" => a + d,
                    "Int.sub" => a - d,
                    "Int.mul" => a * d,
                    "Int.div" => eq.clone(),
                    "Int.mod" => er.clone(),
                    "Int.tdiv" => tq.clone(),
                    "Int.tmod" => tr.clone(),
                    "Int.fdiv" => fq.clone(),
                    _ => fr.clone(),
                };
                let mut args = vec![ex(big_int(g, a)), ex(big_int(g, d))];
                if op.ends_with("div") || op.ends_with("mod") {
                    args.push(proof(0));
                }
                let (v, nf) = machine(g, *id, &args, 1);
                assert_eq!(as_big_int(g, &v), Some(want), "{op} {a} {d}: {nf}");
            }
            let (v, nf) = machine(g, dec_eq, &[ex(big_int(g, a)), ex(big_int(g, d))], 0);
            let Value::Ctor(_, c, _) = v else {
                panic!("Int.decEq {a} {d}: {nf}")
            };
            assert_eq!(c == yes, a == d, "Int.decEq {a} {d}: {nf}");
            let size = nf.chars().filter(|c| !c.is_ascii_digit()).count();
            let negative = |i: &BigInt| usize::from(i.sign() == Sign::Minus);
            let shape = if c == yes {
                0
            } else {
                1 + 2 * negative(a) + negative(d)
            };
            let seen = &mut sizes[shape];
            match seen {
                None => *seen = Some(size),
                Some(first) => assert!(size <= *first + 64, "Int.decEq {a} {d} grows: {nf}"),
            }
        }
    }
}
