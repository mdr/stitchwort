//! Native implementations against the definitions they replace
//! (`stitchwort_core::native`). The natives are trusted, so these tests are
//! what stands between a bug in one and the kernel accepting `2 + 2 = 5`.

use stitchwort_core::check::{declare_def, define_def};
use stitchwort_core::native::{self, Native};
use stitchwort_core::value::{apply, conv, eval, force, quote};
use stitchwort_core::{BigUint, DefId, Globals, Term, Value};
use stitchwort_driver::driver::Session;
use stitchwort_elab::{Elaborator, prelude};
use stitchwort_syntax::{SourceMap, parse_module};

fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .position(|d| &*d.name == name)
            .unwrap_or_else(|| panic!("no `{name}` in the prelude")),
    )
}

fn nat(n: u64) -> Value {
    native::nat_value(BigUint::from(n))
}

fn call(g: &Globals, id: DefId, args: &[Value]) -> Value {
    let mut f = eval(g, &[], &Term::Def(id)).unwrap();
    for arg in args {
        f = apply(g, f, arg.clone()).unwrap();
    }
    force(g, f).unwrap()
}

/// Runs `op` with natives on, and its definition with every native off, on
/// numbers `args`, and checks the whole results are the same.
fn compare(g: &mut Globals, op: Native, args: &[Value]) {
    let id = def(g, op.name());
    assert_eq!(
        g.builtins.native(id),
        Some(op),
        "`{}` isn't native",
        op.name()
    );
    let args = with_proof(op, args);
    let fast = call(g, id, &args);
    g.builtins.disable_natives = true;
    let slow = call(g, id, &args);
    g.builtins.disable_natives = false;
    same_result(g, &format!("{}{args:?}", op.name()), &fast, &slow);
}

/// `op`'s arguments: the numbers `nums`, and for `eqNatSound` its proof,
/// `rfl` when the numbers are equal and otherwise a variable (level 0), as
/// there's no closed proof then.
fn with_proof(op: Native, nums: &[Value]) -> Vec<Value> {
    let mut args = nums.to_vec();
    if op == Native::EqNatSound {
        let equal = match nums {
            [Value::Nat(m), Value::Nat(n)] => m == n,
            _ => panic!("`Nat.equalSound` takes two numbers"),
        };
        args.push(if equal { Value::Refl } else { Value::var(0) });
    }
    args
}

/// Checks that a native's whole result is definitionally the definition's,
/// proofs included, not just the same answer. One variable is in scope.
fn same_result(g: &Globals, what: &str, fast: &Value, slow: &Value) {
    let shown = |v: &Value| match quote(g, 1, v) {
        Ok(term) => format!("{term:?}"),
        Err(e) => format!("{v:?} ({e:?})"),
    };
    assert!(
        conv(g, 1, fast, slow).unwrap(),
        "{what}: native {}, definition {}",
        shown(fast),
        shown(slow)
    );
}

#[test]
fn natives_agree_with_their_definitions_on_small_numbers() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    for op in Native::ALL {
        match op.numbers() {
            1 => (0..=40).for_each(|n| compare(g, op, &[nat(n)])),
            2 => {
                for m in 0..=24 {
                    for n in 0..=24 {
                        compare(g, op, &[nat(m), nat(n)]);
                    }
                }
            }
            3 => {
                for a in 0..=12 {
                    for b in 0..=12 {
                        for c in 0..=12 {
                            compare(g, op, &[nat(a), nat(b), nat(c)]);
                        }
                    }
                }
            }
            n => panic!("no inputs for arity {n}"),
        }
    }
}

/// Runs `f` with room for the definitions' unary recursion.
fn with_big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn natives_agree_with_their_definitions_on_random_numbers() {
    with_big_stack(random_numbers);
}

fn random_numbers() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    // A small linear congruential generator, so failures are reproducible.
    let mut state: u64 = 0x5717_c4b0_e7a1_1234;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % bound
    };
    // The definitions count in unary, so inputs stay small enough for the stack.
    for _ in 0..300 {
        for op in Native::ALL {
            let bound = if op == Native::Mul { 30 } else { 100 };
            let args: Vec<Value> = (0..op.numbers()).map(|_| nat(next(bound))).collect();
            compare(g, op, &args);
        }
    }
}

#[test]
fn natives_accept_succ_around_a_number() {
    let session = Session::new();
    let g = &session.elab.globals;
    let nat_data = g.builtins.nat.unwrap();
    // `Succ 4`, built without the evaluator's compaction.
    let succ_4 = Value::Ctor(nat_data, 1, vec![nat(4)].into());
    let zero = Value::Ctor(nat_data, 0, Vec::new().into());
    assert_eq!(
        native::as_nat(g, &call(g, def(g, "Nat.add"), &[succ_4, zero])).unwrap(),
        Some(BigUint::from(5u32))
    );
}

#[test]
fn natives_wait_for_numbers() {
    let session = Session::new();
    let g = &session.elab.globals;
    // `add x 3` with `x` unknown stays as it is, as the definition would.
    let stuck = call(g, def(g, "Nat.add"), &[Value::var(0), nat(3)]);
    assert!(matches!(stuck, Value::Neutral(..)), "{stuck:?}");
}

#[test]
fn big_numbers_compute_without_counting() {
    let session = Session::new();
    let g = &session.elab.globals;
    let big = |s: &str| native::nat_value(s.parse::<BigUint>().unwrap());
    let product = call(
        g,
        def(g, "Nat.mul"),
        &[
            big("123456789012345678901234567890"),
            big("987654321098765432109876543210"),
        ],
    );
    assert!(
        conv(
            g,
            0,
            &product,
            &big("121932631137021795226185032733622923332237463801111263526900")
        )
        .unwrap()
    );
    // Matching on a big number takes the `Succ` branch: `pred` subtracts one.
    let pred = call(g, def(g, "Nat.pred"), &[big("1000000000000000000000")]);
    assert!(conv(g, 0, &pred, &big("999999999999999999999")).unwrap());
}

#[test]
fn a_number_is_its_succ_chain() {
    let session = Session::new();
    let g = &session.elab.globals;
    let d = g.builtins.nat.unwrap();
    let three = Value::Ctor(
        d,
        1,
        vec![Value::Ctor(
            d,
            1,
            vec![Value::Ctor(
                d,
                1,
                vec![Value::Ctor(d, 0, vec![].into())].into(),
            )]
            .into(),
        )]
        .into(),
    );
    assert!(conv(g, 0, &nat(3), &three).unwrap());
    assert!(conv(g, 0, &three, &nat(3)).unwrap());
    assert!(!conv(g, 0, &nat(2), &three).unwrap());
    assert!(!conv(g, 0, &nat(4), &three).unwrap());
    assert!(!conv(g, 0, &nat(0), &Value::Ctor(d, 1, vec![nat(0)].into())).unwrap());
    // `Succ x` is not any particular number.
    assert!(
        !conv(
            g,
            0,
            &nat(1),
            &Value::Ctor(d, 1, vec![Value::var(0)].into())
        )
        .unwrap()
    );
}

/// Elaborates `source` as if it were the prelude, returning the error codes.
fn as_prelude(source: &str) -> Vec<&'static str> {
    let mut sources = SourceMap::new();
    let file = sources.add("<prelude>", source);
    let module = parse_module(file, source).expect("parses");
    let mut elab = Elaborator::new();
    elab.loading_prelude = true;
    elab.elaborate_module(&module)
        .into_iter()
        .map(|d| d.code)
        .collect()
}

#[test]
fn the_real_prelude_registers_every_native() {
    assert_eq!(as_prelude(prelude()), Vec::<&str>::new());
    let session = Session::new();
    let g = &session.elab.globals;
    for op in Native::ALL {
        assert_eq!(g.builtins.native(def(g, op.name())), Some(op));
    }
}

#[test]
fn builtins_with_the_wrong_shape_are_refused() {
    // An extra constructor would make native matching wrong.
    assert_eq!(
        as_prelude("type Nat : Type =\n  | Zero\n  | Succ (n : Nat)\n  | Extra\n"),
        ["E-BUILTIN"]
    );
    // Constructors in the other order.
    assert_eq!(
        as_prelude("type Nat : Type =\n  | Succ (n : Nat)\n  | Zero\n"),
        ["E-BUILTIN"]
    );
    let nat = "type Nat : Type =\n  | Zero\n  | Succ (n : Nat)\n";
    // `add` with the wrong type.
    assert_eq!(
        as_prelude(&format!("{nat}\ndef Nat.add (n : Nat) : Nat := n\n")),
        ["E-BUILTIN"]
    );
    // `Bool` with a field.
    assert_eq!(
        as_prelude(&format!(
            "{nat}\ntype Bool : Type =\n  | False\n  | True (n : Nat)\n"
        )),
        ["E-BUILTIN"]
    );
    // `leq` before `Bool` is registered.
    assert_eq!(
        as_prelude(&format!(
            "{nat}\ntype B : Type =\n  | F\n  | T\n\ndef Nat.leq (m : Nat) (n : Nat) : B := T\n"
        )),
        ["E-BUILTIN"]
    );
    // A `Decidable` whose `Yes` doesn't hold a proof.
    assert_eq!(
        as_prelude(
            "type Void : Prop\n\n\
             def Not (p : Prop) : Prop := p -> Void\n\n\
             type Decidable (p : Prop) : Type =\n  \
             | Yes (proof : Not p)\n  \
             | No (refutation : Not p)\n"
        ),
        ["E-BUILTIN"]
    );
    // Outside the prelude, these names mean nothing special.
    let mut session = Session::new();
    assert!(
        session
            .load("user.sw", "def eqNat2 (m : Nat) (n : Nat) : Nat := m\n")
            .is_ok()
    );
}

/// `k + x` for an unknown `x` (variable `level`), or the number `k`.
fn plus_var(k: u64, level: Option<usize>) -> Value {
    native::from_view(BigUint::from(k), level.map(Value::var))
}

#[test]
fn shortcuts_with_unknowns_agree_with_the_definitions() {
    with_big_stack(|| {
        let mut session = Session::new();
        let g = &mut session.elab.globals;
        for op in [Native::Add, Native::Sub, Native::Leq, Native::EqNat] {
            let id = def(g, op.name());
            for k1 in 0..12 {
                for k2 in 0..12 {
                    // `k1 + x` against `k2 + y`, `k2`, and `k2 + x`.
                    for (a, b) in [
                        (plus_var(k1, Some(0)), plus_var(k2, Some(1))),
                        (plus_var(k1, Some(0)), plus_var(k2, None)),
                        (plus_var(k1, None), plus_var(k2, Some(0))),
                        (plus_var(k1, Some(0)), plus_var(k2, Some(0))),
                    ] {
                        let fast = call(g, id, &[a.clone(), b.clone()]);
                        g.builtins.disable_natives = true;
                        let slow = call(g, id, &[a.clone(), b.clone()]);
                        g.builtins.disable_natives = false;
                        assert!(
                            conv(g, 2, &fast, &slow).unwrap(),
                            "{}({a:?}, {b:?}): native {fast:?}, definition {slow:?}",
                            op.name()
                        );
                    }
                }
            }
        }
        // `eqNatRefl (k + x)` is `eqNatRefl x`.
        let id = def(g, Native::EqNatRefl.name());
        for k in 0..12 {
            let n = plus_var(k, Some(0));
            let fast = call(g, id, std::slice::from_ref(&n));
            g.builtins.disable_natives = true;
            let slow = call(g, id, std::slice::from_ref(&n));
            g.builtins.disable_natives = false;
            assert!(
                conv(g, 1, &fast, &slow).unwrap(),
                "Nat.equalRefl({n:?}): native {fast:?}, definition {slow:?}"
            );
        }
    });
}

#[test]
fn a_big_number_plus_an_unknown_stays_compact() {
    let session = Session::new();
    let g = &session.elab.globals;
    let big = native::nat_value(BigUint::from(10u32).pow(30));
    let sum = call(g, def(g, "Nat.add"), &[big, Value::var(0)]);
    assert!(matches!(sum, Value::NatAdd(..)), "{sum:?}");
    // Matching on it takes the `Succ` branch: `pred` takes one off.
    let pred = call(g, def(g, "Nat.pred"), std::slice::from_ref(&sum));
    let expected = native::from_view(BigUint::from(10u32).pow(30) - 1u32, Some(Value::var(0)));
    assert!(conv(g, 1, &pred, &expected).unwrap());
    assert!(!conv(g, 1, &pred, &sum).unwrap());
}

/// Loads `source` after the prelude, panicking with the rendered errors.
fn accepts(source: &str) {
    let mut session = Session::new();
    if let Err(diagnostics) = session.load("natives.sw", source) {
        let rendered: String = diagnostics
            .iter()
            .map(|d| stitchwort_driver::render::render(&session.sources, d, false))
            .collect();
        panic!("rejected:\n{rendered}");
    }
}

/// Copies of the prelude's definitions that return proofs, which never run
/// natively (only the calls inside them to other natives do).
const COPIES: &str = "\
import Std (Bool, Nat, Void)

def myDecEqNat : (m : Nat) -> (n : Nat) -> Decidable (m = n)
  | Zero,   Zero   => Yes rfl
  | Zero,   Succ n => No (Nat.equalFalse 0 (Succ n) rfl)
  | Succ m, Zero   => No (Nat.equalFalse (Succ m) 0 rfl)
  | Succ m, Succ n => Nat.decEqFrom (Succ m) (Succ n) (Nat.equal m n) rfl

theorem myEqNatRefl : (n : Nat) -> Nat.equal n n = True
  | Zero   => rfl
  | Succ n => myEqNatRefl n

theorem myEqNatSound : (m : Nat) -> (n : Nat) -> Nat.equal m n = True -> m = n
  | Zero,   Zero,   h => rfl
  | Zero,   Succ n, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Zero,   h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Succ n, h => Std.Eq.cong Succ (myEqNatSound m n h)
";

const BIG: &str = "1180591620717411303424"; // 2^70

/// `rfl` proves a native's result equal to its definition's, for the natives
/// that return proofs. (`decEqNat 3 5` used to give a different refutation.)
#[test]
fn rfl_proves_proof_natives_equal_to_their_definitions() {
    let mut source = COPIES.to_string();
    let pairs = [
        ("0", "0"),
        ("0", "1"),
        ("1", "0"),
        ("1", "1"),
        ("3", "5"),
        ("5", "3"),
        ("4", "4"),
        ("0", BIG),
        (BIG, "1"),
        (BIG, BIG),
        (BIG, "1180591620717411303425"),
    ];
    for (i, (m, n)) in pairs.iter().enumerate() {
        source +=
            &format!("\ntheorem sameDec{i} : myDecEqNat {m} {n} = Nat.decEq {m} {n} := rfl\n");
    }
    for n in ["0", "1", "7"] {
        source += &format!(
            "\n\
             theorem sameRefl{n} : myEqNatRefl {n} = Nat.equalRefl {n} := rfl\n\n\
             theorem sameSound{n} : myEqNatSound {n} {n} rfl = Nat.equalSound {n} {n} rfl := rfl\n"
        );
    }
    accepts(&source);
}

/// A copy of `op`'s definition, unfolding once to the same body, in which
/// the recursive calls go to the native `op`.
fn unfolded_once(g: &mut Globals, op: Native) -> DefId {
    let id = def(g, op.name());
    let d = g.def(id);
    let (ty, body, span) = (d.ty.clone(), d.body().cloned().unwrap(), d.span);
    let name = format!("{}Once", op.name());
    let copy = declare_def(g, &name.as_str().into(), &ty, d.theorem, false, span).unwrap();
    define_def(g, copy, &body).unwrap();
    copy
}

/// On numbers too big for the definitions to count down, each native's whole
/// result is what one step of its definition gives, with the native for the
/// steps after it. With the comparison on small numbers, that's an induction:
/// the native agrees with its definition everywhere.
#[test]
fn natives_agree_with_one_step_of_their_definitions_on_big_numbers() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let big = |s: &str| native::nat_value(s.parse::<BigUint>().unwrap());
    let b = BIG.parse::<BigUint>().unwrap();
    let numbers = [
        big("0"),
        big("1"),
        native::nat_value(b.clone()),
        native::nat_value(&b + 1u32),
        native::nat_value(&b * 3u32),
        big("340282366920938463463374607431768211457"), // 2^128 + 1
    ];
    for op in Native::ALL {
        let id = def(g, op.name());
        let once = unfolded_once(g, op);
        let mut inputs: Vec<Vec<Value>> = Vec::new();
        match op.numbers() {
            1 => inputs.extend(numbers.iter().map(|n| vec![n.clone()])),
            2 => {
                for m in &numbers {
                    for n in &numbers {
                        inputs.push(vec![m.clone(), n.clone()]);
                    }
                }
            }
            3 => {
                for a in &numbers {
                    for (n, d) in [(&b, 7u32), (&b, 1), (&b, 0)] {
                        inputs.push(vec![a.clone(), native::nat_value(n.clone()), nat(d.into())]);
                    }
                }
            }
            n => panic!("no inputs for {n} numbers"),
        }
        for nums in inputs {
            // `eqNatSound` on different numbers isn't native: the definition
            // counts down both ways.
            if op == Native::EqNatSound && !conv(g, 0, &nums[0], &nums[1]).unwrap() {
                continue;
            }
            let args = with_proof(op, &nums);
            let fast = call(g, id, &args);
            let slow = call(g, once, &args);
            same_result(g, &format!("{}{nums:?}", op.name()), &fast, &slow);
        }
    }
}
