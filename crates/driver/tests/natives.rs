//! Native implementations against the definitions they replace
//! (`stitchwort_core::native`). The natives are trusted, so these tests are
//! what stands between a bug in one and the kernel accepting `2 + 2 = 5`.

use stitchwort_core::native::{self, Native};
use stitchwort_core::value::{apply, conv, eval, force};
use stitchwort_core::{BigUint, DefId, Globals, Term, Value};
use stitchwort_driver::driver::Session;
use stitchwort_elab::{Elaborator, PRELUDE};
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
    let mut f = eval(g, &[], &Term::Def(id));
    for arg in args {
        f = apply(g, f, arg.clone());
    }
    force(g, f)
}

/// Runs `op` both ways on `args`, and checks the results agree.
fn compare(g: &mut Globals, op: Native, args: &[Value]) {
    let id = def(g, op.name());
    assert_eq!(
        g.builtins.native(id),
        Some(op),
        "`{}` isn't native",
        op.name()
    );
    let fast = call(g, id, args);
    g.builtins.disable_natives = true;
    let slow = call(g, id, args);
    g.builtins.disable_natives = false;
    let shown = || {
        format!(
            "{}{args:?}: native {fast:?}, definition {slow:?}",
            op.name()
        )
    };
    match op {
        Native::Add | Native::Sub | Native::Mul | Native::DivFuel => {
            let (a, b) = (native::as_nat(g, &fast), native::as_nat(g, &slow));
            assert!(a.is_some() && a == b, "{}", shown());
        }
        Native::EqNatRefl => {
            assert!(conv(g, 0, &fast, &slow), "{}", shown());
        }
        // Booleans and decisions: the same constructor. For `decEqNat`, a `Yes`
        // holds `rfl` either way; a `No`'s refutation differs (it's a
        // function, built differently) but has the same type.
        Native::Leq | Native::EqNat | Native::DecEqNat => match (&fast, &slow) {
            (Value::Ctor(d1, c1, f1), Value::Ctor(d2, c2, f2)) => {
                assert!(d1 == d2 && c1 == c2, "{}", shown());
                if *c1 == 0 && op == Native::DecEqNat {
                    assert!(conv(g, 0, &f1[0], &f2[0]), "{}", shown());
                }
            }
            _ => panic!("not constructors: {}", shown()),
        },
    }
}

#[test]
fn natives_agree_with_their_definitions_on_small_numbers() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    for op in Native::ALL {
        match op.arity() {
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
            let args: Vec<Value> = (0..op.arity()).map(|_| nat(next(bound))).collect();
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
    let succ_4 = Value::Ctor(nat_data, 1, vec![nat(4)]);
    let zero = Value::Ctor(nat_data, 0, Vec::new());
    assert_eq!(
        native::as_nat(g, &call(g, def(g, "add"), &[succ_4, zero])),
        Some(BigUint::from(5u32))
    );
}

#[test]
fn natives_wait_for_numbers() {
    let session = Session::new();
    let g = &session.elab.globals;
    // `add x 3` with `x` unknown stays as it is, as the definition would.
    let stuck = call(g, def(g, "add"), &[Value::var(0), nat(3)]);
    assert!(matches!(stuck, Value::Neutral(..)), "{stuck:?}");
}

#[test]
fn big_numbers_compute_without_counting() {
    let session = Session::new();
    let g = &session.elab.globals;
    let big = |s: &str| native::nat_value(s.parse::<BigUint>().unwrap());
    let product = call(
        g,
        def(g, "mul"),
        &[
            big("123456789012345678901234567890"),
            big("987654321098765432109876543210"),
        ],
    );
    assert!(conv(
        g,
        0,
        &product,
        &big("121932631137021795226185032733622923332237463801111263526900")
    ));
    // Matching on a big number takes the `Succ` branch: `pred` subtracts one.
    let pred = call(g, def(g, "pred"), &[big("1000000000000000000000")]);
    assert!(conv(g, 0, &pred, &big("999999999999999999999")));
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
            vec![Value::Ctor(d, 1, vec![Value::Ctor(d, 0, vec![])])],
        )],
    );
    assert!(conv(g, 0, &nat(3), &three));
    assert!(conv(g, 0, &three, &nat(3)));
    assert!(!conv(g, 0, &nat(2), &three));
    assert!(!conv(g, 0, &nat(4), &three));
    assert!(!conv(g, 0, &nat(0), &Value::Ctor(d, 1, vec![nat(0)])));
    // `Succ x` is not any particular number.
    assert!(!conv(
        g,
        0,
        &nat(1),
        &Value::Ctor(d, 1, vec![Value::var(0)])
    ));
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
    assert_eq!(as_prelude(PRELUDE), Vec::<&str>::new());
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
        as_prelude(&format!("{nat}\nadd : Nat -> Nat\nadd n = n\n")),
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
            "{nat}\ntype B : Type =\n  | F\n  | T\n\nleq : Nat -> Nat -> B\nleq m n = T\n"
        )),
        ["E-BUILTIN"]
    );
    // A `Decidable` whose `Yes` doesn't hold a proof.
    assert_eq!(
        as_prelude(
            "type Void : Prop\n\nNot : Prop -> Prop\nNot p = p -> Void\n\n\
             type Decidable (p : Prop) : Type =\n  | Yes (proof : Not p)\n  | No (refutation : Not p)\n"
        ),
        ["E-BUILTIN"]
    );
    // Outside the prelude, these names mean nothing special.
    let mut session = Session::new();
    assert!(
        session
            .load("user.sw", "eqNat2 : Nat -> Nat -> Nat\neqNat2 m n = m\n")
            .is_ok()
    );
}
