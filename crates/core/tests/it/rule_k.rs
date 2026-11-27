//! Rule K (docs/core.md, "The equality rule"): a cast into data whose ends
//! are equal is its base. The ends are compared while evaluating, where no
//! context counts the variables in scope, so the comparison's fresh
//! variables come from a range no context reaches
//! (docs/proposals/full-proof-irrelevance-audit.md, finding A).

use crate::common::*;
use std::rc::Rc;
use stitchwort_core::Value;
use stitchwort_core::value::{
    Ends, LEVEL_CAP, RESERVED_LEVELS, check_levels, conv, ends_meet, eval,
};
use stitchwort_core::{ProofMark, Term};

/// With six variables in scope, `z => z` and `z => v5` differ. Compared at
/// level 5, the fresh variable for `z` would be `v5` itself and the two
/// would look equal; rule K's test must not be fooled.
#[test]
fn the_ends_test_makes_its_own_fresh_variables() {
    let p = Prelude::new();
    let g = p.g.ev();
    let env: Vec<Value> = (0..6).map(Value::var).collect();
    let nat = eval(&g, &[], &p.nat_ty()).unwrap();
    let identity = eval(&g, &env, &lam("z", v(0))).unwrap();
    let constant = eval(&g, &env, &lam("z", v(1))).unwrap();
    assert!(
        conv(&g, 5, &identity, &constant).unwrap(),
        "at too low a level, the fresh variable is `v5`"
    );
    let ends = Ends {
        ty: nat.clone(),
        x: identity.clone(),
        y: constant,
    };
    assert!(!ends_meet(&g, &ends).unwrap());
    let same = Ends {
        ty: nat.clone(),
        x: identity.clone(),
        y: identity,
    };
    assert!(ends_meet(&g, &same).unwrap());
}

/// `J (z q => Nat) 0 (h: (z => z) = (z => w))` under `w`, with the proof
/// `h` outside it, and `w => 0` beside it, evaluated with `h` as `v0`.
fn cast_under_w(p: &Prelude) -> (Value, Value) {
    let g = p.g.ev();
    let nat = p.nat_ty();
    let ends = eq(
        Some(arrow(nat.clone(), nat.clone())),
        lam("z", v(0)),
        lam("z", v(1)),
    );
    let cast = Term::J(
        Rc::new(lam("z", lam("q", nat))),
        Rc::new(p.num(0)),
        Rc::new(Term::Ann(Rc::new(v(1)), Rc::new(ends))),
        ProofMark::Unknown,
    );
    let env = [Value::var(0)];
    let casting = eval(&g, &env, &lam("w", cast)).unwrap();
    let zero = eval(&g, &env, &lam("w", p.num(0))).unwrap();
    (casting, zero)
}

/// A comparison 2^24 binders deep (where SW-4679's fixed ranges put the
/// next test's first level) still tells `w => cast` from `w => 0`: the
/// cast's test starts above `w`, so its ends `z => z` and `z => w` differ
/// and the cast is stuck. Under fixed ranges the test's `z` was `w` itself
/// and the two looked equal. The levels reached are given back after.
#[test]
fn a_test_deep_in_a_comparison_starts_above_it() {
    let p = Prelude::new();
    let g = p.g.ev();
    check_levels::set(true);
    let (casting, zero) = cast_under_w(&p);
    let deep = RESERVED_LEVELS + (1 << 24);
    assert!(!conv(&g, deep, &casting, &zero).unwrap());
    assert!(!conv(&g, deep - 1, &casting, &zero).unwrap());
    assert_eq!(g.machine.reached.get(), 0, "given back on return");
    assert!(
        g.machine.cast_answers.borrow().is_none(),
        "the answers go when the outermost test ends"
    );
}

/// A test that would make a fresh variable past [`LEVEL_CAP`] (on a 32-bit
/// target, after 2^31 levels of tests and binders) has no answer: an
/// error, not "not equal", with the levels reached and the answers left as
/// they were. Tests work again after.
#[test]
fn a_test_out_of_levels_has_no_answer() {
    let p = Prelude::new();
    let g = p.g.ev();
    check_levels::set(true);
    let nat = eval(&g, &[], &p.nat_ty()).unwrap();
    let env = [Value::var(0)];
    let identity = eval(&g, &env, &lam("z", v(0))).unwrap();
    let constant = eval(&g, &env, &lam("z", v(1))).unwrap();
    // Not the same closure, so comparing them goes under the binder.
    let expanded = eval(&g, &env, &lam("z", app(lam("u", v(0)), [v(0)]))).unwrap();
    let different = Ends {
        ty: nat.clone(),
        x: identity.clone(),
        y: constant,
    };
    let same = Ends {
        ty: nat,
        x: identity,
        y: expanded,
    };
    g.machine.reached.set(LEVEL_CAP);
    assert!(ends_meet(&g, &same).is_err(), "even equal ends");
    assert_eq!(g.machine.reached.get(), LEVEL_CAP, "given back on error");
    assert!(g.machine.cast_answers.borrow().is_none());
    g.machine.budget.reset();
    g.machine.reached.set(0);
    assert!(!ends_meet(&g, &different).unwrap());
    assert!(ends_meet(&g, &same).unwrap());
    assert_eq!(g.machine.reached.get(), 0);
}

/// Nested tests share one space of levels, each starting where the ones
/// around it have reached: here 150 casts, each tested inside the test of
/// the one before, in the 2^31 levels a 32-bit target has (where SW-4679's
/// fixed ranges held 128), are all answered, and all fire.
#[test]
fn many_nested_tests_fit_a_32_bit_space() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let fun = arrow(nat.clone(), nat.clone());
    let claim = eq(Some(nat.clone()), p.num(0), p.num(1));
    let ax = declare(&mut p.g, "ax", claim);
    let motive = Rc::new(lam("z", lam("q", nat.clone())));
    let proof = Rc::new(Term::Def(ax));
    // Each cast is `let k := (z => c); J (z q => Nat) 0 (ax: k = (u => k u))`
    // for the cast before, `c`: its ends are equal but not the same
    // closure, so its test applies both, and so tests `c` (twice; the
    // second is remembered).
    let mut cast = p.num(0);
    for _ in 0..150 {
        let ends = eq(Some(fun.clone()), v(0), lam("u", app(v(1), [v(0)])));
        let body = Term::J(
            motive.clone(),
            Rc::new(p.num(0)),
            Rc::new(Term::Ann(proof.clone(), Rc::new(ends))),
            ProofMark::Unknown,
        );
        cast = Term::let_("k".into(), fun.clone(), lam("z", cast), body);
    }
    let g = p.g.ev();
    check_levels::set(true);
    let base = LEVEL_CAP - (1 << 31);
    g.machine.reached.set(base);
    let value = eval(&g, &[], &cast).unwrap();
    let zero = eval(&g, &[], &p.num(0)).unwrap();
    assert!(conv(&g, base, &value, &zero).unwrap());
    assert_eq!(g.machine.reached.get(), base);
}
