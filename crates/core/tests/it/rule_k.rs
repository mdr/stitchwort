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
use stitchwort_core::{DefId, ProofMark, Term, check};

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

// The invariant's points 2 and 3, and each site that makes a fresh variable
// (docs/core.md, "The comparisons inside evaluation"). Each test builds a
// cast `J (z q => Nat) 0 (ax: (z => z) = (z => w))` whose `w` is the very
// variable the site makes (or, for points 2 and 3, one the comparison was
// promised may be free), and compares it with `0`. The cast must stay
// stuck: if the site's variable weren't counted in `Machine::reached`
// before the cast was evaluated, the cast's test would start at `w` itself,
// its `z` would be `w`, and the cast would fire on unequal ends (or
// `check_levels` panics).

/// The cast above; `w` is written under the binder `z`.
fn cast_ending_at(p: &Prelude, ax: DefId, w: Term) -> Term {
    let nat = p.nat_ty();
    let ends = eq(
        Some(arrow(nat.clone(), nat.clone())),
        lam("z", v(0)),
        lam("z", w),
    );
    Term::J(
        Rc::new(lam("z", lam("q", nat))),
        Rc::new(p.num(0)),
        Rc::new(Term::Ann(Rc::new(Term::Def(ax)), Rc::new(ends))),
        ProofMark::Unknown,
    )
}

/// A prelude and an axiom to cast with (its body is `0`: the cast names its
/// own ends and never reads its proof).
fn with_axiom() -> (Prelude, DefId) {
    let mut p = Prelude::new();
    let claim = eq(Some(p.nat_ty()), p.num(0), p.num(1));
    let ax = declare(&mut p.g, "ax", claim);
    let body = p.num(0);
    admit(&mut p, vec![(ax, body)]);
    (p, ax)
}

/// Admits each of `members` as a group of its own (a group of several is
/// recursive, which the case-tree comparison skips), trusted, since the
/// casts' terms aren't elaborated.
fn admit(p: &mut Prelude, members: Vec<(DefId, Term)>) {
    for member in members {
        check::admit_trusted_group(&mut p.g, &[member]).expect("admitted");
    }
}

/// Rule K's test is where the comparison's variables are, whatever the
/// outer level: `conv` at `RESERVED_LEVELS` of a value with `w` at the
/// reserved level and a lazily evaluated cast on it.
#[test]
fn point_3_conv_raises_the_maximum_to_its_own_level() {
    let (mut p, ax) = with_axiom();
    let nat = p.nat_ty();
    let cast = lam("w", cast_ending_at(&p, ax, v(1)));
    let castw = declare(&mut p.g, "castw", arrow(nat.clone(), nat));
    admit(&mut p, vec![(castw, cast)]);
    let g = p.g.ev();
    check_levels::set(true);
    // `castw w`, kept as a call, with `w` free at the reserved level; the
    // cast is evaluated only when conv looks inside, with nothing yet
    // recording `w`.
    g.machine.glue.set(true);
    let w = Value::var(RESERVED_LEVELS);
    let call = eval(&g, &[w], &app(Term::Def(castw), [v(0)])).unwrap();
    g.machine.glue.set(false);
    assert!(matches!(call, Value::Call(..)));
    let zero = eval(&g, &[], &p.num(0)).unwrap();
    assert_eq!(g.machine.reached.get(), 0);
    assert!(!conv(&g, RESERVED_LEVELS + 1, &call, &zero).unwrap());
    assert_eq!(g.machine.reached.get(), 0, "given back on return");
}

/// While a comparison is running, a site's fresh variable raises the maximum
/// but never lowers it: here the outer comparison has reached
/// `RESERVED_LEVELS + 1000`, a variable of it is live at `RESERVED_LEVELS +
/// 2`, and a comparison at level `RESERVED_LEVELS + 1` under it makes its own
/// variable `RESERVED_LEVELS + 1`, `+ 2` being past that.
#[test]
fn point_2_a_fresh_variable_never_lowers_the_maximum() {
    let (p, ax) = with_axiom();
    let g = p.g.ev();
    check_levels::set(true);
    let live = Value::var(RESERVED_LEVELS + 2);
    // `u => cast with ends z => z, z => live`, against `u => 0`.
    let casting = eval(&g, &[live], &lam("u", cast_ending_at(&p, ax, v(2)))).unwrap();
    let zero = eval(&g, &[], &lam("u", p.num(0))).unwrap();
    g.machine.reached.set(RESERVED_LEVELS + 1000);
    assert!(!conv(&g, RESERVED_LEVELS + 1, &casting, &zero).unwrap());
    assert_eq!(g.machine.reached.get(), RESERVED_LEVELS + 1000);
}

/// The site's variable is `w`: `lam w. cast` against `lam w. 0`.
#[test]
fn site_lambdas_count_their_variable_before_applying() {
    let (p, ax) = with_axiom();
    let g = p.g.ev();
    check_levels::set(true);
    let casting = eval(&g, &[], &lam("w", cast_ending_at(&p, ax, v(1)))).unwrap();
    let zero = eval(&g, &[], &lam("w", p.num(0))).unwrap();
    assert!(!conv(&g, RESERVED_LEVELS, &casting, &zero).unwrap());
}

/// A function type's codomains: `(w: Nat) -> cast` against `(w: Nat) -> 0`.
#[test]
fn site_codomains_count_their_variable_before_applying() {
    let (p, ax) = with_axiom();
    let g = p.g.ev();
    check_levels::set(true);
    let casting = eval(&g, &[], &pi("w", p.nat_ty(), cast_ending_at(&p, ax, v(1)))).unwrap();
    let zero = eval(&g, &[], &pi("w", p.nat_ty(), p.num(0))).unwrap();
    assert!(!conv(&g, RESERVED_LEVELS, &casting, &zero).unwrap());
}

/// `k0 = w => 0` and `kcast = w => cast on w`, as definitions: a bare name
/// is a partly applied definition, not a lambda.
fn constants(p: &mut Prelude, ax: DefId) -> (DefId, DefId) {
    let nat = p.nat_ty();
    let k0 = declare(&mut p.g, "k0", arrow(nat.clone(), nat.clone()));
    let kcast = declare(&mut p.g, "kcast", arrow(nat.clone(), nat));
    let cast = cast_ending_at(p, ax, v(1));
    let zero = lam("w", p.num(0));
    admit(p, vec![(k0, zero), (kcast, lam("w", cast))]);
    (k0, kcast)
}

/// Eta, a lambda against a partly applied definition (`k0`).
#[test]
fn site_lambda_eta_counts_its_variable_before_applying() {
    let (mut p, ax) = with_axiom();
    let (k0, _) = constants(&mut p, ax);
    let g = p.g.ev();
    check_levels::set(true);
    let casting = eval(&g, &[], &lam("w", cast_ending_at(&p, ax, v(1)))).unwrap();
    let constant = eval(&g, &[], &Term::Def(k0)).unwrap();
    assert!(!matches!(constant, Value::Lam(..)), "{constant:?}");
    assert!(!conv(&g, RESERVED_LEVELS, &casting, &constant).unwrap());
    assert!(!conv(&g, RESERVED_LEVELS, &constant, &casting).unwrap());
}

/// Eta for definitions, two partly applied definitions (`push_eta`).
#[test]
fn site_definition_eta_counts_its_variable_before_applying() {
    let (mut p, ax) = with_axiom();
    let (k0, kcast) = constants(&mut p, ax);
    let g = p.g.ev();
    check_levels::set(true);
    let constant = eval(&g, &[], &Term::Def(k0)).unwrap();
    let casting = eval(&g, &[], &Term::Def(kcast)).unwrap();
    assert!(!conv(&g, RESERVED_LEVELS, &casting, &constant).unwrap());
}

/// A `case` branch's fields, shared by the two definitions' trees: `f n =
/// case n of 0 => 0; m + 1 => cast on m` against `g n = case n of 0 => 0; m
/// + 1 => 0`, stuck on a variable.
#[test]
fn site_case_fields_count_their_variables_before_the_leaves() {
    let (mut p, ax) = with_axiom();
    let nat = p.nat;
    let nat_ty = p.nat_ty();
    let tree = |p: &Prelude, succ: Term| {
        lam(
            "n",
            case(0, nat, vec![(vec![], p.num(0)), (vec!["m"], succ)]),
        )
    };
    let f = declare(&mut p.g, "f", arrow(nat_ty.clone(), nat_ty.clone()));
    let h = declare(&mut p.g, "h", arrow(nat_ty.clone(), nat_ty));
    let cast = cast_ending_at(&p, ax, v(1));
    let (tf, th) = (tree(&p, cast), tree(&p, p.num(0)));
    admit(&mut p, vec![(f, tf), (h, th)]);
    let g = p.g.ev();
    check_levels::set(true);
    let n = Value::var(0);
    let call = |id: DefId| eval(&g, std::slice::from_ref(&n), &app(Term::Def(id), [v(0)])).unwrap();
    let (a, b) = (call(f), call(h));
    assert!(matches!(a, Value::Neutral(..)), "{a:?}");
    assert!(!conv(&g, RESERVED_LEVELS, &a, &b).unwrap());
}
