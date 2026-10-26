//! Opaque definitions in the kernel (docs/proposals/opaque-definitions.md
//! §6.4, §6.6, §6.11; §9 lane 1): an opaque definition has a type and no
//! body while checking a declaration that doesn't unfold it, a declaration's
//! `unfolding` list is closed transitively (with group-mates, D1267), and
//! both are hashed. Must-reject tests, each with its paired accepted
//! example. The terms are built by hand through the core API: the surface
//! syntax (`opaque def`, `unfolding`) comes in lane 2.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, define_group};
use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_core::term::Term;
use stitchwort_core::value::{Head, Value, conv, eval, quote};
use stitchwort_core::{DefId, Globals, Limits, Sort};

/// How a declaration is submitted: opaque or not, and what it unfolds.
#[derive(Clone, Copy, Default)]
struct How<'a> {
    opaque: bool,
    theorem: bool,
    unfolding: &'a [DefId],
}

const PLAIN: How = How {
    opaque: false,
    theorem: false,
    unfolding: &[],
};
const OPAQUE: How = How {
    opaque: true,
    theorem: false,
    unfolding: &[],
};
const THEOREM: How = How {
    opaque: false,
    theorem: true,
    unfolding: &[],
};

/// An opaque theorem that unfolds `unfolding`: a theorem with an
/// `unfolding` clause is itself opaque (§6.4, rule 3), which lane 2's
/// elaborator says by marking it so.
fn unfolding(unfolding: &[DefId]) -> How<'_> {
    How {
        opaque: true,
        theorem: true,
        unfolding,
    }
}

/// Declares and defines `name: ty := body` as `how` says, or the error code.
fn submit(
    g: &mut Globals,
    name: &str,
    how: How,
    ty: Term,
    body: Term,
) -> Result<DefId, &'static str> {
    let id =
        check::declare_def(g, &name.into(), &ty, how.theorem, false, span()).map_err(|d| d.code)?;
    if how.opaque {
        check::mark_opaque(g, id);
    }
    check::set_unfolding(g, id, how.unfolding);
    check::define_def(g, id, &body).map_err(|d| d.code)?;
    Ok(id)
}

fn hash_of(g: &Globals, id: DefId) -> ContentHash {
    let _op = g.budget.operation(Limits::default());
    def_hash(g, id).unwrap().expect("final")
}

/// `Nat -> Nat`.
fn nat_to_nat(p: &Prelude) -> Term {
    arrow(p.nat_ty(), p.nat_ty())
}

/// `a = b` at `Nat`.
fn nat_eq(p: &Prelude, a: Term, b: Term) -> Term {
    eq(Some(p.nat_ty()), a, b)
}

/// `two: Nat := 2`, submitted as `how` says.
fn two(p: &mut Prelude, how: How) -> DefId {
    let (ty, body) = (p.nat_ty(), p.num(2));
    submit(&mut p.g, "two", how, ty, body).expect("two")
}

/// `name (n: Nat): Nat := n + n`.
fn double(p: &mut Prelude, name: &str, how: How) -> DefId {
    let (ty, body) = (nat_to_nat(p), lam("n", p.plus(v(0), v(0))));
    submit(&mut p.g, name, how, ty, body).expect("double")
}

/// `name: f arg = result := rfl`, submitted as `how` says.
fn rfl_about(
    p: &mut Prelude,
    name: &str,
    how: How,
    f: DefId,
    arg: Option<Term>,
    result: Term,
) -> Result<DefId, &'static str> {
    let call = match arg {
        Some(arg) => app(Term::Def(f), [arg]),
        None => Term::Def(f),
    };
    let statement = nat_eq(p, call, result);
    submit(&mut p.g, name, how, statement, Term::Refl)
}

// `rfl`, and `unfolding`

#[test]
fn rfl_through_an_opaque_constant_is_refused() {
    let mut p = Prelude::new();
    let two = self::two(&mut p, OPAQUE);
    let n2 = p.num(2);
    assert_eq!(
        rfl_about(&mut p, "twoIsTwo", THEOREM, two, None, n2.clone()),
        Err("E-REFL")
    );
    // Paired: the same with `unfolding two`.
    assert!(rfl_about(&mut p, "twoIsTwo", unfolding(&[two]), two, None, n2).is_ok());
    // And with `two` transparent, no clause is needed.
    let mut p = Prelude::new();
    let two = self::two(&mut p, PLAIN);
    let n2 = p.num(2);
    assert!(rfl_about(&mut p, "twoIsTwo", THEOREM, two, None, n2).is_ok());
}

#[test]
fn rfl_through_an_opaque_function_is_refused() {
    let mut p = Prelude::new();
    let double = self::double(&mut p, "double", OPAQUE);
    let (two, four) = (p.num(2), p.num(4));
    assert_eq!(
        rfl_about(
            &mut p,
            "d",
            THEOREM,
            double,
            Some(two.clone()),
            four.clone()
        ),
        Err("E-REFL")
    );
    assert!(rfl_about(&mut p, "d", unfolding(&[double]), double, Some(two), four).is_ok());
}

#[test]
fn a_declaration_that_unfolds_stays_opaque_to_others() {
    // `four: Nat := double 2`, unfolding `double`, is itself opaque: a
    // declaration that doesn't unfold it can't see that it's 4 (§6.4, rule 3).
    let mut p = Prelude::new();
    let double = self::double(&mut p, "double", OPAQUE);
    let (ty, body) = (p.nat_ty(), app(Term::Def(double), [p.num(2)]));
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[double],
    };
    let four = submit(&mut p.g, "four", how, ty, body).unwrap();
    let n4 = p.num(4);
    assert_eq!(
        rfl_about(&mut p, "a", THEOREM, four, None, n4.clone()),
        Err("E-REFL")
    );
    // Paired: unfolding `four` brings `double` with it.
    assert!(rfl_about(&mut p, "b", unfolding(&[four]), four, None, n4).is_ok());
}

#[test]
fn unfolding_on_a_transparent_definition_is_refused() {
    let mut p = Prelude::new();
    let double = self::double(&mut p, "double", OPAQUE);
    let (ty, body) = (p.nat_ty(), app(Term::Def(double), [p.num(2)]));
    let transparent = How {
        opaque: false,
        theorem: false,
        unfolding: &[double],
    };
    assert_eq!(
        submit(&mut p.g, "four", transparent, ty.clone(), body.clone()),
        Err("E-UNFOLDING-TRANSPARENT")
    );
    // A theorem must be opaque to unfold too.
    let n4 = p.num(4);
    let theorem = How {
        opaque: false,
        theorem: true,
        unfolding: &[double],
    };
    let two = p.num(2);
    assert_eq!(
        rfl_about(&mut p, "t", theorem, double, Some(two), n4),
        Err("E-UNFOLDING-TRANSPARENT")
    );
    // Paired: the same, opaque.
    let opaque = How {
        opaque: true,
        ..transparent
    };
    assert!(submit(&mut p.g, "four", opaque, ty, body).is_ok());
}

#[test]
fn unfolding_a_transparent_definition_is_refused() {
    let mut p = Prelude::new();
    let double = self::double(&mut p, "double", PLAIN);
    let (two, four) = (p.num(2), p.num(4));
    assert_eq!(
        rfl_about(
            &mut p,
            "d",
            unfolding(&[double]),
            double,
            Some(two.clone()),
            four.clone()
        ),
        Err("E-NOT-OPAQUE")
    );
    // Paired: no clause needed.
    assert!(rfl_about(&mut p, "d", THEOREM, double, Some(two), four).is_ok());
}

#[test]
fn unfolding_names_only_final_declarations() {
    let mut p = Prelude::new();
    // A failed opaque definition: its users fail too.
    let ty = p.nat_ty();
    let bad = check::declare_def(&mut p.g, &"bad".into(), &ty, false, false, span()).unwrap();
    check::mark_opaque(&mut p.g, bad);
    assert!(check::define_def(&mut p.g, bad, &ty).is_err());
    let zero = p.num(0);
    assert_eq!(
        rfl_about(&mut p, "t", unfolding(&[bad]), bad, None, zero.clone()),
        Err("E-FAILED-DEPENDENCY")
    );
    // A pending one, or one that doesn't exist, is malformed.
    let pending =
        check::declare_def(&mut p.g, &"pending".into(), &ty, false, false, span()).unwrap();
    check::mark_opaque(&mut p.g, pending);
    let statement = nat_eq(&p, zero.clone(), zero.clone());
    for named in [pending, DefId(10_000)] {
        assert_eq!(
            submit(
                &mut p.g,
                "t",
                unfolding(&[named]),
                statement.clone(),
                Term::Refl
            ),
            Err("E-MALFORMED")
        );
    }
}

// The type is checked with nothing unfolded

#[test]
fn a_type_that_needs_an_unfolding_is_refused() {
    // `Code: Type := Nat`, opaque; `x: Eq Code 0 0` needs `Code` to be
    // `Nat` for `0: Code`. A type is checked with every opaque definition
    // hidden, whatever the declaration unfolds, and even if the caller has
    // a transparency set in place (lane 2's elaborator will, while it
    // checks a body).
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let code = submit(&mut p.g, "Code", OPAQUE, ty(), nat).unwrap();
    let statement = eq(Some(Term::Def(code)), p.num(0), p.num(0));
    let set: Rc<[DefId]> = Rc::from([code]);
    let _ambient = p.g.transparent.set(set);
    assert_eq!(
        submit(&mut p.g, "x", unfolding(&[code]), statement, Term::Refl),
        Err("E-TYPE-MISMATCH")
    );
    // Paired: the same statement about `Nat`.
    let statement = nat_eq(&p, p.num(0), p.num(0));
    assert!(submit(&mut p.g, "x", unfolding(&[code]), statement, Term::Refl).is_ok());
    // And the caller's set is still in place.
    assert!(p.g.transparent.contains(code));
}

// Transitivity: Danielsson and Geng's counterexample (§5)

/// `Code: Type := Nat` and `start: Code := 0` unfolding `Code`, both opaque.
fn code_and_start(p: &mut Prelude) -> (DefId, DefId) {
    let nat = p.nat_ty();
    let code = submit(&mut p.g, "Code", OPAQUE, ty(), nat).unwrap();
    let zero = p.num(0);
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[code],
    };
    let start = submit(&mut p.g, "start", how, Term::Def(code), zero).unwrap();
    (code, start)
}

#[test]
fn start_needs_code_unfolded() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let code = submit(&mut p.g, "Code", OPAQUE, ty(), nat).unwrap();
    let zero = p.num(0);
    assert_eq!(
        submit(&mut p.g, "start", OPAQUE, Term::Def(code), zero.clone()),
        Err("E-TYPE-MISMATCH")
    );
    // Paired: with `unfolding Code`.
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[code],
    };
    assert!(submit(&mut p.g, "start", how, Term::Def(code), zero).is_ok());
}

#[test]
fn unfolding_start_unfolds_code() {
    // `d: Nat := start`, unfolding only `start`: `start` unfolds to `0`, and
    // it has type `Code`, which must be `Nat` here too, or the body no
    // longer fits its type. Transitivity gives `d` both.
    let mut p = Prelude::new();
    let (code, start) = code_and_start(&mut p);
    let nat = p.nat_ty();
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[start],
    };
    assert!(submit(&mut p.g, "d", how, nat.clone(), Term::Def(start)).is_ok());
    // Without the clause, `start: Code` isn't a `Nat`.
    assert_eq!(
        submit(&mut p.g, "d2", OPAQUE, nat.clone(), Term::Def(start)),
        Err("E-TYPE-MISMATCH")
    );
    // No route gives `start` without `Code`: a transparent declaration that
    // unfolds `start` (which would carry it everywhere) is refused.
    let transparent = How {
        opaque: false,
        theorem: false,
        unfolding: &[start],
    };
    assert_eq!(
        submit(&mut p.g, "d3", transparent, nat, Term::Def(start)),
        Err("E-UNFOLDING-TRANSPARENT")
    );
    // And `start = 0` can't even be stated outside: `0` isn't a `Code`.
    let statement = eq(Some(Term::Def(code)), Term::Def(start), p.num(0));
    assert_eq!(
        submit(&mut p.g, "s", unfolding(&[start]), statement, Term::Refl),
        Err("E-TYPE-MISMATCH")
    );
}

#[test]
fn a_chain_of_unfoldings_is_followed() {
    // c := 3; b := c, unfolding c; a theorem unfolding only b sees c's body.
    let mut p = Prelude::new();
    let (nat, three) = (p.nat_ty(), p.num(3));
    let c = submit(&mut p.g, "c", OPAQUE, nat.clone(), three.clone()).unwrap();
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[c],
    };
    let b = submit(&mut p.g, "b", how, nat, Term::Def(c)).unwrap();
    assert!(rfl_about(&mut p, "a", unfolding(&[b]), b, None, three.clone()).is_ok());
    // Must-reject: unfolding only `c`, `b` stays folded.
    assert_eq!(
        rfl_about(&mut p, "a2", unfolding(&[c]), b, None, three),
        Err("E-REFL")
    );
}

// Conversion: an opaque call is a neutral, compared by its spine

#[test]
fn opaque_calls_compare_by_their_arguments() {
    let mut p = Prelude::new();
    let f = double(&mut p, "f", OPAQUE);
    let g = double(&mut p, "g", OPAQUE);
    let (fv, gv) = (Term::Def(f), Term::Def(g));
    // (n: Nat) -> f n = g n: different heads, although the bodies agree.
    let statement = |p: &Prelude, a: Term, b: Term| pi("n", p.nat_ty(), nat_eq(p, a, b));
    let different = statement(&p, app(fv.clone(), [v(0)]), app(gv.clone(), [v(0)]));
    let proof = lam("n", Term::Refl);
    assert_eq!(
        submit(&mut p.g, "fg", THEOREM, different.clone(), proof.clone()),
        Err("E-REFL")
    );
    assert!(submit(&mut p.g, "fg", unfolding(&[f, g]), different, proof.clone()).is_ok());
    // The same head, with arguments that compute to the same: `0 + n` is `n`.
    let same = statement(
        &p,
        app(fv.clone(), [p.plus(p.num(0), v(0))]),
        app(fv.clone(), [v(0)]),
    );
    assert!(submit(&mut p.g, "ff", THEOREM, same, proof.clone()).is_ok());
    // But not with arguments that differ (`n + 0` doesn't compute).
    let differ = statement(
        &p,
        app(fv.clone(), [p.plus(v(0), p.num(0))]),
        app(fv.clone(), [v(0)]),
    );
    assert_eq!(
        submit(&mut p.g, "ff2", THEOREM, differ, proof.clone()),
        Err("E-REFL")
    );
    // An opaque call against a constructor: `f 0` and `0`.
    let ctor = nat_eq(&p, app(fv, [p.num(0)]), p.num(0));
    assert_eq!(
        submit(&mut p.g, "f0", THEOREM, ctor.clone(), Term::Refl),
        Err("E-REFL")
    );
    assert!(submit(&mut p.g, "f0", unfolding(&[f]), ctor, Term::Refl).is_ok());
}

#[test]
fn opaque_calls_with_different_proofs_differ() {
    // h (n: Nat) (proof: n = n): Nat := n, which ignores its proof. With `h`
    // opaque, `h 0 p` and `h 0 q` for two proofs `p`, `q` aren't convertible:
    // there's no definitional proof irrelevance (§6.4).
    let mut p = Prelude::new();
    let ty = pi("n", p.nat_ty(), arrow(nat_eq(&p, v(0), v(0)), p.nat_ty()));
    let body = lam("n", lam("proof", v(1)));
    let opaque_h = submit(&mut p.g, "h", OPAQUE, ty.clone(), body.clone()).unwrap();
    let plain_h = submit(&mut p.g, "h2", PLAIN, ty, body).unwrap();
    let zero_eq = nat_eq(&p, p.num(0), p.num(0));
    let statement = |h: DefId| {
        pi(
            "p",
            zero_eq.clone(),
            pi(
                "q",
                zero_eq.clone(),
                nat_eq(
                    &p,
                    app(Term::Def(h), [p.num(0), v(1)]),
                    app(Term::Def(h), [p.num(0), v(0)]),
                ),
            ),
        )
    };
    let proof = lam("p", lam("q", Term::Refl));
    let (opaque_statement, plain_statement) = (statement(opaque_h), statement(plain_h));
    assert_eq!(
        submit(&mut p.g, "irr", THEOREM, opaque_statement, proof.clone()),
        Err("E-REFL")
    );
    // Paired: transparent, the body ignores the proof.
    assert!(submit(&mut p.g, "irr", THEOREM, plain_statement, proof).is_ok());
}

#[test]
fn an_opaque_dictionary_isnt_compared_unfolded() {
    // A dictionary stays folded by name, and is compared unfolded when its
    // name can't settle a comparison. Opaque, it never is.
    let mut p = Prelude::new();
    let (nat, two) = (p.nat_ty(), p.num(2));
    let folded = |p: &mut Prelude, name: &str, opaque: bool| {
        let id = check::declare_def(&mut p.g, &name.into(), &nat, false, false, span()).unwrap();
        check::mark_folded(&mut p.g, id);
        if opaque {
            check::mark_opaque(&mut p.g, id);
        }
        check::define_def(&mut p.g, id, &two).unwrap();
        id
    };
    let opaque = folded(&mut p, "opaqueDict", true);
    let plain = folded(&mut p, "plainDict", false);
    let two = p.num(2);
    assert_eq!(
        rfl_about(&mut p, "a", THEOREM, opaque, None, two.clone()),
        Err("E-REFL")
    );
    assert!(rfl_about(&mut p, "b", THEOREM, plain, None, two.clone()).is_ok());
    assert!(rfl_about(&mut p, "c", unfolding(&[opaque]), opaque, None, two).is_ok());
}

#[test]
fn an_opaque_case_tree_isnt_compared_by_its_tree() {
    // Two definitions with the same case tree, stuck on a variable, are
    // equal by their trees (`same_stuck_trees`). Not when one is opaque.
    let mut p = Prelude::new();
    let is_zero_body = lam(
        "n",
        case(0, p.nat, vec![(vec![], p.num(1)), (vec!["k"], p.num(0))]),
    );
    let ty = nat_to_nat(&p);
    let plain = submit(&mut p.g, "isZero", PLAIN, ty.clone(), is_zero_body.clone()).unwrap();
    let plain2 = submit(&mut p.g, "isZero2", PLAIN, ty.clone(), is_zero_body.clone()).unwrap();
    let opaque = submit(&mut p.g, "isZero3", OPAQUE, ty, is_zero_body).unwrap();
    let statement = |p: &Prelude, a: DefId, b: DefId| {
        pi(
            "n",
            p.nat_ty(),
            nat_eq(p, app(Term::Def(a), [v(0)]), app(Term::Def(b), [v(0)])),
        )
    };
    let proof = lam("n", Term::Refl);
    let plains = statement(&p, plain, plain2);
    assert!(submit(&mut p.g, "a", THEOREM, plains, proof.clone()).is_ok());
    let mixed = statement(&p, plain, opaque);
    assert_eq!(
        submit(&mut p.g, "b", THEOREM, mixed.clone(), proof.clone()),
        Err("E-REFL")
    );
    assert!(submit(&mut p.g, "c", unfolding(&[opaque]), mixed, proof).is_ok());
}

#[test]
fn conversion_treats_an_opaque_call_as_neutral() {
    // Directly: evaluating `f 2` gives the stuck call, which isn't `4`.
    let mut p = Prelude::new();
    let f = double(&mut p, "f", OPAQUE);
    let call = app(Term::Def(f), [p.num(2)]);
    let _op = p.g.budget.operation(Limits::default());
    let value = eval(&p.g, &[], &call).unwrap();
    assert!(matches!(&value, Value::Neutral(Head::Def(id), spine) if *id == f && spine.len() == 1));
    let four = eval(&p.g, &[], &p.num(4)).unwrap();
    assert!(!conv(&p.g, 0, &value, &four).unwrap());
    // In the transparency set, it computes.
    let set: Rc<[DefId]> = Rc::from([f]);
    let in_set = p.g.transparent.set(set);
    let value = eval(&p.g, &[], &call).unwrap();
    assert!(conv(&p.g, 0, &value, &four).unwrap());
    drop(in_set);
    assert!(matches!(
        eval(&p.g, &[], &call).unwrap(),
        Value::Neutral(..)
    ));
}

// Running ignores opacity (§6.4, rule 5)

#[test]
fn a_running_program_unfolds_opaque_definitions() {
    let mut p = Prelude::new();
    let f = double(&mut p, "f", OPAQUE);
    let two = self::two(&mut p, OPAQUE);
    let _op = p.g.budget.operation(Limits::default());
    let _running = p.g.erasure.running();
    for (term, expected) in [(app(Term::Def(f), [p.num(3)]), 6), (Term::Def(two), 2)] {
        let value = eval(&p.g, &[], &term).unwrap();
        let read = quote(&p.g, 0, &value).unwrap();
        assert_eq!(nat_of(&read), Some(expected));
    }
}

fn nat_of(term: &Term) -> Option<usize> {
    match term.strip_loc() {
        Term::Ctor(_, 0, _) => Some(0),
        Term::Ctor(_, 1, args) => nat_of(&args[0]).map(|n| n + 1),
        Term::Nat(n) => usize::try_from(&**n).ok(),
        _ => None,
    }
}

// Index unification: an opaque call against a constructor is stuck

#[test]
fn an_opaque_index_is_stuck_not_a_conflict() {
    // type IsZero: Nat -> Type = | Yes: IsZero 0. With `one := 1`, a
    // `case` on `IsZero one` has no possible branch when `one` unfolds
    // (`1` and `0` conflict), but is stuck when it's opaque.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let is_zero = family(
        &mut p.g,
        "IsZero",
        vec![],
        vec![("n", nat.clone())],
        Sort::Type(0),
    );
    let yes = ictor("Yes", vec![], vec![p.num(0)]);
    check::define_ctors(&mut p.g, is_zero, vec![yes]).unwrap();
    let one_body = p.num(1);
    let plain_one = submit(&mut p.g, "one", PLAIN, nat.clone(), one_body.clone()).unwrap();
    let opaque_one = submit(&mut p.g, "one2", OPAQUE, nat.clone(), one_body).unwrap();
    let ty = |one: DefId| arrow(Term::data(is_zero, vec![Term::Def(one)]), nat.clone());
    let impossible = lam("w", icase(0, is_zero, vec![(vec![], None)]));
    assert!(submit(&mut p.g, "a", PLAIN, ty(plain_one), impossible.clone()).is_ok());
    assert_eq!(
        submit(&mut p.g, "b", PLAIN, ty(opaque_one), impossible.clone()),
        Err("E-INDEX-STUCK")
    );
    let possible = lam("w", icase(0, is_zero, vec![(vec![], Some(p.num(0)))]));
    assert_eq!(
        submit(&mut p.g, "c", PLAIN, ty(opaque_one), possible),
        Err("E-INDEX-STUCK")
    );
    // Paired: unfolding `one2`, the branch is impossible again.
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[opaque_one],
    };
    assert!(submit(&mut p.g, "d", how, ty(opaque_one), impossible).is_ok());
}

// Groups (§6.11)

/// Declares `even` and `odd: Nat -> Nat` (1 for yes), each opaque if asked,
/// and submits them together.
fn even_odd(
    p: &mut Prelude,
    opaque: [bool; 2],
    unfolding: [&[DefId]; 2],
) -> Result<[DefId; 2], &'static str> {
    let ty = nat_to_nat(p);
    let even = declare(&mut p.g, "even", ty.clone());
    let odd = declare(&mut p.g, "odd", ty);
    let ids = [even, odd];
    for k in 0..2 {
        if opaque[k] {
            check::mark_opaque(&mut p.g, ids[k]);
        }
        check::set_unfolding(&mut p.g, ids[k], unfolding[k]);
    }
    let on_nat =
        |zero: Term, succ: Term| lam("n", case(0, p.nat, vec![(vec![], zero), (vec!["k"], succ)]));
    let bodies = vec![
        (even, on_nat(p.num(1), app(Term::Def(odd), [v(0)]))),
        (odd, on_nat(p.num(0), app(Term::Def(even), [v(0)]))),
    ];
    define_group(&mut p.g, &bodies).map_err(|d| d.code)?;
    Ok(ids)
}

#[test]
fn a_mixed_group_checks() {
    let mut p = Prelude::new();
    let [even, odd] = even_odd(&mut p, [true, false], [&[], &[]]).unwrap();
    // `odd 3` unfolds to a stuck `even 2`.
    let (three, two, one) = (p.num(3), p.num(2), p.num(1));
    let statement = nat_eq(
        &p,
        app(Term::Def(odd), [three]),
        app(Term::Def(even), [two]),
    );
    assert!(submit(&mut p.g, "a", THEOREM, statement, Term::Refl).is_ok());
    let p4 = p.num(4);
    assert_eq!(
        rfl_about(&mut p, "b", THEOREM, even, Some(p4.clone()), one.clone()),
        Err("E-REFL")
    );
    assert!(rfl_about(&mut p, "b", unfolding(&[even]), even, Some(p4), one).is_ok());
}

#[test]
fn unfolding_one_member_of_a_group_unfolds_the_others() {
    // D1267: `even 2 = 1` needs `odd 1`, which needs `even 0`. Unfolding
    // only `even` brings `odd`; the closure ends although the two refer to
    // each other.
    let mut p = Prelude::new();
    let [even, odd] = even_odd(&mut p, [true, true], [&[], &[]]).unwrap();
    let (two, one) = (p.num(2), p.num(1));
    assert_eq!(
        rfl_about(&mut p, "a", THEOREM, even, Some(two.clone()), one.clone()),
        Err("E-REFL")
    );
    assert!(
        rfl_about(
            &mut p,
            "a",
            unfolding(&[even]),
            even,
            Some(two),
            one.clone()
        )
        .is_ok()
    );
    // `odd 3 = 1`, by `even 2`, `odd 1` and `even 0`.
    let three = p.num(3);
    assert!(
        rfl_about(
            &mut p,
            "b",
            unfolding(&[odd]),
            odd,
            Some(three),
            one.clone()
        )
        .is_ok()
    );
    // And through another declaration: `e := even 4` unfolding `even`, then
    // a theorem unfolding only `e`.
    let (nat, four) = (p.nat_ty(), p.num(4));
    let how = How {
        opaque: true,
        theorem: false,
        unfolding: &[even],
    };
    let e = submit(&mut p.g, "e", how, nat, app(Term::Def(even), [four])).unwrap();
    assert!(rfl_about(&mut p, "c", unfolding(&[e]), e, None, one).is_ok());
}

#[test]
fn a_member_cant_unfold_a_group_mate() {
    let mut p = Prelude::new();
    let odd = DefId(p.g.defs.len() + 1); // declared second, below
    assert_eq!(
        even_odd(&mut p, [true, true], [&[odd], &[]]).err(),
        Some("E-UNFOLDING-GROUP")
    );
    // Paired: the same group without the clause.
    let mut p = Prelude::new();
    assert!(even_odd(&mut p, [true, true], [&[], &[]]).is_ok());
}

// Hashing (§6.6)

/// `f`, opaque or not, unfolding `unfolding` (named from `two` and `three`,
/// two opaque constants), and `user := f 1`: their hashes.
fn hashes(opaque: bool, names: &[usize]) -> (ContentHash, ContentHash) {
    let mut p = Prelude::new();
    let two = self::two(&mut p, OPAQUE);
    let (nat, three_body) = (p.nat_ty(), p.num(3));
    let three = submit(&mut p.g, "three", OPAQUE, nat, three_body).unwrap();
    let pool = [two, three];
    let listed: Vec<DefId> = names.iter().map(|i| pool[*i]).collect();
    let how = How {
        opaque,
        theorem: false,
        unfolding: &listed,
    };
    let f = double(&mut p, "f", how);
    let (nat, call) = (p.nat_ty(), app(Term::Def(f), [p.num(1)]));
    let user = submit(&mut p.g, "user", PLAIN, nat, call).unwrap();
    (hash_of(&p.g, f), hash_of(&p.g, user))
}

#[test]
fn a_cached_acceptance_doesnt_survive_a_change_of_opacity() {
    // The check cache is keyed by hash, so a user of `f` accepted with `f`
    // transparent has another key once `f` is opaque.
    let (plain_f, plain_user) = hashes(false, &[]);
    let (opaque_f, opaque_user) = hashes(true, &[]);
    assert_eq!((plain_f, plain_user), hashes(false, &[]), "deterministic");
    assert_ne!(plain_f, opaque_f);
    assert_ne!(plain_user, opaque_user);
    // Or of the `unfolding` list.
    let (listed_f, listed_user) = hashes(true, &[0]);
    assert_ne!(opaque_f, listed_f);
    assert_ne!(opaque_user, listed_user);
    assert_ne!(listed_f, hashes(true, &[1]).0);
    assert_ne!(listed_f, hashes(true, &[0, 1]).0);
}

#[test]
fn the_unfolding_list_is_hashed_in_a_canonical_order() {
    assert_eq!(hashes(true, &[0, 1]), hashes(true, &[1, 0]));
    assert_eq!(hashes(true, &[0, 1]), hashes(true, &[1, 0, 1]));
}

#[test]
fn a_group_members_opacity_changes_every_members_hash() {
    let group = |opaque: [bool; 2]| {
        let mut p = Prelude::new();
        let ids = even_odd(&mut p, opaque, [&[], &[]]).unwrap();
        (hash_of(&p.g, ids[0]), hash_of(&p.g, ids[1]))
    };
    let (even, odd) = group([false, false]);
    let (even2, odd2) = group([false, true]);
    assert_ne!(even, even2);
    assert_ne!(odd, odd2);
    assert_ne!(group([true, false]), group([false, true]));
}
