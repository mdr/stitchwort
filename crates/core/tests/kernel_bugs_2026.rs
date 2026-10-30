//! Kernel bugs other proof assistants had in 2026, as hand-built terms that
//! skip the parser and the elaborator (docs/research/kernel.md §5.4, ticket
//! T1). Each must be refused by the kernel itself, with an accepted
//! neighbour where the shape has one. The `.sw` versions are in
//! `examples/soundness/kernel-2026-*.sw`; those are refused by the
//! elaborator first, so these are the trust-boundary tests.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, define_group};
use stitchwort_core::{DataId, DefId, Sort, Term};

fn refl_proves(
    p: &mut Prelude,
    name: &str,
    ty: Term,
    binders: &[&str],
) -> Result<DefId, &'static str> {
    let body = binders
        .iter()
        .rev()
        .fold(Term::Refl, |body, x| lam(x, body));
    define(&mut p.g, name, ty, body)
}

/// Arena `k-rec-conv`: `(x => x) = (_ => y)` by `rfl`.
#[test]
fn k_rec_conv_identity_is_not_a_constant() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let fun = arrow(nat.clone(), nat.clone());
    let ty = pi("y", nat, eq(Some(fun), lam("x", v(0)), lam("_", v(1))));
    assert_eq!(refl_proves(&mut p, "bad", ty, &["y"]), Err("E-REFL"));
}

/// Arena `k-rec-conv`, K-like reduction: `J` on a proof variable
/// `h: 0 = y` is stuck, never its base. Neighbour: on `rfl` it computes.
#[test]
fn j_on_a_proof_variable_does_not_reduce() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let (motive, five) = (lam("z", lam("q", nat.clone())), p.num(5));
    let j = |proof: Term| {
        Term::J(
            Rc::new(motive.clone()),
            Rc::new(five.clone()),
            Rc::new(proof),
        )
    };
    // (y: Nat) -> (h: 0 = y) -> J (z q => Nat) 5 h = 5
    let ty = pi(
        "y",
        nat.clone(),
        pi(
            "h",
            eq(Some(nat.clone()), p.num(0), v(0)),
            eq(Some(nat.clone()), j(v(0)), five.clone()),
        ),
    );
    assert_eq!(refl_proves(&mut p, "bad", ty, &["y", "h"]), Err("E-REFL"));
    let zero_eq = eq(Some(nat.clone()), p.num(0), p.num(0));
    let refl = Term::Ann(Rc::new(Term::Refl), Rc::new(zero_eq));
    let ty = eq(Some(nat), j(refl), five.clone());
    assert!(refl_proves(&mut p, "good", ty, &[]).is_ok());
}

/// Arena `eta-unit-like-proof-field`: two values of a record whose only
/// field is a proof aren't convertible (no eta for records, no definitional
/// proof irrelevance).
#[test]
fn records_of_a_proof_are_not_convertible() {
    let mut p = Prelude::new();
    let zero_eq = eq(Some(p.nat_ty()), p.num(0), p.num(0));
    let bx = data(&mut p.g, "Box", vec![], Sort::Type(0));
    check::define_ctors(&mut p.g, bx, vec![ctor("MkBox", vec![("h", zero_eq)])]).expect("Box");
    let box_ty = Term::data(bx, vec![]);
    let ty = pi("p", box_ty.clone(), pi("q", box_ty, eq(None, v(1), v(0))));
    assert_eq!(refl_proves(&mut p, "bad", ty, &["p", "q"]), Err("E-REFL"));
}

/// `n => case n of Zero => 0; Succ _ => one`, a definition that isn't
/// recursive, so two of them are compared by their case trees (SW-386).
fn tree(p: &mut Prelude, name: &str, one: usize) -> DefId {
    let nat = p.nat_ty();
    let body = lam(
        "n",
        case(0, p.nat, vec![(vec![], p.num(0)), (vec!["m"], p.num(one))]),
    );
    define(&mut p.g, name, arrow(nat.clone(), nat), body).expect("tree")
}

fn pair(list: DataId, a: Term, b: Term) -> Term {
    let nil = Term::ctor(list, 0, vec![]);
    Term::ctor(list, 1, vec![a, Term::ctor(list, 1, vec![b, nil])])
}

/// lean4#14806: a conversion memo must be keyed by the exact pair. In one
/// comparison `f x ≡ g x` is found (and remembered); `f y ≡ g x` must
/// still be compared, not answered from the pair of definitions.
#[test]
fn the_conversion_memo_is_keyed_by_the_exact_pair() {
    let mut p = Prelude::new();
    let f = tree(&mut p, "f", 1);
    let g = tree(&mut p, "g", 1);
    let h = tree(&mut p, "h", 2);
    let nat = p.nat_ty();
    let list_nat = Term::data(p.list, vec![nat.clone()]);
    let call = |d: DefId, x: Term| app(Term::Def(d), [x]);
    // Context [x, y]: x is v(1), y is v(0).
    let both = |lhs: Term, rhs: Term| {
        pi(
            "x",
            nat.clone(),
            pi("y", nat.clone(), eq(Some(list_nat.clone()), lhs, rhs)),
        )
    };
    let bad = both(
        pair(p.list, call(f, v(1)), call(f, v(0))),
        pair(p.list, call(g, v(1)), call(g, v(1))),
    );
    assert_eq!(refl_proves(&mut p, "bad", bad, &["x", "y"]), Err("E-REFL"));
    // A chain: f x ≡ g x and g x ≡ f x are found, then f x ≡ h x is false.
    let chain = both(
        pair(p.list, call(f, v(1)), call(f, v(1))),
        pair(p.list, call(g, v(1)), call(h, v(1))),
    );
    assert_eq!(
        refl_proves(&mut p, "chain", chain, &["x", "y"]),
        Err("E-REFL")
    );
    let good = both(
        pair(p.list, call(f, v(1)), call(f, v(0))),
        pair(p.list, call(g, v(1)), call(g, v(0))),
    );
    assert!(refl_proves(&mut p, "good", good, &["x", "y"]).is_ok());
}

/// CVE-2026-72703: a group whose only calls are cross-calls, each on a
/// larger argument: `f n = g (Succ n)`, `g n = f (Succ n)`.
#[test]
fn cross_calls_that_grow_are_refused() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let f = declare(&mut p.g, "f", arrow(nat.clone(), nat.clone()));
    let g = declare(&mut p.g, "g", arrow(nat.clone(), nat));
    let succ = |t: Term| Term::ctor(p.nat, 1, vec![t]);
    let members = [
        (f, lam("n", app(Term::Def(g), [succ(v(0))]))),
        (g, lam("n", app(Term::Def(f), [succ(v(0))]))),
    ];
    let e = define_group(&mut p.g, &members).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
}

/// CVE-2026-72705: a recursive function passed to another recursive
/// function, which applies it to something that isn't smaller. `inner k n`
/// recurses on `n` and calls `k 1`; `outer n = inner (x => outer x) n`, or
/// with `outer` bare.
#[test]
fn a_member_passed_to_a_recursive_function_is_refused() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let fun = arrow(nat.clone(), nat.clone());
    let inner = declare(
        &mut p.g,
        "inner",
        arrow(fun, arrow(nat.clone(), nat.clone())),
    );
    // Context [k, n], then [k, n, m] in the `Succ` branch.
    let body = lam(
        "k",
        lam(
            "n",
            case(
                0,
                p.nat,
                vec![
                    (vec![], app(v(1), [p.num(1)])),
                    (vec!["m"], app(Term::Def(inner), [v(2), v(0)])),
                ],
            ),
        ),
    );
    check::define_def(&mut p.g, inner, &body).expect("inner terminates");
    let outer = declare(&mut p.g, "outer", arrow(nat.clone(), nat.clone()));
    let eta = lam("x", app(Term::Def(outer), [v(0)]));
    let body = lam("n", app(Term::Def(inner), [eta, v(0)]));
    let e = check::define_def(&mut p.g, outer, &body).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    let bare = declare(&mut p.g, "outer2", arrow(nat.clone(), nat));
    let body = lam("n", app(Term::Def(inner), [Term::Def(bare), v(0)]));
    let e = check::define_def(&mut p.g, bare, &body).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
}
