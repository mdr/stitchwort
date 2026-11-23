//! Proof marks (docs/core.md, "Proof marks"; full-proof-irrelevance.md §4):
//! the kernel derives each from a sort it computed, records it in the term
//! it returns, and refuses a given mark that differs; `is_proof` reads them
//! back, and the reference evaluator's version agrees.

use std::rc::Rc;

use crate::common::*;
use stitchwort_core::check::infer_closed;
use stitchwort_core::value::{eval, is_proof};
use stitchwort_core::{Icit, ProofMark, Sort, Term, Value};

fn rc(t: Term) -> Rc<Term> {
    Rc::new(t)
}

fn marked_pi(a: Term, b: Term, mark: ProofMark) -> Term {
    Term::Pi("x".into(), Icit::Explicit, rc(a), rc(b), mark)
}

fn marked_lam(body: Term, mark: ProofMark) -> Term {
    Term::Lam("x".into(), Icit::Explicit, rc(body), mark)
}

/// `0 = 0`.
fn zero_eq(p: &Prelude) -> Term {
    eq(Some(p.nat_ty()), p.num(0), p.num(0))
}

fn infer_code(p: &Prelude, term: &Term) -> &'static str {
    infer_closed(&p.g.ev(), term, span())
        .err()
        .map_or("ok", |d| d.code)
}

#[test]
fn binders_are_marked_from_their_types_sorts() {
    let p = Prelude::new();
    let g = p.g.ev();
    let cases = [
        (zero_eq(&p), ProofMark::Proof),
        (p.nat_ty(), ProofMark::NotProof),
        (ty(), ProofMark::NotProof),
        // A function type into a proposition is one (impredicativity).
        (pi("n", p.nat_ty(), zero_eq(&p)), ProofMark::Proof),
    ];
    for (dom, want) in cases {
        let pi_ty = marked_pi(dom.clone(), p.nat_ty(), ProofMark::Unknown);
        let (checked, _) = infer_closed(&g, &pi_ty, span()).expect("a type");
        let Term::Pi(.., mark) = checked.strip_loc() else {
            panic!("a function type")
        };
        assert_eq!(*mark, want, "the function type's binder");
        // A lambda against it: `x => 0`.
        let lam = Term::Ann(
            rc(marked_lam(p.num(0), ProofMark::Unknown)),
            rc(pi_ty.clone()),
        );
        let (checked, _) = infer_closed(&g, &lam, span()).expect("checks");
        let Term::Ann(lam, _) = checked.strip_loc() else {
            panic!("an annotation")
        };
        let Term::Lam(.., mark) = lam.strip_loc() else {
            panic!("a lambda")
        };
        assert_eq!(*mark, want, "the lambda's binder");
        // The variable it binds is read back as a proof or not.
        let value = eval(&g, &[], lam).expect("evaluates");
        let Value::Lam(_, _, _, lam_mark) = value else {
            panic!("a lambda value")
        };
        assert_eq!(lam_mark, want);
        let x = Value::var_marked(0, lam_mark);
        assert_eq!(is_proof(&g, &x), want);
        assert_eq!(stitchwort_core::reference::is_proof(&g, &x), want);
    }
}

#[test]
fn a_given_mark_that_differs_is_malformed() {
    let p = Prelude::new();
    // `(x: Nat) -> Nat` said to bind a proof, and `(x: 0 = 0) -> Nat` said
    // not to.
    let wrong = marked_pi(p.nat_ty(), p.nat_ty(), ProofMark::Proof);
    assert_eq!(infer_code(&p, &wrong), "E-MALFORMED");
    let wrong = marked_pi(zero_eq(&p), p.nat_ty(), ProofMark::NotProof);
    assert_eq!(infer_code(&p, &wrong), "E-MALFORMED");
    // The right marks, and no mark, are accepted.
    let right = marked_pi(p.nat_ty(), p.nat_ty(), ProofMark::NotProof);
    assert_eq!(infer_code(&p, &right), "ok");
    // A lambda over data marked as binding a proof.
    let wrong_lam = Term::Ann(
        rc(marked_lam(p.num(0), ProofMark::Proof)),
        rc(arrow(p.nat_ty(), p.nat_ty())),
    );
    assert_eq!(infer_code(&p, &wrong_lam), "E-MALFORMED");
    // A `let` of a proof marked as data.
    let let_ = Term::Let(
        "h".into(),
        rc(zero_eq(&p)),
        rc(Term::Refl),
        rc(p.num(0)),
        false,
        ProofMark::NotProof,
    );
    assert_eq!(infer_code(&p, &let_), "E-MALFORMED");
    // `J` into data marked as producing a proof: `J (y h => Nat) 1 refl`.
    let motive = lam("y", lam("h", p.nat_ty()));
    let j = |mark| {
        Term::J(
            rc(motive.clone()),
            rc(p.num(1)),
            rc(Term::Ann(rc(Term::Refl), rc(zero_eq(&p)))),
            mark,
        )
    };
    assert_eq!(infer_code(&p, &j(ProofMark::Proof)), "E-MALFORMED");
    assert_eq!(infer_code(&p, &j(ProofMark::Unknown)), "ok");
}

#[test]
fn definitions_are_marked_by_their_types_sort() {
    let mut p = Prelude::new();
    let zero_eq = zero_eq(&p);
    let proof = define(&mut p.g, "proof", zero_eq, Term::Refl).expect("checks");
    let (nat_ty, three) = (p.nat_ty(), p.num(3));
    let data = define(&mut p.g, "data", nat_ty, three).expect("checks");
    let g = p.g.ev();
    assert!(g.def(proof).proof());
    assert!(!g.def(data).proof());
    let call = |id| Value::Neutral(stitchwort_core::value::Head::Def(id), Default::default());
    assert_eq!(is_proof(&g, &call(proof)), ProofMark::Proof);
    assert_eq!(is_proof(&g, &call(data)), ProofMark::NotProof);
    assert_eq!(
        stitchwort_core::reference::is_proof(&g, &call(proof)),
        ProofMark::Proof
    );
    assert_eq!(is_proof(&g, &Value::Refl), ProofMark::Proof);
    assert_eq!(is_proof(&g, &Value::Sort(Sort::Prop)), ProofMark::NotProof);
    // The reference validator agrees with the installed marks.
    stitchwort_core::reference::validate_marks(&g, &[proof, data]);
}
