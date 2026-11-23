//! Rule S's index test reads the type of the scrutinee off the case tree
//! (`slot_type`), which needs the `case` node to occur exactly once in it,
//! so the path to it is the one evaluation took. The elaborator never
//! shares a node between two branches, so only a hand-built tree reaches
//! that guard: admitted trusted (`check::admit_trusted_group`), since it
//! is the one route that installs a body as given.

use std::rc::Rc;

use crate::common::*;
use stitchwort_core::check;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{eval, force};
use stitchwort_core::{DefId, Icit, ProofMark, Sort, Term, Value};

/// `Fam: Nat -> Prop` with `Mk: Fam 0`; `W: Type` with `A (h: Fam 0)` and
/// `B (h: Fam 0)`; and `f: W -> Nat` matching `w`, then the field `h` of
/// either constructor, whose single-branch `case` rule S takes (`h`'s
/// type's index is the constructor's own), to `7`. `share` makes both
/// branches hold the same `case` node.
struct Shared {
    p: Prelude,
    w: stitchwort_core::DataId,
    f: DefId,
}

fn build(share: bool) -> Shared {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let fam = family(&mut p.g, "Fam", vec![], vec![("n", nat)], Sort::Prop);
    let zero = p.num(0);
    check::define_ctors(&mut p.g, fam, vec![ictor("Mk", vec![], vec![zero])]).expect("Fam");
    let fam_zero = Term::data(fam, vec![p.num(0)]);
    let w = data(&mut p.g, "W", vec![], Sort::Type(0));
    let fields = || vec![("h", fam_zero.clone())];
    check::define_ctors(&mut p.g, w, vec![ctor("A", fields()), ctor("B", fields())]).expect("W");
    let inner = || icase(0, fam, vec![(vec![], Some(p.num(7)))]);
    let shared = Rc::new(inner());
    let branch = |names: Vec<&str>| Branch {
        names: names.into_iter().map(Into::into).collect(),
        body: Some(if share {
            shared.clone()
        } else {
            Rc::new(inner())
        }),
    };
    // Trusted admission takes the marks as given: the binder is data.
    let cases = Term::Case(0, w, vec![branch(vec!["h"]), branch(vec!["h"])].into());
    let body = Term::Lam(
        "w".into(),
        Icit::Explicit,
        Rc::new(cases),
        ProofMark::NotProof,
    );
    let ty = arrow(Term::data(w, vec![]), p.nat_ty());
    let f = declare(&mut p.g, "f", ty);
    check::admit_trusted_group(&mut p.g, &[(f, body)]).expect("admitted");
    Shared { p, w, f }
}

/// `f (ctor h)` for a variable proof `h`, forced.
fn apply(s: &Shared, ctor: usize) -> Value {
    let g = s.p.g.ev();
    let call = app(Term::Def(s.f), [Term::ctor(s.w, ctor, vec![v(0)])]);
    let h = Value::var_marked(0, ProofMark::Proof);
    force(&g, eval(&g, &[h], &call).expect("evaluates")).expect("forces")
}

fn seven(s: &Shared) -> Value {
    eval(&s.p.g.ev(), &[], &s.p.num(7)).expect("a number")
}

#[test]
fn rule_s_takes_an_unshared_case_node() {
    let s = build(false);
    for ctor in [0, 1] {
        assert_eq!(
            format!("{:?}", apply(&s, ctor)),
            format!("{:?}", seven(&s)),
            "constructor {ctor}"
        );
    }
}

#[test]
fn rule_s_declines_a_case_node_found_twice() {
    let s = build(true);
    for ctor in [0, 1] {
        let got = apply(&s, ctor);
        assert!(
            matches!(got, Value::Neutral(..)),
            "constructor {ctor}: the match stays stuck, got {got:?}"
        );
    }
}
