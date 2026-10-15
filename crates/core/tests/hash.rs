//! Content hashes distinguish everything that matters about a declaration.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check;
use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, Icit, Sort, Term};

/// Defines `name : ty = body` in a fresh prelude and returns its hash.
fn hash(
    ty: impl Fn(&Prelude) -> Term,
    body: impl Fn(&Prelude) -> Term,
    theorem: bool,
) -> ContentHash {
    let mut p = Prelude::new();
    let (ty, body) = (ty(&p), body(&p));
    let id = check::declare_def(&mut p.g, &"x".into(), &ty, theorem, false, span())
        .expect("type checks");
    check::define_def(&mut p.g, id, &body).expect("body checks");
    def_hash(&p.g, id).unwrap().expect("defined")
}

#[test]
fn hashes_distinguish_every_part_of_a_definition() {
    let nat_id = |p: &Prelude| arrow(p.nat_ty(), p.nat_ty());
    let identity = |_: &Prelude| lam("n", v(0));
    let base = hash(nat_id, identity, false);
    assert_eq!(base, hash(nat_id, identity, false), "deterministic");

    // A different body, a different variable, a different literal.
    assert_ne!(
        base,
        hash(nat_id, |p| lam("n", p.plus(v(0), p.num(0))), false)
    );
    let two = hash(|p| p.nat_ty(), |p| p.num(2), false);
    assert_ne!(two, hash(|p| p.nat_ty(), |p| p.num(3), false));
    let first = hash(
        |p| arrow(p.nat_ty(), arrow(p.nat_ty(), p.nat_ty())),
        |_| lam("a", lam("b", v(1))),
        false,
    );
    let second = hash(
        |p| arrow(p.nat_ty(), arrow(p.nat_ty(), p.nat_ty())),
        |_| lam("a", lam("b", v(0))),
        false,
    );
    assert_ne!(first, second, "which variable");

    // Implicitness.
    let implicit = hash(
        |p| {
            Term::Pi(
                "n".into(),
                Icit::Implicit,
                Rc::new(p.nat_ty()),
                Rc::new(p.nat_ty()),
            )
        },
        |_| ilam("n", v(0)),
        false,
    );
    assert_ne!(base, implicit);

    // Universe levels.
    let small = hash(|_| ty_n(1), |_| ty(), false);
    let large = hash(|_| ty_n(2), |_| ty_n(1), false);
    assert_ne!(small, large);
    let prop_type = hash(|_| ty(), |_| prop(), false);
    assert_ne!(small, prop_type);

    // Whether it's a theorem.
    let statement = |p: &Prelude| eq(None, p.num(1), p.num(1));
    assert_ne!(
        hash(statement, |_| Term::Refl, true),
        hash(statement, |_| Term::Refl, false)
    );
}

#[test]
fn hashes_distinguish_which_data_type_is_used() {
    let mut p = Prelude::new();
    // Two data types with identical structure but different names.
    let mut declare = |name: &str| {
        let d = data(&mut p.g, name, vec![], Sort::Type(0));
        check::define_ctors(&mut p.g, d, vec![ctor("Mk", vec![])]).expect("checks");
        d
    };
    let (a, b) = (declare("A"), declare("B"));
    assert_ne!(data_hash(&p.g, a).unwrap(), data_hash(&p.g, b).unwrap());
    let mut identity_on = |d: DataId| {
        let ty = arrow(Term::Data(d, vec![]), Term::Data(d, vec![]));
        let id = check::declare_def(&mut p.g, &"f".into(), &ty, false, false, span()).unwrap();
        check::define_def(&mut p.g, id, &lam("x", v(0))).unwrap();
        def_hash(&p.g, id).unwrap().unwrap()
    };
    assert_ne!(identity_on(a), identity_on(b));
}

#[test]
fn a_data_types_hash_includes_its_constructors_once_they_are_defined() {
    let mut p = Prelude::new();
    let d = data(&mut p.g, "Later", vec![], Sort::Type(0));
    let before = data_hash(&p.g, d).unwrap();
    check::define_ctors(&mut p.g, d, vec![ctor("One", vec![])]).unwrap();
    assert_ne!(
        before,
        data_hash(&p.g, d).unwrap(),
        "not stuck at the hash it had with no constructors"
    );
}

#[test]
fn hashes_print_as_short_hex() {
    let h = hash(|p| p.nat_ty(), |p| p.num(1), false);
    assert_eq!(h.hex().len(), 64);
    assert_eq!(format!("{h:?}"), format!("#{}", &h.hex()[..12]));
}
