//! Record eta in the kernel (docs/proposals/record-eta.md §6, §7, §14
//! stage 1): which types have it, the projection form `Term::Proj` and its
//! typing, rule 1 (a constructor against an unknown, field by field against
//! its projections) and rule 2 (a `case` on an unknown takes its only
//! branch). Each accepted case has must-reject neighbours: the D1981 unit
//! type, recursive and multi-constructor types, types in `Prop`, interface
//! dictionaries (marked), and ill-typed projections. The terms are built by
//! hand, as the elaborator never would for the rejected ones.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check;
use stitchwort_core::hash::data_hash;
use stitchwort_core::term::Term;
use stitchwort_core::value::{Value, conv, eval};
use stitchwort_core::{DataId, Sort, reference};

fn proj(d: DataId, i: usize, t: Term) -> Term {
    Term::Proj(d, i, Rc::new(t))
}

/// `type Pos = MkPos (row: Nat) (column: Nat)`.
fn position(p: &mut Prelude) -> DataId {
    let nat = p.nat_ty();
    let pos = data(&mut p.g, "Pos", vec![], Sort::Type(0));
    check::define_ctors(
        &mut p.g,
        pos,
        vec![ctor("MkPos", vec![("row", nat.clone()), ("column", nat)])],
    )
    .expect("Pos");
    pos
}

/// `type Box (a: Type) = MkBox (value: a)`.
fn boxed(p: &mut Prelude) -> DataId {
    let b = data(&mut p.g, "Box", vec![("a", ty())], Sort::Type(0));
    check::define_ctors(&mut p.g, b, vec![ctor("MkBox", vec![("value", v(0))])]).expect("Box");
    b
}

/// `(x: ty) -> a = b` proved by `rfl`, with `a` and `b` under `x`.
fn rfl_about(p: &mut Prelude, name: &str, ty: Term, a: Term, b: Term) -> Result<(), &'static str> {
    define(
        &mut p.g,
        name,
        pi("x", ty, eq(None, a, b)),
        lam("x", Term::Refl),
    )
    .map(|_| ())
}

#[test]
fn eta_is_decided_from_the_declaration() {
    let mut p = Prelude::new();
    let pos = position(&mut p);
    let b = boxed(&mut p);
    assert!(p.g.data(pos).eta(), "a record of data fields");
    assert!(p.g.data(b).eta(), "with a parameter");
    assert!(!p.g.data(p.nat).eta(), "two constructors");
    assert!(!p.g.data(p.list).eta(), "two constructors");
}

#[test]
fn a_record_is_its_constructor_applied_to_its_projections() {
    let mut p = Prelude::new();
    let pos = position(&mut p);
    let pos_ty = Term::data(pos, vec![]);
    let rebuilt = Term::ctor(pos, 0, vec![proj(pos, 0, v(0)), proj(pos, 1, v(0))]);
    rfl_about(&mut p, "eta", pos_ty.clone(), v(0), rebuilt.clone()).expect("x = MkPos x.0 x.1");
    rfl_about(&mut p, "etaSym", pos_ty.clone(), rebuilt, v(0)).expect("MkPos x.0 x.1 = x");
    // Not with the fields swapped.
    let swapped = Term::ctor(pos, 0, vec![proj(pos, 1, v(0)), proj(pos, 0, v(0))]);
    assert!(rfl_about(&mut p, "swapped", pos_ty, v(0), swapped).is_err());
}

#[test]
fn a_projection_of_a_constructor_computes() {
    let mut p = Prelude::new();
    let pos = position(&mut p);
    let built = Term::ctor(pos, 0, vec![p.num(3), v(0)]);
    let (nat, three) = (p.nat_ty(), p.num(3));
    rfl_about(
        &mut p,
        "row",
        nat.clone(),
        proj(pos, 0, built.clone()),
        three.clone(),
    )
    .expect("row");
    rfl_about(
        &mut p,
        "column",
        nat.clone(),
        proj(pos, 1, built.clone()),
        v(0),
    )
    .expect("column");
    assert!(rfl_about(&mut p, "wrong", nat, proj(pos, 1, built), three).is_err());
}

/// `down p = match p with | MkPos r c => MkPos (Succ r) c`.
fn down(p: &mut Prelude, pos: DataId) -> stitchwort_core::DefId {
    let pos_ty = Term::data(pos, vec![]);
    let body = lam(
        "p",
        case(
            0,
            pos,
            vec![(
                vec!["r", "c"],
                Term::ctor(pos, 0, vec![Term::ctor(p.nat, 1, vec![v(1)]), v(0)]),
            )],
        ),
    );
    define(&mut p.g, "down", arrow(pos_ty.clone(), pos_ty), body).expect("down")
}

#[test]
fn a_match_on_an_unknown_record_takes_its_branch() {
    let mut p = Prelude::new();
    let pos = position(&mut p);
    let down = down(&mut p, pos);
    let pos_ty = Term::data(pos, vec![]);
    let down_x = app(Term::Def(down), [v(0)]);
    // `(down x).column = x.column`, and `down x = MkPos (Succ x.row) x.column`.
    rfl_about(
        &mut p,
        "downColumn",
        pos_ty.clone(),
        proj(pos, 1, down_x.clone()),
        proj(pos, 1, v(0)),
    )
    .expect("(down x).column = x.column");
    let expected = Term::ctor(
        pos,
        0,
        vec![
            Term::ctor(p.nat, 1, vec![proj(pos, 0, v(0))]),
            proj(pos, 1, v(0)),
        ],
    );
    rfl_about(&mut p, "downIs", pos_ty.clone(), down_x.clone(), expected).expect("down x");
    // But not that it changes nothing.
    assert!(rfl_about(&mut p, "downSame", pos_ty, down_x, v(0)).is_err());
}

#[test]
fn eta_works_through_parameters() {
    let mut p = Prelude::new();
    let b = boxed(&mut p);
    let box_nat = Term::data(b, vec![p.nat_ty()]);
    let rebuilt = Term::ctor(b, 0, vec![proj(b, 0, v(0))]);
    rfl_about(&mut p, "boxEta", box_nat, v(0), rebuilt).expect("x = MkBox x.value");
}

#[test]
fn nested_records_expand_down_to_a_type_without_eta() {
    let mut p = Prelude::new();
    let b = boxed(&mut p);
    let list_nat = Term::data(p.list, vec![p.nat_ty()]);
    let wrap = |t: Term| Term::data(b, vec![t]);
    let ty = wrap(wrap(wrap(list_nat)));
    let inner = proj(b, 0, proj(b, 0, proj(b, 0, v(0))));
    let rebuilt = Term::ctor(
        b,
        0,
        vec![Term::ctor(
            b,
            0,
            vec![Term::ctor(b, 0, vec![inner.clone()])],
        )],
    );
    rfl_about(&mut p, "deep", ty.clone(), v(0), rebuilt).expect("three layers");
    // A list has no eta: the innermost field is an unknown list, not `Nil`.
    let nil = Term::ctor(p.list, 0, vec![]);
    assert!(rfl_about(&mut p, "nil", ty, inner, nil).is_err());
}

#[test]
fn a_proof_field_is_skipped_beside_a_data_field() {
    // `type S = MkS (value: Nat) (ok: value = value)`.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let s = data(&mut p.g, "S", vec![], Sort::Type(0));
    check::define_ctors(
        &mut p.g,
        s,
        vec![ctor(
            "MkS",
            vec![("value", nat.clone()), ("ok", eq(Some(nat), v(0), v(0)))],
        )],
    )
    .expect("S");
    assert!(p.g.data(s).eta());
    let s_ty = Term::data(s, vec![]);
    // Any proof will do for the proof field.
    let rebuilt = Term::ctor(s, 0, vec![proj(s, 0, v(0)), Term::Refl]);
    rfl_about(&mut p, "sEta", s_ty.clone(), v(0), rebuilt).expect("x = MkS x.value rfl");
    // But the data field is compared.
    let other = Term::ctor(s, 0, vec![p.num(0), Term::Refl]);
    assert!(rfl_about(&mut p, "sZero", s_ty, v(0), other).is_err());
}

// D1981: a record whose fields are all proofs gets no eta. With it, every
// value would equal `MkSmall rfl` (the proof field skipped), so any two
// would be equal through it while comparing them directly says they differ.

#[test]
fn a_record_of_proofs_only_has_no_eta() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let small = data(&mut p.g, "Small", vec![], Sort::Type(0));
    let zero = p.num(0);
    check::define_ctors(
        &mut p.g,
        small,
        vec![ctor(
            "MkSmall",
            vec![("ok", eq(Some(nat), zero.clone(), zero))],
        )],
    )
    .expect("Small");
    let small_ty = Term::data(small, vec![]);
    let unit = Term::ctor(small, 0, vec![Term::Refl]);
    assert!(
        rfl_about(&mut p, "unit", small_ty.clone(), v(0), unit).is_err(),
        "x = MkSmall rfl must not hold by computation"
    );
    let two = define(
        &mut p.g,
        "two",
        pi(
            "x",
            small_ty.clone(),
            pi("y", small_ty.clone(), eq(None, v(1), v(0))),
        ),
        lam("x", lam("y", Term::Refl)),
    );
    assert!(two.is_err(), "x = y for two unknown values");
    assert!(rfl_about(&mut p, "proj", small_ty, proj(small, 0, v(0)), Term::Refl).is_err());
    assert!(!p.g.data(small).eta());
}

#[test]
fn a_record_with_no_fields_has_no_eta() {
    let mut p = Prelude::new();
    let unit = data(&mut p.g, "Unit", vec![], Sort::Type(0));
    check::define_ctors(&mut p.g, unit, vec![ctor("MkUnit", vec![])]).expect("Unit");
    assert!(!p.g.data(unit).eta());
    let unit_ty = Term::data(unit, vec![]);
    let mk = Term::ctor(unit, 0, vec![]);
    assert!(rfl_about(&mut p, "unitEta", unit_ty, v(0), mk).is_err());
}

#[test]
fn a_recursive_type_has_no_eta() {
    let mut p = Prelude::new();
    // `type Rose = MkRose (kids: List Rose)`: one constructor, but recursive.
    let rose = data(&mut p.g, "Rose", vec![], Sort::Type(0));
    let kids = Term::data(p.list, vec![Term::data(rose, vec![])]);
    check::define_ctors(&mut p.g, rose, vec![ctor("MkRose", vec![("kids", kids)])]).expect("Rose");
    assert!(!p.g.data(rose).eta());
    // `type Loop = MkLoop (next: Loop)`.
    let lp = data(&mut p.g, "Loop", vec![], Sort::Type(0));
    let lp_ty = Term::data(lp, vec![]);
    check::define_ctors(
        &mut p.g,
        lp,
        vec![ctor("MkLoop", vec![("next", lp_ty.clone())])],
    )
    .expect("Loop");
    assert!(!p.g.data(lp).eta());
    let rebuilt = Term::ctor(lp, 0, vec![proj(lp, 0, v(0))]);
    assert!(rfl_about(&mut p, "loopEta", lp_ty, v(0), rebuilt).is_err());
}

#[test]
fn a_type_with_two_constructors_has_no_eta() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let two = data(&mut p.g, "Two", vec![], Sort::Type(0));
    check::define_ctors(
        &mut p.g,
        two,
        vec![
            ctor("A", vec![("n", nat.clone())]),
            ctor("B", vec![("n", nat.clone())]),
        ],
    )
    .expect("Two");
    assert!(!p.g.data(two).eta());
    let two_ty = Term::data(two, vec![]);
    assert!(
        rfl_about(
            &mut p,
            "a",
            two_ty.clone(),
            v(0),
            Term::ctor(two, 0, vec![proj(two, 0, v(0))])
        )
        .is_err()
    );
    // A case on an unknown of it stays stuck.
    let get = define(
        &mut p.g,
        "get",
        arrow(two_ty.clone(), nat.clone()),
        lam(
            "t",
            case(0, two, vec![(vec!["n"], v(0)), (vec!["n"], v(0))]),
        ),
    )
    .expect("get");
    let zero = p.num(0);
    assert!(rfl_about(&mut p, "getZero", two_ty, app(Term::Def(get), [v(0)]), zero).is_err());
}

#[test]
fn a_proposition_has_no_eta() {
    // `type Has: Prop = MkHas (n: Nat) (ok: n = n)`.
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let has = data(&mut p.g, "Has", vec![], Sort::Prop);
    check::define_ctors(
        &mut p.g,
        has,
        vec![ctor(
            "MkHas",
            vec![("n", nat.clone()), ("ok", eq(Some(nat), v(0), v(0)))],
        )],
    )
    .expect("Has");
    assert!(!p.g.data(has).eta());
    let has_ty = Term::data(has, vec![]);
    let nat = p.nat_ty();
    assert!(
        define(
            &mut p.g,
            "n",
            arrow(has_ty, nat),
            lam("h", proj(has, 0, v(0)))
        )
        .is_err(),
        "no data out of a proof"
    );
}

#[test]
fn an_interface_dictionary_has_no_eta_and_hashes_apart() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let make = |p: &mut Prelude, name: &str, mark: bool| {
        let d = data(&mut p.g, name, vec![], Sort::Type(0));
        if mark {
            check::mark_no_eta(&mut p.g, d);
        }
        check::define_ctors(&mut p.g, d, vec![ctor("MkD", vec![("op", nat.clone())])])
            .expect("dictionary");
        d
    };
    let plain = make(&mut p, "Dict", false);
    let marked = make(&mut p, "Dict", true);
    let ev = p.g.ev();
    assert_ne!(
        data_hash(&ev, plain).unwrap(),
        data_hash(&ev, marked).unwrap()
    );
    let marked_ty = Term::data(marked, vec![]);
    let rebuilt = Term::ctor(marked, 0, vec![proj(marked, 0, v(0))]);
    assert!(rfl_about(&mut p, "dictEta", marked_ty, v(0), rebuilt).is_err());
    assert!(p.g.data(plain).eta());
    assert!(!p.g.data(marked).eta());
}

// Ill-typed projections: the type named must be the value's own (the Lean
// projection bug, records.md §7.6), and the field must exist.

#[test]
fn a_projection_of_another_type_is_refused() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    let person = data(&mut p.g, "Person", vec![], Sort::Type(0));
    let pet = data(&mut p.g, "Pet", vec![], Sort::Type(0));
    for d in [person, pet] {
        check::define_ctors(
            &mut p.g,
            d,
            vec![ctor(
                "Mk",
                vec![("name", nat.clone()), ("age", nat.clone())],
            )],
        )
        .expect("same layout");
    }
    let pet_ty = Term::data(pet, vec![]);
    let err = define(
        &mut p.g,
        "wrong",
        arrow(pet_ty.clone(), nat.clone()),
        lam("q", proj(person, 0, v(0))),
    );
    assert_eq!(err.unwrap_err(), "E-TYPE-MISMATCH");
    // Two types with one layout never convert.
    let as_person = Term::ctor(person, 0, vec![proj(pet, 0, v(0)), proj(pet, 1, v(0))]);
    assert!(rfl_about(&mut p, "petIsPerson", pet_ty.clone(), v(0), as_person).is_err());
    // A field past the last.
    assert!(
        define(
            &mut p.g,
            "third",
            arrow(pet_ty.clone(), nat.clone()),
            lam("q", proj(pet, 2, v(0)))
        )
        .is_err()
    );
    // A projection of something that isn't a value of a data type.
    assert!(
        define(
            &mut p.g,
            "ofNat",
            arrow(nat.clone(), nat),
            lam("n", proj(pet, 0, v(0)))
        )
        .is_err()
    );
}

#[test]
fn a_projection_has_the_field_type_of_the_parameters_given() {
    let mut p = Prelude::new();
    let b = boxed(&mut p);
    let list_nat = Term::data(p.list, vec![p.nat_ty()]);
    let box_nat = Term::data(b, vec![p.nat_ty()]);
    let nat = p.nat_ty();
    define(
        &mut p.g,
        "ok",
        arrow(box_nat.clone(), nat),
        lam("b", proj(b, 0, v(0))),
    )
    .expect("a Nat");
    assert!(
        define(
            &mut p.g,
            "bad",
            arrow(box_nat, list_nat),
            lam("b", proj(b, 0, v(0)))
        )
        .is_err(),
        "a `Box Nat`'s field isn't a list"
    );
}

/// The machine and the reference evaluator agree on both rules.
#[test]
fn the_reference_evaluator_agrees() {
    let mut p = Prelude::new();
    let pos = position(&mut p);
    let down = down(&mut p, pos);
    let ev = &p.g.ev();
    let env = [Value::var(0)];
    let pairs = [
        (
            v(0),
            Term::ctor(pos, 0, vec![proj(pos, 0, v(0)), proj(pos, 1, v(0))]),
            true,
        ),
        (
            proj(pos, 1, app(Term::Def(down), [v(0)])),
            proj(pos, 1, v(0)),
            true,
        ),
        (
            app(Term::Def(down), [v(0)]),
            Term::ctor(
                pos,
                0,
                vec![
                    Term::ctor(p.nat, 1, vec![proj(pos, 0, v(0))]),
                    proj(pos, 1, v(0)),
                ],
            ),
            true,
        ),
        (proj(pos, 0, v(0)), proj(pos, 1, v(0)), false),
        (app(Term::Def(down), [v(0)]), v(0), false),
    ];
    for (a, b, same) in pairs {
        let machine = conv(
            ev,
            1,
            &eval(ev, &env, &a).unwrap(),
            &eval(ev, &env, &b).unwrap(),
        )
        .unwrap();
        let refr = reference::conv(
            ev,
            1,
            &reference::eval(ev, &env, &a).unwrap(),
            &reference::eval(ev, &env, &b).unwrap(),
        )
        .unwrap();
        assert_eq!(machine, same, "machine: {a:?} against {b:?}");
        assert_eq!(refr, same, "reference: {a:?} against {b:?}");
    }
}
