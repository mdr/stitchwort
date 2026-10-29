//! Trusted admission (`check::admit_trusted_*`): the check cache's trust
//! boundary (docs/proposals/check-cache.md, "As built (stage 3)", D1660).
//! What it installs must be exactly what checking installs, and what it
//! still refuses is only structural.

mod common;

use common::*;
use stitchwort_core::check::{self, DataDecl};
use stitchwort_core::globals::{Ctor, Globals, State};
use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::{DefId, Sort, Term};

fn code<T>(result: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    result.err().map_or("ok", |d| d.code)
}

/// `a` again, every declaration admitted trusted with the terms checking
/// gave back, in the same order, as a cache replay does. For environments
/// whose groups each have one member, defined right after being declared.
fn trusted_copy(a: &Globals) -> Globals {
    let mut b = Globals::default();
    let (mut i, mut j) = (0, 0);
    while i < a.defs.len() || j < a.datas.len() {
        if j < a.datas.len() && a.datas[j].defs_before == i {
            let data = &a.datas[j];
            assert_eq!(data.group.len(), 1);
            let decl = DataDecl {
                name: data.name.clone(),
                span: data.span,
                record: data.record,
                indices: data.indices.clone(),
            };
            let ids =
                check::admit_trusted_data_decls(&mut b, data.params.clone(), data.sort, vec![decl])
                    .expect("declared");
            let ctors = data
                .ctors
                .iter()
                .map(|c| Ctor {
                    name: c.name.clone(),
                    fields: c.fields.clone(),
                    field_sorts: c.field_sorts.clone(),
                    field_erased: c.field_erased.clone(),
                    result: c.result.clone(),
                    implicit: c.implicit.clone(),
                })
                .collect();
            check::admit_trusted_data_group(&mut b, vec![(ids[0], ctors)]).expect("defined");
            j += 1;
        } else {
            let def = &a.defs[i];
            assert_eq!(def.group.as_ref().map(|g| g.len()), Some(1));
            let id = check::admit_trusted_def(&mut b, &def.name, &def.ty, def.theorem, def.span)
                .expect("declared");
            assert_eq!(id, DefId(i));
            if def.fold {
                check::mark_folded(&mut b, id);
            }
            if def.instance {
                check::mark_instance(&mut b, id);
            }
            if def.opaque {
                check::mark_opaque(&mut b, id);
            }
            check::set_unfolding(&mut b, id, &def.unfolding);
            let body = (**def.body().expect("final")).clone();
            check::admit_trusted_group(&mut b, &[(id, body)]).expect("defined");
            if let Some(run) = def.own_run_body() {
                check::admit_trusted_run_body(&mut b, id, run).expect("run body");
            }
            i += 1;
        }
    }
    b
}

/// `double n = case n of Zero -> Zero; Succ m -> Succ (Succ (double m))`.
fn with_double(p: &mut Prelude) -> DefId {
    let nat = p.nat;
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let double = declare(&mut p.g, "double", ty);
    let body = lam(
        "n",
        case(
            0,
            nat,
            vec![
                (vec![], Term::Ctor(nat, 0, vec![])),
                (
                    vec!["m"],
                    Term::ctor(
                        nat,
                        1,
                        vec![Term::ctor(nat, 1, vec![app(Term::Def(double), [v(0)])])],
                    ),
                ),
            ],
        ),
    );
    check::define_def(&mut p.g, double, &body).expect("double");
    double
}

#[test]
fn a_trusted_copy_is_the_checked_environment() {
    let mut p = Prelude::new();
    with_double(&mut p);
    let a = &p.g;
    let b = trusted_copy(a);
    assert_eq!(a.defs.len(), b.defs.len());
    assert_eq!(a.datas.len(), b.datas.len());
    for (x, y) in a.defs.iter().zip(&b.defs) {
        assert_eq!(y.state(), State::Final);
        assert_eq!(x.arity, y.arity, "{}", x.name);
        assert_eq!(x.group, y.group, "{}", x.name);
        assert_eq!(x.path, y.path);
        assert_eq!(format!("{:?}", x.body()), format!("{:?}", y.body()));
        assert_eq!(
            x.admitted_metadata(),
            y.admitted_metadata(),
            "{}: transparency set, lift_leaf, recursive",
            x.name
        );
    }
    for (x, y) in a.datas.iter().zip(&b.datas) {
        assert_eq!(y.state(), State::Final);
        assert_eq!(x.group, y.group);
        assert_eq!(
            (x.defs_before, x.datas_before),
            (y.defs_before, y.datas_before)
        );
        for (c, d) in x.ctors.iter().zip(&y.ctors) {
            assert_eq!(format!("{:?}", c.fields), format!("{:?}", d.fields));
            assert_eq!(c.field_sorts, d.field_sorts);
            assert_eq!(c.field_erased, d.field_erased);
            assert_eq!(c.implicit, d.implicit);
        }
    }
    for i in 0..a.defs.len() {
        let id = DefId(i);
        assert_eq!(def_hash(a, id).unwrap(), def_hash(&b, id).unwrap());
    }
    for i in 0..a.datas.len() {
        let id = stitchwort_core::DataId(i);
        assert_eq!(data_hash(a, id).unwrap(), data_hash(&b, id).unwrap());
    }
}

/// The point of trusting: a body checking would refuse (it doesn't
/// terminate) is installed as given. This is why a cache entry is part of
/// the trusted base, and why `--no-cache` is the full check.
#[test]
fn trusted_admission_does_not_check() {
    let mut p = Prelude::new();
    let ty = arrow(p.nat_ty(), p.nat_ty());
    let looping = |f| lam("n", app(Term::Def(f), [v(0)]));
    let checked = declare(&mut p.g, "loop", ty.clone());
    assert_ne!(
        code(check::define_def(&mut p.g, checked, &looping(checked))),
        "ok"
    );
    let trusted = check::admit_trusted_def(&mut p.g, &"loop2".into(), &ty, false, span()).unwrap();
    check::admit_trusted_group(&mut p.g, &[(trusted, looping(trusted))]).unwrap();
    assert_eq!(p.g.def(trusted).state(), State::Final);
}

#[test]
fn trusted_admission_still_refuses_what_isnt_there() {
    let mut p = Prelude::new();
    let ty = arrow(p.nat_ty(), p.nat_ty());
    // A body naming another pending definition.
    let pending = declare(&mut p.g, "pending", ty.clone());
    let f = check::admit_trusted_def(&mut p.g, &"f".into(), &ty, false, span()).unwrap();
    let calls = lam("n", app(Term::Def(pending), [v(0)]));
    assert_eq!(
        code(check::admit_trusted_group(&mut p.g, &[(f, calls)])),
        "E-MALFORMED"
    );
    assert_eq!(p.g.def(f).state(), State::Failed);
    // A type naming a definition that doesn't exist.
    let unknown = arrow(p.nat_ty(), app(Term::Def(DefId(9999)), []));
    assert_eq!(
        code(check::admit_trusted_def(
            &mut p.g,
            &"g".into(),
            &unknown,
            false,
            span()
        )),
        "E-MALFORMED"
    );
    // A group already defined.
    let add = p.add;
    let body = (**p.g.def(add).body().unwrap()).clone();
    assert_eq!(
        code(check::admit_trusted_group(&mut p.g, &[(add, body)])),
        "E-MALFORMED"
    );
}

#[test]
fn a_trusted_constructor_of_the_wrong_shape_is_refused() {
    let mut p = Prelude::new();
    let ids = check::admit_trusted_data_decls(
        &mut p.g,
        vec![],
        Sort::Type(0),
        vec![DataDecl {
            name: "Box".into(),
            span: span(),
            record: false,
            indices: vec![],
        }],
    )
    .unwrap();
    // One field, but no sort or erasure flag for it.
    let ctor = Ctor {
        name: "MkBox".into(),
        fields: vec![("n".into(), p.nat_ty())],
        field_sorts: vec![],
        field_erased: vec![],
        result: vec![],
        implicit: vec![false],
    };
    assert_eq!(
        code(check::admit_trusted_data_group(
            &mut p.g,
            vec![(ids[0], vec![ctor])]
        )),
        "E-MALFORMED"
    );
    assert_eq!(p.g.data(ids[0]).state(), State::Failed);
}
