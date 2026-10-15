//! Admission: everything a declaration refers to must be finished
//! (docs/proposals/kernel-admission.md). These call the kernel directly, in
//! orders the elaborator never uses, since the kernel mustn't rely on the
//! elaborator's order.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, infer_closed};
use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::{DataId, DefId, Icit, Limits, Sort, Term};

fn code<T>(result: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    result.err().map_or("ok", |d| d.code)
}

fn define_def(p: &mut Prelude, id: DefId, body: Term) -> &'static str {
    code(check::define_def(&mut p.g, id, &body))
}

/// `Void : Prop`, with no constructors.
fn void(p: &mut Prelude) -> DataId {
    let void = data(&mut p.g, "Void", vec![], Sort::Prop);
    check::define_ctors(&mut p.g, void, vec![]).unwrap();
    void
}

fn nat_to_nat(nat: DataId) -> Term {
    arrow(Term::Data(nat, vec![]), Term::Data(nat, vec![]))
}

/// `f 0 = 0`, for a definition `f : Nat -> Nat`.
fn about(nat: DataId, f: DefId) -> Term {
    let zero = || Term::Ctor(nat, 0, vec![]);
    eq(None, app(Term::Def(f), [zero()]), zero())
}

#[test]
fn a_cycle_split_across_two_definitions_is_refused() {
    // f n = g n, then g n = f n: accepted one at a time, `f 0` would loop.
    let mut p = Prelude::new();
    let f = declare(&mut p.g, "f", nat_to_nat(p.nat));
    let g = declare(&mut p.g, "g", nat_to_nat(p.nat));
    let calls = |other| lam("n", app(Term::Def(other), [v(0)]));
    assert_eq!(define_def(&mut p, f, calls(g)), "E-MALFORMED");
    assert_eq!(define_def(&mut p, g, calls(f)), "E-FAILED-DEPENDENCY");
    // Neither unfolds, so this is stuck rather than looping.
    let (term, _) = infer_closed(&p.g, &app(Term::Def(f), [p.num(0)]), span()).unwrap();
    stitchwort_core::value::eval(&p.g, &[], &term).unwrap();
}

#[test]
fn a_data_type_without_its_constructors_yet_is_not_empty() {
    let mut p = Prelude::new();
    let void = void(&mut p);
    let d = data(&mut p.g, "D", vec![], Sort::Type(0));
    let d_to_void = arrow(Term::Data(d, vec![]), Term::Data(void, vec![]));
    // impossible : D -> Void, by an empty match. Its signature already
    // refers to `D`, which isn't finished.
    let r = check::declare_def(
        &mut p.g,
        &"impossible".into(),
        &d_to_void,
        false,
        false,
        span(),
    );
    assert_eq!(code(r), "E-MALFORMED");
    // The `case` rule refuses the empty match too, outside any declaration.
    let absurd = lam("x", case(0, d, vec![]));
    let annotated = Term::Ann(Rc::new(absurd.clone()), Rc::new(d_to_void.clone()));
    assert_eq!(code(infer_closed(&p.g, &annotated, span())), "E-MALFORMED");
    // Had it been accepted, `impossible MakeD` would prove `Void`.
    // Neighbour: an empty match on a final data type with no constructors.
    let void_to_nat = arrow(Term::Data(void, vec![]), p.nat_ty());
    let r = define(
        &mut p.g,
        "absurd",
        void_to_nat,
        lam("x", case(0, void, vec![])),
    );
    assert_eq!(r.err(), None);
    // And once `D` is final, `impossible` is just non-exhaustive.
    check::define_ctors(&mut p.g, d, vec![ctor("MakeD", vec![])]).unwrap();
    assert_eq!(
        define(&mut p.g, "impossible", d_to_void, absurd).err(),
        Some("E-NONEXHAUSTIVE")
    );
}

#[test]
fn a_failed_declaration_cannot_be_used() {
    let mut p = Prelude::new();
    // f n = Type: ill-typed, so `f` fails.
    let f = declare(&mut p.g, "f", nat_to_nat(p.nat));
    assert_eq!(define_def(&mut p, f, lam("n", ty())), "E-TYPE-MISMATCH");
    assert_eq!(def_hash(&p.g, f).unwrap(), None);

    // A body using it is still checked, but the result is failed.
    let g = declare(&mut p.g, "g", nat_to_nat(p.nat));
    assert_eq!(
        define_def(&mut p, g, lam("n", app(Term::Def(f), [v(0)]))),
        "E-FAILED-DEPENDENCY"
    );
    assert_eq!(def_hash(&p.g, g).unwrap(), None);
    // Its own errors come first.
    let h = declare(&mut p.g, "h", nat_to_nat(p.nat));
    assert_eq!(
        define_def(&mut p, h, lam("n", app(Term::Def(f), [ty()]))),
        "E-TYPE-MISMATCH"
    );
    // A signature using it is declared, so later declarations can name it,
    // but it can never be defined.
    let f0 = app(Term::Def(f), [p.num(0)]);
    let reflexive = eq(None, f0.clone(), f0);
    let t = check::declare_def(&mut p.g, &"t".into(), &reflexive, true, false, span());
    let t = t.expect("declared");
    assert_eq!(define_def(&mut p, t, Term::Refl), "E-FAILED-DEPENDENCY");
    assert_eq!(def_hash(&p.g, t).unwrap(), None);
    // And neither can anything using that.
    let r = define(&mut p.g, "u", reflexive, Term::Def(t));
    assert_eq!(r.err(), Some("E-FAILED-DEPENDENCY"));
    // Data types too.
    let e = data(&mut p.g, "E", vec![], Sort::Type(0));
    let fields = vec![ctor("MkE", vec![("p", about(p.nat, f))])];
    assert_eq!(
        code(check::define_ctors(&mut p.g, e, fields)),
        "E-FAILED-DEPENDENCY"
    );
    assert_eq!(data_hash(&p.g, e).unwrap(), None);
    let e_to_e = arrow(Term::Data(e, vec![]), Term::Data(e, vec![]));
    let r = define(&mut p.g, "idE", e_to_e, lam("x", v(0)));
    assert_eq!(r.err(), Some("E-FAILED-DEPENDENCY"));
}

#[test]
fn a_definition_is_defined_only_once() {
    let mut p = Prelude::new();
    let id = lam("n", v(0));
    let f = define(&mut p.g, "f", nat_to_nat(p.nat), id.clone()).unwrap();
    let hash = def_hash(&p.g, f).unwrap();
    let zero = lam("n", p.num(0));
    assert_eq!(define_def(&mut p, f, zero), "E-MALFORMED");
    assert_eq!(def_hash(&p.g, f).unwrap(), hash);
    // A failed one isn't retried either.
    let g = declare(&mut p.g, "g", nat_to_nat(p.nat));
    assert_eq!(define_def(&mut p, g, lam("n", ty())), "E-TYPE-MISMATCH");
    assert_eq!(define_def(&mut p, g, id), "E-MALFORMED");
    assert_eq!(def_hash(&p.g, g).unwrap(), None);
}

#[test]
fn a_signature_cannot_refer_to_a_pending_declaration() {
    let mut p = Prelude::new();
    let f = declare(&mut p.g, "f", nat_to_nat(p.nat));
    let t = check::declare_def(&mut p.g, &"t".into(), &about(p.nat, f), true, false, span());
    assert_eq!(code(t), "E-MALFORMED");
    // Nor to a data type without its constructors.
    let d = data(&mut p.g, "D", vec![], Sort::Type(0));
    let ty = arrow(Term::Data(d, vec![]), p.nat_ty());
    let r = check::declare_def(&mut p.g, &"u".into(), &ty, false, false, span());
    assert_eq!(code(r), "E-MALFORMED");
    // Nor can data parameters.
    let params = vec![("x".into(), about(p.nat, f))];
    let r = check::declare_data(&mut p.g, "E".into(), params, Sort::Type(0), span());
    assert_eq!(code(r), "E-MALFORMED");
    let params = vec![("x".into(), Term::Data(d, vec![]))];
    let r = check::declare_data(&mut p.g, "E".into(), params, Sort::Type(0), span());
    assert_eq!(code(r), "E-MALFORMED");
    // Neighbour: once both are final, all of these are fine.
    check::define_def(&mut p.g, f, &lam("n", v(0))).unwrap();
    check::define_ctors(&mut p.g, d, vec![]).unwrap();
    check::declare_def(&mut p.g, &"t".into(), &about(p.nat, f), true, false, span()).unwrap();
    check::declare_def(&mut p.g, &"u".into(), &ty, false, false, span()).unwrap();
}

#[test]
fn a_constructor_field_cannot_refer_to_a_pending_declaration() {
    let mut p = Prelude::new();
    // `f` and `E` are declared before `D`, so they aren't "declared later".
    let f = declare(&mut p.g, "f", nat_to_nat(p.nat));
    let e = data(&mut p.g, "E", vec![], Sort::Type(0));
    let d = data(&mut p.g, "D", vec![], Sort::Type(0));
    let field = |t: Term| vec![ctor("MkD", vec![("x", t)])];
    let r = check::define_ctors(&mut p.g, d, field(about(p.nat, f)));
    assert_eq!(code(r), "E-MALFORMED");
    let d2 = data(&mut p.g, "D2", vec![], Sort::Type(0));
    let r = check::define_ctors(&mut p.g, d2, field(Term::Data(e, vec![])));
    assert_eq!(code(r), "E-MALFORMED");
    // Nor to its own constructors.
    let d3 = data(&mut p.g, "D3", vec![], Sort::Type(0));
    let mk = Term::Ctor(d3, 0, vec![]);
    let r = check::define_ctors(&mut p.g, d3, field(eq(None, mk.clone(), mk)));
    assert_eq!(code(r), "E-MALFORMED");
    // A refused data type is failed: it can't be defined again or used.
    let nat = p.nat_ty();
    let r = check::define_ctors(&mut p.g, d, field(nat));
    assert_eq!(code(r), "E-MALFORMED");
    let d_to_d = arrow(Term::Data(d, vec![]), Term::Data(d, vec![]));
    let r = define(&mut p.g, "idD", d_to_d, lam("x", v(0)));
    assert_eq!(r.err(), Some("E-FAILED-DEPENDENCY"));
    // Neighbour: its own type, recursively, is fine.
    let d4 = data(&mut p.g, "D4", vec![], Sort::Type(0));
    let r = check::define_ctors(&mut p.g, d4, field(Term::Data(d4, vec![])));
    assert_eq!(code(r), "ok");
}

#[test]
fn a_proof_cannot_refer_to_a_pending_declaration() {
    let mut p = Prelude::new();
    let f = declare(&mut p.g, "f", nat_to_nat(p.nat));
    // (\x -> rfl : Nat -> 0 = 0) (f 0)
    let zero_is_zero = eq(None, p.num(0), p.num(0));
    let constant = Term::Ann(
        Rc::new(lam("x", Term::Refl)),
        Rc::new(arrow(p.nat_ty(), zero_is_zero.clone())),
    );
    let proof = app(constant, [app(Term::Def(f), [p.num(0)])]);
    let t = check::declare_def(&mut p.g, &"t".into(), &zero_is_zero, true, false, span());
    let t = t.unwrap();
    assert_eq!(define_def(&mut p, t, proof.clone()), "E-MALFORMED");
    // Neighbour: once `f` is final.
    check::define_def(&mut p.g, f, &lam("n", v(0))).unwrap();
    let t2 = check::declare_def(&mut p.g, &"t2".into(), &zero_is_zero, true, false, span());
    assert_eq!(define_def(&mut p, t2.unwrap(), proof), "ok");
}

#[test]
fn a_validator_cannot_refer_to_a_pending_declaration() {
    let mut p = Prelude::new();
    let void = void(&mut p);
    let decidable = data(&mut p.g, "Decidable", vec![("p", prop())], Sort::Type(0));
    check::define_ctors(
        &mut p.g,
        decidable,
        vec![
            ctor("Yes", vec![("proof", v(0))]),
            ctor(
                "No",
                vec![("refutation", arrow(v(0), Term::Data(void, vec![])))],
            ),
        ],
    )
    .unwrap();
    // f : (n : Nat) -> [auto ok : n = n] -> Nat
    let ty = pi(
        "n",
        p.nat_ty(),
        Term::Pi(
            "ok".into(),
            Icit::Auto,
            Rc::new(eq(None, v(0), v(0))),
            Rc::new(p.nat_ty()),
        ),
    );
    let body = lam("n", Term::Lam("ok".into(), Icit::Auto, Rc::new(v(1))));
    let f = define(&mut p.g, "f", ty, body).unwrap();
    // dec : (n : Nat) -> Decidable (n = n), not yet defined.
    let dec_ty = pi(
        "n",
        p.nat_ty(),
        Term::data(decidable, vec![eq(None, v(0), v(0))]),
    );
    let dec = declare(&mut p.g, "dec", dec_ty);
    let decision = app(Term::Def(dec), [v(0)]);
    let r = check::add_validator(&mut p.g, f, 1, decidable, &decision);
    assert_eq!(code(r), "E-MALFORMED");
    // Neighbour: once `dec` is final.
    let yes = lam("n", Term::ctor(decidable, 0, vec![Term::Refl]));
    check::define_def(&mut p.g, dec, &yes).unwrap();
    let r = check::add_validator(&mut p.g, f, 1, decidable, &decision);
    assert_eq!(code(r), "ok");
}

#[test]
fn builtins_must_be_final() {
    // `Decidable`'s `No` mentions `Void` before `Void`'s constructors are in:
    // registering it would let a native `No` rely on `Void` being empty.
    let mut p = Prelude::new();
    let void = data(&mut p.g, "Void", vec![], Sort::Prop);
    let decidable = data(&mut p.g, "Decidable", vec![("p", prop())], Sort::Type(0));
    let r = check::define_ctors(
        &mut p.g,
        decidable,
        vec![
            ctor("Yes", vec![("proof", v(0))]),
            ctor(
                "No",
                vec![("refutation", arrow(v(0), Term::Data(void, vec![])))],
            ),
        ],
    );
    assert_eq!(code(r), "E-MALFORMED");
    let r = stitchwort_core::native::register_decidable(&mut p.g, decidable);
    assert_eq!(code(r), "E-BUILTIN");
}

#[test]
fn running_out_of_resources_leaves_a_definition_failed() {
    let mut p = Prelude::new();
    // big : 30 + 30 = 60, by computation.
    let statement = eq(None, p.plus(p.num(30), p.num(30)), p.num(60));
    let big = check::declare_def(&mut p.g, &"big".into(), &statement, true, false, span());
    let big = big.unwrap();
    let r = {
        let tiny = Limits {
            work: 10,
            ..Limits::default()
        };
        let saved = p.g.budget.start(tiny);
        let r = check::define_def(&mut p.g, big, &Term::Refl);
        p.g.budget.restore(saved);
        r
    };
    assert_eq!(code(r), "E-RESOURCE");
    assert_eq!(def_hash(&p.g, big).unwrap(), None);
    // With enough resources it would check, but it's failed now.
    assert_eq!(define_def(&mut p, big, Term::Refl), "E-MALFORMED");
}

#[test]
fn references_to_declarations_that_do_not_exist_are_refused() {
    // Declaration ids are plain numbers, so a buggy elaborator could make
    // one up. Nothing is added when it does.
    let mut p = Prelude::new();
    let (defs, datas) = (p.g.defs.len(), p.g.datas.len());
    let missing_def = Term::Def(DefId(1000));
    let missing_data = Term::Data(DataId(1000), vec![]);
    for ty in [arrow(missing_data.clone(), p.nat_ty()), missing_def.clone()] {
        let r = check::declare_def(&mut p.g, &"f".into(), &ty, false, false, span());
        assert_eq!(code(r), "E-MALFORMED");
    }
    let r = check::declare_data(
        &mut p.g,
        "E".into(),
        vec![("x".into(), missing_data)],
        Sort::Type(0),
        span(),
    );
    assert_eq!(code(r), "E-MALFORMED");
    assert_eq!((p.g.defs.len(), p.g.datas.len()), (defs, datas));
    let f = declare(&mut p.g, "f", nat_to_nat(p.nat));
    let body = lam("n", app(missing_def, [v(0)]));
    assert_eq!(define_def(&mut p, f, body), "E-MALFORMED");
    // Defining something that was never declared.
    assert_eq!(
        define_def(&mut p, DefId(1000), lam("n", v(0))),
        "E-MALFORMED"
    );
    let r = check::define_ctors(&mut p.g, DataId(1000), vec![]);
    assert_eq!(code(r), "E-MALFORMED");
}
