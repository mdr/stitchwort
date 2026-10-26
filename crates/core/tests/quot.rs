//! Kernel tests for quotients (docs/proposals/map-equality.md §7), on
//! hand-built core terms, so the elaborator isn't trusted for any of them.
//!
//! The rejection tests come first (§7.6, stage 1.1): each says which
//! forbidden behaviour it covers (R1–R3, R5–R9, R11–R14), the check or rule
//! that refuses it (C1–C6, §7.1), and asserts the error code and a piece of
//! the message, so a refusal only counts if it's for the stated reason. R4 and
//! R10 are elaborator tests (`examples/`), not kernel ones. Then the accepted
//! counterparts, and the computation tests of stage 1.2 (A1, A4, A8).
//!
//! The canonical object is the `Bool`-by-`True` quotient, which identifies
//! `False` and `True`: anything that reads a representative back out of
//! `same: Quot.mk False = Quot.mk True` proves `False = True`.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, infer_closed};
use stitchwort_core::value::{conv, eval, quote};
use stitchwort_core::{DataId, DefId, Globals, QuotForm, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;

use QuotForm::{Ind, Lift, Mk, Sound, Type as QuotType};

fn q(form: QuotForm, args: Vec<Term>) -> Term {
    Term::quot(form, args)
}

/// The prelude plus `Bool`, the proposition `Unit` (proved by `Trivial`),
/// `AllTrue x y := Unit`, `BoolEq x y := x = y`, and `Pair`.
struct Fix {
    p: Prelude,
    bool_: DataId,
    unit: DataId,
    all_true: DefId,
    bool_eq: DefId,
    pair: DataId,
}

impl Fix {
    fn new() -> Fix {
        let mut p = Prelude::new();
        let g = &mut p.g;
        let bool_ = data(g, "Bool", vec![], Sort::Type(0));
        check::define_ctors(g, bool_, vec![ctor("False", vec![]), ctor("True", vec![])])
            .expect("Bool");
        let unit = data(g, "Unit", vec![], Sort::Prop);
        check::define_ctors(g, unit, vec![ctor("Trivial", vec![])]).expect("Unit");
        let bool_ty = Term::Data(bool_, vec![]);
        let rel_ty = arrow(bool_ty.clone(), arrow(bool_ty.clone(), prop()));
        let all_true = define(
            g,
            "AllTrue",
            rel_ty.clone(),
            lam("x", lam("y", Term::Data(unit, vec![]))),
        )
        .expect("AllTrue");
        let bool_eq = define(
            g,
            "BoolEq",
            rel_ty,
            lam("x", lam("y", eq(Some(bool_ty), v(1), v(0)))),
        )
        .expect("BoolEq");
        let pair = data(g, "Pair", vec![("a", ty()), ("b", ty())], Sort::Type(0));
        check::define_ctors(
            g,
            pair,
            vec![ctor("MkPair", vec![("fst", v(1)), ("snd", v(1))])],
        )
        .expect("Pair");
        Fix {
            p,
            bool_,
            unit,
            all_true,
            bool_eq,
            pair,
        }
    }

    fn g(&mut self) -> &mut Globals {
        &mut self.p.g
    }

    fn bool_ty(&self) -> Term {
        Term::Data(self.bool_, vec![])
    }

    fn ff(&self) -> Term {
        Term::Ctor(self.bool_, 0, vec![])
    }

    fn tt(&self) -> Term {
        Term::Ctor(self.bool_, 1, vec![])
    }

    fn unit_ty(&self) -> Term {
        Term::Data(self.unit, vec![])
    }

    fn trivial(&self) -> Term {
        Term::Ctor(self.unit, 0, vec![])
    }

    fn all_true(&self) -> Term {
        Term::Def(self.all_true)
    }

    fn bool_eq(&self) -> Term {
        Term::Def(self.bool_eq)
    }

    /// `Q := Quot Bool AllTrue`. Closed, so it can go under any binder.
    fn q_ty(&self) -> Term {
        q(QuotType, vec![self.bool_ty(), self.all_true()])
    }

    /// `Quot Bool BoolEq`.
    fn qe_ty(&self) -> Term {
        q(QuotType, vec![self.bool_ty(), self.bool_eq()])
    }

    /// `Quot.mk [Bool] [AllTrue] b`.
    fn mk(&self, b: Term) -> Term {
        q(Mk, vec![self.bool_ty(), self.all_true(), b])
    }

    /// `Quot.mk [Bool] [BoolEq] b`.
    fn mk_eq(&self, b: Term) -> Term {
        q(Mk, vec![self.bool_ty(), self.bool_eq(), b])
    }

    fn nat_ty(&self) -> Term {
        self.p.nat_ty()
    }

    fn num(&self, n: usize) -> Term {
        self.p.num(n)
    }

    /// `x y => Unit`, a relation on any carrier.
    fn everything(&self) -> Term {
        lam("x", lam("y", self.unit_ty()))
    }

    /// `0 = 0`, a proposition.
    fn zero_is_zero(&self) -> Term {
        eq(Some(self.nat_ty()), self.num(0), self.num(0))
    }
}

/// Declares and defines `name : ty = body`, returning the kernel's
/// diagnostic if it refuses either.
fn try_define(g: &mut Globals, name: &str, ty: Term, body: Term) -> Result<DefId, Diagnostic> {
    let id = check::declare_def(g, &name.into(), &ty, false, false, span())?;
    check::define_def(g, id, &body)?;
    Ok(id)
}

/// Asserts that `result` is a refusal with `code` whose text (message,
/// labels and notes) contains `reason`.
#[track_caller]
fn refused<T: std::fmt::Debug>(result: Result<T, Diagnostic>, code: &str, reason: &str) {
    match result {
        Ok(t) => panic!("accepted ({t:?}), but expected {code} ({reason})"),
        Err(d) => {
            let text = format!("{d:?}");
            assert_eq!(d.code, code, "wrong code: {text}");
            assert!(
                text.contains(reason),
                "refused with {code}, but not for the stated reason ({reason:?}): {text}"
            );
        }
    }
}

fn infer(g: &Globals, term: &Term) -> Result<(Term, Value), Diagnostic> {
    infer_closed(g, term, span())
}

// R1, R2: no pattern matching on a quotient, so no projection back to the
// representative and no constructor injectivity or no-confusion. `case` needs
// a variable of a data type (the existing rule, §7.5); `Quot A R` isn't one.

/// R1: the projection `Q -> Bool` that would turn `same` into `False = True`
/// is refused at its `case`.
#[test]
fn r1_a_projection_by_case_is_refused() {
    let mut f = Fix::new();
    let ty = arrow(f.q_ty(), f.bool_ty());
    let body = lam(
        "q",
        case(0, f.bool_, vec![(vec![], f.ff()), (vec![], f.tt())]),
    );
    refused(
        try_define(f.g(), "rep", ty, body),
        "E-TYPE-MISMATCH",
        "this matches on a `Bool`, but `q` has type `Quot Bool AllTrue`",
    );
}

/// R1, no-confusion: a `case` on the quotient inside `J`'s motive, to send
/// `Quot.mk False` and `Quot.mk True` to different types, is refused (a
/// `case` only at the top of a definition).
#[test]
fn r1_no_confusion_through_j_is_refused() {
    let mut f = Fix::new();
    // noConfusion (e: Quot.mk False = Quot.mk True): Unit :=
    //   J (y p => case y of …) Trivial e
    let eq_ty = eq(Some(f.q_ty()), f.mk(f.ff()), f.mk(f.tt()));
    let motive = lam(
        "y",
        lam(
            "p",
            case(
                1,
                f.bool_,
                vec![(vec![], f.unit_ty()), (vec![], f.bool_ty())],
            ),
        ),
    );
    let body = lam(
        "e",
        Term::J(Rc::new(motive), Rc::new(f.trivial()), Rc::new(v(0))),
    );
    refused(
        {
            let ty = arrow(eq_ty, f.unit_ty());
            try_define(f.g(), "noConfusion", ty, body)
        },
        "E-MALFORMED",
        "`case` may only appear at the top of a definition",
    );
}

/// R2: the core `case` a `match q with | Quot.mk b => b` would need.
#[test]
fn r2_a_case_on_a_quotient_variable_is_refused() {
    let mut f = Fix::new();
    // rep (n: Nat) (q: Q): Bool, matching on q as if it were a `Bool`.
    let ty = arrow(f.nat_ty(), arrow(f.q_ty(), f.bool_ty()));
    let body = lam(
        "n",
        lam(
            "q",
            case(0, f.bool_, vec![(vec![], f.ff()), (vec![], f.tt())]),
        ),
    );
    refused(
        try_define(f.g(), "rep", ty, body),
        "E-TYPE-MISMATCH",
        "this matches on a `Bool`",
    );
}

// R3, R12: index unification never decomposes `Quot.mk a = Quot.mk b` (it's
// not a constructor), and never calls it a conflict: it's stuck.

/// `At: Q -> Type` with `AtF: At (Quot.mk False)` and `AtT: At (Quot.mk True)`.
fn at_family(f: &mut Fix) -> DataId {
    let q_ty = f.q_ty();
    let at = family(f.g(), "At", vec![], vec![("q", q_ty)], Sort::Type(0));
    let ctors = vec![
        ictor("AtF", vec![], vec![f.mk(f.ff())]),
        ictor("AtT", vec![], vec![f.mk(f.tt())]),
    ];
    check::define_ctors(f.g(), at, ctors).expect("At");
    at
}

/// R3: covering only `AtF` would treat `Quot.mk True = Quot.mk False` as
/// impossible, i.e. `Quot.mk` as injective and disjoint: stuck instead.
#[test]
fn r3_an_index_quot_mk_is_not_decomposed() {
    let mut f = Fix::new();
    let at = at_family(&mut f);
    let ty = arrow(Term::data(at, vec![f.mk(f.ff())]), f.nat_ty());
    let only_f = lam(
        "a",
        icase(0, at, vec![(vec![], Some(f.num(0))), (vec![], None)]),
    );
    refused(
        try_define(f.g(), "only", ty.clone(), only_f),
        "E-INDEX-STUCK",
        "AtT",
    );
}

/// R3: with both branches, the `AtT` branch would get `Quot.mk True =
/// Quot.mk False` refined into something usable; it's stuck instead.
#[test]
fn r3_a_branch_never_learns_from_a_quotient_index() {
    let mut f = Fix::new();
    let at = at_family(&mut f);
    let ty = arrow(Term::data(at, vec![f.mk(f.ff())]), f.nat_ty());
    let both = lam(
        "a",
        icase(
            0,
            at,
            vec![(vec![], Some(f.num(0))), (vec![], Some(f.num(1)))],
        ),
    );
    refused(try_define(f.g(), "both", ty, both), "E-INDEX-STUCK", "AtT");
}

/// R12: a quotient index nested in a pair is decomposed at the pair, and the
/// inner equation at type `Q` is stuck.
#[test]
fn r12_a_quotient_index_inside_a_pair_is_stuck() {
    let mut f = Fix::new();
    let pair_ty = Term::data(f.pair, vec![f.q_ty(), f.nat_ty()]);
    let at = family(f.g(), "AtP", vec![], vec![("p", pair_ty)], Sort::Type(0));
    let pair = |f: &Fix, b: Term| Term::ctor(f.pair, 0, vec![f.mk(b), f.num(0)]);
    let ctors = vec![
        ictor("AtF", vec![], vec![pair(&f, f.ff())]),
        ictor("AtT", vec![], vec![pair(&f, f.tt())]),
    ];
    check::define_ctors(f.g(), at, ctors).expect("AtP");
    let ty = arrow(Term::data(at, vec![pair(&f, f.ff())]), f.nat_ty());
    let only_f = lam(
        "a",
        icase(0, at, vec![(vec![], Some(f.num(0))), (vec![], None)]),
    );
    refused(
        try_define(f.g(), "only", ty, only_f),
        "E-INDEX-STUCK",
        "AtT",
    );
}

/// R12: likewise inside a `List Q`.
#[test]
fn r12_a_quotient_index_inside_a_list_is_stuck() {
    let mut f = Fix::new();
    let list = f.p.list;
    let list_ty = Term::data(list, vec![f.q_ty()]);
    let at = family(f.g(), "AtL", vec![], vec![("l", list_ty)], Sort::Type(0));
    let one = |f: &Fix, b: Term| Term::ctor(list, 1, vec![f.mk(b), Term::Ctor(list, 0, vec![])]);
    let ctors = vec![
        ictor("AtF", vec![], vec![one(&f, f.ff())]),
        ictor("AtT", vec![], vec![one(&f, f.tt())]),
    ];
    check::define_ctors(f.g(), at, ctors).expect("AtL");
    let ty = arrow(Term::data(at, vec![one(&f, f.ff())]), f.nat_ty());
    let only_f = lam(
        "a",
        icase(0, at, vec![(vec![], Some(f.num(0))), (vec![], None)]),
    );
    refused(
        try_define(f.g(), "only", ty, only_f),
        "E-INDEX-STUCK",
        "AtT",
    );
}

/// R12: likewise inside a record `{ q: Q, n: Nat }`.
#[test]
fn r12_a_quotient_index_inside_a_record_is_stuck() {
    let mut f = Fix::new();
    let qn = data(f.g(), "QN", vec![], Sort::Type(0));
    let fields = vec![("q", f.q_ty()), ("n", f.nat_ty())];
    check::define_ctors(f.g(), qn, vec![ctor("MkQN", fields)]).expect("QN");
    let at = family(
        f.g(),
        "AtR",
        vec![],
        vec![("r", Term::data(qn, vec![]))],
        Sort::Type(0),
    );
    let rec = |f: &Fix, b: Term| Term::ctor(qn, 0, vec![f.mk(b), f.num(0)]);
    let ctors = vec![
        ictor("AtF", vec![], vec![rec(&f, f.ff())]),
        ictor("AtT", vec![], vec![rec(&f, f.tt())]),
    ];
    check::define_ctors(f.g(), at, ctors).expect("AtR");
    let ty = arrow(Term::data(at, vec![rec(&f, f.ff())]), f.nat_ty());
    let only_f = lam(
        "a",
        icase(0, at, vec![(vec![], Some(f.num(0))), (vec![], None)]),
    );
    refused(
        try_define(f.g(), "only", ty, only_f),
        "E-INDEX-STUCK",
        "AtT",
    );
}

// R5, R11, C6: the only way out of a quotient into data is `Quot.lift`, with
// a proof that the function respects the relation, for the form's own
// function and relation.

/// R5: the identity lift on the all-related quotient needs `(x y: Bool) ->
/// AllTrue x y -> x = y`, which is unprovable; passing the relation's proof
/// instead is a type mismatch.
#[test]
fn r5_projection_by_lift_needs_an_unprovable_respects_proof() {
    let mut f = Fix::new();
    let ty = arrow(f.q_ty(), f.bool_ty());
    let lift = |f: &Fix, h: Term| {
        lam(
            "q",
            q(
                Lift,
                vec![
                    f.bool_ty(),
                    f.all_true(),
                    f.bool_ty(),
                    lam("b", v(0)),
                    h,
                    v(0),
                ],
            ),
        )
    };
    let body = lift(&f, lam("x", lam("y", lam("r", v(0)))));
    refused(
        try_define(f.g(), "unwrap", ty.clone(), body),
        "E-TYPE-MISMATCH",
        "expected `x = y`, but this has type `AllTrue x y`",
    );
    // And `rfl` can't prove it either.
    let body = lift(&f, lam("x", lam("y", lam("r", Term::Refl))));
    refused(
        try_define(f.g(), "unwrap2", ty, body),
        "E-REFL",
        "`x` and `y` aren't equal",
    );
}

/// R11 (C4): an identity lift justified for `Bool` equality, applied to the
/// all-related quotient, would extract the representative. `q`'s type must be
/// the lift's own `Quot A R`, relation included.
#[test]
fn r11_a_lift_for_another_relation_is_refused() {
    let mut f = Fix::new();
    let ty = arrow(f.q_ty(), f.bool_ty());
    let body = lam(
        "q",
        q(
            Lift,
            vec![
                f.bool_ty(),
                f.bool_eq(),
                f.bool_ty(),
                lam("b", v(0)),
                lam("x", lam("y", lam("h", v(0)))),
                v(0),
            ],
        ),
    );
    refused(
        try_define(f.g(), "unwrap", ty, body),
        "E-TYPE-MISMATCH",
        "expected `Quot Bool BoolEq`, but this has type `Quot Bool AllTrue`",
    );
}

/// C6: the respects proof must be about the lift's own function: one proved
/// for a constant function doesn't do for the identity.
#[test]
fn c6_a_respects_proof_for_another_function_is_refused() {
    let mut f = Fix::new();
    let bool_ty = f.bool_ty();
    let tt = f.tt();
    let const_true = define(
        f.g(),
        "constTrue",
        arrow(bool_ty.clone(), bool_ty),
        lam("b", tt),
    )
    .expect("constTrue");
    // respConst: (x y: Bool) -> AllTrue x y -> constTrue x = constTrue y
    let resp_ty = pi(
        "x",
        f.bool_ty(),
        pi(
            "y",
            f.bool_ty(),
            arrow(
                app(f.all_true(), [v(1), v(0)]),
                eq(
                    Some(f.bool_ty()),
                    app(Term::Def(const_true), [v(1)]),
                    app(Term::Def(const_true), [v(0)]),
                ),
            ),
        ),
    );
    let resp = define(
        f.g(),
        "respConst",
        resp_ty,
        lam("x", lam("y", lam("r", Term::Refl))),
    )
    .expect("respConst");
    let term = q(
        Lift,
        vec![
            f.bool_ty(),
            f.all_true(),
            f.bool_ty(),
            lam("b", v(0)),
            Term::Def(resp),
            f.mk(f.ff()),
        ],
    );
    refused(
        infer(&f.p.g, &term),
        "E-TYPE-MISMATCH",
        "expected `(x: Bool) → (y: Bool) → Unit → x = y`, but this has type `Bool → Bool → Unit → True = True`",
    );
}

// R6, C5: `Quot.ind` only proves propositions.

/// R6: `Quot.ind` into data would be dependent elimination without a
/// respects proof.
#[test]
fn r6_ind_into_data_is_refused() {
    let mut f = Fix::new();
    let ty = arrow(f.q_ty(), f.bool_ty());
    let body = lam(
        "q",
        q(
            Ind,
            vec![
                f.bool_ty(),
                f.all_true(),
                lam("_", f.bool_ty()),
                lam("b", v(0)),
                v(0),
            ],
        ),
    );
    refused(
        try_define(f.g(), "unwrap", ty, body),
        "E-UNIVERSE",
        "expected something of type `Prop`, but this has type `Type`",
    );
}

/// C5: a motive returning `Type` is refused the same way.
#[test]
fn c5_ind_with_a_motive_into_type_is_refused() {
    let f = Fix::new();
    let term = q(
        Ind,
        vec![
            f.bool_ty(),
            f.all_true(),
            lam("_", ty()),
            lam("b", f.nat_ty()),
            f.mk(f.ff()),
        ],
    );
    refused(
        infer(&f.p.g, &term),
        "E-UNIVERSE",
        "expected something of type `Prop`, but this has type `Type 1`",
    );
}

/// C5: `lift`'s result `B` must be a type.
#[test]
fn c5_lift_into_a_non_type_is_refused() {
    let f = Fix::new();
    let term = q(
        Lift,
        vec![
            f.bool_ty(),
            f.all_true(),
            f.ff(),
            lam("b", v(0)),
            lam("x", lam("y", lam("r", Term::Refl))),
            f.mk(f.ff()),
        ],
    );
    refused(infer(&f.p.g, &term), "E-NOT-A-TYPE", "expected a type");
}

// R7, R8: no computation or conversion beyond the one rule.

/// R7: `Quot.ind` has no computation rule (§7.3): with one, it would prove
/// that any two proofs of a proposition are equal.
#[test]
fn r7_ind_doesnt_compute() {
    let mut f = Fix::new();
    let unit_ty = f.unit_ty();
    let trivial = f.trivial();
    let h_ty = arrow(f.bool_ty(), unit_ty);
    let h = define(f.g(), "h", h_ty, lam("b", trivial)).expect("h");
    let ind = q(
        Ind,
        vec![
            f.bool_ty(),
            f.all_true(),
            lam("_", f.unit_ty()),
            Term::Def(h),
            f.mk(f.ff()),
        ],
    );
    let statement = eq(Some(f.unit_ty()), ind, app(Term::Def(h), [f.ff()]));
    refused(
        try_define(f.g(), "computes", statement, Term::Refl),
        "E-REFL",
        "`rfl` can't prove this",
    );
}

/// R8: conversion is structural: related representatives aren't
/// convertible, so `rfl` can't prove `same`.
#[test]
fn r8_related_representatives_arent_convertible() {
    let mut f = Fix::new();
    let statement = eq(Some(f.q_ty()), f.mk(f.ff()), f.mk(f.tt()));
    refused(
        try_define(f.g(), "same", statement, Term::Refl),
        "E-REFL",
        "`Quot.mk False` and `Quot.mk True` aren't equal",
    );
}

// R9, C2, C3: carriers are types, relations are into `Prop`.

/// R9: a quotient of a proposition's proofs.
#[test]
fn r9_a_quotient_of_a_proposition_is_refused() {
    let f = Fix::new();
    let term = q(QuotType, vec![f.zero_is_zero(), f.everything()]);
    refused(
        infer(&f.p.g, &term),
        "E-UNIVERSE",
        "the carrier of a quotient must be a type in `Type`, but `0 = 0` is a proposition",
    );
}

/// C2 on `Quot.mk`, `Quot.sound`, `Quot.lift` and `Quot.ind` themselves,
/// with no `Quot A R` type expression ever checked.
#[test]
fn c2_every_form_checks_its_carrier() {
    let f = Fix::new();
    let zz = || f.zero_is_zero();
    let terms = [
        q(Mk, vec![zz(), f.everything(), Term::Refl]),
        q(
            Sound,
            vec![zz(), f.everything(), Term::Refl, Term::Refl, f.trivial()],
        ),
        q(
            Lift,
            vec![
                zz(),
                f.everything(),
                f.nat_ty(),
                lam("p", f.num(0)),
                lam("x", lam("y", lam("r", Term::Refl))),
                q(Mk, vec![zz(), f.everything(), Term::Refl]),
            ],
        ),
        q(
            Ind,
            vec![
                zz(),
                f.everything(),
                lam("_", f.unit_ty()),
                lam("p", f.trivial()),
                q(Mk, vec![zz(), f.everything(), Term::Refl]),
            ],
        ),
    ];
    for term in terms {
        refused(
            infer(&f.p.g, &term),
            "E-UNIVERSE",
            "the carrier of a quotient must be a type in `Type`, but `0 = 0` is a proposition",
        );
    }
}

/// C3: a `Bool`-valued relation.
#[test]
fn c3_a_bool_valued_relation_is_refused() {
    let mut f = Fix::new();
    let term = q(QuotType, vec![f.bool_ty(), lam("x", lam("y", f.tt()))]);
    refused(
        infer(&f.p.g, &term),
        "E-TYPE-MISMATCH",
        "`True` builds a `Bool`, but the expected type is `Prop`",
    );
    // A `Bool`-valued function given by name.
    let bool_ty = f.bool_ty();
    let tt = f.tt();
    let beq = define(
        f.g(),
        "beq",
        arrow(bool_ty.clone(), arrow(bool_ty.clone(), bool_ty)),
        lam("x", lam("y", tt)),
    )
    .expect("beq");
    let term = q(QuotType, vec![f.bool_ty(), Term::Def(beq)]);
    refused(
        infer(&f.p.g, &term),
        "E-TYPE-MISMATCH",
        "expected `Bool → Bool → Prop`, but this has type `Bool → Bool → Bool`",
    );
}

/// C3: a `Type`-valued relation.
#[test]
fn c3_a_type_valued_relation_is_refused() {
    let f = Fix::new();
    let term = q(QuotType, vec![f.bool_ty(), lam("x", lam("y", f.nat_ty()))]);
    refused(
        infer(&f.p.g, &term),
        "E-UNIVERSE",
        "expected something of type `Prop`, but this has type `Type`",
    );
}

// C4: `sound` and `ind` use the form's own relation.

/// C4 on `Quot.sound`: a proof of another relation doesn't identify.
#[test]
fn c4_sound_with_a_proof_of_another_relation_is_refused() {
    let mut f = Fix::new();
    // bad (r: AllTrue False False): Quot.mk [BoolEq] False = Quot.mk [BoolEq] False
    let ty = pi(
        "r",
        app(f.all_true(), [f.ff(), f.ff()]),
        eq(Some(f.qe_ty()), f.mk_eq(f.ff()), f.mk_eq(f.ff())),
    );
    let body = lam(
        "r",
        q(Sound, vec![f.bool_ty(), f.bool_eq(), f.ff(), f.ff(), v(0)]),
    );
    refused(
        try_define(f.g(), "bad", ty, body),
        "E-TYPE-MISMATCH",
        "expected `False = False`, but this has type `Unit`",
    );
}

/// C4 on `Quot.ind`: `h` must be about the form's own `Quot.mk`.
#[test]
fn c4_ind_with_a_case_for_another_quotient_is_refused() {
    let mut f = Fix::new();
    // hOther: (x: Bool) -> Quot.mk [BoolEq] x = Quot.mk [BoolEq] x
    let h_ty = pi(
        "x",
        f.bool_ty(),
        eq(Some(f.qe_ty()), f.mk_eq(v(0)), f.mk_eq(v(0))),
    );
    let h = define(f.g(), "hOther", h_ty, lam("x", Term::Refl)).expect("hOther");
    let motive = lam("q", eq(Some(f.q_ty()), v(0), v(0)));
    let term = q(
        Ind,
        vec![
            f.bool_ty(),
            f.all_true(),
            motive,
            Term::Def(h),
            f.mk(f.ff()),
        ],
    );
    refused(
        infer(&f.p.g, &term),
        "E-TYPE-MISMATCH",
        "expected `(x: Bool) → Quot.mk x = Quot.mk x`",
    );
}

// R13: positivity sees every argument of a quotient form.

/// R13: a recursive occurrence only in the relation.
#[test]
fn r13_a_recursive_occurrence_in_the_relation_is_refused() {
    let mut f = Fix::new();
    let t = data(f.g(), "T", vec![], Sort::Type(0));
    let relation = lam("x", lam("y", pi("t", Term::data(t, vec![]), f.unit_ty())));
    let kids = q(QuotType, vec![f.nat_ty(), relation]);
    refused(
        check::define_ctors(f.g(), t, vec![ctor("Node", vec![("kids", kids)])]),
        "E-POSITIVITY",
        "`T` is used inside another type",
    );
}

/// R13 (with R10's kernel side): a recursive occurrence in the carrier.
#[test]
fn r13_a_recursive_occurrence_in_the_carrier_is_refused() {
    let mut f = Fix::new();
    let list = f.p.list;
    let t = data(f.g(), "T", vec![], Sort::Type(0));
    let kids = q(
        QuotType,
        vec![
            Term::data(list, vec![Term::data(t, vec![])]),
            f.everything(),
        ],
    );
    refused(
        check::define_ctors(f.g(), t, vec![ctor("Node", vec![("kids", kids)])]),
        "E-POSITIVITY",
        "`T` is used inside another type",
    );
}

// R14 (C1): fixed arity, on every checker path.

#[test]
fn r14_every_form_with_the_wrong_number_of_arguments_is_malformed() {
    let f = Fix::new();
    for form in QuotForm::ALL {
        for n in [form.arity() - 1, form.arity() + 1] {
            let term = q(form, (0..n).map(|_| f.bool_ty()).collect());
            refused(
                infer(&f.p.g, &term),
                "E-MALFORMED",
                &format!("`{}` takes {} arguments", form.name(), form.arity()),
            );
        }
    }
}

/// C1 when the form is checked against a type rather than inferred.
#[test]
fn r14_a_malformed_form_is_refused_when_checked_too() {
    let mut f = Fix::new();
    let ty = f.q_ty();
    let body = q(Mk, vec![f.bool_ty(), f.all_true()]);
    refused(
        try_define(f.g(), "x", ty, body),
        "E-MALFORMED",
        "`Quot.mk` takes 3 arguments",
    );
}

// Accepted counterparts: the nearby terms that must check.

#[test]
fn the_rules_accept_well_formed_forms() {
    let mut f = Fix::new();
    let g = &f.p.g;
    let (_, sort) = infer(g, &f.q_ty()).expect("Q");
    assert!(matches!(sort, Value::Sort(Sort::Type(0))));
    let (_, ty) = infer(g, &f.mk(f.ff())).expect("Quot.mk False");
    assert!(conv(g, 0, &ty, &eval(g, &[], &f.q_ty()).unwrap()).unwrap());
    // Carriers: the universe `Prop`, and `Type 0` (in `Type 1`).
    let (_, sort) = infer(g, &q(QuotType, vec![prop(), f.everything()])).expect("Quot Prop");
    assert!(matches!(sort, Value::Sort(Sort::Type(0))));
    let (_, sort) = infer(g, &q(QuotType, vec![ty_n(0), f.everything()])).expect("Quot Type");
    assert!(matches!(sort, Value::Sort(Sort::Type(1))));

    // same: Quot.mk False = Quot.mk True := Quot.sound Trivial
    let statement = eq(Some(f.q_ty()), f.mk(f.ff()), f.mk(f.tt()));
    let sound = q(
        Sound,
        vec![f.bool_ty(), f.all_true(), f.ff(), f.tt(), f.trivial()],
    );
    try_define(f.g(), "same", statement, sound).expect("same");

    // A constant function respects any relation.
    let ty = arrow(f.q_ty(), f.bool_ty());
    let body = lam(
        "q",
        q(
            Lift,
            vec![
                f.bool_ty(),
                f.all_true(),
                f.bool_ty(),
                lam("b", f.ff()),
                lam("x", lam("y", lam("r", Term::Refl))),
                v(0),
            ],
        ),
    );
    try_define(f.g(), "constFalse", ty, body).expect("constFalse");

    // The identity respects equality (R11's counterpart).
    let ty = arrow(f.qe_ty(), f.bool_ty());
    let body = lam(
        "q",
        q(
            Lift,
            vec![
                f.bool_ty(),
                f.bool_eq(),
                f.bool_ty(),
                lam("b", v(0)),
                lam("x", lam("y", lam("h", v(0)))),
                v(0),
            ],
        ),
    );
    try_define(f.g(), "unwrapEq", ty, body).expect("unwrapEq");

    // allSame (q: Q): q = Quot.mk False, by `ind` and `sound`.
    let ty = pi("q", f.q_ty(), eq(Some(f.q_ty()), v(0), f.mk(f.ff())));
    let motive = lam("q", eq(Some(f.q_ty()), v(0), f.mk(f.ff())));
    let case = lam(
        "x",
        q(
            Sound,
            vec![f.bool_ty(), f.all_true(), v(0), f.ff(), f.trivial()],
        ),
    );
    let body = lam(
        "q",
        q(Ind, vec![f.bool_ty(), f.all_true(), motive, case, v(0)]),
    );
    try_define(f.g(), "allSame", ty, body).expect("allSame");
}

/// D921: the checker records whether a `Quot.mk`'s representative and a
/// `Quot.lift`'s result are erased when running, whatever the term said.
#[test]
fn the_checker_records_the_erasure_flags() {
    let f = Fix::new();
    let flag = |term: Term| match infer(&f.p.g, &term).expect("checks").0.strip_loc() {
        Term::Quot(_, _, erased) => *erased,
        other => panic!("not a quotient form: {other:?}"),
    };
    let marked = |term: Term| match term {
        Term::Quot(form, ref args, _) => Term::Quot(form, args.clone(), true),
        other => other,
    };
    // A representative that's data, and one that's a type.
    assert!(!flag(marked(f.mk(f.ff()))));
    assert!(flag(q(Mk, vec![ty(), f.everything(), f.bool_ty()])));
    // A result that's data, a proof, and a proposition.
    let lift = |b: Term, body: Term| {
        q(
            Lift,
            vec![
                f.bool_ty(),
                f.all_true(),
                b,
                lam("b", body),
                lam("x", lam("y", lam("r", Term::Refl))),
                f.mk(f.ff()),
            ],
        )
    };
    assert!(!flag(marked(lift(f.nat_ty(), f.num(0)))));
    assert!(flag(lift(f.unit_ty(), f.trivial())));
    assert!(flag(lift(prop(), f.unit_ty())));
    // The other forms are never marked.
    let sound = q(
        Sound,
        vec![f.bool_ty(), f.all_true(), f.ff(), f.tt(), f.trivial()],
    );
    assert!(!flag(marked(sound)));
}

/// R3's counterpart: matching on `At q` for a variable `q` solves it.
#[test]
fn a_quotient_index_variable_is_solved() {
    let mut f = Fix::new();
    let at = at_family(&mut f);
    let ty = pi("q", f.q_ty(), arrow(Term::data(at, vec![v(0)]), f.nat_ty()));
    let body = lam(
        "q",
        lam(
            "a",
            icase(
                0,
                at,
                vec![(vec![], Some(f.num(0))), (vec![], Some(f.num(1)))],
            ),
        ),
    );
    try_define(f.g(), "which", ty, body).expect("which");
}

// Stage 1.2: the computation rule `Quot.lift f h (Quot.mk a) ⟶ f a`, and
// the unfolding policy (§7.2).

/// `toNat: Bool -> Nat` (`False` is 0, `True` is 1), with its proof that it
/// respects `BoolEq`, by `J`; and the lift of it on `Quot Bool BoolEq`.
struct Lifted {
    to_nat: DefId,
    resp: DefId,
}

impl Lifted {
    fn new(f: &mut Fix) -> Lifted {
        let (bool_ty, nat_ty) = (f.bool_ty(), f.nat_ty());
        let body = lam(
            "b",
            case(0, f.bool_, vec![(vec![], f.num(0)), (vec![], f.num(1))]),
        );
        let to_nat = define(f.g(), "toNat", arrow(bool_ty, nat_ty), body).expect("toNat");
        let to_nat_eq = |x: Term, y: Term| {
            eq(
                Some(f.nat_ty()),
                app(Term::Def(to_nat), [x]),
                app(Term::Def(to_nat), [y]),
            )
        };
        // (x y: Bool) -> BoolEq x y -> toNat x = toNat y
        let ty = pi(
            "x",
            f.bool_ty(),
            pi(
                "y",
                f.bool_ty(),
                arrow(app(f.bool_eq(), [v(1), v(0)]), to_nat_eq(v(1), v(0))),
            ),
        );
        // x y e => J (y' p => toNat x = toNat y') rfl e
        let motive = lam("y'", lam("p", to_nat_eq(v(4), v(1))));
        let body = lam(
            "x",
            lam(
                "y",
                lam(
                    "e",
                    Term::J(Rc::new(motive), Rc::new(Term::Refl), Rc::new(v(0))),
                ),
            ),
        );
        let resp = define(f.g(), "toNatRespects", ty, body).expect("toNatRespects");
        Lifted { to_nat, resp }
    }

    /// `Quot.lift [Bool] [BoolEq] [Nat] toNat toNatRespects q`.
    fn lift(&self, f: &Fix, q: Term) -> Term {
        Term::quot(
            Lift,
            vec![
                f.bool_ty(),
                f.bool_eq(),
                f.nat_ty(),
                Term::Def(self.to_nat),
                Term::Def(self.resp),
                q,
            ],
        )
    }
}

/// Defines the theorem `ty := rfl`, which must check.
#[track_caller]
fn by_rfl(f: &mut Fix, name: &str, ty: Term) -> DefId {
    try_define(f.g(), name, ty, Term::Refl).unwrap_or_else(|d| panic!("{name}: {d:?}"))
}

/// A1, data in `Type 0`: on a `Quot.mk`, written there or reached through a
/// definition or a `let`.
#[test]
fn a1_lift_on_mk_computes() {
    let mut f = Fix::new();
    let l = Lifted::new(&mut f);
    let lifted = l.lift(&f, f.mk_eq(f.tt()));
    let statement = eq(
        Some(f.nat_ty()),
        lifted.clone(),
        app(Term::Def(l.to_nat), [f.tt()]),
    );
    by_rfl(&mut f, "liftIsF", statement);
    let statement = eq(Some(f.nat_ty()), lifted, f.num(1));
    by_rfl(&mut f, "liftIsOne", statement);
    // Through a definition.
    let (qe_ty, mk) = (f.qe_ty(), f.mk_eq(f.tt()));
    let mk_true = define(f.g(), "mkTrue", qe_ty, mk).expect("mkTrue");
    let statement = eq(Some(f.nat_ty()), l.lift(&f, Term::Def(mk_true)), f.num(1));
    by_rfl(&mut f, "throughADef", statement);
    // Through a `let`.
    let through_let = Term::let_("q".into(), f.qe_ty(), f.mk_eq(f.ff()), l.lift(&f, v(0)));
    let statement = eq(Some(f.nat_ty()), through_let, f.num(0));
    by_rfl(&mut f, "throughALet", statement);
    // And `False` and `True` stay apart: the rule computes, it doesn't
    // identify.
    let statement = eq(Some(f.nat_ty()), l.lift(&f, f.mk_eq(f.ff())), f.num(1));
    refused(
        try_define(f.g(), "wrong", statement, Term::Refl),
        "E-REFL",
        "`0` and `1` aren't equal",
    );
}

/// A1, for every kind of result and every kind of carrier: data in `Type 1`,
/// a type (`B := Type`), a proposition (`B := Prop`), a proof (`B : Prop`);
/// carriers `Type` (in `Type 1`) and `Prop` (in `Type 0`).
#[test]
fn a1_lift_computes_at_every_result_and_carrier() {
    let mut f = Fix::new();
    let respects = || lam("x", lam("y", lam("r", Term::Refl)));
    let lift = |f: &Fix, carrier: Term, b: Term, fun: DefId, a: Term| {
        Term::quot(
            Lift,
            vec![
                carrier.clone(),
                f.everything(),
                b,
                Term::Def(fun),
                respects(),
                Term::quot(Mk, vec![carrier, f.everything(), a]),
            ],
        )
    };
    // Data in `Type 1`: `TBox = MkTBox (t: Type)`.
    let tbox = data(f.g(), "TBox", vec![], Sort::Type(1));
    check::define_ctors(f.g(), tbox, vec![ctor("MkTBox", vec![("t", ty())])]).expect("TBox");
    let tbox_ty = Term::data(tbox, vec![]);
    let nat_box = Term::ctor(tbox, 0, vec![f.nat_ty()]);
    let fun_ty = arrow(f.bool_ty(), tbox_ty.clone());
    let boxed = define(f.g(), "boxed", fun_ty, lam("b", nat_box)).expect("boxed");
    let statement = eq(
        Some(tbox_ty.clone()),
        lift(&f, f.bool_ty(), tbox_ty, boxed, f.ff()),
        app(Term::Def(boxed), [f.ff()]),
    );
    by_rfl(&mut f, "inType1", statement);
    // A type: `B := Type`.
    let fun_ty = arrow(f.bool_ty(), ty());
    let nat_ty = f.nat_ty();
    let natty = define(f.g(), "natTy", fun_ty, lam("b", nat_ty)).expect("natTy");
    let statement = eq(
        Some(ty()),
        lift(&f, f.bool_ty(), ty(), natty, f.tt()),
        f.nat_ty(),
    );
    by_rfl(&mut f, "aType", statement);
    // A proposition: `B := Prop`.
    let fun_ty = arrow(f.bool_ty(), prop());
    let unit_ty = f.unit_ty();
    let unit_of = define(f.g(), "unitOf", fun_ty, lam("b", unit_ty)).expect("unitOf");
    let statement = eq(
        Some(prop()),
        lift(&f, f.bool_ty(), prop(), unit_of, f.tt()),
        f.unit_ty(),
    );
    by_rfl(&mut f, "aProposition", statement);
    // A proof: `B := Unit`, a proposition.
    let fun_ty = arrow(f.bool_ty(), f.unit_ty());
    let trivial = f.trivial();
    let proof_of = define(f.g(), "proofOf", fun_ty, lam("b", trivial)).expect("proofOf");
    let statement = eq(
        Some(f.unit_ty()),
        lift(&f, f.bool_ty(), f.unit_ty(), proof_of, f.ff()),
        app(Term::Def(proof_of), [f.ff()]),
    );
    by_rfl(&mut f, "aProof", statement);
    // A carrier of types, in `Type 1`: `seven (a: Type): Nat := 7`.
    let fun_ty = arrow(ty(), f.nat_ty());
    let seven_body = lam("a", f.num(7));
    let seven = define(f.g(), "seven", fun_ty, seven_body).expect("seven");
    let statement = eq(
        Some(f.nat_ty()),
        lift(&f, ty(), f.nat_ty(), seven, f.bool_ty()),
        app(Term::Def(seven), [f.bool_ty()]),
    );
    by_rfl(&mut f, "carrierOfTypes", statement);
    // A carrier of propositions, the universe `Prop`, in `Type 0`.
    let fun_ty = arrow(prop(), f.nat_ty());
    let three_body = lam("p", f.num(3));
    let three = define(f.g(), "three", fun_ty, three_body).expect("three");
    let statement = eq(
        Some(f.nat_ty()),
        lift(&f, prop(), f.nat_ty(), three, f.zero_is_zero()),
        f.num(3),
    );
    by_rfl(&mut f, "carrierOfPropositions", statement);
}

/// R7 and R8 still hold with the rule in: it's for `lift` alone, and it
/// doesn't make related values convertible. (The tests above run again too;
/// these say so where the rule is.)
#[test]
fn r7_r8_the_rule_is_for_lift_alone() {
    let mut f = Fix::new();
    // `ind` on a `Quot.mk` stays stuck.
    let h_ty = arrow(f.bool_ty(), f.unit_ty());
    let trivial = f.trivial();
    let h = define(f.g(), "h", h_ty, lam("b", trivial)).expect("h");
    let ind = Term::quot(
        Ind,
        vec![
            f.bool_ty(),
            f.bool_eq(),
            lam("_", f.unit_ty()),
            Term::Def(h),
            f.mk_eq(f.tt()),
        ],
    );
    let statement = eq(Some(f.unit_ty()), ind, f.trivial());
    refused(
        try_define(f.g(), "indComputes", statement, Term::Refl),
        "E-REFL",
        "aren't equal",
    );
    // Related representatives stay apart under conversion.
    let statement = eq(Some(f.q_ty()), f.mk(f.ff()), f.mk(f.tt()));
    refused(
        try_define(f.g(), "same", statement, Term::Refl),
        "E-REFL",
        "`Quot.mk False` and `Quot.mk True` aren't equal",
    );
}

/// A8: a definition whose case tree is a `Quot.lift` on its argument stays
/// folded on a variable (so goals show `observe q`), and that never stops
/// conversion from comparing it with its body, or with another definition
/// with the same body, or with itself on different but unused arguments.
#[test]
fn a8_a_folded_lift_is_still_its_body() {
    let mut f = Fix::new();
    let l = Lifted::new(&mut f);
    let observe_ty = arrow(f.qe_ty(), f.nat_ty());
    let observe_body = lam("q", l.lift(&f, v(0)));
    let observe =
        define(f.g(), "observe", observe_ty.clone(), observe_body.clone()).expect("observe");
    let again = define(f.g(), "again", observe_ty, observe_body).expect("again");
    let applied = |id: DefId| app(Term::Def(id), [v(0)]);
    let for_all = |f: &Fix, body: Term| pi("q", f.qe_ty(), body);
    let proof = lam("q", Term::Refl);
    // observe q = Quot.lift toNat toNatRespects q, both ways round.
    let statement = for_all(&f, eq(Some(f.nat_ty()), applied(observe), l.lift(&f, v(0))));
    try_define(f.g(), "unfolds", statement, proof.clone()).expect("unfolds");
    let statement = for_all(&f, eq(Some(f.nat_ty()), l.lift(&f, v(0)), applied(observe)));
    try_define(f.g(), "folds", statement, proof.clone()).expect("folds");
    // Two definitions with the same body.
    let statement = for_all(&f, eq(Some(f.nat_ty()), applied(observe), applied(again)));
    try_define(f.g(), "same", statement, proof.clone()).expect("same");
    // An argument the body doesn't use: different, but equal unfolded.
    let ignoring_ty = arrow(f.qe_ty(), arrow(f.nat_ty(), f.nat_ty()));
    let ignoring_body = lam("q", lam("n", l.lift(&f, v(1))));
    let ignoring = define(f.g(), "ignoring", ignoring_ty, ignoring_body).expect("ignoring");
    let statement = for_all(
        &f,
        eq(
            Some(f.nat_ty()),
            app(Term::Def(ignoring), [v(0), f.num(1)]),
            app(Term::Def(ignoring), [v(0), f.num(2)]),
        ),
    );
    try_define(f.g(), "ignored", statement, proof.clone()).expect("ignored");
    // A lift under a case is a leaf too.
    let under_ty = arrow(f.bool_ty(), arrow(f.qe_ty(), f.nat_ty()));
    let under_body = lam(
        "b",
        lam(
            "q",
            case(
                1,
                f.bool_,
                vec![(vec![], f.num(0)), (vec![], l.lift(&f, v(0)))],
            ),
        ),
    );
    let under = define(f.g(), "under", under_ty, under_body).expect("under");
    let statement = for_all(
        &f,
        eq(
            Some(f.nat_ty()),
            app(Term::Def(under), [f.tt(), v(0)]),
            applied(observe),
        ),
    );
    try_define(f.g(), "underCase", statement, proof.clone()).expect("underCase");
    // On a `Quot.mk`, it computes.
    let statement = eq(
        Some(f.nat_ty()),
        app(Term::Def(observe), [f.mk_eq(f.tt())]),
        f.num(1),
    );
    by_rfl(&mut f, "observeTrue", statement);
    // Folding changes nothing that's equal: an open `observe q` still
    // isn't a number.
    let statement = for_all(&f, eq(Some(f.nat_ty()), applied(observe), f.num(1)));
    refused(
        try_define(f.g(), "notOne", statement, proof),
        "E-REFL",
        "`observe q` and `1` aren't equal",
    );

    // What's shown: `observe q`, folded, for a variable `q`; the lift
    // itself when written out; the number on a `Quot.mk`.
    let g = &f.p.g;
    let names: Vec<stitchwort_core::Name> = vec!["q".into()];
    let shown = |term: &Term, level: usize| {
        let env: Vec<Value> = (0..level).map(Value::var).collect();
        let value = eval(g, &env, term).expect("evaluates");
        let quoted = quote(g, level, &value).expect("quotes");
        stitchwort_core::pretty::term(g, &names[..level], &quoted)
    };
    assert_eq!(shown(&applied(observe), 1), "observe q");
    let under_true = app(Term::Def(under), [f.tt(), v(0)]);
    assert_eq!(shown(&under_true, 1), "under True q");
    assert_eq!(
        shown(&l.lift(&f, v(0)), 1),
        "Quot.lift toNat toNatRespects q"
    );
    let on_mk = app(Term::Def(observe), [f.mk_eq(f.tt())]);
    assert_eq!(shown(&on_mk, 0), "1");
}

/// A lift on a closed quotient that isn't a `Quot.mk` (`J` on `Quot.sound`,
/// stuck) doesn't compute, in a definition with no parameters too; and that
/// definition is still its body (A8's condition: whether a definition stays
/// folded never changes what's equal).
#[test]
fn a_lift_on_a_stuck_closed_quotient_is_neutral_and_still_its_body() {
    let mut f = Fix::new();
    let q_ty = f.q_ty();
    // sameQ: Quot.mk False = Quot.mk True := Quot.sound Trivial
    let same_ty = eq(Some(f.q_ty()), f.mk(f.ff()), f.mk(f.tt()));
    let sound = q(
        Sound,
        vec![f.bool_ty(), f.all_true(), f.ff(), f.tt(), f.trivial()],
    );
    let same = try_define(f.g(), "sameQ", same_ty, sound).expect("sameQ");
    // stuckQ: Q := J (y p => Q) (Quot.mk True) sameQ
    let motive = lam("y", lam("p", f.q_ty()));
    let stuck_body = Term::J(
        Rc::new(motive),
        Rc::new(f.mk(f.tt())),
        Rc::new(Term::Def(same)),
    );
    let stuck = try_define(f.g(), "stuckQ", q_ty, stuck_body).expect("stuckQ");
    // constLift: Nat := Quot.lift [Bool] [AllTrue] [Nat] (b => 0) (x y r => rfl) stuckQ
    let lift = |f: &Fix| {
        q(
            Lift,
            vec![
                f.bool_ty(),
                f.all_true(),
                f.nat_ty(),
                lam("b", f.num(0)),
                lam("x", lam("y", lam("r", Term::Refl))),
                Term::Def(stuck),
            ],
        )
    };
    let (nat_ty, body) = (f.nat_ty(), lift(&f));
    let c = try_define(f.g(), "constLift", nat_ty, body).expect("constLift");
    let statement = eq(Some(f.nat_ty()), Term::Def(c), lift(&f));
    by_rfl(&mut f, "constLiftIsItsBody", statement);
    let statement = eq(Some(f.nat_ty()), lift(&f), Term::Def(c));
    by_rfl(&mut f, "constLiftIsItsBodyBackwards", statement);
    // Not a number: the rule needs a `Quot.mk`, and `stuckQ` isn't one.
    let statement = eq(Some(f.nat_ty()), Term::Def(c), f.num(0));
    refused(
        try_define(f.g(), "constLiftIsZero", statement, Term::Refl),
        "E-REFL",
        "aren't equal",
    );
}
