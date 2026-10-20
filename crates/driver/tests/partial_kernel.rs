//! The kernel's partial computations (docs/proposals/partial.md §7.2, §8):
//! `Delay` and its constants, admitted from the prelude, called directly
//! with core terms, in ways the elaborator never would. Each must-reject
//! case is paired with an accepted neighbour where there is one.

use std::rc::Rc;

use stitchwort_core::check::{self, CtorDecl};
use stitchwort_core::globals::State;
use stitchwort_core::hash::def_hash;
use stitchwort_core::partial::{self, Primitive};
use stitchwort_core::value::{conv, eval};
use stitchwort_core::{DataId, DefId, Globals, Icit, Sort, Term};
use stitchwort_driver::driver::Session;
use stitchwort_elab::{Elaborator, PRELUDE};
use stitchwort_syntax::{SourceMap, Span};

fn span() -> Span {
    let mut sources = SourceMap::new();
    let file = sources.add("test", "");
    Span::point(file, 0)
}

fn data(g: &Globals, name: &str) -> DataId {
    g.find_data(name).expect("the prelude declares it")
}

fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .rposition(|d| &*d.name == name)
            .expect("declared"),
    )
}

fn prim(g: &Globals, p: Primitive) -> DefId {
    g.builtins.primitive_id(p).expect("admitted")
}

fn app(f: Term, args: impl IntoIterator<Item = (Term, Icit)>) -> Term {
    args.into_iter()
        .fold(f, |f, (a, icit)| Term::app_icit(f, a, icit))
}

fn imp(t: Term) -> (Term, Icit) {
    (t, Icit::Implicit)
}

fn exp(t: Term) -> (Term, Icit) {
    (t, Icit::Explicit)
}

fn lam(x: &str, body: Term) -> Term {
    Term::Lam(x.into(), Icit::Explicit, Rc::new(body))
}

fn arrow(a: Term, b: Term) -> Term {
    Term::Pi("_".into(), Icit::Explicit, Rc::new(a), Rc::new(b))
}

fn code<T>(r: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    r.err().map_or("ok", |d| d.code)
}

/// Terms for the row `{}` and a description over `{Rec Nat}`.
struct Rows {
    nat: Term,
    no_op: Term,
    no_res: Term,
    rec_nat: Term,
    /// `Plus (Rec Nat) NoOp`
    ops: Term,
    /// `PlusRes (RecRes (_ => Nat)) NoRes`
    res: Term,
    /// `_ => Nat`, under `depth` binders.
    ans: Term,
}

fn rows(g: &Globals) -> Rows {
    let nat = Term::Data(data(g, "Nat"), vec![]);
    let no_op = Term::Data(data(g, "Effect.NoOp"), vec![]);
    let no_res = Term::Def(def(g, "Effect.NoRes"));
    let rec_nat = Term::data(data(g, "Effect.Rec"), vec![nat.clone()]);
    let ops = Term::data(data(g, "Effect.Plus"), vec![rec_nat.clone(), no_op.clone()]);
    let ans = lam("_", nat.clone());
    let rec_res = app(
        Term::Def(def(g, "Effect.RecRes")),
        [imp(nat.clone()), exp(ans.clone())],
    );
    let res = app(
        Term::Def(def(g, "Effect.PlusRes")),
        [
            imp(rec_nat.clone()),
            imp(no_op.clone()),
            exp(rec_res),
            exp(no_res.clone()),
        ],
    );
    Rows {
        nat,
        no_op,
        no_res,
        rec_nat,
        ops,
        res,
        ans,
    }
}

fn delay(g: &Globals, ops: Term, res: Term, a: Term) -> Term {
    app(
        Term::Def(prim(g, Primitive::Delay)),
        [exp(ops), exp(res), exp(a)],
    )
}

/// `\x -> pfix [{}] [Nat] [\_ -> Nat] (\y -> body y) x`, where `body`
/// builds the description's result from `y` (variable 0).
fn wrapper(g: &Globals, r: &Rows, body: Term) -> Term {
    let pfix = app(
        Term::Def(prim(g, Primitive::Pfix)),
        [
            imp(r.no_op.clone()),
            imp(r.no_res.clone()),
            imp(r.nat.clone()),
            imp(r.ans.clone()),
        ],
    );
    lam("x", app(pfix, [exp(lam("y", body)), exp(Term::Var(0))]))
}

/// `mapSig sigRight d`: a computation over `{}` moved into the
/// description's row `{Rec Nat}`.
fn map_right(g: &Globals, r: &Rows, d: Term) -> Term {
    let sig_right = app(
        Term::Def(def(g, "Effect.sigRight")),
        [
            imp(r.rec_nat.clone()),
            imp(r.no_op.clone()),
            imp(app(
                Term::Def(def(g, "Effect.RecRes")),
                [imp(r.nat.clone()), exp(r.ans.clone())],
            )),
            imp(r.no_res.clone()),
        ],
    );
    app(
        Term::Def(prim(g, Primitive::MapSig)),
        [
            imp(r.no_op.clone()),
            imp(r.no_res.clone()),
            imp(r.ops.clone()),
            imp(r.res.clone()),
            imp(r.nat.clone()),
            exp(sig_right),
            exp(d),
        ],
    )
}

fn nat_to_delay(g: &Globals, r: &Rows) -> Term {
    arrow(
        r.nat.clone(),
        delay(g, r.no_op.clone(), r.no_res.clone(), r.nat.clone()),
    )
}

#[test]
fn delay_and_its_constants_are_final_opaque_and_hashed() {
    let session = Session::new();
    let g = &session.elab.globals;
    assert!(
        g.find_data("Effect.Delay").is_none(),
        "`Effect.Delay` isn't a data type"
    );
    for p in Primitive::ALL {
        let id = prim(g, p);
        let d = g.def(id);
        assert_eq!(&*d.name, p.name());
        assert_eq!(d.state(), State::Final, "{}", p.name());
        assert!(d.body().is_none(), "{} has no computation rule", p.name());
        assert!(def_hash(g, id).unwrap().is_some(), "{} is hashed", p.name());
    }
}

/// A constant whose type isn't exactly the proposal's is refused when the
/// prelude declares it: in particular one that would take a value out of a
/// `Delay` (an eliminator, which would let total code run partial code).
#[test]
fn a_constant_with_another_type_is_refused() {
    let cases = [
        (
            "def Effect.now: [op: Type] -> [res: op -> Type] -> [a: Type] -> a -> Delay op res a",
            "def Effect.now: [op: Type] -> [res: op -> Type] -> [a: Type] -> Delay op res a -> a",
        ),
        (
            "  (x: req) -> Delay op res (ans x)",
            "  (x: req) -> Delay (Plus (Rec req) op) (PlusRes (RecRes ans) res) (ans x)",
        ),
        (
            "def Effect.Delay: (op: Type) -> (res: op -> Type) -> Type -> Type",
            "def Effect.Delay: (op: Type) -> (res: op -> Type) -> Type -> Prop",
        ),
    ];
    for (original, changed) in cases {
        assert!(PRELUDE.contains(original), "{original}");
        let prelude = PRELUDE.replacen(original, changed, 1);
        let mut session = Session {
            sources: SourceMap::new(),
            elab: Elaborator::new(),
            warnings: Vec::new(),
        };
        session.elab.loading_prelude = true;
        let errors = session.load("<prelude>", &prelude).unwrap_err();
        assert!(
            errors.iter().any(|d| d.code == "E-BUILTIN"),
            "{changed}: {errors:#?}"
        );
    }
}

#[test]
fn a_constant_is_admitted_once() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    // A second `now`, with exactly the right type: refused, since `now` is
    // admitted already.
    let ty = g.def(prim(g, Primitive::Now)).ty.clone();
    let again = check::declare_def(g, &"now2".into(), &ty, false, false, span()).unwrap();
    assert_eq!(
        code(partial::define_primitive(g, again, Primitive::Now)),
        "E-BUILTIN"
    );
    assert_eq!(g.def(again).state(), State::Failed);
    // Admitting a final definition again is malformed.
    let now = prim(g, Primitive::Now);
    assert_eq!(
        code(partial::define_primitive(g, now, Primitive::Now)),
        "E-MALFORMED"
    );
}

/// `Delay` has no `case`: it isn't a data type, so a match on a `Delay`
/// value can only claim to be a match on some data type, and the kernel
/// refuses it.
#[test]
fn a_delay_cant_be_matched_on() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let r = rows(g);
    let nat = data(g, "Nat");
    let ty = arrow(
        delay(g, r.no_op.clone(), r.no_res.clone(), r.nat.clone()),
        r.nat.clone(),
    );
    let f = check::declare_def(g, &"drain".into(), &ty, false, false, span()).unwrap();
    let zero = || Term::Ctor(nat, 0, vec![]);
    let body = lam(
        "d",
        Term::Case(
            0,
            nat,
            vec![
                stitchwort_core::term::Branch {
                    names: vec![],
                    body: Some(Rc::new(zero())),
                },
                stitchwort_core::term::Branch {
                    names: vec!["k".into()],
                    body: Some(Rc::new(zero())),
                },
            ]
            .into(),
        ),
    );
    assert_eq!(code(check::define_def(g, f, &body)), "E-TYPE-MISMATCH");
    // Neighbour: the same match on a `Nat` is fine.
    let ty = arrow(r.nat.clone(), r.nat.clone());
    let f = check::declare_def(g, &"fine".into(), &ty, false, false, span()).unwrap();
    assert_eq!(code(check::define_def(g, f, &body)), "ok");
}

/// The `pfixBad` shape (§8.3): a description that runs the function being
/// defined, rather than requesting it, is an ordinary recursive definition,
/// which the termination checker refuses. Its neighbour, which requests the
/// recursive call, is accepted.
#[test]
fn a_description_calling_its_own_wrapper_is_refused() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let r = rows(g);
    let ty = nat_to_delay(g, &r);
    let bad = check::declare_def(g, &"bad".into(), &ty, false, false, span()).unwrap();
    // bad x = pfix (\y -> mapSig sigRight (bad y)) x
    let calls_itself = wrapper(
        g,
        &r,
        map_right(g, &r, app(Term::Def(bad), [exp(Term::Var(0))])),
    );
    assert_eq!(
        code(check::define_def(g, bad, &calls_itself)),
        "E-TERMINATION"
    );
    assert_eq!(g.def(bad).state(), State::Failed);

    // good x = pfix (\y -> lift (Call (L (Recur y)) (\v -> Done v))) x
    let good = check::declare_def(g, &"good".into(), &ty, false, false, span()).unwrap();
    let comp = data(g, "Effect.Comp");
    let request = Term::ctor(
        data(g, "Effect.Plus"),
        0,
        vec![Term::ctor(data(g, "Effect.Rec"), 0, vec![Term::Var(0)])],
    );
    let call = Term::ctor(
        comp,
        1,
        vec![request, lam("v", Term::ctor(comp, 0, vec![Term::Var(0)]))],
    );
    let lift = app(
        Term::Def(prim(g, Primitive::Lift)),
        [
            imp(r.ops.clone()),
            imp(r.res.clone()),
            imp(r.nat.clone()),
            exp(call),
        ],
    );
    assert_eq!(
        code(check::define_def(g, good, &wrapper(g, &r, lift))),
        "ok"
    );
}

/// A description calling another wrapper that isn't finished yet (a sibling
/// left in by a buggy translation) is refused by admission.
#[test]
fn a_description_calling_an_unfinished_wrapper_is_refused() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let r = rows(g);
    let ty = nat_to_delay(g, &r);
    let first = check::declare_def(g, &"first".into(), &ty, false, false, span()).unwrap();
    let second = check::declare_def(g, &"second".into(), &ty, false, false, span()).unwrap();
    let calls_second = wrapper(
        g,
        &r,
        map_right(g, &r, app(Term::Def(second), [exp(Term::Var(0))])),
    );
    assert_eq!(
        code(check::define_def(g, first, &calls_second)),
        "E-MALFORMED"
    );
}

/// Conversion never runs partial code: `collatzSteps 1` and `now 0` have the
/// same eventual result, but they aren't equal, and comparing them unfolds
/// no `pfix`. Syntactically equal ones are.
#[test]
fn conversion_never_unfolds_a_partial_computation() {
    let mut session = Session::new();
    session
        .load(
            "test.sw",
            "def collatzSteps : Nat -> {Partial} Nat\n  \
             | 1 => 0\n  \
             | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)\n\
             def spin (n : Nat) : {Partial} Nat := spin n\n",
        )
        .unwrap();
    let g = &session.elab.globals;
    let r = rows(g);
    let one = Term::Nat(Rc::new(1u32.into()));
    let steps = app(Term::Def(def(g, "collatzSteps")), [exp(one)]);
    let now = app(
        Term::Def(prim(g, Primitive::Now)),
        [
            imp(r.no_op.clone()),
            imp(r.no_res.clone()),
            imp(r.nat.clone()),
            exp(Term::Nat(Rc::new(0u32.into()))),
        ],
    );
    let a = eval(g, &[], &steps).unwrap();
    let b = eval(g, &[], &now).unwrap();
    assert!(!conv(g, 0, &a, &b).unwrap());
    assert!(conv(g, 0, &a, &eval(g, &[], &steps).unwrap()).unwrap());
    // `spin 0` never finishes, and comparing it with itself, or with
    // something else, takes a few steps.
    let spin = app(
        Term::Def(def(g, "spin")),
        [exp(Term::Nat(Rc::new(0u32.into())))],
    );
    let s = eval(g, &[], &spin).unwrap();
    assert!(conv(g, 0, &s, &s).unwrap());
    assert!(!conv(g, 0, &s, &b).unwrap());
}

/// A data type can't recurse through `Delay`: it's a nested occurrence.
#[test]
fn a_data_type_recursing_through_delay_is_refused() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let r = rows(g);
    let bad = check::declare_data(g, "Bad".into(), vec![], Sort::Type(0), span()).unwrap();
    let field = delay(
        g,
        r.no_op.clone(),
        r.no_res.clone(),
        Term::Data(bad, vec![]),
    );
    let ctors = vec![CtorDecl {
        name: "MkBad".into(),
        fields: vec![("d".into(), field, span())],
        result: Vec::new(),
        implicit: Vec::new(),
    }];
    assert_eq!(code(check::define_ctors(g, bad, ctors)), "E-POSITIVITY");
}
