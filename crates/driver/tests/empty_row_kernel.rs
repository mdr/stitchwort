//! A computation over the empty row, `Comp NoOp NoRes a`, used
//! where an `a` is expected (SW-124). The elaborator runs it with
//! `Effect.runPure`, as for any computation named in direct style; the
//! kernel never treats the two types as one. Each must-reject case is
//! paired with the accepted term the elaborator actually produces.

use std::rc::Rc;

use stitchwort_core::check;
use stitchwort_core::value::{conv, eval};
use stitchwort_core::{DefId, Globals, Icit, Term};
use stitchwort_driver::driver::Session;
use stitchwort_syntax::{SourceMap, Span};

fn span() -> Span {
    let mut sources = SourceMap::new();
    let file = sources.add("test", "");
    Span::point(file, 0)
}

fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .rposition(|d| &*d.name == name)
            .expect("declared"),
    )
}

fn code<T>(r: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    r.err().map_or("ok", |d| d.code)
}

fn comp_nat(g: &Globals) -> (Term, Term) {
    let nat = Term::Data(g.find_data("Nat").unwrap(), vec![]);
    let no_op = Term::Data(g.find_data("Effect.NoOp").unwrap(), vec![]);
    let no_res = Term::Def(def(g, "Effect.NoRes"));
    let comp = Term::data(
        g.find_data("Effect.Comp").unwrap(),
        vec![no_op, no_res, nat.clone()],
    );
    (comp, nat)
}

// Written with `Comp` itself: a row written `{}` is no row at all, so
// `def f: {} Nat` would just be a `Nat`.
const SOURCE: &str = "import Std.Effect (Comp, NoOp, NoRes)\n\
                      def f: Comp NoOp NoRes Nat := 3\n\
                      def g: Nat := f\n";

/// The elaborated `g` is `runPure f`: the kernel checks a well-typed term,
/// not a conversion between `Comp NoOp NoRes Nat` and `Nat`.
#[test]
fn the_elaborator_runs_the_computation_with_run_pure() {
    let mut session = Session::new();
    session.load("test.sw", SOURCE).unwrap();
    let g = &session.elab.globals;
    let body = g.def(def(g, "g")).body().expect("g has a body").clone();
    let printed = stitchwort_core::pretty::term(g, &[], &body);
    assert!(
        printed.contains("Effect.runPure") && printed.contains('f'),
        "g's core body: {printed}"
    );
}

/// The kernel itself: `Comp NoOp NoRes Nat` and `Nat` aren't convertible,
/// `f` alone is refused at `Nat`, and `runPure [Nat] f` is accepted.
#[test]
fn the_kernel_keeps_the_empty_row_apart_from_its_result() {
    let mut session = Session::new();
    session.load("test.sw", SOURCE).unwrap();
    let g = &mut session.elab.globals;
    let (comp, nat) = comp_nat(g);
    let a = eval(g, &[], &comp).unwrap();
    let b = eval(g, &[], &nat).unwrap();
    assert!(!conv(g, 0, &a, &b).unwrap());

    let f = Term::Def(def(g, "f"));
    let bad = check::declare_def(g, &"bad".into(), &nat, false, false, span()).unwrap();
    assert_eq!(code(check::define_def(g, bad, &f)), "E-TYPE-MISMATCH");

    let run = Term::app_icit(
        Term::app_icit(
            Term::Def(def(g, "Effect.runPure")),
            nat.clone(),
            Icit::Implicit,
        ),
        f.clone(),
        Icit::Explicit,
    );
    let good = check::declare_def(g, &"good".into(), &nat, false, false, span()).unwrap();
    assert_eq!(code(check::define_def(g, good, &run)), "ok");

    // The other way round: a `Nat` isn't a `Comp NoOp NoRes Nat` either.
    let three = Term::Nat(Rc::new(3u32.into()));
    let bad2 = check::declare_def(g, &"bad2".into(), &comp, false, false, span()).unwrap();
    assert_eq!(code(check::define_def(g, bad2, &three)), "E-TYPE-MISMATCH");
}

// A handler with an open row, used where nothing else is performed: its
// row is empty, so the call runs in place and an equation about it is an
// ordinary equation (docs/proposals/abilities.md, "Effectful calls at the
// empty row"). One theorem for each place a call can stand: an equation's
// side, an argument, a `let`'s value and a `match`'s scrutinee.
const HANDLERS: &str = "import Std (Abort, Option)

theorem same (c: () -> {Abort} Nat): Abort.toOption c = Abort.toOption c := rfl

theorem asArgument (c: () -> {Abort} Nat): Option.isSome (Abort.toOption c) = Option.isSome (Abort.toOption c) := rfl

def viaLet (c: () -> {Abort} Nat): Bool :=
  let r := Abort.toOption c
  Option.isSome r

theorem inLet (c: () -> {Abort} Nat): viaLet c = Option.isSome (Abort.toOption c) := rfl

def viaMatch (c: () -> {Abort} Nat): Nat :=
  match Abort.toOption c with
    | Some n => n
    | None => 0

theorem inMatch (c: () -> {Abort} Nat): viaMatch c = Option.getOrElse 0 (Abort.toOption c) :=
  match h: Abort.toOption c with
    | Some n => rfl
    | None => rfl
";

/// The statement of `same` is an equation between two calls of
/// `Abort.toOption` at the empty row, with nothing run or sequenced: its
/// result type `{e} Option a` is `Option a` there (design C of
/// docs/proposals/effect-polymorphism.md).
#[test]
fn an_equation_about_a_handler_at_the_empty_row_is_an_equation() {
    let mut session = Session::new();
    if let Err(ds) = session.load("test.sw", HANDLERS) {
        panic!("{:?}", ds.iter().map(|d| &d.message).collect::<Vec<_>>());
    }
    let g = &session.elab.globals;
    let ty = g.def(def(g, "same")).ty.clone();
    let printed = stitchwort_core::pretty::term(g, &[], &ty);
    assert!(
        !printed.contains("Effect.bind")
            && !printed.contains("Effect.runPure")
            && printed.contains("Abort.toOption"),
        "same's statement: {printed}"
    );
}

/// The canonical form of rows (docs/proposals/effect-polymorphism.md
/// §5.C.2): a pure use of an effect-polymorphic function elaborates with the
/// row `Empty`, and no `Comp`, `Done`, `runPure` or `Ops` anywhere in the
/// term; and `{}` is no row at all.
#[test]
fn a_pure_use_of_an_effect_polymorphic_function_has_no_computation() {
    let mut session = Session::new();
    let source = "import Std (List)\n\
                  def doubled (xs: List Nat): List Nat := List.mapIn (x => x + x) xs\n\
                  def successors (xs: List Nat): List Nat := List.mapIn Succ xs\n\
                  def unannotated (xs: List Nat): Nat :=\n  let ys := List.mapIn (x => x + 1) xs\n  List.sum ys\n\
                  def emptyRow (f: Nat -> {} Nat) (xs: List Nat): List Nat := List.mapIn f xs\n";
    if let Err(ds) = session.load("test.sw", source) {
        panic!("{:?}", ds.iter().map(|d| &d.message).collect::<Vec<_>>());
    }
    let g = &session.elab.globals;
    let comp = g.find_data("Effect.Comp").unwrap();
    let row = g.find_data("Effect.Effects").unwrap();
    let run_pure = def(g, "Effect.runPure");
    for name in ["doubled", "successors", "unannotated", "emptyRow"] {
        let d = g.def(def(g, name));
        let body = d.body().expect("checked").clone();
        let mut empty_rows = 0;
        for term in [&d.ty, &*body] {
            for (t, _) in term.subterms() {
                match t {
                    Term::Data(id, _) => assert_ne!(*id, comp, "`{name}` mentions `Comp`"),
                    Term::Ctor(id, c, _) if *id == comp => {
                        panic!("`{name}` has a `Comp` constructor ({c})")
                    }
                    Term::Ctor(id, 0, _) if *id == row => empty_rows += 1,
                    Term::Ctor(id, _, _) if *id == row => panic!("`{name}` has an `Ops` row"),
                    Term::Def(id) => assert_ne!(*id, run_pure, "`{name}` runs `runPure`"),
                    _ => {}
                }
            }
        }
        assert!(empty_rows > 0, "`{name}` has no `Empty` row");
    }
}

/// A call that does perform an ability is still refused where none is
/// allowed: it isn't run in place.
#[test]
fn a_call_that_performs_is_still_refused_in_a_pure_place() {
    let mut session = Session::new();
    let errors = session
        .load(
            "test.sw",
            "import Std (Abort)\n\
             theorem bad (c: () -> {Abort} Nat): c () = c () := rfl\n",
        )
        .expect_err("`c ()` performs `Abort`");
    assert_eq!(errors[0].code, "E-ABILITY");
}
