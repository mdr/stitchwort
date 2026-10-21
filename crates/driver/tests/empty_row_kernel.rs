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
/// not a conversion between `{} Nat` and `Nat`.
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
