//! Binding instead of evaluating (docs/proposals/checker-evaluation.md,
//! option (a)).
//!
//! The evaluator is strict, so putting an argument's value into a type
//! computes the argument completely, and the kernel, checking the result,
//! computes it again. Where only the type of a use of the argument is
//! needed, and that type doesn't depend on the argument's value, the use is
//! elaborated with a variable in its place, and the program is
//! `(\x => use x) arg`: exactly how a pure `let` is elaborated. Neither the
//! elaborator nor the kernel then computes `arg` (the kernel's application
//! rule computes an argument only if the function's type mentions it), and
//! at run time `arg` is computed once, before the use, as it was before:
//! application is strict, so nothing is reordered, repeated or dropped.
//!
//! Where the type might depend on the argument (it mentions the variable at
//! all, even inside a stuck call `F x`), everything the attempt did is
//! undone and the caller does what it did before.

use std::rc::Rc;

use stitchwort_core::value::{eval, unused};
use stitchwort_core::{Icit, Term, Value};

use crate::check::{Ctx, Result};

/// Whether computing `term` costs nothing worth avoiding: it's built from
/// variables, literals and constructors only (a text literal, `Just 3`).
/// Binding those would only make the program longer.
pub(crate) fn cheap(term: &Term) -> bool {
    term.subterms().all(|(t, _)| {
        matches!(
            t,
            Term::Loc(..)
                | Term::Var(_)
                | Term::Nat(_)
                | Term::Chars(_)
                | Term::Sort(_)
                | Term::Refl
                | Term::Ctor(..)
        )
    })
}

/// `use arg`, for `arg : dom` (already checked), elaborated without
/// computing `arg`: `(\name => use name) arg`, if the use's type doesn't
/// depend on `arg`. `use` elaborates the use, given the term standing for
/// the argument, and gives it with its type; `whole` gives the type of the
/// use's term from that type, if they differ (an operation's result type,
/// and its computation type). The result is the term and the use's type.
///
/// `None` (with everything undone) if `arg` is cheap anyway, or the type
/// might depend on it, or `use` fails with the variable (the caller then
/// elaborates it with `arg`, and reports any error from that).
pub(crate) fn bind_argument(
    cx: &mut Ctx,
    name: &str,
    dom: &Value,
    arg: &Term,
    use_: impl FnOnce(&mut Ctx, Term) -> Result<(Term, Value)>,
    whole: impl FnOnce(&Ctx, &Value) -> Result<Value>,
) -> Result<Option<(Term, Value)>> {
    if cheap(arg) {
        return Ok(None);
    }
    crate::undo::transaction(cx, |cx| {
        let mark = cx.mark();
        cx.bind_hidden(name.into(), dom.clone());
        let (inner, ty) = match use_(cx, Term::Var(0)) {
            Ok(found) => found,
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(_) => return Ok(None),
        };
        let ty_term = cx.quote(&ty)?;
        if ty_term.mentions(0) {
            return Ok(None);
        }
        let whole_term = cx.quote(&whole(cx, &ty)?)?;
        if whole_term.mentions(0) {
            return Ok(None);
        }
        cx.reset(mark);
        let lam = Term::Lam(name.into(), Icit::Explicit, Rc::new(inner));
        let pi = Term::Pi(
            name.into(),
            Icit::Explicit,
            Rc::new(cx.quote(dom)?),
            Rc::new(whole_term),
        );
        // The use's type, outside the binder: it doesn't mention it.
        let mut env = cx.env.clone();
        env.push(unused());
        let ty = eval(cx.g(), &env, &ty_term)?;
        Ok(Some((
            Term::app(Term::Ann(Rc::new(lam), Rc::new(pi)), arg.clone()),
            ty,
        )))
    })
}
