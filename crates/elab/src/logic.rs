//! `a && b`, `a || b` and `not a`, on `Bool`s or on propositions
//! (docs/syntax.md, "Expressions").
//!
//! Each has two readings:
//! - As a `Bool`: `a && b` is `if a then b else False` and `a || b` is
//!   `if a then True else b`, so `b` is only evaluated (and its operations
//!   only performed) when it's needed; `not a` is `Bool.not a`. Each operand
//!   is a condition, as `if` reads one: a `Bool`, or failing that a
//!   proposition with a decision procedure, decided. As in that `if`, when
//!   `a` is a proposition `b` is checked knowing that it holds (`a && b`) or
//!   doesn't (`a || b`), so `n != 0 && len % n == 0` finds `%`'s proof.
//! - As a proposition: `And a b`, `Or a b` and `Not a`, each operand a
//!   proposition.
//!
//! Where a proposition is expected (a type, as in `if h : p && q`), it's the
//! proposition. Otherwise (a `Bool` expected, or nothing known) the `Bool`
//! reading is tried first, and only if it fails, with everything it did
//! undone, the proposition, as `if c` does. If both fail, the `Bool`
//! reading's error is reported.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::force;
use stitchwort_core::{DefId, Icit, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{BinOp, Expr, Name as AstName};

use crate::check::{Result, builtin_ctor, builtin_data, builtin_def, check, check_type};
use crate::{Ctx, Global};

/// One of the logical forms.
#[derive(Clone, Copy)]
pub(crate) enum Logic<'a> {
    And(&'a Expr, &'a Expr),
    Or(&'a Expr, &'a Expr),
    /// `not a`, with the library's `Bool.not`.
    Not(&'a Expr, DefId),
}

impl Logic<'_> {
    fn symbol(self) -> &'static str {
        match self {
            Logic::And(..) => "&&",
            Logic::Or(..) => "||",
            Logic::Not(..) => "not",
        }
    }
}

/// `expr` as a logical form: `a && b`, `a || b`, or `not a` where `not` is
/// the library's (not a local variable or a declaration of the module's own
/// that happens to be called `not`).
pub(crate) fn classify<'a>(cx: &Ctx, expr: &'a Expr) -> Option<Logic<'a>> {
    match expr {
        Expr::Binary(BinOp::And, a, b) => Some(Logic::And(a, b)),
        Expr::Binary(BinOp::Or, a, b) => Some(Logic::Or(a, b)),
        Expr::App(f, a) if !matches!(**a, Expr::NamedArg(..)) => {
            let Expr::Var(name) = &**f else {
                return None;
            };
            if cx.lookup(&name.text).is_some() {
                return None;
            }
            match cx.e.named(&name.text) {
                Some((Global::Def(id), _)) if cx.g().registry.is_def(Builtin::BoolNot, *id) => {
                    Some(Logic::Not(a, *id))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// A condition, as `if c` reads it.
pub(crate) enum Condition {
    /// A `Bool`.
    Bool(Term),
    /// A proposition, and a decision procedure for it.
    Decided {
        prop: Term,
        decision: crate::bind::Decision,
    },
}

/// `cond` as a `Bool`; or if that fails, with everything it did undone, as a
/// proposition with a decision procedure. If both fail, the `Bool` reading's
/// error, unless `cond` is a proposition nothing decides. `what` is the
/// syntax taking the condition, for that error.
///
/// When the `Bool` reading's error is the one reported, the state is the
/// `Bool` reading's too. The local definitions it met (`local.rs`) may be
/// why it failed: a call of one is a frozen metavariable until it's lifted,
/// and the declaration is elaborated again once they're admitted, which
/// needs their drafts. Undoing the reading drops them, so if it made any,
/// it's done again.
pub(crate) fn condition(cx: &mut Ctx, cond: &Expr, what: &str) -> Result<Condition> {
    let bool_ty = Value::Data(builtin_data(cx, Builtin::Bool)?, Vec::new());
    let snapshot = crate::undo::Snapshot::take(cx);
    let outer = cx.e.condition.replace(std::ptr::from_ref(cond) as usize);
    let as_bool = check(cx, cond, &bool_ty);
    cx.e.condition.set(outer);
    let not_bool = match as_bool {
        Ok(cond) => return Ok(Condition::Bool(cond)),
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(not_bool) => not_bool,
    };
    let drafted = snapshot.drafted_since(cx);
    snapshot.restore(cx);
    let before = crate::undo::Snapshot::take(cx);
    match decided(cx, cond, what, &not_bool)? {
        Some(found) => Ok(found),
        None if drafted => {
            before.restore(cx);
            check(cx, cond, &bool_ty).map(Condition::Bool)
        }
        None => Err(not_bool),
    }
}

/// `cond` as a decided proposition, for [`condition`]; `None` if the `Bool`
/// reading's error `not_bool` is the one to report.
fn decided(
    cx: &mut Ctx,
    cond: &Expr,
    what: &str,
    not_bool: &Diagnostic,
) -> Result<Option<Condition>> {
    let Some((prop, Sort::Prop)) = crate::undo::attempt(cx, |cx| check_type(cx, cond))? else {
        return Ok(None);
    };
    // No decision procedure. If the `Bool` reading already found an operand
    // nothing decides (`x < 3 && g = h`), that's the more precise error.
    // Otherwise say so at the condition, keeping the search's explanations
    // (its notes after the first).
    let decision = match crate::bind::decide(cx, &prop) {
        Ok(decision) => decision,
        Err(e)
            if e.code == "E-AUTO-NONE"
                && matches!(not_bool.code, "E-AUTO-NONE" | "E-INSTANCE-NONE") =>
        {
            return Ok(None);
        }
        Err(mut e) if e.code == "E-AUTO-NONE" && !e.notes.is_empty() => {
            e.labels.clear();
            e.notes[0] = format!(
                "`{what}` takes a `Bool`, or a proposition with a decision procedure: an \
                 `instance` returning `Decidable …`"
            );
            return Err(e.with_label(cond.span(), "this is a proposition, and nothing decides it"));
        }
        Err(e) => return Err(e),
    };
    Ok(Some(Condition::Decided { prop, decision }))
}

/// `expr` as a `Bool`: a decided proposition is `Decidable.toBool` of its
/// decision.
pub(crate) fn bool_operand(cx: &mut Ctx, expr: &Expr, what: &str) -> Result<Term> {
    Ok(match condition(cx, expr, what)? {
        Condition::Bool(term) => term,
        Condition::Decided { prop, decision } => decision.into_bool(cx, prop)?,
    })
}

/// The `Bool` reading.
fn as_bool(cx: &mut Ctx, logic: Logic) -> Result<Term> {
    let what = logic.symbol();
    let (a, b) = match logic {
        Logic::Not(a, not) => {
            let a = bool_operand(cx, a, what)?;
            return Ok(Term::app(Term::Def(not), a));
        }
        Logic::And(a, b) | Logic::Or(a, b) => (a, b),
    };
    let and = matches!(logic, Logic::And(..));
    let bool_ty = Term::Data(builtin_data(cx, Builtin::Bool)?, Vec::new());
    let unit = Value::Data(builtin_data(cx, Builtin::Unit)?, Vec::new());
    let ite = builtin_def(cx, Builtin::IfThenElse)?;
    let ite = Term::app_icit(Term::Def(ite), bool_ty.clone(), Icit::Implicit);
    // `b` is checked as the branch of `if a` that needs it: assuming `a`
    // (in `a && b`) or `Not a` (in `a || b`) when `a` is a proposition, so
    // `n != 0 && len % n == 0` finds `%`'s proof; or, for a `Bool` `a`, an
    // unused proof of `Unit`, as the branches of `Bool.ifThenElse` take.
    let (head, a, b) = match condition(cx, a, what)? {
        Condition::Bool(a) => {
            let mark = cx.mark();
            cx.bind("_", unit);
            let b = bool_operand(cx, b, what);
            cx.reset(mark);
            (ite, a, b?)
        }
        Condition::Decided { prop, decision } => {
            let prop_value = cx.eval(&prop)?;
            let assumption = if and {
                prop_value
            } else {
                let not = cx.eval(&Term::Def(builtin_def(cx, Builtin::Not)?))?;
                stitchwort_core::value::apply(cx.g(), not, prop_value)?
            };
            let before = cx.e.obligations.borrow().len();
            let mark = cx.mark();
            cx.bind("_", assumption);
            let b = bool_operand(cx, b, what);
            cx.reset(mark);
            let b = b?;
            if needs_proofs(cx, before)? {
                // `if _ : a then b else False`, as `if` makes it: `elimDec`.
                let elim = builtin_def(cx, Builtin::ElimDec)?;
                let head = Term::app_icit(
                    Term::app_icit(Term::Def(elim), prop, Icit::Implicit),
                    bool_ty,
                    Icit::Implicit,
                );
                (head, decision.term(cx)?, b)
            } else {
                // Nothing in `b` can have used the assumption (only the
                // search for an auto argument's proof sees it), so it's
                // `if a then b else False` on the decision's `Bool`, as
                // ever: the same term as `Bool.and (toBool …) b` reads, so
                // the library's facts about `&&` on `Bool`s apply to it.
                (ite, decision.into_bool(cx, prop)?, b)
            }
        }
    };
    let constant = |cx: &Ctx, which| -> Result<Term> {
        let (d, c) = builtin_ctor(cx, which)?;
        Ok(Term::Ctor(d, c, Vec::new()))
    };
    let (then, otherwise) = if and {
        (b, constant(cx, Builtin::False)?)
    } else {
        (constant(cx, Builtin::True)?, b)
    };
    let branch = |body| Term::Lam("_".into(), Icit::Explicit, Rc::new(body));
    Ok(Term::app(
        Term::app(Term::app(head, a), branch(then)),
        branch(otherwise),
    ))
}

/// Whether an obligation recorded since the first `before` needs a proof:
/// an auto argument (not an instance to find), whose search sees the
/// hypotheses in scope.
fn needs_proofs(cx: &Ctx, before: usize) -> Result<bool> {
    let goals: Vec<Value> = cx.e.obligations.borrow()[before..]
        .iter()
        .map(|ob| ob.goal.clone())
        .collect();
    for goal in &goals {
        if crate::interfaces::interface_goal(cx.e, goal)?.is_none() {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The proposition reading.
pub(crate) fn as_prop(cx: &mut Ctx, logic: Logic) -> Result<Term> {
    let what = logic.symbol();
    let operand = |cx: &mut Ctx, e: &Expr| -> Result<Term> {
        let note = format!(
            "`{what}` here is on propositions; for a `Bool` `b`, the proposition that it's \
             true is `b = True`"
        );
        match check_type(cx, e) {
            Ok((term, Sort::Prop)) => Ok(term),
            Ok(_) => Err(
                Diagnostic::error("E-TYPE-MISMATCH", "expected a proposition")
                    .with_label(e.span(), "this is a type of data, not a proposition")
                    .with_note(note),
            ),
            Err(err) if err.code == "E-NOT-A-TYPE" => Err(err.with_note(note)),
            Err(err) => Err(err),
        }
    };
    Ok(match logic {
        Logic::Not(a, _) => {
            let a = operand(cx, a)?;
            Term::app(Term::Def(builtin_def(cx, Builtin::Not)?), a)
        }
        Logic::And(a, b) | Logic::Or(a, b) => {
            let a = operand(cx, a)?;
            let b = operand(cx, b)?;
            let d = builtin_data(
                cx,
                match logic {
                    Logic::And(..) => Builtin::And,
                    _ => Builtin::Or,
                },
            )?;
            Term::data(d, vec![a, b])
        }
    })
}

/// With nothing expected: the `Bool` reading, or failing that the
/// proposition.
pub(crate) fn infer(cx: &mut Ctx, logic: Logic) -> Result<(Term, Value)> {
    let snapshot = crate::undo::Snapshot::take(cx);
    let not_bool = match as_bool(cx, logic) {
        Ok(term) => {
            let bool_data = builtin_data(cx, Builtin::Bool)?;
            return Ok((term, Value::Data(bool_data, Vec::new())));
        }
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(not_bool) => not_bool,
    };
    snapshot.restore(cx);
    match crate::undo::attempt(cx, |cx| as_prop(cx, logic))? {
        Some(term) => Ok((term, Value::Sort(Sort::Prop))),
        None => Err(not_bool),
    }
}

/// Against `expected`: a `Bool`, a proposition where a type is expected, and
/// otherwise as `infer` finds it.
pub(crate) fn check_against(cx: &mut Ctx, logic: Logic, expected: &Value) -> Result<Term> {
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    let (term, found) = match force(cx.g(), expected.clone())? {
        Value::Data(d, _) if d == bool_data => return as_bool(cx, logic),
        Value::Sort(Sort::Prop) => return as_prop(cx, logic),
        Value::Sort(_) => (as_prop(cx, logic)?, Value::Sort(Sort::Prop)),
        _ => infer(cx, logic)?,
    };
    crate::check::compare(cx, term, &found, expected)
}

/// The `Bool` reading as an `if`, for operands that perform operations:
/// `a && b` is `if a then (if b then True else False) else False`, and
/// `a || b` is `if a then True else (if b then True else False)`. The inner
/// `if` makes `b` a condition, as `a` is.
pub(crate) fn as_if(op: BinOp, a: &Expr, b: &Expr) -> Expr {
    let span = a.span().to(b.span());
    let constant = |which: &str| {
        Expr::Var(AstName {
            text: format!("Std.Bool.{which}"),
            span,
        })
    };
    let ite = |cond: Expr, then: Expr, otherwise: Expr| Expr::If {
        binder: None,
        cond: Box::new(cond),
        then: Box::new(then),
        otherwise: Box::new(otherwise),
        span,
    };
    let b = ite(b.clone(), constant("True"), constant("False"));
    match op {
        BinOp::And => ite(a.clone(), b, constant("False")),
        _ => ite(a.clone(), constant("True"), b),
    }
}
