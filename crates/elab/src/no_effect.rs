//! `W-NO-EFFECT` (D1702, SW-889): a statement line that performs nothing.
//!
//! Every line of a block but the last, and the `a` of a sequence `a; b`, is
//! run for its effects and its value is dropped. A line that performs no
//! effects can't do anything, so it's a mistake: `shortNumber` missing its
//! `()`, `char` missing its argument, `x + 1`, or `list.map f` written as if
//! it changed `list` (docs/proposals/direct-style-grammars.md §2.5 (3)).
//!
//! A line performs nothing when:
//! - [`crate::effects::may_perform`] says it doesn't, so it's elaborated as
//!   a plain value, and its type is known and isn't a computation type (a
//!   type still unknown might become one, as a call of a parameter whose
//!   type isn't known yet may);
//! - it's a call in the empty row whose computation is a plain value made
//!   one (an effect-polymorphic call whose callbacks are pure, in a pure
//!   definition);
//! - it's a call that performs only through calls whose result is in a bare
//!   row (`List.map f xs`), and elaborated as plain calls, undone afterwards,
//!   its type isn't a computation: the callbacks are pure, so the row is
//!   empty whatever row the line is in.
//!
//! A `()` line, a `handle`, and lines whose type is still unknown never
//! warn. A dropped result of a call that performs (`shortNumber()` read
//! only to skip it) isn't this warning (D1713).

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{Icit, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::Expr;

use crate::check::{Ctx, Result, builtin_data};

pub(crate) const CODE: &str = "W-NO-EFFECT";

/// Whether a line like `expr` is one this warning looks at: `()` is written
/// on purpose, and a `handle`'s body performs, even when all of it is handled.
pub(crate) fn applies(expr: &Expr) -> bool {
    !matches!(expr, Expr::Unit(_) | Expr::Handle { .. })
}

/// Whether `expr` is a call this warning may judge by its elaborated
/// computation (a plain value made one): a variable, application, field or
/// pipe, not a compound whose parts perform.
pub(crate) fn call_like(expr: &Expr) -> bool {
    match expr {
        Expr::Var(_) | Expr::App(..) | Expr::Field(..) | Expr::Pipe(..) => true,
        Expr::Bracketed(e, _) | Expr::Interpolated(e, _) => call_like(e),
        _ => false,
    }
}

/// Records the warning for the statement line `expr`, a plain value of type
/// `ty`, unless its type is unknown or a computation.
pub(crate) fn check_value(cx: &Ctx, expr: &Expr, ty: &Value) -> Result<()> {
    if !applies(expr) {
        return Ok(());
    }
    let forced = force(cx.g(), ty.clone())?;
    if matches!(forced, Value::Neutral(Head::Meta(_), _))
        || crate::effects::comp_parts(cx, &forced)?.is_some()
    {
        return Ok(());
    }
    warn(cx, expr, &forced)
}

/// Whether `expr`, which may perform only through calls whose result is in
/// a bare row, is pure: elaborated as plain calls, undone afterwards, its
/// type isn't a computation. That type, if so.
pub(crate) fn pure_as_plain_calls(cx: &mut Ctx, expr: &Expr) -> Result<Option<Value>> {
    if !applies(expr) || !call_like(expr) {
        return Ok(None);
    }
    if !crate::effects::performs_only_in_bare_rows(cx, expr, None)? {
        return Ok(None);
    }
    let snapshot = crate::undo::Snapshot::take(cx);
    let first_new = cx.e.row_constraints.borrow().len();
    let first_meta = cx.g().metas.borrow().len();
    let found = crate::check::infer_value(cx, expr).and_then(|(_, ty)| {
        while cx.e.retry_rows_from(first_new)? {}
        let ty = force(cx.g(), ty)?;
        let ty = match crate::effects::comp_parts(cx, &ty)? {
            None => ty,
            // A row nothing has settled: the callbacks performed nothing, so
            // it's the empty row, if it was made for this line. One made
            // before it (a callback whose type isn't known yet) may still
            // become an effectful one.
            Some((row, value))
                if row.labels.is_empty()
                    && !row.partial
                    && row.tail.iter().chain(row.div.iter()).all(|v| {
                        matches!(force(cx.g(), v.clone()),
                            Ok(Value::Neutral(Head::Meta(m), _)) if m >= first_meta)
                    }) =>
            {
                force(cx.g(), value)?
            }
            Some(_) => return Ok(None),
        };
        Ok((!matches!(ty, Value::Neutral(Head::Meta(_), _))).then_some(ty))
    });
    snapshot.restore(cx);
    match found {
        Ok(found) => Ok(found),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(_) => Ok(None),
    }
}

/// Records the warning for the statement line `expr`, whose value, of type
/// `ty` (forced), is dropped. Once per line.
pub(crate) fn warn(cx: &Ctx, expr: &Expr, ty: &Value) -> Result<()> {
    if !applies(expr) {
        return Ok(());
    }
    let span = expr.span();
    let note = match ty {
        Value::Pi(_, Icit::Explicit, dom, _) => {
            let unit = builtin_data(cx, Builtin::UnitType).ok();
            let takes_unit = matches!(
                force(cx.g(), (**dom).clone())?,
                Value::Data(d, ref params) if Some(d) == unit && params.is_empty()
            );
            match (named(expr), takes_unit) {
                (Some(name), true) => format!("call it: `{name}()`"),
                (Some(name), false) => {
                    format!("`{name}` is a function missing its arguments: give them to call it")
                }
                (None, true) => "it's a function: call it with `()`".to_string(),
                (None, false) => {
                    "it's a function missing its arguments: give them to call it".to_string()
                }
            }
        }
        _ => "remove the line, or bind its value with `let` if it's meant for later".to_string(),
    };
    let mut seen = cx.e.lambda_warnings.borrow_mut();
    if seen
        .iter()
        .any(|w| w.code == CODE && w.labels.first().is_some_and(|l| l.span == span))
    {
        return Ok(());
    }
    seen.push(
        Diagnostic::warning(
            CODE,
            "this line does nothing: it performs no effects, and its value is dropped",
        )
        .with_label(span, "performs nothing")
        .with_note(note),
    );
    Ok(())
}

/// How to write `expr` in a hint, if it's a name or a field of one.
fn named(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Var(name) => Some(name.text.clone()),
        Expr::Field(recv, field) => named(recv).map(|r| format!("{r}.{}", field.text)),
        Expr::Bracketed(e, _) => named(e),
        _ => None,
    }
}
