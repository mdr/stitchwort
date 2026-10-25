//! `x in c`: membership in a list, a set or a map's keys (D1201,
//! docs/proposals/logic-notation.md).
//!
//! It's a proposition, chosen by the type of `c`:
//! - on a list, `List.Mem x c` (element first, D1199);
//! - on a `Set` or a `Map`, `c.contains x = True`.
//!
//! Where a `Bool` is expected it's decided, as `a <= b` is: on a list by
//! `List.decMem` (an instance, so `if h: x in xs` works too), and on a set
//! or a map it's `c.contains x` itself. `x !in c` is parsed as `!(x in c)`,
//! so it follows `!`'s two readings.
//!
//! Each form is elaborated as the expression it stands for, written with
//! names in full, so the terms (and hashes) are those of the long forms.

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{Term, Value};
use stitchwort_syntax::ast::{BinOp, Expr, Name};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Result, check, infer};
use crate::{Ctx, Global};

/// What `c` in `x in c` is.
enum Container {
    /// A list, or a type not known yet (taken to be a list).
    List,
    /// A `Set`, or a `Map` (its keys).
    Keys,
}

/// `x in c` with nothing expected: the proposition.
pub(crate) fn infer_member(
    cx: &mut Ctx,
    op: Span,
    elem: &Expr,
    container: &Expr,
) -> Result<(Term, Value)> {
    let prop = match container_kind(cx, container)? {
        Container::List => list_mem(op, elem, container),
        Container::Keys => keys_prop(op, elem, container),
    };
    infer(cx, &prop)
}

/// `x in c` against `expected`: on a set or a map where a `Bool` is
/// expected, `c.contains x`; otherwise the proposition (which a `Bool`
/// expected decides).
pub(crate) fn check_member(
    cx: &mut Ctx,
    op: Span,
    elem: &Expr,
    container: &Expr,
    expected: &Value,
) -> Result<Term> {
    let expr = match container_kind(cx, container)? {
        Container::List => list_mem(op, elem, container),
        Container::Keys if is_bool(cx, expected)? => contains(op, elem, container),
        Container::Keys => keys_prop(op, elem, container),
    };
    check(cx, &expr, expected)
}

fn is_bool(cx: &Ctx, ty: &Value) -> Result<bool> {
    Ok(matches!(force(cx.g(), ty.clone())?,
        Value::Data(d, _) if cx.g().registry.is_data(Builtin::Bool, d)))
}

/// The kind of `container`, from its type, worked out and then forgotten:
/// the expression it becomes elaborates it again.
fn container_kind(cx: &mut Ctx, container: &Expr) -> Result<Container> {
    let snapshot = crate::undo::Snapshot::take(cx);
    let found = infer(cx, container);
    let ty = match found {
        Ok((_, ty)) => force(cx.g(), ty),
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        // Its own error is reported when it's elaborated as part of the
        // proposition.
        Err(_) => {
            snapshot.restore(cx);
            return Ok(Container::List);
        }
    };
    let kind = match &ty {
        Ok(Value::Data(d, _)) => {
            let g = cx.g();
            if g.registry.is_data(Builtin::List, *d) {
                Some(Container::List)
            } else if g.registry.loaded_data(Builtin::Map) == Some(*d)
                || matches!(cx.e.named("Std.Set"), Some((Global::Data(set), _)) if set == d)
            {
                Some(Container::Keys)
            } else {
                None
            }
        }
        Ok(Value::Neutral(Head::Meta(_), _)) => Some(Container::List),
        _ => None,
    };
    let shown = match (&kind, &ty) {
        (None, Ok(ty)) => Some(cx.show(ty)),
        _ => None,
    };
    snapshot.restore(cx);
    match kind {
        Some(kind) => Ok(kind),
        None => Err(Diagnostic::error(
            "E-TYPE-MISMATCH",
            "`in` needs a list, a set or a map on its right",
        )
        .with_label(
            container.span(),
            match shown {
                Some(ty) => format!("this is a `{ty}`"),
                None => "this isn't a list, a set or a map".to_string(),
            },
        )
        .with_note(
            "`x in xs` is `List.Mem x xs` on a list, and `s.contains x = True` on a set or a \
             map (its keys)",
        )),
    }
}

fn var(text: &str, span: Span) -> Expr {
    Expr::Var(Name {
        text: text.to_string(),
        span,
    })
}

fn app(f: Expr, a: &Expr) -> Expr {
    Expr::App(Box::new(f), Box::new(a.clone()))
}

/// `Std.List.Mem elem container`, its head at the operator.
fn list_mem(op: Span, elem: &Expr, container: &Expr) -> Expr {
    app(app(var(LIST_MEM, op), elem), container)
}

/// `container.contains elem`, the name at the operator.
fn contains(op: Span, elem: &Expr, container: &Expr) -> Expr {
    let field = Expr::Field(
        Box::new(container.clone()),
        Name {
            text: "contains".to_string(),
            span: op,
        },
    );
    app(field, elem)
}

/// `container.contains elem = True`.
fn keys_prop(op: Span, elem: &Expr, container: &Expr) -> Expr {
    Expr::Binary(
        BinOp::Eq,
        Box::new(contains(op, elem, container)),
        Box::new(var("Std.Bool.True", op)),
    )
}

/// The proposition `x in xs` is on a list.
pub(crate) const LIST_MEM: &str = "Std.List.Mem";

/// The instance that decides it.
pub(crate) const LIST_DEC_MEM: &str = "Std.List.decMem";
