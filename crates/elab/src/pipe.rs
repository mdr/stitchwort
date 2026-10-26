//! Pipe forward (docs/syntax.md): `x |> f a b` is `f x a b`, the value going
//! first, as with dot notation (D304): `x.f a`, `x |> .f a`, `x |> T.f a`
//! and `T.f x a` all put `x` in the same place.
//!
//! `x` is elaborated first, so its type can tell the call what the other
//! arguments are: in `people |> List.map (p => p.name)`, `p` is a `Person`.
//! Since `x` is the first explicit argument, that's ordinary application
//! order.
//!
//! Only a pure pipe comes here; `effects.rs` runs `x` first when something
//! performs operations, and comes back here if the call itself doesn't.

use std::rc::Rc;

use stitchwort_core::value::Closure;
use stitchwort_core::{Icit, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{BinOp, Expr};

use crate::check::{
    Arg, Ctx, Piped, Result, apply_args, check, infer, infer_app, infer_head, insert, known_head,
};

/// `x |> f == y` is `x |> (f == y)`, since `|>` binds looser than the
/// comparisons: when that pipe fails to type, a note says so and suggests
/// brackets. `f` is the pipe's right side.
pub(crate) fn compared_pipe_note(error: Diagnostic, f: &Expr) -> Diagnostic {
    let Expr::Binary(op, _, _) = f else {
        return error;
    };
    let comparison = matches!(
        op,
        BinOp::EqEq | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le
    );
    if error.code != "E-TYPE-MISMATCH" || !comparison {
        return error;
    }
    let op = op.symbol();
    error.with_note(format!(
        "`|>` binds looser than `{op}`, so `x |> f {op} y` pipes `x` into the whole comparison \
         `f {op} y`; to compare the result of the pipe, write brackets: `(x |> f) {op} y`"
    ))
}

/// `value |> f` as the call it stands for, `f value …`: `value` goes before
/// the arguments written after `f`'s head. For a lambda (or anything else
/// that isn't a call), `f value`.
pub(crate) fn as_call(value: Expr, f: &Expr) -> Expr {
    if matches!(f, Expr::Lam(..) | Expr::TypedLam(..)) {
        return Expr::App(Box::new(f.clone()), Box::new(value));
    }
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = f;
    while let Expr::App(g, a) = head {
        args.push(a);
        head = g;
    }
    let mut call = Expr::App(Box::new(head.clone()), Box::new(value));
    for arg in args.into_iter().rev() {
        call = Expr::App(Box::new(call), Box::new(arg.clone()));
    }
    call
}

/// `value |> f`.
pub(crate) fn infer_pipe(cx: &mut Ctx, value: &Expr, f: &Expr) -> Result<(Term, Value)> {
    let (head, mut args) = crate::check::spine(f);
    // A number literal takes its type from where it's used: `5 |> f` is
    // `f 5`, whatever number type `f` takes.
    if crate::numbers::any_literal(value) && !matches!(f, Expr::Lam(..) | Expr::TypedLam(..)) {
        args.insert(0, Arg::Explicit(value));
        return infer_app(cx, head, &args);
    }
    // A computation piped into a parameter of computation type is passed,
    // not run (stage 0 of docs/proposals/effect-polymorphism.md).
    let (term, ty) = if crate::effects::piped_passed(cx, f)? {
        crate::check::infer_unrun(cx, value)?
    } else {
        infer(cx, value)?
    };
    let (term, ty) = insert(cx, term, ty)?;
    let piped = Piped {
        term,
        ty,
        span: f.span(),
        dot: false,
    };
    if let Expr::Lam(..) | Expr::TypedLam(..) = f {
        return lambda(cx, f, piped);
    }
    if let Some(known) = known_head(cx, head) {
        if let Expr::Var(name) = head {
            if let Some(level) = cx.lookup(&name.text) {
                cx.e.note_local(cx, name, &cx.types[level]);
            } else if let Ok(Some((_, ty))) = cx.local(&name.text) {
                cx.note_local_use(name, &ty);
            } else {
                cx.e.note_name(name);
            }
        }
        // The value piped in is the first positional argument: with named
        // arguments, it fills the first explicit parameter they don't
        // (docs/proposals/named-arguments.md §4.4).
        args.insert(0, Arg::Piped(&piped));
        if let Some(defaults) = crate::defaults::of_head(cx, &known.0) {
            return crate::defaults::apply(cx, known, defaults, &args);
        }
        return apply_args(cx, known, &args);
    }
    let call = match head {
        // `x |> r.g a`: `r.g` as dot notation makes it, then `x`, then `a`.
        Expr::Field(recv, field) => crate::dot::infer_dot(cx, recv, field, &[])?,
        _ => infer_head(cx, head)?,
    };
    args.insert(0, Arg::Piped(&piped));
    apply_args(cx, call, &args)
}

/// `x |> y => body`: the lambda is checked as a function from `x`'s type,
/// and applied to `x`.
fn lambda(cx: &mut Ctx, f: &Expr, piped: Piped) -> Result<(Term, Value)> {
    let g = cx.g();
    let name: Name = match f {
        Expr::Lam(names, _, _) => names[0].text.as_str().into(),
        Expr::TypedLam(name, ..) => name.text.as_str().into(),
        _ => unreachable!("only called with a lambda"),
    };
    let mark = cx.mark();
    cx.bind_hidden(name.clone(), piped.ty.clone());
    let cod = cx.fresh_meta();
    cx.reset(mark);
    let cod = Closure {
        env: cx.env.as_slice().into(),
        body: Rc::new(cod),
    };
    let pi = Value::Pi(name, Icit::Explicit, Rc::new(piped.ty.clone()), cod.clone());
    let lam = check(cx, f, &pi)?;
    let ty = cod.apply(g, cx.eval(&piped.term)?)?;
    // Annotated for the kernel, which doesn't infer a lambda's type.
    let ann = Term::Ann(Rc::new(lam), Rc::new(cx.quote(&pi)?));
    Ok((Term::app(ann, piped.term), ty))
}
