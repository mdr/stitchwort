//! Pipe forward (docs/syntax.md): `x |> f a b` is `f a b x`, elaborated
//! with `x` first, so its type can tell the call what the other arguments
//! are: in `people |> List.map (p => p.name)`, `p` is a `Person`.
//!
//! As dot notation does with its receiver (`dot.rs`), `x` is inferred, then
//! the parameter it fills is found by walking `f`'s type, with variables
//! standing for the written arguments, and compared with `x`'s type before
//! those arguments are checked. The walk is speculative: if it can't be
//! made (`f`'s type isn't known, or the parameter's type depends on a
//! written argument's value), what it did is undone and the call is
//! elaborated left to right, comparing `x` with its parameter when reached.
//!
//! Only a pure pipe comes here; `effects.rs` runs `x` first when something
//! performs operations, and comes back here if the call itself doesn't.

use std::rc::Rc;

use stitchwort_core::value::{Closure, force, quote};
use stitchwort_core::{Icit, Name, Term, Value};
use stitchwort_syntax::ast::Expr;

use crate::check::{
    Arg, Ctx, Piped, Result, Supply, apply_args, apply_args_with, check, implicit_arg, infer,
    infer_app, infer_head, insert, known_head, piped_mismatch,
};

/// `value |> f`.
pub(crate) fn infer_pipe(cx: &mut Ctx, value: &Expr, f: &Expr) -> Result<(Term, Value)> {
    let mut args = Vec::new();
    let mut head = f;
    while let Expr::App(g, a) = head {
        args.push(match a.as_ref() {
            Expr::NamedArg(name, value, _) => Arg::Named(name, value),
            other => Arg::Explicit(other),
        });
        head = g;
    }
    args.reverse();
    // A number literal takes its type from where it's used: `5 |> f` is
    // `f 5`, whatever number type `f` takes.
    if crate::numbers::any_literal(value) && !matches!(f, Expr::Lam(..) | Expr::TypedLam(..)) {
        args.push(Arg::Explicit(value));
        return infer_app(cx, head, &args);
    }
    let (term, ty) = infer(cx, value)?;
    let (term, ty) = insert(cx, term, ty)?;
    let piped = Piped {
        term,
        ty,
        span: f.span(),
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
        return receiver_first(cx, known, &args, &piped);
    }
    let call = match head {
        // `x |> r.g a`: `r.g a` as dot notation makes it, then `x`.
        Expr::Field(recv, field) => {
            let call = crate::dot::infer_dot(cx, recv, field, &args)?;
            args.clear();
            call
        }
        _ => infer_head(cx, head)?,
    };
    args.push(Arg::Piped(&piped));
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

/// `x |> f args`, where `f` is a variable or a definition: `x` is compared
/// with its parameter before `args` are checked, if that can be found.
fn receiver_first(
    cx: &mut Ctx,
    head: (Term, Value),
    args: &[Arg],
    piped: &Piped,
) -> Result<(Term, Value)> {
    let mut all = args.to_vec();
    all.push(Arg::Piped(piped));
    let snapshot = crate::undo::Snapshot::take(cx);
    let Some((dom, mut supply)) = parameter(cx, &head.1, args)? else {
        snapshot.restore(cx);
        return apply_args(cx, head, &all);
    };
    if !cx.unify(&piped.ty, &dom)? {
        return Err(piped_mismatch(cx, piped, &dom));
    }
    apply_args_with(cx, head, &all, &mut supply)
}

/// The type of the explicit parameter after those `args` fill, in a
/// function of type `ty`, with metavariables for the implicit arguments
/// before it (as `apply_args_with` takes them, in order). `None` if the
/// type isn't known that far, or depends on the arguments' values, or an
/// auto parameter's proposition might.
fn parameter(cx: &mut Ctx, ty: &Value, args: &[Arg]) -> Result<Option<(Value, Supply)>> {
    let g = cx.g();
    let base = cx.level();
    let mut ty = ty.clone();
    let mut supply = Supply::new();
    let mut written = 0;
    for arg in args {
        let stop = |x: &Name, icit: Icit| match arg {
            Arg::Named(name, _) => icit.is_implicit() && **x == *name.text,
            _ => icit == Icit::Explicit,
        };
        let Some((icit, _, cod)) = implicits(cx, &mut ty, &mut supply, written, stop)? else {
            return Ok(None);
        };
        if icit == Icit::Auto {
            return Ok(None);
        }
        // A variable standing for the argument, outside the context.
        ty = cod.apply(g, Value::var(base + written))?;
        written += 1;
    }
    let stop = |_: &Name, icit: Icit| icit == Icit::Explicit;
    let Some((_, dom, _)) = implicits(cx, &mut ty, &mut supply, written, stop)? else {
        return Ok(None);
    };
    let quoted = quote(g, base + written, &dom)?;
    if (0..written).any(|i| quoted.mentions(i)) {
        return Ok(None);
    }
    Ok(Some((dom, supply)))
}

/// Gives the implicit parameters at the front of `ty` metavariables, added
/// to `supply`, until `stop` says to stop at one: its kind, type and
/// codomain. `None` at anything else, or at an auto parameter after
/// `written` arguments (its proposition could mention them).
fn implicits(
    cx: &mut Ctx,
    ty: &mut Value,
    supply: &mut Supply,
    written: usize,
    stop: impl Fn(&Name, Icit) -> bool,
) -> Result<Option<(Icit, Value, Closure)>> {
    let g = cx.g();
    loop {
        match force(g, ty.clone())? {
            Value::Pi(x, icit, dom, cod) if stop(&x, icit) => {
                return Ok(Some((icit, (*dom).clone(), cod)));
            }
            Value::Pi(_, Icit::Auto, _, _) if written > 0 => return Ok(None),
            Value::Pi(_, icit, dom, cod) if icit.is_implicit() => {
                let meta = implicit_arg(cx, icit, &dom);
                let value = cx.eval(&meta)?;
                supply.push_back(meta);
                *ty = cod.apply(g, value)?;
            }
            _ => return Ok(None),
        }
    }
}
