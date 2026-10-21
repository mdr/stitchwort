//! A pattern `let` on a tuple or a record binds its names to projections
//! (docs/proposals/let.md §7):
//!
//! ```text
//! let (a, b) := e     is     let %p := e
//!                            let a := %p.fst
//!                            let b := %p.snd
//! ```
//!
//! each a transparent `let`, so the rest of the block computes even when `e`
//! is an unknown, where the one-alternative `match` it otherwise means would
//! be stuck. The hidden `%p` computes `e` once; there's none when `e` is a
//! variable. Nested tuple and record patterns repeat this, through a hidden
//! `let` per level. `%p` can't be written, and as a `let` it never appears
//! in a computed type, so diagnostics don't show it.
//!
//! In a proof (the expected type is evidently a proposition), the `match`
//! is kept: there, splitting `e` into a pair refines the goal, which is what
//! a proof by `let (a, b) := p` wants (`examples/accept/let-patterns.sw`,
//! `swapTwice`). Patterns with anything but variables, `_`, tuples and
//! records stay `match`es.

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::force;
use stitchwort_core::{DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Expr, MatchKind, Pattern};

use crate::check::{Ctx, Result, builtin_data, builtin_def, check, infer, insert};

/// The pattern, right-hand side and rest of a pattern `let` that can be
/// projections.
fn parts(expr: &Expr) -> Option<(&Pattern, &Expr, &Expr)> {
    let Expr::Match {
        scrutinees,
        alts,
        kind: MatchKind::Let,
        ..
    } = expr
    else {
        return None;
    };
    let ([s], [alt]) = (scrutinees.as_slice(), alts.as_slice()) else {
        return None;
    };
    let [pattern] = alt.patterns.as_slice() else {
        return None;
    };
    let top = matches!(pattern, Pattern::Tuple(..) | Pattern::Record { .. });
    (s.name.is_none() && top && simple(pattern)).then_some((pattern, &s.expr, &alt.body))
}

fn simple(p: &Pattern) -> bool {
    match p {
        Pattern::Var(_) | Pattern::Wildcard(_) => true,
        Pattern::Tuple(a, b, _) => simple(a) && simple(b),
        Pattern::Record { fields, .. } => fields.iter().all(|(_, p)| simple(p)),
        _ => false,
    }
}

/// Whether `expr`, checked against `goal`, is a pattern `let` made into
/// projections.
pub(crate) fn applies(cx: &Ctx, expr: &Expr, goal: &Value) -> Result<bool> {
    Ok(parts(expr).is_some() && !proposition(cx, goal)?)
}

/// Whether `ty` is evidently a proposition: an equation, a data type in
/// `Prop`, or a function into one.
fn proposition(cx: &Ctx, ty: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(match force(g, ty.clone())? {
        Value::Eq(..) => true,
        Value::Data(d, _) => g.data(d).sort == Sort::Prop,
        Value::Pi(_, _, _, cod) => {
            // A fresh variable no binder in scope has, for the test only.
            proposition(cx, &cod.apply(g, Value::var(usize::MAX - 2))?)?
        }
        _ => false,
    })
}

/// The pattern `let` `expr` (one [`applies`] to), checked against `goal`.
pub(crate) fn check_let(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    let (pattern, value, body) = parts(expr).expect("checked by `applies`");
    let mark = cx.mark();
    let mut lets = Vec::new();
    let result = (|| {
        let level = match variable(cx, value) {
            Some(level) => level,
            None => {
                let (term, ty) = infer(cx, value)?;
                let (term, ty) = insert(cx, term, ty)?;
                bind(cx, None, term, ty, &mut lets)?
            }
        };
        destructure(cx, pattern, level, &mut lets)?;
        check(cx, body, goal)
    })();
    cx.reset(mark);
    let mut term = result?;
    for (x, ty, value) in lets.into_iter().rev() {
        term = Term::let_(x, ty, value, term);
    }
    Ok(term)
}

/// The variable `e` names, if it's one (a local definition isn't).
fn variable(cx: &Ctx, e: &Expr) -> Option<usize> {
    let Expr::Var(x) = e else {
        return None;
    };
    if cx.local(&x.text).ok().flatten().is_some() {
        return None;
    }
    let level = cx.lookup(&x.text)?;
    cx.e.note_local(cx, x, &cx.types[level]);
    Some(level)
}

/// A `let` of `value : ty`, named or hidden: its level.
fn bind(
    cx: &mut Ctx,
    name: Option<&str>,
    value: Term,
    ty: Value,
    lets: &mut Vec<(Name, Term, Term)>,
) -> Result<usize> {
    let shown: Name = name.unwrap_or("%p").into();
    let ty_term = cx.quote(&ty)?;
    lets.push((shown.clone(), ty_term.clone(), value.clone()));
    cx.define(name, shown, ty, ty_term, value)?;
    Ok(cx.level() - 1)
}

/// Binds the names in tuple or record pattern `p` to projections of the
/// variable at `level`.
fn destructure(
    cx: &mut Ctx,
    p: &Pattern,
    level: usize,
    lets: &mut Vec<(Name, Term, Term)>,
) -> Result<()> {
    let g = cx.g();
    let ty = force(g, cx.types[level].clone())?;
    match p {
        Pattern::Tuple(a, b, span) => {
            let pair = builtin_data(cx, Builtin::Pair)?;
            let params = match ty {
                Value::Data(d, params) if d == pair => params,
                other => {
                    let a_ty = cx.fresh_meta();
                    let b_ty = cx.fresh_meta();
                    let expected = Value::Data(pair, vec![cx.eval(&a_ty)?, cx.eval(&b_ty)?]);
                    if !cx.unify(&other, &expected)? {
                        let saved = std::mem::replace(&mut cx.span, *span);
                        let e = cx.mismatch(&other, &expected);
                        cx.span = saved;
                        return Err(e.with_note("a tuple pattern matches a pair"));
                    }
                    let Value::Data(_, params) = force(g, expected)? else {
                        unreachable!("a data type")
                    };
                    params
                }
            };
            let fst = builtin_def(cx, Builtin::Fst)?;
            let snd = builtin_def(cx, Builtin::Snd)?;
            for (def, p) in [(fst, a), (snd, b)] {
                let (term, ty) = project(cx, def, &params, level)?;
                component(cx, p, term, ty, lets)?;
            }
            Ok(())
        }
        Pattern::Record { fields, rest, span } => {
            let pattern = cx.e.record_pattern(fields, *rest, *span, Some(&ty))?;
            let Value::Data(_, params) = ty else {
                unreachable!("`record_pattern` accepts only a record type")
            };
            let projections = cx.e.records[&pattern.data].projections.clone();
            for (i, arg) in pattern.args.iter().enumerate() {
                if matches!(&**arg, Pattern::Wildcard(_)) {
                    continue;
                }
                let Some(def) = projections[i] else {
                    return Err(Diagnostic::error(
                        "E-PROP-ELIM",
                        "this record is a proof, and this field can't be taken out of it",
                    )
                    .with_label(*span, "this pattern")
                    .with_note("use `match` instead"));
                };
                let (term, ty) = project(cx, def, &params, level)?;
                component(cx, arg, term, ty, lets)?;
            }
            Ok(())
        }
        _ => unreachable!("only tuples and records are destructured"),
    }
}

/// Projection `def` (taking the type's parameters implicitly, then a value
/// of it) applied to the variable at `level`, and its type.
fn project(cx: &Ctx, def: DefId, params: &[Value], level: usize) -> Result<(Term, Value)> {
    let g = cx.g();
    let mut term = Term::Def(def);
    let mut ty = g.def(def).ty_value.clone();
    let args = params
        .iter()
        .map(|p| Ok((cx.quote(p)?, p.clone(), Icit::Implicit)))
        .chain(std::iter::once(Ok((
            Term::Var(cx.level() - 1 - level),
            cx.env[level].clone(),
            Icit::Explicit,
        ))))
        .collect::<Result<Vec<_>>>()?;
    for (arg, value, icit) in args {
        let Value::Pi(_, _, _, cod) = force(g, ty)? else {
            unreachable!("a projection takes the parameters and the value")
        };
        ty = cod.apply(g, value)?;
        term = Term::app_icit(term, arg, icit);
    }
    Ok((term, ty))
}

/// A field's pattern `p`, for the projection `term` of type `ty`.
fn component(
    cx: &mut Ctx,
    p: &Pattern,
    term: Term,
    ty: Value,
    lets: &mut Vec<(Name, Term, Term)>,
) -> Result<()> {
    match p {
        Pattern::Wildcard(_) => Ok(()),
        Pattern::Var(x) => bind(cx, Some(&x.text), term, ty, lets).map(|_| ()),
        p => {
            let level = bind(cx, None, term, ty, lets)?;
            destructure(cx, p, level, lets)
        }
    }
}
