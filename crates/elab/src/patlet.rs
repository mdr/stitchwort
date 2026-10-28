//! A pattern `let` (or lambda parameter) on a tuple or a record binds its names to projections
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
//! A constructor pattern of a one-constructor proposition whose fields are
//! all named proofs, `let (Both below above) := e`, binds the same way,
//! through the fields' accessors (`And.left`, `And.right`): the rest of the
//! block, and so a definition's unfolding equation, computes even when the
//! proof `e` doesn't reduce to `Both`.
//!
//! In a proof (the expected type is evidently a proposition), the `match`
//! is kept: there, splitting `e` into a pair refines the goal, which is what
//! a proof by `let (a, b) := p` wants (`examples/accept/let-patterns.sw`,
//! `swapTwice`). Patterns with anything but variables, `_`, tuples, records
//! and such constructors stay `match`es.

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::force;
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Expr, MatchKind, Pattern};

use crate::check::{Ctx, Result, builtin_data, builtin_def, check, infer, insert};
use crate::scope::Resolved;
use crate::{Elaborator, Global};

/// The patterns with their scrutinees, and the rest, of a pattern `let` or
/// pattern lambda that can be projections. A lambda's patterns are all
/// tuples or records, or it stays a `match`.
fn parts(expr: &Expr) -> Option<(Vec<(&Pattern, &Expr)>, &Expr)> {
    let Expr::Match {
        scrutinees,
        alts,
        kind,
        ..
    } = expr
    else {
        return None;
    };
    let [alt] = alts.as_slice() else {
        return None;
    };
    if !matches!(kind, MatchKind::Let | MatchKind::Lambda)
        || scrutinees.len() != alt.patterns.len()
        || (*kind == MatchKind::Let && scrutinees.len() != 1)
    {
        return None;
    }
    let mut out = Vec::new();
    for (s, pattern) in scrutinees.iter().zip(&alt.patterns) {
        let top = matches!(
            pattern,
            Pattern::Tuple(..) | Pattern::Record { .. } | Pattern::Ctor(..)
        );
        if s.name.is_some() || !top || !simple(pattern) {
            return None;
        }
        out.push((pattern, &s.expr));
    }
    Some((out, &alt.body))
}

fn simple(p: &Pattern) -> bool {
    match p {
        Pattern::Var(_) | Pattern::Wildcard(_) => true,
        Pattern::Tuple(a, b, _) => simple(a) && simple(b),
        Pattern::Record { fields, .. } => fields.iter().all(|(_, p)| simple(p)),
        Pattern::Ctor(_, args, _) => args.iter().all(simple),
        _ => false,
    }
}

/// The data type of constructor `name` and each field's accessor, if it's
/// the only constructor of a proposition without indices whose fields are
/// all explicit and have accessors (named proofs, as `And`'s are).
fn proof_ctor(cx: &Ctx, name: &str) -> Option<(DataId, Vec<DefId>)> {
    let Resolved::Found {
        global: Global::Ctor(d, 0),
        rest,
        ..
    } = cx.e.resolve(name)
    else {
        return None;
    };
    let data = cx.g().data(d);
    let single = data.ctors.len() == 1 && data.indices.is_empty();
    if !rest.is_empty() || data.sort != Sort::Prop || !single {
        return None;
    }
    let ctor = &data.ctors[0];
    if ctor.implicit.iter().any(|&i| i) {
        return None;
    }
    let key = cx.e.data_key(d);
    let accessors = ctor
        .fields
        .iter()
        .map(
            |(f, _)| match cx.e.scope.get(&Elaborator::member_key(&key, f)) {
                Some((Global::Def(id), _)) => Some(id),
                _ => None,
            },
        )
        .collect::<Option<Vec<_>>>()?;
    Some((d, accessors))
}

/// Whether every constructor pattern in `p` is one [`proof_ctor`] accepts,
/// with an argument per field.
fn projectable(cx: &Ctx, p: &Pattern) -> bool {
    match p {
        Pattern::Tuple(a, b, _) => projectable(cx, a) && projectable(cx, b),
        Pattern::Record { fields, .. } => fields.iter().all(|(_, p)| projectable(cx, p)),
        Pattern::Ctor(n, args, _) => {
            proof_ctor(cx, &n.text).is_some_and(|(_, fields)| fields.len() == args.len())
                && args.iter().all(|p| projectable(cx, p))
        }
        _ => true,
    }
}

/// Whether `expr`, checked against `goal`, is a pattern `let` made into
/// projections.
pub(crate) fn applies(cx: &Ctx, expr: &Expr, goal: &Value) -> Result<bool> {
    let Some((patterns, _)) = parts(expr) else {
        return Ok(false);
    };
    Ok(patterns.iter().all(|(p, _)| projectable(cx, p)) && !proposition(cx, goal)?)
}

/// Whether `ty` is evidently a proposition: an equation, a data type in
/// `Prop`, or a function into one.
pub(crate) fn proposition(cx: &Ctx, ty: &Value) -> Result<bool> {
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
    let (patterns, body) = parts(expr).expect("checked by `applies`");
    let mark = cx.mark();
    let mut lets = Vec::new();
    let result = (|| {
        for (pattern, value) in patterns {
            let level = match variable(cx, value) {
                Some(level) => level,
                None => {
                    let (term, ty) = infer(cx, value)?;
                    let (term, ty) = insert(cx, term, ty)?;
                    bind(cx, None, term, ty, &mut lets)?
                }
            };
            destructure(cx, pattern, level, &mut lets)?;
        }
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
        Pattern::Ctor(n, args, span) => {
            let (data, accessors) = proof_ctor(cx, &n.text).expect("checked by `applies`");
            cx.e.ctor_named(&n.text, n.span)?;
            let params = match ty {
                Value::Data(d, params) if d == data => params,
                other => {
                    let mut params = Vec::new();
                    for _ in 0..g.data(data).params.len() {
                        let meta = cx.fresh_meta();
                        params.push(cx.eval(&meta)?);
                    }
                    let expected = Value::Data(data, params.clone());
                    if !cx.unify(&other, &expected)? {
                        let saved = std::mem::replace(&mut cx.span, *span);
                        let e = cx.mismatch(&other, &expected);
                        cx.span = saved;
                        return Err(e);
                    }
                    params
                }
            };
            for (def, p) in accessors.into_iter().zip(args) {
                if matches!(p, Pattern::Wildcard(_)) {
                    continue;
                }
                let (term, ty) = project(cx, def, &params, level)?;
                component(cx, p, term, ty, lets)?;
            }
            Ok(())
        }
        _ => unreachable!("only tuples, records and proof constructors are destructured"),
    }
}

/// Projection `def` (taking the type's parameters implicitly, then a value
/// of it) applied to the variable at `level`, and its type.
fn project(cx: &Ctx, def: DefId, params: &[Value], level: usize) -> Result<(Term, Value)> {
    let g = cx.g();
    let mut term = Term::Def(def);
    let mut ty = crate::kernel::def_ty(g, def)?;
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
