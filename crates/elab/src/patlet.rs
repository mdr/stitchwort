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
//! A scrutinee that is a test fact (`e = True`) is first read as what its test
//! means (docs/proposals/bool-as-proposition.md §6.1), into a hidden `let`
//! the accessors project, as a `match` would.
//!
//! In a proof (the expected type is evidently a proposition), a `let` on
//! data stays a `match`: there, splitting `e` into a pair refines the goal,
//! which is what a proof by `let (a, b) := p` wants
//! (`examples/accept/let-patterns.sw`, `swapTwice`). A `let` on a proof
//! (`let (below, above) := bounds x`, at `∧` or a record or constructor of
//! proofs) binds projections there too: a `match` would generalise the goal
//! and every hypothesis over the proof, reading each back, which in a goal
//! about a large term cost millions of steps (SW-4619, SW-4629), and a goal
//! rarely mentions a proof. Where one does and the body needs it refined,
//! the body fails with projections and the `let` is checked again as the
//! `match`, so a proof that checked as a `match` still does, with the same
//! errors; the `let`s inside that `match` are kept as `match`es
//! ([`Ctx::kept_matches`]), so a failure deep inside costs a check more per
//! `let` around it, rather than doubling with each. Patterns with anything but variables, `_`, tuples,
//! records and such constructors stay `match`es.

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::force;
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{Expr, MatchKind, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

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
    Some((out, alt.body.as_ref()?))
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
    if !rest.is_empty() {
        return None;
    }
    proof_data(cx, d)
}

/// [`proof_ctor`] for the data type `d`.
fn proof_data(cx: &Ctx, d: DataId) -> Option<(DataId, Vec<DefId>)> {
    let data = cx.g().data(d);
    let single = data.ctors().len() == 1 && data.indices().is_empty();
    if data.sort() != Sort::Prop || !single {
        return None;
    }
    let ctor = &data.ctors()[0];
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
    if !patterns.iter().all(|(p, _)| projectable(cx, p)) {
        return Ok(false);
    }
    // In a proof, only proofs are taken apart by projections, and only
    // while the `let`s around aren't kept as `match`es. A scrutinee that
    // isn't a variable is judged once its type is known, in `check_let`.
    if proposition(cx, goal)? {
        if cx.kept_matches {
            return Ok(false);
        }
        for (pattern, value) in &patterns {
            if let Expr::Var(x) = value
                && cx.local(&x.text).ok().flatten().is_none()
                && let Some(level) = cx.lookup(&x.text)
                && !proposition(cx, &cx.types[level])?
            {
                return Ok(false);
            }
            // A lemma's result that is evidently data or opens an `∃` is
            // the `match` without first elaborating the call to find out,
            // which the `match` would then do again.
            if let Some(result) = declared_result(cx, value)?
                && (!proposition(cx, &result)? || opens_exists(cx, pattern, &result)?)
            {
                return Ok(false);
            }
        }
    }
    // A tuple on a proof of `∃` is `Witness`, which has no projections, so
    // it is the `match` that `Witness` written out would be, whose
    // scrutinee, a variable, can then be split in place.
    for (pattern, value) in patterns {
        if let Expr::Var(x) = value
            && let Some(level) = cx.lookup(&x.text)
            && opens_exists(cx, pattern, &cx.types[level])?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The type a call of a global definition, `f a b`, ends in after all of
/// `f`'s parameters, its own variables stood for by a placeholder: what
/// the call's type is when it gives every argument, for a guess at it
/// before elaborating the call. `None` for anything else.
fn declared_result(cx: &Ctx, e: &Expr) -> Result<Option<Value>> {
    let mut head = e;
    while let Expr::App(f, _) = head {
        head = f;
    }
    let Expr::Var(x) = head else {
        return Ok(None);
    };
    if cx.lookup(&x.text).is_some() || cx.local(&x.text).ok().flatten().is_some() {
        return Ok(None);
    }
    let Resolved::Found {
        global: Global::Def(def),
        rest,
        ..
    } = cx.e.resolve(&x.text)
    else {
        return Ok(None);
    };
    if !rest.is_empty() {
        return Ok(None);
    }
    let g = cx.g();
    let mut ty = crate::kernel::def_ty(&g, def)?;
    while let Value::Pi(_, _, _, cod, _) = force(&g, ty.clone())? {
        // A variable no binder in scope has, as in `proposition`.
        ty = cod.apply(&g, Value::dummy_var())?;
    }
    Ok(Some(ty))
}

/// Whether a tuple in `p`, matching a value of type `ty`, meets a proof of
/// `∃`, through the tuples and constructors around it.
fn opens_exists(cx: &Ctx, p: &Pattern, ty: &Value) -> Result<bool> {
    let g = cx.g();
    let registry = g.env.registry();
    let Value::Data(d, params) = force(&g, ty.clone())? else {
        return Ok(false);
    };
    let parts: Vec<&Pattern> = match p {
        Pattern::Tuple(..) if registry.is_data(Builtin::Exists, d) => return Ok(true),
        Pattern::Tuple(a, b, _) => vec![a, b],
        Pattern::Ctor(_, args, _) => args.iter().collect(),
        _ => return Ok(false),
    };
    // `∧` and pairs: the parts' types are the parameters.
    let pair = registry.is_data(Builtin::Pair, d);
    if !(registry.is_data(Builtin::And, d) || pair) || params.len() != 2 {
        return Ok(false);
    }
    for (part, ty) in parts.into_iter().zip(params.iter()) {
        if opens_exists(cx, part, ty)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Whether `ty` is evidently a proposition: an equation, a data type in
/// `Prop`, or a function into one.
pub(crate) fn proposition(cx: &Ctx, ty: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(match force(&g, ty.clone())? {
        Value::Eq(..) => true,
        Value::Data(d, _) => g.data(d).sort() == Sort::Prop,
        Value::Pi(_, _, _, cod, _) => {
            // A fresh variable no binder in scope has, for the test only.
            proposition(cx, &cod.apply(&g, Value::dummy_var())?)?
        }
        _ => false,
    })
}

/// The pattern `let` `expr` (one [`applies`] to), checked against `goal`.
/// `None`, with everything it did undone, where a tuple pattern meets a
/// proof of `∃`, which has no projections, and in a proof where the
/// scrutinee isn't a proof or anything fails: the caller makes it the
/// `match` it otherwise means. After a failure in a proof,
/// [`Ctx::kept_matches`] is set, for the caller to reset once that `match`
/// is checked.
pub(crate) fn check_let(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Option<Term>> {
    let (patterns, body) = parts(expr).expect("checked by `applies`");
    let snapshot = crate::undo::Snapshot::take(cx);
    let mark = cx.mark();
    let in_proof = proposition(cx, goal)?;
    let mut lets = Lets {
        items: Vec::new(),
        opaque: in_proof,
    };
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
            if in_proof && !proposition(cx, &cx.types[level])? {
                return Ok(None);
            }
            if !destructure(cx, pattern, level, &mut lets)? {
                return Ok(None);
            }
        }
        check(cx, body, goal).map(Some)
    })();
    cx.reset(mark);
    // In a proof, any failure (most often a body that needs the goal
    // refined by the `match`, which projections don't do) is checked again
    // as that `match`, as before, with the `let`s inside it kept as
    // `match`es too, so its errors are the `match`'s.
    let failed = matches!(&result, Err(e) if in_proof && !crate::undo::fatal(e));
    let result = if failed { Ok(None) } else { result };
    let Some(mut term) = result? else {
        snapshot.restore(cx);
        if failed {
            cx.kept_matches = true;
        }
        return Ok(None);
    };
    for (x, ty, value) in lets.items.into_iter().rev() {
        term = Term::let_(x, ty, value, term);
    }
    Ok(Some(term))
}

/// The `let`s a pattern `let` makes, outermost first, as (name, type,
/// value) terms. In a proof they are `opaque`: the rest of the proof sees
/// each as a variable of its type, as the `match`'s arm would, rather than
/// as its projection. Checked with the values hidden, the body checks with
/// them shown too, which is how the kernel reads the `let`s; and a later
/// `match` or `rewrite` doesn't carry the projections along or read them
/// back, which made proofs slower than the `match` (SW-4629).
struct Lets {
    items: Vec<(Name, Term, Term)>,
    opaque: bool,
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
    lets: &mut Lets,
) -> Result<usize> {
    let shown: Name = name.unwrap_or("%p").into();
    let ty_term = cx.quote_folded(&ty)?;
    lets.items
        .push((shown.clone(), ty_term.clone(), value.clone()));
    if lets.opaque {
        match name {
            Some(name) => cx.bind(name, ty),
            None => cx.bind_hidden(shown, ty),
        }
    } else {
        cx.define(name, shown, ty, ty_term, value)?;
    }
    Ok(cx.level() - 1)
}

/// Binds the names in tuple or record pattern `p` to projections of the
/// variable at `level`. False where a tuple pattern meets a proof of `∃`,
/// which can't be projected.
fn destructure(cx: &mut Ctx, p: &Pattern, level: usize, lets: &mut Lets) -> Result<bool> {
    let g = cx.g();
    let ty = force(&g, cx.types[level].clone())?;
    let registry = g.env.registry();
    match p {
        // On a proof of `∧`, `(a, b)` is `Both a b` (proof-tuples.md §4.2),
        // projected through its accessors as that pattern is.
        Pattern::Tuple(a, b, _) if matches!(&ty, Value::Data(d, _) if registry.is_data(Builtin::And, *d)) =>
        {
            let Value::Data(and, params) = ty else {
                unreachable!("just matched")
            };
            let (_, accessors) = proof_data(cx, and).expect("`∧` has accessors");
            for (def, p) in accessors.into_iter().zip([a, b]) {
                if matches!(**p, Pattern::Wildcard(_)) {
                    continue;
                }
                let (term, ty) = project(cx, def, &params, level)?;
                if !component(cx, p, term, ty, lets)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Pattern::Tuple(..) if matches!(&ty, Value::Data(d, _) if registry.is_data(Builtin::Exists, *d)) => {
            Ok(false)
        }
        // At an unknown proposition a pair can't be right: the `match` the
        // pattern falls back to says so, and fails in place.
        Pattern::Tuple(..) if crate::prop_unknown(cx, &ty) => Ok(false),
        // A test fact (`rest: (b && c) = True`, the second part of
        // `h.read` on a longer chain) is taken apart by what it reads as,
        // which the `match` the pattern falls back to does (SW-3740).
        Pattern::Tuple(..) if crate::reading::test_fact(cx, &ty)?.is_some() => Ok(false),
        Pattern::Tuple(a, b, span) => {
            let pair = builtin_data(cx, Builtin::Pair)?;
            let params = match ty {
                Value::Data(d, params) if d == pair => params,
                other => {
                    let params = crate::check::fresh_telescope(cx, g.data(pair).params())?;
                    let expected = Value::Data(pair, params.into());
                    if !cx.unify(&other, &expected)? {
                        let note = match crate::check::tuple_target_note(
                            cx,
                            &other,
                            crate::check::TupleNote::Pattern,
                        ) {
                            Some(tail) => format!(
                                "a tuple pattern opens a pair, a proof of `∧` or a proof of \
                                 `∃`; {tail}"
                            ),
                            None => "a tuple pattern opens a pair, a proof of `∧` or a proof of \
                                     `∃`"
                            .to_string(),
                        };
                        let saved = std::mem::replace(&mut cx.span, *span);
                        let e = cx.mismatch(&other, &expected);
                        cx.span = saved;
                        return Err(e.with_note(note));
                    }
                    let Value::Data(_, params) = force(&g, expected)? else {
                        unreachable!("a data type")
                    };
                    params
                }
            };
            let fst = builtin_def(cx, Builtin::Fst)?;
            let snd = builtin_def(cx, Builtin::Snd)?;
            for (def, p) in [(fst, a), (snd, b)] {
                let (term, ty) = project(cx, def, &params, level)?;
                if !component(cx, p, term, ty, lets)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // A record pattern on a test fact (`h: inRange 1 x 9`) reads it
        // through its reading, which the `match` does.
        Pattern::Record { .. } if crate::reading::test_fact(cx, &ty)?.is_some() => Ok(false),
        Pattern::Record { fields, rest, span } => {
            let pattern = cx.e.record_pattern(fields, *rest, *span, Some(&ty))?;
            let Value::Data(_, params) = ty else {
                unreachable!("`record_pattern` accepts only a record type")
            };
            let projections = cx.e.tables.records[&pattern.data].projections.clone();
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
                if !component(cx, arg, term, ty, lets)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Pattern::Ctor(n, args, span) => {
            let (data, accessors) = proof_ctor(cx, &n.text).expect("checked by `applies`");
            cx.e.ctor_named(&n.text, n.span)?;
            // A test fact is taken apart by what its test reads as
            // (docs/proposals/bool-as-proposition.md §6.1), bound to a
            // hidden variable the accessors then project.
            let (level, ty) = match read_fact(cx, level, &ty, data, *span, lets)? {
                Some(read) => read,
                None => (level, ty),
            };
            let params = match ty {
                Value::Data(d, params) if d == data => params,
                other => {
                    let params = crate::check::fresh_telescope(cx, g.data(data).params())?;
                    let expected = Value::Data(data, params.clone().into());
                    if !cx.unify(&other, &expected)? {
                        let saved = std::mem::replace(&mut cx.span, *span);
                        let e = cx.mismatch(&other, &expected);
                        cx.span = saved;
                        return Err(e);
                    }
                    params.into()
                }
            };
            for (def, p) in accessors.into_iter().zip(args) {
                if matches!(p, Pattern::Wildcard(_)) {
                    continue;
                }
                let (term, ty) = project(cx, def, &params, level)?;
                if !component(cx, p, term, ty, lets)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => unreachable!("only tuples, records and proof constructors are destructured"),
    }
}

/// The variable `level` of test-fact type `ty`, read as the proposition
/// `data` (§6.1): a new hidden variable holding the reading and its type,
/// or `None` where `ty` isn't a test fact. A test with no such reading is
/// an error, as for a `match`.
fn read_fact(
    cx: &mut Ctx,
    level: usize,
    ty: &Value,
    data: DataId,
    span: Span,
    lets: &mut Lets,
) -> Result<Option<(usize, Value)>> {
    let ty = crate::reading::variable_as_written(cx, level, ty)?;
    let Some((test, polarity)) = crate::reading::test_fact(cx, &ty)? else {
        return Ok(None);
    };
    match crate::reading::read_through(cx, &test, polarity)? {
        crate::reading::Read::Found(found) if matches!(force(&cx.g(), found.prop.clone())?, Value::Data(d, _) if d == data) =>
        {
            let term = found.forward(cx, Term::Var(cx.level() - 1 - level))?;
            let read = bind(cx, None, term, found.prop.clone(), lets)?;
            let prop = force(&cx.g(), found.prop)?;
            Ok(Some((read, prop)))
        }
        read => {
            let how = format!(
                "taken apart with {}",
                crate::reading::constructors_shown(cx, data)
            );
            Err(crate::reading::no_reading(
                cx,
                span,
                &test,
                polarity,
                &how,
                &read,
                Some((data, "this pattern matches")),
            ))
        }
    }
}

/// Projection `def` (taking the type's parameters implicitly, then a value
/// of it) applied to the variable at `level`, and its type.
fn project(cx: &Ctx, def: DefId, params: &[Value], level: usize) -> Result<(Term, Value)> {
    let g = cx.g();
    let mut term = Term::Def(def);
    let mut ty = crate::kernel::def_ty(&g, def)?;
    let args = params
        .iter()
        .map(|p| Ok((cx.quote_folded(p)?, p.clone(), Icit::Implicit)))
        .chain(std::iter::once(Ok((
            Term::Var(cx.level() - 1 - level),
            cx.env[level].clone(),
            Icit::Explicit,
        ))))
        .collect::<Result<Vec<_>>>()?;
    for (arg, value, icit) in args {
        let Value::Pi(_, _, _, cod, _) = force(&g, ty)? else {
            unreachable!("a projection takes the parameters and the value")
        };
        ty = cod.apply(&g, value)?;
        term = Term::app_icit(term, arg, icit);
    }
    Ok((term, ty))
}

/// A field's pattern `p`, for the projection `term` of type `ty`.
fn component(cx: &mut Ctx, p: &Pattern, term: Term, ty: Value, lets: &mut Lets) -> Result<bool> {
    match p {
        Pattern::Wildcard(_) => Ok(true),
        Pattern::Var(x) => bind(cx, Some(&x.text), term, ty, lets).map(|_| true),
        p => {
            let level = bind(cx, None, term, ty, lets)?;
            destructure(cx, p, level, lets)
        }
    }
}
