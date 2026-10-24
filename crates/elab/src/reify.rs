//! `match reify t with` (docs/proposals/proof-reification.md, D1144 to
//! D1148): in a proof, a split on what the computation `t ()` does first,
//! with clauses written as a handler's.
//!
//! ```text
//! match reify t with
//!   | return x => …
//!   | Fail.stop msg, k => …
//! ```
//!
//! is elaborated as an ordinary generalised `match` (`matching.rs`) on the
//! tree `t ()`, with the patterns written by identity: `Done x` for the
//! `return` clause, `Call (L (Fail.%stop msg)) k` for an operation (its
//! constructor inside the row's injections, `R` once per ability before
//! it), and an absurd row `Call (R … (R ())) _` for the closed row's end,
//! `NoOp`. So in each clause the goal has `Done x` or that `Call` in place
//! of `t ()`, and handlers in it compute. The continuation `k` is the
//! `Call`'s own: a function from what the operation returns to the rest of
//! the computation, `y -> {Fail} a`.
//!
//! Only a declaration whose result is erased (a proof or a type) may use it
//! (D1147, `E-PROOF-ONLY`): what it computes then never runs, so no program
//! depends on how the computation is represented. R1 splits one step, on a
//! thunk whose row is closed and lists its abilities.

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::force;
use stitchwort_core::{Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Alt, Clause, Expr, MatchKind, Pattern};

use crate::Global;
use crate::check::{Ctx, Result, builtin_data, infer, infer_unrun, insert};
use crate::effects::{REC, Row, comp_parts};
use crate::{UNIT_PATTERN, internal_ctor_pattern};

/// `match reify t with …` where no type is expected: its type is a new
/// unknown.
pub(crate) fn infer_reify(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    let goal = cx.eval(&cx.fresh_meta())?;
    let term = check_reify(cx, expr, &goal)?;
    Ok((term, goal))
}

/// `match reify t with …`, checked against `goal`.
pub(crate) fn check_reify(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    let Expr::Reify {
        thunk,
        clauses,
        span,
    } = expr
    else {
        unreachable!("only called on `match reify`")
    };
    let written = stitchwort_syntax::Span::new(span.file, span.start, thunk.span().end);
    proof_only(cx, written)?;
    let (term, ty, row) = computation(cx, thunk)?;
    let (alts, absurd) = alternatives(cx, clauses, &row, &ty, *span)?;
    crate::matching::generalised_term(cx, term, ty, thunk.span(), &alts, &absurd, *span, goal)
}

/// `E-PROOF-ONLY`: `reify` only in a declaration whose result is erased
/// (D1147), decided from its declared type.
fn proof_only(cx: &Ctx, span: stitchwort_syntax::Span) -> Result<()> {
    let label = match cx.e.body_erased()? {
        Some(true) => return Ok(()),
        Some(false) => "this declaration computes data, so this would run",
        // A test, an expression typed in, or a signature.
        None => "this isn't the body of a proof, so this could run",
    };
    Err(
        Diagnostic::error("E-PROOF-ONLY", "`reify` can only be used in a proof")
            .with_label(span, label)
            .with_note(
                "`reify` may be used in a `theorem`, or a `def` whose type ends in `Prop` or a \
             type: what it computes is never run",
            )
            .with_note(
                "state what you need as a theorem and use `reify` there; to act on a failure at \
             run time, use a handler such as `Fail.toResult` or `Fail.orElse`",
            ),
    )
}

/// The computation `t ()` the thunk `t` stands for: its term, its type (a
/// `Comp` over a closed row of abilities) and that row. A lambda `() => e`
/// gives `e` itself, passed as a computation and not run.
fn computation(cx: &mut Ctx, thunk: &Expr) -> Result<(Term, Value, Row)> {
    let span = thunk.span();
    let (term, ty) = match lambda_body(thunk) {
        Some(body) => {
            let (term, ty) = infer_unrun(cx, body)?;
            insert(cx, term, ty)?
        }
        None => {
            let (term, ty) = infer(cx, thunk)?;
            let ty = force(cx.g(), ty)?;
            let unit = builtin_data(cx, Builtin::UnitType)?;
            let Value::Pi(_, stitchwort_core::Icit::Explicit, dom, cod) = &ty else {
                return Err(not_a_thunk(cx, span, &ty));
            };
            if !cx.unify(dom, &Value::Data(unit, Vec::new()))? {
                return Err(not_a_thunk(cx, span, &ty));
            }
            // `t ()`.
            let result = cod.apply(cx.g(), Value::Ctor(unit, 0, Vec::new().into()))?;
            (Term::app(term, Term::Ctor(unit, 0, Vec::new())), result)
        }
    };
    let ty = force(cx.g(), ty)?;
    let Some((row, _)) = comp_parts(cx, &ty)? else {
        return Err(Diagnostic::error(
            "E-REIFY",
            format!(
                "`reify` needs a computation that performs abilities, but this is `{}`",
                cx.show(&ty)
            ),
        )
        .with_label(span, "this computation performs nothing")
        .with_note(
            "a computation that performs nothing is just its value: a proof needs no `reify`",
        ));
    };
    let shown = cx.show(&ty);
    if row.partial || row.labels.iter().any(|l| l.ability == REC) {
        return Err(Diagnostic::error(
            "E-REIFY",
            format!("`reify` can't take apart a `Partial` computation: `{shown}`"),
        )
        .with_label(span, "this computation may not finish")
        .with_note("`reify` needs a computation that finishes, so a proof can look at all of it"));
    }
    if row.is_bare() {
        return Err(Diagnostic::error(
            "E-REIFY",
            format!("this computation's row isn't known: `{shown}`"),
        )
        .with_label(span, "its abilities are a row variable")
        .with_note("`reify` needs a row that lists its abilities, such as `{Fail}`"));
    }
    if row.tail.is_some() {
        return Err(Diagnostic::error(
            "E-REIFY",
            format!("this computation's row is open: `{shown}`"),
        )
        .with_label(span, "it may perform abilities its row doesn't list")
        .with_note(
            "`reify` needs a closed row, one that lists every ability, such as `{Fail}`; \
             an open row (`{Fail | e}`) isn't supported yet",
        ));
    }
    Ok((term, ty, row))
}

/// `e`, when `thunk` is `() => e` (a lambda whose one parameter is the unit
/// pattern, which the parser writes as a one-alternative `match`).
fn lambda_body(thunk: &Expr) -> Option<&Expr> {
    let Expr::Lam(names, body, _) = thunk else {
        return None;
    };
    let [name] = &names[..] else {
        return None;
    };
    let Expr::Match {
        scrutinees,
        alts,
        kind: MatchKind::Lambda,
        ..
    } = &**body
    else {
        return None;
    };
    match (&scrutinees[..], &alts[..]) {
        ([s], [alt])
            if matches!(&s.expr, Expr::Var(x) if x.text == name.text)
                && matches!(&alt.patterns[..], [Pattern::Absurd(_)]) =>
        {
            Some(&alt.body)
        }
        _ => None,
    }
}

fn not_a_thunk(cx: &Ctx, span: stitchwort_syntax::Span, ty: &Value) -> Diagnostic {
    Diagnostic::error(
        "E-REIFY",
        format!(
            "`reify` takes a computation as a thunk, `() -> {{A}} t`, but this is `{}`",
            cx.show(ty)
        ),
    )
    .with_label(span, "expected a thunk")
    .with_note("write the computation as `() => …`, or pass a function `() -> {Fail} a`")
}

/// The alternatives of the `match` on the tree, one per clause, and the
/// absurd row for the closed row's end.
fn alternatives(
    cx: &mut Ctx,
    clauses: &[Clause],
    row: &Row,
    ty: &Value,
    span: stitchwort_syntax::Span,
) -> Result<(Vec<Alt>, Vec<Vec<Pattern>>)> {
    let comp = builtin_data(cx, Builtin::Comp)?;
    let plus = builtin_data(cx, Builtin::Plus)?;
    // `Comp`: `Done` 0, `Call` 1. `Plus`: `L` 0, `R` 1.
    let (done, call, left, right) = (0, 1, 0, 1);
    let mut alts = Vec::new();
    let mut returned = false;
    // Which operations have a clause, as (position in the row, operation).
    let mut seen: Vec<(usize, usize)> = Vec::new();
    for clause in clauses {
        match clause {
            Clause::Return { var, body } => {
                if returned {
                    return Err(Diagnostic::error("E-DUPLICATE", "two `return` clauses")
                        .with_label(var.span, "the second"));
                }
                returned = true;
                let pattern =
                    internal_ctor_pattern(comp, done, vec![Pattern::Var(var.clone())], var.span);
                alts.push(Alt {
                    patterns: vec![pattern],
                    body: body.clone(),
                    span: var.span.to(body.span()),
                });
            }
            Clause::Op { op, arg, k, body } => {
                cx.e.note_name(op);
                let found = cx.e.named(&op.text).copied();
                if let Some((Global::Unchecked(item), _)) = found {
                    return Err(cx.e.unchecked(op, item));
                }
                if let Some((Global::Failed, _)) = found {
                    return Err(crate::module::failed_name(op));
                }
                if let Some((Global::Pending(file, _), _)) = found {
                    return Err(cx.e.unloaded(op, file));
                }
                let Some((Global::Op(ability, index), _)) = found else {
                    return Err(Diagnostic::error(
                        "E-ABILITY",
                        format!("`{}` isn't an operation", op.text),
                    )
                    .with_label(op.span, "a clause of `match reify` needs an operation"));
                };
                let Some(position) = row.labels.iter().position(|l| l.ability == ability) else {
                    return Err(Diagnostic::error(
                        "E-ABILITY",
                        format!(
                            "`{}` isn't an operation this computation can perform: it is `{}`",
                            op.text,
                            cx.show(ty)
                        ),
                    )
                    .with_label(op.span, "not in the computation's row"));
                };
                if seen.contains(&(position, index)) {
                    return Err(Diagnostic::error(
                        "E-DUPLICATE",
                        format!("two clauses for `{}`", op.text),
                    )
                    .with_label(op.span, "the second"));
                }
                seen.push((position, index));
                let arg = match arg {
                    Pattern::Var(_) | Pattern::Wildcard(_) => arg.clone(),
                    Pattern::Absurd(s) => Pattern::Ctor(
                        ast::Name {
                            text: UNIT_PATTERN.into(),
                            span: *s,
                        },
                        Vec::new(),
                        *s,
                    ),
                    other => {
                        return Err(Diagnostic::error(
                            "E-HANDLER",
                            "a clause's argument is a name, `_` or `()`",
                        )
                        .with_label(other.span(), "here"));
                    }
                };
                let op_data = cx.e.abilities[ability].op_data;
                let mut operation = internal_ctor_pattern(op_data, index, vec![arg], op.span);
                operation = internal_ctor_pattern(plus, left, vec![operation], op.span);
                for _ in 0..position {
                    operation = internal_ctor_pattern(plus, right, vec![operation], op.span);
                }
                let continuation = if k.text == "_" {
                    Pattern::Wildcard(k.span)
                } else {
                    Pattern::Var(k.clone())
                };
                let pattern =
                    internal_ctor_pattern(comp, call, vec![operation, continuation], op.span);
                alts.push(Alt {
                    patterns: vec![pattern],
                    body: body.clone(),
                    span: op.span.to(body.span()),
                });
            }
        }
    }
    // Every case has a clause: finishing, and each operation of the row.
    let mut missing = Vec::new();
    if !returned {
        missing.push("`return x`".to_string());
    }
    for (position, label) in row.labels.iter().enumerate() {
        let info = &cx.e.abilities[label.ability];
        for (index, name) in info.ops.iter().enumerate() {
            if !seen.contains(&(position, index)) {
                missing.push(format!("`{}.{name}`", info.name));
            }
        }
    }
    if !missing.is_empty() {
        return Err(Diagnostic::error(
            "E-NONEXHAUSTIVE",
            format!(
                "this `match reify` has no clause for {}",
                missing.join(", ")
            ),
        )
        .with_label(span, format!("`{}` may do that", cx.show(ty)))
        .with_note(
            "a `match reify` needs a `return` clause and a clause for each operation of the \
             computation's row",
        ));
    }
    // The closed row's end: `Call (R … (R ())) _`, with no values.
    let mut end = Pattern::Absurd(span);
    for _ in 0..row.labels.len() {
        end = internal_ctor_pattern(plus, right, vec![end], span);
    }
    let absurd = vec![vec![internal_ctor_pattern(
        comp,
        call,
        vec![end, Pattern::Wildcard(span)],
        span,
    )]];
    Ok((alts, absurd))
}
