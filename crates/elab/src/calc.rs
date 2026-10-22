//! `calc` chains (docs/syntax.md, "calc"; docs/proposals/calc-rewrite.md §5).
//!
//! ```text
//! calc e0
//!   _ = e1  := p1
//!   _ <= e2 := p2
//!   _ < e3
//! ```
//!
//! Each step `_ R e` is a proposition `previous R e`, proved by its `:= proof`
//! or, with none, by `rfl` (checked against the step's own proposition, so for
//! `<=` and `<` it means that the order proposition computes to true, not that
//! the two ends are convertible). The steps are combined left to right with
//! the table in [`combine`] into terms people write by hand (`Eq.trans`, `J`,
//! `Nat.leTrans`, `Nat.lessTrans`); the chain proves what the fold ends with.
//! Elaboration only: the kernel re-checks the result.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, force};
use stitchwort_core::{Icit, Term, Value};
use stitchwort_syntax::ast::{BinOp, CalcStep, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{
    Arg, Ctx, Piped, Result, apply_args, builtin_ctor, builtin_def, check, infer, insert, nat,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Rel {
    Eq,
    Le,
    Lt,
}

impl Rel {
    fn of(op: BinOp) -> Rel {
        match op {
            BinOp::Eq => Rel::Eq,
            BinOp::Le => Rel::Le,
            BinOp::Lt => Rel::Lt,
            _ => unreachable!("the parser only accepts `=`, `<=` and `<` in a calc step"),
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            Rel::Eq => "=",
            Rel::Le => "<=",
            Rel::Lt => "<",
        }
    }
}

/// What the steps so far prove: `proof : start rel end`.
struct Link {
    rel: Rel,
    proof: Term,
    /// The type of `proof`.
    prop: Value,
    end: Term,
}

/// `calc` with no type expected: it proves what its steps add up to.
pub(crate) fn infer_calc(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    let (term, prop, _) = elaborate(cx, expr, None)?;
    Ok((term, prop))
}

/// `calc` against a goal: the chain must prove it, up to computation.
pub(crate) fn check_calc(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let (term, prop, ends) = elaborate(cx, expr, Some(expected))?;
    if cx.unify(&prop, expected)? {
        Ok(term)
    } else {
        Err(goal_error(cx, expr, expected, &ends))
    }
}

/// The chain's ends as elaborated: its relation, first expression and last.
struct Ends {
    rel: Rel,
    start: Value,
    end: Value,
    /// What the chain proves, as its expressions were written.
    shown: String,
    start_term: Term,
    end_term: Term,
}

fn elaborate(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value, Ends)> {
    let Expr::Calc { first, steps, .. } = expr else {
        unreachable!("only called on a calc");
    };
    let ordered = steps.iter().any(|s| s.rel != BinOp::Eq);
    let hint = match expected {
        Some(goal) => hint(cx, goal, ordered)?,
        None => None,
    };
    let (start, ty) = match infer(cx, first).and_then(|(t, ty)| insert(cx, t, ty)) {
        Ok(found) => found,
        Err(e) if e.code == "E-CANNOT-INFER" && hint.is_some() => {
            let hint = hint.expect("just checked");
            (check(cx, first, &hint)?, hint)
        }
        Err(e) => return Err(e),
    };
    let ty_term = Rc::new(cx.quote(&ty)?);
    let nat_ty = Value::Data(nat(cx)?, Vec::new());
    let mut link: Option<Link> = None;
    for step in steps {
        let rel = Rel::of(step.rel);
        if rel != Rel::Eq && !cx.unify(&ty, &nat_ty)? {
            return Err(relation_error(cx, step, rel, &ty));
        }
        let end = link
            .as_ref()
            .map_or_else(|| start.clone(), |l| l.end.clone());
        let next = check(cx, &step.rhs, &ty)?;
        let prop_term = relation(cx, rel, &ty_term, end, next.clone())?;
        let prop = cx.eval(&prop_term)?;
        let line = written(cx, &prop_term);
        let proof = match &step.proof {
            Some(p) => check_step(cx, p, &prop, &prop_term, &line)?,
            None => by_computation(cx, step, &prop, &line)?,
        };
        link = Some(match link {
            None => Link {
                rel,
                proof,
                prop,
                end: next,
            },
            Some(acc) => combine(
                cx,
                &start,
                &ty_term,
                acc,
                Step {
                    rel,
                    proof,
                    prop,
                    end: next,
                    span: step.span,
                },
            )?,
        });
    }
    let link = link.expect("a calc has a step");
    let chain = relation(cx, link.rel, &ty_term, start.clone(), link.end.clone())?;
    let ends = Ends {
        rel: link.rel,
        start: cx.eval(&start)?,
        end: cx.eval(&link.end)?,
        shown: written(cx, &chain),
        start_term: start.clone(),
        end_term: link.end.clone(),
    };
    Ok((link.proof, link.prop, ends))
}

/// A type to check the first expression against if it can't be inferred
/// (`[]`): the goal's, where the goal is an equation or the chain is of
/// orders.
fn hint(cx: &mut Ctx, goal: &Value, ordered: bool) -> Result<Option<Value>> {
    if ordered {
        return Ok(Some(Value::Data(nat(cx)?, Vec::new())));
    }
    Ok(match force(cx.g(), goal.clone())? {
        Value::Eq(ty, _, _) => Some((*ty).clone()),
        _ => None,
    })
}

/// A step's proposition `end rel next`.
fn relation(cx: &Ctx, rel: Rel, ty: &Rc<Term>, a: Term, b: Term) -> Result<Term> {
    Ok(match rel {
        Rel::Eq => Term::Eq(Some(ty.clone()), Rc::new(a), Rc::new(b)),
        Rel::Le => ordering(cx, Builtin::LessEq, a, b)?,
        Rel::Lt => ordering(cx, Builtin::LessThan, a, b)?,
    })
}

fn ordering(cx: &Ctx, which: Builtin, a: Term, b: Term) -> Result<Term> {
    let id = builtin_def(cx, which)?;
    Ok(Term::app(Term::app(Term::Def(id), a), b))
}

/// A term as written, for messages (orders print as `a <= b`).
fn written(cx: &Ctx, term: &Term) -> String {
    stitchwort_core::pretty::term_for_message(cx.g(), &cx.names, term)
}

/// A step's proof, checked against its line's proposition. A proof that
/// proves something else is `E-CALC-STEP`, pointing at the proof; an error
/// inside the proof is reported as it would be anywhere else.
fn check_step(
    cx: &mut Ctx,
    proof: &Expr,
    prop: &Value,
    prop_term: &Term,
    line: &str,
) -> Result<Term> {
    // A `rewrite` shows the line as it was built in its messages (rewrite.rs).
    cx.written_goal = matches!(proof, Expr::Rewrite { .. }).then(|| prop_term.clone());
    let checked = check(cx, proof, prop);
    cx.written_goal = None;
    match checked {
        Err(e)
            if matches!(e.code, "E-TYPE-MISMATCH" | "E-REFL")
                && e.primary_span() == Some(proof.span()) =>
        {
            let mut label = e
                .labels
                .first()
                .map_or_else(|| e.message.clone(), |l| l.message.clone());
            if e.code == "E-TYPE-MISMATCH"
                && let Ok(Some((_, found))) = crate::numbers::attempt(cx, |cx| infer(cx, proof))
            {
                label = format!("this proves `{}`", show_prop(cx, &found));
            }
            let mut error =
                Diagnostic::error("E-CALC-STEP", "this step doesn't prove what its line says")
                    .with_label(proof.span(), label)
                    .with_note(format!("the line says `{line}`"));
            for note in e.notes {
                error = error.with_note(note);
            }
            Err(error)
        }
        result => result,
    }
}

/// A step with no proof: `rfl` against the step's proposition.
fn by_computation(cx: &mut Ctx, step: &CalcStep, prop: &Value, line: &str) -> Result<Term> {
    let computed = force(cx.g(), prop.clone())?;
    if let Value::Eq(_, a, b) = &computed
        && cx.unify(a, b)?
    {
        return Ok(Term::Refl);
    }
    let mut error = Diagnostic::error(
        "E-CALC-STEP",
        "this step has no proof, and `rfl` doesn't prove it",
    )
    .with_label(step.span, format!("`{line}` doesn't hold by computation"));
    error = match &computed {
        Value::Eq(_, a, b) => error.with_note(format!(
            "the line says `{line}`, which computes to `{} = {}`",
            cx.show(a),
            cx.show(b)
        )),
        other => error.with_note(format!("computing it gives `{}`", cx.show(other))),
    };
    Err(error.with_note("a step without `:=` must hold by computation alone"))
}

/// `Nat.leq x y = True`, which is what `x <= y` computes to (and `a < b`,
/// with `Succ a` for `x`): its `x` and `y`.
fn order_sides(cx: &Ctx, value: &Value) -> Option<(Value, Value)> {
    let Value::Eq(_, l, r) = value else {
        return None;
    };
    let (bool_data, true_ix) = builtin_ctor(cx, Builtin::True).ok()?;
    let Value::Ctor(d, c, _) = force(cx.g(), (**r).clone()).ok()? else {
        return None;
    };
    if (d, c) != (bool_data, true_ix) {
        return None;
    }
    let Value::Neutral(Head::Def(id), elims) = force(cx.g(), (**l).clone()).ok()? else {
        return None;
    };
    if builtin_def(cx, Builtin::Leq).ok() != Some(id) {
        return None;
    }
    let [Elim::App(x, _), Elim::App(y, _)] = &elims[..] else {
        return None;
    };
    Some((x.clone(), y.clone()))
}

/// A proposition read as `a = b`, `a <= b` or `a < b` (`Succ a <= b` is read
/// as `a < b`).
fn reading(cx: &Ctx, prop: &Value) -> Option<(Rel, Value, Value)> {
    let prop = force(cx.g(), prop.clone()).ok()?;
    if let Some((x, y)) = order_sides(cx, &prop) {
        let (k, base) = stitchwort_core::native::view(cx.g(), &x).ok()?;
        if k == num_bigint::BigUint::default() {
            return Some((Rel::Le, x, y));
        }
        let pred = stitchwort_core::native::from_view(k - 1u32, base);
        return Some((Rel::Lt, pred, y));
    }
    match prop {
        Value::Eq(_, a, b) => Some((Rel::Eq, (*a).clone(), (*b).clone())),
        _ => None,
    }
}

/// A proposition for a message: `a <= b` rather than what it computes to.
fn show_prop(cx: &Ctx, prop: &Value) -> String {
    match reading(cx, prop) {
        Some((rel, a, b)) if rel != Rel::Eq => {
            format!("{} {} {}", cx.show(&a), rel.symbol(), cx.show(&b))
        }
        _ => cx.show(prop),
    }
}

/// A step's relation on a type it isn't defined on.
fn relation_error(cx: &Ctx, step: &CalcStep, rel: Rel, ty: &Value) -> Diagnostic {
    Diagnostic::error(
        "E-CALC-RELATION",
        format!("`{}` can't be chained on this type", rel.symbol()),
    )
    .with_label(
        step.rel_span,
        format!(
            "`{}` steps are on `Nat`, but this chain is on `{}`",
            rel.symbol(),
            cx.show(ty)
        ),
    )
    .with_note("a chain of `=` steps works at any type; `<=` and `<` only on `Nat` for now")
}

/// The step being added to the chain.
struct Step {
    rel: Rel,
    proof: Term,
    prop: Value,
    end: Term,
    span: Span,
}

/// Adds `step` to what `acc` proves. With `R1` the relation proved so far,
/// from `a` to `b` (proof `p`), and `R2` the new step, from `b` to `c`
/// (proof `q`):
///
/// | `R1`, `R2` | result | term |
/// |---|---|---|
/// | `=`, `=` | `=` | `Eq.trans p q` |
/// | `=`, `R` | `R` | `J (w _ => w R c) q (Eq.sym p)` |
/// | `R`, `=` | `R` | `J (w _ => a R w) p q` |
/// | `<=`, `<=` | `<=` | `Nat.leTrans a b c p q` |
/// | `<`, `<=` | `<` | `Nat.leTrans (Succ a) b c p q` |
/// | `<=`, `<` | `<` | `Nat.leTrans (Succ a) (Succ b) c p q` |
/// | `<`, `<` | `<` | `Nat.lessTrans a b c p q` |
///
/// `a < b` is `Succ a <= b` and `Succ a <= Succ b` computes to `a <= b`, so
/// the proofs fit the lemmas by conversion and the table needs no new lemma.
fn combine(cx: &mut Ctx, start: &Term, ty_term: &Rc<Term>, acc: Link, step: Step) -> Result<Link> {
    let (a, b, c) = (start.clone(), acc.end.clone(), step.end.clone());
    let nat_ty = Value::Data(nat(cx)?, Vec::new());
    let push = |piped: &mut Vec<Piped>, term: Term, ty: &Value| {
        piped.push(Piped {
            term,
            ty: ty.clone(),
            span: step.span,
        });
    };
    let mut args: Vec<Piped> = Vec::new();
    let (rel, term) = match (acc.rel, step.rel) {
        (Rel::Eq, Rel::Eq) => {
            let trans = with_ends(cx, Builtin::EqTrans, ty_term, &[&a, &b, &c])?;
            let trans = Term::app(Term::app(trans, acc.proof.clone()), step.proof.clone());
            (Rel::Eq, trans)
        }
        (Rel::Eq, r) => {
            let sym = with_ends(cx, Builtin::EqSym, ty_term, &[&a, &b])?;
            let sym = Term::app(sym, acc.proof.clone());
            let c = c.shift(cx.g(), 2, 0)?;
            let motive = motive(ordering_of(cx, r, Term::Var(1), c)?);
            (
                r,
                Term::J(Rc::new(motive), Rc::new(step.proof.clone()), Rc::new(sym)),
            )
        }
        (r, Rel::Eq) => {
            let a = a.shift(cx.g(), 2, 0)?;
            let motive = motive(ordering_of(cx, r, a, Term::Var(1))?);
            (
                r,
                Term::J(
                    Rc::new(motive),
                    Rc::new(acc.proof.clone()),
                    Rc::new(step.proof.clone()),
                ),
            )
        }
        (r1, r2) => {
            let (nat_data, succ) = builtin_ctor(cx, Builtin::Succ)?;
            let succ_of = |t: &Term| Term::ctor(nat_data, succ, vec![t.clone()]);
            let (lemma_id, first, second, rel) = match (r1, r2) {
                (Rel::Le, Rel::Le) => (Builtin::LeTrans, a.clone(), b.clone(), Rel::Le),
                (Rel::Lt, Rel::Le) => (Builtin::LeTrans, succ_of(&a), b.clone(), Rel::Lt),
                (Rel::Le, Rel::Lt) => (Builtin::LeTrans, succ_of(&a), succ_of(&b), Rel::Lt),
                _ => (Builtin::LessTrans, a.clone(), b.clone(), Rel::Lt),
            };
            for number in [first, second, c.clone()] {
                push(&mut args, number, &nat_ty);
            }
            push(&mut args, acc.proof.clone(), &acc.prop);
            push(&mut args, step.proof.clone(), &step.prop);
            (rel, lemma(cx, lemma_id, &args)?)
        }
    };
    let prop_term = relation(cx, rel, ty_term, a, step.end.clone())?;
    Ok(Link {
        rel,
        proof: term,
        prop: cx.eval(&prop_term)?,
        end: step.end,
    })
}

/// `x rel y` for an order, as the body of a `J` motive.
fn ordering_of(cx: &Ctx, rel: Rel, x: Term, y: Term) -> Result<Term> {
    match rel {
        Rel::Le => ordering(cx, Builtin::LessEq, x, y),
        Rel::Lt => ordering(cx, Builtin::LessThan, x, y),
        Rel::Eq => unreachable!("only orders go through a `J` motive"),
    }
}

/// `w q => body`: the motive of `J`, with `w` as `Var(1)` in `body`.
fn motive(body: Term) -> Term {
    Term::Lam(
        "w".into(),
        Icit::Explicit,
        Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(body))),
    )
}

/// The prelude lemma `which` with its hidden arguments given directly: the
/// chain's type, then `ends`, the terms the person wrote. Leaving them to
/// the unifier would read them back from the proofs' types, which have been
/// evaluated and so are far larger than what was written (SW-256).
fn with_ends(cx: &Ctx, which: Builtin, ty: &Rc<Term>, ends: &[&Term]) -> Result<Term> {
    let mut term = Term::Def(builtin_def(cx, which)?);
    for hidden in std::iter::once(ty.as_ref()).chain(ends.iter().copied()) {
        term = Term::app_icit(term, hidden.clone(), Icit::Implicit);
    }
    Ok(term)
}

/// The prelude lemma `which` applied to `args`, with its implicit arguments
/// found from their types.
pub(crate) fn lemma(cx: &mut Ctx, which: Builtin, args: &[Piped]) -> Result<Term> {
    let id = builtin_def(cx, which)?;
    let head = (Term::Def(id), cx.g().def(id).ty_value.clone());
    let args: Vec<Arg> = args.iter().map(Arg::Piped).collect();
    Ok(apply_args(cx, head, &args)?.0)
}

/// What a chain proves that isn't what the goal says. The message names the
/// end that differs, so a slip in the last line doesn't look like a broken
/// step.
fn goal_error(cx: &Ctx, expr: &Expr, goal: &Value, ends: &Ends) -> Diagnostic {
    let Expr::Calc { first, steps, .. } = expr else {
        unreachable!("only called on a calc");
    };
    let last = &steps.last().expect("a calc has a step").rhs;
    let wanted = show_prop(cx, goal);
    let error = |span: Span, label: String| {
        Diagnostic::error(
            "E-CALC-GOAL",
            format!(
                "the chain proves `{}`, but `{wanted}` is expected",
                ends.shown
            ),
        )
        .with_label(span, label)
    };
    let general = || error(expr.span(), "this chain doesn't prove the goal".into());
    let Some((rel, start, end)) = reading(cx, goal) else {
        return general();
    };
    let start_matches = cx.unify(&ends.start, &start).unwrap_or(false);
    let end_matches = cx.unify(&ends.end, &end).unwrap_or(false);
    if rel != ends.rel {
        if start_matches && end_matches && rel != Rel::Eq && ends.rel != Rel::Eq {
            let mut e = error(
                expr.span(),
                format!(
                    "the chain's relation is `{}`, but the goal's is `{}`",
                    ends.rel.symbol(),
                    rel.symbol()
                ),
            )
            .with_note(
                "a chain's relation is the fold of its steps' relations, left to right \
                 (`<=` then `<` is `<`), and is never weakened",
            );
            if ends.rel == Rel::Lt {
                e = e.with_note("`Nat.lessLe` turns `a < b` into `a <= b`");
            }
            return e;
        }
        return general();
    }
    match (start_matches, end_matches) {
        (false, true) => error(
            first.span(),
            format!(
                "the first line, `{}`, differs from the goal's left side `{}`",
                written_expr(cx, ends, true),
                cx.show(&start)
            ),
        ),
        (true, false) => error(
            last.span(),
            format!(
                "the last line, `{}`, differs from the goal's right side `{}`",
                written_expr(cx, ends, false),
                cx.show(&end)
            ),
        ),
        _ => general(),
    }
}

fn written_expr(cx: &Ctx, ends: &Ends, start: bool) -> String {
    let term = if start {
        &ends.start_term
    } else {
        &ends.end_term
    };
    written(cx, term)
}
