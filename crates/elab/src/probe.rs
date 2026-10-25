//! What a failed test can say about why it failed (D601): the shape of the
//! test's expression, through `let`s and `&&`, down to its comparisons.
//!
//! Elaborating the test notes the closed terms for the expressions
//! [`wanted`] finds ([`record_sides`], [`record_truth`]); [`build`] puts
//! them in a [`Probe`]. Nothing here is checked by the kernel, and nothing
//! runs unless the test fails: it is only how the failure is explained.

use stitchwort_core::Term;
use stitchwort_core::registry::Builtin;
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{BinOp, Expr};

use crate::check::builtin_data;
use crate::{Ctx, Elaborator, Probe, ProbeKind, SidesCapture};

/// How many `&&`s deep a probe goes.
const DEPTH: usize = 32;

/// The spans of the expressions of `expr` worth noting terms for: the
/// comparisons, and the operands of `&&`, reached through `let`s and `&&`.
pub(crate) fn wanted(expr: &Expr) -> stitchwort_core::collections::HashSet<Span> {
    let mut found = stitchwort_core::collections::HashSet::default();
    walk(expr, &mut found, 0);
    found
}

fn walk(expr: &Expr, found: &mut stitchwort_core::collections::HashSet<Span>, depth: usize) {
    if depth > DEPTH {
        return;
    }
    found.insert(expr.span());
    match expr {
        Expr::Let { body, .. } => walk(body, found, depth),
        Expr::Binary(BinOp::And, a, b) => {
            walk(a, found, depth + 1);
            walk(b, found, depth + 1);
        }
        _ => {}
    }
}

/// `term`, which is in the context of `cx`, as a closed term: with a `let`
/// for each variable of the context, the value it was defined with (and for
/// the variables that aren't `let`s, only the unused proofs `&&` binds, a
/// placeholder: proofs aren't run).
fn close(cx: &Ctx, term: &Term) -> Option<Term> {
    let unit = builtin_data(cx, Builtin::Unit).ok()?;
    let mut term = term.clone();
    for i in (0..cx.level()).rev() {
        let (ty, value) = match &cx.lets[i] {
            Some(def) => (def.ty.clone(), def.value.clone()),
            None => (
                Term::Data(unit, Vec::new()),
                Term::Ctor(unit, 0, Vec::new()),
            ),
        };
        term = Term::let_(cx.names[i].clone(), ty, value, term);
    }
    Some(term)
}

/// If `expr` is a comparison the test being elaborated has a probe for,
/// notes its sides, in the order they were written (the parser turns `a > b`
/// into `b < a`: the operands are then in the opposite order in the
/// source).
pub(crate) fn record_sides(cx: &Ctx, expr: &Expr, op: BinOp, a: &Term, b: &Term) {
    let Expr::Binary(_, x, y) = expr else { return };
    if !cx.e.sides_capture.borrow().wanted.contains(&expr.span()) {
        return;
    }
    let flipped = x.span().start > y.span().start;
    let (op, left, right) = match (op, flipped) {
        (BinOp::Lt, true) => (">", b, a),
        (BinOp::Le, true) => (">=", b, a),
        (op, _) => (crate::numbers::op_text(op), a, b),
    };
    let (Some(left), Some(right)) = (close(cx, left), close(cx, right)) else {
        return;
    };
    cx.e.sides_capture
        .borrow_mut()
        .sides
        .insert(expr.span(), (op, left, right));
}

/// If `expr` is an expression the test has a probe for, notes `term`, its
/// value as a `Bool`.
pub(crate) fn record_truth(cx: &Ctx, expr: &Expr, term: &Term) {
    if !cx.e.sides_capture.borrow().wanted.contains(&expr.span()) {
        return;
    }
    if let Some(term) = close(cx, term) {
        cx.e.sides_capture
            .borrow_mut()
            .truths
            .insert(expr.span(), term);
    }
}

/// The probe of `expr`, from what was noted. Terms that can't be finished
/// (an unsolved metavariable) are left out: the failure is then explained
/// less, never wrongly.
pub(crate) fn build(e: &Elaborator, capture: &SidesCapture, expr: &Expr) -> Probe {
    let mut root = probe(e, capture, expr, 0);
    root.whole = !matches!(expr, Expr::Let { .. });
    root
}

fn probe(e: &Elaborator, capture: &SidesCapture, expr: &Expr, depth: usize) -> Probe {
    let span = expr.span();
    let truth = capture.truths.get(&span).and_then(|t| e.finish(t, 0).ok());
    let kind = match expr {
        Expr::Let { body, .. } => {
            let mut inner = probe(e, capture, body, depth);
            // The `let`s are part of the terms already.
            inner.truth = inner.truth.or(truth);
            return inner;
        }
        Expr::Binary(BinOp::And, a, b) if depth < DEPTH => ProbeKind::And(
            Box::new(probe(e, capture, a, depth + 1)),
            Box::new(probe(e, capture, b, depth + 1)),
        ),
        _ => match capture.sides.get(&span) {
            Some((op, left, right)) => match (e.finish(left, 0), e.finish(right, 0)) {
                (Ok(left), Ok(right)) => ProbeKind::Compare { op, left, right },
                _ => ProbeKind::Other,
            },
            None => ProbeKind::Other,
        },
    };
    Probe {
        span,
        truth,
        whole: false,
        kind,
    }
}
