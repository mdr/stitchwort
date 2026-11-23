//! What a failed test can say about why it failed (D601): the shape of the
//! test's expression, through `let`s and `&&`, down to its comparisons.
//!
//! Elaborating the test notes the closed terms for the expressions
//! [`wanted`] finds ([`record_sides`], [`record_truth`]); [`build`] puts
//! them in a [`Probe`]. Nothing here is checked by the kernel, and nothing
//! runs unless the test fails: it is only how the failure is explained.

use std::rc::Rc;
use stitchwort_core::ProofMark;

use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::body_seen;
use stitchwort_core::{DataId, Term};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{BinOp, Expr};

use crate::check::builtin_data;
use crate::{Ctx, Elaborator, Probe, ProbeKind, SidesCapture};

/// How many `&&`s deep a probe goes.
const DEPTH: usize = 32;

/// Whether `expr` is a `match`, under any `let`s.
fn is_match(expr: &Expr) -> bool {
    match expr {
        Expr::Let { body, .. } => is_match(body),
        expr => matches!(expr, Expr::Match { .. }),
    }
}

/// The right-hand sides of the arms of the `match` that `expr` is (through
/// `let`s), where one is a comparison: their sides are noted in the arms'
/// own contexts (`arms`).
pub(crate) fn arm_bodies(expr: &Expr) -> stitchwort_core::collections::HashSet<Span> {
    let mut found = stitchwort_core::collections::HashSet::default();
    arm_bodies_in(expr, &mut found, 0);
    found
}

fn arm_bodies_in(
    expr: &Expr,
    found: &mut stitchwort_core::collections::HashSet<Span>,
    depth: usize,
) {
    if depth > DEPTH {
        return;
    }
    match expr {
        Expr::Let { body, .. } => arm_bodies_in(body, found, depth),
        Expr::Binary(BinOp::And, a, b) => {
            arm_bodies_in(a, found, depth + 1);
            arm_bodies_in(b, found, depth + 1);
        }
        Expr::Match { alts, .. } => {
            for body in alts.iter().filter_map(|a| a.body.as_ref()) {
                if matches!(body, Expr::Binary(..)) {
                    found.insert(body.span());
                }
            }
        }
        _ => {}
    }
}

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
    let (wanted, arm) = {
        let capture = cx.e.decl.sides_capture.borrow();
        (
            capture.wanted.contains(&expr.span()),
            capture.arm_bodies.contains(&expr.span()),
        )
    };
    if !wanted && !arm {
        return;
    }
    let flipped = x.span().start > y.span().start;
    let (op, left, right) = match (op, flipped) {
        (BinOp::Lt, true) => (">", b, a),
        (BinOp::Le, true) => (">=", b, a),
        (op, _) => (crate::numbers::op_text(op), a, b),
    };
    if arm {
        cx.e.decl
            .sides_capture
            .borrow_mut()
            .raw_sides
            .insert(expr.span(), (op, left.clone(), right.clone()));
    }
    if !wanted {
        return;
    }
    let (Some(left), Some(right)) = (close(cx, left), close(cx, right)) else {
        return;
    };
    cx.e.decl
        .sides_capture
        .borrow_mut()
        .sides
        .insert(expr.span(), (op, left, right));
}

/// If `expr` is an expression the test has a probe for, notes `term`, its
/// value as a `Bool`.
pub(crate) fn record_truth(cx: &Ctx, expr: &Expr, term: &Term) {
    if !cx
        .e
        .decl
        .sides_capture
        .borrow()
        .wanted
        .contains(&expr.span())
    {
        return;
    }
    if let Some(term) = close(cx, term) {
        cx.e.decl
            .sides_capture
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
        Expr::Match { .. } => match truth.as_ref().and_then(|t| arms(e, capture, t)) {
            Some(kind) => kind,
            None => ProbeKind::Other,
        },
        Expr::Let { body, .. } => {
            let mut inner = probe(e, capture, body, depth);
            // The `let`s are part of the terms already.
            // A `match` under the `let`s has no term of its own: the `let`s'
            // term is the `match` in their context.
            if matches!(inner.kind, ProbeKind::Other)
                && is_match(body)
                && let Some(kind) = truth.as_ref().and_then(|t| arms(e, capture, t))
            {
                inner.kind = kind;
            }
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

/// How the sides of an arm's comparison sit in the arm's term: the steps
/// from the root of the `Bool` the arm elaborates to, down to each side.
/// The arm is looked for again in the finished `match`, which is a helper
/// definition whose case tree the lifting rebuilt (its variables renumbered,
/// its metavariables solved), but whose leaves keep their shape.
#[derive(Clone, PartialEq)]
pub(crate) struct ArmShape {
    op: &'static str,
    span: Span,
    left: Vec<Step>,
    right: Vec<Step>,
}

/// One step down a term: the kind of node left, and which child is taken.
#[derive(Clone, PartialEq)]
struct Step {
    node: (u8, usize, usize),
    child: usize,
}

/// What a node is, ignoring what is under it.
fn node(t: &Term) -> (u8, usize, usize) {
    match t {
        Term::Var(_) => (0, 0, 0),
        Term::Def(d) => (1, d.0, 0),
        Term::Data(d, _) => (2, d.0, 0),
        Term::Ctor(d, c, _) => (3, d.0, *c),
        Term::Proj(d, i, _) => (4, d.0, *i),
        Term::App(..) => (5, 0, 0),
        Term::Lam(..) => (6, 0, 0),
        Term::Let(..) => (7, 0, 0),
        Term::Eq(..) => (8, 0, 0),
        Term::Pi(..) => (9, 0, 0),
        _ => (10, 0, 0),
    }
}

/// The children of `t`, left to right, with the number of binders each is
/// under.
fn children(t: &Term) -> Vec<(&Term, usize)> {
    let mut out = Vec::new();
    t.for_each_child(|c, binders| out.push((c, binders)));
    out
}

/// The steps from `root` to the first sub-term equal to `target` (which is
/// outside `binders` binders of its own there), wherever it sits.
fn path_to(root: &Term, target: &Term, binders: usize, depth: usize) -> Option<Vec<Step>> {
    let root = root.strip_loc();
    if crate::matching::same_shifted(target, root, binders, 0) {
        return Some(Vec::new());
    }
    if depth > 64 {
        return None;
    }
    for (child, (c, under)) in children(root).into_iter().enumerate() {
        if let Some(mut rest) = path_to(c, target, binders + under, depth + 1) {
            rest.insert(
                0,
                Step {
                    node: node(root),
                    child,
                },
            );
            return Some(rest);
        }
    }
    None
}

/// The sub-term of `root` at `path`, if `root` has that shape, as a term of
/// `root`'s own context: not if it refers to a variable bound on the way.
fn follow(g: &stitchwort_core::Ev, root: &Term, path: &[Step]) -> Option<Term> {
    let mut at = root.strip_loc();
    let mut binders = 0;
    for step in path {
        if node(at) != step.node {
            return None;
        }
        let (child, under) = *children(at).get(step.child)?;
        binders += under;
        at = child.strip_loc();
    }
    if binders == 0 {
        return Some(at.clone());
    }
    // Each binder's variable is replaced by a marker that must not survive.
    let hole = Term::Meta(usize::MAX);
    let mut moved = at.clone();
    for _ in 0..binders {
        moved = moved.instantiate(g, &hole).ok()?;
    }
    (!has_hole(&moved, 0)).then_some(moved)
}

/// Whether `t` holds the marker, counting a term nested too deep to look at
/// as holding it.
fn has_hole(t: &Term, depth: usize) -> bool {
    if depth > 256 || matches!(t, Term::Meta(m) if *m == usize::MAX) {
        return true;
    }
    let mut found = false;
    t.for_each_child(|c, _| found = found || has_hole(c, depth + 1));
    found
}

/// An arm that is a comparison, as elaborated: its term and sides, in the
/// context of `level` variables.
#[derive(Clone)]
pub(crate) struct ArmRaw {
    op: &'static str,
    span: Span,
    body: Term,
    left: Term,
    right: Term,
    level: usize,
}

/// Notes the arm whose right-hand side `rhs` was elaborated to `body`, if it
/// is a comparison with sides noted.
pub(crate) fn record_arm(cx: &Ctx, rhs: &Expr, body: &Term) {
    let mut capture = cx.e.decl.sides_capture.borrow_mut();
    let Some((op, left, right)) = capture.raw_sides.get(&rhs.span()).cloned() else {
        return;
    };
    let arm = ArmRaw {
        op,
        span: rhs.span(),
        body: body.clone(),
        left,
        right,
        level: cx.level(),
    };
    capture.arms.retain(|a| a.span != arm.span);
    capture.arms.push(arm);
}

/// The shape of `arm`, with its terms finished.
fn shape(e: &Elaborator, arm: &ArmRaw) -> Option<ArmShape> {
    let body = e.finish(&arm.body, arm.level).ok()?;
    let left = e.finish(&arm.left, arm.level).ok()?;
    let right = e.finish(&arm.right, arm.level).ok()?;
    Some(ArmShape {
        op: arm.op,
        span: arm.span,
        left: path_to(&body, &left, 0, 0)?,
        right: path_to(&body, &right, 0, 0)?,
    })
}

/// The probe of a `match` whose finished term is `truth`: `truth` with the
/// case tree of the helper it calls changed to answer, for an arm that is
/// a comparison, with its two sides.
fn arms(e: &Elaborator, capture: &SidesCapture, truth: &Term) -> Option<ProbeKind> {
    let shapes: Vec<ArmShape> = capture.arms.iter().filter_map(|a| shape(e, a)).collect();
    if shapes.is_empty() {
        return None;
    }
    let marker = e.kernel.env.registry().data(Builtin::List)?;
    let g = &e.ev();
    let term = instrument(g, &shapes, marker, truth)?;
    let arms = shapes.iter().map(|s| (s.op, s.span)).collect();
    Some(ProbeKind::Arms { term, marker, arms })
}

/// `t` (`let`s around the call of a helper) with the helper's body
/// instrumented in place of the helper.
fn instrument(
    g: &stitchwort_core::Ev,
    shapes: &[ArmShape],
    marker: DataId,
    t: &Term,
) -> Option<Term> {
    Some(match t {
        Term::Loc(_, t) => return instrument(g, shapes, marker, t),
        Term::Let(x, ty, v, b, erased, _) => Term::Let(
            x.clone(),
            ty.clone(),
            v.clone(),
            Rc::new(instrument(g, shapes, marker, b)?),
            *erased,
            ProofMark::Unknown,
        ),
        Term::App(f, a, icit) => {
            Term::App(Rc::new(instrument(g, shapes, marker, f)?), a.clone(), *icit)
        }
        Term::Def(d) => {
            let body = body_seen(g, *d)?;
            let mut found = false;
            let tree = tree(g, shapes, marker, body, &mut found);
            if !found {
                return None;
            }
            tree
        }
        _ => return None,
    })
}

/// A helper's body with each leaf that has the shape of a recorded arm
/// answering with its sides.
fn tree(
    g: &stitchwort_core::Ev,
    shapes: &[ArmShape],
    marker: DataId,
    t: &Term,
    found: &mut bool,
) -> Term {
    match t.strip_loc() {
        Term::Lam(x, icit, b, _) => Term::Lam(
            x.clone(),
            *icit,
            Rc::new(tree(g, shapes, marker, b, found)),
            ProofMark::Unknown,
        ),
        // The helper binds what it captured of the test's `let`s.
        Term::Let(x, ty, v, b, erased, _) => Term::Let(
            x.clone(),
            ty.clone(),
            v.clone(),
            Rc::new(tree(g, shapes, marker, b, found)),
            *erased,
            ProofMark::Unknown,
        ),
        Term::Case(ix, d, branches) => Term::Case(
            *ix,
            *d,
            branches
                .iter()
                .map(|b| Branch {
                    names: b.names.clone(),
                    body: (b.body.as_ref())
                        .map(|body| Rc::new(tree(g, shapes, marker, body, found))),
                })
                .collect(),
        ),
        Term::NumCase(ix, arms, default) => Term::NumCase(
            *ix,
            arms.iter()
                .map(|a| NumArm {
                    value: a.value.clone(),
                    body: Rc::new(tree(g, shapes, marker, &a.body, found)),
                })
                .collect(),
            Rc::new(tree(g, shapes, marker, default, found)),
        ),
        leaf => match answer(g, shapes, marker, leaf, located(t)) {
            Some(answer) => {
                *found = true;
                answer
            }
            None => leaf.clone(),
        },
    }
}

/// Where `t` says it is written, if it does.
fn located(t: &Term) -> Option<Span> {
    match t {
        Term::Loc(span, _) => Some(*span),
        _ => None,
    }
}

/// The marker for the arm `leaf` is, if it has the shape of one recorded;
/// when several do, they must find the same sides.
fn answer(
    g: &stitchwort_core::Ev,
    shapes: &[ArmShape],
    marker: DataId,
    leaf: &Term,
    at: Option<Span>,
) -> Option<Term> {
    let mut chosen: Option<(usize, Term, Term)> = None;
    for (k, shape) in shapes.iter().enumerate() {
        if at.is_some_and(|at| at != shape.span) {
            continue;
        }
        let (Some(left), Some(right)) =
            (follow(g, leaf, &shape.left), follow(g, leaf, &shape.right))
        else {
            continue;
        };
        match &chosen {
            None => chosen = Some((k, left, right)),
            Some((j, l, r)) => {
                let same = crate::matching::same(l, &left) && crate::matching::same(r, &right);
                if !same || shapes[*j].span != shape.span {
                    return None;
                }
            }
        }
    }
    let (k, left, right) = chosen?;
    let number = Term::Nat(Rc::new(num_bigint::BigUint::from(k)));
    let sides = Term::Ctor(marker, 1, vec![Rc::new(left), Rc::new(right)]);
    Some(Term::Ctor(marker, 1, vec![Rc::new(number), Rc::new(sides)]))
}
