//! Numbers: literals at `Nat` and `Int`, and arithmetic and comparisons, which
//! are typed a *group* at a time (docs/proposals/integers.md, "Literals" and
//! "Numeric expressions").
//!
//! A group is a maximal tree of `+ - * / %` and prefix `-`, or a comparison
//! (`=`, `!=`, `==`, `<`, `<=`) with the trees on both sides. Everything else
//! in it is a *leaf*. The group gets one operand type `T`, decided by, in
//! order: the expected type, a prefix `-` (which forces `Int`), the leaves
//! without literals, the other leaves, and finally a default of `Nat`. The
//! leaves are only *typed* out of order: the term built keeps every leaf in
//! its place, so evaluation is still left to right.

use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, eval, force};
use stitchwort_core::{DefId, Icit, Sort, Term, Value};
use stitchwort_syntax::ast::{BinOp, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{
    Ctx, PASS, Result, builtin_ctor, builtin_data, builtin_def, check, infer, insert, nat,
};

/// A metavariable that became `Nat` because a literal was checked against it
/// before anything else said what it was: remembered so that a later
/// mismatch can say why (the "defaulted literal" note).
pub(crate) struct Defaulted {
    meta: usize,
    span: Span,
    literal: BigUint,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Nat,
    Int,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Nat => "a `Nat`",
            Kind::Int => "an `Int`",
        }
    }
}

/// What a type is, as far as numbers are concerned.
enum Class {
    Num(Kind),
    /// An unsolved metavariable: defaulting may still settle it.
    Unknown,
    /// Any other type, including a user's own type named `Int`.
    Other,
}

/// Classifies `ty`, after substituting solved metavariables. Definitions
/// such as `Price = Int` are already unfolded by evaluation.
fn classify(cx: &Ctx, ty: &Value) -> Result<Class> {
    let g = cx.g();
    Ok(match force(g, ty.clone())? {
        Value::Data(d, params) if params.is_empty() && Some(d) == g.builtins.nat => {
            Class::Num(Kind::Nat)
        }
        Value::Data(d, params) if params.is_empty() && Some(d) == g.registry.data(Builtin::Int) => {
            Class::Num(Kind::Int)
        }
        Value::Neutral(Head::Meta(_), _) => Class::Unknown,
        _ => Class::Other,
    })
}

fn num_type(cx: &Ctx, kind: Kind) -> Result<Value> {
    let d = match kind {
        Kind::Nat => nat(cx)?,
        Kind::Int => builtin_data(cx, Builtin::Int)?,
    };
    Ok(Value::Data(d, Vec::new()))
}

// Literals

/// `k` or `-k`, for a numeral `k`: the number, whether it's negative, and
/// where it is.
pub(crate) fn literal(expr: &Expr) -> Option<(&BigUint, bool)> {
    match expr {
        Expr::Num(k, _) => Some((k, false)),
        Expr::Neg(inner, _) => match &**inner {
            Expr::Num(k, _) => Some((k, true)),
            _ => None,
        },
        _ => None,
    }
}

/// Checks the literal `k` (or `-k`) against `expected`: a `Nat` is the
/// number, an `Int` is `OfNat k` or `NegSucc (k - 1)` (and `-0` is
/// `OfNat 0`). An unknown type becomes `Nat` (or `Int`, for `-k`).
pub(crate) fn check_literal(
    cx: &mut Ctx,
    k: &BigUint,
    negative: bool,
    expected: &Value,
) -> Result<Term> {
    match classify(cx, expected)? {
        Class::Num(Kind::Nat) if negative => Err(negative_nat()
            .with_label(cx.span, "this is negative, but a `Nat` is expected here")
            .with_note("use an `Int` for numbers that can be negative")),
        Class::Num(Kind::Nat) => Ok(Term::Nat(Rc::new(k.clone()))),
        Class::Num(Kind::Int) => int_literal(cx, k, negative),
        Class::Unknown => {
            let kind = if negative { Kind::Int } else { Kind::Nat };
            let found = num_type(cx, kind)?;
            let meta = match force(cx.g(), expected.clone())? {
                Value::Neutral(Head::Meta(m), _) => Some(m),
                _ => None,
            };
            if !cx.unify(&found, expected)? {
                return Err(cx.mismatch(expected, &found));
            }
            if negative {
                return int_literal(cx, k, true);
            }
            if let Some(meta) = meta {
                cx.e.defaulted.borrow_mut().push(Defaulted {
                    meta,
                    span: cx.span,
                    literal: k.clone(),
                });
            }
            Ok(Term::Nat(Rc::new(k.clone())))
        }
        Class::Other => {
            let found = num_type(cx, if negative { Kind::Int } else { Kind::Nat })?;
            Err(cx
                .mismatch(expected, &found)
                .with_note("a numeral can only be the prelude's `Nat` or `Int`"))
        }
    }
}

fn int_literal(cx: &Ctx, k: &BigUint, negative: bool) -> Result<Term> {
    let (int, of_nat) = builtin_ctor(cx, Builtin::OfNat)?;
    let (_, neg_succ) = builtin_ctor(cx, Builtin::NegSucc)?;
    let zero = BigUint::default();
    Ok(if negative && *k != zero {
        let pred = k - 1u32;
        Term::ctor(int, neg_succ, vec![Term::Nat(Rc::new(pred))])
    } else {
        Term::ctor(int, of_nat, vec![Term::Nat(Rc::new(k.clone()))])
    })
}

fn negative_nat() -> Diagnostic {
    Diagnostic::error("E-TYPE-MISMATCH", "a `Nat` can't be negative")
}

/// Adds the "defaulted literal" explanation to `d` if one of `types` is a
/// metavariable that a literal made `Nat`.
pub(crate) fn explain_default(cx: &Ctx, d: Diagnostic, types: &[&Value]) -> Diagnostic {
    if d.code != "E-TYPE-MISMATCH" || d.notes.iter().any(|n| n.contains("because of the literal")) {
        return d;
    }
    let defaulted = cx.e.defaulted.borrow();
    for ty in types {
        let Value::Neutral(Head::Meta(m), _) = ty else {
            continue;
        };
        if let Some(found) = defaulted.iter().find(|x| x.meta == *m) {
            let k = &found.literal;
            return d
                .with_label(found.span, "this literal made it a `Nat`")
                .with_note(format!(
                    "this type became `Nat` because of the literal `{k}`, checked before \
                     anything said otherwise; write `({k}: Int)` if an `Int` was meant"
                ));
        }
    }
    d
}

// Groups

/// The part of a group above its leaves.
enum Node {
    Leaf(usize),
    Op(BinOp, Box<Node>, Box<Node>, Span),
    Neg(Box<Node>, Span),
}

struct Leaf<'a> {
    expr: &'a Expr,
    /// The operator it's an operand of, for error messages.
    op: &'static str,
    /// A literal `k` or `-k` on its own: it waits until `T` is decided.
    bare: bool,
    state: State,
}

enum State {
    Waiting,
    Inferred(Term, Value),
    /// Couldn't be inferred: checked against `T` at the end.
    Failed(Diagnostic),
    Done(Term),
}

#[derive(Default)]
struct Group<'a> {
    leaves: Vec<Leaf<'a>>,
    /// The first prefix `-`, including a negative literal's.
    minus: Option<Span>,
    /// Whether it has an arithmetic operator.
    arith: bool,
    /// Whether it's `<` or `<=`.
    ordering: bool,
}

/// What decided the group's type, for error messages.
#[derive(Clone, Copy)]
enum Decider {
    Expected,
    Leaf(usize),
    Minus(Span),
    Default,
}

pub(crate) fn is_arith(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
    )
}

fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::Ne | BinOp::EqEq | BinOp::Lt | BinOp::Le
    )
}

fn op_text(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "=",
        BinOp::Ne => "!=",
        BinOp::EqEq => "==",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Append => "++",
        BinOp::And => "&&",
        BinOp::Or => "||",
    }
}

impl<'a> Group<'a> {
    fn tree(&mut self, cx: &Ctx, expr: &'a Expr, op: &'static str) -> Result<Node> {
        cx.g().budget.nesting(PASS)?;
        match expr {
            Expr::Binary(o, a, b) if is_arith(*o) => {
                self.arith = true;
                let a = self.tree(cx, a, op_text(*o))?;
                let b = self.tree(cx, b, op_text(*o))?;
                Ok(Node::Op(*o, Box::new(a), Box::new(b), expr.span()))
            }
            Expr::Neg(inner, span) => {
                self.minus.get_or_insert(*span);
                if literal(expr).is_some() {
                    return Ok(self.leaf(expr, op));
                }
                Ok(Node::Neg(Box::new(self.tree(cx, inner, "-")?), *span))
            }
            _ => Ok(self.leaf(expr, op)),
        }
    }

    fn leaf(&mut self, expr: &'a Expr, op: &'static str) -> Node {
        self.leaves.push(Leaf {
            expr,
            op,
            bare: literal(expr).is_some(),
            state: State::Waiting,
        });
        Node::Leaf(self.leaves.len() - 1)
    }

    /// Whether the group has numeric syntax, so that it defaults to `Nat`.
    fn numeric(&self) -> bool {
        self.arith || self.ordering || self.minus.is_some() || self.leaves.iter().any(|l| l.bare)
    }
}

/// Rebuilds the group `expr` with each leaf replaced by `f` of it, in source
/// order (for computation mode, which runs effectful leaves first).
pub(crate) fn map_leaves(
    cx: &mut Ctx,
    expr: &Expr,
    f: &mut dyn FnMut(&mut Ctx, &Expr) -> Result<Expr>,
) -> Result<Expr> {
    fn tree(
        cx: &mut Ctx,
        expr: &Expr,
        f: &mut dyn FnMut(&mut Ctx, &Expr) -> Result<Expr>,
    ) -> Result<Expr> {
        cx.g().budget.nesting(PASS)?;
        match expr {
            Expr::Binary(op, a, b) if is_arith(*op) => {
                let a = tree(cx, a, f)?;
                let b = tree(cx, b, f)?;
                Ok(Expr::Binary(*op, Box::new(a), Box::new(b)))
            }
            Expr::Neg(inner, span) if literal(expr).is_none() => {
                Ok(Expr::Neg(Box::new(tree(cx, inner, f)?), *span))
            }
            _ => f(cx, expr),
        }
    }
    match expr {
        Expr::Binary(op, a, b) if is_comparison(*op) => {
            let a = tree(cx, a, f)?;
            let b = tree(cx, b, f)?;
            Ok(Expr::Binary(*op, Box::new(a), Box::new(b)))
        }
        _ => tree(cx, expr, f),
    }
}

/// Elaborates the group `expr` (arithmetic, a comparison, or a prefix `-`
/// that isn't part of a negative literal), against `expected` if
/// it's an arithmetic tree and that's given: its term and type.
pub(crate) fn group(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value)> {
    // An equation is elaborated as before groups where that works, so
    // existing programs elaborate to the same terms: inferring a side rather
    // than checking it can add annotations (`[]` is inferred as
    // `([] : List ?a)`), which would change their hashes. Where the old way
    // fails, as in `0 == x` for an `Int` `x`, the group rule decides.
    if let Expr::Binary(op @ (BinOp::Eq | BinOp::Ne | BinOp::EqEq), a, b) = expr
        && let Some((a, b, t)) = attempt(cx, |cx| equation_before_groups(cx, a, b))?
    {
        return equation(cx, *op, a, b, &t);
    }
    let mut g = Group::default();
    let (top, sides) = match expr {
        Expr::Binary(op, a, b) if is_comparison(*op) => {
            g.ordering = matches!(op, BinOp::Lt | BinOp::Le);
            let a = g.tree(cx, a, op_text(*op))?;
            let b = g.tree(cx, b, op_text(*op))?;
            (Some(*op), (a, Some(b)))
        }
        _ => (None, (g.tree(cx, expr, "")?, None)),
    };
    // Comparisons constrain their operands, not their result.
    let expected = if top.is_some() { None } else { expected };
    let what = if top.is_some() {
        "comparison"
    } else {
        "arithmetic"
    };
    // An equation with no arithmetic in it may be on any type.
    let equality =
        matches!(top, Some(BinOp::Eq | BinOp::Ne | BinOp::EqEq)) && !g.arith && g.minus.is_none();
    let mut decided: Option<(Value, Decider)> = None;

    // 1. The expected type.
    if let Some(e) = expected {
        match classify(cx, e)? {
            Class::Num(kind) => decided = Some((num_type(cx, kind)?, Decider::Expected)),
            Class::Unknown => {}
            Class::Other => {
                let op = match &sides.0 {
                    Node::Op(op, ..) => op_text(*op),
                    _ => "-",
                };
                return Err(cx.error(
                    "E-TYPE-MISMATCH",
                    format!("`{op}` gives a `Nat` or an `Int`"),
                    format!("but `{}` is expected here", cx.show(e)),
                ));
            }
        }
    }

    // 2. Minus signs.
    if let Some(span) = g.minus {
        match &decided {
            None => decided = Some((num_type(cx, Kind::Int)?, Decider::Minus(span))),
            Some((t, _)) if matches!(classify(cx, t)?, Class::Num(Kind::Nat)) => {
                return Err(negative_nat()
                    .with_label(
                        span,
                        "this `-` needs an `Int`, but a `Nat` is expected here",
                    )
                    .with_note("use an `Int` for numbers that can be negative"));
            }
            Some(_) => {}
        }
    }

    // 3. Pass 1: leaves that can't default anything.
    for i in 0..g.leaves.len() {
        if decided.is_some() {
            break;
        }
        let expr = g.leaves[i].expr;
        if !matches!(expr, Expr::Ann(..)) && (has_number(expr) || hopeless(expr)) {
            continue;
        }
        decided = infer_leaf(cx, &mut g, i, equality)?;
    }

    // 4. Pass 2: the rest, except bare literals.
    for i in 0..g.leaves.len() {
        if g.leaves[i].bare || !matches!(g.leaves[i].state, State::Waiting) {
            continue;
        }
        match &decided {
            Some((t, decider)) => {
                let (t, decider) = (t.clone(), *decider);
                let term = check_leaf(cx, &g, i, &t, decider, what)?;
                g.leaves[i].state = State::Done(term);
            }
            None => decided = infer_leaf(cx, &mut g, i, equality)?,
        }
    }

    // 5. Defaulting.
    if decided.is_none() {
        for (i, leaf) in g.leaves.iter().enumerate() {
            if let State::Inferred(_, ty) = &leaf.state
                && let Class::Num(kind) = classify(cx, ty)?
            {
                decided = Some((num_type(cx, kind)?, Decider::Leaf(i)));
                break;
            }
        }
    }
    if decided.is_none() {
        if g.numeric() {
            decided = Some((num_type(cx, Kind::Nat)?, Decider::Default));
        } else {
            // An equality with nothing numeric about it: the first leaf's
            // type, as before groups.
            for (i, leaf) in g.leaves.iter().enumerate() {
                if let State::Inferred(_, ty) = &leaf.state {
                    decided = Some((ty.clone(), Decider::Leaf(i)));
                    break;
                }
            }
        }
    }
    let Some((t, decider)) = decided else {
        // Nothing could be inferred.
        let failed = g.leaves.into_iter().rev().find_map(|l| match l.state {
            State::Failed(e) => Some(e),
            _ => None,
        });
        return Err(failed.expect("a group with no type has a leaf that failed"));
    };

    // 6. Finish the leaves.
    for i in 0..g.leaves.len() {
        let state = std::mem::replace(&mut g.leaves[i].state, State::Waiting);
        let term = match state {
            State::Done(term) => term,
            State::Inferred(term, ty) => {
                if !cx.unify(&ty, &t)? {
                    return Err(mixed(cx, &g, i, &ty, &t, decider, what));
                }
                term
            }
            State::Waiting | State::Failed(_) => check_leaf(cx, &g, i, &t, decider, what)?,
        };
        g.leaves[i].state = State::Done(term);
    }

    // 7. Build.
    let kind = match classify(cx, &t)? {
        Class::Num(kind) => Some(kind),
        _ => None,
    };
    let mut leaves: Vec<Option<Term>> = g
        .leaves
        .into_iter()
        .map(|l| match l.state {
            State::Done(term) => Some(term),
            _ => unreachable!("every leaf is finished"),
        })
        .collect();
    let a = build(cx, sides.0, kind, &mut leaves)?;
    let Some(op) = top else {
        if let Some(e) = expected
            && !cx.unify(&t, e)?
        {
            return Err(cx.mismatch(e, &t));
        }
        return Ok((a, t));
    };
    let b = build(
        cx,
        sides.1.expect("a comparison has two sides"),
        kind,
        &mut leaves,
    )?;
    let prop = Value::Sort(Sort::Prop);
    match op {
        BinOp::Lt | BinOp::Le => {
            let builtin = match (op, kind.expect("an ordering is on numbers")) {
                (BinOp::Lt, Kind::Nat) => Builtin::LessThan,
                (BinOp::Le, Kind::Nat) => Builtin::LessEq,
                (BinOp::Lt, Kind::Int) => Builtin::IntLessThan,
                (_, Kind::Int) => Builtin::IntLessEq,
                _ => unreachable!(),
            };
            Ok((apply_def(cx, builtin_def(cx, builtin)?, vec![a, b])?, prop))
        }
        _ => equation(cx, op, a, b, &t),
    }
}

/// `a = b`, `a != b` or `a == b`, with both sides of type `t`.
fn equation(cx: &mut Ctx, op: BinOp, a: Term, b: Term, t: &Value) -> Result<(Term, Value)> {
    let prop = Value::Sort(Sort::Prop);
    let ty = cx.quote(t)?;
    let eq = Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b));
    match op {
        BinOp::Eq => Ok((eq, prop)),
        // `a != b` means `Not (a = b)`.
        BinOp::Ne => {
            let not = builtin_def(cx, Builtin::Not)?;
            Ok((Term::app(Term::Def(not), eq), prop))
        }
        // `a == b` is `toBool d`, for a decision procedure `d` for `a = b`,
        // found as for `if h : a = b`.
        // The search sees the operands as variables where it can
        // (`bind.rs`), so they aren't computed here or by the kernel.
        _ => {
            let decision = crate::bind::decide(cx, &eq)?;
            let bool_data = builtin_data(cx, Builtin::Bool)?;
            Ok((
                decision.into_bool(cx, eq)?,
                Value::Data(bool_data, Vec::new()),
            ))
        }
    }
}

/// An equation the way it was elaborated before groups: the left side
/// inferred (or, if it can't be, the right) and the other side checked
/// against its type.
fn equation_before_groups(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Term, Value)> {
    Ok(match infer(cx, a).and_then(|(t, ty)| insert(cx, t, ty)) {
        Ok((a, ty)) => (a, check(cx, b, &ty)?, ty),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            let (b, ty) = infer(cx, b)?;
            let (b, ty) = insert(cx, b, ty)?;
            (check(cx, a, &ty)?, b, ty)
        }
        Err(e) => return Err(e),
    })
}

/// Runs `f`, or if it fails (other than by running out of resources),
/// undoes what it did (`undo.rs`) and gives `None`.
pub(crate) fn attempt<T>(cx: &mut Ctx, f: impl FnOnce(&mut Ctx) -> Result<T>) -> Result<Option<T>> {
    crate::undo::attempt(cx, f)
}

/// Infers leaf `i` (steps 3 and 4): the decision it makes, if any. A leaf
/// that can't be inferred is left for step 6, with everything its attempt
/// did undone.
fn infer_leaf(
    cx: &mut Ctx,
    g: &mut Group,
    i: usize,
    equality: bool,
) -> Result<Option<(Value, Decider)>> {
    let expr = g.leaves[i].expr;
    let (term, ty) = match speculate(cx, expr)? {
        Ok(found) => found,
        Err(e) => {
            g.leaves[i].state = State::Failed(e);
            return Ok(None);
        }
    };
    let decision = match classify(cx, &ty)? {
        Class::Num(kind) => Some((num_type(cx, kind)?, Decider::Leaf(i))),
        Class::Unknown => None,
        Class::Other if equality => Some((ty.clone(), Decider::Leaf(i))),
        Class::Other => {
            let op = g.leaves[i].op;
            return Err(Diagnostic::error(
                "E-TYPE-MISMATCH",
                format!("`{op}` works on `Nat` and `Int`"),
            )
            .with_label(expr.span(), format!("this is `{}`", cx.show(&ty))));
        }
    };
    g.leaves[i].state = State::Inferred(term, ty);
    Ok(decision)
}

/// Infers `expr`, or `Ok(Err(…))` if it can't be inferred, undoing whatever
/// the attempt did to metavariables and auto obligations: unification isn't
/// atomic, so a failed attempt may have solved some.
fn speculate(cx: &mut Ctx, expr: &Expr) -> Result<std::result::Result<(Term, Value), Diagnostic>> {
    let snapshot = crate::undo::Snapshot::take(cx);
    match infer(cx, expr).and_then(|(term, ty)| insert(cx, term, ty)) {
        Ok(found) => Ok(Ok(found)),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            snapshot.restore(cx);
            Ok(Err(e))
        }
        Err(e) => Err(e),
    }
}

/// Checks leaf `i` against the group's type `t`, saying what decided `t`
/// if the leaf doesn't fit.
fn check_leaf(
    cx: &mut Ctx,
    g: &Group,
    i: usize,
    t: &Value,
    decider: Decider,
    what: &str,
) -> Result<Term> {
    let expr = g.leaves[i].expr;
    // A local variable is inferred, so a mismatch can say what it is.
    if let Expr::Var(name) = expr
        && cx.lookup(&name.text).is_some()
        && matches!(classify(cx, t)?, Class::Num(_))
    {
        let (term, ty) = infer(cx, expr)?;
        let (term, ty) = insert(cx, term, ty)?;
        if !cx.unify(&ty, t)? {
            return Err(mixed(cx, g, i, &ty, t, decider, what));
        }
        return Ok(term);
    }
    check(cx, expr, t).map_err(|e| {
        if e.code == "E-TYPE-MISMATCH" && e.primary_span() == Some(expr.span()) {
            decided_by(cx, g, e, t, decider, what)
        } else {
            e
        }
    })
}

/// Leaf `i`, of type `found`, isn't the group's type `t`.
fn mixed(
    cx: &Ctx,
    g: &Group,
    i: usize,
    found: &Value,
    t: &Value,
    decider: Decider,
    what: &str,
) -> Diagnostic {
    let span = g.leaves[i].expr.span();
    let d = match (classify(cx, found), classify(cx, t)) {
        (Ok(Class::Num(f)), Ok(Class::Num(k))) => {
            Diagnostic::error("E-TYPE-MISMATCH", "type mismatch")
                .with_label(
                    span,
                    format!(
                        "this is {}, but this {what} is on `{}`",
                        f.name(),
                        cx.show(t)
                    ),
                )
                .with_note(match k {
                    Kind::Int => "a `Nat` becomes an `Int` with `.toInt`, as in `n.toInt`",
                    Kind::Nat => {
                        "an `Int` becomes a `Nat` with `Int.toNat` (negatives become 0) or \
                     `Int.toNatChecked`"
                    }
                })
        }
        _ => Diagnostic::error("E-TYPE-MISMATCH", "type mismatch").with_label(
            span,
            format!(
                "expected `{}`, but this has type `{}`",
                cx.show(t),
                cx.show(found)
            ),
        ),
    };
    let d = explain_default(cx, d, &[found]);
    decided_by(cx, g, d, t, decider, what)
}

/// Adds to `d` what decided the group's type `t`.
fn decided_by(
    cx: &Ctx,
    g: &Group,
    d: Diagnostic,
    t: &Value,
    decider: Decider,
    what: &str,
) -> Diagnostic {
    let shown = cx.show(t);
    match decider {
        Decider::Expected => d.with_note(format!(
            "this {what} is on `{shown}` because `{shown}` is expected here"
        )),
        Decider::Leaf(j) => d.with_label(
            g.leaves[j].expr.span(),
            format!("this {what} is on `{shown}` because of this"),
        ),
        Decider::Minus(span) => d.with_label(span, "this `-` makes it an `Int`"),
        Decider::Default => d.with_note(format!(
            "this {what} is on `Nat` because nothing in it says otherwise"
        )),
    }
}

/// Assembles the term for `node`, at the number type `kind`.
fn build(
    cx: &mut Ctx,
    node: Node,
    kind: Option<Kind>,
    leaves: &mut [Option<Term>],
) -> Result<Term> {
    cx.g().budget.nesting(PASS)?;
    match node {
        Node::Leaf(i) => Ok(leaves[i].take().expect("each leaf is used once")),
        Node::Op(op, a, b, span) => {
            let a = build(cx, *a, kind, leaves)?;
            let b = build(cx, *b, kind, leaves)?;
            let builtin = match (op, kind.expect("arithmetic is on numbers")) {
                (BinOp::Add, Kind::Nat) => Builtin::Add,
                (BinOp::Sub, Kind::Nat) => Builtin::Sub,
                (BinOp::Mul, Kind::Nat) => Builtin::Mul,
                (BinOp::Div, Kind::Nat) => Builtin::Div,
                (BinOp::Mod, Kind::Nat) => Builtin::Mod,
                (BinOp::Add, Kind::Int) => Builtin::IntAdd,
                (BinOp::Sub, Kind::Int) => Builtin::IntSub,
                (BinOp::Mul, Kind::Int) => Builtin::IntMul,
                (BinOp::Div, Kind::Int) => Builtin::IntDiv,
                (BinOp::Mod, Kind::Int) => Builtin::IntMod,
                _ => unreachable!("only arithmetic operators are nodes"),
            };
            let id = builtin_def(cx, builtin)?;
            // The obligation `d != 0` of `/` and `%` is reported at the
            // operation.
            let saved = std::mem::replace(&mut cx.span, span);
            let term = apply_def(cx, id, vec![a, b]);
            cx.span = saved;
            Ok(Term::Loc(span, Rc::new(term?)))
        }
        Node::Neg(x, span) => {
            let x = build(cx, *x, kind, leaves)?;
            let neg = builtin_def(cx, Builtin::IntNeg)?;
            Ok(Term::Loc(span, Rc::new(Term::app(Term::Def(neg), x))))
        }
    }
}

/// `id args`, with any implicit or auto parameters after them inserted.
fn apply_def(cx: &mut Ctx, id: DefId, args: Vec<Term>) -> Result<Term> {
    let g = cx.g();
    let mut term = Term::Def(id);
    let mut ty = g.def(id).ty_value.clone();
    for arg in args {
        let Value::Pi(_, Icit::Explicit, _, cod) = force(g, ty)? else {
            unreachable!("built-in operators take two explicit arguments");
        };
        ty = cod.apply_lazy(g, || eval(g, &cx.env, &arg))?;
        term = Term::app(term, arg);
    }
    Ok(insert(cx, term, ty)?.0)
}

/// Whether inferring `expr` is sure to fail, so pass 1 doesn't try.
fn hopeless(expr: &Expr) -> bool {
    matches!(expr, Expr::Lam(..) | Expr::Record { base: None, .. })
}

/// Whether `expr` contains a numeric literal anywhere.
fn has_number(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        match e {
            Expr::Num(..) => return true,
            Expr::Var(_)
            | Expr::Str(..)
            | Expr::Char(..)
            | Expr::Type(..)
            | Expr::Prop(_)
            | Expr::Hole(_)
            | Expr::Unit(_) => {}
            Expr::App(a, b)
            | Expr::Arrow(a, b)
            | Expr::Binary(_, a, b)
            | Expr::Seq(a, b)
            | Expr::Pipe(a, b)
            | Expr::Tuple(a, b, _) => {
                stack.extend([&**a, &**b]);
            }
            Expr::Neg(a, _) | Expr::NamedArg(_, a, _) | Expr::Field(a, _) => stack.push(a),
            Expr::Lam(_, body, _) => stack.push(body),
            Expr::Pi { dom, cod, .. } => stack.extend([&**dom, &**cod]),
            Expr::If {
                cond,
                then,
                otherwise,
                ..
            } => stack.extend([&**cond, &**then, &**otherwise]),
            Expr::Ann(e, t, _) => stack.extend([&**e, &**t]),
            Expr::List(items, _) => stack.extend(items),
            Expr::Record { base, fields, .. } => {
                stack.extend(base.as_deref());
                stack.extend(fields.iter().map(|(_, e)| e));
            }
            Expr::Effect(row, ty) => {
                stack.extend(&row.abilities);
                stack.push(ty);
            }
            Expr::Let {
                ty, value, body, ..
            } => {
                stack.extend(ty.as_deref());
                stack.extend([&**value, &**body]);
            }
            // The definitions are elaborated on their own.
            Expr::LocalDefs { body, .. } => stack.push(body),
            Expr::Calc { first, steps, .. } => {
                stack.push(first);
                for step in steps {
                    stack.push(&step.rhs);
                    stack.extend(step.proof.as_ref());
                }
            }
            Expr::Rewrite { rules, body, .. } => {
                stack.extend(rules.iter().map(|r| &r.proof));
                stack.extend(body.as_deref());
            }
            Expr::Match {
                scrutinees, alts, ..
            } => {
                stack.extend(scrutinees.iter().map(|s| &s.expr));
                stack.extend(alts.iter().map(|a| &a.body));
            }
            Expr::Handle { body, clauses, .. } => {
                stack.push(body);
                for clause in clauses {
                    stack.push(match clause {
                        stitchwort_syntax::ast::Clause::Return { body, .. }
                        | stitchwort_syntax::ast::Clause::Op { body, .. } => body,
                    });
                }
            }
        }
    }
    false
}
