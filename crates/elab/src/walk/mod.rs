//! The walk, `byWalking [lemmas] then t` (docs/proposals/proof-walk-step.md,
//! as amended by docs/reviews/SW-4238-walk-step-review.md; docs/syntax.md,
//! "byWalking").
//!
//! A walk proves a statement about effectful code, `R … (() => f args) post`
//! for a **family** `R`, by following `f`'s body: it writes the chain of the
//! family's lemmas a person would write, and the elaborator checks that
//! chain as it checks a hand-written one. Nothing here is trusted and the
//! kernel sees only applications of the family's lemmas, proof `match`es
//! and the closers' terms.
//!
//! **Families** are declared by attributes on std's (or a project's)
//! lemmas, so nothing here names one: `@[walk.bind]` on a lemma
//! `R … (() => j (p())) post` whose first explicit premise is about `p` and
//! whose last is a `∀` over `p`'s value ending in `R` at `j`; `@[walk.done]`
//! on `R … (() => x) post`; `@[walk.weaken]` on one whose first explicit
//! premise is `R` with another post and whose last is the implication. A
//! then-lemma whose first premise is in another relation (`Parse.Reads0`
//! for `Parse.givesAfter0`) is a bridge: a lemma in that relation fits a
//! call there.
//!
//! A family's relation may have two thunks (`Parse.Follows`, two runs of a
//! parser): its walk follows both runs in lockstep ([`two`]).
//!
//! **Steps.** The goal's own function is walked through once (its case
//! tree split on, or its body unfolded); then, at each point of the body:
//! - `Effect.bind c k`: a lemma for the call `c` (below), the family's
//!   then-lemma, and the walk goes on in `k`, its value named after `k`'s
//!   binder (or `<function>Value`, for a binder the compiler made); where
//!   `c` isn't one call (`f (g ())`, a split), it is walked as the
//!   then-lemma's first premise and the walk goes on in `k` where it ends
//!   ([`nested_bind`]);
//! - `if c` (also on a proposition, `Decidable.elim`) and a lifted `match`
//!   (whose case tree is read here, a level at a time): a split on the
//!   scrutinee where the program's case tree is stuck, a proof
//!   `match branchN: c` with the program's own names for the fields. A
//!   branch's goal is the goal before the split with the equation's
//!   pattern for the scrutinee ([`Planned`]), read folded;
//! - a value, `Done x`: the family's done-lemma;
//! - a call in tail position: its lemma, weakened when its post differs;
//!   or, if the brackets say `unfold f`, its body, walked.
//!
//! **Which lemma a call uses**, in this order (SW-4238 §3.3): a term in the
//! brackets that fits; the theorem being proved, at a call of its own
//! function; a hypothesis in scope that fits; the `@[walk]` lemma for the
//! function and family. Two that fit in one tier is an error, never a
//! choice. A lemma fits when its thunk unifies with the call as written,
//! its other arguments fixed by the call, by a premise a hypothesis is, or
//! as the one hypothesis of their type; a premise (a proposition) is a
//! leaf. A value the call fixes that isn't a variable is passed as a local
//! definition, so the premises after it are checked with it known.
//!
//! **Leaves** (a value's post, a lemma's premise, a weakening's
//! implication) are closed by, in order: `()`; a hypothesis that is the
//! goal; the closers of `cases` (a part of a hypothesis, two that
//! contradict); computation; a conjunction built from its parts;
//! `arithmetic`, with the parts of the conjunctions in scope; then `t` from
//! `then t`. A leaf whose goal still has an unknown in it waits for it. A
//! leaf none closes is `E-WALK`, with its goal and the path to it.
//!
//! **Stops.** Everything else is `E-WALK` at the walk, naming the call or
//! construct and showing the goal: a call with no lemma (the note gives
//! both fixes), two lemmas that fit, a construct the walk doesn't follow
//! (`handle`, `translate`, effect-polymorphic code, a `match` on numbers,
//! an operation performed directly), more than [`PATH_CAP`] paths.
//!
//! **Expanding.** Every check of a walk records the chain it wrote, as text
//! with the user's own terms quoted from the source ([`Piece`]), for
//! `check --expand-walk` ([`expand_file`]), with a trace of the lemma used
//! at each call.

mod expand;
mod leaf;
mod registry;
mod two;

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, Spine, apply, force, force_solved, unfold_once};
use stitchwort_core::{DataId, DefId, Icit, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Expr, Pattern, Walk};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, Result, check, infer};
use crate::undo::{Snapshot, fatal};

use expand::*;
pub use expand::{Piece, WalkExpansion, expand_file, trace_line};
use leaf::*;
use registry::*;
pub(crate) use registry::{WALK, WALK_BIND, WALK_DONE, WALK_WEAKEN};

/// The most paths one walk follows: each split adds its alternatives
/// less one. Past this the walk stops (SW-4238 §3.5); a split whose arms
/// share a long tail is better made a function with its own lemma.
pub(crate) const PATH_CAP: usize = 64;

/// The most steps the walk may take in the code before it stops: reductions
/// and unfolds that never settle ("the code keeps computing").
const STEP_CAP: usize = 1000;

/// A bracket lemma that fits no call or leaf in the walk.
pub(crate) const UNUSED_ITEM: &str = "W-WALK-UNUSED-ITEM";

/// What the walks checked so far have recorded: one [`CallInfo`] per check
/// of a written walk, and the places it went on from.
#[derive(Default)]
pub(crate) struct Walks {
    calls: Vec<CallInfo>,
    nodes: Vec<NodeInfo>,
    /// The premises being walked inside one another now, outermost first.
    nesting: Vec<leaf::Nested>,
}

struct CallInfo {
    keyword: Span,
    span: Span,
    items: Vec<Item>,
    /// For each item, whether the walk used it (as a call's lemma or a
    /// leaf's proof).
    used: Vec<bool>,
    body: Option<Expr>,
    /// The theorem being proved, by name, and the function its statement
    /// is about: a call of that function uses the theorem.
    own: Option<(String, DefId)>,
    root: u32,
}

#[derive(Clone)]
enum Item {
    Lemma(Expr),
    Unfold(String),
}

#[derive(Clone)]
struct NodeInfo {
    call: usize,
    kind: Kind,
    /// Where in the program this is, for messages: the function and the
    /// splits taken.
    place: Rc<str>,
    /// The calls taken to reach this place, in order, so that a repeated
    /// call can say which occurrence it is.
    calls_before: Rc<Vec<Callee>>,
    text: Option<Vec<Piece>>,
    /// The lemma used here, and what was unfolded, for the trace.
    trace: Vec<Vec<Piece>>,
    /// The paths a split here adds: its constructors but one.
    split: usize,
    /// For each run, the function whose own case tree a split here was
    /// made in: that run's code is still a call of it, walked through once
    /// more. Empty where none was.
    through: Vec<Option<DefId>>,
    /// After a two-run bind whose values the lemma says are equal: the
    /// second run's value is rewritten to the first's before the walk goes
    /// on, so that a split on it is made once, for both runs.
    equate: Option<Rc<Equate>>,
    /// A split's branch: the goal before the split, which the branch's
    /// goal is with the split's equation's right side for its scrutinee.
    planned: Option<Rc<Planned>>,
    /// Within the walk of a bound computation that isn't one call
    /// ([`nested_bind`]): where that computation ends, the walk goes on in
    /// the code after it. Kept by the places of the same walk, not by
    /// leaves.
    cont: Option<Rc<Cont>>,
    /// The first premise of a [`nested_bind`].
    nest: Option<Rc<Nest>>,
}

/// What the goal at the first premise of a [`nested_bind`] is: the
/// application it is in leaves its thunks and its post unknown (`p ()`
/// against the code is no pattern, and the post is fixed only by the
/// premise after it), so the walk fixes them.
struct Nest {
    /// Each run's bound computation: the thunks are `() => c`.
    codes: Vec<Value>,
    /// Which of the relation's arguments is the post, and what it is: what
    /// the rest of the code needs of the values.
    post_at: usize,
    post: Term,
}

/// The code after a bound computation that isn't one call: each run's
/// continuation, and the one this walk is itself inside, if any.
struct Cont {
    ks: Vec<Value>,
    parent: Option<Rc<Cont>>,
}

/// The goal a split's branch has, read back folded: the generalised goal a
/// `match` gives its arms is unfolded (the scrutinee is found in the
/// relation's unfolding), where the walk reads its thunk. The same for the
/// goal after a two-run walk's `rewrite`, which is unfolded too.
struct Planned {
    /// The goal before the split, folded, in `base` variables.
    goal: Term,
    /// The scrutinee, in `base` variables.
    needle: Term,
    base: usize,
    /// What `needle` becomes in the branch.
    with: Replacement,
}

enum Replacement {
    /// The right side of the equation the branch is checked with:
    /// `needle = pattern`.
    Equation(String),
    /// The variable at this level.
    Variable(usize),
}

/// The names a two-run bind gave its values and their fact.
struct Equate {
    value: String,
    twin: String,
    fact: String,
}

#[derive(Clone, Copy)]
enum Kind {
    /// The rest of a body, in the family whose relation is this.
    Step(DefId),
    /// A goal the closers close.
    Leaf,
}

fn var(text: impl Into<String>, span: Span) -> Expr {
    Expr::Var(ast::Name {
        text: text.into(),
        span,
    })
}

fn app(f: Expr, arg: Expr) -> Expr {
    Expr::App(Box::new(f), Box::new(arg))
}

/// A lambda the walk writes. Its names' spans are empty, at the walk's
/// end: they were never written, and a binder named as a function is
/// (`number`) is no lambda written by mistake (`W-LAMBDA-SHADOW`). With no
/// names (a premise that is no `∀`, so there is nothing to bind) it is
/// the body itself: a lambda takes at least one parameter.
fn lambda(names: &[String], body: Expr, span: Span) -> Expr {
    if names.is_empty() {
        return body;
    }
    let at = Span {
        start: span.end,
        ..span
    };
    Expr::Lam(
        (names.iter())
            .map(|n| ast::Name {
                text: n.clone(),
                span: at,
            })
            .collect(),
        Box::new(body),
        span,
    )
}

fn resume(id: u32, span: Span) -> Expr {
    Expr::Walk(Box::new(Walk {
        items: Vec::new(),
        body: None,
        keyword: span,
        span,
        resume: Some(id),
    }))
}

pub(crate) fn no_goal(_cx: &Ctx, expr: &Expr) -> Diagnostic {
    Diagnostic::error("E-WALK", "a walk needs to know what it proves")
        .with_label(expr.span(), "the expected type isn't known here")
        .with_note("give it a type: `(byWalking [] : R … (() => f x) post)`")
}

/// A walk, or a place one goes on from, against `expected`.
pub(crate) fn check_walk(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    crate::queue::tactic_or_wait(cx, expr, expected, walk_goal)
}

fn walk_goal(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Walk(walk) = expr else {
        unreachable!("only called on a walk")
    };
    match walk.resume {
        Some(id) => go_on(cx, id, expected),
        None => start(cx, walk, expected),
    }
}

/// A written walk: reads its family off the goal, files the call, and
/// walks the goal's body from its function's unfolding.
fn start(cx: &mut Ctx, walk: &Walk, expected: &Value) -> Result<Term> {
    let families = families(cx);
    let Some((family, args)) = read_goal(cx, expected, &families, None)? else {
        let known: Vec<String> = families
            .iter()
            .map(|f| format!("`{}`", written_name(cx, f.relation)))
            .collect();
        return Err(Diagnostic::error(
            "E-WALK",
            "a walk proves a statement about effectful code in a family it knows",
        )
        .with_label(walk.keyword, "the goal isn't one")
        .with_note(format!("the goal is {}", cx.show(expected)))
        .with_note(if known.is_empty() {
            "no family is loaded: a family is declared by `@[walk.bind]`, `@[walk.done]` and \
             `@[walk.weaken]` on its lemmas"
                .to_string()
        } else {
            format!("the families loaded: {}", known.join(", "))
        }));
    };
    let items = walk
        .items
        .iter()
        .map(|item| match item {
            Expr::App(f, x)
                if matches!(&**f, Expr::Var(n) if n.text == "unfold")
                    && matches!(&**x, Expr::Var(_)) =>
            {
                let Expr::Var(n) = &**x else { unreachable!() };
                Item::Unfold(n.text.clone())
            }
            other => Item::Lemma(other.clone()),
        })
        .collect::<Vec<_>>();
    // An item that doesn't elaborate is the writer's mistake, not a lemma
    // that fits nothing: reported as it stands.
    for item in &items {
        if let Item::Lemma(e) = item {
            let snapshot = Snapshot::take(cx);
            let inferred = infer(cx, e);
            snapshot.restore(cx);
            inferred?;
        }
    }
    let bodies = (family.thunks.iter())
        .map(|&i| thunk_body(cx, &args[i]))
        .collect::<Result<Vec<_>>>()?;
    let own = match head_of(&bodies[0]) {
        Some(Callee::Def(f)) => own_theorem(cx).map(|t| (t, f)),
        _ => None,
    };
    let root = {
        let mut walks = cx.e.session.walks.borrow_mut();
        let call = walks.calls.len();
        let root = walks.nodes.len() as u32;
        let used = vec![false; items.len()];
        walks.calls.push(CallInfo {
            keyword: walk.keyword,
            span: walk.span,
            items,
            used,
            body: walk.body.clone(),
            own,
            root,
        });
        let mut names: Vec<String> = Vec::new();
        for body in &bodies {
            let name = match head_of(body) {
                Some(Callee::Def(f)) => format!("`{}`", written_name(cx, f)),
                _ => "the goal's code".to_string(),
            };
            if !names.contains(&name) {
                names.push(name);
            }
        }
        let place = format!("in {}", names.join(" and "));
        walks.nodes.push(NodeInfo {
            call,
            kind: Kind::Step(family.relation),
            place: place.into(),
            calls_before: Rc::new(Vec::new()),
            text: None,
            trace: Vec::new(),
            split: 0,
            through: Vec::new(),
            equate: None,
            planned: None,
            cont: None,
            nest: None,
        });
        (call, root)
    };
    let (call, root) = root;
    let result = step(cx, root, &family, args, true, expected);
    if result.is_ok() {
        warn_unused(cx, call);
    }
    result
}

/// Warns about each bracket lemma the walk never used, at the item: it fits
/// no call or leaf the walk met, so it is either a leftover or a mistake.
fn warn_unused(cx: &Ctx, call: usize) {
    let unused: Vec<Expr> = {
        let walks = cx.e.session.walks.borrow();
        let info = &walks.calls[call];
        (info.items.iter().zip(&info.used))
            .filter_map(|(item, used)| match item {
                Item::Lemma(e) if !*used => Some(e.clone()),
                _ => None,
            })
            .collect()
    };
    for e in unused {
        let span = e.span();
        let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
        if warnings
            .iter()
            .any(|w| w.code == UNUSED_ITEM && w.labels.first().is_some_and(|l| l.span == span))
        {
            continue;
        }
        warnings.push(
            Diagnostic::warning(UNUSED_ITEM, "this lemma fits no call the walk met")
                .with_label(span, "unused")
                .with_note(
                    "remove it from the brackets; if a call was meant to use it, the walk \
                     didn't meet that call as written",
                ),
        );
    }
}

/// Marks bracket item `at` of the walk at `call` as used.
fn mark_used(cx: &Ctx, call: usize, at: usize) {
    if let Some(used) = cx.e.session.walks.borrow_mut().calls[call].used.get_mut(at) {
        *used = true;
    }
}

/// The place of a call of `callee`: the base place, or, if the same call was
/// made before on this path, which occurrence it is (`the second call of
/// `look` in `lookTwice``).
fn at_call(cx: &Ctx, info: &NodeInfo, callee: Callee) -> Rc<str> {
    let before = info.calls_before.iter().filter(|c| **c == callee).count();
    if before == 0 {
        return info.place.clone();
    }
    format!(
        "the {} call of `{}` {}",
        ordinal(before + 1),
        callee.shown(cx),
        info.place
    )
    .into()
}

/// `n` as an ordinal word, for the first few occurrences a walk names.
fn ordinal(n: usize) -> String {
    match n {
        1 => "first".into(),
        2 => "second".into(),
        3 => "third".into(),
        4 => "fourth".into(),
        5 => "fifth".into(),
        6 => "sixth".into(),
        7 => "seventh".into(),
        8 => "eighth".into(),
        9 => "ninth".into(),
        10 => "tenth".into(),
        _ => format!("{n}th"),
    }
}

/// The name of the theorem whose body is being checked, if it is one.
fn own_theorem(cx: &Ctx) -> Option<String> {
    let owner = cx.e.decl.owner.borrow();
    if owner.len() != 1 {
        return None;
    }
    Some(crate::scope::display(&owner[0]).to_string())
}

/// The place `id` of a walk, against `expected`.
fn go_on(cx: &mut Ctx, id: u32, expected: &Value) -> Result<Term> {
    let node = {
        let walks = cx.e.session.walks.borrow();
        match walks.nodes.get(id as usize) {
            Some(node) => node.clone(),
            None => {
                return Err(Diagnostic::error("E-WALK", "this isn't a place in a walk")
                    .with_label(cx.span, "here"));
            }
        }
    };
    match node.kind {
        Kind::Leaf => leaf(cx, id, &node, expected),
        Kind::Step(relation) => {
            let families = families(cx);
            let Some(family) = families.iter().find(|f| f.relation == relation).cloned() else {
                return Err(stuck(
                    cx,
                    &node,
                    expected,
                    "its family is no longer loaded",
                    &[],
                ));
            };
            if let Some(planned) = &node.planned
                && let Some(goal) = planned_goal(cx, planned, expected)?
            {
                let Some((_, args)) = read_goal(cx, &goal, &families, Some(relation))? else {
                    return Err(stuck(
                        cx,
                        &node,
                        expected,
                        "the branch's goal can't be read",
                        &[],
                    ));
                };
                return step(cx, id, &family, args, false, &goal);
            }
            let Some((_, args)) = read_goal(cx, expected, &families, Some(relation))? else {
                return Err(stuck(
                    cx,
                    &node,
                    expected,
                    "the goal here isn't a statement in the walk's family",
                    &[],
                ));
            };
            step(cx, id, &family, args, false, expected)
        }
    }
}

/// A split branch's goal, folded, if it is `expected`.
fn planned_goal(cx: &mut Ctx, planned: &Planned, expected: &Value) -> Result<Option<Value>> {
    let g = cx.g();
    let depth = cx.level();
    let with = match &planned.with {
        Replacement::Equation(equation) => {
            let Some(level) = cx.lookup(equation) else {
                return Ok(None);
            };
            let Value::Eq(_, _, pattern) = force(&g, cx.types[level].clone())? else {
                return Ok(None);
            };
            cx.quote_folded(&pattern)?
        }
        Replacement::Variable(level) => Term::Var(depth - 1 - level),
    };
    let term = crate::check::abstract_needle(
        &g,
        &planned.goal,
        planned.base,
        &planned.needle,
        depth - planned.base,
        &with,
    )?;
    let goal = cx.eval(&term)?;
    Ok(cx.conv_now(&goal, expected)?.then_some(goal))
}

/// The goal as a family's relation applied to arguments: as written (a
/// folded call), or, if it has been unfolded, by unifying it with the
/// relation applied to unknowns (only `only`'s, if given).
fn read_goal(
    cx: &mut Ctx,
    expected: &Value,
    families: &[Family],
    only: Option<DefId>,
) -> Result<Option<(Family, Vec<Value>)>> {
    let g = cx.g();
    let mut shown = force_solved(&g, expected.clone())?;
    // The declaration's own goal, as written, if that is what this is.
    if !matches!(shown, Value::Call(..) | Value::Neutral(Head::Def(_), _))
        && let Some((level, written)) = cx.goal.clone()
        && level == cx.level()
        && let Ok(value) = cx.eval(&written)
        && crate::undo::unify(cx, &value, expected)?
    {
        shown = force_solved(&g, value)?;
    }
    if let Value::Call(id, spine, _) | Value::Neutral(Head::Def(id), spine) = &shown
        && let Some(f) = families.iter().find(|f| f.relation == *id)
        && only.is_none_or(|o| o == *id)
        && spine.len() == f.arity
    {
        let args = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>();
        if let Some(args) = args {
            return Ok(Some((f.clone(), args)));
        }
    }
    for f in families {
        if only.is_some_and(|o| o != f.relation) {
            continue;
        }
        let g = cx.g();
        let mut ty = force(&g, g.def(f.relation).ty_value().clone())?;
        let mut metas = Vec::new();
        let mut candidate = cx.eval(&Term::Def(f.relation))?;
        while let Value::Pi(_, icit, _, cod) = &ty {
            // Untyped: a typed unknown for the thunk's value type stops
            // `?p` being solved by a thunk whose type mentions it.
            let m = cx.fresh_meta();
            let v = cx.eval(&m)?;
            candidate = stitchwort_core::value::apply_icit(&g, candidate, v.clone(), *icit)?;
            ty = force(&g, cod.apply(&g, v)?)?;
            metas.push(m);
        }
        if metas.len() != f.arity {
            continue;
        }
        // Unfolded as far as the goal is: the unifier compares a folded
        // call of the relation with a `∀` only after unfolding both.
        let candidate = match force_solved(&g, expected.clone())? {
            Value::Call(..) | Value::Neutral(..) => candidate,
            _ => force(&g, candidate)?,
        };
        // By the arguments: compared by their unfoldings, `ReadsAt start ?p
        // …` against `ReadsAt start (() => Done x) …` meets `?p ()` against
        // a computed `Done x`, which no pattern solves.
        if crate::undo::unify_solving_arguments(cx, &candidate, expected)? {
            let args = metas
                .iter()
                .map(|m| Ok(force_solved(&cx.g(), cx.eval(m)?)?))
                .collect::<Result<Vec<_>>>()?;
            return Ok(Some((f.clone(), args)));
        }
    }
    Ok(None)
}

/// The family's relation applied to `args` with the thunks `() => body`,
/// one body per run: the goal, computed as far as the walk has, and not
/// unfolded.
fn refold(cx: &mut Ctx, family: &Family, args: &[Value], bodies: &[Value]) -> Result<Value> {
    let g = cx.g();
    let icits = binder_icits(g.def(family.relation).ty());
    let mut term = Term::Def(family.relation);
    for (i, a) in args.iter().enumerate() {
        let arg = if let Some(run) = family.thunks.iter().position(|&t| t == i) {
            let code = quote_code(cx, &bodies[run])?.shift(&g, 1, 0)?;
            Term::Lam("arg".into(), Icit::Explicit, Rc::new(code))
        } else {
            cx.quote_folded(a)?
        };
        let icit = icits.get(i).copied().unwrap_or(Icit::Explicit);
        term = Term::App(Rc::new(term), Rc::new(arg), icit);
    }
    cx.eval(&term)
}

/// How each binder of a type, as written, is passed.
fn binder_icits(ty: &Term) -> Vec<Icit> {
    let mut out = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(_, icit, _, cod) = t {
        out.push(*icit);
        t = cod.strip_loc();
    }
    out
}

/// Whether the family's relation, unfolded, no longer mentions its thunk or
/// its post: a relation whose body is a constant such as `True`. The walk
/// reads the family, the code and the post back from the goal, so it can't
/// follow one that forgets them.
fn ignores_arguments(cx: &Ctx, family: &Family) -> bool {
    let g = cx.g();
    let Some(body) = g.def(family.relation).body() else {
        return false;
    };
    let params = g.def(family.relation).arity();
    let body = body.peel_lams(params);
    let mentioned = |i: usize| i < params && body.mentions(params - 1 - i);
    let post = family.arity.checked_sub(1);
    !family.thunks.iter().any(|&i| mentioned(i)) && !post.is_some_and(mentioned)
}

/// What a thunk's code is: the thunk applied to `()`.
fn thunk_body(cx: &Ctx, thunk: &Value) -> Result<Value> {
    let g = cx.g();
    let unit = crate::check::builtin_ctor(cx, Builtin::UnitValue)?;
    let body = apply(
        &g,
        thunk.clone(),
        Value::Ctor(unit.0, unit.1, Vec::new().into()),
    )?;
    Ok(force_solved(&g, body)?)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Callee {
    Def(DefId),
    /// A variable in scope, by level.
    Local(usize),
    /// An operation performed directly (`Parse.mark()`), by its constructor
    /// in the ability's operation type: `Call o (y => Done y)` with `o`
    /// that constructor, inside the row's injections.
    Op(DataId, usize),
}

impl Callee {
    /// How a call of this reads in a place: `look`, or the parameter's name.
    fn shown(&self, cx: &Ctx) -> String {
        match self {
            Callee::Def(id) => short_name(&written_name(cx, *id)),
            Callee::Local(level) => cx
                .name_of_level(*level)
                .unwrap_or("a parameter")
                .to_string(),
            Callee::Op(d, c) => short_name(&op_name(cx, *d, *c)),
        }
    }
}

/// Code read back as written: every call as the call, one that steps at
/// once too, so that the walk, reading it again, meets the calls the
/// program makes (`blockLines (Succ m.left) …`, which would read back
/// folded as its unfolding) and their lemmas fit.
fn quote_code(cx: &Ctx, code: &Value) -> Result<Term> {
    Ok(stitchwort_core::value::quote_as_written(
        &cx.g(),
        cx.level(),
        code,
    )?)
}

/// An operation's name as written: its constructor's.
fn op_name(cx: &Ctx, d: DataId, c: usize) -> String {
    cx.g().data(d).ctors()[c].name.to_string()
}

/// The operation `o` performs, inside the row's injections (`L`, `R` of
/// `Effect.Plus`): its constructor.
fn op_ctor(cx: &Ctx, o: &Value) -> Result<Option<(DataId, usize)>> {
    let g = cx.g();
    let plus = g.env.registry().data(Builtin::Plus);
    let mut o = force(&g, o.clone())?;
    loop {
        match o {
            Value::Ctor(d, _, fields) if Some(d) == plus && fields.len() == 1 => {
                o = force(&g, fields[0].clone())?;
            }
            Value::Ctor(d, c, _) => return Ok(Some((d, c))),
            _ => return Ok(None),
        }
    }
}

/// `Call o k`, an operation performed with its rest `k`: the operation and
/// `k`.
fn op_call(cx: &Ctx, body: &Value) -> Result<Option<((DataId, usize), Value, Value)>> {
    let Value::Ctor(d, c, fields) = body else {
        return Ok(None);
    };
    if cx.g().env.registry().ctor(Builtin::Call) != Some((*d, *c)) || fields.len() != 2 {
        return Ok(None);
    }
    Ok(op_ctor(cx, &fields[0])?.map(|op| (op, fields[0].clone(), fields[1].clone())))
}

/// Whether `k` is `y => Done y`, as the elaborator writes the rest of an
/// operation performed on its own.
fn done_rest(cx: &Ctx, k: &Value) -> bool {
    let Value::Lam(_, _, closure) = k else {
        return false;
    };
    let done = cx.g().env.registry().ctor(Builtin::Done);
    matches!(bare(&closure.body), Term::Ctor(d, c, fields)
        if Some((*d, *c)) == done
            && matches!(&fields[..], [f] if matches!(bare(f), Term::Var(0))))
}

/// What a call is of: [`head_of`], or the operation a `Call o (y => Done
/// y)` performs.
fn callee_of(cx: &Ctx, value: &Value) -> Result<Option<Callee>> {
    if let Some(head) = head_of(value) {
        return Ok(Some(head));
    }
    Ok(op_call(cx, value)?.map(|((d, c), _, _)| Callee::Op(d, c)))
}

fn head_of(value: &Value) -> Option<Callee> {
    match value {
        Value::Call(id, ..) | Value::Neutral(Head::Def(id), _) => Some(Callee::Def(*id)),
        Value::Neutral(Head::Var(l, _), _) => Some(Callee::Local(*l)),
        _ => None,
    }
}

fn spine_of(value: &Value) -> Option<&Spine> {
    match value {
        Value::Call(_, spine, _) | Value::Neutral(_, spine) => Some(spine),
        _ => None,
    }
}

fn arg(spine: &Spine, i: usize) -> Option<Value> {
    match spine.get(i)? {
        Elim::App(v, _) => Some(v.clone()),
        _ => None,
    }
}

/// What the code at a point is.
enum Code {
    /// `Effect.bind c k`.
    Bind(Value, Value),
    /// A split the program makes on `scrutinee`, of data `data`, with the
    /// program's names for each constructor's fields.
    Split {
        scrutinee: Value,
        data: DataId,
        names: Vec<Vec<String>>,
        /// The function whose own body is split, if not a lifted `match`.
        through: Option<DefId>,
    },
    /// The program computes on: the same code, a step on.
    Reduced(Value),
    /// `Done x`.
    Value,
    /// A call in tail position.
    Call(Callee, Value),
    Other(&'static str),
}

/// `through`: a function whose own case tree is read where it is called
/// (the goal's function), rather than the call treated as a call.
fn classify(cx: &Ctx, body: &Value, through: Option<DefId>) -> Result<Code> {
    let g = cx.g();
    let reg = g.env.registry();
    let body = force_solved(&g, body.clone())?;
    if let Value::Ctor(d, c, fields) = &body {
        if reg.ctor(Builtin::Done) == Some((*d, *c)) && !fields.is_empty() {
            return Ok(Code::Value);
        }
        // An operation performed directly: a call of it where its rest
        // only returns the reply, else `Effect.bind (Call o (y => Done
        // y)) k`, which `Call o k` computes to.
        if let Some(((od, oc), o, k)) = op_call(cx, &body)? {
            if done_rest(cx, &k) {
                return Ok(Code::Call(Callee::Op(od, oc), body));
            }
            let (done_d, done_c) = reg
                .ctor(Builtin::Done)
                .expect("the prelude declares `Done`");
            let identity = cx.eval(&Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Ctor(done_d, done_c, vec![Rc::new(Term::Var(0))])),
            ))?;
            let performed = Value::Ctor(*d, *c, vec![o, identity].into());
            return Ok(Code::Bind(performed, k));
        }
        return Ok(Code::Other("code the walk doesn't follow"));
    }
    let Some(head) = head_of(&body) else {
        return Ok(Code::Other("code the walk doesn't follow"));
    };
    let spine = spine_of(&body).cloned().unwrap_or_default();
    let Callee::Def(id) = head else {
        return Ok(Code::Call(head, body));
    };
    if reg.def(Builtin::Bind) == Some(id) && spine.len() == 6 {
        let (Some(c), Some(k)) = (arg(&spine, 4), arg(&spine, 5)) else {
            return Ok(Code::Other("a `bind` the walk can't read"));
        };
        return Ok(Code::Bind(c, k));
    }
    for b in [Builtin::BindIn, Builtin::BindD, Builtin::BindDv] {
        if reg.def(b) == Some(id) {
            return Ok(Code::Other("effect-polymorphic code (a bare row `{e}`)"));
        }
    }
    for b in [Builtin::FoldComp, Builtin::FoldCompD, Builtin::Translate] {
        if reg.def(b) == Some(id) {
            return Ok(Code::Other("a `handle` or a `translate`"));
        }
    }
    // An `if` on a proposition: `Decidable.elim d yes no`, whose body
    // splits on `d.holds`, followed as the program's own split.
    if reg.def(Builtin::ElimDec) == Some(id) && spine.len() >= 5 {
        return Ok(Code::Reduced(force_solved(
            &g,
            unfold_once(&g, id, spine)?,
        )?));
    }
    if reg.def(Builtin::IfThenElse) == Some(id) && spine.len() >= 4 {
        // The condition as the code has it, which the split looks for in
        // the goal; forced only to see whether it computes.
        let cond = arg(&spine, 1).expect("an `if` has a condition");
        let bool_data = crate::check::builtin_data(cx, Builtin::Bool)?;
        return Ok(match force(&g, cond.clone())? {
            Value::Ctor(..) => Code::Reduced(unfold_once(&g, id, spine)?),
            _ => Code::Split {
                scrutinee: cond,
                data: bool_data,
                names: vec![Vec::new(), Vec::new()],
                through: None,
            },
        });
    }
    let lifted = cx.e.tables.match_columns.contains_key(&id);
    if lifted || through == Some(id) {
        return Ok(match case_tree(cx, id, &spine)? {
            Some(Tree::Stuck(scrutinee, data, names)) => Code::Split {
                scrutinee,
                data,
                names,
                through: (!lifted).then_some(id),
            },
            Some(Tree::Numbers) => Code::Other("a `match` on numbers"),
            Some(Tree::Leaf) | None => Code::Reduced(unfold_once(&g, id, spine)?),
        });
    }
    Ok(Code::Call(head, body))
}

enum Tree {
    /// The case tree reaches a leaf: the call computes.
    Leaf,
    Stuck(Value, DataId, Vec<Vec<String>>),
    Numbers,
}

/// Where the case tree of lifted `match` `id`, applied to `spine`, is
/// stuck, or that it isn't. None if `id`'s body isn't a case tree.
fn case_tree(cx: &Ctx, id: DefId, spine: &Spine) -> Result<Option<Tree>> {
    let g = cx.g();
    let def = g.def(id);
    let Some(body) = def.body() else {
        return Ok(None);
    };
    let mut env: Vec<Value> = Vec::new();
    for e in spine.iter() {
        match e {
            Elim::App(v, _) => env.push(v.clone()),
            _ => return Ok(None),
        }
    }
    let mut t: &Term = body.strip_loc();
    let mut params = 0;
    while let Term::Lam(_, _, inner) = t {
        t = inner.strip_loc();
        params += 1;
    }
    if params != env.len() {
        return Ok(None);
    }
    loop {
        match t {
            Term::Case(ix, d, branches) => {
                let written = env[env.len() - 1 - ix].clone();
                let value = force(&g, written.clone())?;
                let (c, fields): (usize, Vec<Value>) = match &value {
                    Value::Ctor(d2, c, fields) if d2 == d => (*c, fields.to_vec()),
                    Value::Nat(n) if Some(*d) == g.env.builtins().nat => {
                        if n.as_ref() == &num_bigint::BigUint::from(0u8) {
                            (0, Vec::new())
                        } else {
                            let less: num_bigint::BigUint = n.as_ref() - 1u8;
                            (1, vec![Value::Nat(Rc::new(less))])
                        }
                    }
                    _ => {
                        let names = branches
                            .iter()
                            .map(|b| b.names.iter().map(|n| n.to_string()).collect())
                            .collect();
                        return Ok(Some(Tree::Stuck(written, *d, names)));
                    }
                };
                let Some(next) = &branches[c].body else {
                    return Ok(Some(Tree::Leaf));
                };
                env.extend(fields);
                t = next.strip_loc();
            }
            Term::NumCase(..) => return Ok(Some(Tree::Numbers)),
            _ => return Ok(Some(Tree::Leaf)),
        }
    }
}

/// A new place in `info`'s walk, after the calls taken to reach it.
fn place(cx: &Ctx, info: &NodeInfo, kind: Kind, where_: &str) -> u32 {
    let mut walks = cx.e.session.walks.borrow_mut();
    let id = walks.nodes.len() as u32;
    walks.nodes.push(NodeInfo {
        call: info.call,
        kind,
        place: where_.into(),
        calls_before: info.calls_before.clone(),
        text: None,
        trace: Vec::new(),
        split: 0,
        through: Vec::new(),
        equate: None,
        planned: None,
        cont: match kind {
            Kind::Step(_) => info.cont.clone(),
            Kind::Leaf => None,
        },
        nest: None,
    });
    id
}

fn set_text(cx: &Ctx, node: u32, text: Vec<Piece>) {
    if let Some(n) = cx.e.session.walks.borrow_mut().nodes.get_mut(node as usize) {
        n.text = Some(text);
    }
}

fn note_trace(cx: &Ctx, node: u32, line: Vec<Piece>) {
    cx.e.session.walks.borrow_mut().nodes[node as usize]
        .trace
        .push(line);
}

/// With `STITCHWORT_WALK_TRACE=1`, a line on stderr about what the walk
/// tried at `node` and dropped: an error it recovers from (a direct fit
/// before weakening) is otherwise never seen.
fn debug_trace(cx: &Ctx, node: &NodeInfo, what: &str, expected: &Value, err: &Diagnostic) {
    if std::env::var_os("STITCHWORT_WALK_TRACE").is_none_or(|v| v == "0") {
        return;
    }
    let mut line = format!(
        "walk trace: {}: {what}: {}: {}",
        node.place, err.code, err.message
    );
    for n in &err.notes {
        line.push_str(&format!("\n  note: {n}"));
    }
    line.push_str(&format!("\n  goal: {}", cx.show(expected)));
    eprintln!("{line}");
}

/// `E-WALK` at the walk of `node`, about `what`, with the goal there.
fn stuck(cx: &Ctx, node: &NodeInfo, expected: &Value, what: &str, notes: &[String]) -> Diagnostic {
    let walks = cx.e.session.walks.borrow();
    let at = walks.calls.get(node.call).map_or(cx.span, |c| c.keyword);
    let mut d = Diagnostic::error("E-WALK", format!("the walk stops: {what}"))
        .with_label(at, format!("{}", node.place));
    for n in notes {
        d = d.with_note(n.clone());
    }
    d.with_note(format!("the goal there is {}", cx.show(expected)))
}

fn node_info(cx: &Ctx, node: u32) -> NodeInfo {
    cx.e.session.walks.borrow().nodes[node as usize].clone()
}

/// The walk at `node`: the code of the goal's thunk, `args[family.thunk]`.
fn step(
    cx: &mut Ctx,
    node: u32,
    family: &Family,
    args: Vec<Value>,
    top: bool,
    expected: &Value,
) -> Result<Term> {
    cx.e.session.walks.borrow_mut().nodes[node as usize]
        .trace
        .clear();
    let info = node_info(cx, node);
    let (args, rebuilt) = match info.nest.clone() {
        Some(nest) => {
            let (args, goal) = fix_nested_goal(cx, &info, family, args, &nest, expected)?;
            (args, Some(goal))
        }
        None => (args, None),
    };
    let expected = rebuilt.as_ref().unwrap_or(expected);
    if family.thunks.len() == 2 {
        return two::step(cx, node, &info, family, args, top, expected);
    }
    let mut body = thunk_body(cx, &args[family.thunks[0]])?;
    // The goal's own function is walked through, once: its case tree
    // split on, or its body unfolded.
    let mut through = if top {
        match head_of(&body) {
            Some(Callee::Def(f)) => Some(f),
            _ => None,
        }
    } else {
        info.through.first().copied().flatten()
    };
    let mut steps = 0;
    loop {
        steps += 1;
        if steps > STEP_CAP {
            return Err(stuck(cx, &info, expected, "the code keeps computing", &[]));
        }
        let code = classify(cx, &body, through)?;
        through = None;
        match code {
            Code::Reduced(next) => body = next,
            Code::Bind(c, k) => {
                return bind_step(cx, node, &info, family, vec![c], vec![k], expected);
            }
            Code::Split {
                scrutinee,
                data,
                names,
                through,
            } => {
                // The goal with the code as it now is, folded: the split
                // finds its scrutinee in the thunk, and its branches' goals
                // are the family's relation still.
                let goal = refold(cx, family, &args, std::slice::from_ref(&body))?;
                // Each step from `expected` to `goal` is a definitional
                // unfolding, so they agree; a step that isn't one would
                // otherwise surface as the kernel's internal error.
                if !cx.conv_now(&goal, expected)? {
                    return Err(stuck(
                        cx,
                        &info,
                        expected,
                        "the goal rebuilt for this split isn't the goal the proof has here",
                        &[format!("the rebuilt goal is {}", cx.show(&goal))],
                    ));
                }
                return split(
                    cx,
                    node,
                    &info,
                    family,
                    (scrutinee, data, names, vec![through]),
                    false,
                    &goal,
                );
            }
            Code::Value => return done_step(cx, node, &info, family, expected),
            Code::Call(callee, call) => {
                if let Callee::Def(f) = callee
                    && unfolds(cx, info.call, f)
                    && !has_bracket_lemma(cx, &info, family, std::slice::from_ref(&call))?
                {
                    let g = cx.g();
                    let spine = spine_of(&call).cloned().unwrap_or_default();
                    note_trace(
                        cx,
                        node,
                        vec![Piece::Text(format!(
                            "{}: `{}` unfolded",
                            info.place,
                            written_name(cx, f)
                        ))],
                    );
                    body = force_solved(&g, unfold_once(&g, f, spine)?)?;
                    continue;
                }
                return tail_call(cx, node, &info, family, callee, vec![call], expected);
            }
            Code::Other(what) => {
                let mut notes = Vec::new();
                if ignores_arguments(cx, family) {
                    notes.push(format!(
                        "the family's relation {} ignores its program and its post (its body mentions neither), \
                         so the walk can't read them; state the relation so it uses both",
                        written_name(cx, family.relation)
                    ));
                }
                return Err(stuck(
                    cx,
                    &info,
                    expected,
                    &format!("it doesn't follow {what}"),
                    &notes,
                ));
            }
        }
    }
}

fn unfolds(cx: &Ctx, call: usize, f: DefId) -> bool {
    let name = written_name(cx, f);
    let walks = cx.e.session.walks.borrow();
    walks.calls[call].items.iter().any(|i| match i {
        Item::Unfold(n) => *n == name || name.ends_with(&format!(".{n}")),
        Item::Lemma(_) => false,
    })
}

fn has_bracket_lemma(
    cx: &mut Ctx,
    info: &NodeInfo,
    family: &Family,
    calls: &[Value],
) -> Result<bool> {
    let items = cx.e.session.walks.borrow().calls[info.call].items.clone();
    for item in items {
        if let Item::Lemma(e) = item
            && fit_expr(cx, &e, calls, &[family.relation])?.is_some()
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The chosen lemma applied, at `node`: a leaf for each premise, a value
/// by its name when unification finds a variable, else `_`. A
/// [`Param::Known`] is bound as a local definition named after `node`, so
/// the caller resets `cx` to a mark taken before, once the application is
/// checked.
fn applied(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    chosen: &Chosen,
) -> Result<(Expr, Vec<Piece>)> {
    let span = cx.span;
    let mut e = chosen.expr.clone();
    let mut text = chosen.text.clone();
    let bare = chosen.fit.params.is_empty();
    if !bare {
        text.insert(0, Piece::Text("(".into()));
    }
    for (i, p) in chosen.fit.params.iter().enumerate() {
        match p {
            Param::Premise => {
                let leaf = place(cx, info, Kind::Leaf, &info.place);
                e = app(e, resume(leaf, span));
                text.push(Piece::Text(" (".into()));
                text.push(Piece::Child(leaf));
                text.push(Piece::Text(")".into()));
            }
            Param::Value(name) => match name {
                Some(n) => {
                    e = app(e, var(n.clone(), span));
                    text.push(Piece::Text(format!(" {n}")));
                }
                None => {
                    e = app(e, Expr::Hole(span));
                    text.push(Piece::Text(" _".into()));
                }
            },
            Param::Shown(shown) => {
                e = app(e, Expr::Hole(span));
                text.push(Piece::Text(format!(" ({shown})")));
            }
            Param::Known { term, ty, shown } => {
                let name = format!("%walk{node}.{i}");
                let ty = cx.eval(ty)?;
                cx.bind_local(&name, term.clone(), ty);
                e = app(e, var(name, span));
                text.push(Piece::Text(if !atomic(&[Piece::Text(shown.clone())]) {
                    format!(" ({shown})")
                } else {
                    format!(" {shown}")
                }));
            }
        }
    }
    if !bare {
        text.push(Piece::Text(")".into()));
    }
    Ok((e, text))
}

/// Checks `e`, which the walk wrote at `node`, against `expected`. An error
/// in it that isn't the walk's own is the walk's, at the walk.
fn check_written(
    cx: &mut Ctx,
    info: &NodeInfo,
    e: &Expr,
    expected: &Value,
    what: &str,
) -> Result<Term> {
    match check(cx, e, expected) {
        Ok(t) => Ok(t),
        Err(err) if fatal(&err) || err.code == "E-WALK" => Err(err),
        Err(err) => Err(stuck(
            cx,
            info,
            expected,
            &format!("{what} doesn't check"),
            &[format!("{}: {}", err.code, err.message)],
        )),
    }
}

/// A fresh name for a variable the walk binds, from `base`.
fn fresh(cx: &Ctx, base: &str, taken: &[String]) -> String {
    let free =
        |n: &str| !cx.has_local(n) && cx.lookup(n).is_none() && !taken.iter().any(|t| t == n);
    if free(base) {
        return base.to_string();
    }
    (1..)
        .map(|k| format!("{base}{k}"))
        .find(|n| free(n))
        .expect("some name is free")
}

/// Whether a binder's name was made by the compiler rather than written.
/// The compiler marks its own names with `%` (`pretty::readable`); `_` and
/// the empty name are not names anyone can use. A user's `x`, `_x` or
/// `$x` is written, and counts.
fn generated(name: &str) -> bool {
    name.is_empty() || name == "_" || name.starts_with('%')
}

/// The binders of a `∀` premise of a lemma, as written: names and how many.
fn premise_binders(ty: &Term) -> Vec<String> {
    let mut out = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, _, _, cod) = t {
        out.push(name.to_string());
        t = cod.strip_loc();
    }
    out
}

/// Names for a `∀` premise's binders: `values` gives the value binders
/// (where each is, and its name); the last binder is `<first value>Facts`,
/// and the others take the lemma's own names after the first value.
fn rest_names(cx: &Ctx, binders: &[String], values: &[(usize, String)]) -> Vec<String> {
    let mut taken: Vec<String> = Vec::new();
    let n = binders.len();
    let value = values.first().map_or("value", |(_, v)| v.as_str());
    for (i, b) in binders.iter().enumerate() {
        let base = if let Some((_, v)) = values.iter().find(|(at, _)| *at == i) {
            v.clone()
        } else if i + 1 == n {
            format!("{value}Facts")
        } else if generated(b) {
            format!("{value}Fact{}", i + 1)
        } else {
            let mut cs = b.chars();
            let cap: String = cs
                .next()
                .map(|c| c.to_uppercase().chain(cs).collect())
                .unwrap_or_default();
            format!("{value}{cap}")
        };
        let name = fresh(cx, &base, &taken);
        taken.push(name);
    }
    taken
}

/// Which binders of a then-lemma's last premise are the values, one per
/// run: those its conclusion's continuations are applied to, in order.
fn value_binders(rest: &Term) -> Vec<usize> {
    let mut t = rest.strip_loc();
    let mut k = 0;
    while let Term::Pi(_, _, _, cod) = t {
        t = cod.strip_loc();
        k += 1;
    }
    let (_, args) = t.spine();
    let mut out = Vec::new();
    for a in args {
        let Term::Lam(_, _, body) = a.strip_loc() else {
            continue;
        };
        let (head, args) = body.spine();
        // Under the thunk's own binder.
        if let (Term::Var(_), [only]) = (head.strip_loc(), &args[..])
            && let Term::Var(ix) = only.strip_loc()
            && *ix >= 1
            && ix - 1 < k
        {
            out.push(k - 1 - (ix - 1));
        }
    }
    out
}

/// The names of a bind's values: the program's own for the first run (or
/// one after the call, for a binder the compiler made), and that with
/// `Twin` for the second.
fn value_names(cx: &Ctx, callee: Callee, k: &Value, runs: usize) -> Vec<String> {
    let call_name = match callee {
        Callee::Def(id) => short_name(&written_name(cx, id))
            .rsplit('.')
            .next()
            .unwrap_or("value")
            .to_string(),
        Callee::Local(l) => cx.name_of_level(l).unwrap_or("value").to_string(),
        Callee::Op(d, c) => short_name(&op_name(cx, d, c))
            .rsplit('.')
            .next()
            .unwrap_or("value")
            .to_string(),
    };
    // Not the callee's own name, which a binder would hide.
    let first = match k {
        Value::Lam(name, ..) if !generated(name.as_ref()) => name.to_string(),
        _ => format!("{call_name}Value"),
    };
    let mut out = vec![first.clone()];
    if runs > 1 {
        out.push(format!("{first}Twin"));
    }
    out
}

/// `Effect.bind c k` in each run: the calls' lemma and the family's
/// then-lemma, then the walk goes on in the `k`s.
#[allow(clippy::too_many_arguments)]
fn bind_step(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    cs: Vec<Value>,
    ks: Vec<Value>,
    expected: &Value,
) -> Result<Term> {
    let outer = info;
    let mut cs = (cs.into_iter())
        .map(|c| Ok(force_solved(&cx.g(), c)?))
        .collect::<Result<Vec<_>>>()?;
    // `unfold f` on a call run here: its body, if that is one call too
    // (`full self modes` is `self { … }`), or code [`nested_bind`] takes.
    for run in 0..cs.len() {
        let mut unfolded = 0;
        while let Some(Callee::Def(f)) = head_of(&cs[run])
            && unfolds(cx, info.call, f)
            && !has_bracket_lemma(cx, info, family, &cs)?
            && unfolded < 16
        {
            unfolded += 1;
            let g = cx.g();
            let spine = spine_of(&cs[run]).cloned().unwrap_or_default();
            note_trace(
                cx,
                node,
                vec![Piece::Text(format!(
                    "{}: `{}` unfolded",
                    info.place,
                    written_name(cx, f)
                ))],
            );
            cs[run] = force_solved(&g, unfold_once(&g, f, spine)?)?;
            let code = classify(cx, &cs[run], None)?;
            if nestable(&code) {
                break;
            }
            if !matches!(code, Code::Call(..)) {
                return Err(stuck(
                    cx,
                    info,
                    expected,
                    &format!(
                        "`{}` is unfolded where its value is used, and its body isn't one call",
                        written_name(cx, f)
                    ),
                    &["give a lemma for it instead".into()],
                ));
            }
        }
    }
    let Some(callee) = callee_of(cx, &cs[0])? else {
        return Err(stuck(
            cx,
            info,
            expected,
            "the code runs something that isn't a call",
            &[format!("it is {}", cx.show(&cs[0]))],
        ));
    };
    let mut other = None;
    for c in &cs[1..] {
        if other.is_none() && callee_of(cx, c)?.is_none() {
            other = Some(c);
        }
    }
    if let Some(other) = other {
        return Err(stuck(
            cx,
            info,
            expected,
            "the second run runs something that isn't a call",
            &[format!("it is {}", cx.show(other))],
        ));
    }
    // This call's place, and the calls taken to reach it: the next place
    // after the bind is in the same call's history.
    let here = NodeInfo {
        place: at_call(cx, outer, callee),
        calls_before: Rc::new(
            (outer.calls_before.iter())
                .copied()
                .chain([callee])
                .collect(),
        ),
        ..outer.clone()
    };
    let info = &here;
    // The goal's own family first, then the first premises of its bind
    // lemmas (`Reads0` for `Gives`), then the other families: a lemma in
    // one the family's own is defined by (`ReadsIn … spec` for `Gives`)
    // goes to the family's own bind lemma, and the check sees through the
    // definition.
    let mut ranks = vec![vec![family.relation]];
    let mut seen = vec![family.relation];
    let firsts: Vec<DefId> = (family.then.iter())
        .map(|(_, f, _)| *f)
        .filter(|f| !seen.contains(f))
        .collect();
    seen.extend(&firsts);
    if !firsts.is_empty() {
        ranks.push(firsts);
    }
    let others: Vec<DefId> = (families(cx).into_iter())
        .map(|f| f.relation)
        .filter(|r| !seen.contains(r))
        .collect();
    if !others.is_empty() {
        ranks.push(others);
    }
    // A lemma for what the bind runs as a whole comes first; where there
    // is none and it isn't one call, it is walked.
    let snapshot = Snapshot::take(cx);
    let chosen = match choose(cx, info, callee, &cs, &ranks, expected) {
        Ok(chosen) => chosen,
        Err(e) if fatal(&e) => return Err(e),
        Err(e) => {
            snapshot.restore(cx);
            match nested_bind(cx, node, outer, family, &cs, &ks, expected)? {
                Some(term) => return Ok(term),
                None => return Err(e),
            }
        }
    };
    let then = family
        .then
        .iter()
        .find(|(_, first, _)| *first == chosen.fit.family)
        .or_else(|| {
            family
                .then
                .iter()
                .find(|(_, first, _)| *first == family.relation)
        });
    let Some(&(then, _, _)) = then else {
        return Err(stuck(
            cx,
            info,
            expected,
            "no then-lemma takes a lemma of that family",
            &[],
        ));
    };
    let values = value_names(cx, callee, &ks[0], cs.len());
    let shown: Vec<String> = cs.iter().map(|c| format!("`{}`", cx.show(c))).collect();
    note_trace(
        cx,
        node,
        [
            vec![Piece::Text(format!(
                "{}: {}: ",
                info.place,
                shown.join(" and ")
            ))],
            chosen.text.clone(),
            vec![Piece::Text(format!(
                " ({}), then `{}`",
                chosen.how,
                short_name(&written_name(cx, then))
            ))],
        ]
        .concat(),
    );
    let g = cx.g();
    let then_shape = statement(g.def(then).ty()).expect("a then-lemma is a relation");
    let explicit = then_shape.explicit();
    let span = cx.span;
    let mark = cx.mark();
    let (lemma, lemma_text) = applied(cx, node, info, &chosen)?;
    let then_name = written_name(cx, then);
    let mut e = var(then_name.clone(), span);
    let mut text = vec![Piece::Text(short_name(&then_name)), Piece::Text(" ".into())];
    text.extend(lemma_text);
    e = app(e, lemma);
    for _ in 2..explicit.len() {
        let leaf = place(cx, info, Kind::Leaf, &info.place);
        e = app(e, resume(leaf, span));
        text.extend([
            Piece::Text(" (".into()),
            Piece::Child(leaf),
            Piece::Text(")".into()),
        ]);
    }
    let rest = &then_shape.binders[explicit[explicit.len() - 1]].1;
    let binders = premise_binders(rest);
    let mut at = value_binders(rest);
    if at.len() != values.len() {
        at = (0..values.len()).collect();
    }
    let named: Vec<(usize, String)> = at.into_iter().zip(values).collect();
    let names = rest_names(cx, &binders, &named);
    let next = place(cx, info, Kind::Step(family.relation), &outer.place);
    if let [(first, _), (second, _)] = &named[..]
        && binders.len() > 2
    {
        cx.e.session.walks.borrow_mut().nodes[next as usize].equate = Some(Rc::new(Equate {
            value: names[*first].clone(),
            twin: names[*second].clone(),
            fact: names[names.len() - 1].clone(),
        }));
    }
    let lambda = lambda(&names, resume(next, span), span);
    e = app(e, lambda);
    text.extend([
        Piece::Text(format!(" ({}\n", binding(&names))),
        Piece::Child(next),
        Piece::Text(")".into()),
    ]);
    set_text(cx, node, text);
    let result = check_written(cx, info, &e, expected, "the step");
    cx.reset(mark);
    result
}

/// Whether code a bind runs is walked as a computation of its own
/// ([`nested_bind`]) rather than given a lemma as a call.
fn nestable(code: &Code) -> bool {
    matches!(code, Code::Bind(..) | Code::Split { .. } | Code::Reduced(_))
}

/// A bind whose bound computation isn't one call: `let y := f (g ()); k y`
/// is `Effect.bind (Effect.bind (g ()) f) k`, and the walk reads it as
/// `let x := g (); let y := f x; k y`. The family's own then-lemma takes
/// the bound computation, walked, as its first premise, with the post the
/// rest of the code needs (`y => R … (() => k y) post`), so its last
/// premise is the identity: `then (walk of f (g ())) (y yFacts => yFacts)`.
/// Where the bound computation ends, in a value or a call, the walk goes on
/// in `k` ([`Cont`]). A bound computation that splits is walked the same
/// way. Taken only where no lemma fits the bound computation as a whole
/// (`givesHandlerNameAt` for `handlerName modes what (modes.at
/// Underscore)`). None where the code is a call, or the then-lemma's last premise
/// isn't `∀ vs => first vs → …` with `first` its first premise's post
/// (`Parse.readsAtThen`'s has a fact about the mark too).
#[allow(clippy::too_many_arguments)]
fn nested_bind(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    cs: &[Value],
    ks: &[Value],
    expected: &Value,
) -> Result<Option<Term>> {
    for c in cs {
        if !nestable(&classify(cx, c, None)?) {
            return Ok(None);
        }
    }
    let Some(&(then, _, _)) = (family.then.iter()).find(|(_, first, _)| *first == family.relation)
    else {
        return Ok(None);
    };
    let g = cx.g();
    let Some(shape) = statement(g.def(then).ty()) else {
        return Ok(None);
    };
    let explicit = shape.explicit();
    let [first_at, rest_at] = explicit[..] else {
        return Ok(None);
    };
    if statement(&shape.binders[first_at].1).is_none_or(|s| s.head != family.relation) {
        return Ok(None);
    }
    // The last premise: `∀ v… => first v… → R …`, `first` an implicit of
    // the lemma's applied to the values in order.
    let rest = &shape.binders[rest_at].1;
    let binders = premise_binders(rest);
    let Some(values_count) = binders.len().checked_sub(1) else {
        return Ok(None);
    };
    let mut t = rest.strip_loc();
    for _ in 0..values_count {
        let Term::Pi(_, _, _, cod) = t else {
            return Ok(None);
        };
        t = cod.strip_loc();
    }
    let Term::Pi(_, _, hypothesis, _) = t else {
        return Ok(None);
    };
    let (head, hyp_args) = hypothesis.spine();
    let post_binder = match head.strip_loc() {
        Term::Var(ix) if *ix >= values_count => rest_at.checked_sub(1 + ix - values_count),
        _ => None,
    };
    let Some(post_binder) = post_binder.filter(|&b| shape.binders[b].0 != Icit::Explicit) else {
        return Ok(None);
    };
    if hyp_args.len() != values_count
        || !(hyp_args.iter().enumerate())
            .all(|(i, a)| matches!(a.strip_loc(), Term::Var(ix) if *ix == values_count - 1 - i))
    {
        return Ok(None);
    }
    let first_name = match ks.first() {
        Some(Value::Lam(name, ..)) if !generated(name.as_ref()) => name.to_string(),
        _ => "value".to_string(),
    };
    let mut values: Vec<(usize, String)> = vec![(0, first_name.clone())];
    let mut at = value_binders(rest);
    if family.thunks.len() > 1 {
        values.push((1, format!("{first_name}Twin")));
    }
    if at.len() != values.len() {
        at = (0..values.len()).collect();
    }
    let named: Vec<(usize, String)> = at
        .into_iter()
        .zip(values.into_iter().map(|(_, n)| n))
        .collect();
    let names = rest_names(cx, &binders, &named);
    let span = cx.span;
    let identity = lambda(
        &names,
        var(names.last().cloned().unwrap_or_default(), span),
        span,
    );
    let Some((post_at, post)) = nested_post(
        cx,
        then,
        &shape,
        (first_at, rest_at, post_binder),
        family,
        cs,
        &identity,
        expected,
    )?
    else {
        return Ok(None);
    };
    let inner = place(cx, info, Kind::Step(family.relation), &info.place);
    {
        let mut walks = cx.e.session.walks.borrow_mut();
        let n = &mut walks.nodes[inner as usize];
        n.nest = Some(Rc::new(Nest {
            codes: cs.to_vec(),
            post_at,
            post,
        }));
        n.cont = Some(Rc::new(Cont {
            ks: ks.to_vec(),
            parent: info.cont.clone(),
        }));
    }
    let then_name = written_name(cx, then);
    let facts = names.last().cloned().unwrap_or_default();
    let e = app(
        app(var(then_name.clone(), span), resume(inner, span)),
        identity,
    );
    note_trace(
        cx,
        node,
        vec![Piece::Text(format!(
            "{}: `{}` walked as the code it runs, then `{}`",
            info.place,
            cx.show(&cs[0]),
            short_name(&then_name)
        ))],
    );
    set_text(
        cx,
        node,
        vec![
            Piece::Text(format!("{}\n{MORE}(", short_name(&then_name))),
            Piece::Child(inner),
            Piece::Text(format!(")\n{MORE}({} {facts})", binding(&names))),
        ],
    );
    check_written(cx, info, &e, expected, "the step").map(Some)
}

/// The post the first premise of a [`nested_bind`] has, and which of the
/// relation's arguments it is: the then-lemma instantiated at `expected`,
/// its thunks the bound computations, and its last premise checked as the
/// identity, which fixes the post. Found aside, with everything it solved
/// undone; None if it doesn't check.
#[allow(clippy::too_many_arguments)]
fn nested_post(
    cx: &mut Ctx,
    then: DefId,
    shape: &Shape,
    (first_at, rest_at, post_binder): (usize, usize, usize),
    family: &Family,
    codes: &[Value],
    identity: &Expr,
    expected: &Value,
) -> Result<Option<(usize, Term)>> {
    let Some(first) = statement(&shape.binders[first_at].1) else {
        return Ok(None);
    };
    // The lemma's binder each of the first premise's arguments is, if it
    // is one.
    let binder_of = |arg: &Term| match arg.strip_loc() {
        Term::Var(ix) => first_at.checked_sub(1 + ix),
        _ => None,
    };
    let Some(post_at) = (0..first.args.len())
        .find(|&i| !family.thunks.contains(&i) && binder_of(&first.args[i]) == Some(post_binder))
    else {
        return Ok(None);
    };
    let snapshot = Snapshot::take(cx);
    let found = (|| -> Result<Option<Term>> {
        let g = cx.g();
        let mut ty = force(&g, g.def(then).ty_value().clone())?;
        let mut metas = Vec::new();
        let mut doms = Vec::new();
        // As many binders as the lemma has as written: forced further, its
        // conclusion would unfold into the relation's own `∀`s.
        for _ in 0..shape.binders.len() {
            let Value::Pi(_, _, dom, cod) = &ty else {
                return Ok(None);
            };
            let m = cx.fresh_meta();
            let v = cx.eval(&m)?;
            doms.push((**dom).clone());
            metas.push(v.clone());
            ty = cod.apply(&g, v)?;
            if metas.len() < shape.binders.len() {
                ty = force(&g, ty)?;
            }
        }
        for (run, &at) in family.thunks.iter().enumerate() {
            let Some(b) = binder_of(&first.args[at]) else {
                return Ok(None);
            };
            let code = quote_code(cx, &codes[run])?.shift(&g, 1, 0)?;
            let thunk = cx.eval(&Term::Lam("arg".into(), Icit::Explicit, Rc::new(code)))?;
            if !crate::undo::unify(cx, &metas[b], &thunk)? {
                return Ok(None);
            }
        }
        // By the arguments, as [`read_goal`] compares: the goal's code
        // against the lemma's `() => j (p())`, not their relation's
        // unfoldings.
        if !crate::undo::unify_solving_arguments(cx, &ty, expected)? {
            return Ok(None);
        }
        if check(cx, identity, &doms[rest_at]).is_err() {
            return Ok(None);
        }
        let post = force_solved(&g, metas[post_binder].clone())?;
        let term = quote_code(cx, &post)?;
        let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
        Ok(Some(term))
    })();
    snapshot.restore(cx);
    Ok(found?.map(|term| (post_at, term)))
}

/// At the first premise of a [`nested_bind`]: the goal's thunks are the
/// bound computations, `() => c`, and its post the one [`nested_post`]
/// found.
fn fix_nested_goal(
    cx: &mut Ctx,
    info: &NodeInfo,
    family: &Family,
    mut args: Vec<Value>,
    nest: &Nest,
    expected: &Value,
) -> Result<(Vec<Value>, Value)> {
    let g = cx.g();
    let mut thunks = Vec::new();
    for (run, &at) in family.thunks.iter().enumerate() {
        let code = quote_code(cx, &nest.codes[run])?.shift(&g, 1, 0)?;
        let thunk = cx.eval(&Term::Lam("arg".into(), Icit::Explicit, Rc::new(code)))?;
        thunks.push((at, thunk.clone()));
        if !crate::undo::unify(cx, &args[at], &thunk)? {
            return Err(stuck(
                cx,
                info,
                expected,
                "the goal for the code a bind runs isn't about that code",
                &[format!("the code is {}", cx.show(&nest.codes[run]))],
            ));
        }
    }
    let post = cx.eval(&nest.post)?;
    if !crate::undo::unify(cx, &args[nest.post_at], &post)? {
        return Err(stuck(
            cx,
            info,
            expected,
            "the goal for the code a bind runs doesn't ask what the code after it needs",
            &[format!("what it needs is {}", cx.show(&post))],
        ));
    }
    // The goal again with the code as the bind runs it, its calls as the
    // calls: the goal the elaborator has may read the code back folded,
    // where a call that steps at once (`blockLines (Succ m.left) …`) is
    // written as its unfolding, and no lemma about the call fits that.
    let goal = refold(cx, family, &args, &nest.codes)?;
    if !cx.conv_now(&goal, expected)? {
        return Err(stuck(
            cx,
            info,
            expected,
            "the goal rebuilt for the code a bind runs isn't the goal the proof has here",
            &[format!("the rebuilt goal is {}", cx.show(&goal))],
        ));
    }
    for (at, thunk) in thunks {
        args[at] = thunk;
    }
    Ok((args, goal))
}

/// The place for a premise of a value's or a call's lemma about its
/// value: a leaf, or, where the code ends a bound computation
/// ([`nested_bind`]), the walk of the code after it.
fn premise_place(cx: &Ctx, info: &NodeInfo, family: &Family) -> u32 {
    let Some(cont) = &info.cont else {
        return place(cx, info, Kind::Leaf, &info.place);
    };
    let next = place(cx, info, Kind::Step(family.relation), &info.place);
    cx.e.session.walks.borrow_mut().nodes[next as usize].cont = cont.parent.clone();
    next
}

/// The family's done-lemma at a value, its premise a leaf.
fn done_step(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    expected: &Value,
) -> Result<Term> {
    let Some(done) = family.done else {
        return Err(stuck(
            cx,
            info,
            expected,
            "the family has no `@[walk.done]` lemma",
            &[],
        ));
    };
    let span = cx.span;
    let name = written_name(cx, done);
    let shape = statement(cx.g().def(done).ty()).expect("a done-lemma is a relation");
    let mut e = var(name.clone(), span);
    let mut text = vec![Piece::Text(short_name(&name))];
    for i in shape.explicit() {
        let dom = &shape.binders[i].1;
        // A premise is a proposition about the value; the others (the
        // value itself, a mark) unification finds.
        if is_premise_term(dom) {
            let leaf = premise_place(cx, info, family);
            e = app(e, resume(leaf, span));
            text.extend([
                Piece::Text(" (".into()),
                Piece::Child(leaf),
                Piece::Text(")".into()),
            ]);
        } else {
            e = app(e, Expr::Hole(span));
            text.push(Piece::Text(" _".into()));
        }
    }
    set_text(cx, node, text);
    check_written(cx, info, &e, expected, "the value's step")
}

/// Whether a lemma's parameter type, as written, is a premise: an
/// application of one of its own parameters (`holds x`, `spec [] x`).
fn is_premise_term(dom: &Term) -> bool {
    matches!(dom.spine().0.strip_loc(), Term::Var(_)) && !dom.spine().1.is_empty()
}

/// A call in tail position: its lemma, weakened if its post differs.
fn tail_call(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    callee: Callee,
    calls: Vec<Value>,
    expected: &Value,
) -> Result<Term> {
    let outer = info;
    let here = NodeInfo {
        place: at_call(cx, outer, callee),
        calls_before: Rc::new(
            (outer.calls_before.iter())
                .copied()
                .chain([callee])
                .collect(),
        ),
        ..outer.clone()
    };
    let info = &here;
    let chosen = choose(cx, info, callee, &calls, &[vec![family.relation]], expected)?;
    let mark = cx.mark();
    let (lemma, lemma_text) = applied(cx, node, info, &chosen)?;
    let shown: Vec<String> = calls.iter().map(|c| format!("`{}`", cx.show(c))).collect();
    note_trace(
        cx,
        node,
        [
            vec![Piece::Text(format!(
                "{}: {}: ",
                info.place,
                shown.join(" and ")
            ))],
            chosen.text.clone(),
            vec![Piece::Text(format!(" ({})", chosen.how))],
        ]
        .concat(),
    );
    // As it is, if its post is the goal's; never where the code after it
    // is still to be walked, which the weakening's implication goes on in.
    if info.cont.is_none() {
        let snapshot = Snapshot::take(cx);
        match check(cx, &lemma, expected) {
            Ok(term) => {
                cx.reset(mark);
                let mut text = lemma_text.clone();
                if matches!(text.first(), Some(Piece::Text(t)) if t == "(") {
                    text.remove(0);
                    text.pop();
                }
                set_text(cx, node, text);
                return Ok(term);
            }
            Err(e) if fatal(&e) => {
                cx.reset(mark);
                return Err(e);
            }
            Err(e) => {
                debug_trace(cx, info, "direct fit failed", expected, &e);
                snapshot.restore(cx);
            }
        }
    }
    let Some(weaken) = family.weaken else {
        return Err(stuck(
            cx,
            info,
            expected,
            "the call's lemma says something else, and the family has no `@[walk.weaken]` lemma",
            &[],
        ));
    };
    let span = cx.span;
    let name = written_name(cx, weaken);
    let shape = statement(cx.g().def(weaken).ty()).expect("a weaken-lemma is a relation");
    let explicit = shape.explicit();
    // The premise in the family's relation takes the call's lemma; the
    // other is the implication, in whichever order the lemma has them
    // (`Parse.givesWeaken gives implies`, `Parse.followsWeaken implies
    // follows`).
    let lemma_first = statement(&shape.binders[explicit[0]].1)
        .is_some_and(|s| s.head == family.relation)
        || explicit.len() < 2;
    let implies_at = if lemma_first {
        explicit[explicit.len() - 1]
    } else {
        explicit[0]
    };
    let implies = &shape.binders[implies_at].1;
    let binders = premise_binders(implies);
    let runs = family.thunks.len();
    let bases = match &info.cont {
        Some(cont) => value_names(cx, callee, &cont.ks[0], runs),
        None => vec!["value".to_string(), "valueTwin".to_string()],
    };
    let values: Vec<(usize, String)> = (0..runs)
        .map(|run| {
            let at = (binders.len() + run).saturating_sub(runs + 1);
            (at, fresh(cx, &bases[run], &[]))
        })
        .collect();
    let names = rest_names(cx, &binders, &values);
    let leaf = premise_place(cx, info, family);
    let lambda = lambda(&names, resume(leaf, span), span);
    let mut text = vec![Piece::Text(format!("{}\n{MORE}", short_name(&name)))];
    let implication = [
        Piece::Text(format!(
            "({}",
            binding(&names) + if names.is_empty() { "" } else { " " }
        )),
        Piece::Child(leaf),
        Piece::Text(")".into()),
    ];
    let e = if lemma_first {
        text.extend(lemma_text);
        text.push(Piece::Text(format!("\n{MORE}")));
        text.extend(implication);
        app(app(var(name.clone(), span), lemma), lambda)
    } else {
        text.extend(implication);
        text.push(Piece::Text(format!("\n{MORE}")));
        text.extend(lemma_text);
        app(app(var(name.clone(), span), lambda), lemma)
    };
    set_text(cx, node, text);
    let result = check_written(cx, info, &e, expected, "the weakened call");
    cx.reset(mark);
    result
}

/// A split where the program's case tree is stuck: a proof `match` on the
/// same scrutinee, the program's names for the fields, and an equation
/// named `branchN`. `twin` is set for a split in the
/// second run alone, whose field names take `Twin`.
fn split(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    (scrutinee, data, names, through): (Value, DataId, Vec<Vec<String>>, Vec<Option<DefId>>),
    twin: bool,
    expected: &Value,
) -> Result<Term> {
    let g = cx.g();
    let ctors = g.data(data).ctors().len();
    {
        let mut walks = cx.e.session.walks.borrow_mut();
        walks.nodes[node as usize].split = ctors.saturating_sub(1);
        // Counted over the chain as it now stands: a place checked again
        // (the elaborator retrying an application) replaces its own text,
        // so what it split before isn't counted twice.
        let root = walks.calls[info.call].root;
        let paths = 1 + walks.splits(root, node);
        if paths > PATH_CAP {
            drop(walks);
            return Err(stuck(
                cx,
                info,
                expected,
                &format!("it would follow more than {PATH_CAP} paths"),
                &["make the split a function with a lemma of its own, and use that lemma".into()],
            ));
        }
    }
    let span = cx.span;
    let term = cx.quote_folded(&scrutinee)?;
    let ty = crate::cases::atom_type(cx, &term, data)?;
    let shown = condition_text(&cx.show(&scrutinee));
    let depth = (0..cx.level())
        .filter(|&l| cx.name_of_level(l).is_some_and(|n| n.starts_with("branch")))
        .count();
    let equation = fresh(cx, &format!("branch{}", depth + 1), &[]);
    let planned = Rc::new(Planned {
        goal: cx.quote_folded(expected)?,
        needle: term.clone(),
        base: cx.level(),
        with: Replacement::Equation(equation.clone()),
    });
    let mut alts = Vec::new();
    let mut text = vec![Piece::Text(format!("(match {equation}: {shown} with"))];
    for c in 0..ctors {
        let ctor = &g.data(data).ctors()[c];
        let explicit: Vec<usize> = (0..ctor.fields.len())
            .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
            .collect();
        let mut taken = Vec::new();
        let mut fields = Vec::new();
        for (k, &i) in explicit.iter().enumerate() {
            let base = names
                .get(c)
                .and_then(|n| n.get(i))
                .filter(|n| !generated(n))
                .cloned()
                .unwrap_or_else(|| format!("field{}", k + 1));
            // The second run's names are told from the first's, which are in scope.
            let base = if twin { format!("{base}Twin") } else { base };
            let n = fresh(cx, &base, &taken);
            taken.push(n.clone());
            fields.push(Pattern::Var(ast::Name { text: n, span }));
        }
        let ctor_name = ctor.name.to_string();
        let ctor_short = ctor_name
            .rsplit('.')
            .next()
            .unwrap_or(&ctor_name)
            .to_string();
        let arm = if taken.is_empty() {
            ctor_short.clone()
        } else {
            format!("{ctor_short} {}", taken.join(" "))
        };
        let where_ = format!("{}, `{arm}`", info.place);
        let next = place(cx, info, Kind::Step(family.relation), &where_);
        {
            let mut walks = cx.e.session.walks.borrow_mut();
            walks.nodes[next as usize].through = through.clone();
            walks.nodes[next as usize].planned = Some(planned.clone());
        }
        alts.push(Alt {
            guard: None,
            patterns: vec![crate::internal_ctor_pattern(data, c, fields, span)],
            body: Some(resume(next, span)),
            span,
        });
        text.extend([Piece::Text(format!("\n| {arm} => ")), Piece::Child(next)]);
    }
    text.push(Piece::Text(")".into()));
    set_text(cx, node, text);
    let name = Some(ast::Name {
        text: equation,
        span,
    });
    crate::matching::generalised_named(cx, term, ty, span, name, None, &alts, &[], span, expected)
}

/// A condition as source: `a == b` is shown as the derived instance's
/// `(T.%decide a b).holds`, which can't be written.
fn condition_text(shown: &str) -> String {
    if let Some(inner) = shown
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(").holds"))
        && let Some((_, args)) = inner.split_once(".%decide ")
        && let [a, b] = args.split(' ').collect::<Vec<_>>()[..]
    {
        return format!("{a} == {b}");
    }
    shown.to_string()
}

/// How a lambda over `names` reads in a step's text: `a b =>`, or
/// nothing when there are no names.
fn binding(names: &[String]) -> String {
    if names.is_empty() {
        String::new()
    } else {
        format!("{} =>", names.join(" "))
    }
}
