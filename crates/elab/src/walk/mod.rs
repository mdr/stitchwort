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
//!   binder (or `<function>Value`, for a binder the compiler made);
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
/// (`number`) is no lambda written by mistake (`W-LAMBDA-SHADOW`).
fn lambda(names: &[String], body: Expr, span: Span) -> Expr {
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
        walks.calls.push(CallInfo {
            keyword: walk.keyword,
            span: walk.span,
            items,
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
            text: None,
            trace: Vec::new(),
            split: 0,
            through: Vec::new(),
            equate: None,
            planned: None,
        });
        root
    };
    step(cx, root, &family, args, true, expected)
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
            let code = cx.quote_folded(&bodies[run])?.shift(&g, 1, 0)?;
            Term::Lam("arg".into(), Icit::Explicit, Rc::new(code))
        } else {
            cx.quote_folded(a)?
        };
        let icit = icits.get(i).copied().unwrap_or(Icit::Explicit);
        term = Term::App(Rc::new(term), Rc::new(arg), icit);
    }
    cx.eval(&term)
}

/// The goal with its arguments other than the thunks eta-contracted, if
/// that changes any (`x y => WordsAlike x y` to `WordsAlike`), and the
/// arguments: the same goal by conversion. A then-lemma's post comes out
/// eta-expanded where unification solved it from the unfolded relation
/// (`?alike x y` against `WordsAlike x y`), and a lemma that leaves a run
/// open (`second`) then fails to fit, since the unifier settles an unknown
/// function facing a lambda only when a data unknown faces a known argument
/// too (`unify_by_unknown_arguments`); the contracted post is a known
/// argument, as the statement wrote it.
fn eta_contracted(
    cx: &mut Ctx,
    family: &Family,
    args: &[Value],
    expected: &Value,
) -> Result<Option<(Vec<Value>, Value)>> {
    let g = cx.g();
    let mut contracted = Vec::with_capacity(args.len());
    for (i, a) in args.iter().enumerate() {
        let lambda = matches!(force_solved(&g, a.clone())?, Value::Lam(..));
        contracted.push(if lambda && !family.thunks.contains(&i) {
            eta_contract(&g, &cx.quote_folded(a)?)?
        } else {
            None
        });
    }
    if contracted.iter().all(Option::is_none) {
        return Ok(None);
    }
    let terms = (args.iter().zip(contracted))
        .map(|(a, c)| c.map_or_else(|| cx.quote_folded(a), Ok))
        .collect::<Result<Vec<_>>>()?;
    let icits = binder_icits(g.def(family.relation).ty());
    let mut goal = Term::Def(family.relation);
    for (i, t) in terms.iter().enumerate() {
        let icit = icits.get(i).copied().unwrap_or(Icit::Explicit);
        goal = Term::App(Rc::new(goal), Rc::new(t.clone()), icit);
    }
    let goal = cx.eval(&goal)?;
    if !cx.conv_now(&goal, expected)? {
        return Ok(None);
    }
    let args = (terms.iter())
        .map(|t| cx.eval(t))
        .collect::<Result<Vec<_>>>()?;
    Ok(Some((args, goal)))
}

/// `t` eta-contracted, if it is a lambda that only applies a function to
/// its variables (`x y => f x y` is `f`), where `f` mentions none of them.
fn eta_contract(g: &stitchwort_core::Ev, t: &Term) -> Result<Option<Term>> {
    let Term::Lam(_, icit, body) = t.strip_loc() else {
        return Ok(None);
    };
    let inner = eta_contract(g, body)?;
    let body = inner.as_ref().unwrap_or(body);
    if let Term::App(f, a, applied) = body.strip_loc()
        && applied == icit
        && matches!(a.strip_loc(), Term::Var(0))
        && !f.mentions(0)
    {
        return Ok(Some(f.instantiate_var(g, 0)?));
    }
    Ok(None)
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
        return Ok(Code::Other("an operation called directly"));
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

/// A new place in call `call`'s walk.
fn place(cx: &Ctx, call: usize, kind: Kind, where_: &str) -> u32 {
    let mut walks = cx.e.session.walks.borrow_mut();
    let id = walks.nodes.len() as u32;
    walks.nodes.push(NodeInfo {
        call,
        kind,
        place: where_.into(),
        text: None,
        trace: Vec::new(),
        split: 0,
        through: Vec::new(),
        equate: None,
        planned: None,
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
    let contracted = eta_contracted(cx, family, &args, expected)?;
    let (args, expected) = match &contracted {
        Some((args, goal)) => (args.clone(), goal),
        None => (args, expected),
    };
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
        if steps > 1000 {
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
                return Err(stuck(
                    cx,
                    &info,
                    expected,
                    &format!("it doesn't follow {what}"),
                    &[],
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
                let leaf = place(cx, info.call, Kind::Leaf, &info.place);
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
fn generated(name: &str) -> bool {
    name.is_empty() || name == "x" || name == "_" || name.starts_with(['_', '$', '%'])
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
    let mut cs = (cs.into_iter())
        .map(|c| Ok(force_solved(&cx.g(), c)?))
        .collect::<Result<Vec<_>>>()?;
    // `unfold f` on a call run here: its body, if that is one call too
    // (`full self modes` is `self { … }`). A body that binds would need
    // the binds reassociated, which the walk doesn't do.
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
            if !matches!(classify(cx, &cs[run], None)?, Code::Call(..)) {
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
    let Some(callee) = head_of(&cs[0]) else {
        return Err(stuck(
            cx,
            info,
            expected,
            "the code runs something that isn't a call",
            &[format!("it is {}", cx.show(&cs[0]))],
        ));
    };
    if let Some(other) = cs[1..].iter().find(|c| head_of(c).is_none()) {
        return Err(stuck(
            cx,
            info,
            expected,
            "the second run runs something that isn't a call",
            &[format!("it is {}", cx.show(other))],
        ));
    }
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
    let chosen = choose(cx, info, callee, &cs, &ranks, expected)?;
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
        let leaf = place(cx, info.call, Kind::Leaf, &info.place);
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
    let next = place(cx, info.call, Kind::Step(family.relation), &info.place);
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
        Piece::Text(format!(" ({} =>\n", names.join(" "))),
        Piece::Child(next),
        Piece::Text(")".into()),
    ]);
    set_text(cx, node, text);
    let result = check_written(cx, info, &e, expected, "the step");
    cx.reset(mark);
    result
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
            let leaf = place(cx, info.call, Kind::Leaf, &info.place);
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
    // As it is, if its post is the goal's.
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
    let values: Vec<(usize, String)> = (0..runs)
        .map(|run| {
            let at = (binders.len() + run).saturating_sub(runs + 1);
            let base = if run == 0 { "value" } else { "valueTwin" };
            (at, fresh(cx, base, &[]))
        })
        .collect();
    let names = rest_names(cx, &binders, &values);
    let leaf = place(cx, info.call, Kind::Leaf, &info.place);
    let lambda = lambda(&names, resume(leaf, span), span);
    let mut text = vec![Piece::Text(format!("{}\n{MORE}", short_name(&name)))];
    let implication = [
        Piece::Text(format!("({} => ", names.join(" "))),
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
/// named `branchN`.
fn split(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    (scrutinee, data, names, through): (Value, DataId, Vec<Vec<String>>, Vec<Option<DefId>>),
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
        let next = place(cx, info.call, Kind::Step(family.relation), &where_);
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
