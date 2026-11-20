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

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, Spine, apply, force, force_solved, unfold_once};
use stitchwort_core::{DataId, DefId, Icit, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Expr, Pattern, Walk};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, Result, check, infer};
use crate::undo::{Snapshot, fatal};

/// The most paths one walk follows: each split adds its alternatives
/// less one. Past this the walk stops (SW-4238 §3.5); a split whose arms
/// share a long tail is better made a function with its own lemma.
pub(crate) const PATH_CAP: usize = 64;

/// The attributes, as written after `@[`.
pub(crate) const WALK: &str = "walk";
pub(crate) const WALK_BIND: &str = "walk.bind";
pub(crate) const WALK_DONE: &str = "walk.done";
pub(crate) const WALK_WEAKEN: &str = "walk.weaken";

/// What the walks checked so far have recorded: one [`CallInfo`] per check
/// of a written walk, and the places it went on from.
#[derive(Default)]
pub(crate) struct Walks {
    calls: Vec<CallInfo>,
    nodes: Vec<NodeInfo>,
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
    /// The function whose own case tree a split here was made in: the
    /// goal's code is still a call of it, walked through once more.
    through: Option<DefId>,
    /// A split's branch: the goal before the split, which the branch's
    /// goal is with the split's equation's right side for its scrutinee.
    planned: Option<Rc<Planned>>,
}

/// The goal a split's branch has, read back folded: the generalised goal a
/// `match` gives its arms is unfolded (the scrutinee is found in the
/// relation's unfolding), where the walk reads its thunk.
struct Planned {
    /// The goal before the split, folded, in `base` variables.
    goal: Term,
    /// The scrutinee, in `base` variables.
    needle: Term,
    base: usize,
    /// The equation the branch is checked with: `needle = pattern`.
    equation: String,
}

#[derive(Clone, Copy)]
enum Kind {
    /// The rest of a body, in the family whose relation is this.
    Step(DefId),
    /// A goal the closers close.
    Leaf,
}

/// A piece of a walk's expansion.
#[derive(Clone, Debug)]
pub enum Piece {
    Text(String),
    /// The user's own text, as written there.
    Source(Span),
    /// What a place the walk went on from wrote.
    Child(u32),
}

/// One check of a written walk, for `check --expand-walk`: where it is, the
/// chain it stands for and the lemma used at each call.
#[derive(Clone, Debug)]
pub struct WalkExpansion {
    pub span: Span,
    pub pieces: Vec<Piece>,
    pub trace: Vec<Vec<Piece>>,
}

impl Walks {
    /// The paths the splits reached from `node`'s text add, and `extra`'s.
    fn splits(&self, node: u32, extra: u32) -> usize {
        let mut seen = vec![node];
        let mut todo = vec![node];
        let mut total = 0;
        while let Some(n) = todo.pop() {
            let Some(info) = self.nodes.get(n as usize) else {
                continue;
            };
            total += info.split;
            for piece in info.text.iter().flatten() {
                if let Piece::Child(k) = piece
                    && !seen.contains(k)
                {
                    seen.push(*k);
                    todo.push(*k);
                }
            }
        }
        if !seen.contains(&extra) {
            total += self.nodes[extra as usize].split;
        }
        total
    }

    /// The expansion of call `c`, with its children's pieces in place.
    fn expansion(&self, c: usize) -> Option<WalkExpansion> {
        let call = &self.calls[c];
        let mut out = Vec::new();
        let mut trace = Vec::new();
        self.flatten(call.root, &mut out, &mut trace)?;
        Some(WalkExpansion {
            span: call.span,
            pieces: out,
            trace,
        })
    }

    /// The pieces and trace of the places the final chain goes through:
    /// a place tried and given up (a call first tried unweakened) isn't
    /// reached from the root's text.
    fn flatten(&self, node: u32, out: &mut Vec<Piece>, trace: &mut Vec<Vec<Piece>>) -> Option<()> {
        let info = self.nodes.get(node as usize)?;
        trace.extend(info.trace.iter().cloned());
        let Some(text) = info.text.as_ref() else {
            // Where the walk stopped: left open.
            out.push(Piece::Text("?".into()));
            return Some(());
        };
        let mut skip_close = false;
        for (i, piece) in text.iter().enumerate() {
            match piece {
                Piece::Child(k) => {
                    let mut child = Vec::new();
                    self.flatten(*k, &mut child, trace)?;
                    // `f (x)` is written `f x`.
                    let opened = matches!(out.last(), Some(Piece::Text(t)) if t.ends_with('('));
                    let closed =
                        matches!(text.get(i + 1), Some(Piece::Text(t)) if t.starts_with(')'));
                    if opened && closed && atomic(&child) {
                        if let Some(Piece::Text(t)) = out.last_mut() {
                            t.pop();
                        }
                        skip_close = true;
                    }
                    out.extend(child);
                }
                Piece::Text(t) if skip_close => {
                    skip_close = false;
                    out.push(Piece::Text(t[1..].to_string()));
                }
                other => out.push(other.clone()),
            }
        }
        Some(())
    }
}

/// Whether written pieces are one word, or one bracketed whole, needing no
/// brackets as an argument.
fn atomic(pieces: &[Piece]) -> bool {
    let mut text = String::new();
    for p in pieces {
        match p {
            Piece::Text(t) => text.push_str(t),
            _ => return false,
        }
    }
    if text.is_empty() {
        return false;
    }
    if !text.contains([' ', '\n']) {
        return true;
    }
    let (Some(open), Some(close)) = (text.chars().next(), text.chars().last()) else {
        return false;
    };
    if !matches!((open, close), ('(', ')') | ('[', ']')) {
        return false;
    }
    // The first bracket closes at the end, not before.
    let mut depth = 0usize;
    for (i, c) in text.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => {
                depth -= 1;
                if depth == 0 {
                    return i + c.len_utf8() == text.len();
                }
            }
            _ => {}
        }
    }
    false
}

impl Elaborator {
    /// What each walk checked so far wrote: for a walk checked more than
    /// once, the last (`check --expand-walk`).
    pub fn take_walk_expansions(&self) -> Vec<WalkExpansion> {
        let walks = self.session.walks.borrow();
        let mut out: Vec<WalkExpansion> = Vec::new();
        for c in 0..walks.calls.len() {
            if let Some(e) = walks.expansion(c) {
                match out.iter_mut().find(|o| o.span == e.span) {
                    Some(o) => *o = e,
                    None => out.push(e),
                }
            }
        }
        out
    }

    /// Files theorem `id` under the walk attribute `tag`, written at `at`,
    /// after checking its statement has the shape the attribute needs
    /// (`E-ATTRIBUTE`), and, for `@[walk]`, that no other lemma is filed
    /// for its function and family (`E-WALK-LEMMA`).
    pub(crate) fn register_walk(&mut self, id: DefId, tag: &str, at: Span) -> Result<()> {
        let g = &self.ev();
        let name = g.def(id).name().to_string();
        let Some(shape) = statement(g.def(id).ty()) else {
            return Err(Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{name}` can't be `@[{tag}]`: its statement isn't a relation"),
            )
            .with_label(at, "here"));
        };
        let wrong = |what: &str| {
            Diagnostic::error(
                "E-ATTRIBUTE",
                format!("`{name}` can't be `@[{tag}]`: {what}"),
            )
            .with_label(at, "here")
            .with_note(
                "a family is a relation `R … (() => code) post`, with `@[walk.bind]` on its \
                 lemma for `() => j (p())`, `@[walk.done]` on its lemma for `() => x` and \
                 `@[walk.weaken]` on its lemma for another post; `@[walk]` files a lemma about one \
                 function's calls, `R … (() => f x…) post` (docs/syntax.md, \"byWalking\")",
            )
        };
        let thunk = shape
            .args
            .iter()
            .position(|a| matches!(a.strip_loc(), Term::Lam(..)));
        match tag {
            WALK_BIND => {
                let explicit = shape.explicit();
                if thunk.is_none() || explicit.len() < 2 {
                    return Err(wrong(
                        "a then-lemma's statement is about a thunk `() => j (p())`, with a first \
                         premise about `p` and a last one about `j` of each value",
                    ));
                }
                let first = &shape.binders[explicit[0]].1;
                if statement(first).is_none() {
                    return Err(wrong("its first premise isn't a relation"));
                }
            }
            WALK_DONE | WALK_WEAKEN => {
                if thunk.is_none() && tag == WALK_DONE {
                    return Err(wrong("a done-lemma's statement is about a thunk `() => x`"));
                }
            }
            _ => {
                let Some(t) = thunk else {
                    return Err(wrong("its statement isn't about a thunk `() => f x…`"));
                };
                let Some(head) = thunk_head(&shape.args[t]) else {
                    return Err(wrong(
                        "its thunk isn't a call of a function, `() => f x…` (a lemma about `k (p())` \
                         is a then-lemma)",
                    ));
                };
                for (&other, (other_tag, other_at)) in self.tables.walk_tags.iter() {
                    if other_tag != WALK || other == id {
                        continue;
                    }
                    let Some(s) = statement(g.def(other).ty()) else {
                        continue;
                    };
                    let t2 = s
                        .args
                        .iter()
                        .position(|a| matches!(a.strip_loc(), Term::Lam(..)));
                    if s.head == shape.head && t2.and_then(|t| thunk_head(&s.args[t])) == Some(head)
                    {
                        return Err(Diagnostic::error(
                            "E-WALK-LEMMA",
                            format!(
                                "`{}` already has a walk lemma in this family: `{}`",
                                g.def(head).name(),
                                g.def(other).name()
                            ),
                        )
                        .with_label(at, "a second one")
                        .with_label(*other_at, "the first")
                        .with_note(
                            "a call uses its function's one registered lemma, never a choice \
                             between two; name the other where it is wanted, in a walk's \
                             brackets",
                        ));
                    }
                }
            }
        }
        self.tables
            .walk_tags
            .insert(&self.session.owners, id, (tag.to_string(), at));
        Ok(())
    }
}

/// A statement read off its type as written: the binders, then the
/// relation's head and arguments.
struct Shape {
    binders: Vec<(Icit, Term, String)>,
    head: DefId,
    args: Vec<Term>,
}

impl Shape {
    fn explicit(&self) -> Vec<usize> {
        (0..self.binders.len())
            .filter(|&i| self.binders[i].0 == Icit::Explicit)
            .collect()
    }
}

/// `ty`, a type as written, as a [`Shape`], if its conclusion is a
/// definition applied to arguments.
fn statement(ty: &Term) -> Option<Shape> {
    let mut binders = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, icit, dom, cod) = t {
        binders.push((*icit, (**dom).clone(), name.to_string()));
        t = cod.strip_loc();
    }
    let (head, args) = t.spine();
    let Term::Def(head) = head.strip_loc() else {
        return None;
    };
    Some(Shape {
        binders,
        head: *head,
        args: args.into_iter().cloned().collect(),
    })
}

/// The function a thunk `() => f x…` calls.
fn thunk_head(thunk: &Term) -> Option<DefId> {
    let Term::Lam(_, _, body) = thunk.strip_loc() else {
        return None;
    };
    match body.spine().0.strip_loc() {
        Term::Def(f) => Some(*f),
        _ => None,
    }
}

/// Which argument of relation `rel` is the thunk: a family's, or the
/// first premise's of a then-lemma.
fn thunk_index(cx: &Ctx, rel: DefId) -> Option<usize> {
    let all = families(cx);
    all.iter()
        .find(|f| f.relation == rel)
        .map(|f| f.thunk)
        .or_else(|| {
            all.iter()
                .flat_map(|f| f.then.iter())
                .find(|(_, first, _)| *first == rel)
                .map(|(_, _, i)| *i)
        })
}

/// A family: its relation and its lemmas.
#[derive(Clone)]
struct Family {
    relation: DefId,
    /// Which of the relation's arguments is the thunk.
    thunk: usize,
    arity: usize,
    /// The then-lemmas, each with the relation of its first premise and
    /// which of that relation's arguments is the thunk.
    then: Vec<(DefId, DefId, usize)>,
    done: Option<DefId>,
    weaken: Option<DefId>,
}

/// The families the `@[walk.bind]`, `@[walk.done]` and `@[walk.weaken]`
/// lemmas loaded so far declare.
fn families(cx: &Ctx) -> Vec<Family> {
    let g = cx.g();
    let mut out: Vec<Family> = Vec::new();
    let mut tags: Vec<(DefId, String)> = (cx.e.tables.walk_tags.iter())
        .map(|(id, (tag, _))| (*id, tag.clone()))
        .collect();
    tags.sort_by_key(|(id, _)| id.0);
    for (id, tag) in tags {
        if tag == WALK {
            continue;
        }
        let Some(shape) = statement(g.def(id).ty()) else {
            continue;
        };
        let family = match out.iter_mut().position(|f| f.relation == shape.head) {
            Some(i) => &mut out[i],
            None => {
                let Some(thunk) = shape
                    .args
                    .iter()
                    .position(|a| matches!(a.strip_loc(), Term::Lam(..)))
                else {
                    continue;
                };
                out.push(Family {
                    relation: shape.head,
                    thunk,
                    arity: shape.args.len(),
                    then: Vec::new(),
                    done: None,
                    weaken: None,
                });
                out.last_mut().expect("just pushed")
            }
        };
        match tag.as_str() {
            WALK_BIND => {
                let explicit = shape.explicit();
                if let Some(&at) = explicit.first()
                    && let Some(first) = statement(&shape.binders[at].1)
                {
                    // The thunk `p` is the argument whose binder is a
                    // function.
                    let thunk = first.args.iter().position(|a| {
                        matches!(a.strip_loc(), Term::Var(ix) if *ix < at
                            && matches!(shape.binders[at - 1 - ix].1.strip_loc(), Term::Pi(..)))
                    });
                    if let Some(thunk) = thunk {
                        family.then.push((id, first.head, thunk));
                    }
                }
            }
            WALK_DONE => family.done = family.done.or(Some(id)),
            _ => family.weaken = family.weaken.or(Some(id)),
        }
    }
    out
}

/// The name a definition is written by in the walk's terms and expansion.
fn written_name(cx: &Ctx, id: DefId) -> String {
    cx.g().def(id).name().to_string()
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
        .collect();
    let body = thunk_body(cx, &args[family.thunk])?;
    let own = match head_of(&body) {
        Some(Callee::Def(f)) => own_theorem(cx).map(|t| (t, f)),
        _ => None,
    };
    let (call, root) = {
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
        let place = match head_of(&body) {
            Some(Callee::Def(f)) => format!("in `{}`", written_name(cx, f)),
            _ => "in the goal's code".to_string(),
        };
        walks.nodes.push(NodeInfo {
            call,
            kind: Kind::Step(family.relation),
            place: place.into(),
            text: None,
            trace: Vec::new(),
            split: 0,
            through: None,
            planned: None,
        });
        (call, root)
    };
    let _ = call;
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
    let Some(level) = cx.lookup(&planned.equation) else {
        return Ok(None);
    };
    let g = cx.g();
    let Value::Eq(_, _, pattern) = force(&g, cx.types[level].clone())? else {
        return Ok(None);
    };
    let with = cx.quote_folded(&pattern)?;
    let depth = cx.level();
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

/// The family's relation applied to `args` with the thunk `() => body`:
/// the goal, computed as far as the walk has, and not unfolded.
fn refold(cx: &mut Ctx, family: &Family, args: &[Value], body: &Value) -> Result<Value> {
    let g = cx.g();
    let icits = binder_icits(g.def(family.relation).ty());
    let mut term = Term::Def(family.relation);
    for (i, a) in args.iter().enumerate() {
        let arg = if i == family.thunk {
            let code = cx.quote_folded(body)?.shift(&g, 1, 0)?;
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
        through: None,
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
    let mut body = thunk_body(cx, &args[family.thunk])?;
    // The goal's own function is walked through, once: its case tree
    // split on, or its body unfolded.
    let mut through = if top {
        match head_of(&body) {
            Some(Callee::Def(f)) => Some(f),
            _ => None,
        }
    } else {
        info.through
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
            Code::Bind(c, k) => return bind_step(cx, node, &info, family, c, k, expected),
            Code::Split {
                scrutinee,
                data,
                names,
                through,
            } => {
                // The goal with the code as it now is, folded: the split
                // finds its scrutinee in the thunk, and its branches' goals
                // are the family's relation still.
                let goal = refold(cx, family, &args, &body)?;
                return split(
                    cx,
                    node,
                    &info,
                    family,
                    (scrutinee, data, names, through),
                    &goal,
                );
            }
            Code::Value => return done_step(cx, node, &info, family, expected),
            Code::Call(callee, call) => {
                if let Callee::Def(f) = callee
                    && unfolds(cx, info.call, f)
                    && !has_bracket_lemma(cx, &info, family, &call)?
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
                return tail_call(cx, node, &info, family, callee, call, expected);
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

fn has_bracket_lemma(cx: &mut Ctx, info: &NodeInfo, family: &Family, call: &Value) -> Result<bool> {
    let items = cx.e.session.walks.borrow().calls[info.call].items.clone();
    for item in items {
        if let Item::Lemma(e) = item
            && fit_expr(cx, &e, call, &[family.relation])?.is_some()
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// How a lemma fits a call: its family, and for each of its explicit
/// parameters left, whether it is a premise (a leaf) or a value
/// unification finds (named, if it is a variable in scope).
struct Fit {
    family: DefId,
    params: Vec<Param>,
}

enum Param {
    Premise,
    /// A variable in scope, by name; `None` if it is left to unification.
    Value(Option<String>),
    /// A value the call fixes that isn't a variable (`count + 1`): passed
    /// as a local definition, so the premises after it are checked with
    /// it known, and written as the value.
    Known {
        term: Term,
        ty: Term,
        shown: String,
    },
}

/// Whether a lemma of type `ty` fits `call` in one of `families`.
fn fit_type(cx: &mut Ctx, ty: &Value, call: &Value, families: &[DefId]) -> Result<Option<Fit>> {
    let mut found = None;
    crate::undo::transaction(cx, |cx| {
        let g = cx.g();
        let mut ty = ty.clone();
        let mut params = Vec::new();
        let mut metas = Vec::new();
        // Down the lemma's `∀`s to a family's relation, which is not
        // unfolded further.
        let mut unfolds = 0;
        let shown = loop {
            let shown = force_solved(&g, ty)?;
            if let Value::Call(rel, ..) | Value::Neutral(Head::Def(rel), _) = &shown
                && families.contains(rel)
            {
                break shown;
            }
            // A name for a family's statement (`Reads0 p` for
            // `Parse.Reads0 GoodItems p`), unfolded to it.
            if let Value::Call(f, spine, _) = &shown
                && unfolds < 4
            {
                unfolds += 1;
                ty = unfold_once(&g, *f, spine.clone())?;
                continue;
            }
            let Value::Pi(_, icit, dom, cod) = force(&g, shown)? else {
                return Ok(None::<()>);
            };
            let m = cx.fresh_meta_of(&dom);
            let v = cx.eval(&m)?;
            if icit == Icit::Explicit {
                // Whether it is a premise is asked once the call has fixed
                // the lemma's unknowns: a type with one may be any sort.
                params.push(Value::clone(&dom));
                metas.push(m);
            }
            ty = cod.apply(&g, v)?;
        };
        let (Value::Call(rel, spine, _) | Value::Neutral(Head::Def(rel), spine)) = &shown else {
            return Ok(None);
        };
        if !families.contains(rel) {
            return Ok(None);
        }
        let index = thunk_index(cx, *rel);
        let Some(thunk) = index.and_then(|i| arg(spine, i)) else {
            return Ok(None);
        };
        let body = thunk_body(cx, &thunk)?;
        if !cx.unify(&body, call)? {
            return Ok(None);
        }
        // What the call leaves open (a predicate only its premises
        // mention), from the hypotheses: a premise one of them is.
        for dom in &params {
            if !crate::cases::is_proposition(cx, dom)? {
                continue;
            }
            for level in (0..cx.level()).rev() {
                let ty = cx.types[level].clone();
                if crate::undo::unify(cx, &ty, dom)? {
                    break;
                }
            }
        }
        let params = params
            .into_iter()
            .zip(&metas)
            .map(|(dom, m)| {
                if crate::cases::is_proposition(cx, &dom)? {
                    return Ok(Param::Premise);
                }
                let mut v = force(&cx.g(), cx.eval(m)?)?;
                // Still unknown: the one hypothesis of its type
                // (`outside: OutsideAtoms self`).
                if matches!(v, Value::Neutral(Head::Meta(_), _)) {
                    let mut found = Vec::new();
                    for level in (0..cx.level()).rev() {
                        let Some(name) = cx.name_of_level(level) else {
                            continue;
                        };
                        if generated(name) || cx.lookup(name) != Some(level) {
                            continue;
                        }
                        let ty = cx.types[level].clone();
                        let snapshot = Snapshot::take(cx);
                        let fits = cx.unify(&ty, &dom)?;
                        snapshot.restore(cx);
                        if fits {
                            found.push(level);
                        }
                    }
                    if let [level] = found[..] {
                        let var = Value::var(level);
                        if crate::undo::unify(cx, &v, &var)? {
                            v = var;
                        }
                    }
                }
                if let Some(name) = variable_name(cx, &v)? {
                    return Ok(Param::Value(Some(name)));
                }
                let term = cx.quote_folded(&v)?;
                let ty = cx.quote_folded(&dom)?;
                let open = |t: &Term| t.subterms().any(|(t, _)| matches!(t, Term::Meta(_)));
                if open(&term) || open(&ty) {
                    return Ok(Param::Value(None));
                }
                Ok(Param::Known {
                    shown: cx.show_term(&term),
                    term,
                    ty,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        found = Some(Fit {
            family: *rel,
            params,
        });
        // Undone either way: the lemma is applied for real later.
        Ok(None)
    })?;
    Ok(found)
}

/// The name of the variable `v` is, also eta-expanded (`x => holds x`).
fn variable_name(cx: &Ctx, v: &Value) -> Result<Option<String>> {
    let term = cx.quote_folded(v)?;
    let mut t = term.strip_loc();
    let mut under = 0;
    while let Term::Lam(_, _, body) = t {
        t = body.strip_loc();
        under += 1;
    }
    let (head, args) = t.spine();
    if args.len() != under {
        return Ok(None);
    }
    for (i, a) in args.iter().enumerate() {
        if !matches!(a.strip_loc(), Term::Var(ix) if *ix == under - 1 - i) {
            return Ok(None);
        }
    }
    let Term::Var(ix) = head.strip_loc() else {
        return Ok(None);
    };
    let Some(ix) = ix.checked_sub(under) else {
        return Ok(None);
    };
    let level = cx.level() - 1 - ix;
    Ok(cx
        .name_of_level(level)
        .filter(|n| cx.lookup(n) == Some(level))
        .map(str::to_string))
}

fn fit_expr(cx: &mut Ctx, e: &Expr, call: &Value, families: &[DefId]) -> Result<Option<Fit>> {
    let snapshot = Snapshot::take(cx);
    let inferred = infer(cx, e);
    let ty = match inferred {
        Ok((_, ty)) => ty,
        Err(err) if fatal(&err) => return Err(err),
        Err(_) => {
            snapshot.restore(cx);
            return Ok(None);
        }
    };
    let fit = fit_type(cx, &ty, call, families);
    snapshot.restore(cx);
    fit
}

/// A lemma chosen for a call: its term as written, with what goes on it.
struct Chosen {
    expr: Expr,
    text: Vec<Piece>,
    fit: Fit,
    how: String,
}

/// The lemma for `call` (whose head is `callee`), in one of `families`,
/// by the four tiers.
fn choose(
    cx: &mut Ctx,
    info: &NodeInfo,
    callee: Callee,
    call: &Value,
    families: &[DefId],
    expected: &Value,
) -> Result<Chosen> {
    let (items, own) = {
        let walks = cx.e.session.walks.borrow();
        let c = &walks.calls[info.call];
        (c.items.clone(), c.own.clone())
    };
    let span = cx.span;
    // 1. The brackets.
    let mut fits = Vec::new();
    for item in &items {
        if let Item::Lemma(e) = item
            && let Some(fit) = fit_expr(cx, e, call, families)?
        {
            fits.push((e.clone(), fit));
        }
    }
    if fits.len() > 1 {
        return Err(two_fit(cx, info, expected, call, "in the brackets"));
    }
    if let Some((e, fit)) = fits.pop() {
        // As written, bracketed unless it is a name.
        let text = match &e {
            Expr::Var(_) => vec![Piece::Source(e.span())],
            _ => vec![
                Piece::Text("(".into()),
                Piece::Source(e.span()),
                Piece::Text(")".into()),
            ],
        };
        return Ok(Chosen {
            text,
            expr: e,
            fit,
            how: "named in the brackets".into(),
        });
    }
    // 2. The theorem being proved, at a call of its own function.
    if let (Some((name, f)), Callee::Def(id)) = (&own, callee)
        && *f == id
    {
        let e = var(name.clone(), span);
        if let Some(fit) = fit_expr(cx, &e, call, families)? {
            let short = name.rsplit('.').next().unwrap_or(name).to_string();
            return Ok(Chosen {
                expr: var(short.clone(), span),
                text: vec![Piece::Text(short)],
                fit,
                how: "the theorem itself".into(),
            });
        }
    }
    // 3. A hypothesis in scope.
    let mut fits = Vec::new();
    for level in (0..cx.level()).rev() {
        let Some(name) = cx.name_of_level(level).map(str::to_string) else {
            continue;
        };
        if cx.lookup(&name) != Some(level) {
            continue;
        }
        let ty = cx.types[level].clone();
        if let Some(fit) = fit_type(cx, &ty, call, families)? {
            fits.push((name, fit));
        }
    }
    if fits.len() > 1 {
        let names: Vec<String> = fits.iter().map(|(n, _)| format!("`{n}`")).collect();
        return Err(two_fit(
            cx,
            info,
            expected,
            call,
            &format!("among the hypotheses ({})", names.join(", ")),
        ));
    }
    if let Some((name, fit)) = fits.pop() {
        return Ok(Chosen {
            expr: var(name.clone(), span),
            text: vec![Piece::Text(name)],
            fit,
            how: "a hypothesis".into(),
        });
    }
    // 4. The registered lemma.
    if let Callee::Def(id) = callee {
        let g = cx.g();
        let registered: Vec<DefId> = (cx.e.tables.walk_tags.iter())
            .filter(|(_, (tag, _))| tag == WALK)
            .map(|(lemma, _)| *lemma)
            .filter(|lemma| {
                statement(g.def(*lemma).ty()).is_some_and(|s| {
                    families.contains(&s.head) && s.args.iter().any(|a| thunk_head(a) == Some(id))
                })
            })
            .collect();
        let mut fits = Vec::new();
        for lemma in registered {
            let ty = cx.eval(g.def(lemma).ty())?;
            if let Some(fit) = fit_type(cx, &ty, call, families)? {
                fits.push((lemma, fit));
            }
        }
        if fits.len() > 1 {
            return Err(two_fit(
                cx,
                info,
                expected,
                call,
                "among the registered lemmas",
            ));
        }
        if let Some((lemma, fit)) = fits.pop() {
            let name = written_name(cx, lemma);
            return Ok(Chosen {
                expr: var(name.clone(), span),
                text: vec![Piece::Text(short_name(&name))],
                fit,
                how: "registered `@[walk]`".into(),
            });
        }
    }
    let what = match callee {
        Callee::Def(id) => format!("`{}`", written_name(cx, id)),
        Callee::Local(l) => format!("`{}`", cx.name_of_level(l).unwrap_or("a parameter")),
    };
    let mut notes = vec![format!("the call is {}", cx.show(call))];
    match callee {
        Callee::Local(_) => notes.push(format!(
            "{what} is a parameter: give its lemma in the brackets, or as a hypothesis"
        )),
        Callee::Def(_) => notes.push(format!(
            "give a lemma for it in the brackets, register one with `@[walk]`, or write \
             `unfold {}` in the brackets to walk its body",
            what.trim_matches('`')
        )),
    }
    Err(stuck(
        cx,
        info,
        expected,
        &format!("it has no lemma for this call of {what}"),
        &notes,
    ))
}

/// A name as an expansion writes it: without `Std.`.
fn short_name(name: &str) -> String {
    name.strip_prefix("Std.").unwrap_or(name).to_string()
}

fn two_fit(cx: &Ctx, info: &NodeInfo, expected: &Value, call: &Value, tier: &str) -> Diagnostic {
    stuck(
        cx,
        info,
        expected,
        &format!("two lemmas fit this call {tier}"),
        &[
            format!("the call is {}", cx.show(call)),
            "name the one wanted in the brackets: a walk never chooses between two".into(),
        ],
    )
}

/// `chosen` applied to its parameters left: a premise is a leaf, a value
/// is its name when unification finds a variable, else `_`.
/// The chosen lemma applied: a leaf for each premise. A [`Param::Known`]
/// is bound as a local definition, so the caller resets `cx` to a mark
/// taken before, once the application is checked.
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
    let _ = node;
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

/// Names for a `∀` premise's binders: `value` for its value binder (the
/// one its continuation is applied to, else the first), `valueFacts` for the
/// last, and the lemma's own names after `value` for the others.
fn rest_names(cx: &Ctx, binders: &[String], value: &str, value_at: usize) -> Vec<String> {
    let mut taken: Vec<String> = Vec::new();
    let n = binders.len();
    for (i, b) in binders.iter().enumerate() {
        let base = if i == value_at {
            value.to_string()
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

/// Which binder of a then-lemma's last premise is the value: the one its
/// conclusion's continuation is applied to.
fn value_binder(rest: &Term) -> usize {
    let mut t = rest.strip_loc();
    let mut k = 0;
    while let Term::Pi(_, _, _, cod) = t {
        t = cod.strip_loc();
        k += 1;
    }
    let (_, args) = t.spine();
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
            return k - 1 - (ix - 1);
        }
    }
    0
}

/// `Effect.bind c k`: the call's lemma and the family's then-lemma, then
/// the walk goes on in `k`.
#[allow(clippy::too_many_arguments)]
fn bind_step(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    c: Value,
    k: Value,
    expected: &Value,
) -> Result<Term> {
    let mut c = force_solved(&cx.g(), c)?;
    // `unfold f` on a call run here: its body, if that is one call too
    // (`full self modes` is `self { … }`). A body that binds would need
    // the binds reassociated, which the walk doesn't do.
    let mut unfolded = 0;
    while let Some(Callee::Def(f)) = head_of(&c)
        && unfolds(cx, info.call, f)
        && !has_bracket_lemma(cx, info, family, &c)?
        && unfolded < 16
    {
        unfolded += 1;
        let g = cx.g();
        let spine = spine_of(&c).cloned().unwrap_or_default();
        note_trace(
            cx,
            node,
            vec![Piece::Text(format!(
                "{}: `{}` unfolded",
                info.place,
                written_name(cx, f)
            ))],
        );
        c = force_solved(&g, unfold_once(&g, f, spine)?)?;
        if !matches!(classify(cx, &c, None)?, Code::Call(..)) {
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
    let Some(callee) = head_of(&c) else {
        return Err(stuck(
            cx,
            info,
            expected,
            "the code runs something that isn't a call",
            &[format!("it is {}", cx.show(&c))],
        ));
    };
    let firsts: Vec<DefId> = family.then.iter().map(|(_, f, _)| *f).collect();
    let mut ordered = vec![family.relation];
    ordered.extend(firsts.iter().copied().filter(|f| *f != family.relation));
    // Then the other families: a lemma in one the family's own is defined
    // by (`ReadsIn … spec` for `Gives`) goes to the family's own then-lemma,
    // and the check sees through the definition.
    for other in families(cx) {
        if !ordered.contains(&other.relation) {
            ordered.push(other.relation);
        }
    }
    let chosen = choose(cx, info, callee, &c, &ordered, expected)?;
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
    let call_name = match callee {
        Callee::Def(id) => short_name(&written_name(cx, id))
            .rsplit('.')
            .next()
            .unwrap_or("value")
            .to_string(),
        Callee::Local(l) => cx.name_of_level(l).unwrap_or("value").to_string(),
    };
    // The program's own name for the value, else one after the call (not
    // the callee's own name, which a binder would hide).
    let binder = match &k {
        Value::Lam(name, ..) if !generated(name.as_ref()) => name.to_string(),
        _ => format!("{call_name}Value"),
    };
    note_trace(
        cx,
        node,
        [
            vec![Piece::Text(format!("{}: `{}`: ", info.place, cx.show(&c)))],
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
    for &i in &explicit[1..explicit.len() - 1] {
        let leaf = place(cx, info.call, Kind::Leaf, &info.place);
        e = app(e, resume(leaf, span));
        text.extend([
            Piece::Text(" (".into()),
            Piece::Child(leaf),
            Piece::Text(")".into()),
        ]);
        let _ = i;
    }
    let rest = &then_shape.binders[explicit[explicit.len() - 1]].1;
    let binders = premise_binders(rest);
    let names = rest_names(cx, &binders, &binder, value_binder(rest));
    let next = place(cx, info.call, Kind::Step(family.relation), &info.place);
    let lambda = Expr::Lam(
        names
            .iter()
            .map(|n| ast::Name {
                text: n.clone(),
                span,
            })
            .collect(),
        Box::new(resume(next, span)),
        span,
    );
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
    call: Value,
    expected: &Value,
) -> Result<Term> {
    let chosen = choose(cx, info, callee, &call, &[family.relation], expected)?;
    let mark = cx.mark();
    let (lemma, lemma_text) = applied(cx, node, info, &chosen)?;
    note_trace(
        cx,
        node,
        [
            vec![Piece::Text(format!(
                "{}: `{}`: ",
                info.place,
                cx.show(&call)
            ))],
            chosen.text.clone(),
            vec![Piece::Text(format!(" ({})", chosen.how))],
        ]
        .concat(),
    );
    // As it is, if its post is the goal's.
    let snapshot = Snapshot::take(cx);
    let walks_before = cx.e.session.walks.borrow().nodes.len();
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
        Err(_) => snapshot.restore(cx),
    }
    let _ = walks_before;
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
    let implies = &shape.binders[explicit[explicit.len() - 1]].1;
    let binders = premise_binders(implies);
    let value = fresh(cx, "value", &[]);
    let at = binders.len().saturating_sub(2);
    let names = rest_names(cx, &binders, &value, at);
    let leaf = place(cx, info.call, Kind::Leaf, &info.place);
    let e = app(
        app(var(name.clone(), span), lemma),
        Expr::Lam(
            names
                .iter()
                .map(|n| ast::Name {
                    text: n.clone(),
                    span,
                })
                .collect(),
            Box::new(resume(leaf, span)),
            span,
        ),
    );
    let mut text = vec![Piece::Text(format!("{}\n{MORE}", short_name(&name)))];
    text.extend(lemma_text);
    text.extend([
        Piece::Text(format!("\n{MORE}({} => ", names.join(" "))),
        Piece::Child(leaf),
        Piece::Text(")".into()),
    ]);
    set_text(cx, node, text);
    let result = check_written(cx, info, &e, expected, "the weakened call");
    cx.reset(mark);
    result
}

/// A split where the program's case tree is stuck: a proof `match` on the
/// same scrutinee, the program's names for the fields, an equation named
/// `branchN` when the scrutinee isn't a variable.
fn split(
    cx: &mut Ctx,
    node: u32,
    info: &NodeInfo,
    family: &Family,
    (scrutinee, data, names, through): (Value, DataId, Vec<Vec<String>>, Option<DefId>),
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
    let is_var = matches!(&scrutinee, Value::Neutral(Head::Var(..), s) if s.is_empty());
    let term = cx.quote_folded(&scrutinee)?;
    let ty = crate::cases::atom_type(cx, &term, data)?;
    let shown = condition_text(&cx.show(&scrutinee));
    let _ = is_var;
    let depth = (0..cx.level())
        .filter(|&l| cx.name_of_level(l).is_some_and(|n| n.starts_with("branch")))
        .count();
    let equation = fresh(cx, &format!("branch{}", depth + 1), &[]);
    let planned = Rc::new(Planned {
        goal: cx.quote_folded(expected)?,
        needle: term.clone(),
        base: cx.level(),
        equation: equation.clone(),
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
            walks.nodes[next as usize].through = through;
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

/// A leaf: closed by a hypothesis, computation, a conjunction of closed
/// parts, `arithmetic`, or the walk's `then t`.
fn leaf(cx: &mut Ctx, id: u32, info: &NodeInfo, expected: &Value) -> Result<Term> {
    // A goal with an unknown the rest of the chain fixes (a value the
    // lemma's conclusion gives) waits for it: closed now, a hypothesis
    // could fix it wrongly. Failing here queues the leaf
    // ([`crate::queue::tactic_or_wait`]).
    if crate::queue::search_pending_in(cx, expected)?.is_some() {
        return Err(stuck(
            cx,
            info,
            expected,
            "a goal is left with an unknown in it",
            &[],
        ));
    }
    let g = cx.g();
    let reg = g.env.registry();
    if let Value::Data(d, _) = force(&g, expected.clone())?
        && reg.data(Builtin::Unit) == Some(d)
    {
        let (d, c) = crate::check::builtin_ctor(cx, Builtin::Trivial)?;
        set_text(cx, id, vec![Piece::Text("()".into())]);
        return Ok(Term::Ctor(d, c, Vec::new()));
    }
    // A hypothesis that is the goal, fixing what the goal leaves open
    // (a predicate only a premise mentions).
    for level in (0..cx.level()).rev() {
        let Some(name) = cx.name_of_level(level).map(str::to_string) else {
            continue;
        };
        if generated(&name) || cx.lookup(&name) != Some(level) {
            continue;
        }
        let ty = cx.types[level].clone();
        if crate::undo::unify(cx, &ty, expected)? {
            set_text(cx, id, vec![Piece::Text(name)]);
            return Ok(Term::Var(cx.level() - 1 - level));
        }
    }
    if let Some(term) = crate::cases::close_by_hypotheses(cx, expected)? {
        let shown = match term.strip_loc() {
            Term::Var(_) | Term::Proj(..) => cx.show_term(&term),
            _ => "cases".to_string(),
        };
        set_text(cx, id, vec![Piece::Text(shown)]);
        return Ok(term);
    }
    let goal = force(&g, expected.clone())?;
    if let Value::Eq(_, l, r) = &goal
        && cx.conv_now(l, r)?
    {
        set_text(cx, id, vec![Piece::Text("byComputing".into())]);
        return Ok(Term::Refl);
    }
    let reg = g.env.registry();
    if let Value::Data(d, _) = &goal {
        if reg.data(Builtin::Unit) == Some(*d) {
            let (d, c) = crate::check::builtin_ctor(cx, Builtin::Trivial)?;
            set_text(cx, id, vec![Piece::Text("()".into())]);
            return Ok(Term::Ctor(d, c, Vec::new()));
        }
        if reg.data(Builtin::And) == Some(*d) {
            let span = cx.span;
            let left = place(cx, info.call, Kind::Leaf, &info.place);
            let right = place(cx, info.call, Kind::Leaf, &info.place);
            let pair = Expr::Tuple(
                Box::new(resume(left, span)),
                Box::new(resume(right, span)),
                span,
            );
            let snapshot = Snapshot::take(cx);
            match check(cx, &pair, expected) {
                Ok(term) => {
                    set_text(
                        cx,
                        id,
                        vec![
                            Piece::Text("(".into()),
                            Piece::Child(left),
                            Piece::Text(", ".into()),
                            Piece::Child(right),
                            Piece::Text(")".into()),
                        ],
                    );
                    return Ok(term);
                }
                Err(e) if fatal(&e) => return Err(e),
                Err(_) => snapshot.restore(cx),
            }
        }
    }
    if is_arithmetic(&goal)
        && let Some((term, text)) = by_arithmetic(cx, expected)?
    {
        set_text(cx, id, vec![Piece::Text(text)]);
        return Ok(term);
    }
    let body = cx.e.session.walks.borrow().calls[info.call].body.clone();
    if let Some(body) = body {
        let snapshot = Snapshot::take(cx);
        match check(cx, &body, expected) {
            Ok(term) => {
                set_text(cx, id, vec![Piece::Source(body.span())]);
                return Ok(term);
            }
            Err(e) if fatal(&e) => return Err(e),
            Err(e) => {
                snapshot.restore(cx);
                return Err(stuck(
                    cx,
                    info,
                    expected,
                    "a goal is left that `then` doesn't prove",
                    &[format!("there `then` gives {}: {}", e.code, e.message)],
                ));
            }
        }
    }
    Err(stuck(
        cx,
        info,
        expected,
        "a goal is left that the closers don't prove",
        &[
            "prove it with `then t`, or expand the walk (`check --expand-walk`) and write it"
                .into(),
        ],
    ))
}

/// `arithmetic`, with as few of the conjunctions' parts in scope as it
/// needs ([`conjunct_facts`]), and its text.
fn by_arithmetic(cx: &mut Ctx, expected: &Value) -> Result<Option<(Term, String)>> {
    let span = cx.span;
    let run = |cx: &mut Ctx, facts: &[(Expr, String)]| {
        let e = Expr::Omega {
            facts: facts.iter().map(|(e, _)| e.clone()).collect(),
            span,
        };
        crate::undo::attempt(cx, |cx| check(cx, &e, expected))
    };
    let mut facts = conjunct_facts(cx)?;
    let Some(mut term) = run(cx, &facts)? else {
        return Ok(None);
    };
    let mut k = 0;
    while k < facts.len() {
        let mut fewer = facts.clone();
        fewer.remove(k);
        match run(cx, &fewer)? {
            Some(t) => {
                term = t;
                facts = fewer;
            }
            None => k += 1,
        }
    }
    let text = if facts.is_empty() {
        "arithmetic".to_string()
    } else {
        let names: Vec<&str> = facts.iter().map(|(_, t)| t.as_str()).collect();
        format!("arithmetic [{}]", names.join(", "))
    };
    Ok(Some((term, text)))
}

/// The parts of the conjunctions in scope, as `h.left`, `h.right.left`
/// and so on: `arithmetic` reads hypotheses that are comparisons, not
/// comparisons inside a conjunction.
fn conjunct_facts(cx: &Ctx) -> Result<Vec<(Expr, String)>> {
    let g = cx.g();
    let and = g.env.registry().data(Builtin::And);
    let span = cx.span;
    let mut out = Vec::new();
    for level in 0..cx.level() {
        let Some(name) = cx.name_of_level(level) else {
            continue;
        };
        if generated(name) || cx.lookup(name) != Some(level) {
            continue;
        }
        let mut todo = vec![(
            var(name, span),
            name.to_string(),
            cx.types[level].clone(),
            0,
        )];
        while let Some((e, text, ty, depth)) = todo.pop() {
            match force(&g, ty)? {
                Value::Data(d, params) if Some(d) == and && params.len() == 2 && depth < 4 => {
                    for (field, ty) in ["left", "right"].into_iter().zip(params.iter()) {
                        let part = Expr::Field(
                            Box::new(e.clone()),
                            ast::Name {
                                text: field.into(),
                                span,
                            },
                        );
                        todo.push((part, format!("{text}.{field}"), ty.clone(), depth + 1));
                    }
                }
                _ if depth > 0 => out.push((e, text)),
                _ => {}
            }
        }
    }
    Ok(out)
}

/// Whether a goal is one `arithmetic` might prove: a comparison or an
/// equation, under any conjunctions.
fn is_arithmetic(goal: &Value) -> bool {
    matches!(goal, Value::Eq(..) | Value::Neutral(..) | Value::Call(..))
}

/// A line of a walk's trace ([`WalkExpansion::trace`]) as text, from the
/// text of the file it is in.
pub fn trace_line(text: &str, line: &[Piece]) -> String {
    line.iter()
        .map(|p| match p {
            Piece::Text(t) => t.as_str(),
            Piece::Source(span) => text.get(span.range()).unwrap_or("?"),
            Piece::Child(_) => "…",
        })
        .collect()
}

/// A file's text with each walk replaced by the chain it stands for, from
/// the expansions recorded for it (those of other files ignored), indented
/// where the walk was. How many were expanded.
pub fn expand_file(
    text: &str,
    file: stitchwort_syntax::FileId,
    expansions: &[WalkExpansion],
) -> (String, usize) {
    let mut mine: Vec<&WalkExpansion> = expansions.iter().filter(|e| e.span.file == file).collect();
    mine.sort_by_key(|e| e.span.range().start);
    let mut out = String::new();
    let mut at = 0;
    let mut done = 0;
    for e in mine {
        let range = e.span.range();
        if range.start < at {
            continue;
        }
        let line_start = text[..range.start].rfind('\n').map_or(0, |i| i + 1);
        let indent: String = text[line_start..range.start]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        out.push_str(&text[at..range.start]);
        out.push_str(&render(text, &e.pieces, &indent));
        at = range.end;
        done += 1;
    }
    out.push_str(&text[at..]);
    (out, done)
}

/// Starts a line that continues the one before (an argument of a call on
/// the line above), in [`render`].
const MORE: char = '\u{1}';

/// The pieces as text, each line after the first indented by `indent` and
/// by the depth of the brackets open before it.
fn render(text: &str, pieces: &[Piece], indent: &str) -> String {
    let mut raw = String::new();
    for p in pieces {
        match p {
            Piece::Text(t) => raw.push_str(t),
            Piece::Source(span) => raw.push_str(text.get(span.range()).unwrap_or("?")),
            Piece::Child(_) => {}
        }
    }
    let mut out = String::new();
    let mut depth: usize = 0;
    for (i, line) in raw.split('\n').enumerate() {
        let mut line = line;
        if i > 0 {
            out.push('\n');
            out.push_str(indent);
            for _ in 0..depth {
                out.push_str("  ");
            }
            // A line that goes on the one before: one level further in.
            if let Some(rest) = line.strip_prefix(MORE) {
                out.push_str("  ");
                line = rest;
            }
        }
        out.push_str(line);
        for c in line.chars() {
            match c {
                '(' | '[' => depth += 1,
                ')' | ']' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    out
}
