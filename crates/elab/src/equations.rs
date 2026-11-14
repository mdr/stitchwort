//! Generated equations for each arm (docs/proposals/function-equations.md,
//! stage 1a; D2173–D2180, D2183–D2187): for a definition with arms,
//!
//! ```text
//! ex.eq3 (depth: Nat) (left: Num) (right: Num)
//!     (notArm2: (a: Nat) → (b: Nat) → left = Reg a → right = Reg b → Void):
//!     ex depth (Pr left right) = ex (depth + 1) left + ex (depth + 1) right
//! ```
//!
//! one theorem `f.eqK` per arm `K` (`f.eqK.orN` per alternative of an arm
//! with an or-pattern), whose left side is the arm's patterns and whose
//! right side is the arm's body as elaborated, `let`s substituted. Each
//! earlier arm that overlaps it becomes a hypothesis (§3.2): `notArmJ:
//! (vars) → x = p → … → Void` in Lean's form, `n ≠ k` for a number, and the
//! earlier arms' characters on one variable merged into `notListed: c ∉
//! ['k', 'j']`. A `:=` body that is a `match` on the header's parameters
//! counts as arms (D2187); local definitions get theirs (`f.go.eq1`), except
//! in a `decreasing` definition; an effect-polymorphic definition's are at
//! the empty row (its implicit rows `Empty`, divergences `Total`).
//!
//! **How a statement is found.** The arm's left side and the variables it
//! binds come from compiling the arm on its own, as the definition's own
//! `match` would, with a probe for its body ([`PROBE`]): the context there
//! is the arm's. Its right side is the body of one of the definition's
//! leaves for the arm (the leaves `check_tree` records in [`LeafLog`], by
//! their place in the case tree), read in the arm's variables. An arm the
//! tree splits further, because an earlier arm overlaps it, has several
//! leaves; their bodies are the same term with the arm's variables refined,
//! unless the body captured a refined variable (a lifted `match` does), and
//! then no leaf says the arm's right side in its own variables: the arm is
//! skipped. Its branches aren't (SW-1071): each leaf is read in its own
//! context ([`Elaborator::refined_leaves`]), the splits gone down from
//! there, and the branch stated in the arm's variables, what the leaf
//! refined each to (`Regular a`) being that variable again (`left`); every
//! leaf must give the same statement, and each is proved by its own steps.
//!
//! **How it's proved.** As a kernel term, never trusted: a case tree on the
//! equation's variables that splits wherever the definition's tree does
//! (walking that tree with the arm's left side), `rfl` at the arm's own
//! leaves and `Void.exfalso` of the hypothesis at an earlier arm's. A
//! `decreasing` definition is walked through its `f.%step`, each leaf
//! proved by `f.unfold`; an `opaque` one's equations are checked with
//! `unfolding f`, as `f.unfold` is (§4).
//!
//! **Branches** (stage 1b). Below each arm (and below a `:=` body, as
//! `f.eq`), every way through the `if`s and `match`es in tail position gets
//! an equation of its own, `f.eq2.ifTrue`, `f.eq3.some.none`
//! ([`branch_paths`] names them from the source alone). A `match` on the
//! arm's variables that is compiled into the case tree gives rows of its
//! own, whose patterns are part of the left side ([`alternative_rows`]);
//! below a row, each split adds the hypothesis it was taken under: `c =
//! True` for a `Bool` `if`, `h: p` or `notH: Not p` for `if h: p` (the
//! other `Bool` equation for `p` of the form `b = True`, D2186), and for a
//! lifted `match`, its pattern variables, `e = pattern` (named after the
//! `match`'s equation, `match found: e`) and the earlier alternatives it
//! overlaps ([`Elaborator::branch_equation`]). Proved by the row's proof,
//! going on at the row's leaf along a proof that its right side is the
//! branch's: one `J` per `Bool` `if`, `Decidable.elimEq` per `if h:` (with
//! a `J` along `Bool.uniqueEq` or `DecEq.uniqueEq` where the branch uses
//! `h`, §3.5), and per lifted `match` the helper's own equation for the
//! alternative (stage 1a's, a hidden lemma `f.%match1.eq2` where it splits)
//! carried along the hypothesis by one `J`. A `match` below a lifted
//! alternative, compiled into its helper's tree, on a variable bound further
//! up (SW-1069) is stated where the variable is bound, in the left side
//! (`repair (Succ fewer) bits`) or in an earlier alternative's pattern
//! (`List.head name = Some 'x'`): its pattern is compiled below that row
//! ([`Refine`]).
//!
//! **When.** A program's definitions get theirs when they're checked. The
//! core's and the library's are made on demand (D2178's fallback: eager,
//! they cost every start), when first named (a module's needs) or listed
//! (`search`), from their source in the library index
//! ([`Elaborator::ensure_equations`]), in the defining file's scope (its
//! imports, and for the core no library names), so they come out the same
//! whoever asks.
//!
//! What isn't generated (§3.2, "Not generated") is recorded with the reason,
//! and naming it is `E-NO-EQUATION` ([`no_equation`]).

use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{Elim, Head, eval, force};
use stitchwort_core::{DataId, DefId, Ev, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Decl, Expr, MatchKind, Pattern, Scrutinee};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Saved};
use crate::decreasing::{Binder, apps, lams, pis, split_pis};
use crate::{Elaborator, Global, Result, kernel};

mod induct;

/// The variable the probe's body is: [`probe`] records the context it's
/// checked in.
pub(crate) const PROBE: &str = "%equation-probe";

/// What making one equation may take: steps, the size of a term, frames.
/// The equations of std take far less (the largest a few thousand steps).
const ATTEMPT: stitchwort_core::budget::Limits = stitchwort_core::budget::Limits {
    work: 5_000_000,
    stack: 0,
    size: 1_000_000,
    frames: 100_000,
    native_frames: 100_000,
};

/// A right side larger than this many times its arm's elaborated body
/// (`let`s substituted can make it so) isn't generated (§10; the factor is
/// the note's guess).
const SIZE_FACTOR: usize = 10;

/// Whether a right side of `size` nodes is too large to state for an arm
/// whose elaborated body has `arm_size` (§10).
fn too_large(size: usize, arm_size: usize) -> bool {
    size > 256 && size > SIZE_FACTOR.saturating_mul(arm_size)
}

/// A leaf body with `let`s substituted larger than this isn't read further
/// for its row's equation, whatever the branches its splits take: reading
/// it costs time linear in it (a quarter of a second at 150,000 nodes), for
/// every row, and a chain of `let`s each using the last twice substitutes
/// to a tree exponential in the chain's length (SW-2512). A body this
/// large is also more than ten times its arm's (§10), so a row with no
/// splits loses nothing; a row whose split takes a small branch of it
/// loses its equation.
const READ_CAP: usize = 1 << 16;

fn too_large_to_read(size: usize, arm_size: usize) -> String {
    format!(
        "its body with `let`s substituted would be {size} nodes, too many to read (over \
         {READ_CAP}, and ten times its arm's {arm_size})"
    )
}

fn too_large_why(size: usize, arm_size: usize) -> String {
    format!("its right side would be {size} nodes, more than ten times its arm's {arm_size}")
}

/// An equation that would take more than this many hypotheses `x ≠ k` for
/// earlier number arms isn't generated (D2189): its proof splits on the
/// number with every one of them in context, which the kernel refines at
/// each number, so checking it costs their count squared.
const LITERAL_CAP: usize = 64;

/// Why a row an earlier one overlaps has no equation of its own when each
/// of its leaves' bodies captures what that leaf refined (SW-1071).
const REFINED: &str = "an earlier arm overlaps it, so its body was elaborated once for each \
                       case of that arm's patterns, each with the variables refined, and a \
                       lifted `match` or local definition captures them: no one right side \
                       states it in the arm's variables";

/// [`REFINED`], and for a row with branches, that they have equations.
fn refined_reason(branches: bool) -> String {
    if branches {
        format!("{REFINED} (its branches' equations, each read from every case, do)")
    } else {
        REFINED.to_string()
    }
}

// ------------------------------------------------------------ the leaf log

/// Where each case tree's leaves are: recorded by `check_tree` while a
/// declaration's bodies are checked, by the tree's root (the name of the
/// definition, top-level or local, whose body it is) and the path of choices
/// to the leaf, which the kernel term has too.
#[derive(Default)]
pub(crate) struct LeafLog {
    /// The choices from the current root to here: a constructor's index, or
    /// a number case's arm (its default after them).
    pub(crate) path: Vec<u32>,
    root: Option<Span>,
    leaves: Vec<Leaf>,
}

#[derive(Clone)]
struct Leaf {
    root: Span,
    path: Vec<u32>,
    /// The row's span: the arm's, or the or-pattern alternative's.
    span: Span,
    /// The or-pattern alternatives that chose the row.
    alternatives: Vec<Span>,
}

impl LeafLog {
    /// A leaf of the tree being checked, if it's a definition's.
    pub(crate) fn record(&mut self, span: Span, alternatives: &[Span]) {
        if let Some(root) = self.root {
            self.leaves.push(Leaf {
                root,
                path: self.path.clone(),
                span,
                alternatives: alternatives.to_vec(),
            });
        }
    }

    /// The body of the definition named at `root` is checked from here.
    pub(crate) fn enter_root(&mut self, root: Span) -> (Option<Span>, Vec<u32>) {
        (self.root.replace(root), std::mem::take(&mut self.path))
    }

    /// Back to the tree [`Self::enter_root`] left.
    pub(crate) fn leave_root(&mut self, saved: (Option<Span>, Vec<u32>)) {
        self.root = saved.0;
        self.path = saved.1;
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.leaves.is_empty() && self.path.is_empty() && self.root.is_none()
    }
}

// --------------------------------------------------------------- the probe

/// What the probe saw: the context at the arm's leaf and its goal.
pub(crate) struct Probed {
    saved: Saved,
    goal: Value,
}

/// The probe's state: which probe to record, and what it saw.
#[derive(Default)]
pub(crate) struct ProbeState {
    wanted: Option<Span>,
    found: Option<Probed>,
}

impl ProbeState {
    pub(crate) fn is_empty(&self) -> bool {
        self.wanted.is_none() && self.found.is_none()
    }
}

/// The probe [`PROBE`], checked at `span` against `expected`: records the
/// context if it's the one wanted. Its term is never used.
pub(crate) fn probe(cx: &mut Ctx, expected: &Value, span: Span) -> Term {
    let mut state = cx.e.decl.arm_probe.borrow_mut();
    if state.wanted == Some(span) && state.found.is_none() {
        state.found = Some(Probed {
            saved: cx.save(),
            goal: expected.clone(),
        });
    }
    Term::Refl
}

// ---------------------------------------------------------------- the arms

/// How a definition's arms are written.
enum Form {
    /// Arms, each with the header's parameters first.
    Arms,
    /// A `:=` body that is, as a whole, a `match` on header parameters
    /// (D2187): its alternatives are the arms, matching those parameters.
    WholeMatch,
    /// Any other `:=` body with a split in tail position: no arms, so no
    /// `f.eqK`, only the branches below the body, `f.eq.ifTrue` (§3.3).
    Body,
}

/// One row: an arm, one alternative of an arm with or-patterns, or (stage
/// 1b) an alternative of a `match` on the arm's variables that is compiled
/// into the case tree (§3.2, "`match` in tail position"), whose pattern is
/// part of its left side.
#[derive(Clone)]
struct Row {
    /// The arm's number, from 1 (0 for a [`Form::Body`]).
    arm: usize,
    /// The alternative's number among the arm's, from 1; `None` for an arm
    /// without or-patterns.
    or: Option<usize>,
    /// Its patterns, without or-patterns, one per column.
    patterns: Vec<Pattern>,
    /// The spans of the alternatives chosen, sorted.
    alternatives: Vec<Span>,
    /// The arm's span: a leaf's row span is it or inside it.
    span: Span,
    /// Whether it has a right side (an arm with `()` has none).
    has_rhs: bool,
    /// Whether the arm has an `if` condition, and the condition.
    guarded: bool,
    guard: Option<ast::Guard>,
    /// Its name below the definition's: `eq2`, `eq2.or1`, `eq2.cons`.
    suffix: String,
    /// The right side as written, if the row has one.
    rhs: Option<Expr>,
    /// For an alternative of a `match` compiled into the case tree: the
    /// row whose right side the `match` is, and its number in the `match`.
    parent: Option<usize>,
    alt: usize,
    /// The `match`es from the arm down to this alternative, each with the
    /// alternative's patterns: the probe compiles them below the arm's.
    chain: Vec<(Vec<Scrutinee>, Vec<Pattern>)>,
}

impl Row {
    fn suffix(&self) -> String {
        self.suffix.clone()
    }

    /// Every pattern from the arm down: the variables in written order.
    fn written(&self) -> Vec<Pattern> {
        let mut out = self.patterns.clone();
        for (_, ps) in &self.chain {
            out.extend(ps.iter().cloned());
        }
        out
    }
}

// ------------------------------------------------- splits, as written

/// A split in tail position of a right side, as the source writes it
/// (§3.1): tail position goes through `let`s and local definitions, and
/// through the branches of these splits, nowhere else.
#[derive(Clone, Copy)]
enum TailSplit<'a> {
    If {
        binder: Option<&'a ast::Name>,
    },
    Match {
        scrutinees: &'a [Scrutinee],
        alts: &'a [Alt],
    },
}

/// One way through a split: the split, which way (`0` for `then`, or the
/// alternative's index), and its segment of the name.
#[derive(Clone)]
struct Taken<'a> {
    split: TailSplit<'a>,
    choice: usize,
    seg: String,
}

/// The split `e` is in tail position, and its ways, each with its body.
fn tail_split(e: &Expr) -> Option<(TailSplit<'_>, Vec<(String, &Expr)>)> {
    match e {
        Expr::Bracketed(inner, _) => tail_split(inner),
        Expr::Let { body, .. } | Expr::LocalDefs { body, .. } => tail_split(body),
        // A destructuring `let` (`let (a, b) := e`, `let { x, y } := e`) is a
        // one-alternative `match` in the source. A tuple or record pattern
        // (or a proof constructor's) binds projections outside a proof
        // (`patlet.rs`), so the split below it is in tail position as an
        // ordinary `let`'s is; one whose pattern compiles into the case tree
        // is skipped by `alternative_rows`, with the reason.
        Expr::Match {
            alts,
            kind: MatchKind::Let,
            ..
        } if alts.len() == 1 => tail_split(alts[0].body.as_ref()?),
        Expr::If {
            binder,
            then,
            otherwise,
            ..
        } => Some((
            TailSplit::If {
                binder: binder.as_ref(),
            },
            vec![
                ("ifTrue".to_string(), &**then),
                ("ifFalse".to_string(), &**otherwise),
            ],
        )),
        Expr::Match {
            scrutinees,
            alts,
            kind: MatchKind::Match,
            ..
        } if alts.iter().all(|a| a.body.is_some()) => Some((
            TailSplit::Match { scrutinees, alts },
            alt_names(alts)
                .into_iter()
                .zip(alts)
                .filter_map(|(s, a)| Some((s, a.body.as_ref()?)))
                .collect(),
        )),
        _ => None,
    }
}

/// The constructor an alternative is, when it's one constructor applied to
/// variables or `_` (in one column): `Some`, `Cons`, `True`.
fn alt_ctor(alt: &Alt) -> Option<String> {
    let [p] = alt.patterns.as_slice() else {
        return None;
    };
    let plain = |p: &Pattern| matches!(p, Pattern::Var(_) | Pattern::Wildcard(_));
    let last = |n: &ast::Name| n.text.rsplit('.').next().unwrap_or("").to_string();
    let name = match p {
        Pattern::Ctor(n, args, _) if args.iter().all(plain) => last(n),
        Pattern::Var(n) if last(n).starts_with(|c: char| c.is_uppercase()) => last(n),
        Pattern::CtorFields { ctor, fields, .. } if fields.iter().all(|(_, p)| plain(p)) => {
            last(ctor)
        }
        Pattern::Nil(_) => "Nil".to_string(),
        Pattern::Cons(a, b, _) if plain(a) && plain(b) => "Cons".to_string(),
        _ => return None,
    };
    (!name.is_empty()).then_some(name)
}

/// Each alternative's segment of the name (§3.2): its constructor in lower
/// case (`some`, `cons`, `true`), or `altN` (a literal, a nested pattern,
/// several columns, a catch-all, or a constructor an earlier one took).
fn alt_names(alts: &[Alt]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for (i, a) in alts.iter().enumerate() {
        let name = alt_ctor(a).map(|c| {
            let mut cs = c.chars();
            let first = cs.next().map(|f| f.to_lowercase().collect::<String>());
            first.unwrap_or_default() + cs.as_str()
        });
        match name {
            Some(n) if !out.contains(&n) => out.push(n),
            _ => out.push(format!("alt{}", i + 1)),
        }
    }
    out
}

/// The ways through the splits in tail position of `e`, to a result
/// through at least one split, each as the splits taken.
fn branch_paths(e: &Expr) -> Vec<Vec<Taken<'_>>> {
    let Some((split, ways)) = tail_split(e) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (choice, (seg, body)) in ways.into_iter().enumerate() {
        let taken = Taken { split, choice, seg };
        let below = branch_paths(body);
        if below.is_empty() {
            out.push(vec![taken.clone()]);
        }
        for mut b in below {
            b.insert(0, taken.clone());
            out.push(b);
        }
    }
    out
}

/// The rows for the alternatives of the `match` that is row `parent`'s
/// (index `at`) right side, compiled into the case tree: each with the
/// alternative's patterns below the row's. Or why there are none.
fn alternative_rows(parent: &Row, at: usize) -> std::result::Result<Vec<Row>, &'static str> {
    let mut rhs = parent.rhs.as_ref().ok_or("it has no right side")?;
    while let Expr::Bracketed(inner, _) = rhs {
        rhs = inner;
    }
    let Expr::Match {
        scrutinees,
        alts,
        kind,
        ..
    } = rhs
    else {
        return Err("its `match` compiled into the case tree isn't its whole right side");
    };
    if matches!(kind, MatchKind::Let) {
        return Err(
            "a destructuring `let` compiled into the case tree (a data constructor, `_` or `()`) \
             isn't stated in stage 1b: only a tuple or record pattern `let` binds projections, \
             which a tail `match` or `if` can be stated below",
        );
    }
    if !matches!(kind, MatchKind::Match) {
        return Err("its `match` compiled into the case tree isn't its whole right side");
    }
    if parent.or.is_some() {
        return Err(
            "a `match` compiled into the case tree below an arm with an or-pattern isn't stated \
             in stage 1b",
        );
    }
    if alts.iter().any(|a| a.patterns.iter().any(has_or)) {
        return Err(
            "an alternative with an or-pattern, in a `match` compiled into the case tree, isn't \
             stated in stage 1b",
        );
    }
    let mut out = Vec::new();
    for (a, (alt, seg)) in alts.iter().zip(alt_names(alts)).enumerate() {
        let mut chain = parent.chain.clone();
        chain.push((scrutinees.clone(), alt.patterns.clone()));
        out.push(Row {
            arm: parent.arm,
            or: None,
            patterns: parent.patterns.clone(),
            alternatives: Vec::new(),
            span: alt.span,
            has_rhs: alt.body.is_some(),
            guarded: alt.guard.is_some(),
            guard: alt.guard.clone(),
            suffix: format!("{}.{seg}", parent.suffix),
            rhs: alt.body.clone(),
            parent: Some(at),
            alt: a + 1,
            chain,
        });
    }
    Ok(out)
}

/// The body a probe compiles in place of an arm's right side `rhs`, when
/// the arms are compiled again: the probe, or where the right side is a
/// `match` on the variables `known` (which the definition compiled into its
/// case tree), that `match` with a probe for each alternative's body, so
/// its leaves are recorded too.
fn probe_body(rhs: Option<&Expr>, span: Span, known: &[String]) -> Expr {
    let probe = Expr::Var(ast::Name {
        text: PROBE.into(),
        span,
    });
    let Some(Expr::Match {
        scrutinees,
        alts,
        span: at,
        kind: MatchKind::Match,
    }) = rhs
    else {
        return probe;
    };
    let mut seen: Vec<&str> = Vec::new();
    for s in scrutinees {
        match (&s.name, &s.expr) {
            (None, Expr::Var(x)) if known.contains(&x.text.to_string()) => {
                if seen.contains(&x.text.as_str()) {
                    return probe;
                }
                seen.push(&x.text);
            }
            _ => return probe,
        }
    }
    Expr::Match {
        scrutinees: scrutinees.clone(),
        alts: alts
            .iter()
            .map(|a| {
                let mut inner = known.to_vec();
                inner.extend(
                    crate::written_names(&a.patterns)
                        .into_iter()
                        .map(str::to_string),
                );
                Alt {
                    guard: a.guard.clone(),
                    patterns: a.patterns.clone(),
                    // An absurd alternative stays one: given a body, its `()`
                    // would be the unit pattern.
                    body: (a.body.as_ref()).map(|b| probe_body(Some(b), a.span, &inner)),
                    span: a.span,
                }
            })
            .collect(),
        span: *at,
        kind: MatchKind::Match,
    }
}

/// A path's name below its row's: `ifTrue.some`.
fn path_suffix(path: &[Taken]) -> String {
    path.iter()
        .map(|t| t.seg.as_str())
        .collect::<Vec<_>>()
        .join(".")
}

/// Every way of choosing one alternative of each or-pattern in `patterns`:
/// the patterns chosen, and the spans of the alternatives, sorted.
fn expand_or(patterns: &[Pattern]) -> Vec<(Vec<Pattern>, Vec<Span>)> {
    let mut out: Vec<(Vec<Pattern>, Vec<Span>)> = vec![(Vec::new(), Vec::new())];
    for p in patterns {
        let mut next = Vec::new();
        for (done, spans) in &out {
            for (q, more) in expand_one(p) {
                let mut d = done.clone();
                d.push(q);
                let mut s = spans.clone();
                s.extend(more);
                next.push((d, s));
            }
        }
        out = next;
    }
    for (_, spans) in &mut out {
        spans.sort_by_key(|s| (s.start, s.end));
    }
    out
}

fn expand_one(p: &Pattern) -> Vec<(Pattern, Vec<Span>)> {
    let many = |ps: &[Pattern], rebuild: &dyn Fn(Vec<Pattern>) -> Pattern| {
        expand_or(ps)
            .into_iter()
            .map(|(qs, spans)| (rebuild(qs), spans))
            .collect::<Vec<_>>()
    };
    match p {
        Pattern::Or(alternatives, _) => alternatives
            .iter()
            .flat_map(|a| {
                expand_one(a).into_iter().map(move |(q, mut spans)| {
                    spans.push(a.span());
                    (q, spans)
                })
            })
            .collect(),
        Pattern::Ctor(n, args, span) => many(args, &|qs| Pattern::Ctor(n.clone(), qs, *span)),
        Pattern::Tuple(a, b, span) => many(&[(**a).clone(), (**b).clone()], &|mut qs| {
            let b = qs.pop().expect("two");
            let a = qs.pop().expect("two");
            Pattern::Tuple(Box::new(a), Box::new(b), *span)
        }),
        Pattern::Cons(a, b, span) => many(&[(**a).clone(), (**b).clone()], &|mut qs| {
            let b = qs.pop().expect("two");
            let a = qs.pop().expect("two");
            Pattern::Cons(Box::new(a), Box::new(b), *span)
        }),
        Pattern::Named(n, q, span) => many(std::slice::from_ref(&**q), &|mut qs| {
            Pattern::Named(n.clone(), Box::new(qs.pop().expect("one")), *span)
        }),
        Pattern::Record { fields, rest, span } => {
            let ps: Vec<Pattern> = fields.iter().map(|(_, p)| p.clone()).collect();
            many(&ps, &|qs| Pattern::Record {
                fields: fields.iter().map(|(n, _)| n.clone()).zip(qs).collect(),
                rest: *rest,
                span: *span,
            })
        }
        Pattern::CtorFields {
            ctor,
            fields,
            rest,
            span,
            ..
        } => {
            let ps: Vec<Pattern> = fields.iter().map(|(_, p)| p.clone()).collect();
            many(&ps, &|qs| {
                Pattern::ctor_fields(
                    ctor.clone(),
                    fields.iter().map(|(n, _)| n.clone()).zip(qs).collect(),
                    *rest,
                    *span,
                )
            })
        }
        Pattern::Var(_)
        | Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => vec![(p.clone(), Vec::new())],
    }
}

fn has_or(p: &Pattern) -> bool {
    expand_one(p).len() > 1 || matches!(p, Pattern::Or(..))
}

/// The name `if h: P` gives a guard's proof, if it names one.
fn guard_name(guard: Option<&ast::Guard>) -> Option<String> {
    guard
        .and_then(|g| g.binder.as_ref())
        .map(|h| h.text.to_string())
        .filter(|h| h != "_")
}

/// One arm as the source writes it: its patterns, its right side (`None`
/// for an arm with `()`), and its span.
struct SourceArm {
    patterns: Vec<Pattern>,
    /// The arm's `if` condition, if it has one.
    guard: Option<ast::Guard>,
    rhs: Option<Expr>,
    span: Span,
}

/// A definition's arms as the source writes them (`source_arms`): the form,
/// the columns' parameter names (for a whole-body `match`, its
/// scrutinees), and the arms (for a [`Form::Body`], the body as one arm
/// without patterns).
type SourceArms = (Form, Vec<String>, Vec<SourceArm>);

fn source_arms(equations: &[Decl]) -> Option<SourceArms> {
    let first = equations.first()?;
    let Decl::Equation {
        patterns,
        rhs,
        arm,
        span,
        ..
    } = first
    else {
        return None;
    };
    if arm.is_some() {
        let arms = equations
            .iter()
            .filter_map(|e| match e {
                Decl::Equation {
                    patterns,
                    guard,
                    rhs,
                    span,
                    ..
                } => Some(SourceArm {
                    patterns: patterns.clone(),
                    guard: guard.clone(),
                    rhs: rhs.clone(),
                    span: *span,
                }),
                _ => None,
            })
            .collect();
        return Some((Form::Arms, Vec::new(), arms));
    }
    if equations.len() != 1 {
        return None;
    }
    let body = rhs.as_ref()?;
    // Any other `:=` body: its branches, if it has a split in tail
    // position.
    let as_body = || {
        (!branch_paths(body).is_empty()).then(|| {
            (
                Form::Body,
                Vec::new(),
                vec![SourceArm {
                    patterns: Vec::new(),
                    guard: None,
                    rhs: Some(body.clone()),
                    span: *span,
                }],
            )
        })
    };
    let Expr::Match {
        scrutinees,
        alts,
        kind: MatchKind::Match,
        ..
    } = body
    else {
        return as_body();
    };
    let header: Vec<&str> = patterns
        .iter()
        .filter_map(|p| match p {
            Pattern::Var(x) => Some(x.text.as_str()),
            _ => None,
        })
        .collect();
    let mut columns = Vec::new();
    for s in scrutinees {
        match (&s.name, &s.expr) {
            (None, Expr::Var(x)) if header.contains(&x.text.as_str()) => {
                columns.push(x.text.to_string())
            }
            _ => return as_body(),
        }
    }
    let arms = alts
        .iter()
        .map(|a: &Alt| SourceArm {
            patterns: a.patterns.clone(),
            guard: a.guard.clone(),
            rhs: a.body.clone(),
            span: a.span,
        })
        .collect();
    Some((Form::WholeMatch, columns, arms))
}

/// The equation names the source implies for a definition with these
/// equations (§3.3): `eq1`, `eq2`, `eq3.or1`, …, and below each its
/// branches (`eq2.ifTrue`, `eq3.some.none`; `eq.ifFalse` below a `:=`
/// body), under the definition's key. The library index lists them before
/// the file is elaborated.
pub(crate) fn source_suffixes(equations: &[Decl]) -> Vec<String> {
    let Some((form, _, arms)) = source_arms(equations) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (k, arm) in arms.iter().enumerate() {
        let mut rows = Vec::new();
        if matches!(form, Form::Body) {
            rows.push("eq".to_string());
        } else if arm.patterns.iter().any(has_or) {
            for m in 1..=expand_or(&arm.patterns).len() {
                rows.push(format!("eq{}.or{m}", k + 1));
            }
        } else {
            rows.push(format!("eq{}", k + 1));
        }
        let paths = arm.rhs.as_ref().map(branch_paths).unwrap_or_default();
        for row in rows {
            if !matches!(form, Form::Body) {
                out.push(row.clone());
            }
            for path in &paths {
                out.push(format!("{row}.{}", path_suffix(path)));
            }
        }
    }
    out
}

/// Whether a declared key's last part is an equation name reserved for the
/// definition `prefix` names: `f.eq`, `f.eq3`, `f.eq3.or1`, … (D2176).
pub(crate) fn reserved_suffix(key: &str) -> Option<(&str, &str)> {
    // `f.eqK.orN` and `f.eqK.ifTrue…`: the `eq` part is the first one that
    // looks like it, after at least one segment of the owner.
    let mut owner_len = 0;
    for (i, part) in key.split('.').enumerate() {
        let digits = part.strip_prefix("eq");
        if i > 0 && digits.is_some_and(|d| d.chars().all(|c| c.is_ascii_digit())) {
            return Some((&key[..owner_len - 1], &key[owner_len..]));
        }
        owner_len += part.len() + 1;
    }
    // `f.induct` (stage 2a).
    match key.strip_suffix(".induct") {
        Some(owner) if !owner.is_empty() => Some((owner, "induct")),
        _ => None,
    }
}

/// Whether a local definition can't be called `name`: `eq`, `eqK` and
/// `induct` would be its owner's generated names (D2176).
pub(crate) fn reserved_local(name: &str) -> bool {
    name == "induct"
        || name
            .strip_prefix("eq")
            .is_some_and(|d| d.chars().all(|c| c.is_ascii_digit()))
}

// ------------------------------------------------------- what an arm says

/// An arm's statement, as the probe found it: a context of `depth`
/// variables (the probe's predicate at level 0, then the definition's
/// parameters, then the patterns' fields), the definition's arguments in
/// it, and the variables the equation takes, in order.
struct Shape {
    depth: usize,
    lhs: Vec<Term>,
    /// The levels the equation takes, in order, with their names, how
    /// they're passed, and their types (terms at `depth`).
    tele: Vec<usize>,
    names: Vec<Name>,
    icits: Vec<Icit>,
    types: Vec<Term>,
    /// A guarded row's condition.
    guard: Option<GuardRead>,
}

/// A guarded row's condition, as the definition's tree tests it where the
/// row is first reached: `Bool.ifThenElse` on a `Bool` `cond`, or
/// `Decidable.elim` on a proposition `cond` (a decided one whose proof an
/// arm uses, or `if h: P`). `cond` is a term at the shape's depth.
///
/// `prop` is set where the `Bool` is a decided proposition's,
/// `Decidable.holds d` (but not a comparison's, which reads as itself):
/// the hypotheses say the proposition, `P` and `¬P`.
#[derive(Clone)]
struct GuardRead {
    dec: bool,
    cond: Term,
    prop: Option<Term>,
    /// The tree tests a comparison by `Decidable.elim` (an arm uses its
    /// proof), whose proposition is an equation of `Bool`s: `cond` is
    /// that equation, `c = True`, so the hypotheses read as they do where
    /// the tree uses `Bool.ifThenElse` (`c = True`, `c = False`), and
    /// the walk reads the tree's proposition the same way
    /// ([`Elaborator::bool_equation`]).
    unfolded: bool,
    /// For a condition `¬Q` of a decided `Q` tested by its `Bool`
    /// (`n != 3`), `Q`: the arm below takes `Q`, not `¬¬Q`.
    negated: Option<Term>,
}

impl GuardRead {
    /// What the hypotheses about the condition say: whether it is a
    /// proposition, and the term.
    fn stated(&self) -> (bool, &Term) {
        match &self.prop {
            Some(p) => (true, p),
            None => (self.dec, &self.cond),
        }
    }
}

/// A row's statement ([`Elaborator::stated`]): the variables and
/// hypotheses it takes, and its two sides at their depth.
struct Stated {
    binders: Vec<(Name, Icit, Term)>,
    hyps: Vec<Hyp>,
    lhs: Term,
    /// `None` for a row an earlier one overlaps whose leaves' bodies each
    /// capture the variables that leaf refined: no one term says its right
    /// side ([`Elaborator::refined_leaves`] reads each leaf instead).
    rhs: Option<Term>,
    /// The sizes of the right side and of the leaf's body it came from.
    rhs_size: usize,
    arm_size: usize,
}

/// A branch's statement below its row's ([`Elaborator::branch_steps`]):
/// the row's binders and the splits' after them, the splits, and the
/// branch's right side at the depth of all the binders.
struct Stepped {
    binders: Vec<(Name, Icit, Term)>,
    steps: Vec<Step>,
    cur: Term,
    unfolding: Vec<DefId>,
}

/// One split a branch goes down, as its statement says it (stage 1b):
/// `depth` is how many binders the statement has before the split's, and
/// the terms are at that depth.
enum Step {
    /// `Bool.ifThenElse [a] c t e`, either way; its hypothesis `c = True` (or
    /// `False`) is the binder at level `depth`.
    Ite {
        depth: usize,
        head: Term,
        args: Vec<(Term, Icit)>,
    },
    /// `Decidable.elim [p] [a] d y n` (`if h: p`), one way; its hypothesis
    /// is the binder at level `depth`: `p`, or `Not p`, or for `p` of the
    /// form `b = X` (`X` a `Bool`, `true` if `True`), `b` is the other
    /// (`normal`, D2186). `uniq`: how two proofs of `p` are equal, when
    /// the branch uses its proof (§3.5).
    Dec {
        depth: usize,
        args: Vec<(Term, Icit)>,
        yes: bool,
        uniq: Option<Uniq>,
        normal: Option<(Term, bool)>,
    },
    /// A lifted `match`'s helper `head` applied to `args`, one
    /// alternative: matching argument `cols` (with its equation argument
    /// `eq`, `match h: e`), its hypothesis `e = pattern` the binder at
    /// level `hyp` (none for a catch-all), the statement having `after`
    /// binders once the alternative's are added. `proof`, at `after`, is
    /// the helper's equation for the alternative: `head args' = result`,
    /// with `args'` the call's arguments but the pattern for `e`.
    Helper {
        depth: usize,
        after: usize,
        head: Term,
        args: Vec<(Term, Icit)>,
        /// The arguments matched: one, or on several expressions (SW-1074)
        /// each, `hyp` being `(e1, e2, …) = (p1, p2, …)` at the tuple of
        /// `col_tys` (at `depth`), which is otherwise empty.
        cols: Vec<usize>,
        col_tys: Vec<Term>,
        eq: Option<usize>,
        hyp: Option<usize>,
        proof: Term,
        result: Term,
    },
}

/// How two proofs of an `if`'s condition are equal: `Bool.uniqueEq l r`
/// for an equation `l = r` of `Bool`s; `DecEq.uniqueEq` with these
/// arguments (`[a] [instance] [x] [y]`) and the icits of its two proofs.
enum Uniq {
    Bool(Term, Term),
    DecEq(DefId, Vec<(Term, Icit)>, Vec<Icit>),
}

/// A lifted `match`'s helper's call: the parameter it matches, and its
/// equation's (`match h: e`), if it takes one.
struct Call {
    cols: Vec<usize>,
    eq: Option<usize>,
}

/// A lifted `match`'s helper's equations, one for each alternative, as its
/// arms' would be (stage 1a), or why not.
struct Helper {
    arity: usize,
    /// The helper as a definition whose arms are the alternatives, and
    /// where its alternatives are written (for probing a row again with
    /// patterns below it, [`Refine`]).
    def: Def,
    root: Span,
    /// Rows made again with patterns below them ([`Elaborator::refined_row`]),
    /// by the row and the refinements' keys.
    #[allow(clippy::type_complexity)]
    refined: std::cell::RefCell<HashMap<(usize, Vec<Span>), Rc<(HelperEq, Shape)>>>,
    /// By row: the alternatives first, then the rows below those whose
    /// right side is a `match` compiled into the helper's tree.
    shapes: Vec<std::result::Result<Shape, String>>,
    eqs: Vec<std::result::Result<HelperEq, String>>,
    /// Each row's rows below it, in the inner `match`'s order.
    children: Vec<Vec<usize>>,
}

/// One alternative's equation of a helper: its binders (variables, then
/// hypotheses), the helper's arguments on its left side and its right side
/// (at their depth), and its proof and type, closed.
struct HelperEq {
    binders: Vec<(Name, Icit, Term)>,
    args: Vec<(Term, Icit)>,
    rhs: Term,
    proof: Term,
    ty: Term,
    /// Whether its proof splits a variable: then it is declared, once, as
    /// a hidden lemma (`decl`) for the branches' proofs to use.
    split: bool,
    decl: std::cell::Cell<Option<DefId>>,
}

/// Where a variable a `match` below a lifted `match`'s alternative splits
/// was bound (SW-1069): by the row's left side (the arm's patterns, the
/// header's parameters), or as a pattern variable of the alternative taken
/// at the lifted `match` that is `path[i]`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Site {
    Row,
    Step(usize),
}

/// A `match` compiled into a lifted `match`'s helper's tree, on a variable
/// the helper captured from further up (SW-1069): the helper's equation for
/// the alternative takes the variable as that `match`'s pattern, so the
/// branch states it there, where the variable is bound. The `match`'s
/// scrutinees and the alternative's patterns are compiled below that row
/// (the definition's, or the helper's), as rows below an arm are.
#[derive(Clone)]
struct Refine {
    site: Site,
    scrutinees: Vec<Scrutinee>,
    patterns: Vec<Pattern>,
    /// The alternative's span: one refinement is asked for once.
    key: Span,
    /// The alternative's segment of the name (`zero`, `alt1`).
    seg: String,
}

/// One leaf of a row an earlier row overlaps (SW-1071), as a walk of the
/// definition's tree with the row's left side reaches it: its context is
/// the row's variables then the fields the walk split off, `depth` in all.
struct LeafCtx {
    path: Vec<u32>,
    depth: usize,
    /// The leaf's body, read here (`let`s substituted, as a right side is).
    body: Term,
    /// The row's variables the walk refined, with what each is here
    /// (`left` is `Regular a`).
    images: Vec<(usize, Term)>,
    /// The size of the leaf's body as elaborated.
    size: usize,
}

/// A leaf's proof (SW-1071), at its [`LeafCtx`]'s depth then the branch's
/// binders, that its body is the branch's right side.
struct LeafProof {
    path: Vec<u32>,
    depth: usize,
    q: Term,
}

/// How a row's leaf goes on, in an equation's proof: `rfl` (or
/// `f.unfold`) alone; for a branch, along a proof that the row's right side
/// is the branch's, one for every leaf, or (SW-1071) one per leaf; with the
/// statement's left side (both at the statement's depth).
enum Then {
    Own,
    One(Term, Term),
    PerLeaf(Term, Vec<LeafProof>),
}

/// The declarations branch equations are proved with.
struct BranchLib {
    ite: DefId,
    elim: DefId,
    elim_eq: DefId,
    elim_eq_icits: Vec<Icit>,
    bool: DataId,
    true_: usize,
    false_: usize,
    not: DefId,
    exfalso: DefId,
    true_not_false: DefId,
    false_not_true: DefId,
    bool_unique: DefId,
    deceq_unique: Option<(DefId, Vec<Icit>)>,
    deceq_decide: Option<DefId>,
    inspect: Option<DefId>,
    to_bool: DefId,
    /// `Decidable` and `Decidable.refute` and `Decidable.toBoolOfNot`, if
    /// std is loaded: a guard on a decided proposition that the definition
    /// tests by its `Bool` is stated as the proposition only with them and
    /// the decision's `sound` and `complete` fields.
    to_bool_lemmas: Option<(DataId, DefId, DefId)>,
    /// `Bool.decTrue`, which decides a `Bool` operand `c` as `c = True`.
    dec_true: Option<DefId>,
    and_data: DataId,
    /// `Decidable.and`, whose `holds` is the `a && b` of its sides', so a
    /// conjunction ([`Decided::Conj`]) is decided by it and the four
    /// lemmas above apply to that decision.
    and_dec: Option<DefId>,
    /// `Decidable.notNotOf` and `Decidable.not`, which decide `¬Q` from `Q`'s decision.
    not_not: Option<(DefId, DefId)>,
}

/// A `Bool` that states a decided proposition, as the hypotheses about a
/// guard say it.
#[derive(Clone)]
enum Decided {
    /// `Decidable.holds [P] d`.
    One(Term, Term),
    /// `a && b`, as `if a then b else False`, each operand a decided
    /// proposition's `Bool` or another `Bool` `c` (as `c = True`).
    Conj(Box<ConjView>),
}

/// `a && b` read as the conjunction `pa ∧ pb`: each side's proposition
/// `p` and its decision `d`, whose `holds` is that side's `Bool`.
#[derive(Clone)]
struct ConjView {
    left: Operand,
    right: Operand,
}

#[derive(Clone)]
struct Operand {
    prop: Term,
    decision: Term,
}

impl Decided {
    /// The proposition the `Bool` is a decision of.
    fn prop(&self, lib: &BranchLib) -> Term {
        match self {
            Decided::One(p, _) => p.clone(),
            Decided::Conj(v) => Term::data(
                lib.and_data,
                vec![v.left.prop.clone(), v.right.prop.clone()],
            ),
        }
    }

    fn shift(&self, g: &Ev, by: usize) -> R<Decided> {
        let sh = |t: &Term| t.shift(g, by, 0);
        Ok(match self {
            Decided::One(p, d) => Decided::One(sh(p)?, sh(d)?),
            Decided::Conj(v) => {
                let op = |o: &Operand| -> R<Operand> {
                    Ok(Operand {
                        prop: sh(&o.prop)?,
                        decision: sh(&o.decision)?,
                    })
                };
                Decided::Conj(Box::new(ConjView {
                    left: op(&v.left)?,
                    right: op(&v.right)?,
                }))
            }
        })
    }

    /// The proof `which` (0 `d.complete`, 1 `Decidable.toBoolOfNot`, 2
    /// `d.sound`, 3 `Decidable.refute`; for a conjunction, its decision's)
    /// of the proposition and the `Bool`, applied to `h`.
    fn lemma(&self, lib: &BranchLib, which: usize, h: Term) -> R<Term> {
        match self {
            Decided::One(p, d) => lib.to_bool_lemma(which, p.clone(), d.clone(), h),
            Decided::Conj(v) => {
                let decision = lib.conjunction_decision(v)?;
                lib.to_bool_lemma(which, self.prop(lib), decision, h)
            }
        }
    }
}

impl BranchLib {
    fn bool_ty(&self) -> Term {
        Term::Data(self.bool, Vec::new())
    }

    /// `Decidable.and` of a conjunction's sides' decisions.
    fn conjunction_decision(&self, v: &ConjView) -> R<Term> {
        let and = self
            .and_dec
            .ok_or_else(|| Stop::Skip("`Decidable.and` isn't loaded yet".into()))?;
        Ok(apps(
            Term::Def(and),
            [
                (v.left.prop.clone(), Icit::Implicit),
                (v.right.prop.clone(), Icit::Implicit),
                (v.left.decision.clone(), Icit::Explicit),
                (v.right.decision.clone(), Icit::Explicit),
            ],
        ))
    }

    fn bool_value(&self, value: bool) -> Term {
        Term::Ctor(
            self.bool,
            if value { self.true_ } else { self.false_ },
            Vec::new(),
        )
    }

    /// `P` and `d`, when `c` is `Decidable.holds [P] d`: a decided
    /// proposition's `Bool` that isn't a comparison's.
    fn decided(&self, c: &Term) -> Option<(Term, Term)> {
        let (head, args) = c.spine();
        match (head.strip_loc(), args.as_slice()) {
            (Term::Def(id), [p, d]) if *id == self.to_bool => Some(((*p).clone(), (*d).clone())),
            _ => None,
        }
    }

    /// `c` as an operand of a conjunction: a decided proposition's `Bool`,
    /// a conjunction, or any other `Bool` `c` as `c = True`.
    fn operand(&self, g: &Ev, c: &Term) -> R<Option<Operand>> {
        if let Some((p, d)) = self.decided(c) {
            return Ok(Some(Operand {
                prop: p,
                decision: d,
            }));
        }
        if let Some(view) = self.conjunction(g, c)? {
            let prop = Term::data(
                self.and_data,
                vec![view.left.prop.clone(), view.right.prop.clone()],
            );
            let decision = self.conjunction_decision(&view)?;
            return Ok(Some(Operand { prop, decision }));
        }
        let Some(dec_true) = self.dec_true else {
            return Ok(None);
        };
        Ok(Some(Operand {
            prop: Term::Eq(
                Some(Rc::new(self.bool_ty())),
                Rc::new(c.clone()),
                Rc::new(self.bool_value(true)),
            ),
            decision: Term::app(Term::Def(dec_true), c.clone()),
        }))
    }

    /// `c` as `a && b` (`if a then b else False`), each side an
    /// [`Operand`].
    fn conjunction(&self, g: &Ev, c: &Term) -> R<Option<ConjView>> {
        if self.and_dec.is_none() || self.to_bool_lemmas.is_none() {
            return Ok(None);
        }
        let (head, args) = spine_icit(c.strip_loc());
        let Term::Def(h) = head.strip_loc() else {
            return Ok(None);
        };
        if *h != self.ite || args.len() != 4 {
            return Ok(None);
        }
        let (Term::Lam(_, _, yes), Term::Lam(_, _, no)) =
            (args[2].0.strip_loc(), args[3].0.strip_loc())
        else {
            return Ok(None);
        };
        let is_false = matches!(no.strip_loc(), Term::Ctor(d, c, a)
            if *d == self.bool && *c == self.false_ && a.is_empty());
        if !is_false || yes.mentions(0) {
            return Ok(None);
        }
        let right = yes.instantiate_var(g, 0)?;
        let (Some(left), Some(right)) = (self.operand(g, &args[1].0)?, self.operand(g, &right)?)
        else {
            return Ok(None);
        };
        Ok(Some(ConjView { left, right }))
    }

    /// What `c` is a decision of, if it is a decided proposition's `Bool`
    /// or a conjunction of two `Bool`s.
    fn decided_view(&self, g: &Ev, c: &Term) -> R<Option<Decided>> {
        if let Some((p, d)) = self.decided(c) {
            return Ok(Some(Decided::One(p, d)));
        }
        Ok(self
            .conjunction(g, c)?
            .map(|view| Decided::Conj(Box::new(view))))
    }

    /// `Q` and its decision, when `p` is `¬Q` decided by `Decidable.not` of
    /// that.
    fn negation(&self, p: &Term, d: &Term) -> Option<(Term, Term)> {
        let (not_not, dec_not) = self.not_not?;
        let _ = not_not;
        let (head, args) = p.spine();
        let Term::Def(h) = head.strip_loc() else {
            return None;
        };
        let [q] = args.as_slice() else {
            return None;
        };
        let (dhead, dargs) = spine_icit(d.strip_loc());
        if *h != self.not || !matches!(dhead.strip_loc(), Term::Def(x) if *x == dec_not) {
            return None;
        }
        let (dq, _) = dargs.last()?;
        Some(((*q).clone(), dq.clone()))
    }

    /// `which` applied to `h`, for the decision `d` of `p`: 0 `d.complete`
    /// (`p` to `holds d = True`), 1 `toBoolOfNot` (`¬p` to `holds d = False`),
    /// 2 `d.sound` (back to `p`), 3 `refute d` (`holds d = False` to `¬p`).
    fn to_bool_lemma(&self, which: usize, p: Term, d: Term, h: Term) -> R<Term> {
        let (decidable, of_not, refute) = self
            .to_bool_lemmas
            .ok_or_else(|| Stop::Skip("`Decidable.refute` isn't loaded yet".into()))?;
        let field = |k| Term::Proj(decidable, k, Rc::new(d.clone()));
        let lemma = |f: DefId| {
            apps(
                Term::Def(f),
                [(p.clone(), Icit::Implicit), (d.clone(), Icit::Explicit)],
            )
        };
        Ok(match which {
            0 => apps(field(2), [(h, Icit::Explicit)]),
            1 => apps(lemma(of_not), [(h, Icit::Explicit)]),
            2 => apps(field(1), [(h, Icit::Explicit)]),
            _ => apps(lemma(refute), [(h, Icit::Explicit)]),
        })
    }

    /// `b` and whether `X` is `True`, when `p` is `b = X` with `X` a
    /// `Bool` constructor.
    fn bool_test(&self, p: &Term) -> Option<(Term, bool)> {
        let Term::Eq(_, b, x) = p.strip_loc() else {
            return None;
        };
        match x.strip_loc() {
            Term::Ctor(d, c, args) if *d == self.bool && args.is_empty() => {
                Some(((**b).clone(), *c == self.true_))
            }
            _ => None,
        }
    }

    /// `Not (b = X)` from the hypothesis `b = notX`, the innermost binder:
    /// `e => apart (J (y _ => y = X) e hyp)`.
    fn refutation_of_other(&self, x: bool) -> Term {
        let target = self.bool_value(x);
        let motive = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "e".into(),
                Icit::Explicit,
                Rc::new(Term::Eq(
                    Some(Rc::new(self.bool_ty())),
                    Rc::new(Term::Var(1)),
                    Rc::new(target),
                )),
            )),
        );
        // Under `e`: `e` is 0, the hypothesis 1. `J` along `b = notX` from
        // `b = X` gives `notX = X`.
        let swapped = Term::J(
            Rc::new(motive),
            Rc::new(Term::Var(0)),
            Rc::new(Term::Var(1)),
        );
        let apart = if x {
            self.false_not_true
        } else {
            self.true_not_false
        };
        Term::Lam(
            "e".into(),
            Icit::Explicit,
            Rc::new(Term::app(Term::Def(apart), swapped)),
        )
    }

    /// `Void.exfalso [goal] void`.
    fn exfalso(&self, goal: Term, void: Term) -> Term {
        apps(
            Term::Def(self.exfalso),
            [(goal, Icit::Implicit), (void, Icit::Explicit)],
        )
    }

    /// `J (y _ => (ite y t e = z) → (ite c t e = z)) (x => x) hyp q`: from
    /// `q: t () = z`, along `hyp: c = True` (`c = False`, `q: e () = z`),
    /// that `ite [a] c t e = z`. `head` is `Bool.ifThenElse`, `args` its
    /// arguments; all at one depth.
    fn ite_step(
        &self,
        g: &Ev,
        head: &Term,
        args: &[(Term, Icit)],
        hyp: Term,
        z: &Term,
        q: Term,
    ) -> R<Term> {
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let pi =
            |dom: Term, cod: Term| Term::Pi("_".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
        let id = lam("x", Term::Var(0));
        let call = |cond: Term, by: usize| -> R<Term> {
            let mut out = head.clone();
            for (i, (a, icit)) in args.iter().enumerate() {
                let a = if i == 1 {
                    cond.clone()
                } else {
                    a.shift(g, by, 0)?
                };
                out = Term::app_icit(out, a, *icit);
            }
            Ok(out)
        };
        let ty = |by: usize| args[0].0.shift(g, by, 0).map(Rc::new);
        let dom = Term::Eq(
            Some(ty(2)?),
            Rc::new(call(Term::Var(1), 2)?),
            Rc::new(z.shift(g, 2, 0)?),
        );
        let cod = Term::Eq(
            Some(ty(3)?),
            Rc::new(call(args[1].0.shift(g, 3, 0)?, 3)?),
            Rc::new(z.shift(g, 3, 0)?),
        );
        let motive = lam("y", lam("e", pi(dom, cod)));
        Ok(Term::app(
            Term::J(Rc::new(motive), Rc::new(id), Rc::new(hyp)),
            q,
        ))
    }

    /// `Void` from `h': b = X` (the innermost binder) and `hyp: b = notX`,
    /// both at the depth of `b` and `hyp`: `X = notX` from `J (y _ => b =
    /// notX → y = notX) (x => x) h' hyp`.
    fn normal_void(&self, g: &Ev, b: Term, x: bool, hyp: Term) -> R<Term> {
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let pi =
            |dom: Term, cod: Term| Term::Pi("_".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
        let id = lam("x", Term::Var(0));
        let other = self.bool_value(!x);
        let dom = Term::Eq(
            Some(Rc::new(self.bool_ty())),
            Rc::new(b.shift(g, 2, 0)?),
            Rc::new(other.clone()),
        );
        let cod = Term::Eq(
            Some(Rc::new(self.bool_ty())),
            Rc::new(Term::Var(2)),
            Rc::new(other),
        );
        let motive = lam("y", lam("e", pi(dom, cod)));
        let swapped = Term::app(
            Term::J(Rc::new(motive), Rc::new(id), Rc::new(Term::Var(0))),
            hyp,
        );
        let apart = if x {
            self.true_not_false
        } else {
            self.false_not_true
        };
        Ok(Term::app(Term::Def(apart), swapped))
    }

    /// `Decidable.elimEq d y n z ey en`, `args` being `Decidable.elim`'s.
    fn elim_eq(&self, args: &[(Term, Icit)], z: Term, ey: Term, en: Term) -> R<Term> {
        let a: Vec<Term> = args.iter().map(|(t, _)| t.clone()).collect();
        let given = [
            a[0].clone(),
            a[1].clone(),
            a[2].clone(),
            a[3].clone(),
            a[4].clone(),
            z,
            ey,
            en,
        ];
        if self.elim_eq_icits.len() != given.len() {
            return skip("`Decidable.elimEq` isn't as stage 1b expects");
        }
        Ok(apps(
            Term::Def(self.elim_eq),
            given.into_iter().zip(self.elim_eq_icits.iter().copied()),
        ))
    }

    /// From `q`, a proof (at `top`) that the branch `yes` of `Decidable.elim
    /// [p] [a] d y n` (`args`) is `z`, with `hyp` its condition (`p`, or
    /// `Not p`, or for `normal`, `b = notX`), that the `elim` is `z`:
    /// `Decidable.elimEq d y n z (h' => …) (r => …)`, `uniq` saying how two
    /// proofs of `p` are equal when the branch uses its proof (all at
    /// `top`).
    #[allow(clippy::too_many_arguments)]
    fn dec_step(
        &self,
        g: &Ev,
        args: &[(Term, Icit)],
        yes: bool,
        uniq: Option<&Uniq>,
        normal: Option<&(Term, bool)>,
        hyp: Term,
        top: usize,
        z: &Term,
        q: Term,
    ) -> R<Term> {
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let a: Vec<Term> = args.iter().map(|(t, _)| t.clone()).collect();
        let (y, n) = (&a[3], &a[4]);
        let result = |by: usize| a[1].shift(g, by, 0).map(|t| Some(Rc::new(t)));
        // Under the one binder of `ey` or `en`.
        // `branch h = z`, the application reduced (the kernel
        // infers an equation's type from its left side).
        let goal_of = |branch: &Term| -> R<Term> {
            let Term::Lam(_, _, body) = branch.strip_loc() else {
                return skip("an `if`'s branch isn't a function as elaborated");
            };
            Ok(Term::Eq(
                result(1)?,
                Rc::new((**body).clone()),
                Rc::new(z.shift(g, 1, 0)?),
            ))
        };
        let (ey, en) = if yes {
            let taken = match uniq {
                None => q.shift(g, 1, 0)?,
                Some(uniq) => {
                    // `J (q e => A[q] = z) q' (unique hyp h')`.
                    let Term::Lam(_, _, body) = y.strip_loc() else {
                        return skip("an `if`'s branch isn't a function as elaborated");
                    };
                    let at = top + 3;
                    let opened = remap(g, body, top + 1, at, &|l| {
                        Some(if l < top {
                            Term::Var(at - 1 - l)
                        } else {
                            Term::Var(1)
                        })
                    })?
                    .ok_or_else(|| Stop::Skip("an `if`'s branch couldn't be read".into()))?;
                    let motive = lam(
                        "q",
                        lam(
                            "e",
                            Term::Eq(result(3)?, Rc::new(opened), Rc::new(z.shift(g, 3, 0)?)),
                        ),
                    );
                    let both = [hyp.shift(g, 1, 0)?, Term::Var(0)];
                    let proof = match uniq {
                        Uniq::Bool(l, r) => apps(
                            Term::Def(self.bool_unique),
                            [
                                (l.shift(g, 1, 0)?, Icit::Explicit),
                                (r.shift(g, 1, 0)?, Icit::Explicit),
                                (both[0].clone(), Icit::Explicit),
                                (both[1].clone(), Icit::Explicit),
                            ],
                        ),
                        Uniq::DecEq(unique, given, icits) => {
                            let mut out = Term::Def(*unique);
                            for (t, icit) in given {
                                out = Term::app_icit(out, t.shift(g, 1, 0)?, *icit);
                            }
                            for (t, icit) in both.iter().zip(icits) {
                                out = Term::app_icit(out, t.clone(), *icit);
                            }
                            out
                        }
                    };
                    Term::J(Rc::new(motive), Rc::new(q.shift(g, 1, 0)?), Rc::new(proof))
                }
            };
            let refuted = Term::app(Term::Var(0), hyp.shift(g, 1, 0)?);
            (
                lam("h", taken),
                lam("r", self.exfalso(goal_of(n)?, refuted)),
            )
        } else {
            // `h'` against the hypothesis: `Not p` applied, or for
            // the other `Bool` equation (D2186), `X = notX`.
            let void = match normal {
                None => Term::app(hyp.shift(g, 1, 0)?, Term::Var(0)),
                Some((b, x)) => self.normal_void(g, b.shift(g, 1, 0)?, *x, hyp.shift(g, 1, 0)?)?,
            };
            (
                lam("h", self.exfalso(goal_of(y)?, void)),
                lam("r", q.shift(g, 1, 0)?),
            )
        };
        self.elim_eq(args, z.clone(), ey, en)
    }

    /// From `q`, a proof (at `top`, the statement's depth) that the tail
    /// below `step` is `z`, a proof that the tail at `step` is.
    fn step_proof(&self, g: &Ev, step: &Step, top: usize, z: &Term, q: Term) -> R<Term> {
        let up = |t: &Term, from: usize, by: usize| t.shift(g, top - from + by, 0);
        let lam = |x: &str, body: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(body));
        let pi =
            |dom: Term, cod: Term| Term::Pi("_".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
        let id = lam("x", Term::Var(0));
        let at_top = |args: &[(Term, Icit)], depth: usize| -> R<Vec<(Term, Icit)>> {
            args.iter()
                .map(|(t, icit)| Ok((up(t, depth, 0)?, *icit)))
                .collect()
        };
        Ok(match step {
            Step::Ite { depth, head, args } => {
                let hyp = Term::Var(top - 1 - depth);
                self.ite_step(g, head, &at_top(args, *depth)?, hyp, z, q)?
            }
            Step::Dec {
                depth,
                args,
                yes,
                uniq,
                normal,
            } => {
                let hyp = Term::Var(top - 1 - depth);
                let uniq = match uniq {
                    None => None,
                    Some(Uniq::Bool(l, r)) => {
                        Some(Uniq::Bool(up(l, *depth, 0)?, up(r, *depth, 0)?))
                    }
                    Some(Uniq::DecEq(unique, given, icits)) => {
                        Some(Uniq::DecEq(*unique, at_top(given, *depth)?, icits.clone()))
                    }
                };
                let normal = match normal {
                    None => None,
                    Some((b, x)) => Some((up(b, *depth, 0)?, *x)),
                };
                self.dec_step(
                    g,
                    &at_top(args, *depth)?,
                    *yes,
                    uniq.as_ref(),
                    normal.as_ref(),
                    hyp,
                    top,
                    z,
                    q,
                )?
            }
            // `J (y q => (h args[y, q] = result) → (h args = result)) (x =>
            // x) hyp proof`, then on to `z` along `q`.
            //
            // On several expressions, `y` is the tuple, taken apart by its
            // projections: `h … (Pair.fst y) (Pair.snd y) …`, which at
            // `(e1, e2)` computes to the call.
            Step::Helper {
                depth,
                after,
                head,
                args,
                cols,
                col_tys,
                eq,
                hyp,
                proof,
                result,
            } => {
                let proof = proof.shift(g, top - after, 0)?;
                // (Every one a catch-all: no hypothesis, no `col_tys`.)
                let parts = if !col_tys.is_empty() {
                    let tys = col_tys
                        .iter()
                        .map(|t| up(t, *depth, 2))
                        .collect::<std::result::Result<Vec<_>, _>>()?;
                    tuple_projections(g, &tys, Term::Var(1))?
                } else {
                    vec![Term::Var(1)]
                };
                let call = |by: usize, swap: bool| -> R<Term> {
                    let mut out = head.clone();
                    for (i, (a, icit)) in args.iter().enumerate() {
                        // Swapped only under `hyp: Some`, where `parts` has
                        // one component for each column.
                        let a = match (swap, cols.iter().position(|c| *c == i), Some(i) == *eq) {
                            (true, Some(k), _) => {
                                debug_assert!(hyp.is_some() && k < parts.len());
                                parts[k].clone()
                            }
                            (true, _, true) => Term::Var(0),
                            _ => up(a, *depth, by)?,
                        };
                        out = Term::app_icit(out, a, *icit);
                    }
                    Ok(out)
                };
                let local = match hyp {
                    None => proof,
                    Some(level) => {
                        let result = result.shift(g, top - after, 0)?;
                        let dom = Term::Eq(
                            None,
                            Rc::new(call(2, true)?),
                            Rc::new(result.shift(g, 2, 0)?),
                        );
                        let cod = Term::Eq(
                            None,
                            Rc::new(call(3, false)?),
                            Rc::new(result.shift(g, 3, 0)?),
                        );
                        let motive = lam("y", lam("e", pi(dom, cod)));
                        Term::app(
                            Term::J(
                                Rc::new(motive),
                                Rc::new(id),
                                Rc::new(Term::Var(top - 1 - level)),
                            ),
                            proof,
                        )
                    }
                };
                if matches!(q, Term::Refl) {
                    local
                } else {
                    let motive = lam(
                        "w",
                        lam(
                            "e",
                            Term::Eq(None, Rc::new(call(2, false)?), Rc::new(Term::Var(1))),
                        ),
                    );
                    Term::J(Rc::new(motive), Rc::new(local), Rc::new(q))
                }
            }
        })
    }
}

/// `Pair` and its constructor, for a `match` on several expressions.
fn tuple_parts(g: &Ev) -> R<(DataId, usize)> {
    g.env
        .registry()
        .ctor(Builtin::MkPair)
        .ok_or_else(|| Stop::Skip("`Pair` isn't loaded yet".into()))
}

/// `(t1, t2, …)`, nesting to the right as a tuple does.
fn tuple(pair: (DataId, usize), ts: &[Term]) -> Term {
    match ts {
        [] => unreachable!("a tuple of no terms"),
        [t] => t.clone(),
        [t, rest @ ..] => Term::ctor(pair.0, pair.1, vec![t.clone(), tuple(pair, rest)]),
    }
}

/// `(T1, T2, …)`: `Pair T1 (Pair T2 …)`.
fn tuple_ty(pair: DataId, ts: &[Term]) -> Term {
    match ts {
        [] => unreachable!("a tuple type of no types"),
        [t] => t.clone(),
        [t, rest @ ..] => Term::Data(
            pair,
            vec![Rc::new(t.clone()), Rc::new(tuple_ty(pair, rest))],
        ),
    }
}

/// The components of `y`, a tuple of these types: `Pair.fst y`,
/// `Pair.fst (Pair.snd y)`, …, the last `Pair.snd (… y)`.
fn tuple_projections(g: &Ev, tys: &[Term], y: Term) -> R<Vec<Term>> {
    let pair = tuple_parts(g)?.0;
    let none = || Stop::Skip("`Pair.fst` isn't loaded yet".into());
    let fst = g.env.registry().def(Builtin::Fst).ok_or_else(none)?;
    let snd = g.env.registry().def(Builtin::Snd).ok_or_else(none)?;
    let project = |f: DefId, i: usize, t: Term| {
        apps(
            Term::Def(f),
            [
                (tys[i].clone(), Icit::Implicit),
                (tuple_ty(pair, &tys[i + 1..]), Icit::Implicit),
                (t, Icit::Explicit),
            ],
        )
    };
    let mut out = Vec::new();
    let mut rest = y;
    for i in 0..tys.len() - 1 {
        out.push(project(fst, i, rest.clone()));
        rest = project(snd, i, rest);
    }
    out.push(rest);
    Ok(out)
}

/// `(x: A) → … → body` over `binders`.
fn pi_over(binders: &[(Name, Icit, Term)], body: Term) -> Term {
    binders.iter().rev().fold(body, |acc, (x, icit, ty)| {
        Term::Pi(x.clone(), *icit, Rc::new(ty.clone()), Rc::new(acc))
    })
}

/// A hypothesis: an earlier row the arm overlaps, as the arm's variables
/// can't be.
enum Hyp {
    /// `notArmJ: (vars) → x = p → … → Void`, or `x ≠ p` with no vars and
    /// one equation. `vars` are levels of the earlier row's shape, with its
    /// types; each equation is a level of this arm's shape and a term in
    /// the earlier row's.
    ///
    /// When the earlier row is guarded, its condition is one more premise:
    /// `(vars) → x = p → … → c = True → Void` (`P` for a proposition).
    Overlap {
        row: usize,
        vars: Vec<usize>,
        eqs: Vec<(usize, Term)>,
        bound: HashMap<usize, Term>,
        guarded: bool,
    },
    /// `notListed: c ∉ [chars]`: the earlier rows (by index), each a
    /// character `c` can't be.
    Listed {
        level: usize,
        rows: Vec<(usize, char)>,
    },
    /// An earlier guarded row that takes every value this one does: its
    /// condition is false here, `c[σ] = False` or `Not P[σ]` (`b = notX`
    /// for `P` of the form `b = X`, D2186), `bound` being `σ`, as in
    /// `Overlap`.
    NotGuard {
        row: usize,
        bound: HashMap<usize, Term>,
    },
    /// The row's own condition, the last hypothesis: `guard: c = True`, or
    /// `guard: P` (`h: P` for `if h: P`).
    Guard,
}

/// Why an equation isn't made: a shape this stage doesn't cover, or an
/// error (which stops the definition's equations).
enum Stop {
    Skip(String),
    Error(Diagnostic),
}

impl From<Diagnostic> for Stop {
    fn from(d: Diagnostic) -> Stop {
        Stop::Error(d)
    }
}

impl From<stitchwort_core::budget::ResourceError> for Stop {
    fn from(e: stitchwort_core::budget::ResourceError) -> Stop {
        Stop::Error(e.into())
    }
}

type R<T> = std::result::Result<T, Stop>;

fn skip<T>(why: impl Into<String>) -> R<T> {
    Err(Stop::Skip(why.into()))
}

/// What kind of definition the equations are for.
#[derive(Clone, Copy)]
pub(crate) enum Kind {
    Plain,
    Opaque,
    /// `decreasing`: its tree is `step`'s, whose parameter `header` is
    /// `%rec`; each leaf is proved by `unfold`.
    Decreasing {
        step: DefId,
        unfold: DefId,
        header: usize,
    },
}

/// The definition, as the generator reads it.
struct Def {
    f: DefId,
    kind: Kind,
    /// Its key and display name.
    key: String,
    display: String,
    /// Its parameters, as many as its body takes.
    binders: Vec<Binder>,
    /// The names the probe binds them by.
    names: Vec<String>,
    /// What each is in the equations if not a variable: an implicit row of
    /// abilities is `Empty`, a divergence `Total`.
    special: Vec<Option<Term>>,
    /// Its case tree, under its parameters (`%step`'s for `decreasing`).
    tree: Rc<Term>,
    /// The leaves recorded for it.
    leaves: Vec<Leaf>,
    rows: Vec<Row>,
    /// The parameters matched (indices into `binders`).
    columns: Vec<usize>,
    /// Whether its rows are a `match`'s alternatives (a lifted `match`'s
    /// helper): the hypotheses for earlier ones are `notAltJ`.
    alt_names: bool,
    /// While `f.induct` is made (`induct.rs`): `%rec` stands for `(y… p =>
    /// f y… p)`, a recursive call keeping its decrease proof as one more
    /// argument, so a branch's right side says the proofs its calls were
    /// made with ([`unmark`] drops them).
    mark_rec: std::cell::Cell<bool>,
}

impl Def {
    /// The number of parameters of the tree (one more than `binders` for
    /// `decreasing`: `%rec`).
    fn tree_params(&self) -> usize {
        match self.kind {
            Kind::Decreasing { .. } => self.binders.len() + 1,
            _ => self.binders.len(),
        }
    }

    /// The tree's parameter at `level`, as the definition's parameter it
    /// stands for (`None` for `%rec`).
    fn param_of_tree_level(&self, level: usize) -> Option<usize> {
        match self.kind {
            Kind::Decreasing { header, .. } => match level.cmp(&header) {
                std::cmp::Ordering::Less => Some(level),
                std::cmp::Ordering::Equal => None,
                std::cmp::Ordering::Greater => Some(level - 1),
            },
            _ => Some(level),
        }
    }

    /// The row a leaf of the tree at `path` belongs to, if it's an arm's:
    /// the innermost, for an alternative of a `match` compiled into the
    /// tree below an arm.
    fn row_at(&self, path: &[u32]) -> Option<usize> {
        let leaf = self
            .leaves
            .iter()
            .filter(|l| l.path == path)
            .find(|l| self.rows.iter().any(|r| contains(r.span, l.span)))?;
        let mut alts = leaf.alternatives.clone();
        alts.sort_by_key(|s| (s.start, s.end));
        alts.dedup();
        let mut best: Option<(usize, u32)> = None;
        for (i, r) in self.rows.iter().enumerate() {
            if contains(r.span, leaf.span) && r.alternatives == alts {
                let size = r.span.end - r.span.start;
                if best.is_none_or(|(_, s)| size < s) {
                    best = Some((i, size));
                }
            }
        }
        best.map(|(i, _)| i)
    }

    /// The guarded row whose condition is tested at `path`, if one is:
    /// its leaf is the `then` below it.
    fn guard_row_at(&self, path: &mut Vec<u32>) -> Option<usize> {
        path.push(crate::GUARD_THEN);
        let row = self.row_at(path);
        path.pop();
        row.filter(|&r| self.rows[r].guarded)
    }

    /// Row `j` in a message, and what it is: `arm 2`, `alternative 1`.
    fn row_said(&self, j: usize) -> (String, &'static str) {
        let r = &self.rows[j];
        if r.parent.is_some() {
            (format!("alternative {}", r.alt), "alternative")
        } else if self.alt_names {
            (format!("alternative {}", r.arm), "alternative")
        } else {
            (format!("arm {}", r.arm), "arm")
        }
    }

    /// Whether row `a` is `k` or one it is an alternative below.
    fn is_ancestor(&self, a: usize, k: usize) -> bool {
        let mut at = Some(k);
        while let Some(r) = at {
            if r == a {
                return true;
            }
            at = self.rows[r].parent;
        }
        false
    }

    /// The rows that come before row `k`, in the order the definition tries
    /// them: the earlier arms, and for `k` and each row it is below, the
    /// earlier alternatives of its `match`.
    fn earlier(&self, k: usize) -> Vec<usize> {
        let mut out = Vec::new();
        let mut at = k;
        loop {
            let parent = self.rows[at].parent;
            for (j, r) in self.rows.iter().enumerate().take(at) {
                if r.parent == parent {
                    out.push(j);
                }
            }
            match parent {
                Some(p) => at = p,
                None => break,
            }
        }
        out.sort_unstable();
        out
    }
}

fn contains(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.start <= inner.start && inner.end <= outer.end
}

// ----------------------------------------------------------- the generator

impl Elaborator {
    /// The equations of a `decreasing` definition `f`, just admitted: its
    /// tree is its `f.%step`'s, and each leaf is proved by `f.unfold`.
    pub(crate) fn decreasing_equations(
        &mut self,
        f: DefId,
        signature: &Decl,
        equations: &[Decl],
        key: Option<&str>,
    ) -> Result<()> {
        let Decl::Signature { name, theorem, .. } = signature else {
            return Ok(());
        };
        if *theorem {
            return self.generate_equations_keyed(f, signature, equations, Kind::Plain, key);
        }
        let key = match key {
            Some(k) => k.to_string(),
            None => self.declaration_key(name)?,
        };
        let Some(unfold) = self.lookup_def(&format!("{key}.unfold")) else {
            return Ok(());
        };
        let g = &self.ev();
        let generated = |suffix: &str| {
            let name = format!("{}.{suffix}", crate::scope::display(&key));
            (0..g.env.defs().len())
                .rev()
                .map(DefId)
                .find(|id| &**g.def(*id).name() == name.as_str())
        };
        let Some(step) = generated("%step") else {
            return Ok(());
        };
        // Where `f.unfold` shows plain `if`s (`decreasing/plain.rs`), the
        // equation about `f.%step`'s own tree is `f.%unfoldStep`.
        let unfold = generated("%unfoldStep")
            .filter(|u| *u > step)
            .unwrap_or(unfold);
        let (tel, _) = split_pis(g.def(step).ty(), None);
        let Some(header) = tel.iter().position(|b| &*b.name == crate::decreasing::REC) else {
            return Ok(());
        };
        self.generate_equations_keyed(
            f,
            signature,
            equations,
            Kind::Decreasing {
                step,
                unfold,
                header,
            },
            Some(&key),
        )
    }

    /// The equations of definition `f` (final), whose signature and
    /// equations are given: each generated, or recorded as skipped with the
    /// reason. Errors only for running out of resources.
    pub(crate) fn generate_equations(
        &mut self,
        f: DefId,
        signature: &Decl,
        equations: &[Decl],
        kind: Kind,
    ) -> Result<()> {
        self.generate_equations_keyed(f, signature, equations, kind, None)
    }

    /// [`Self::generate_equations`], for a definition by its key (a local
    /// one, or one made on demand outside its own module).
    fn generate_equations_keyed(
        &mut self,
        f: DefId,
        signature: &Decl,
        equations: &[Decl],
        kind: Kind,
        local_key: Option<&str>,
    ) -> Result<()> {
        let Decl::Signature {
            name: def_name,
            theorem,
            instance,
            unfolding,
            ..
        } = signature
        else {
            return Ok(());
        };
        let Some((form, scrutinees, arms)) = source_arms(equations) else {
            return Ok(());
        };
        let key = match local_key {
            Some(k) => k.to_string(),
            None => self.declaration_key(def_name)?,
        };
        let suffixes = source_suffixes(equations);
        let why_none = if *theorem {
            Some("a theorem's arms have no equations: nothing unfolds a proof")
        } else if *instance {
            Some(
                "an instance's arms have no equations: write the method as a named `def` the \
                 instance points to, which gets them",
            )
        } else if !unfolding.is_empty() || !self.kernel.def(f).unfolding().is_empty() {
            Some(
                "an `opaque` definition with an `unfolding` clause has no equations, as it has no `unfold`",
            )
        } else {
            None
        };
        if let Some(why) = why_none {
            // A theorem's and an instance's are said by `no_equation` from
            // the definition itself.
            if !*theorem && !*instance {
                for s in &suffixes {
                    self.tables
                        .equation_skips
                        .push((f, s.clone(), why.to_string()));
                }
                induct::no_equations(self, f, kind, why);
            }
            return Ok(());
        }
        let def = self.kernel.def(f);
        if def.state() != stitchwort_core::globals::State::Final {
            return Ok(());
        }
        let (arity, def_ty) = (def.arity(), def.ty().clone());
        let mut rows = Vec::new();
        let body_form = matches!(form, Form::Body);
        for (k, arm) in arms.iter().enumerate() {
            let combos = expand_or(&arm.patterns);
            let or = arm.patterns.iter().any(has_or);
            for (m, (patterns, alternatives)) in combos.into_iter().enumerate() {
                let or = or.then_some(m + 1);
                let suffix = match (body_form, or) {
                    (true, _) => "eq".to_string(),
                    (false, Some(m)) => format!("eq{}.or{m}", k + 1),
                    (false, None) => format!("eq{}", k + 1),
                };
                rows.push(Row {
                    arm: if body_form { 0 } else { k + 1 },
                    or,
                    patterns,
                    alternatives,
                    span: arm.span,
                    has_rhs: arm.rhs.is_some(),
                    guarded: arm.guard.is_some(),
                    guard: arm.guard.clone(),
                    suffix,
                    rhs: arm.rhs.clone(),
                    parent: None,
                    alt: 0,
                    chain: Vec::new(),
                });
            }
        }
        let display = crate::scope::display(&key).to_string();
        let skip_all = |e: &mut Elaborator, why: &str| {
            for s in &suffixes {
                e.tables
                    .equation_skips
                    .push((f, s.clone(), why.to_string()));
            }
            induct::no_equations(e, f, kind, why);
        };
        let (tree_def, tree_lams) = match kind {
            Kind::Decreasing { step, header, .. } => (step, Some(header)),
            _ => (f, None),
        };
        let (binders, _) = split_pis(&def_ty, Some(arity));
        if binders.len() != arity {
            skip_all(
                self,
                "its type doesn't show all the parameters its body takes",
            );
            return Ok(());
        }
        let Some(body) = self.kernel.def(tree_def).body().cloned() else {
            skip_all(self, "its body isn't available");
            return Ok(());
        };
        let body = match plain_ifs(&self.ev(), &body) {
            Ok(body) => Rc::new(body),
            Err(Stop::Skip(why)) => {
                skip_all(self, &why);
                return Ok(());
            }
            Err(Stop::Error(e)) => return Err(e),
        };
        let tree_params = arity + usize::from(tree_lams.is_some());
        if self.kernel.def(tree_def).arity() != tree_params {
            skip_all(
                self,
                "its body returns a function, so its arms aren't a case tree",
            );
            return Ok(());
        }
        let special = special_params(&self.ev(), &binders);
        if performs_abilities(&self.ev(), &def_ty, &special)? {
            skip_all(
                self,
                "it performs abilities (or is polymorphic in them): its arms are computations, \
                 not stated by equations in stage 1a",
            );
            return Ok(());
        }
        let tree = Term::peel_lams_rc(&body, tree_params);
        let names = probe_names(&binders);
        let columns: Vec<usize> = match form {
            // The last explicit parameters: a local definition's captures
            // come before its own.
            Form::Arms => {
                let explicit: Vec<usize> = (0..arity)
                    .filter(|&i| binders[i].icit == Icit::Explicit)
                    .collect();
                let p = rows.first().map_or(0, |r| r.patterns.len());
                if p > explicit.len() {
                    skip_all(self, "its arms' patterns don't line up with its parameters");
                    return Ok(());
                }
                explicit[explicit.len() - p..].to_vec()
            }
            Form::WholeMatch => {
                let mut cols = Vec::new();
                for s in &scrutinees {
                    match names.iter().rposition(|n| n == s) {
                        Some(i) => cols.push(i),
                        None => {
                            return Ok(());
                        }
                    }
                }
                cols
            }
            Form::Body => Vec::new(),
        };
        if let Some(first) = rows.first()
            && first.patterns.len() != columns.len()
        {
            skip_all(self, "its arms' patterns don't line up with its parameters");
            return Ok(());
        }
        let leaves: Vec<Leaf> = self
            .decl
            .leaf_log
            .borrow()
            .leaves
            .iter()
            .filter(|l| l.root == def_name.span)
            .cloned()
            .collect();
        let mut d = Def {
            f,
            kind,
            key: key.clone(),
            display,
            binders,
            names,
            special,
            tree,
            leaves,
            rows,
            columns,
            alt_names: false,
            mark_rec: std::cell::Cell::new(false),
        };
        if body_form {
            // A `:=` body is one leaf, the whole tree.
            if d.special.iter().any(Option::is_some) {
                skip_all(
                    self,
                    "an effect-polymorphic definition's `:=` body isn't stated at the empty row \
                     in stage 1b",
                );
                return Ok(());
            }
            d.leaves = vec![Leaf {
                root: def_name.span,
                path: Vec::new(),
                span: d.rows[0].span,
                alternatives: Vec::new(),
            }];
        }
        // Made on demand, after the definition: its leaves weren't
        // recorded, so its arms are compiled again.
        if d.leaves.is_empty() {
            let why = match self.recompute_leaves(&d, &arms, def_name.span) {
                Ok(Some(leaves)) => {
                    d.leaves = leaves;
                    None
                }
                Ok(None) => Some("its arms couldn't be compiled again as a `match`".to_string()),
                Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
                Err(Stop::Error(e)) => Some(format!(
                    "its arms couldn't be compiled again: {}",
                    e.message
                )),
                Err(Stop::Skip(why)) => Some(why),
            };
            if let Some(why) = why {
                skip_all(self, &why);
                return Ok(());
            }
        }
        self.equations_of(&mut d, def_name.span)?;
        // Every name the source implies is made or recorded as skipped: one
        // whose split the elaborated definition doesn't show is said here.
        for s in &suffixes {
            let made = self.scope.get(&format!("{key}.{s}")).is_some();
            let said = (self.tables.equation_skips.iter()).any(|(g, t, _)| *g == f && t == s);
            if !made && !said {
                self.tables.equation_skips.push((
                    f,
                    s.clone(),
                    "its branch couldn't be followed in the elaborated definition".to_string(),
                ));
            }
        }
        Ok(())
    }

    fn equations_of(&mut self, d: &mut Def, span: Span) -> Result<()> {
        // Each row's shape, from the probe, and what its leaf is. A row
        // whose right side is a `match` on its variables, compiled into
        // the case tree, has rows below it, one for each alternative.
        let mut shapes: Vec<std::result::Result<Shape, String>> = Vec::new();
        let mut leaves: Vec<Option<Found>> = Vec::new();
        // Why a row's alternatives aren't rows of their own.
        let mut unfollowed: Vec<Option<String>> = Vec::new();
        let mut i = 0;
        while i < d.rows.len() {
            let row = &d.rows[i];
            let shape = if !row.has_rhs {
                Err("an arm with `()` has no right side".to_string())
            } else {
                match self.attempt(|e| e.probe_row(d, i, row, span)) {
                    Ok(s) => Ok(s),
                    Err(Stop::Skip(why)) => Err(why),
                    Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
                    Err(Stop::Error(e)) => {
                        Err(format!("its patterns couldn't be read: {}", e.message))
                    }
                }
            };
            let found = match &shape {
                Ok(s) => match self.attempt(|e| e.leaf_found(d, i, s)) {
                    Ok(f) => Some(f),
                    Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
                    Err(_) => None,
                },
                Err(_) => None,
            };
            let mut why_not = None;
            if matches!(found, Some(Found::Match)) {
                match alternative_rows(&d.rows[i], i) {
                    Ok(new) => d.rows.extend(new),
                    Err(why) => why_not = Some(why.to_string()),
                }
            }
            shapes.push(shape);
            leaves.push(found);
            unfollowed.push(why_not);
            i += 1;
        }
        // The lifted `match`es' helpers met so far, with their equations.
        let mut helpers: HashMap<DefId, Rc<Helper>> = HashMap::default();
        for k in 0..d.rows.len() {
            let row = &d.rows[k];
            let paths = row.rhs.as_ref().map(branch_paths).unwrap_or_default();
            // The row's own equation: an arm's (stage 1a), or an
            // alternative's with nothing below it.
            let own = if row.parent.is_some() {
                paths.is_empty() && !matches!(leaves[k], Some(Found::Match))
            } else {
                row.arm != 0
            };
            if own {
                let skipped = self.tables.equation_skips.len();
                let cache = &mut helpers;
                self.one_equation(d, k, row.suffix(), &shapes, |e, d, shape, shapes| {
                    e.equation(d, k, shape, shapes, span, cache)
                })?;
                if self.tables.equation_skips.len() != skipped {
                    helpers.clear();
                }
            }
            if matches!(leaves[k], Some(Found::Match)) {
                if let Some(why) = &unfollowed[k] {
                    for path in &paths {
                        let s = format!("{}.{}", row.suffix, path_suffix(path));
                        self.tables.equation_skips.push((d.f, s, why.clone()));
                    }
                }
                continue;
            }
            for path in &paths {
                let suffix = format!("{}.{}", row.suffix, path_suffix(path));
                let skipped = self.tables.equation_skips.len();
                let cache = &mut helpers;
                self.one_equation(d, k, suffix.clone(), &shapes, |e, d, shape, shapes| {
                    e.branch_equation(d, k, shape, shapes, path, &suffix, cache, span)
                })?;
                // A failed attempt is undone, hidden lemmas it declared
                // included: the helpers' are made again when next needed.
                if self.tables.equation_skips.len() != skipped {
                    helpers.clear();
                }
            }
        }
        // `f.induct`, for a recursive definition (stage 2a).
        self.function_induct(d, &shapes, &leaves, &mut helpers)
    }

    /// Makes one equation of row `k` named `suffix` with `make`, or records
    /// why not.
    fn one_equation(
        &mut self,
        d: &Def,
        k: usize,
        suffix: String,
        shapes: &[std::result::Result<Shape, String>],
        make: impl FnOnce(&mut Self, &Def, &Shape, &[std::result::Result<Shape, String>]) -> R<()>,
    ) -> Result<()> {
        let name = (d.f, suffix);
        if self.scope.get(&format!("{}.{}", d.key, name.1)).is_some() {
            // Reserved names are refused where they're declared; a clash
            // here is one declared before the definition.
            self.tables.equation_skips.push((
                name.0,
                name.1,
                "the name is already declared".to_string(),
            ));
            return Ok(());
        }
        let shape = match &shapes[k] {
            Ok(s) => s,
            Err(why) => {
                self.tables
                    .equation_skips
                    .push((name.0, name.1, why.clone()));
                return Ok(());
            }
        };
        let mark = self.kernel.mark();
        match self.attempt(|e| make(e, d, shape, shapes)) {
            Ok(()) => {}
            Err(Stop::Skip(why)) => {
                self.rewind_globals(&mark);
                self.tables.equation_skips.push((name.0, name.1, why));
            }
            Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
            Err(Stop::Error(e)) => {
                self.rewind_globals(&mark);
                self.tables.equation_skips.push((
                    name.0,
                    name.1,
                    format!(
                        "the kernel refused the generated proof ({}: {})",
                        e.code, e.message
                    ),
                ));
            }
        }
        Ok(())
    }

    /// `f`, with a step, size and frame budget of its own ([`ATTEMPT`]):
    /// running out of it skips the equation, with the reason, instead of
    /// failing the definition. An equation whose `rfl` the kernel can only
    /// check by computing far (a body that calls a definition on a known
    /// number, `digits 40 (k + n) 0`, compared without sharing) would
    /// otherwise take the time and memory of that computation.
    fn attempt<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let limits = stitchwort_core::budget::Limits {
            work: ATTEMPT.work,
            size: ATTEMPT.size,
            frames: ATTEMPT.frames,
            ..self.options.limits
        };
        let saved = self.kernel.machine.budget.start_attempt(limits);
        let result = f(self);
        self.kernel.machine.budget.restore(saved);
        match result {
            Err(Stop::Error(e))
                if e.code == "E-RESOURCE" && self.kernel.machine.budget.exhausted().is_none() =>
            {
                Err(Stop::Skip(
                    "checking it takes more than the generator allows for one equation (its \
                     proof computes too far)"
                        .to_string(),
                ))
            }
            other => other,
        }
    }

    /// Whether `row`'s guard names its proof (`if h: P`).
    fn guard_named(&self, row: &Row) -> bool {
        row.guard.as_ref().is_some_and(|g| g.binder.is_some())
    }

    /// `p` (at `depth`) as the equation `b = X` of a `Bool` and a `Bool`
    /// constructor that it computes to, if it does: `<` and `<=` on `Nat`
    /// and `Int` are such.
    fn bool_equation(&self, p: &Term, depth: usize) -> R<Option<Term>> {
        let g = &self.ev();
        let lib = self.branch_lib()?;
        let env: Vec<Value> = (0..depth).map(Value::var).collect();
        let Value::Eq(ty, l, r) = force(g, eval(g, &env, p)?)? else {
            return Ok(None);
        };
        if !matches!(force(g, (*ty).clone())?, Value::Data(b, _) if b == lib.bool) {
            return Ok(None);
        }
        let l = stitchwort_core::value::quote_folded(g, depth, &l)?;
        let r = stitchwort_core::value::quote(g, depth, &r)?;
        let eq = Term::Eq(Some(Rc::new(lib.bool_ty())), Rc::new(l), Rc::new(r));
        Ok(lib.bool_test(&eq).map(|_| eq))
    }

    /// The shape of `row` (row `k`, or one refined below it): compiles its
    /// patterns alone, as a `match` on the definition's parameters, and
    /// probes its body; for a guarded row, reads its condition off the
    /// definition's tree.
    fn probe_row(&mut self, d: &Def, k: usize, row: &Row, span: Span) -> R<Shape> {
        if d.columns.is_empty() && row.chain.is_empty() {
            return self.body_shape(d);
        }
        let drafts = self.attempt.drafts.borrow().len();
        let shape = self.probe_row_in(d, row, span);
        // A `match` below the arm is compiled into the tree, as it was in
        // the definition; were one lifted instead, its helper is dropped.
        if self.attempt.drafts.borrow().len() != drafts {
            self.attempt.drafts.borrow_mut().truncate(drafts);
            return skip("its `match`es couldn't be compiled again as the definition's were");
        }
        let (mut shape, condition) = shape?;
        if let Some((prop, as_bool)) = condition {
            // `(x => 2 < x) (f n)` is the condition `2 < f n`.
            let g = &self.ev();
            let prop = beta_rec(g, prop)?;
            let as_bool = as_bool.map(|c| beta_rec(g, c)).transpose()?;
            let dec = self.guard_form(d, k, &shape)?;
            // A comparison is stated as the `Bool` equation it is, whichever
            // `if` the definition tests it by; `if h: P` is the proposition
            // the programmer wrote.
            let unfolded = if dec && !self.guard_named(row) {
                self.bool_equation(&prop, shape.depth)?
            } else {
                None
            };
            let cond = if let Some(eq) = &unfolded {
                Some(eq.clone())
            } else if dec {
                Some(prop.clone())
            } else {
                as_bool
            };
            let cond = cond.ok_or_else(|| {
                Stop::Skip("its condition `if h: P` is tested as a `Bool`".into())
            })?;
            let blib = self.branch_lib()?;
            // `a == b` too is a `Bool` condition whose `Bool` is a decision's.
            let prop = if !dec && blib.to_bool_lemmas.is_some() {
                blib.decided_view(&self.ev(), &cond)?
                    .map(|view| view.prop(&blib))
            } else {
                None
            };
            let negated = match (&prop, blib.decided_view(&self.ev(), &cond)?) {
                (Some(_), Some(Decided::One(p, d))) => blib.negation(&p, &d).map(|(q, _)| q),
                _ => None,
            };
            shape.guard = Some(GuardRead {
                dec,
                cond,
                prop,
                unfolded: unfolded.is_some(),
                negated,
            });
        }
        Ok(shape)
    }

    /// The shape of a [`Form::Body`]'s one row: the parameters themselves.
    fn body_shape(&self, d: &Def) -> R<Shape> {
        let g = &self.ev();
        let n = d.binders.len();
        let depth = n + 1;
        let lhs: Vec<Term> = (0..n).map(|i| Term::Var(n - 1 - i)).collect();
        let tele: Vec<usize> = (1..=n).collect();
        let mut names: Vec<Name> = Vec::new();
        let mut unnamed = 0;
        for b in &d.binders {
            let base = b.name.to_string();
            let base = if base.is_empty() || base == "_" || base.starts_with('%') {
                unnamed += 1;
                format!("x{unnamed}")
            } else {
                base
            };
            names.push(fresh(&names, &base).into());
        }
        let mut types = Vec::new();
        for (i, b) in d.binders.iter().enumerate() {
            let ty = remap(g, &b.ty, i, depth, &|l| Some(Term::Var(n - 1 - l)))?
                .ok_or_else(|| Stop::Skip("a parameter's type couldn't be read".into()))?;
            types.push(ty);
        }
        Ok(Shape {
            depth,
            lhs,
            tele,
            names,
            icits: d.binders.iter().map(|b| b.icit).collect(),
            types,
            guard: None,
        })
    }

    /// [`Self::probe_row`]'s shape, and for a guarded row its condition
    /// elaborated in the arm's context ([`guard_condition`]).
    #[allow(clippy::type_complexity)]
    fn probe_row_in(
        &mut self,
        d: &Def,
        row: &Row,
        span: Span,
    ) -> R<(Shape, Option<(Term, Option<Term>)>)> {
        let n = d.binders.len();
        // The predicate `%P: (params) → Prop` the goal applies to the
        // parameters, so the goal at the leaf shows what they are there.
        let pred_ty = pis(&d.binders, Term::Sort(Sort::Prop));
        let pred_ty = eval(&self.ev(), &[], &pred_ty)?;
        let probe_span = Span {
            file: span.file,
            start: span.start,
            end: span.start,
        };
        let other_span = Span {
            file: span.file,
            start: span.end,
            end: span.end,
        };
        let nav = self.present.nav.take();
        let lambda_warnings = self.attempt.lambda_warnings.borrow().len();
        let branch_errors = self.attempt.branch_errors.borrow().len();
        *self.decl.arm_probe.borrow_mut() = ProbeState {
            wanted: Some(probe_span),
            found: None,
        };
        let result = (|| -> Result<Option<()>> {
            let mut cx = Ctx::new(self, span);
            cx.bind_hidden("%P".into(), pred_ty.clone());
            for (i, b) in d.binders.iter().enumerate() {
                let ty = eval(&cx.g(), &cx.env[1..], &b.ty)?;
                if let Some(value) = &d.special[i] {
                    let ty_term = cx.quote(&ty)?;
                    cx.define(
                        Some(&d.names[i]),
                        b.name.clone(),
                        ty,
                        ty_term,
                        value.clone(),
                    )?;
                } else {
                    cx.bind(&d.names[i], ty);
                }
                cx.set_kind(b.icit);
            }
            let goal_term = apps(
                Term::Var(n),
                (0..n).map(|i| (Term::Var(n - 1 - i), d.binders[i].icit)),
            );
            let goal = cx.eval(&goal_term)?;
            let var = |text: &str, span: Span| {
                Expr::Var(ast::Name {
                    text: text.into(),
                    span,
                })
            };
            // Below an arm, its `match`es down to the row's alternative.
            let mut body = var(PROBE, probe_span);
            for (scrutinees, patterns) in row.chain.iter().rev() {
                body = Expr::Match {
                    scrutinees: scrutinees.clone(),
                    alts: vec![
                        Alt {
                            guard: None,
                            patterns: patterns.clone(),
                            body: Some(body),
                            span: probe_span,
                        },
                        Alt {
                            guard: None,
                            patterns: scrutinees
                                .iter()
                                .map(|_| Pattern::Wildcard(other_span))
                                .collect(),
                            body: Some(var(PROBE, other_span)),
                            span: other_span,
                        },
                    ],
                    span,
                    kind: MatchKind::Match,
                };
            }
            let expr = Expr::Match {
                scrutinees: d
                    .columns
                    .iter()
                    .map(|&i| Scrutinee {
                        name: None,
                        expr: var(&d.names[i], span),
                    })
                    .collect(),
                alts: vec![
                    Alt {
                        guard: None,
                        patterns: row.patterns.clone(),
                        body: Some(body),
                        span: probe_span,
                    },
                    Alt {
                        guard: None,
                        patterns: d
                            .columns
                            .iter()
                            .map(|_| Pattern::Wildcard(other_span))
                            .collect(),
                        body: Some(var(PROBE, other_span)),
                        span: other_span,
                    },
                ],
                span,
                kind: MatchKind::Match,
            };
            match crate::matching::in_tree(&mut cx, &expr, &goal) {
                None => Ok(None),
                Some(r) => r.map(|_| Some(())),
            }
        })();
        self.present.nav = nav;
        self.attempt
            .lambda_warnings
            .borrow_mut()
            .truncate(lambda_warnings);
        self.attempt
            .branch_errors
            .borrow_mut()
            .truncate(branch_errors);
        let found = std::mem::take(&mut *self.decl.arm_probe.borrow_mut()).found;
        self.clear_metas();
        match result {
            Ok(Some(())) => {}
            Ok(None) => return skip("its patterns aren't a match on its parameters"),
            Err(e) => return Err(Stop::Error(e)),
        }
        let Some(Probed { saved, goal }) = found else {
            return skip("its arm is never reached");
        };
        let cx = saved.ctx(self);
        let g = &self.ev();
        let depth = cx.level();
        let Value::Neutral(Head::Var(0, _), spine) = force(g, goal)? else {
            return skip("its arm's goal wasn't the probe's");
        };
        let mut lhs = Vec::new();
        for elim in spine.iter() {
            match elim {
                Elim::App(v, _) => lhs.push(stitchwort_core::value::quote(g, depth, v)?),
                _ => return skip("its arm's goal wasn't the probe's"),
            }
        }
        if lhs.len() != n {
            return skip("its arm's goal wasn't the probe's");
        }
        let own = |l: usize| {
            cx.lets[l].is_none()
                && matches!(&cx.env[l], Value::Neutral(Head::Var(x, _), s) if *x == l && s.is_empty())
        };
        // A character pattern's proof field (`'k'` is `MkChar 107 p`) is
        // `rfl` on the left side, the literal's own, so the equation doesn't
        // take it as a variable. Only where every argument stays convertible
        // with itself when `p` becomes `rfl` (the kernel skips the proof
        // field); a bare `p`, or one that a call computes on, stays a
        // variable, as the equation would be narrower at `rfl`.
        let mut to_refl: Vec<Value> = (0..depth).map(Value::var).collect();
        let mut any_refl = false;
        for l in 1..depth {
            if !own(l) || !is_computed_bool_eq(g, depth, &cx.types[l])? {
                continue;
            }
            let mut one: Vec<Value> = (0..depth).map(Value::var).collect();
            one[l] = Value::Refl;
            let mut same = true;
            for t in &lhs {
                let (x, y) = (eval(g, &to_refl, t)?, eval(g, &one, t)?);
                if !stitchwort_core::value::conv(g, depth, &x, &y)? {
                    same = false;
                    break;
                }
            }
            if same {
                to_refl[l] = Value::Refl;
                any_refl = true;
            }
        }
        if any_refl {
            for t in &mut lhs {
                *t = stitchwort_core::value::quote(g, depth, &eval(g, &to_refl, t)?)?;
            }
        }
        let mut types: HashMap<usize, Term> = HashMap::default();
        for l in 1..depth {
            if own(l) {
                types.insert(l, stitchwort_core::value::quote(g, depth, &cx.types[l])?);
            }
        }
        // The variables the equation takes: those its arguments mention,
        // and those their types do.
        let mut wanted: Vec<usize> = Vec::new();
        let mut pending: Vec<usize> = lhs.iter().flat_map(|t| levels_in(t, depth)).collect();
        while let Some(l) = pending.pop() {
            if wanted.contains(&l) {
                continue;
            }
            if l == 0 || !own(l) {
                return skip("its left side mentions something other than its variables");
            }
            wanted.push(l);
            pending.extend(levels_in(&types[&l], depth));
        }
        // In order: the parameters the arms don't match (implicit ones, the
        // header's), then the arm's variables as written, with each `_`
        // (no name to find it by) placed among them by where it stands on
        // the left side, or last when it isn't there. Each comes after
        // the variables its type mentions.
        let all_patterns = row.written();
        let written: Vec<usize> = crate::written_names(&all_patterns)
            .into_iter()
            .filter_map(|x| cx.lookup(x))
            .collect();
        let rank = |l: usize| -> (usize, usize) {
            if l <= n && !d.columns.contains(&(l - 1)) {
                (0, l)
            } else if let Some(i) = written.iter().position(|&w| w == l) {
                (1, i)
            } else {
                (2, l)
            }
        };
        wanted.sort_by_key(|&l| rank(l));
        if let Some(at) = wanted.iter().position(|&l| rank(l).0 == 2) {
            // Where each variable first appears on the left side, which is
            // where its pattern is.
            let mut seen: Vec<usize> = Vec::new();
            for t in &lhs {
                for l in levels_in(t, depth) {
                    if !seen.contains(&l) {
                        seen.push(l);
                    }
                }
            }
            let at_lhs = |l: usize| seen.iter().position(|&m| m == l);
            for b in wanted.split_off(at) {
                let to = at_lhs(b)
                    .and_then(|pb| {
                        wanted
                            .iter()
                            .position(|&l| rank(l).0 == 1 && at_lhs(l).is_some_and(|p| p > pb))
                    })
                    .unwrap_or(wanted.len());
                wanted.insert(to, b);
            }
        }
        let mut tele: Vec<usize> = Vec::new();
        while tele.len() < wanted.len() {
            let next = wanted
                .iter()
                .copied()
                .find(|l| {
                    !tele.contains(l)
                        && levels_in(&types[l], depth)
                            .iter()
                            .all(|m| m == l || tele.contains(m))
                })
                .ok_or_else(|| {
                    Stop::Skip("its variables' types depend on each other in a cycle".into())
                })?;
            tele.push(next);
        }
        let mut names: Vec<Name> = Vec::new();
        let mut icits = Vec::new();
        // `x1`, `x2`, … for those with no name to take (§3.1).
        let mut unnamed = 0;
        for &l in &tele {
            let base = if (1..=n).contains(&l) {
                let given = d.binders[l - 1].name.to_string();
                match cx.name_of_level(l) {
                    Some(x) if !x.starts_with('%') => x.to_string(),
                    _ => given,
                }
            } else {
                cx.name_of_level(l)
                    .map(str::to_string)
                    .unwrap_or_else(|| cx.names[l].trim_end_matches('✝').to_string())
            };
            let base = if base.is_empty() || base == "_" || base.starts_with('%') {
                unnamed += 1;
                format!("x{unnamed}")
            } else {
                base
            };
            names.push(fresh(&names, &base).into());
            icits.push(if (1..=n).contains(&l) {
                d.binders[l - 1].icit
            } else {
                Icit::Explicit
            });
        }
        let pure = d.special.iter().any(Option::is_some);
        let types = tele
            .iter()
            .map(|l| {
                if pure {
                    pure_at_empty(g, &types[l], depth)
                } else {
                    Ok(types[l].clone())
                }
            })
            .collect::<stitchwort_core::budget::Result<_>>()?;
        let shape = Shape {
            depth,
            lhs,
            tele,
            names,
            icits,
            types,
            guard: None,
        };
        let Some(guard) = &row.guard else {
            return Ok((shape, None));
        };
        // The condition, elaborated in the arm's context as the
        // definition's was in each case of its tree.
        let nav = self.present.nav.take();
        let lambda_warnings = self.attempt.lambda_warnings.borrow().len();
        let branch_errors = self.attempt.branch_errors.borrow().len();
        let mut cx = saved.ctx(self);
        let condition = guard_condition(&mut cx, guard);
        drop(cx);
        self.present.nav = nav;
        self.attempt
            .lambda_warnings
            .borrow_mut()
            .truncate(lambda_warnings);
        self.attempt
            .branch_errors
            .borrow_mut()
            .truncate(branch_errors);
        self.clear_metas();
        // A condition that needs an earlier guarded arm's failed condition
        // (`| n if h: n = 0 => … | n if 10 % n > 2 => …`) can't be
        // elaborated outside the definition's tree, where that fact is in
        // scope.
        let earlier = d
            .rows
            .iter()
            .enumerate()
            .rfind(|(_, r)| r.guarded && r.arm < row.arm)
            .map(|(j, _)| d.row_said(j).0);
        let reason = |why: Option<String>| {
            let again = "couldn't be elaborated again in its arm's variables";
            match (&earlier, why) {
                (Some(arm), why) => format!(
                    "its condition {again}: it may depend on {arm}'s condition having failed, \
                     which is known in the definition's tree and not here{}",
                    why.map_or(String::new(), |w| format!(" ({w})"))
                ),
                (None, Some(w)) => format!("its condition {again}: {w}"),
                (None, None) => format!("its condition {again}"),
            }
        };
        match condition {
            Ok(Some(c)) => Ok((shape, Some(c))),
            Ok(None) => skip(reason(None)),
            Err(e) if crate::undo::fatal(&e) => Err(Stop::Error(e)),
            Err(e) => skip(reason(Some(e.message))),
        }
    }

    /// Generates row `k`'s equation (or says why it can't).
    fn equation(
        &mut self,
        d: &Def,
        k: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
        span: Span,
        helpers: &mut HashMap<DefId, Rc<Helper>>,
    ) -> R<()> {
        let s = self.stated(d, k, shape, shapes)?;
        let Some(rhs) = &s.rhs else {
            // Its leaves' bodies differ (SW-1071): read each, as a branch
            // with no splits is.
            let suffix = d.rows[k].suffix();
            return self.branch_equation(d, k, shape, shapes, &[], &suffix, helpers, span);
        };
        let depth = s.binders.len();
        let body = Term::Eq(None, Rc::new(s.lhs.clone()), Rc::new(rhs.clone()));
        let ty = pi_over(&s.binders, body.clone());
        // §10: a right side much larger than the arm's body (a `let` used
        // many times, substituted) isn't generated.
        let (size, arm_size) = (s.rhs_size, s.arm_size);
        if too_large(size, arm_size) {
            return skip(too_large_why(size, arm_size));
        }
        // The proof.
        let tree = self.walk_proof(d, k, shape, shapes, &s.hyps, depth, &body, Then::Own)?;
        let lam_names: Vec<(Name, Icit)> =
            s.binders.iter().map(|(x, i, _)| (x.clone(), *i)).collect();
        let proof = lams(&lam_names, tree);
        self.declare_equation(d, k, &d.rows[k].suffix(), &ty, proof, &[])
    }

    /// Row `k`'s statement: its variables and hypotheses, and the two sides
    /// of its equation, at the depth of those.
    fn stated(
        &self,
        d: &Def,
        k: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
    ) -> R<Stated> {
        let g = &self.ev();
        // The hypotheses: each earlier row it overlaps.
        let mut hyps: Vec<Hyp> = Vec::new();
        for j in d.earlier(k) {
            let (what, noun) = d.row_said(j);
            let other = match &shapes[j] {
                Ok(s) => s,
                // An earlier arm without a right side (`()`): what it covers
                // has no values, so it needs no hypothesis.
                Err(_) if !d.rows[j].has_rhs => continue,
                Err(_) => {
                    return skip(format!(
                        "the overlap with {what} can't be stated: that {noun}'s patterns couldn't be read"
                    ));
                }
            };
            match overlap(g, other, shape)? {
                Overlap::Disjoint => {}
                Overlap::Unknown => {
                    return skip(format!(
                        "the overlap with {what} can't be stated as equations of this arm's \
                         variables"
                    ));
                }
                Overlap::Indexed => {
                    return skip(format!(
                        "it overlaps {what} on an indexed family, where the hypothesis would \
                         compare values of different types (D2185; a heterogeneous equation \
                         isn't in std)"
                    ));
                }
                // Reached where its condition is false.
                Overlap::Covers { bound } if d.rows[j].guarded => {
                    let cond = other.guard.as_ref().map(|r| &r.cond);
                    if cond.is_none_or(|c| {
                        levels_in(c, other.depth)
                            .iter()
                            .any(|l| !bound.contains_key(l))
                    }) {
                        return skip(format!(
                            "{what}'s condition mentions what its patterns don't bind, which                              this {noun}'s variables can't say"
                        ));
                    }
                    hyps.push(Hyp::NotGuard { row: j, bound });
                }
                Overlap::Covers { .. } => {
                    return skip(format!(
                        "{what} matches everything it does, so it's never reached"
                    ));
                }
                Overlap::Meets {
                    mut vars,
                    eqs,
                    bound,
                } => {
                    let guarded = d.rows[j].guarded;
                    if guarded {
                        // The condition's variables are bound too.
                        let cond = &other
                            .guard
                            .as_ref()
                            .ok_or_else(|| Stop::Skip(format!("{what}'s condition wasn't read")))?
                            .cond;
                        let mut pending = levels_in(cond, other.depth);
                        while let Some(l) = pending.pop() {
                            if vars.contains(&l) || bound.contains_key(&l) {
                                continue;
                            }
                            let Some(pos) = other.tele.iter().position(|&x| x == l) else {
                                return skip(format!(
                                    "{what}'s condition mentions what its patterns don't bind"
                                ));
                            };
                            vars.push(l);
                            pending.extend(levels_in(&other.types[pos], other.depth));
                        }
                        vars.sort_by_key(|l| other.tele.iter().position(|x| x == l));
                    }
                    hyps.push(Hyp::Overlap {
                        row: j,
                        vars,
                        eqs,
                        bound,
                        guarded,
                    })
                }
            }
        }
        let mut hyps = merge_chars(g, hyps, shapes);
        // D2189: past the cap, decided before any kernel work.
        let literals = hyps.iter().filter(|h| number_overlap(h)).count();
        if literals > LITERAL_CAP {
            return skip(format!(
                "it would take {literals} hypotheses `x ≠ k`, one for each earlier number arm, \
                 more than the {LITERAL_CAP} an equation is made with (its proof's cost grows \
                 with their square)"
            ));
        }
        if d.rows[k].guarded {
            hyps.push(Hyp::Guard);
        }
        // The right side: a leaf of this row, read in the arm's variables
        // (a guarded row's under its condition's proof, one level more).
        let (rhs, arm_size) = self.right_side(d, k, shape)?;
        // The statement.
        let tk = shape.tele.len();
        let at = |t: &Term, to: usize| -> R<Term> { remap_shape(g, t, shape, to) };
        let mut binders: Vec<(Name, Icit, Term)> = Vec::new();
        for (j, ty) in shape.types.iter().enumerate() {
            binders.push((shape.names[j].clone(), shape.icits[j], at(ty, j)?));
        }
        let mut used: Vec<Name> = shape.names.clone();
        for (i, h) in hyps.iter().enumerate() {
            let base = match h {
                Hyp::Guard => {
                    guard_name(d.rows[k].guard.as_ref()).unwrap_or_else(|| "guard".to_string())
                }
                Hyp::Overlap { row, .. } | Hyp::NotGuard { row, .. } => {
                    let r = &d.rows[*row];
                    if r.parent.is_some() {
                        format!("notAlt{}", r.alt)
                    } else if d.alt_names {
                        format!("notAlt{}", r.arm)
                    } else if r.arm == d.rows[k].arm {
                        format!("notOr{}", r.or.unwrap_or(1))
                    } else {
                        let same_arm = hyps.iter().filter(|h| matches!(h, Hyp::Overlap { row: o, .. } | Hyp::NotGuard { row: o, .. } if d.rows[*o].arm == r.arm && d.rows[*o].parent.is_none())).count();
                        match (same_arm > 1, r.or) {
                            (true, Some(m)) => format!("notArm{}or{m}", r.arm),
                            _ => format!("notArm{}", r.arm),
                        }
                    }
                }
                Hyp::Listed { .. } => "notListed".to_string(),
            };
            let name: Name = fresh(&used, &base).into();
            used.push(name.clone());
            let ty = self.hyp_type(h, shape, shapes, tk + i)?;
            binders.push((name, Icit::Explicit, ty));
        }
        let depth = tk + hyps.len();
        let f_args: Vec<(Term, Icit)> = shape
            .lhs
            .iter()
            .zip(&d.binders)
            .map(|(t, b)| Ok((at(t, depth)?, b.icit)))
            .collect::<R<_>>()?;
        let lhs = apps(Term::Def(d.f), f_args);
        let rhs_size = rhs.as_ref().map_or(0, |r| r.subterms().count());
        let rhs = match rhs {
            // The condition's proof, read at the shape's depth, is the
            // `guard` hypothesis, the last binder; a `Bool`'s `()` isn't.
            Some(r) if d.rows[k].guarded => {
                let dec = shape.guard.as_ref().is_some_and(|r| r.dec);
                let r = remap(g, &r, shape.depth + 1, depth, &|l| {
                    if l == shape.depth {
                        dec.then_some(Term::Var(0))
                    } else {
                        let j = shape.tele.iter().position(|&x| x == l)?;
                        Some(Term::Var(depth - 1 - j))
                    }
                })?
                .ok_or_else(|| {
                    Stop::Skip(
                        "its right side mentions a variable its arm doesn't bind, or its                          condition's `()`"
                            .into(),
                    )
                })?;
                Some(r)
            }
            Some(r) => Some(at(&r, depth)?),
            None => None,
        };
        Ok(Stated {
            binders,
            hyps,
            lhs,
            rhs,
            rhs_size,
            arm_size,
        })
    }

    /// The proof, at `depth` (the statement's variables and hypotheses,
    /// and any binders after them), of row `k`'s `body` (`f lhs = rhs`): a
    /// case tree that walks the definition's.
    #[allow(clippy::too_many_arguments)]
    fn walk_proof(
        &self,
        d: &Def,
        k: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
        hyps: &[Hyp],
        depth: usize,
        body: &Term,
        then: Then,
    ) -> R<Term> {
        let mut walk = Walk::new(self, d, k, shape, shapes, hyps, depth, body)?;
        walk.then = then;
        let mut fvals = Vec::new();
        for level in 0..d.tree_params() {
            fvals.push(match d.param_of_tree_level(level) {
                Some(i) => walk.pv_of(&shape.lhs[i], shape)?,
                None => PV::Rec,
            });
        }
        walk.go(&d.tree, &mut fvals, &mut Vec::new())
    }

    /// Row `k`'s leaves, as walking the definition's tree with its left side
    /// reaches them, each read in its own context (SW-1071): for a row an
    /// earlier one overlaps, whose leaves' bodies capture what each refined.
    fn refined_leaves(
        &self,
        d: &Def,
        k: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
    ) -> R<Vec<LeafCtx>> {
        let tk = shape.tele.len();
        let unused = Term::Refl;
        let mut walk = Walk::new(self, d, k, shape, shapes, &[], tk, &unused)?;
        walk.dry = Some(Vec::new());
        let mut fvals = Vec::new();
        for level in 0..d.tree_params() {
            fvals.push(match d.param_of_tree_level(level) {
                Some(i) => walk.pv_of(&shape.lhs[i], shape)?,
                None => PV::Rec,
            });
        }
        walk.go(&d.tree, &mut fvals, &mut Vec::new())?;
        Ok(walk.dry.take().unwrap_or_default())
    }

    /// Declares the equation `f.suffix` of row `k`, of type `ty`, and has
    /// the kernel check `proof`; `unfolding` are the opaque helpers it
    /// looks inside, besides an opaque `f`.
    fn declare_equation(
        &mut self,
        d: &Def,
        k: usize,
        suffix: &str,
        ty: &Term,
        proof: Term,
        unfolding: &[DefId],
    ) -> R<()> {
        // Declared and checked by the kernel like any theorem.
        let name: Name = format!("{}.{suffix}", d.display).into();
        let id = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            ty,
            true,
            false,
            d.rows[k].span,
        )?;
        let opaque = matches!(d.kind, Kind::Opaque);
        if opaque || !unfolding.is_empty() {
            let mut all: Vec<DefId> = opaque.then_some(d.f).into_iter().collect();
            all.extend(unfolding.iter().copied());
            if opaque {
                stitchwort_core::check::mark_opaque(&mut self.kernel, id);
            }
            stitchwort_core::check::set_unfolding(&mut self.kernel, id, &all);
        }
        kernel::define_group(&mut self.kernel, &self.tables, &[(id, proof)])?;
        if let Some(item) = self.unit.module.item {
            self.unit.module.note_def(id, item);
        }
        let key = format!("{}.{suffix}", d.key);
        self.scope
            .insert(&key, Global::Def(id), d.rows[k].span, false);
        // A name under `f.eqK`, as an update lemma is under its accessor:
        // dot notation looks these up as local definitions; so are the
        // names it is under (`f.eq2` for `f.eq2.or1` and `f.eq2.ifTrue`).
        let parts: Vec<&str> = suffix.split('.').collect();
        let mut under = d.key.clone();
        for part in &parts[..parts.len() - 1] {
            under = format!("{under}.{part}");
            self.tables.helper_keys.add(under.clone());
        }
        self.tables.helper_keys.add(key);
        Ok(())
    }

    /// The equation of one branch below row `k` (stage 1b, §3.2 and §4,
    /// item 4): the row's statement, then one step down each split of
    /// `path`, each adding the hypothesis it was taken under (and a lifted
    /// `match`'s pattern variables). Proved by the row's own proof (`f lhs
    /// = rhs`, walking the definition's tree), carried along a proof that
    /// `rhs` is the branch's right side under the hypotheses.
    ///
    /// A `match` below a lifted `match`'s alternative, compiled into its
    /// helper's tree, on a variable bound further up (SW-1069) is stated
    /// where that variable is bound: an attempt finds it ([`Refine`]), and
    /// the next compiles its pattern below that row, the definition's (so
    /// its left side) or the alternative's.
    #[allow(clippy::too_many_arguments)]
    fn branch_equation(
        &mut self,
        d: &Def,
        k: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
        path: &[Taken],
        suffix: &str,
        helpers: &mut HashMap<DefId, Rc<Helper>>,
        span: Span,
    ) -> R<()> {
        let mut refines: Vec<Refine> = Vec::new();
        loop {
            let mut wanted = Vec::new();
            let at = (shape, shapes, path, suffix, span);
            match self.branch_equation_with(d, k, at, helpers, &refines, &mut wanted) {
                Err(Stop::Skip(why)) if !wanted.is_empty() => {
                    // Each refinement is asked for once, so this ends.
                    if wanted
                        .iter()
                        .any(|w| refines.iter().any(|r| r.key == w.key))
                    {
                        return skip(why);
                    }
                    refines.extend(wanted);
                }
                other => return other,
            }
        }
    }

    /// [`Self::branch_equation`] with `refines` compiled below their rows;
    /// any more it needs are added to `wanted` (and it is skipped).
    #[allow(clippy::type_complexity)]
    fn branch_equation_with(
        &mut self,
        d: &Def,
        k: usize,
        (shape, shapes, path, suffix, span): (
            &Shape,
            &[std::result::Result<Shape, String>],
            &[Taken],
            &str,
            Span,
        ),
        helpers: &mut HashMap<DefId, Rc<Helper>>,
        refines: &[Refine],
        wanted: &mut Vec<Refine>,
    ) -> R<()> {
        // The row's patterns, with those of the `match`es on its variables
        // below lifted alternatives (SW-1069) compiled below them.
        let refined;
        let shape = if refines.iter().any(|r| r.site == Site::Row) {
            let mut row = d.rows[k].clone();
            for r in refines.iter().filter(|r| r.site == Site::Row) {
                row.chain.push((r.scrutinees.clone(), r.patterns.clone()));
            }
            refined = self.probe_row(d, k, &row, span)?;
            &refined
        } else {
            shape
        };
        let s = self.stated(d, k, shape, shapes)?;
        let base = s.binders.len();
        let lib = self.branch_lib()?;
        let tk = shape.tele.len();
        let used: Vec<Name> = s.binders.iter().map(|b| b.0.clone()).collect();
        let (binders, z, unfolding, then, arm_size) = match &s.rhs {
            Some(rhs) => {
                let run = self.branch_run(
                    d,
                    &lib,
                    (s.binders.clone(), used, tk),
                    rhs.clone(),
                    path,
                    helpers,
                    (refines, wanted),
                    false,
                )?;
                let g = &self.ev();
                let top = run.binders.len();
                // The proof that the row's right side is the branch's, from
                // the inside out.
                let mut q = Term::Refl;
                for step in run.steps.iter().rev() {
                    q = lib.step_proof(g, step, top, &run.cur, q)?;
                }
                let lhs = s.lhs.shift(g, top - base, 0)?;
                let then = if matches!(q, Term::Refl) {
                    Then::Own
                } else {
                    Then::One(lhs, q)
                };
                (run.binders, run.cur, run.unfolding, then, s.arm_size)
            }
            // An earlier row overlaps it and each of its leaves' bodies
            // captures what that leaf refined (SW-1071): the splits are
            // gone down from each leaf, in its own context, and stated in
            // the row's variables, each term a leaf refined a variable to
            // being that variable again; every leaf must say the same.
            None => {
                let leaves = self.refined_leaves(d, k, shape, shapes)?;
                let Some(first) = leaves.first() else {
                    return skip("its arm is never reached in the definition's case tree");
                };
                let arm_size = first.size;
                let mut said: Option<(Vec<(Name, Icit, Term)>, Term)> = None;
                let mut proofs = Vec::new();
                let mut unfolding: Vec<DefId> = Vec::new();
                for leaf in &leaves {
                    let mut binders = s.binders[..tk].to_vec();
                    for i in tk..leaf.depth {
                        binders.push((
                            format!("%field{i}").into(),
                            Icit::Explicit,
                            Term::Sort(Sort::Prop),
                        ));
                    }
                    let run = self.branch_run(
                        d,
                        &lib,
                        (binders, used.clone(), tk),
                        leaf.body.clone(),
                        path,
                        helpers,
                        (refines, wanted),
                        false,
                    )?;
                    let g = &self.ev();
                    let top = run.binders.len();
                    let mut q = Term::Refl;
                    for step in run.steps.iter().rev() {
                        q = lib.step_proof(g, step, top, &run.cur, q)?;
                    }
                    let left_over = || {
                        Stop::Skip(if path.is_empty() {
                            let rhs = d.rows[k].rhs.as_ref();
                            refined_reason(rhs.is_some_and(|e| !branch_paths(e).is_empty()))
                        } else {
                            "an earlier arm overlaps it, and in one case of that arm's patterns its \
                             right side mentions what the case's patterns bind (a lifted `match` or \
                             local definition captures it), which the arm's variables can't say"
                                .to_string()
                        })
                    };
                    let mut bs = Vec::new();
                    for (i, (x, icit, ty)) in run.binders[leaf.depth..].iter().enumerate() {
                        let ty = generalise(g, ty, leaf.depth + i, leaf, tk, base)?
                            .ok_or_else(left_over)?;
                        bs.push((x.clone(), *icit, ty));
                    }
                    let z = generalise(g, &run.cur, top, leaf, tk, base)?.ok_or_else(left_over)?;
                    match &said {
                        None => said = Some((bs, z)),
                        Some((bs0, z0)) => {
                            let same = bs0.len() == bs.len()
                                && bs0.iter().zip(&bs).all(|(a, b)| {
                                    a.1 == b.1 && stitchwort_core::value::same_term(&a.2, &b.2)
                                })
                                && stitchwort_core::value::same_term(z0, &z);
                            if !same {
                                return skip(
                                    "an earlier arm overlaps it, and its cases of that arm's \
                                     patterns state the branch differently",
                                );
                            }
                        }
                    }
                    for u in run.unfolding {
                        if !unfolding.contains(&u) {
                            unfolding.push(u);
                        }
                    }
                    proofs.push(LeafProof {
                        path: leaf.path.clone(),
                        depth: leaf.depth,
                        q,
                    });
                }
                let (bs, z) = said.expect("a leaf was read");
                let mut binders = s.binders.clone();
                binders.extend(bs);
                let top = binders.len();
                let lhs = s.lhs.shift(&self.ev(), top - base, 0)?;
                (binders, z, unfolding, Then::PerLeaf(lhs, proofs), arm_size)
            }
        };
        let g = &self.ev();
        let top = binders.len();
        // §10, for the branch's right side too.
        let size = z.subterms().count();
        if too_large(size, arm_size) {
            return skip(too_large_why(size, arm_size));
        }
        // The row's proof, walking the definition's tree (its case splits
        // at the top), going on along the proof that its right side is the
        // branch's at the row's leaf.
        let lhs = s.lhs.shift(g, top - base, 0)?;
        let body = Term::Eq(None, Rc::new(lhs), Rc::new(z));
        let tree = self.walk_proof(d, k, shape, shapes, &s.hyps, top, &body, then)?;
        let ty = pi_over(&binders, body);
        let lam_names: Vec<(Name, Icit)> =
            binders.iter().map(|(x, i, _)| (x.clone(), *i)).collect();
        let proof = lams(&lam_names, tree);
        self.declare_equation(d, k, suffix, &ty, proof, &unfolding)
    }

    /// The splits of `path` below row `k`'s statement `s`, each adding its
    /// hypothesis (and a lifted `match`'s pattern variables) to the
    /// statement's binders: the steps, and the branch's right side. With
    /// `marked` (for `f.induct`, `induct.rs`), the statement was made with
    /// recursive calls marked ([`Def::mark_rec`]): whether a branch uses its
    /// binder is decided without the marks (the decrease proofs they keep
    /// don't count), an `else` normalised by D2186 whose decrease proofs use
    /// the refutation gets it from the other `Bool` equation, and the
    /// helpers' proofs aren't made. A row with no one right side (SW-1071)
    /// and a branch that refines a variable bound further up (SW-1069) are
    /// skipped here: their equations are stated from each leaf, or with a
    /// refined left side, which a case of `f.induct` doesn't follow.
    fn branch_steps(
        &mut self,
        d: &Def,
        s: &Stated,
        path: &[Taken],
        helpers: &mut HashMap<DefId, Rc<Helper>>,
        marked: bool,
    ) -> R<Stepped> {
        let Some(rhs) = s.rhs.clone() else {
            return skip(
                "an earlier arm overlaps it and its body captures what that arm's cases bind, so \
                 its branches are stated from each case (SW-1071), which a case here doesn't follow",
            );
        };
        let lib = self.branch_lib()?;
        let used: Vec<Name> = s.binders.iter().map(|b| b.0.clone()).collect();
        let row_vars = s.binders.len() - s.hyps.len();
        let mut wanted = Vec::new();
        let at = (s.binders.clone(), used, row_vars);
        match self.branch_run(d, &lib, at, rhs, path, helpers, (&[], &mut wanted), marked) {
            Err(Stop::Skip(_)) if !wanted.is_empty() => skip(
                "a `match` below a lifted `match`'s alternative splits a variable bound further up, \
                 so its equation refines where that is bound (SW-1069), which a case here doesn't \
                 follow",
            ),
            other => other,
        }
    }

    /// Goes down the splits of `path` from a row's right side `cur`, at the
    /// depth of `binders` (whose names are `used`, the first `row_vars` of
    /// them the row's variables): each split's hypothesis (and a lifted
    /// `match`'s pattern variables) added, with the step its proof takes;
    /// `marked` as for [`Self::branch_steps`].
    #[allow(clippy::too_many_arguments, clippy::type_complexity)]
    fn branch_run(
        &mut self,
        d: &Def,
        lib: &BranchLib,
        (mut binders, mut used, row_vars): (Vec<(Name, Icit, Term)>, Vec<Name>, usize),
        mut cur: Term,
        path: &[Taken],
        helpers: &mut HashMap<DefId, Rc<Helper>>,
        (refines, wanted): (&[Refine], &mut Vec<Refine>),
        marked: bool,
    ) -> R<Stepped> {
        let mut steps: Vec<Step> = Vec::new();
        let mut unfolding: Vec<DefId> = Vec::new();
        let mut unnamed = 0;
        let decreasing = matches!(d.kind, Kind::Decreasing { .. });
        // Whether a branch uses its binder, its decrease proofs aside.
        let uses_var = |g: &Ev, t: &Term| -> stitchwort_core::budget::Result<bool> {
            Ok(if marked {
                unmark(g, d, t)?.mentions(0)
            } else {
                t.mentions(0)
            })
        };
        // Which lifted `match` each binder is a pattern variable of.
        let mut origin: Vec<Option<usize>> = Vec::new();
        let mut path = path.iter().enumerate();
        while let Some((pi, taken)) = path.next() {
            let depth = binders.len();
            origin.resize(depth, None);
            let (head, args) = spine_icit(&cur);
            let lambda_body = |t: &Term| match t.strip_loc() {
                Term::Lam(_, _, b) => Ok((**b).clone()),
                _ => skip("an `if`'s branch isn't a function as elaborated"),
            };
            match taken.split {
                TailSplit::If { binder } => {
                    let named = binder.filter(|b| b.text != "_");
                    let yes = taken.choice == 0;
                    let is = |id: DefId| matches!(head, Term::Def(h) if *h == id);
                    // The condition: `c` of `Bool.ifThenElse [a] c t e`, `p` of
                    // `Decidable.elim p motive dec yes no` (whose `args[1]`
                    // is the result type, closed whatever the condition).
                    let condition = if is(lib.ite) && args.len() == 4 {
                        Some(&args[1].0)
                    } else if is(lib.elim) && args.len() == 5 {
                        Some(&args[0].0)
                    } else {
                        None
                    };
                    if refines.is_empty() && condition.is_some_and(closed) {
                        return skip(CLOSED_SPLIT);
                    }
                    if is(lib.ite) && args.len() == 4 && named.is_none() {
                        let branch = lambda_body(&args[if yes { 2 } else { 3 }].0)?;
                        if branch.mentions(0) {
                            return skip("its `if`'s branch uses its `()`");
                        }
                        unnamed += 1;
                        let name: Name = fresh(&used, &format!("h{unnamed}")).into();
                        let value = lib.bool_value(yes);
                        let ty = Term::Eq(
                            Some(Rc::new(lib.bool_ty())),
                            Rc::new(args[1].0.clone()),
                            Rc::new(value),
                        );
                        used.push(name.clone());
                        binders.push((name, Icit::Explicit, ty));
                        steps.push(Step::Ite {
                            depth,
                            head: head.clone(),
                            args,
                        });
                        cur = branch;
                    } else if is(lib.elim) && args.len() == 5 {
                        let p = args[0].0.clone();
                        let mut branch = lambda_body(&args[if yes { 3 } else { 4 }].0)?;
                        let uses = uses_var(&self.ev(), &branch)?
                            && !self.proof_is_inert_in(&branch, marked.then_some(d), depth)?;
                        if uses && !yes {
                            return skip(
                                "its `else` branch uses the proof that the condition is false: \
                                 the branch computes on it, so two such proofs aren't known to be \
                                 equal (D2180)",
                            );
                        }
                        let uniq = if uses && !marked {
                            Some(self.uniqueness(lib, &p, &args[2].0, depth)?)
                        } else {
                            None
                        };
                        // D2186: the `else` of `b = True` is `b = False`.
                        let normal = if yes { None } else { lib.bool_test(&p) };
                        let base_name = match named {
                            Some(h) if yes => h.text.to_string(),
                            Some(h) => {
                                let mut cs = h.text.chars();
                                let first = cs.next().map(|c| c.to_uppercase().collect::<String>());
                                format!("not{}{}", first.unwrap_or_default(), cs.as_str())
                            }
                            None => {
                                unnamed += 1;
                                format!("h{unnamed}")
                            }
                        };
                        let ty = match (&normal, yes) {
                            (_, true) => p.clone(),
                            (Some((b, x)), false) => Term::Eq(
                                Some(Rc::new(lib.bool_ty())),
                                Rc::new(b.clone()),
                                Rc::new(lib.bool_value(!*x)),
                            ),
                            (None, false) => Term::app(Term::Def(lib.not), p.clone()),
                        };
                        // A decrease proof that uses the refutation `Not (b =
                        // X)` gets it from the hypothesis `b = notX`.
                        if marked
                            && let Some((_, x)) = &normal
                            && branch.mentions(0)
                        {
                            let conv = lib.refutation_of_other(*x);
                            let at = depth + 1;
                            branch = remap(&self.ev(), &branch, at, at, &|l| {
                                Some(if l == depth {
                                    conv.clone()
                                } else {
                                    Term::Var(at - 1 - l)
                                })
                            })?
                            .ok_or_else(|| {
                                Stop::Skip("an `if`'s branch couldn't be read".into())
                            })?;
                        }
                        let name: Name = fresh(&used, &base_name).into();
                        used.push(name.clone());
                        binders.push((name, Icit::Explicit, ty));
                        steps.push(Step::Dec {
                            depth,
                            args,
                            yes,
                            uniq,
                            normal,
                        });
                        cur = branch;
                    } else {
                        return skip(
                            "its `if` isn't elaborated as `Bool.ifThenElse` or `Decidable.elim`, \
                             the two stage 1b follows",
                        );
                    }
                }
                TailSplit::Match { scrutinees, alts } => {
                    // On several expressions (SW-1074), stated as on the
                    // one tuple of them: `isAlt1: (a, b) = (p, q)`.
                    let several = scrutinees.len() > 1;
                    if several && scrutinees.iter().any(|s| s.name.is_some()) {
                        return skip(
                            "a `match` on several expressions naming one's equation (`h: e`) \
                             isn't stated",
                        );
                    }
                    let scrutinee = &scrutinees[0];
                    let alt = &alts[taken.choice];
                    if alt.patterns.iter().any(has_or) {
                        return skip(
                            "an alternative with an or-pattern, in a lifted `match`, isn't stated \
                             in stage 1b",
                        );
                    }
                    let Term::Def(h) = head else {
                        return skip("its `match` isn't a call of a lifted `match`'s helper here");
                    };
                    let h = *h;
                    let call = self.helper_call(h, scrutinees, &args)?;
                    // Only unrefined: a row refined where its variable is
                    // bound (SW-1069) can close a scrutinee the program
                    // computes from that variable (`List.head rest` with
                    // `rest` refined to `Nil`); the closed check is for terms
                    // closed in the program, which the unrefined run meets
                    // first (SW-1078).
                    if refines.is_empty() && call.cols.iter().all(|&c| closed(&args[c].0)) {
                        return skip(CLOSED_SPLIT);
                    }
                    let helper = match helpers.get(&h) {
                        Some(x) => x.clone(),
                        None => {
                            let made = Rc::new(self.helper(d, h, &call.cols, alts)?);
                            helpers.insert(h, made.clone());
                            made
                        }
                    };
                    if self.kernel.def(h).opaque() {
                        unfolding.push(h);
                    }
                    // The alternative's row, or below it, the row of each
                    // `match` on its variables compiled into the helper's
                    // tree that the path goes on through.
                    let mut row = taken.choice;
                    let mut below: Vec<&Taken> = Vec::new();
                    while !helper.children[row].is_empty() {
                        let Some((_, next)) = path.next() else {
                            return skip("its `match`'s alternative has no one right side");
                        };
                        row = *helper.children[row].get(next.choice).ok_or_else(|| {
                            Stop::Skip("its `match`'s alternatives couldn't be followed".into())
                        })?;
                        below.push(next);
                    }
                    // With the patterns of `match`es further down on its
                    // variables compiled below it (SW-1069).
                    let here: Vec<&Refine> = refines
                        .iter()
                        .filter(|r| r.site == Site::Step(pi))
                        .collect();
                    let refined = if here.is_empty() {
                        None
                    } else {
                        Some(self.refined_row(&helper, row, &here)?)
                    };
                    let (he, hs) = match &refined {
                        Some(x) => (&x.0, &x.1),
                        None => match (&helper.eqs[row], &helper.shapes[row]) {
                            (Ok(he), Ok(hs)) => (he, hs),
                            (Err(why), _) | (_, Err(why)) => {
                                return skip(format!("its `match`'s alternative: {why}"));
                            }
                        },
                    };
                    let g = &self.ev();
                    let n_h = helper.arity;
                    let he_len = he.binders.len();
                    // A variable the helper captured that the alternative's
                    // row refines (a `match` below it, compiled into the
                    // helper's tree): the call's argument is the pattern, its
                    // variables the branch's; where it is only the variable,
                    // that is refined where it is bound, and the branch
                    // stated again (SW-1069).
                    let (hb, _) = split_pis(g.def(h).ty(), Some(n_h));
                    let mut solved: HashMap<usize, Term> = HashMap::default();
                    let mut asked = Vec::new();
                    for (p, (a, _)) in he.args.iter().enumerate() {
                        if call.cols.contains(&p)
                            || Some(p) == call.eq
                            || matches!(a.strip_loc(), Term::Var(_))
                        {
                            continue;
                        }
                        if match_pattern(g, a, he_len, &args[p].0, &mut solved) {
                            continue;
                        }
                        let site = match args[p].0.strip_loc() {
                            Term::Var(i) if *i < depth => {
                                let level = depth - 1 - i;
                                if level < row_vars {
                                    Some(Site::Row)
                                } else {
                                    origin[level].map(Site::Step)
                                }
                            }
                            _ => None,
                        };
                        let by = below.iter().find_map(|t| match t.split {
                            TailSplit::Match { scrutinees, alts }
                                if scrutinees.iter().all(|s| {
                                    s.name.is_none()
                                        && matches!(&s.expr, Expr::Var(x) if x.text.as_str() == &*hb[p].name)
                                }) =>
                            {
                                Some((scrutinees, &alts[t.choice], t.seg.clone()))
                            }
                            _ => None,
                        });
                        match (site, by) {
                            (Some(site), Some((scrutinees, a, seg))) => asked.push(Refine {
                                site,
                                scrutinees: scrutinees.to_vec(),
                                patterns: a.patterns.clone(),
                                key: a.span,
                                seg,
                            }),
                            _ => {
                                return skip(
                                    "a `match` below its `match`'s alternative splits a variable \
                                     bound further up, where the branch can't state it refined",
                                );
                            }
                        }
                    }
                    if !asked.is_empty() {
                        wanted.extend(asked);
                        return skip(
                            "a `match` below its `match`'s alternative splits a variable bound \
                             further up, and stating it refined there didn't give the pattern",
                        );
                    }
                    // The helper's equation's variables, as the branch has
                    // them: its captures are the call's arguments, the
                    // alternative's pattern variables are the branch's, a
                    // catch-all is the scrutinee itself.
                    // On several expressions, a catch-all is a variable of
                    // the branch, as a tuple pattern's component is (named
                    // `fst` or `snd` for a `_`, as that component is); where
                    // every one is, the expressions themselves, as for a
                    // catch-all of the tuple.
                    let mut vals: Vec<(Term, usize)> = Vec::new();
                    let col_vars: Vec<Option<usize>> = call
                        .cols
                        .iter()
                        .map(|&c| match hs.lhs[c].strip_loc() {
                            Term::Var(i) => Some(hs.depth - 1 - i),
                            _ => None,
                        })
                        .collect();
                    let col = call.cols[0];
                    let all_vars = col_vars.iter().all(Option::is_some);
                    let col_var = if several { None } else { col_vars[0] };
                    let mut hyp = None;
                    for (j, &l) in hs.tele.iter().enumerate() {
                        let here = binders.len();
                        if let Some(t) = solved.get(&j) {
                            vals.push((t.clone(), depth));
                            continue;
                        }
                        let (hname, hicit, hty) = &he.binders[j];
                        let param = (1..=n_h).contains(&l).then(|| l - 1);
                        let component = (0..call.cols.len())
                            .find(|&c| col_vars[c] == Some(l) || param == Some(call.cols[c]));
                        if several
                            && all_vars
                            && let Some(c) = component
                        {
                            vals.push((args[call.cols[c]].0.clone(), depth));
                        } else if several && let Some(c) = component {
                            let ty = instantiate(g, hty, j, &vals, here)?;
                            let base = match &alt.patterns[c] {
                                Pattern::Wildcard(_) if c + 1 < call.cols.len() => "fst",
                                Pattern::Wildcard(_) => "snd",
                                Pattern::Var(x) => x.text.as_str(),
                                _ => &**hname,
                            };
                            let name: Name = fresh(&used, base).into();
                            used.push(name.clone());
                            binders.push((name, Icit::Explicit, ty));
                            origin.resize(here, None);
                            origin.push(Some(pi));
                            vals.push((Term::Var(0), here + 1));
                        } else if Some(l) == col_var || param == Some(col) {
                            vals.push((args[col].0.clone(), depth));
                        } else if param.is_some() && param != call.eq {
                            let p = param.expect("a parameter");
                            vals.push((args[p].0.clone(), depth));
                        } else {
                            let ty = instantiate(g, hty, j, &vals, here)?;
                            let base = match (param, &scrutinee.name) {
                                (Some(_), Some(n)) => n.text.to_string(),
                                _ => hname.to_string(),
                            };
                            let name: Name = fresh(&used, &base).into();
                            used.push(name.clone());
                            let icit = if param.is_some() {
                                Icit::Explicit
                            } else {
                                *hicit
                            };
                            binders.push((name, icit, ty));
                            origin.resize(here, None);
                            origin.push(Some(pi));
                            vals.push((Term::Var(0), here + 1));
                            if param.is_some() {
                                hyp = Some(here);
                            }
                        }
                    }
                    let tk_h = hs.tele.len();
                    // The hypothesis that the scrutinee is the pattern,
                    // where the helper takes no equation of its own.
                    // On several expressions, `(a, b) = (p, q)`, at the type
                    // `(A, B)` of the helper's parameters.
                    let mut col_tys = Vec::new();
                    if several && !all_vars {
                        let here = binders.len();
                        let mut es = Vec::new();
                        let mut ps = Vec::new();
                        for &c in &call.cols {
                            ps.push(instantiate(g, &he.args[c].0, he_len, &vals, here)?);
                            es.push(args[c].0.shift(g, here - depth, 0)?);
                            let at: Vec<(Term, usize)> =
                                args[..c].iter().map(|(a, _)| (a.clone(), depth)).collect();
                            col_tys.push(instantiate(g, &hb[c].ty, c, &at, depth)?);
                        }
                        let tys = col_tys
                            .iter()
                            .map(|t| t.shift(g, here - depth, 0))
                            .collect::<std::result::Result<Vec<_>, _>>()?;
                        let pair = tuple_parts(g)?;
                        let name: Name = fresh(&used, &format!("isAlt{}", taken.choice + 1)).into();
                        used.push(name.clone());
                        binders.push((
                            name,
                            Icit::Explicit,
                            Term::Eq(
                                Some(Rc::new(tuple_ty(pair.0, &tys))),
                                Rc::new(tuple(pair, &es)),
                                Rc::new(tuple(pair, &ps)),
                            ),
                        ));
                        hyp = Some(here);
                    }
                    if !several && hyp.is_none() && col_var.is_none() {
                        let here = binders.len();
                        let pattern = instantiate(g, &he.args[col].0, he_len, &vals, here)?;
                        let e = args[col].0.shift(g, here - depth, 0)?;
                        let base = match (&scrutinee.name, alt_ctor(alt)) {
                            (Some(n), _) => n.text.to_string(),
                            (None, Some(c)) => format!("is{c}"),
                            (None, None) => format!("isAlt{}", taken.choice + 1),
                        };
                        // Its type, the helper's parameter's with the call's
                        // arguments (a pair's can't be inferred).
                        let at: Vec<(Term, usize)> = args[..col]
                            .iter()
                            .map(|(a, _)| (a.clone(), depth))
                            .collect();
                        let ty = instantiate(g, &hb[col].ty, col, &at, here)?;
                        let name: Name = fresh(&used, &base).into();
                        used.push(name.clone());
                        binders.push((
                            name,
                            Icit::Explicit,
                            Term::Eq(Some(Rc::new(ty)), Rc::new(e), Rc::new(pattern)),
                        ));
                        hyp = Some(here);
                    }
                    // The earlier alternatives it overlaps.
                    for j in tk_h..he_len {
                        let here = binders.len();
                        let (hname, _, hty) = &he.binders[j];
                        let ty = instantiate(g, hty, j, &vals, here)?;
                        // `e = p`, where `e` took a catch-all's place: typed,
                        // as a pair's equation can't be inferred.
                        let ty = match col_var {
                            None if several && all_vars => {
                                let mut ty = ty;
                                for &c in &call.cols {
                                    let e = args[c].0.shift(g, here - depth, 0)?;
                                    let at: Vec<(Term, usize)> =
                                        args[..c].iter().map(|(a, _)| (a.clone(), depth)).collect();
                                    let col_ty = instantiate(g, &hb[c].ty, c, &at, here)?;
                                    ty = typed_equations(g, &ty, &e, &col_ty, 0)?;
                                }
                                ty
                            }
                            Some(_) => {
                                let e = args[col].0.shift(g, here - depth, 0)?;
                                let at: Vec<(Term, usize)> = args[..col]
                                    .iter()
                                    .map(|(a, _)| (a.clone(), depth))
                                    .collect();
                                let col_ty = instantiate(g, &hb[col].ty, col, &at, here)?;
                                typed_equations(g, &ty, &e, &col_ty, 0)?
                            }
                            None => ty,
                        };
                        let name: Name = fresh(&used, hname).into();
                        used.push(name.clone());
                        binders.push((name, Icit::Explicit, ty));
                        vals.push((Term::Var(0), here + 1));
                    }
                    let after = binders.len();
                    let mut result = instantiate(g, &he.rhs, he_len, &vals, after)?;
                    if decreasing {
                        result = beta_rec(g, result)?;
                    }
                    // Its proof inline, or where it splits a variable (a
                    // case tree may only be at the top of a declaration),
                    // declared as a hidden lemma `f.%match1.eq2` once.
                    let mut proof = if marked {
                        Term::Refl
                    } else if he.split {
                        match he.decl.get() {
                            Some(id) => Term::Def(id),
                            None => {
                                let mut name = format!("eq{}", row + 1);
                                for r in &here {
                                    name += &format!(".{}", r.seg);
                                }
                                let id = self.helper_lemma(h, &name, he, alt.span)?;
                                he.decl.set(Some(id));
                                Term::Def(id)
                            }
                        }
                    } else {
                        Term::Ann(Rc::new(he.proof.clone()), Rc::new(he.ty.clone()))
                    };
                    let g = &self.ev();
                    if !marked {
                        for ((v, at), (_, icit, _)) in vals.iter().zip(&he.binders) {
                            proof = Term::app_icit(proof, v.shift(g, after - at, 0)?, *icit);
                        }
                    }
                    steps.push(Step::Helper {
                        depth,
                        after,
                        head: head.clone(),
                        args,
                        cols: call.cols.clone(),
                        col_tys,
                        eq: call.eq,
                        hyp,
                        proof,
                        result: result.clone(),
                    });
                    cur = result;
                }
            }
        }
        Ok(Stepped {
            binders,
            steps,
            cur,
            unfolding,
        })
    }

    /// Row `row` of a lifted `match`'s helper `h`, with the patterns of
    /// `refines` compiled below it (SW-1069): its equation and shape, made
    /// once for each set of refinements.
    fn refined_row(
        &mut self,
        helper: &Helper,
        row: usize,
        refines: &[&Refine],
    ) -> R<Rc<(HelperEq, Shape)>> {
        let key = (row, refines.iter().map(|r| r.key).collect::<Vec<_>>());
        if let Some(made) = helper.refined.borrow().get(&key) {
            return Ok(made.clone());
        }
        let mut r = helper.def.rows[row].clone();
        for x in refines {
            r.chain.push((x.scrutinees.clone(), x.patterns.clone()));
        }
        let hs = self.probe_row(&helper.def, row, &r, helper.root)?;
        let he = self.helper_equation(&helper.def, row, &hs, &helper.shapes)?;
        let made = Rc::new((he, hs));
        helper.refined.borrow_mut().insert(key, made.clone());
        Ok(made)
    }

    /// Which of a lifted `match`'s helper's parameters are the ones it
    /// matches, and which its equation (`match h: e`): as the lifter
    /// recorded them (`lift::MatchColumns`), one for each scrutinee, never
    /// read off the parameters' names.
    fn helper_call(&self, h: DefId, scrutinees: &[Scrutinee], args: &[(Term, Icit)]) -> R<Call> {
        let g = &self.ev();
        let def = g.def(h);
        if !def.name().contains(".%match") {
            return skip("its `match` isn't a call of a lifted `match`'s helper here");
        }
        let (hb, cod) = split_pis(def.ty(), Some(def.arity()));
        if hb.len() != def.arity() || args.len() != def.arity() {
            return skip("its `match`'s helper isn't called with all its parameters");
        }
        let Some(recorded) = self.tables.match_columns.get(&h) else {
            return skip("its `match`'s helper doesn't record what it matches");
        };
        if recorded.cols.len() != scrutinees.len()
            || recorded
                .cols
                .iter()
                .chain(recorded.eqs.iter().flatten())
                .any(|&p| p >= hb.len())
        {
            return skip("its `match`'s helper doesn't take what it matches");
        }
        let cols = recorded.cols.clone();
        // The lifter refuses a variable matched twice, so this is a guard.
        let distinct = (1..cols.len()).all(|i| !cols[..i].contains(&cols[i]));
        debug_assert!(distinct, "a `match`'s columns are distinct");
        if !distinct {
            return skip("its `match`'s helper doesn't take what it matches");
        }
        let eq = match recorded.eqs.as_slice() {
            [eq] => *eq,
            _ => None,
        };
        for &col in &cols {
            for (j, b) in hb.iter().enumerate().skip(col + 1) {
                if Some(j) != eq && b.ty.mentions(j - 1 - col) {
                    return skip(if cols.len() == 1 {
                        "its `match`'s helper takes copies of variables whose types mention what \
                         it matches, which stage 1b doesn't transport (§4, item 4)"
                    } else {
                        "its `match`'s helper takes variables whose types mention what it \
                         matches, which a tuple of the expressions can't state"
                    });
                }
            }
        }
        // A generalising `match` (`match h: xs.length with | Zero => Yes
        // rfl`, SW-1182): an alternative's result has the type at its
        // pattern, the call's at the expression, so `f lhs = result` isn't
        // well-typed.
        let mut matched = cols.iter().copied().chain(eq);
        if matched.any(|p| cod.mentions(def.arity() - 1 - p)) {
            return skip(
                "its `match`'s result type mentions what it matches (the `match` generalises it \
                 in the goal), so an alternative's right side has another type than the call's, \
                 which stage 1b doesn't transport (§4, item 4)",
            );
        }
        Ok(Call { cols, eq })
    }

    /// The equations of a lifted `match`'s helper `h`, one for each of its
    /// alternatives (`alts`), matching parameters `cols`: as a definition's
    /// for its arms (stage 1a), not declared, each a closed term.
    fn helper(&mut self, owner: &Def, h: DefId, cols: &[usize], alts: &[Alt]) -> R<Helper> {
        let g = &self.ev();
        let def = g.def(h);
        let arity = def.arity();
        let (binders, _) = split_pis(def.ty(), Some(arity));
        let body = def
            .body()
            .cloned()
            .ok_or_else(|| Stop::Skip("its `match`'s helper has no body".into()))?;
        let body = Rc::new(plain_ifs(g, &body)?);
        let special = special_params(g, &binders);
        if special.iter().any(Option::is_some) {
            return skip("its `match`'s helper is polymorphic in abilities");
        }
        let names = probe_names(&binders);
        let rows = alts
            .iter()
            .enumerate()
            .map(|(i, a)| Row {
                arm: i + 1,
                or: None,
                patterns: a.patterns.clone(),
                alternatives: Vec::new(),
                span: a.span,
                has_rhs: a.body.is_some(),
                guarded: a.guard.is_some(),
                guard: a.guard.clone(),
                suffix: format!("alt{}", i + 1),
                rhs: a.body.clone(),
                parent: None,
                alt: i + 1,
                chain: Vec::new(),
            })
            .collect();
        let mut hd = Def {
            f: h,
            kind: if def.opaque() {
                Kind::Opaque
            } else {
                Kind::Plain
            },
            key: def.name().to_string(),
            display: def.name().to_string(),
            binders,
            names,
            special,
            tree: Term::peel_lams_rc(&body, arity),
            leaves: Vec::new(),
            rows,
            columns: cols.to_vec(),
            alt_names: true,
            mark_rec: std::cell::Cell::new(false),
        };
        let arms: Vec<SourceArm> = alts
            .iter()
            .map(|a| SourceArm {
                patterns: a.patterns.clone(),
                guard: a.guard.clone(),
                rhs: a.body.clone(),
                span: a.span,
            })
            .collect();
        let root = alts.first().map_or(owner.rows[0].span, |a| a.span);
        hd.leaves = match self.recompute_leaves(&hd, &arms, root) {
            Ok(Some(leaves)) => leaves,
            Ok(None) => return skip("its `match`'s alternatives couldn't be compiled again"),
            Err(Stop::Error(e)) if !crate::undo::fatal(&e) => {
                return skip(format!(
                    "its `match`'s alternatives couldn't be compiled again: {}",
                    e.message
                ));
            }
            Err(e) => return Err(e),
        };
        // Each alternative's shape; one whose body is a `match` on its
        // variables, compiled into the helper's tree, has rows below it.
        let mut shapes = Vec::new();
        let mut children: Vec<Vec<usize>> = Vec::new();
        let mut i = 0;
        while i < hd.rows.len() {
            let shape = match self.probe_row(&hd, i, &hd.rows[i], root) {
                Ok(s) => Ok(s),
                Err(Stop::Skip(why)) => Err(why),
                Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(Stop::Error(e)),
                Err(Stop::Error(e)) => Err(format!("its patterns couldn't be read: {}", e.message)),
            };
            let mut below = Vec::new();
            if let Ok(s) = &shape
                && matches!(self.leaf_found(&hd, i, s)?, Found::Match)
                && let Ok(rows) = alternative_rows(&hd.rows[i], i)
            {
                below = (hd.rows.len()..hd.rows.len() + rows.len()).collect();
                hd.rows.extend(rows);
            }
            shapes.push(shape);
            children.push(below);
            i += 1;
        }
        let mut eqs = Vec::new();
        for (i, shape) in shapes.iter().enumerate() {
            let made = match shape {
                Ok(_) if !children[i].is_empty() => Err(Stop::Skip(String::new())),
                Ok(shape) => self.helper_equation(&hd, i, shape, &shapes),
                Err(why) => Err(Stop::Skip(why.clone())),
            };
            eqs.push(match made {
                Ok(e) => Ok(e),
                Err(Stop::Skip(why)) => Err(why),
                Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(Stop::Error(e)),
                Err(Stop::Error(e)) => Err(format!("{}: {}", e.code, e.message)),
            });
        }
        Ok(Helper {
            arity,
            def: hd,
            root,
            refined: Default::default(),
            shapes,
            eqs,
            children,
        })
    }

    /// Declares an alternative's equation of a lifted `match`'s helper `h`
    /// as a hidden theorem, `f.%match1.eq2` (`suffix` is `eq2`, and for a
    /// row refined below, SW-1069, its alternatives' names after it), for a
    /// branch equation whose proof uses it.
    fn helper_lemma(&mut self, h: DefId, suffix: &str, he: &HelperEq, span: Span) -> R<DefId> {
        let name: Name = format!("{}.{suffix}", self.kernel.def(h).name()).into();
        let id = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &name,
            &he.ty,
            true,
            false,
            span,
        )?;
        if self.kernel.def(h).opaque() {
            stitchwort_core::check::set_unfolding(&mut self.kernel, id, &[h]);
        }
        kernel::define_group(&mut self.kernel, &self.tables, &[(id, he.proof.clone())])?;
        if let Some(item) = self.unit.module.item {
            self.unit.module.note_def(id, item);
        }
        Ok(id)
    }

    /// Alternative `i`'s equation of a helper `hd`, as a closed term and
    /// its type (checked where it is used).
    fn helper_equation(
        &self,
        hd: &Def,
        i: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
    ) -> R<HelperEq> {
        let s = self.stated(hd, i, shape, shapes)?;
        let Some(rhs) = s.rhs.clone() else {
            return skip(refined_reason(false));
        };
        let depth = s.binders.len();
        let body = Term::Eq(None, Rc::new(s.lhs.clone()), Rc::new(rhs.clone()));
        let ty = pi_over(&s.binders, body.clone());
        let tree = self.walk_proof(hd, i, shape, shapes, &s.hyps, depth, &body, Then::Own)?;
        let lam_names: Vec<(Name, Icit)> =
            s.binders.iter().map(|(x, i, _)| (x.clone(), *i)).collect();
        let (_, args) = spine_icit(&s.lhs);
        let split = tree
            .subterms()
            .any(|(t, _)| matches!(t, Term::Case(..) | Term::NumCase(..)));
        Ok(HelperEq {
            binders: s.binders,
            args,
            rhs,
            proof: lams(&lam_names, tree),
            ty,
            split,
            decl: std::cell::Cell::new(None),
        })
    }

    /// Whether a branch `body` of an `if h: p` (under the binder `h`, in
    /// a context of `depth` variables) gives the same value for any two
    /// proofs `h`, by conversion: it reaches `h` only in inert positions
    /// (docs/proposals/proof-irrelevance.md), so the branch's equation
    /// needs no `J` along the uniqueness of proofs (§3.5). `d` for a
    /// `decreasing` definition, whose recursion marks are not part of the
    /// branch.
    fn proof_is_inert_in(&self, body: &Term, d: Option<&Def>, depth: usize) -> R<bool> {
        let g = &self.ev();
        let body = match d {
            Some(d) => unmark(g, d, body)?,
            None => body.clone(),
        };
        let with = |h: usize| -> R<Value> {
            let mut env: Vec<Value> = (0..depth).map(Value::var).collect();
            env.push(Value::var(h));
            Ok(eval(g, &env, &body)?)
        };
        Ok(stitchwort_core::value::conv(
            g,
            depth + 2,
            &with(depth)?,
            &with(depth + 1)?,
        )?)
    }

    /// A proof that any two proofs of `p` (decided by `decision`, at
    /// `depth`) are equal, for a branch of `if h: p` that uses `h` (§3.5,
    /// D2180): `p` an equation of `Bool`s (`<` and `≤` on `Nat` and `Int`
    /// are), or one decided by a `DecEq` instance.
    fn uniqueness(&self, lib: &BranchLib, p: &Term, decision: &Term, depth: usize) -> R<Uniq> {
        let g = &self.ev();
        let env: Vec<Value> = (0..depth).map(Value::var).collect();
        if let Value::Eq(ty, l, r) = force(g, eval(g, &env, p)?)?
            && matches!(force(g, (*ty).clone())?, Value::Data(b, _) if b == lib.bool)
        {
            return Ok(Uniq::Bool(
                stitchwort_core::value::quote(g, depth, &l)?,
                stitchwort_core::value::quote(g, depth, &r)?,
            ));
        }
        if let (Some((unique, icits)), Some(decide)) = (&lib.deceq_unique, lib.deceq_decide) {
            let (head, args) = spine_icit(decision);
            if matches!(head, Term::Def(id) if *id == decide) && args.len() == 4 && icits.len() == 6
            {
                return Ok(Uniq::DecEq(
                    *unique,
                    args.into_iter()
                        .zip(icits)
                        .map(|((t, _), i)| (t, *i))
                        .collect(),
                    icits[4..].to_vec(),
                ));
            }
        }
        skip(
            "its branch uses the proof `h` of a condition that isn't an equation in a type with \
             `DecEq` (or a comparison), and the branch computes on it: two proofs of it \
             aren't known to be equal (D2180)",
        )
    }

    /// The declarations branch equations are made with.
    fn branch_lib(&self) -> R<BranchLib> {
        let g = &self.ev();
        let r = &g.env.registry();
        let none = || Stop::Skip("the core's logic isn't loaded yet".into());
        let def = |key: &str| self.lookup_def(&format!("Std.{key}")).ok_or_else(none);
        let (bool_, true_) = r.ctor(Builtin::True).ok_or_else(none)?;
        let (_, false_) = r.ctor(Builtin::False).ok_or_else(none)?;
        let elim_eq = def("Decidable.elimEq")?;
        let (eb, _) = split_pis(g.def(elim_eq).ty(), None);
        let deceq_unique = self.lookup_def("Std.DecEq.uniqueEq").map(|id| {
            let (b, _) = split_pis(g.def(id).ty(), None);
            (id, b.iter().map(|b| b.icit).collect::<Vec<_>>())
        });
        Ok(BranchLib {
            ite: r.def(Builtin::IfThenElse).ok_or_else(none)?,
            elim: r.def(Builtin::ElimDec).ok_or_else(none)?,
            elim_eq,
            elim_eq_icits: eb.iter().map(|b| b.icit).collect(),
            bool: bool_,
            true_,
            false_,
            not: r.def(Builtin::Not).ok_or_else(none)?,
            exfalso: r.def(Builtin::VoidExfalso).ok_or_else(none)?,
            true_not_false: def("Bool.trueNotFalse")?,
            false_not_true: r.def(Builtin::FalseNotTrue).ok_or_else(none)?,
            bool_unique: r.def(Builtin::BoolUniqueEq).ok_or_else(none)?,
            deceq_unique,
            deceq_decide: self.lookup_def("Std.DecEq.decide"),
            inspect: self.lookup_def("Std.Bool.inspect"),
            to_bool: r.def(Builtin::Holds).ok_or_else(none)?,
            to_bool_lemmas: (|| {
                Some((
                    r.data(Builtin::Decidable)?,
                    r.def(Builtin::ToBoolOfNot)?,
                    r.def(Builtin::Refute)?,
                ))
            })(),
            dec_true: r.def(Builtin::DecTrue),
            and_data: r.data(Builtin::And).ok_or_else(none)?,
            and_dec: self.lookup_def("Std.Decidable.and"),
            not_not: (|| {
                Some((
                    self.lookup_def("Std.Decidable.notNotOf")?,
                    self.lookup_def("Std.Decidable.not")?,
                ))
            })(),
        })
    }

    /// Walks the definition's tree with row `k`'s left side, for its leaf
    /// ([`find_rhs`]).
    fn seek(&self, d: &Def, k: usize, shape: &Shape) -> R<Sought> {
        let g = &self.ev();
        let mut fmap: Vec<Option<Term>> = Vec::new();
        for level in 0..d.tree_params() {
            fmap.push(match d.param_of_tree_level(level) {
                Some(i) => Some(shape.lhs[i].clone()),
                None => Some(rec_term(d, shape.depth)),
            });
        }
        let unit = g.env.registry().ctor(Builtin::Trivial);
        let mut out = Sought {
            found: Found::None,
            guard_dec: None,
            unit: unit.map(|(d, c)| Term::Ctor(d, c, Vec::new())),
            blocked: Vec::new(),
        };
        find_rhs(
            g,
            d,
            k,
            &d.tree,
            &mut fmap,
            &mut Vec::new(),
            shape.depth,
            &mut out,
        )?;
        Ok(out)
    }

    /// What row `k`'s leaf is ([`Found`]).
    fn leaf_found(&self, d: &Def, k: usize, shape: &Shape) -> R<Found> {
        Ok(self.seek(d, k, shape)?.found)
    }

    /// Whether guarded row `k`'s condition is tested by `Decidable.elim`
    /// (else `Bool.ifThenElse`), where the definition first tests it.
    fn guard_form(&self, d: &Def, k: usize, shape: &Shape) -> R<bool> {
        let out = self.seek(d, k, shape)?;
        out.guard_dec.ok_or_else(|| {
            Stop::Skip("its arm is never reached in the definition's case tree".into())
        })
    }

    /// Row `k`'s right side, in its shape's context (for a guarded row, with
    /// its condition's proof one level more): the body of the first of its
    /// leaves that mentions only what the arm's patterns bind; `None` if
    /// each leaf's body mentions what that leaf refined (SW-1071).
    fn right_side(&self, d: &Def, k: usize, shape: &Shape) -> R<(Option<Term>, usize)> {
        match self.seek(d, k, shape)?.found {
            Found::Rhs(t, size) => Ok((Some(t), size)),
            Found::TooLarge(size, arm_size) => skip(too_large_to_read(size, arm_size)),
            Found::Match => skip(
                "its right side is a `match` on its variables, compiled into the case tree, so \
                 no one equation states it: each alternative's has its own (`f.eqK.cons`, …)",
            ),
            Found::Refined => Ok((None, 0)),
            Found::GuardProof => skip(GUARD_PROOF),
            Found::None => skip("its arm is never reached in the definition's case tree"),
        }
    }

    /// Hypothesis `h`'s type, at `depth` (the shape's variables, then the
    /// hypotheses before it).
    fn hyp_type(
        &self,
        h: &Hyp,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
        depth: usize,
    ) -> R<Term> {
        let g = &self.ev();
        let lib =
            Lib::new(g).ok_or_else(|| Stop::Skip("the core's logic isn't loaded yet".into()))?;
        match h {
            Hyp::Listed { level, rows } => {
                let x = remap_shape(g, &Term::Var(shape.depth - 1 - level), shape, depth)?;
                let chars: Rc<[char]> = rows.iter().map(|(_, c)| *c).collect();
                let list = lib.char_list(g, &chars)?;
                let mem = apps(
                    Term::Def(lib.mem),
                    [
                        (Term::Data(lib.char, Vec::new()), Icit::Implicit),
                        (x, Icit::Explicit),
                        (list, Icit::Explicit),
                    ],
                );
                Ok(Term::app(Term::Def(lib.not), mem))
            }
            Hyp::Guard => {
                let read = shape
                    .guard
                    .as_ref()
                    .ok_or_else(|| Stop::Skip("its condition wasn't read".into()))?;
                let (is_prop, cond) = read.stated();
                let cond = remap_shape(g, cond, shape, depth)?;
                Ok(guard_holds(self, is_prop, cond)?)
            }
            Hyp::NotGuard { row, bound } => {
                let other = shapes[*row].as_ref().map_err(|e| Stop::Skip(e.clone()))?;
                let read = other
                    .guard
                    .as_ref()
                    .ok_or_else(|| Stop::Skip("an earlier arm's condition wasn't read".into()))?;
                let mut solved: HashMap<usize, Term> = HashMap::default();
                for (l, t) in bound {
                    if let Ok(t) = remap_shape(g, t, shape, depth) {
                        solved.insert(*l, t);
                    }
                }
                let (is_prop, cond) = match &read.negated {
                    Some(q) => (true, q),
                    None => read.stated(),
                };
                let cond = remap(g, cond, other.depth, depth, &|l| solved.get(&l).cloned())?
                    .ok_or_else(|| {
                        Stop::Skip(
                            "an earlier arm's condition can't be stated in this arm's variables"
                                .into(),
                        )
                    })?;
                let blib = self.branch_lib()?;
                Ok(if read.negated.is_some() {
                    cond
                } else if read.prop.is_some() {
                    Term::app(Term::Def(lib.not), cond)
                } else if !is_prop {
                    Term::Eq(
                        Some(Rc::new(blib.bool_ty())),
                        Rc::new(cond),
                        Rc::new(blib.bool_value(false)),
                    )
                } else if let Some((b, x)) = blib.bool_test(&cond) {
                    Term::Eq(
                        Some(Rc::new(blib.bool_ty())),
                        Rc::new(b),
                        Rc::new(blib.bool_value(!x)),
                    )
                } else {
                    Term::app(Term::Def(lib.not), cond)
                })
            }
            Hyp::Overlap {
                row,
                vars,
                eqs,
                bound,
                guarded,
            } => {
                let other = shapes[*row].as_ref().map_err(|e| Stop::Skip(e.clone()))?;
                // This arm's terms the earlier row's solved variables stand
                // for, at `depth`.
                let mut solved: HashMap<usize, Term> = HashMap::default();
                for (l, t) in bound {
                    if let Ok(t) = remap_shape(g, t, shape, depth) {
                        solved.insert(*l, t);
                    }
                }
                // The earlier row's levels: its vars bound here in order,
                // the solved ones as this arm's terms.
                let jmap = |t: &Term, to: usize, taken: usize| -> R<Term> {
                    remap(g, t, other.depth, to, &|l| match vars
                        .iter()
                        .take(taken)
                        .position(|&v| v == l)
                    {
                        Some(i) => Some(Term::Var(to - 1 - (depth + i))),
                        None => solved.get(&l).map(|t| t.shift(g, to - depth, 0).ok())?,
                    })?
                    .ok_or_else(|| {
                        Stop::Skip("an overlap mentions a variable it doesn't bind".into())
                    })
                };
                let mut binders: Vec<(Name, Term)> = Vec::new();
                for (i, &v) in vars.iter().enumerate() {
                    let pos = other.tele.iter().position(|&l| l == v).ok_or_else(|| {
                        Stop::Skip("an overlap's variable isn't one of the earlier arm's".into())
                    })?;
                    let ty = jmap(&other.types[pos], depth + i, i)?;
                    binders.push((other.names[pos].clone(), ty));
                }
                let inner = depth + vars.len();
                let mut eq_terms = Vec::new();
                for (e, (lk, s)) in eqs.iter().enumerate() {
                    let x = remap_shape(g, &Term::Var(shape.depth - 1 - lk), shape, inner + e)?;
                    let p = jmap(s, inner + e, vars.len())?;
                    eq_terms.push(Term::Eq(None, Rc::new(x), Rc::new(p)));
                }
                let mut void = Term::Data(lib.void, Vec::new());
                if *guarded {
                    // `c = True → Void`, under the equations.
                    let read = other.guard.as_ref().ok_or_else(|| {
                        Stop::Skip("an earlier arm's condition wasn't read".into())
                    })?;
                    let at = inner + eq_terms.len();
                    let (is_prop, cond) = read.stated();
                    let cond = jmap(cond, at, vars.len())?;
                    void = Term::Pi(
                        "_".into(),
                        Icit::Explicit,
                        Rc::new(guard_holds(self, is_prop, cond)?),
                        Rc::new(void),
                    );
                } else if vars.is_empty() && eq_terms.len() == 1 {
                    return Ok(Term::app(Term::Def(lib.not), eq_terms.pop().expect("one")));
                }
                let mut ty = void;
                for eq in eq_terms.into_iter().rev() {
                    ty = Term::Pi("_".into(), Icit::Explicit, Rc::new(eq), Rc::new(ty));
                }
                for (x, t) in binders.into_iter().rev() {
                    ty = Term::Pi(x, Icit::Explicit, Rc::new(t), Rc::new(ty));
                }
                Ok(ty)
            }
        }
    }
}

/// That a guard's condition holds: `cond = True` for a `Bool`, `cond`
/// itself for a proposition (`dec`).
fn guard_holds(e: &Elaborator, dec: bool, cond: Term) -> R<Term> {
    if dec {
        return Ok(cond);
    }
    let blib = e.branch_lib()?;
    Ok(Term::Eq(
        Some(Rc::new(blib.bool_ty())),
        Rc::new(cond),
        Rc::new(blib.bool_value(true)),
    ))
}

/// [`guard_condition`] before the placeholders are looked at. A chain of
/// comparisons with a computed middle has the middle put back in place, as
/// a guard can't perform, so the equations read as the conjunction
/// written out.
fn guard_terms(
    cx: &mut Ctx,
    binder: Option<&ast::Name>,
    cond: &ast::Expr,
) -> Result<Option<(Term, Option<Term>)>> {
    use crate::logic::Condition;
    if let Some((name, value, body)) = cond.as_chain_let() {
        let (terms, binding) =
            crate::chain::around(cx, name, value, |cx| guard_terms(cx, binder, body))?;
        let Some((prop, as_bool)) = terms else {
            return Ok(None);
        };
        // The `Bool` is read back so the operands a decision bound as
        // variables are applied (`(x => 2 < x) (twice k)` is `3 <= twice k`).
        let as_bool = match as_bool {
            Some(c) => {
                let c = binding.inline(cx, &c)?;
                let value = cx.eval(&c)?;
                Some(cx.quote_folded(&value)?)
            }
            None => None,
        };
        return Ok(Some((binding.inline(cx, &prop)?, as_bool)));
    }
    Ok(Some(match binder {
        Some(h) => (crate::check::if_h_condition(cx, h, cond)?.0, None),
        None => match crate::logic::condition(cx, cond, "if")?.decided_now(cx, cond.span())? {
            Condition::Bool(c) => (crate::logic::true_prop(cx, c.clone())?, Some(c)),
            Condition::Decided { prop, decision } => {
                let c = decision.into_bool(cx, prop.clone())?;
                (prop, Some(c))
            }
            Condition::Conjunction { as_bool, prop, .. } => (prop, Some(as_bool)),
            Condition::Waiting { .. } => return Ok(None),
        },
    }))
}

/// A guard's condition elaborated in its arm's context `cx`, as
/// `check_if_in` does: the proposition it decides (for a `Bool` `c`, `c =
/// True`) and, but for `if h: P`, its `Bool` (a decided proposition's
/// decision's, `a && b`'s reading). `None` if a placeholder is left in
/// them.
fn guard_condition(cx: &mut Ctx, guard: &ast::Guard) -> Result<Option<(Term, Option<Term>)>> {
    let Some((prop, as_bool)) = guard_terms(cx, guard.binder.as_ref(), &guard.cond)? else {
        return Ok(None);
    };
    let level = cx.level();
    let zonk = |t: &Term| -> Option<Term> {
        crate::unify::zonk_in(&cx.u(), level, t, &|_| false, &[]).ok()
    };
    let Some(prop) = zonk(&prop) else {
        return Ok(None);
    };
    let as_bool = match as_bool {
        Some(c) => match zonk(&c) {
            Some(c) => Some(c),
            None => return Ok(None),
        },
        None => None,
    };
    Ok(Some((prop, as_bool)))
}

/// `t`, at `at` in a leaf's context (the row's `tk` variables, the leaf's
/// fields, then binders after them), in the statement's (the row's
/// variables and hypotheses, `base` in all, then the same binders), each
/// term the leaf refined a variable to being that variable again (SW-1071:
/// `Regular a` is `left` again). `None` if a field is left over: the leaf
/// says something of what its patterns bind that the row's variables can't.
fn generalise(
    g: &Ev,
    t: &Term,
    at: usize,
    leaf: &LeafCtx,
    tk: usize,
    base: usize,
) -> R<Option<Term>> {
    // The largest first, so a refined variable inside another's is found
    // within it.
    let mut images: Vec<&(usize, Term)> = leaf.images.iter().collect();
    images.sort_by_key(|(_, t)| std::cmp::Reverse(t.subterms().count()));
    fn go(
        g: &Ev,
        t: &Term,
        under: usize,
        (at, from): (usize, usize),
        images: &[&(usize, Term)],
        cache: &mut Vec<Vec<Term>>,
    ) -> stitchwort_core::budget::Result<Term> {
        g.machine.budget.nesting("equations")?;
        while cache.len() <= under {
            let by = at + cache.len() - from;
            let shifted = images
                .iter()
                .map(|(_, image)| image.shift(g, by, 0))
                .collect::<stitchwort_core::budget::Result<Vec<_>>>()?;
            cache.push(shifted);
        }
        let here = at + under;
        for (i, (level, _)) in images.iter().enumerate() {
            if stitchwort_core::value::same_term(t, &cache[under][i]) {
                return Ok(Term::Var(here - 1 - level));
            }
        }
        rebuild(t, &mut |s, b| {
            Ok(Rc::new(go(g, s, under + b, (at, from), images, cache)?))
        })
    }
    let abstracted = go(g, t, 0, (at, leaf.depth), &images, &mut Vec::new())?;
    let to = base + (at - leaf.depth);
    Ok(remap(g, &abstracted, at, to, &|l| {
        if l < tk {
            Some(Term::Var(to - 1 - l))
        } else if l < leaf.depth {
            None
        } else {
            Some(Term::Var(to - 1 - (base + l - leaf.depth)))
        }
    })?)
}

/// Matches `pat`, a term at `depth` (a helper's equation's left-side
/// argument, its variables that equation's binders), with `t`, solving its
/// variables (by their position among the binders) as terms in `t`'s
/// context (SW-1069).
fn match_pattern(
    g: &Ev,
    pat: &Term,
    depth: usize,
    t: &Term,
    out: &mut HashMap<usize, Term>,
) -> bool {
    match (pat.strip_loc(), t.strip_loc()) {
        (Term::Var(i), _) if *i < depth => {
            let j = depth - 1 - i;
            match out.get(&j) {
                Some(prev) => stitchwort_core::value::same_term(prev, t),
                None => {
                    out.insert(j, t.clone());
                    true
                }
            }
        }
        (Term::Ctor(d, c, xs), other) => {
            let Some((c2, ys)) = ctor_view(g, other, *d) else {
                return false;
            };
            if *c != c2 || xs.len() != ys.len() {
                return false;
            }
            for (x, y) in xs.iter().zip(&ys) {
                if !match_pattern(g, x, depth, y, out) {
                    return false;
                }
            }
            true
        }
        (Term::Nat(_), Term::Ctor(d, ..)) => match ctor_view(g, pat, *d) {
            Some((c, xs)) => match_pattern(
                g,
                &Term::Ctor(*d, c, xs.into_iter().map(Rc::new).collect()),
                depth,
                t,
                out,
            ),
            None => false,
        },
        _ => closed(pat) && stitchwort_core::value::same_term(pat, t),
    }
}

/// `t` with each plain `if` on a decided proposition as the `if` on the
/// decision's `Bool`: `Decidable.elim [p] [a] d (_ => y) (_ => n)` whose
/// branches don't use the proof is `Bool.ifThenElse [a] b (_ => y) (_ =>
/// n)`, `b` the test as a plain `if`'s condition reads it
/// (`bind::Decision::into_bool`: a comparison's `Bool`, `c` for `Bool.decTrue
/// c`, `a && b` for `Decidable.andThen`, else `Decidable.holds [p] d`). The
/// two compute alike (docs/proposals/decidable-record.md §3.1), so the
/// equations are stated, and proved, as for a `Bool` `if`, with the
/// hypotheses `b = True` and `b = False`. An `if h:` (its binder named)
/// stays as it is.
fn plain_ifs(g: &Ev, t: &Term) -> R<Term> {
    let r = g.env.registry();
    let (Some(elim), Some(ite), Some(bool_data), Some((_, fls))) = (
        r.def(Builtin::ElimDec),
        r.def(Builtin::IfThenElse),
        r.data(Builtin::Bool),
        r.ctor(Builtin::False),
    ) else {
        return Ok(t.clone());
    };
    let to_bool = r.def(Builtin::Holds);
    let dec_true = r.def(Builtin::DecTrue);
    let and_then = r.def(Builtin::DecAndThen);
    let bool_ty = Term::Data(bool_data, Vec::new());
    let is = |t: &Term, id: Option<DefId>| matches!(t.strip_loc(), Term::Def(h) if Some(*h) == id);
    // The test of decision `d` of `p`, as a plain `if` reads it.
    fn test(
        g: &Ev,
        d: &Term,
        p: &Term,
        is: &dyn Fn(&Term, Option<DefId>) -> bool,
        ids: (Option<DefId>, Option<DefId>, Option<DefId>, DefId),
        bool_ty: &Term,
        fls: Term,
    ) -> Option<Term> {
        let (to_bool, dec_true, and_then, ite) = ids;
        if let Some(c) = crate::bind::comparison_in(g, d) {
            return Some(c);
        }
        let (head, args) = spine_icit(d.strip_loc());
        if is(head, dec_true) && args.len() == 1 {
            return Some(args[0].0.clone());
        }
        if is(head, and_then) && args.len() == 4 {
            let (pa, pb) = (&args[0].0, &args[1].0);
            let a = test(g, &args[2].0, pa, is, ids, bool_ty, fls.clone())?;
            let Term::Lam(x, i, db) = args[3].0.strip_loc() else {
                return None;
            };
            if db.mentions(0) {
                return None;
            }
            let b = test(
                g,
                db,
                &pb.shift(g, 1, 0).ok()?,
                is,
                ids,
                bool_ty,
                fls.clone(),
            )?;
            let head = Term::app_icit(Term::Def(ite), bool_ty.clone(), Icit::Implicit);
            return Some(apps(
                head,
                [
                    (a, Icit::Explicit),
                    (Term::Lam(x.clone(), *i, Rc::new(b)), Icit::Explicit),
                    (
                        Term::Lam("_".into(), Icit::Explicit, Rc::new(fls)),
                        Icit::Explicit,
                    ),
                ],
            ));
        }
        // With the operands bound, `(x… => d') ops…` (`bind::Bound`).
        if let Term::Ann(lam, pi) = head
            && !args.is_empty()
        {
            let k = args.len();
            let mut body = lam.strip_loc();
            let mut cod = pi.strip_loc();
            let mut names = Vec::new();
            for _ in 0..k {
                match (body, cod) {
                    (Term::Lam(x, i, b), Term::Pi(_, _, _, c)) => {
                        names.push((x.clone(), *i));
                        body = b.strip_loc();
                        cod = c.strip_loc();
                    }
                    _ => return None,
                }
            }
            let Term::Data(_, ps) = cod else {
                return None;
            };
            let inner = test(g, body, ps.first()?, is, ids, bool_ty, fls)?;
            let mut pi_bool = bool_ty.shift(g, k, 0).ok()?;
            let mut pis = Vec::new();
            let mut node = pi.strip_loc();
            for _ in 0..k {
                if let Term::Pi(x, i, a, c) = node {
                    pis.push((x.clone(), *i, a.clone()));
                    node = c.strip_loc();
                }
            }
            for (x, i, a) in pis.into_iter().rev() {
                pi_bool = Term::Pi(x, i, a, Rc::new(pi_bool));
            }
            let lam_bool = names
                .into_iter()
                .rev()
                .fold(inner, |b, (x, i)| Term::Lam(x, i, Rc::new(b)));
            return Some(apps(Term::Ann(Rc::new(lam_bool), Rc::new(pi_bool)), args));
        }
        let to_bool = to_bool?;
        Some(Term::app(
            Term::app_icit(Term::Def(to_bool), p.clone(), Icit::Implicit),
            d.clone(),
        ))
    }
    let ids = (to_bool, dec_true, and_then, ite);
    let fls = Term::Ctor(bool_data, fls, Vec::new());
    Ok(t.rewrite_up(g, &mut |node| {
        let (head, args) = spine_icit(node);
        if !is(head, Some(elim)) || args.len() != 5 {
            return Ok(None);
        }
        let plain = |b: &Term| {
            matches!(b.strip_loc(), Term::Lam(x, _, body) if &**x == "_" && !body.mentions(0))
        };
        if !plain(&args[3].0) || !plain(&args[4].0) {
            return Ok(None);
        }
        let Some(c) = test(g, &args[2].0, &args[0].0, &is, ids, &bool_ty, fls.clone()) else {
            return Ok(None);
        };
        let head = Term::app_icit(Term::Def(ite), args[1].0.clone(), Icit::Implicit);
        Ok(Some(apps(
            head,
            [
                (c, Icit::Explicit),
                (args[3].0.clone(), Icit::Explicit),
                (args[4].0.clone(), Icit::Explicit),
            ],
        )))
    })?)
}

/// `t` as a head applied to arguments, with how each is passed, looking
/// through locations.
fn spine_icit(t: &Term) -> (&Term, Vec<(Term, Icit)>) {
    let mut args = Vec::new();
    let mut head = t.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push(((**a).clone(), *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}

/// `t`, a term under the first `from` binders of an equation whose
/// binder `l` is `vals[l]` (a term at the depth given), at depth `to`.
fn instantiate(g: &Ev, t: &Term, from: usize, vals: &[(Term, usize)], to: usize) -> R<Term> {
    remap(g, t, from, to, &|l| {
        let (v, at) = vals.get(l)?;
        v.shift(g, to - at, 0).ok()
    })?
    .ok_or_else(|| Stop::Skip("a `match`'s alternative couldn't be stated in the branch".into()))
}

/// `t` (under `by` binders more than `e` and `ty`) with each untyped
/// equation `e = p` given the type `ty`.
fn typed_equations(g: &Ev, t: &Term, e: &Term, ty: &Term, by: usize) -> R<Term> {
    g.machine.budget.nesting("equations")?;
    if let Term::Eq(None, a, b) = t {
        let e = e.shift(g, by, 0)?;
        if stitchwort_core::value::same_term(a, &e) {
            return Ok(Term::Eq(
                Some(Rc::new(ty.shift(g, by, 0)?)),
                a.clone(),
                b.clone(),
            ));
        }
    }
    let mut failed = None;
    let out = rebuild(
        t,
        &mut |s, under| match typed_equations(g, s, e, ty, by + under) {
            Ok(t) => Ok(Rc::new(t)),
            Err(stop) => {
                failed = Some(stop);
                Ok(s.clone())
            }
        },
    )?;
    match failed {
        Some(stop) => Err(stop),
        None => Ok(out),
    }
}

/// The names a probe binds a definition's parameters by: their own where
/// they're plain and distinct, else `%eN`.
fn probe_names(binders: &[Binder]) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    for (i, b) in binders.iter().enumerate() {
        let n = b.name.to_string();
        let plain = !n.is_empty()
            && n != "_"
            && !n.starts_with('%')
            && n.chars().next().is_some_and(|c| c.is_alphabetic())
            && !names.contains(&n);
        names.push(if plain { n } else { format!("%e{i}") });
    }
    names
}

/// A fresh name: `base`, or with a digit added if it's taken.
fn fresh(taken: &[Name], base: &str) -> String {
    if !taken.iter().any(|t| &**t == base) {
        return base.to_string();
    }
    (2..)
        .map(|i| format!("{base}{i}"))
        .find(|c| !taken.iter().any(|t| &**t == c.as_str()))
        .expect("some number is free")
}

/// Whether `t` mentions a computation type: `Comp`, `CompIn`, `CompD` or
/// `Delay`.
fn mentions_computation(g: &Ev, t: &Term) -> bool {
    let r = &g.env.registry();
    let comp = r.data(Builtin::Comp);
    let defs = [
        r.def(Builtin::CompIn),
        r.def(Builtin::CompD),
        r.def(Builtin::Delay),
    ];
    t.subterms().any(|(t, _)| match t {
        Term::Data(d, _) => Some(*d) == comp,
        Term::Def(id) => defs.contains(&Some(*id)),
        _ => false,
    })
}

/// Whether a definition of type `ty` (taking `binders`) performs abilities:
/// with its implicit rows `Empty` and its divergences `Total` (`special`),
/// a parameter's type or its result is still a computation.
fn performs_abilities(
    g: &Ev,
    ty: &Term,
    special: &[Option<Term>],
) -> stitchwort_core::budget::Result<bool> {
    let mut v = eval(g, &[], ty)?;
    let mut depth = 0;
    for s in special {
        let Value::Pi(_, _, dom, cod) = force(g, v)? else {
            return Ok(true);
        };
        if let Some(t) = s {
            v = cod.apply(g, eval(g, &[], t)?)?;
            continue;
        }
        if mentions_computation(g, &stitchwort_core::value::quote(g, depth, &dom)?) {
            return Ok(true);
        }
        v = cod.apply(g, Value::var(depth))?;
        depth += 1;
    }
    Ok(mentions_computation(
        g,
        &stitchwort_core::value::quote(g, depth, &v)?,
    ))
}

/// What each parameter is in the equations, if not a variable: an
/// effect-polymorphic definition's are stated at the empty row (§3.2), so
/// an implicit row of abilities is `Empty` and an implicit divergence
/// `Total`.
fn special_params(g: &Ev, binders: &[Binder]) -> Vec<Option<Term>> {
    let r = &g.env.registry();
    let row = r.data(Builtin::Row);
    let div = r.data(Builtin::Divergence);
    let empty = r.ctor(Builtin::RowEmpty);
    let total = r.ctor(Builtin::DivTotal);
    binders
        .iter()
        .map(|b| {
            if b.icit == Icit::Explicit {
                return None;
            }
            match b.ty.strip_loc() {
                Term::Data(d, args) if args.is_empty() && Some(*d) == row => {
                    empty.map(|(d, c)| Term::Ctor(d, c, Vec::new()))
                }
                Term::Data(d, args) if args.is_empty() && Some(*d) == div => {
                    total.map(|(d, c)| Term::Ctor(d, c, Vec::new()))
                }
                _ => None,
            }
        })
        .collect()
}

/// What [`rebuild`] does to each immediate sub-term, given the binders it's
/// under.
type Sub<'a> = &'a mut dyn FnMut(&Rc<Term>, usize) -> stitchwort_core::budget::Result<Rc<Term>>;

/// Rebuilds `t` with each immediate sub-term replaced by `f(sub, binders
/// it's under)`.
fn rebuild(t: &Term, f: Sub<'_>) -> stitchwort_core::budget::Result<Term> {
    let all = |ts: &[Rc<Term>], f: Sub<'_>| {
        ts.iter()
            .map(|t| f(t, 0))
            .collect::<stitchwort_core::budget::Result<Vec<_>>>()
    };
    Ok(match t {
        Term::App(a, b, i) => Term::App(f(a, 0)?, f(b, 0)?, *i),
        Term::Loc(s, inner) => Term::Loc(*s, f(inner, 0)?),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, all(args, f)?),
        Term::Data(d, args) => Term::Data(*d, all(args, f)?),
        Term::Quot(q, args, e) => Term::Quot(*q, all(args, f)?, *e),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, f(a, 0)?, f(b, 1)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, f(b, 1)?),
        Term::Ann(a, b) => Term::Ann(f(a, 0)?, f(b, 0)?),
        Term::Let(x, a, v, b, e) => Term::Let(x.clone(), f(a, 0)?, f(v, 0)?, f(b, 1)?, *e),
        Term::Eq(ty, a, b) => {
            let ty = match ty {
                Some(ty) => Some(f(ty, 0)?),
                None => None,
            };
            Term::Eq(ty, f(a, 0)?, f(b, 0)?)
        }
        Term::J(m, b, p) => Term::J(f(m, 0)?, f(b, 0)?, f(p, 0)?),
        Term::Proj(d, i, t) => Term::Proj(*d, *i, f(t, 0)?),
        Term::Case(i, d, branches) => Term::Case(
            *i,
            *d,
            branches
                .iter()
                .map(|b| {
                    Ok(Branch {
                        names: b.names.clone(),
                        body: match &b.body {
                            Some(body) => Some(f(body, b.names.len())?),
                            None => None,
                        },
                    })
                })
                .collect::<stitchwort_core::budget::Result<Vec<_>>>()?
                .into(),
        ),
        Term::NumCase(i, arms, default) => Term::NumCase(
            *i,
            arms.iter()
                .map(|a| {
                    Ok(NumArm {
                        value: a.value.clone(),
                        body: f(&a.body, 0)?,
                    })
                })
                .collect::<stitchwort_core::budget::Result<Vec<_>>>()?
                .into(),
            f(default, 0)?,
        ),
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => t.clone(),
    })
}

/// `t` with every `let` substituted.
fn zeta(g: &Ev, t: &Term) -> stitchwort_core::budget::Result<Term> {
    g.machine.budget.nesting("equations")?;
    if let Term::Let(_, _, v, b, _) = t {
        let v = zeta(g, v)?;
        let b = zeta(g, b)?;
        return b.instantiate(g, &v);
    }
    rebuild(t, &mut |s, _| Ok(Rc::new(zeta(g, s)?)))
}

/// `zeta(t).subterms().count()`, counted without building it, and whether
/// `zeta(t)` is a variable under its `Loc`s. A chain of `let`s each using
/// the last twice substitutes to a tree exponential in the chain's length,
/// which [`READ_CAP`] must turn down before it is built (SW-2512). `lets`
/// has, per variable in scope (outermost first), what its `let`'s value
/// substitutes as, or `None` for another binder's. Sizes saturate.
fn zeta_size(
    g: &Ev,
    t: &Term,
    lets: &mut Vec<Option<(usize, bool)>>,
) -> stitchwort_core::budget::Result<(usize, bool)> {
    g.machine.budget.nesting("equations")?;
    match t {
        Term::Var(i) => Ok(lets
            .len()
            .checked_sub(i + 1)
            .and_then(|l| lets[l])
            .unwrap_or((1, true))),
        Term::Loc(_, inner) => {
            let (size, var) = zeta_size(g, inner, lets)?;
            Ok((size.saturating_add(1), var))
        }
        Term::Let(_, _, v, b, _) => {
            // `instantiate` puts a variable in bare, else the value whole.
            let (size, var) = zeta_size(g, v, lets)?;
            lets.push(Some(if var { (1, true) } else { (size, false) }));
            let r = zeta_size(g, b, lets);
            lets.pop();
            r
        }
        _ => {
            let mut children = Vec::new();
            t.for_each_child(|c, under| children.push((c, under)));
            let mut size: usize = 1;
            for (c, under) in children {
                lets.extend(std::iter::repeat_n(None, under));
                let r = zeta_size(g, c, lets);
                lets.truncate(lets.len() - under);
                size = size.saturating_add(r?.0);
            }
            Ok((size, false))
        }
    }
}

/// `t` (at `depth`) with the effect library's plumbing at the empty row and
/// `Total` computed away (`bindDv Total Empty c next` is `next c`, `CompIn
/// Empty a` is `a`), so an effect-polymorphic definition's equation reads
/// as pure code (§3.2).
fn pure_at_empty(g: &Ev, t: &Term, depth: usize) -> stitchwort_core::budget::Result<Term> {
    g.machine.budget.nesting("equations")?;
    let r = &g.env.registry();
    let plumbing = [
        Builtin::CompIn,
        Builtin::DoneIn,
        Builtin::BindIn,
        Builtin::CompD,
        Builtin::DoneD,
        Builtin::BindDv,
        Builtin::LiftD,
        Builtin::LiftIn,
    ]
    .map(|b| r.def(b));
    let t = rebuild(t, &mut |s, under| {
        Ok(Rc::new(pure_at_empty(g, s, depth + under)?))
    })?;
    let (head, args) = t.spine();
    let Term::Def(id) = head else {
        return Ok(t);
    };
    if args.is_empty() || !plumbing.contains(&Some(*id)) {
        return Ok(t);
    }
    // One step of its case tree, where its row or divergence is known.
    let env: Vec<Value> = (0..depth).map(Value::var).collect();
    let value = eval(g, &env, &t)?;
    let stepped = force(g, value)?;
    let back = stitchwort_core::value::quote_folded(g, depth, &stepped)?;
    if matches!(back.spine().0, Term::Def(d) if d == id) {
        return Ok(t);
    }
    let back = beta_rec(g, back)?;
    pure_at_empty(g, &back, depth)
}

/// The levels of a context of `depth` variables `t` mentions.
fn levels_in(t: &Term, depth: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for (s, binders) in t.subterms() {
        if let Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) = s
            && *i >= binders
            && let Some(l) = depth.checked_sub(1 + (i - binders))
            && !out.contains(&l)
        {
            out.push(l);
        }
    }
    out
}

/// `t`, a term in a shape's context, in a context of `to` variables whose
/// first are the shape's variables in order.
fn remap_shape(g: &Ev, t: &Term, shape: &Shape, to: usize) -> R<Term> {
    remap(g, t, shape.depth, to, &|l| {
        shape
            .tele
            .iter()
            .position(|&x| x == l)
            .map(|j| Term::Var(to - 1 - j))
    })?
    .ok_or_else(|| Stop::Skip("its statement mentions a variable its arm doesn't bind".into()))
}

/// `t`, in a context of `from` variables, with each free variable at level
/// `l` replaced by `map(l)`, a term in a context of `to` variables; `None`
/// if one isn't mapped, or is a case's scrutinee.
fn remap(
    g: &Ev,
    t: &Term,
    from: usize,
    to: usize,
    map: &dyn Fn(usize) -> Option<Term>,
) -> stitchwort_core::budget::Result<Option<Term>> {
    struct Missing;
    fn go(
        g: &Ev,
        t: &Term,
        k: usize,
        from: usize,
        map: &dyn Fn(usize) -> Option<Term>,
    ) -> stitchwort_core::budget::Result<std::result::Result<Term, Missing>> {
        g.machine.budget.nesting("equations")?;
        macro_rules! sub {
            ($t:expr, $k:expr) => {
                match go(g, $t, $k, from, map)? {
                    Ok(t) => Rc::new(t),
                    Err(m) => return Ok(Err(m)),
                }
            };
        }
        Ok(Ok(match t {
            Term::Var(i) if *i < k => Term::Var(*i),
            Term::Var(i) => {
                let Some(level) = from.checked_sub(1 + (i - k)) else {
                    return Ok(Err(Missing));
                };
                match map(level) {
                    Some(t) => t.shift(g, k, 0)?,
                    None => return Ok(Err(Missing)),
                }
            }
            Term::Def(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => t.clone(),
            Term::Data(d, args) => {
                let mut out = Vec::new();
                for a in args {
                    out.push(sub!(a, k));
                }
                Term::Data(*d, out)
            }
            Term::Ctor(d, c, args) => {
                let mut out = Vec::new();
                for a in args {
                    out.push(sub!(a, k));
                }
                Term::Ctor(*d, *c, out)
            }
            Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, sub!(a, k), sub!(b, k + 1)),
            Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, sub!(b, k + 1)),
            Term::App(f, a, i) => Term::App(sub!(f, k), sub!(a, k), *i),
            Term::Ann(e, ty) => Term::Ann(sub!(e, k), sub!(ty, k)),
            Term::Let(x, a, v, b, e) => {
                Term::Let(x.clone(), sub!(a, k), sub!(v, k), sub!(b, k + 1), *e)
            }
            Term::Eq(ty, a, b) => {
                let ty = match ty {
                    Some(ty) => Some(sub!(ty, k)),
                    None => None,
                };
                Term::Eq(ty, sub!(a, k), sub!(b, k))
            }
            Term::J(m, b, p) => Term::J(sub!(m, k), sub!(b, k), sub!(p, k)),
            Term::Proj(d, i, t) => Term::Proj(*d, *i, sub!(t, k)),
            Term::Quot(form, args, erased) => {
                let mut out = Vec::new();
                for a in args {
                    out.push(sub!(a, k));
                }
                Term::Quot(*form, out, *erased)
            }
            Term::Loc(span, t) => Term::Loc(*span, sub!(t, k)),
            // A case on a free variable can't be moved to a context where
            // it's a term; one on a bound variable stays.
            Term::Case(i, d, branches) if *i < k => {
                let mut out = Vec::new();
                for b in branches.iter() {
                    out.push(Branch {
                        names: b.names.clone(),
                        body: match &b.body {
                            Some(body) => Some(sub!(body, k + b.names.len())),
                            None => None,
                        },
                    });
                }
                Term::Case(*i, *d, out.into())
            }
            Term::NumCase(i, arms, default) if *i < k => {
                let mut out = Vec::new();
                for a in arms.iter() {
                    out.push(NumArm {
                        value: a.value.clone(),
                        body: sub!(&a.body, k),
                    });
                }
                Term::NumCase(*i, out.into(), sub!(default, k))
            }
            Term::Case(..) | Term::NumCase(..) => return Ok(Err(Missing)),
        }))
    }
    let _ = to;
    Ok(go(g, t, 0, from, map)?.ok())
}

/// What `%rec` stands for in a `decreasing` definition's equations, at
/// `depth`: `(y… [decreasing]) => f y…`.
fn rec_term(d: &Def, depth: usize) -> Term {
    let n = d.binders.len();
    let inner = depth + n + 1;
    let mut call = apps(
        Term::Def(d.f),
        (0..n).map(|i| (Term::Var(inner - 1 - (depth + i)), d.binders[i].icit)),
    );
    if d.mark_rec.get() {
        call = Term::app_icit(call, Term::Var(0), Icit::Auto);
    }
    let mut names: Vec<(Name, Icit)> = d.binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
    names.push(("decreasing".into(), Icit::Auto));
    lams(&names, call)
}

/// Applications of `%rec`'s lambda, reduced: `((y => f y) a)` is `f a`.
fn beta_rec(g: &Ev, t: Term) -> stitchwort_core::budget::Result<Term> {
    g.machine.budget.nesting("equations")?;
    let (head, args) = {
        let (h, a) = t.spine();
        (h.clone(), a.into_iter().cloned().collect::<Vec<Term>>())
    };
    if let Term::Lam(..) = head
        && !args.is_empty()
    {
        let mut f = head;
        for a in args {
            let a = beta_rec(g, a)?;
            f = match f.strip_loc() {
                Term::Lam(_, _, body) => body.instantiate(g, &a)?,
                _ => Term::app(f, a),
            };
        }
        return Ok(f);
    }
    let go = |t: &Rc<Term>| -> stitchwort_core::budget::Result<Rc<Term>> {
        Ok(Rc::new(beta_rec(g, (**t).clone())?))
    };
    let all = |ts: &[Rc<Term>]| -> stitchwort_core::budget::Result<Vec<Rc<Term>>> {
        ts.iter().map(go).collect()
    };
    Ok(match &t {
        Term::App(f, a, i) => Term::App(go(f)?, go(a)?, *i),
        Term::Loc(s, inner) => Term::Loc(*s, go(inner)?),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, all(args)?),
        Term::Data(d, args) => Term::Data(*d, all(args)?),
        Term::Quot(f, args, e) => Term::Quot(*f, all(args)?, *e),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a)?, go(b)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b)?),
        Term::Ann(a, b) => Term::Ann(go(a)?, go(b)?),
        Term::Let(x, a, v, b, e) => Term::Let(x.clone(), go(a)?, go(v)?, go(b)?, *e),
        Term::Eq(ty, a, b) => Term::Eq(ty.as_ref().map(go).transpose()?, go(a)?, go(b)?),
        Term::J(m, b, p) => Term::J(go(m)?, go(b)?, go(p)?),
        Term::Proj(d, i, x) => Term::Proj(*d, *i, go(x)?),
        _ => t,
    })
}

/// `t` with the marks of [`Def::mark_rec`] dropped: `f y… p` is `f y…`.
fn unmark(g: &Ev, d: &Def, t: &Term) -> stitchwort_core::budget::Result<Term> {
    let n = d.binders.len();
    let f = d.f;
    fn go(g: &Ev, f: DefId, n: usize, t: &Term) -> stitchwort_core::budget::Result<Term> {
        g.machine.budget.nesting("equations")?;
        if let Term::App(head, _, Icit::Auto) = t {
            let (h, args) = t.spine();
            if matches!(h.strip_loc(), Term::Def(x) if *x == f) && args.len() == n + 1 {
                return go(g, f, n, head);
            }
        }
        let sub = |t: &Rc<Term>| -> stitchwort_core::budget::Result<Rc<Term>> {
            Ok(Rc::new(go(g, f, n, t)?))
        };
        let all = |ts: &[Rc<Term>]| -> stitchwort_core::budget::Result<Vec<Rc<Term>>> {
            ts.iter().map(sub).collect()
        };
        Ok(match t {
            Term::App(a, b, i) => Term::App(sub(a)?, sub(b)?, *i),
            Term::Loc(s, inner) => Term::Loc(*s, sub(inner)?),
            Term::Ctor(d, c, args) => Term::Ctor(*d, *c, all(args)?),
            Term::Data(d, args) => Term::Data(*d, all(args)?),
            Term::Quot(q, args, e) => Term::Quot(*q, all(args)?, *e),
            Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, sub(a)?, sub(b)?),
            Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, sub(b)?),
            Term::Ann(a, b) => Term::Ann(sub(a)?, sub(b)?),
            Term::Let(x, a, v, b, e) => Term::Let(x.clone(), sub(a)?, sub(v)?, sub(b)?, *e),
            Term::Eq(ty, a, b) => Term::Eq(ty.as_ref().map(sub).transpose()?, sub(a)?, sub(b)?),
            Term::J(m, b, p) => Term::J(sub(m)?, sub(b)?, sub(p)?),
            Term::Proj(d, i, x) => Term::Proj(*d, *i, sub(x)?),
            _ => t.clone(),
        })
    }
    if !d.mark_rec.get() {
        return Ok(t.clone());
    }
    go(g, f, n, t)
}

enum Found {
    None,
    /// A leaf whose body mentions what the arm's patterns don't bind.
    Refined,
    /// A leaf whose body is a further case tree.
    Match,
    /// A leaf whose body uses the proof that an earlier arm's condition is
    /// false.
    GuardProof,
    /// The right side, and the size of the leaf's body it came from.
    Rhs(Term, usize),
    /// A right side over [`READ_CAP`] (and [`too_large`]) with its `let`s
    /// substituted: that size, and its leaf body's.
    TooLarge(usize, usize),
}

/// Why a row whose body uses the proof that an earlier arm's condition is
/// false has no equation.
const GUARD_PROOF: &str = "its body uses the proof that an earlier arm's condition is false, \
                           which the equation has no hypothesis for (D2180)";

/// What [`find_rhs`] finds: the leaf, and for a guarded row whether its
/// condition is tested by `Decidable.elim`. `unit` is `()`, the value of a
/// `Bool` guard's branches' binder; `blocked` the tree's levels that are
/// proofs that an earlier arm's condition is false.
struct Sought {
    found: Found,
    guard_dec: Option<bool>,
    unit: Option<Term>,
    blocked: Vec<usize>,
}

/// The `if` a guarded row's condition is tested by, at its guard node in a
/// tree: `Bool.ifThenElse [a] c t e` or `Decidable.elim [p] [a] d y n`,
/// its head and arguments, and its branches' bodies, each under the one
/// binder of its lambda (a `Bool`'s `()`, or the proof).
struct GuardIf {
    dec: bool,
    head: Term,
    args: Vec<(Term, Icit)>,
    then: Term,
    otherwise: Term,
}

fn guard_if(g: &Ev, t: &Term) -> R<GuardIf> {
    let r = g.env.registry();
    let (head, args) = spine_icit(t.strip_loc());
    let is = |b: Builtin| matches!(head.strip_loc(), Term::Def(h) if r.def(b) == Some(*h));
    let dec = if is(Builtin::IfThenElse) && args.len() == 4 {
        false
    } else if is(Builtin::ElimDec) && args.len() == 5 {
        true
    } else {
        return skip(
            "an arm's condition isn't elaborated as `Bool.ifThenElse` or `Decidable.elim`, the \
             two the generator follows",
        );
    };
    let body = |t: &Term| match t.strip_loc() {
        Term::Lam(_, _, b) => Ok((**b).clone()),
        _ => skip("an arm's condition's branch isn't a function as elaborated"),
    };
    let n = args.len();
    Ok(GuardIf {
        dec,
        then: body(&args[n - 2].0)?,
        otherwise: body(&args[n - 1].0)?,
        head: head.clone(),
        args,
    })
}

/// Looks through the tree, with the arm's arguments (`fmap`, terms at
/// `to`), for a leaf of row `k` whose body says its right side in the
/// arm's variables. Below another row's guard it goes on in the `else`;
/// below row `k`'s own, in the `then`, its binder at level `to`.
#[allow(clippy::too_many_arguments)]
fn find_rhs(
    g: &Ev,
    d: &Def,
    k: usize,
    t: &Term,
    fmap: &mut Vec<Option<Term>>,
    path: &mut Vec<u32>,
    to: usize,
    out: &mut Sought,
) -> R<()> {
    g.machine.budget.nesting("equations")?;
    if matches!(out.found, Found::Rhs(..)) {
        return Ok(());
    }
    if let Some(row) = d.row_at(path)
        && (row == k || !d.is_ancestor(row, k))
    {
        if row != k {
            return Ok(());
        }
        let depth = fmap.len();
        let body = t.strip_loc();
        if matches!(body, Term::Case(..) | Term::NumCase(..)) {
            out.found = Found::Match;
            return Ok(());
        }
        if !out.blocked.is_empty() && levels_in(t, depth).iter().any(|l| out.blocked.contains(l)) {
            if matches!(out.found, Found::None | Found::Refined) {
                out.found = Found::GuardProof;
            }
            return Ok(());
        }
        let mapped = remap(g, t, depth, to, &|l| fmap[l].clone())?;
        match mapped {
            Some(rhs) => {
                let rhs = if matches!(d.kind, Kind::Decreasing { .. }) {
                    beta_rec(g, rhs)?
                } else {
                    rhs
                };
                let rhs = if d.special.iter().any(Option::is_some) {
                    pure_at_empty(g, &rhs, to)?
                } else {
                    rhs
                };
                // `let`s substituted, as goals show them (§3.1). The
                // branches a row's splits take are smaller, and §10
                // bounds what is stated; [`READ_CAP`] bounds what is
                // built on the way.
                let arm_size = t.subterms().count();
                let (size, _) = zeta_size(g, &rhs, &mut Vec::new())?;
                out.found = if size > READ_CAP && too_large(size, arm_size) {
                    Found::TooLarge(size, arm_size)
                } else {
                    Found::Rhs(zeta(g, &rhs)?, arm_size)
                };
            }
            None => {
                if matches!(out.found, Found::None) {
                    out.found = Found::Refined;
                }
            }
        }
        return Ok(());
    }
    if let Some(j) = d.guard_row_at(path) {
        let node = guard_if(g, t)?;
        if j == k {
            out.guard_dec.get_or_insert(node.dec);
            let mut inner = Vec::new();
            for v in fmap.iter() {
                inner.push(match v {
                    Some(v) => Some(v.shift(g, 1, 0)?),
                    None => None,
                });
            }
            inner.push(Some(Term::Var(0)));
            path.push(crate::GUARD_THEN);
            let r = find_rhs(g, d, k, &node.then, &mut inner, path, to + 1, out);
            path.pop();
            return r;
        }
        // The rows below row `j` are in its `else`.
        let binder = if node.dec {
            out.blocked.push(fmap.len());
            None
        } else {
            out.unit.clone()
        };
        fmap.push(binder);
        path.push(crate::GUARD_ELSE);
        let r = find_rhs(g, d, k, &node.otherwise, fmap, path, to, out);
        path.pop();
        fmap.pop();
        if node.dec {
            out.blocked.pop();
        }
        return r;
    }
    match t.strip_loc() {
        Term::Case(ix, data, branches) => {
            let depth = fmap.len();
            let x = depth - 1 - ix;
            let known = fmap[x].as_ref().and_then(|v| ctor_view(g, v, *data));
            for (c, b) in branches.iter().enumerate() {
                let Some(body) = &b.body else { continue };
                let fields: Vec<Option<Term>> = match &known {
                    Some((kc, args)) if *kc == c => args.iter().cloned().map(Some).collect(),
                    Some(_) => continue,
                    None => vec![None; b.names.len()],
                };
                let mark = fmap.len();
                fmap.extend(fields);
                path.push(c as u32);
                find_rhs(g, d, k, body, fmap, path, to, out)?;
                path.pop();
                fmap.truncate(mark);
            }
            Ok(())
        }
        Term::NumCase(ix, arms, default) => {
            let depth = fmap.len();
            let x = depth - 1 - ix;
            let known = fmap[x].as_ref().and_then(|v| match v.strip_loc() {
                Term::Nat(n) => Some((**n).clone()),
                _ => None,
            });
            for (i, a) in arms.iter().enumerate() {
                if known.as_ref().is_some_and(|n| *n != *a.value) {
                    continue;
                }
                path.push(i as u32);
                find_rhs(g, d, k, &a.body, fmap, path, to, out)?;
                path.pop();
            }
            if !known
                .as_ref()
                .is_some_and(|n| arms.iter().any(|a| *a.value == *n))
            {
                path.push(arms.len() as u32);
                find_rhs(g, d, k, default, fmap, path, to, out)?;
                path.pop();
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// `t` as constructor `c` of `data` applied to fields, if it is one (a
/// number, of `Nat`, as `Zero` or `Succ`).
fn ctor_view(g: &Ev, t: &Term, data: DataId) -> Option<(usize, Vec<Term>)> {
    match t.strip_loc() {
        Term::Ctor(d, c, args) if *d == data => {
            Some((*c, args.iter().map(|a| (**a).clone()).collect()))
        }
        Term::Nat(n) if g.env.builtins().nat == Some(data) => {
            if n.bits() == 0 {
                Some((0, Vec::new()))
            } else {
                Some((1, vec![Term::Nat(Rc::new((**n).clone() - 1u32))]))
            }
        }
        _ => None,
    }
}

impl Elaborator {
    /// The equations of the local definitions lifted from the declaration
    /// (or group) just admitted: `helpers` are their keys, ids and spans.
    /// In a `decreasing` definition they take `%rec`, which a statement
    /// can't use, so they get none (§3.2).
    pub(crate) fn local_equations(
        &mut self,
        helpers: &[(String, DefId, Span)],
        decreasing: bool,
    ) -> Result<()> {
        let asts = std::mem::take(&mut *self.decl.local_asts.borrow_mut());
        for (key, id, _) in helpers {
            let Some((_, def)) = asts.iter().find(|(k, _)| k == key) else {
                continue;
            };
            if decreasing {
                for s in source_suffixes(&def.equations) {
                    self.tables.equation_skips.push((
                        *id,
                        s,
                        "a local definition in a `decreasing` definition takes `%rec`, which a \
                         statement can't use; the owner's own equations cover it"
                            .to_string(),
                    ));
                }
                continue;
            }
            let kind = if self.kernel.def(*id).opaque() {
                Kind::Opaque
            } else {
                Kind::Plain
            };
            self.generate_equations_keyed(*id, &def.signature, &def.equations, kind, Some(key))?;
        }
        Ok(())
    }

    /// Whether a top-level definition's equations are made on demand, not
    /// with it: the core's and the library's (D2178's fallback). The core
    /// loads at every start, the playground's included, and a library
    /// file without the check cache with whatever uses it, so their
    /// equations, made eagerly, cost every run (+11% of a small program's
    /// steps). A program's own stay eager. Local definitions' too.
    pub(crate) fn defers_equations(&self) -> bool {
        self.unit.loading_prelude
    }

    /// Makes the equations of the library's and the core's definitions
    /// with these keys (a reference to `f.eq2` names `f`), from their
    /// source in the library index, if they aren't made yet.
    pub(crate) fn ensure_equations<'a>(
        &mut self,
        keys: impl IntoIterator<Item = &'a String>,
    ) -> Result<()> {
        let keys: Vec<String> = keys.into_iter().cloned().collect();
        for key in keys {
            self.ensure_equations_of(&key)?;
        }
        Ok(())
    }

    fn ensure_equations_of(&mut self, key: &str) -> Result<()> {
        if self.tables.equations_done.iter().any(|k| k == key) {
            return Ok(());
        }
        let Some(lib) = &self.session.library else {
            return Ok(());
        };
        let index = lib.index.clone();
        let Some(f) = index.owner(key) else {
            return Ok(());
        };
        let Some(id) = self.lookup_def(key) else {
            return Ok(());
        };
        if self.kernel.def(id).state() != stitchwort_core::globals::State::Final {
            return Ok(());
        }
        let file = &index.files[f];
        let Some(span) = (file.names.iter()).find(|n| n.key == key).map(|n| n.span) else {
            return Ok(());
        };
        let Some((signature, equations)) = crate::project::grouped(&file.module.decls)
            .into_iter()
            .find(|(d, _)| matches!(d, Decl::Signature { name, .. } if name.span == span))
        else {
            return Ok(());
        };
        self.tables.equations_done.push(key.to_string());
        // Made with the definition already (a library file replayed from
        // the check cache, whose own proofs named them).
        if source_suffixes(equations)
            .first()
            .is_some_and(|s| self.scope.get(&format!("{key}.{s}")).is_some())
        {
            return Ok(());
        }
        let saved_item = self.unit.module.item.take();
        // Made as a declaration of its own, whatever is being elaborated:
        // from an empty `Decl`, and what it leaves there is dropped.
        let outer = std::mem::take(&mut self.decl);
        let decreasing = matches!(
            signature,
            Decl::Signature {
                decreasing: Some(_),
                ..
            }
        );
        let opaque = matches!(signature, Decl::Signature { opaque: true, .. });
        // In the defining file's scope (its imports, the library's names,
        // the library's full names), whoever asks: a program, `search`, or
        // another library file (SW-1068).
        let result = self.in_library_file(f, |e| {
            if decreasing {
                e.decreasing_equations(id, signature, equations, Some(key))
            } else {
                let kind = if opaque { Kind::Opaque } else { Kind::Plain };
                e.generate_equations_keyed(id, signature, equations, kind, Some(key))
            }
        });
        self.decl = outer;
        self.unit.module.item = saved_item;
        result
    }

    /// The equations of the library file being loaded's own definitions
    /// that its proofs name: made, as on demand, once the definitions are.
    pub(crate) fn ensure_loading_file_equations(&mut self) {
        let (Some(f), Some(lib)) = (self.scope.loading, &self.session.library) else {
            return;
        };
        let needs = lib.index.files[f].equation_needs.clone();
        if !needs.is_empty() {
            let _ = self.ensure_equations(&needs);
        }
    }

    /// Makes every put-off equation of the core and the loaded library
    /// files: for listing them all (`search`, `doc`).
    pub fn generate_deferred_equations(&mut self) -> Result<()> {
        let Some(lib) = &self.session.library else {
            return Ok(());
        };
        let index = lib.index.clone();
        let mut files = vec![0];
        files.extend(lib.order.iter().copied());
        for f in files {
            let keys: Vec<String> = crate::project::grouped(&index.files[f].module.decls)
                .into_iter()
                .filter(|(d, e)| {
                    matches!(
                        d,
                        Decl::Signature {
                            theorem: false,
                            instance: false,
                            ..
                        }
                    ) && source_arms(e).is_some()
                })
                .filter_map(|(d, _)| {
                    let Decl::Signature { name, .. } = d else {
                        return None;
                    };
                    (index.files[f].names.iter())
                        .find(|n| n.span == name.span)
                        .map(|n| n.key.clone())
                })
                .collect();
            self.ensure_equations(&keys)?;
        }
        Ok(())
    }

    /// The leaves of the definition's case tree, when none were recorded
    /// (its equations made on demand, after it): its arms compiled again,
    /// as its body was, with a probe for each body, under a root of their
    /// own, and read off the log.
    fn recompute_leaves(
        &mut self,
        d: &Def,
        arms: &[SourceArm],
        root: Span,
    ) -> R<Option<Vec<Leaf>>> {
        let n = d.binders.len();
        let pred_ty = eval(&self.ev(), &[], &pis(&d.binders, Term::Sort(Sort::Prop)))?;
        let nav = self.present.nav.take();
        let lambda_warnings = self.attempt.lambda_warnings.borrow().len();
        let branch_errors = self.attempt.branch_errors.borrow().len();
        let drafts = self.attempt.drafts.borrow().len();
        let logged = self.decl.leaf_log.borrow().leaves.len();
        let saved_root = self.decl.leaf_log.borrow_mut().enter_root(root);
        let result = (|| -> Result<Option<()>> {
            let mut cx = Ctx::new(self, root);
            cx.bind_hidden("%P".into(), pred_ty.clone());
            for (i, b) in d.binders.iter().enumerate() {
                let ty = eval(&cx.g(), &cx.env[1..], &b.ty)?;
                if let Some(value) = &d.special[i] {
                    let ty_term = cx.quote(&ty)?;
                    cx.define(
                        Some(&d.names[i]),
                        b.name.clone(),
                        ty,
                        ty_term,
                        value.clone(),
                    )?;
                } else {
                    cx.bind(&d.names[i], ty);
                }
                cx.set_kind(b.icit);
            }
            let goal_term = apps(
                Term::Var(n),
                (0..n).map(|i| (Term::Var(n - 1 - i), d.binders[i].icit)),
            );
            let goal = cx.eval(&goal_term)?;
            let var = |text: &str, span: Span| {
                Expr::Var(ast::Name {
                    text: text.into(),
                    span,
                })
            };
            let expr = Expr::Match {
                scrutinees: d
                    .columns
                    .iter()
                    .map(|&i| Scrutinee {
                        name: None,
                        expr: var(&d.names[i], root),
                    })
                    .collect(),
                alts: arms
                    .iter()
                    .map(|a| {
                        let mut known: Vec<String> = d.names.clone();
                        known.extend(
                            crate::written_names(&a.patterns)
                                .into_iter()
                                .map(str::to_string),
                        );
                        Alt {
                            guard: a.guard.clone(),
                            patterns: a.patterns.clone(),
                            // An absurd arm stays absurd: given a probe body,
                            // its `()` would be the unit pattern.
                            body: (a.rhs.as_ref()).map(|rhs| probe_body(Some(rhs), a.span, &known)),
                            span: a.span,
                        }
                    })
                    .collect(),
                span: root,
                kind: MatchKind::Match,
            };
            match crate::matching::in_tree(&mut cx, &expr, &goal) {
                None => Ok(None),
                Some(r) => r.map(|_| Some(())),
            }
        })();
        self.present.nav = nav;
        self.attempt
            .lambda_warnings
            .borrow_mut()
            .truncate(lambda_warnings);
        self.attempt
            .branch_errors
            .borrow_mut()
            .truncate(branch_errors);
        // A `match` below an arm that was lifted, not compiled into the
        // tree: its helper is dropped (its leaves are below the arm's, so
        // the arm's leaf is found as before).
        self.attempt.drafts.borrow_mut().truncate(drafts);
        let leaves = {
            let mut log = self.decl.leaf_log.borrow_mut();
            log.leave_root(saved_root);
            let leaves: Vec<Leaf> = log.leaves[logged..]
                .iter()
                .filter(|l| l.root == root)
                .cloned()
                .collect();
            log.leaves.truncate(logged);
            leaves
        };
        self.clear_metas();
        match result {
            Ok(Some(())) => Ok(Some(leaves)),
            Ok(None) => Ok(None),
            Err(e) => Err(Stop::Error(e)),
        }
    }
}

// ------------------------------------------------------------- overlaps

enum Overlap {
    Disjoint,
    /// The earlier row takes every value this one does: its variables
    /// solved by this one's terms.
    Covers {
        bound: HashMap<usize, Term>,
    },
    /// The earlier row's variables the equations need, the equations (a
    /// level of this arm's shape, equal to a term in the earlier row's),
    /// and the earlier row's variables solved by terms of this one's.
    Meets {
        vars: Vec<usize>,
        eqs: Vec<(usize, Term)>,
        bound: HashMap<usize, Term>,
    },
    Unknown,
    /// The overlap's equation would be on an indexed family.
    Indexed,
}

/// Whether an earlier row (`other`) overlaps this one (`shape`): their
/// left sides unified, the earlier's variables solved by this one's terms
/// where they can be, and the rest left as equations of this one's
/// variables.
fn overlap(g: &Ev, other: &Shape, shape: &Shape) -> R<Overlap> {
    let mut bound: HashMap<usize, Term> = HashMap::default();
    let mut eqs: Vec<(usize, Term)> = Vec::new();
    // Every column, so one that's disjoint settles it even when another
    // can't be read.
    let mut worst = Unified::Yes;
    for (a, b) in other.lhs.iter().zip(&shape.lhs) {
        match unify(g, a, other.depth, b, shape.depth, &mut bound, &mut eqs) {
            Unified::Yes => {}
            Unified::No => return Ok(Overlap::Disjoint),
            Unified::Indexed => worst = Unified::Indexed,
            Unified::Unknown => {
                if !matches!(worst, Unified::Indexed) {
                    worst = Unified::Unknown;
                }
            }
        }
    }
    match worst {
        Unified::Indexed => return Ok(Overlap::Indexed),
        Unified::Unknown => return Ok(Overlap::Unknown),
        _ => {}
    }
    if eqs.is_empty() {
        // Every value this arm takes, the earlier one does too.
        return Ok(Overlap::Covers { bound });
    }
    // The earlier row's variables the equations mention and nothing solved,
    // and those their types mention.
    let mut vars: Vec<usize> = Vec::new();
    let mut pending: Vec<usize> = eqs
        .iter()
        .flat_map(|(_, s)| levels_in(s, other.depth))
        .collect();
    while let Some(l) = pending.pop() {
        if vars.contains(&l) || bound.contains_key(&l) {
            continue;
        }
        let Some(pos) = other.tele.iter().position(|&x| x == l) else {
            return Ok(Overlap::Unknown);
        };
        vars.push(l);
        pending.extend(levels_in(&other.types[pos], other.depth));
    }
    vars.sort_by_key(|l| other.tele.iter().position(|x| x == l));
    Ok(Overlap::Meets { vars, eqs, bound })
}

enum Unified {
    Yes,
    No,
    Unknown,
    Indexed,
}

/// Unifies `a` (in the earlier row's context) with `b` (in this one's).
fn unify(
    g: &Ev,
    a: &Term,
    adepth: usize,
    b: &Term,
    bdepth: usize,
    bound: &mut HashMap<usize, Term>,
    eqs: &mut Vec<(usize, Term)>,
) -> Unified {
    let a = a.strip_loc();
    let b = b.strip_loc();
    // A variable of the earlier row matches anything.
    if let Term::Var(i) = a {
        let la = adepth - 1 - i;
        return match bound.get(&la) {
            None => {
                bound.insert(la, b.clone());
                Unified::Yes
            }
            Some(t) if stitchwort_core::value::same_term(t, b) => Unified::Yes,
            Some(_) => Unified::Unknown,
        };
    }
    if let Term::Var(i) = b {
        let lb = bdepth - 1 - i;
        if eqs.iter().any(|(l, _)| *l == lb) {
            return Unified::Unknown;
        }
        // On an indexed family, `x = C …` may compare values of different
        // types (D2185).
        if let Some(d) = data_of(a)
            && !g.data(d).indices().is_empty()
        {
            return Unified::Indexed;
        }
        eqs.push((lb, a.clone()));
        return Unified::Yes;
    }
    if let (Some(data), _) | (_, Some(data)) = (data_of(a), data_of(b))
        && let (Some((ca, xs)), Some((cb, ys))) = (ctor_view(g, a, data), ctor_view(g, b, data))
    {
        if ca != cb {
            return Unified::No;
        }
        for (x, y) in xs.iter().zip(&ys) {
            match unify(g, x, adepth, y, bdepth, bound, eqs) {
                Unified::Yes => {}
                other => return other,
            }
        }
        return Unified::Yes;
    }
    match (a, b) {
        (Term::Refl, Term::Refl) => Unified::Yes,
        (Term::Nat(x), Term::Nat(y)) => {
            if x == y {
                Unified::Yes
            } else {
                Unified::No
            }
        }
        _ if closed(a) && stitchwort_core::value::same_term(a, b) => Unified::Yes,
        _ => Unified::Unknown,
    }
}

fn closed(t: &Term) -> bool {
    levels_in(t, usize::MAX).is_empty()
}

/// Why a branch below an `if` or a `match` on a closed term (`if cost == 5`,
/// no variable in it) isn't stated: the kernel would compute the term to
/// read the hypothesis's type, and again checking its proof, work that
/// checking the program never needed (SW-1077, `check_work`). The call
/// takes one way, which computing the definition finds.
const CLOSED_SPLIT: &str = "it is below an `if` or `match` on a term that mentions no variable, \
     which the kernel would compute to state the branch's hypothesis; computing the definition \
     takes the branch it goes down";

fn data_of(t: &Term) -> Option<DataId> {
    match t.strip_loc() {
        Term::Ctor(d, _, _) => Some(*d),
        _ => None,
    }
}

/// Whether `ty` is `a = b` in `Bool` with `a` computing to `b`: a proof
/// that is `rfl` wherever the kernel ignores proofs.
fn is_computed_bool_eq(g: &Ev, depth: usize, ty: &Value) -> R<bool> {
    Ok(match force(g, ty.clone())? {
        Value::Eq(ty, a, b) => {
            matches!(force(g, (*ty).clone())?,
                Value::Data(d, _) if g.env.registry().is_data(Builtin::Bool, d))
                && stitchwort_core::value::conv(g, depth, &a, &b)?
        }
        _ => false,
    })
}

/// A character literal `MkChar k rfl`'s character.
fn char_literal(g: &Ev, t: &Term) -> Option<char> {
    let char_data = g.env.registry().data(Builtin::Char)?;
    match t.strip_loc() {
        Term::Ctor(d, 0, args) if *d == char_data && args.len() == 2 => {
            let Term::Nat(code) = args[0].strip_loc() else {
                return None;
            };
            if !matches!(args[1].strip_loc(), Term::Refl) {
                return None;
            }
            u32::try_from(&**code).ok().and_then(char::from_u32)
        }
        _ => None,
    }
}

/// Whether `h` only says a variable isn't some number (`n ≠ k`).
fn number_overlap(h: &Hyp) -> bool {
    matches!(h, Hyp::Overlap { vars, eqs, guarded: false, .. }
        if vars.is_empty() && eqs.len() == 1 && matches!(eqs[0].1.strip_loc(), Term::Nat(_)))
}

/// The earlier rows that only say a variable isn't some character, merged
/// into one `c ∉ […]` per variable (§3.2), where the first of them was.
fn merge_chars(g: &Ev, hyps: Vec<Hyp>, shapes: &[std::result::Result<Shape, String>]) -> Vec<Hyp> {
    let _ = shapes;
    let single = |h: &Hyp| -> Option<(usize, usize, char)> {
        match h {
            Hyp::Overlap {
                row,
                vars,
                eqs,
                guarded: false,
                ..
            } if vars.is_empty() && eqs.len() == 1 => {
                let (l, s) = &eqs[0];
                char_literal(g, s).map(|c| (*row, *l, c))
            }
            _ => None,
        }
    };
    let mut out: Vec<Hyp> = Vec::new();
    for h in hyps {
        if let Some((row, level, c)) = single(&h) {
            if let Some(Hyp::Listed { rows, .. }) = out
                .iter_mut()
                .find(|o| matches!(o, Hyp::Listed { level: l, .. } if *l == level))
            {
                rows.push((row, c));
                continue;
            }
            out.push(Hyp::Listed {
                level,
                rows: vec![(row, c)],
            });
            continue;
        }
        out.push(h);
    }
    out
}

// ---------------------------------------------------------------- proofs

/// The library's declarations the proofs use.
struct Lib {
    void: DataId,
    char: DataId,
    or: DataId,
    not: DefId,
    mem: DefId,
    exfalso: DefId,
}

impl Lib {
    fn new(g: &Ev) -> Option<Lib> {
        let r = &g.env.registry();
        Some(Lib {
            void: r.data(Builtin::Void)?,
            char: r.data(Builtin::Char)?,
            or: r.data(Builtin::Or)?,
            not: r.def(Builtin::Not)?,
            mem: r.def(Builtin::ListMem)?,
            exfalso: r.def(Builtin::VoidExfalso)?,
        })
    }

    /// The list of these characters, as a literal is.
    fn char_list(&self, g: &Ev, chars: &Rc<[char]>) -> R<Term> {
        if let Some(text) = g.env.builtins().compact_literals() {
            return Ok(stitchwort_core::chars::term(
                text,
                &stitchwort_core::chars::Chars::whole(chars.clone()),
            ));
        }
        let list = g
            .env
            .registry()
            .data(Builtin::List)
            .ok_or_else(|| Stop::Skip("`List` isn't loaded yet".into()))?;
        let mut t = Term::Ctor(list, 0, Vec::new());
        for c in chars.iter().rev() {
            let ch = Term::ctor(
                self.char,
                0,
                vec![Term::Nat(Rc::new(BigUint::from(u32::from(*c)))), Term::Refl],
            );
            t = Term::ctor(list, 1, vec![ch, t]);
        }
        Ok(t)
    }
}

/// A value in the proof's context: a variable (by level), a constructor,
/// a number, a term (at the depth given), or `%rec`.
#[derive(Clone)]
enum PV {
    Var(usize),
    Ctor(DataId, usize, Vec<PV>),
    Nat(Rc<BigUint>),
    Term(Term, usize),
    Rec,
}

/// The proof of one equation, built by walking the definition's tree.
struct Walk<'a> {
    e: &'a Elaborator,
    d: &'a Def,
    k: usize,
    shapes: &'a [std::result::Result<Shape, String>],
    hyps: &'a [Hyp],
    /// The equation's variables and hypotheses.
    base: usize,
    tk: usize,
    /// The statement's `lhs = rhs`, at `base`.
    body: &'a Term,
    /// What each variable of the proof's context is (itself, unless a
    /// split refined it).
    pvals: Vec<PV>,
    /// The numbers a variable is known not to be.
    apart: HashMap<usize, Vec<BigUint>>,
    /// `None` before the core's logic is loaded: then no leaf of an earlier
    /// arm can be refuted.
    lib: Option<Lib>,
    /// For a branch: the statement's left side and the proof (both at
    /// `base`) that the row's right side is the branch's, which the row's
    /// leaf goes on along.
    then: Then,
    /// The arm's shape.
    shape: &'a Shape,
    /// A walk that only reads row `k`'s leaves ([`Elaborator::refined_leaves`]):
    /// them, so far.
    dry: Option<Vec<LeafCtx>>,
    /// Below a guard, the branch of its `if` the proof is about, at the
    /// depth given: the goal there is that it is the right side, not `f
    /// lhs`, which is stuck on the condition.
    under: Option<(Term, usize)>,
}

impl<'a> Walk<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        e: &'a Elaborator,
        d: &'a Def,
        k: usize,
        shape: &'a Shape,
        shapes: &'a [std::result::Result<Shape, String>],
        hyps: &'a [Hyp],
        base: usize,
        body: &'a Term,
    ) -> R<Walk<'a>> {
        let lib = Lib::new(&e.ev());
        Ok(Walk {
            e,
            d,
            k,
            shapes,
            hyps,
            base,
            tk: shape.tele.len(),
            body,
            pvals: (0..base).map(PV::Var).collect(),
            apart: HashMap::default(),
            lib,
            then: Then::Own,
            shape,
            dry: None,
            under: None,
        })
    }

    fn g(&self) -> Ev<'a> {
        self.e.ev()
    }

    fn lib(&self) -> R<&Lib> {
        self.lib
            .as_ref()
            .ok_or_else(|| Stop::Skip("the core's logic isn't loaded yet".into()))
    }

    fn depth(&self) -> usize {
        self.pvals.len()
    }

    /// A term of the arm's shape as a value here (at the start).
    fn pv_of(&self, t: &Term, shape: &Shape) -> R<PV> {
        Ok(match t.strip_loc() {
            Term::Var(i) => {
                let l = shape.depth - 1 - i;
                let j = shape.tele.iter().position(|&x| x == l).ok_or_else(|| {
                    Stop::Skip("its left side mentions a variable it doesn't take".into())
                })?;
                PV::Var(j)
            }
            Term::Ctor(d, c, args) => PV::Ctor(
                *d,
                *c,
                args.iter()
                    .map(|a| self.pv_of(a, shape))
                    .collect::<R<_>>()?,
            ),
            Term::Nat(n) => PV::Nat(n.clone()),
            other => PV::Term(
                remap_shape(&self.g(), other, shape, self.depth())?,
                self.depth(),
            ),
        })
    }

    /// `v` with every refined variable replaced by what it is.
    fn resolve(&self, v: &PV) -> PV {
        match v {
            PV::Var(l) => match &self.pvals[*l] {
                PV::Var(m) if m == l => v.clone(),
                other => self.resolve(&other.clone()),
            },
            PV::Ctor(d, c, args) => {
                PV::Ctor(*d, *c, args.iter().map(|a| self.resolve(a)).collect())
            }
            other => other.clone(),
        }
    }

    /// `v` as a term here.
    fn term(&self, v: &PV) -> R<Term> {
        let depth = self.depth();
        Ok(match self.resolve(v) {
            PV::Var(l) => Term::Var(depth - 1 - l),
            PV::Ctor(d, c, args) => Term::Ctor(
                d,
                c,
                args.iter()
                    .map(|a| Ok(Rc::new(self.term(a)?)))
                    .collect::<R<_>>()?,
            ),
            PV::Nat(n) => Term::Nat(n),
            PV::Term(t, at) => {
                // Refinements since it was made are substituted.
                let shifted = t.shift(&self.g(), depth - at, 0)?;
                self.refine(&shifted)?
            }
            PV::Rec => return skip("`%rec` escaped into a proof term"),
        })
    }

    /// A term here with every refined variable replaced by what it is.
    fn refine(&self, t: &Term) -> R<Term> {
        let depth = self.depth();
        let pvals = &self.pvals;
        let any_refined = (0..depth).any(|l| !matches!(&pvals[l], PV::Var(m) if *m == l));
        if !any_refined {
            return Ok(t.clone());
        }
        let mut cache: Vec<Option<Term>> = vec![None; depth];
        for (l, slot) in cache.iter_mut().enumerate() {
            *slot = Some(match &pvals[l] {
                PV::Var(m) if *m == l => Term::Var(depth - 1 - l),
                other => self.term(&other.clone())?,
            });
        }
        remap(&self.g(), t, depth, depth, &|l| cache[l].clone())?
            .ok_or_else(|| Stop::Skip("a refined term couldn't be read".into()))
    }

    /// The proof for the tree `t` (in a context of the definition's
    /// `fvals`), here.
    fn go(&mut self, t: &Term, fvals: &mut Vec<PV>, path: &mut Vec<u32>) -> R<Term> {
        self.g().machine.budget.nesting("equations")?;
        if let Some(row) = self.d.row_at(path)
            && (row == self.k || !self.d.is_ancestor(row, self.k))
        {
            if self.dry.is_some() {
                return self.read_leaf(row, fvals, t, path);
            }
            return self.leaf(row, fvals, path);
        }
        if let Some(j) = self.d.guard_row_at(path) {
            return self.guard(j, t, fvals, path);
        }
        match t.strip_loc() {
            Term::Case(ix, data, branches) => {
                let x = fvals.len() - 1 - ix;
                let v = self.resolve(&fvals[x]);
                let nat = self.g().env.builtins().nat == Some(*data);
                match v {
                    PV::Ctor(d, c, args) if d == *data => {
                        let Some(body) = &branches[c].body else {
                            return skip("a branch it takes is impossible");
                        };
                        let mark = fvals.len();
                        fvals.extend(args);
                        path.push(c as u32);
                        let r = self.go(body, fvals, path);
                        path.pop();
                        fvals.truncate(mark);
                        r
                    }
                    PV::Nat(n) if nat => {
                        let (c, args) = if n.bits() == 0 {
                            (0, Vec::new())
                        } else {
                            (1, vec![PV::Nat(Rc::new((*n).clone() - 1u32))])
                        };
                        let Some(body) = &branches[c].body else {
                            return skip("a branch it takes is impossible");
                        };
                        let mark = fvals.len();
                        fvals.extend(args);
                        path.push(c as u32);
                        let r = self.go(body, fvals, path);
                        path.pop();
                        fvals.truncate(mark);
                        r
                    }
                    PV::Var(t) if t < self.tk || t >= self.base => {
                        if !self.g().data(*data).indices().is_empty() {
                            return skip(
                                "proving it needs a split on an indexed family, which stage 1a \
                                 doesn't make",
                            );
                        }
                        let depth = self.depth();
                        let mut out = Vec::new();
                        for (c, b) in branches.iter().enumerate() {
                            let Some(body) = &b.body else {
                                out.push(Branch {
                                    names: b.names.clone(),
                                    body: None,
                                });
                                continue;
                            };
                            let m = b.names.len();
                            let fields: Vec<PV> = (depth..depth + m).map(PV::Var).collect();
                            let saved = self.pvals.clone();
                            self.pvals.extend(fields.iter().cloned());
                            self.pvals[t] = PV::Ctor(*data, c, fields.clone());
                            let mark = fvals.len();
                            fvals.extend(fields);
                            path.push(c as u32);
                            let r = self.go(body, fvals, path);
                            path.pop();
                            fvals.truncate(mark);
                            self.pvals = saved;
                            out.push(Branch {
                                names: b.names.clone(),
                                body: Some(Rc::new(r?)),
                            });
                        }
                        Ok(Term::Case(depth - 1 - t, *data, out.into()))
                    }
                    _ => skip(
                        "the definition's case tree is stuck on something that isn't a variable",
                    ),
                }
            }
            Term::NumCase(ix, arms, default) => {
                let x = fvals.len() - 1 - ix;
                let v = self.resolve(&fvals[x]);
                match v {
                    PV::Nat(n) => match arms.iter().position(|a| *a.value == *n) {
                        Some(i) => {
                            path.push(i as u32);
                            let r = self.go(&arms[i].body, fvals, path);
                            path.pop();
                            r
                        }
                        None => {
                            path.push(arms.len() as u32);
                            let r = self.go(default, fvals, path);
                            path.pop();
                            r
                        }
                    },
                    PV::Var(t) => {
                        let known = self.apart.get(&t).cloned().unwrap_or_default();
                        if arms.iter().all(|a| known.contains(&a.value)) {
                            path.push(arms.len() as u32);
                            let r = self.go(default, fvals, path);
                            path.pop();
                            return r;
                        }
                        let depth = self.depth();
                        let mut out = Vec::new();
                        for (i, a) in arms.iter().enumerate() {
                            let saved = self.pvals.clone();
                            self.pvals[t] = PV::Nat(a.value.clone());
                            path.push(i as u32);
                            let r = self.go(&a.body, fvals, path);
                            path.pop();
                            self.pvals = saved;
                            out.push(NumArm {
                                value: a.value.clone(),
                                body: Rc::new(r?),
                            });
                        }
                        let saved = self.apart.get(&t).cloned();
                        self.apart
                            .entry(t)
                            .or_default()
                            .extend(arms.iter().map(|a| (*a.value).clone()));
                        path.push(arms.len() as u32);
                        let r = self.go(default, fvals, path);
                        path.pop();
                        match saved {
                            Some(s) => {
                                self.apart.insert(t, s);
                            }
                            None => {
                                self.apart.remove(&t);
                            }
                        }
                        Ok(Term::NumCase(depth - 1 - t, out.into(), Rc::new(r?)))
                    }
                    _ => skip(
                        "the definition's number case is stuck on something that isn't a variable",
                    ),
                }
            }
            _ => skip("a leaf of the definition's case tree belongs to no arm"),
        }
    }

    /// At a leaf of row `row` of a dry walk ([`Elaborator::refined_leaves`]):
    /// row `k`'s leaf body `t`, read here, with what the walk refined.
    fn read_leaf(&mut self, row: usize, fvals: &[PV], t: &Term, path: &[u32]) -> R<Term> {
        if row != self.k {
            return Ok(Term::Refl);
        }
        if matches!(t.strip_loc(), Term::Case(..) | Term::NumCase(..)) {
            return skip("its right side is a `match` compiled into the case tree");
        }
        let g = self.g();
        let depth = self.depth();
        let mut terms: Vec<Option<Term>> = Vec::new();
        for v in fvals {
            terms.push(Some(match v {
                PV::Rec => rec_term(self.d, depth),
                v => self.term(v)?,
            }));
        }
        let body = remap(&g, t, fvals.len(), depth, &|l| terms[l].clone())?
            .ok_or_else(|| Stop::Skip("a leaf's body couldn't be read".into()))?;
        let body = if matches!(self.d.kind, Kind::Decreasing { .. }) {
            beta_rec(&g, body)?
        } else {
            body
        };
        let body = if self.d.special.iter().any(Option::is_some) {
            pure_at_empty(&g, &body, depth)?
        } else {
            body
        };
        let size = t.subterms().count();
        let (full, _) = zeta_size(&g, &body, &mut Vec::new())?;
        if full > READ_CAP && too_large(full, size) {
            return skip(too_large_to_read(full, size));
        }
        let body = zeta(&g, &body)?;
        let mut images = Vec::new();
        for j in 0..self.tk {
            if !matches!(&self.pvals[j], PV::Var(m) if *m == j) {
                images.push((j, self.term(&PV::Var(j))?));
            }
        }
        if let Some(found) = &mut self.dry {
            found.push(LeafCtx {
                path: path.to_vec(),
                depth,
                body,
                images,
                size,
            });
        }
        Ok(Term::Refl)
    }

    /// The proof at a leaf of row `row`.
    fn leaf(&mut self, row: usize, fvals: &[PV], path: &[u32]) -> R<Term> {
        if row == self.k {
            let own = match self.d.kind {
                // Below a guard the branch computes to the right side.
                _ if self.under.is_some() => Term::Refl,
                Kind::Decreasing { unfold, .. } => {
                    let mut args = Vec::new();
                    for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
                        if let Some(i) = self.d.param_of_tree_level(level) {
                            args.push((self.term(v)?, self.d.binders[i].icit));
                        }
                    }
                    apps(Term::Def(unfold), args)
                }
                _ => Term::Refl,
            };
            // A branch: on along its proof that the row's right side is
            // the branch's, `J (z _ => f lhs = z) own then` (here, where a
            // case tree may only be at the top).
            let depth = self.depth();
            let g = self.g();
            let (lhs, then) = match &self.then {
                Then::Own => return Ok(own),
                Then::One(lhs, then) => (lhs, then.shift(&g, depth - self.base, 0)?),
                // This leaf's own proof (SW-1071), from its context (the
                // row's variables, its fields, the branch's binders) to
                // here (the statement's binders, then the same fields).
                Then::PerLeaf(lhs, proofs) => {
                    let p = proofs.iter().find(|p| p.path == path).ok_or_else(|| {
                        Stop::Skip("a leaf of its arm wasn't read before its proof".into())
                    })?;
                    let (tk, at) = (self.tk, self.tk + self.hyps.len());
                    let fields = depth - self.base;
                    if p.depth != tk + fields {
                        return skip("a leaf of its arm has other fields than when it was read");
                    }
                    let from = p.depth + (self.base - at);
                    let q = remap(&g, &p.q, from, depth, &|l| {
                        Some(Term::Var(
                            depth
                                - 1
                                - if l < tk {
                                    l
                                } else if l < p.depth {
                                    self.base + (l - tk)
                                } else {
                                    at + (l - p.depth)
                                },
                        ))
                    })?
                    .ok_or_else(|| Stop::Skip("a leaf's proof couldn't be moved".into()))?;
                    (lhs, q)
                }
            };
            let lhs = match &self.under {
                Some((u, at)) => self.refine(&u.shift(&g, depth - at, 0)?)?,
                None => self.refine(&lhs.shift(&g, depth - self.base, 0)?)?,
            };
            let then = self.refine(&then)?;
            let motive = Term::Lam(
                "z".into(),
                Icit::Explicit,
                Rc::new(Term::Lam(
                    "e".into(),
                    Icit::Explicit,
                    Rc::new(Term::Eq(
                        None,
                        Rc::new(lhs.shift(&g, 2, 0)?),
                        Rc::new(Term::Var(1)),
                    )),
                )),
            );
            return Ok(Term::J(Rc::new(motive), Rc::new(own), Rc::new(then)));
        }
        if !self.d.earlier(self.k).contains(&row) {
            return skip("a later arm's leaf is reached from its left side");
        }
        // An earlier row: its hypothesis is refuted here.
        let (i, h) = self.hyp_of(row)?;
        let depth = self.depth();
        let hyp = Term::Var(depth - 1 - (self.tk + i));
        let void = match h {
            Hyp::Overlap { guarded: true, .. } | Hyp::NotGuard { .. } | Hyp::Guard => {
                return skip("a guarded earlier arm's leaf is reached outside its condition");
            }
            Hyp::Overlap { vars, eqs, .. } => self.overlap_applied(row, fvals, hyp, vars, eqs)?,
            Hyp::Listed { level, rows } => {
                let j = self
                    .shapes_tele(level)
                    .ok_or_else(|| Stop::Skip("an equation's variable isn't the arm's".into()))?;
                let x = self.resolve(&PV::Var(j));
                let at = rows
                    .iter()
                    .position(|(r, _)| *r == row)
                    .expect("found above");
                let c = rows[at].1;
                let lit = PV::Ctor(
                    self.lib()?.char,
                    0,
                    vec![
                        PV::Nat(Rc::new(BigUint::from(u32::from(c)))),
                        PV::Term(Term::Refl, depth),
                    ],
                );
                // `List.Any (y => y = x)`: the element first.
                let or = self.lib()?.or;
                let mut proof = Term::ctor(or, 0, vec![self.eq_proof(&lit, &x)?]);
                for _ in 0..at {
                    proof = Term::ctor(or, 1, vec![proof]);
                }
                Term::app(hyp, proof)
            }
        };
        let goal = self.goal_here()?;
        Ok(apps(
            Term::Def(self.lib()?.exfalso),
            [(goal, Icit::Implicit), (void, Icit::Explicit)],
        ))
    }

    /// The equation proved here: the statement's, or below a guard, that
    /// the branch is its right side.
    fn goal_here(&self) -> R<Term> {
        let g = self.g();
        let depth = self.depth();
        let body = self.body.shift(&g, depth - self.base, 0)?;
        match (&self.under, &body) {
            (Some((u, at)), Term::Eq(ty, _, rhs)) => self.refine(&Term::Eq(
                ty.clone(),
                Rc::new(u.shift(&g, depth - at, 0)?),
                rhs.clone(),
            )),
            (Some(_), _) => skip("an equation's statement isn't an equation"),
            (None, _) => self.refine(&body),
        }
    }

    /// The right side of the equation proved, here.
    fn rhs_here(&self) -> R<Term> {
        match self.goal_here()? {
            Term::Eq(_, _, ref rhs) => Ok((**rhs).clone()),
            _ => skip("an equation's statement isn't an equation"),
        }
    }

    /// The hypothesis for earlier row `row`, and its position among the
    /// statement's.
    fn hyp_of(&self, row: usize) -> R<(usize, &'a Hyp)> {
        self.hyps
            .iter()
            .enumerate()
            .find(|(_, h)| match h {
                Hyp::Overlap { row: r, .. } | Hyp::NotGuard { row: r, .. } => *r == row,
                Hyp::Listed { rows, .. } => rows.iter().any(|(r, _)| *r == row),
                Hyp::Guard => false,
            })
            .ok_or_else(|| {
                Stop::Skip("an earlier arm is reached that no hypothesis rules out".into())
            })
    }

    /// An overlap hypothesis `hyp` for earlier row `row`, applied to that
    /// row's variables as they are here and the proofs of its equations:
    /// `Void`, or for a guarded row, `c = True → Void`.
    fn overlap_applied(
        &self,
        row: usize,
        fvals: &[PV],
        hyp: Term,
        vars: &[usize],
        eqs: &[(usize, Term)],
    ) -> R<Term> {
        let other = self.shapes[row]
            .as_ref()
            .map_err(|e| Stop::Skip(e.clone()))?;
        // The earlier row's variables, as they are here.
        let mut jvals: HashMap<usize, PV> = HashMap::default();
        for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
            if let Some(p) = self.d.param_of_tree_level(level) {
                self.match_pv(&other.lhs[p], other.depth, v, &mut jvals)?;
            }
        }
        let mut args = Vec::new();
        for v in vars {
            let pv = jvals
                .get(v)
                .ok_or_else(|| Stop::Skip("an earlier arm's variable has no value here".into()))?;
            args.push((self.term(pv)?, Icit::Explicit));
        }
        for (lk, s) in eqs {
            let j = self
                .shapes_tele(lk)
                .ok_or_else(|| Stop::Skip("an equation's variable isn't the arm's".into()))?;
            let y = self.pv_in(s, other, &jvals)?;
            args.push((self.eq_proof(&PV::Var(j), &y)?, Icit::Explicit));
        }
        Ok(apps(hyp, args))
    }

    /// `t` (a term of the definition's tree, in a context of `fvals`), here.
    fn read_tree(&self, t: &Term, fvals: &[PV]) -> R<Term> {
        let depth = self.depth();
        let mut terms: Vec<Option<Term>> = Vec::new();
        for v in fvals {
            terms.push(Some(match v {
                PV::Rec => rec_term(self.d, depth),
                v => self.term(v)?,
            }));
        }
        let g = self.g();
        let read = remap(&g, t, fvals.len(), depth, &|l| terms[l].clone())?
            .ok_or_else(|| Stop::Skip("a term of the definition's tree couldn't be read".into()))?;
        if matches!(self.d.kind, Kind::Decreasing { .. }) {
            Ok(beta_rec(&g, read)?)
        } else {
            Ok(read)
        }
    }

    /// The proof for `body`, a branch of a guard's `if` whose binder is
    /// `binder`: that it, read here, is the right side.
    fn branch(
        &mut self,
        body: &Term,
        binder: PV,
        side: u32,
        fvals: &mut Vec<PV>,
        path: &mut Vec<u32>,
    ) -> R<Term> {
        fvals.push(binder);
        let read = self.read_tree(body, fvals);
        let read = match read {
            Ok(r) => r,
            Err(e) => {
                fvals.pop();
                return Err(e);
            }
        };
        let saved = self.under.replace((read, self.depth()));
        path.push(side);
        let r = self.go(body, fvals, path);
        path.pop();
        fvals.pop();
        self.under = saved;
        r
    }

    /// At the guard node of row `j`, `t`, the `if` on its condition: for
    /// row `k` itself, on into the `then` along its `guard` hypothesis; for
    /// an earlier row, into the `else` along the hypothesis that the
    /// condition is false here. A proof that the `if` is the right side,
    /// carried to the statement's left side at the top.
    fn guard(&mut self, j: usize, t: &Term, fvals: &mut Vec<PV>, path: &mut Vec<u32>) -> R<Term> {
        let g = self.g();
        let node = guard_if(&g, t)?;
        let read = guard_if(&g, &self.read_tree(t, fvals)?)?;
        let depth = self.depth();
        let blib = self.e.branch_lib()?;
        let unit = || -> R<PV> {
            let (d, c) = g
                .env
                .registry()
                .ctor(Builtin::Trivial)
                .ok_or_else(|| Stop::Skip("no `Unit`".into()))?;
            Ok(PV::Term(Term::Ctor(d, c, Vec::new()), depth))
        };
        let recorded = self.shapes[j].as_ref().ok().and_then(|s| s.guard.as_ref());
        // For a condition stated as its proposition but tested by its
        // `Bool` `holds d`: `P` and `d` here, to go between the two.
        let decided = match recorded {
            Some(r) if r.prop.is_some() => {
                Some(blib.decided_view(&g, &read.args[1].0)?.ok_or_else(|| {
                    Stop::Skip(
                        "an arm's condition is a decided proposition in its statement but not \
                     where the definition tests it"
                            .into(),
                    )
                })?)
            }
            _ => None,
        };
        if recorded.map(|r| r.dec) != Some(node.dec) {
            return skip(
                "an arm's condition is elaborated differently in different cases of the \
                 definition (`Bool.ifThenElse` in one, `Decidable.elim` in another)",
            );
        }
        if self.dry.is_some() {
            // Reading row `k`'s leaves: through the branch towards them,
            // where the binder can't be a hypothesis.
            let (body, side) = if j == self.k {
                (&node.then, crate::GUARD_THEN)
            } else {
                (&node.otherwise, crate::GUARD_ELSE)
            };
            if node.dec && body.mentions(0) {
                return skip(
                    "a guarded arm an earlier arm overlaps, whose leaves are read one by one, \
                     uses its condition's proof",
                );
            }
            fvals.push(unit()?);
            path.push(side);
            let r = self.go(body, fvals, path);
            path.pop();
            fvals.pop();
            return r;
        }
        let z = self.rhs_here()?;
        let proof = if j == self.k {
            let i = self
                .hyps
                .iter()
                .position(|h| matches!(h, Hyp::Guard))
                .ok_or_else(|| Stop::Skip("its condition has no hypothesis".into()))?;
            let level = self.tk + i;
            let hyp = Term::Var(depth - 1 - level);
            let binder = if node.dec { PV::Var(level) } else { unit()? };
            let q = self.branch(&node.then, binder, crate::GUARD_THEN, fvals, path)?;
            if node.dec {
                let uniq = if node.then.mentions(0)
                    && !self.e.proof_is_inert_in(&node.then, None, depth)?
                {
                    Some(
                        self.e
                            .uniqueness(&blib, &read.args[0].0, &read.args[2].0, depth)?,
                    )
                } else {
                    None
                };
                blib.dec_step(&g, &read.args, true, uniq.as_ref(), None, hyp, depth, &z, q)?
            } else {
                let hyp = match &decided {
                    Some(view) => view.lemma(&blib, 0, hyp)?,
                    None => hyp,
                };
                blib.ite_step(&g, &read.head, &read.args, hyp, &z, q)?
            }
        } else {
            if !self.d.earlier(self.k).contains(&j) {
                return skip("a later arm's condition is reached from its left side");
            }
            let (i, h) = self.hyp_of(j)?;
            let hyp = Term::Var(depth - 1 - (self.tk + i));
            // `c = True → Void` (`P → Void`) for an overlap, else `None`:
            // the hypothesis is that the condition is false.
            let refutes = match h {
                Hyp::Overlap {
                    vars,
                    eqs,
                    guarded: true,
                    ..
                } => Some(self.overlap_applied(j, fvals, hyp.clone(), vars, eqs)?),
                Hyp::NotGuard { .. } => None,
                _ => return skip("a guarded earlier arm's hypothesis isn't about its condition"),
            };
            if !node.dec {
                let q = self.branch(&node.otherwise, unit()?, crate::GUARD_ELSE, fvals, path)?;
                match refutes {
                    None => {
                        // `Q` for the failure of `¬Q`: `¬¬Q` is `e => e q`.
                        let hyp = match (&decided, recorded.and_then(|r| r.negated.as_ref())) {
                            (Some(view), Some(_)) => {
                                let by = Term::Lam(
                                    "e".into(),
                                    Icit::Explicit,
                                    Rc::new(Term::app(Term::Var(0), hyp.shift(&g, 1, 0)?)),
                                );
                                view.lemma(&blib, 1, by)?
                            }
                            (Some(view), None) => view.lemma(&blib, 1, hyp)?,
                            (None, _) => hyp,
                        };
                        blib.ite_step(&g, &read.head, &read.args, hyp, &z, q)?
                    }
                    // `Bool.inspect c (y => ite y t e = z) (h => exfalso
                    // (refutes h)) (_ => q)`.
                    Some(refutes) => {
                        let inspect = blib
                            .inspect
                            .ok_or_else(|| Stop::Skip("`Bool.inspect` isn't loaded yet".into()))?;
                        let call = |cond: Term, by: usize| -> R<Term> {
                            let mut out = read.head.clone();
                            for (i, (a, icit)) in read.args.iter().enumerate() {
                                let a = if i == 1 {
                                    cond.clone()
                                } else {
                                    a.shift(&g, by, 0)?
                                };
                                out = Term::app_icit(out, a, *icit);
                            }
                            Ok(out)
                        };
                        let ty = |by: usize| -> R<Option<Rc<Term>>> {
                            Ok(Some(Rc::new(read.args[0].0.shift(&g, by, 0)?)))
                        };
                        let lam = |x: &str, body: Term| {
                            Term::Lam(x.into(), Icit::Explicit, Rc::new(body))
                        };
                        let motive = lam(
                            "y",
                            Term::Eq(
                                ty(1)?,
                                Rc::new(call(Term::Var(0), 1)?),
                                Rc::new(z.shift(&g, 1, 0)?),
                            ),
                        );
                        let goal_true = Term::Eq(
                            ty(1)?,
                            Rc::new(call(blib.bool_value(true), 1)?),
                            Rc::new(z.shift(&g, 1, 0)?),
                        );
                        let holds = match &decided {
                            Some(view) => view.shift(&g, 1)?.lemma(&blib, 2, Term::Var(0))?,
                            None => Term::Var(0),
                        };
                        let yes = lam(
                            "h",
                            blib.exfalso(goal_true, Term::app(refutes.shift(&g, 1, 0)?, holds)),
                        );
                        let no = lam("h", q.shift(&g, 1, 0)?);
                        apps(
                            Term::Def(inspect),
                            [read.args[1].0.clone(), motive, yes, no]
                                .into_iter()
                                .map(|t| (t, Icit::Explicit)),
                        )
                    }
                }
            } else {
                // `Decidable.elimEq d y n z (h => exfalso …) (r => q)`, the
                // `else` read with its binder `r`.
                let r_level = depth;
                self.pvals.push(PV::Var(r_level));
                let q = self.branch(
                    &node.otherwise,
                    PV::Var(r_level),
                    crate::GUARD_ELSE,
                    fvals,
                    path,
                );
                self.pvals.pop();
                let q = q?;
                let normal = match recorded {
                    Some(r) if r.unfolded => self
                        .e
                        .bool_equation(&read.args[0].0, depth)?
                        .and_then(|eq| blib.bool_test(&eq)),
                    _ => blib.bool_test(&read.args[0].0),
                };
                let void = match (&refutes, &normal) {
                    (Some(refutes), _) => Term::app(refutes.shift(&g, 1, 0)?, Term::Var(0)),
                    (None, Some((b, x))) => {
                        blib.normal_void(&g, b.shift(&g, 1, 0)?, *x, hyp.shift(&g, 1, 0)?)?
                    }
                    (None, None) => Term::app(hyp.shift(&g, 1, 0)?, Term::Var(0)),
                };
                let y = &read.args[3].0;
                let Term::Lam(_, _, y_body) = y.strip_loc() else {
                    return skip("an `if`'s branch isn't a function as elaborated");
                };
                let goal_y = Term::Eq(
                    Some(Rc::new(read.args[1].0.shift(&g, 1, 0)?)),
                    y_body.clone(),
                    Rc::new(z.shift(&g, 1, 0)?),
                );
                let ey = Term::Lam(
                    "h".into(),
                    Icit::Explicit,
                    Rc::new(blib.exfalso(goal_y, void)),
                );
                let en = Term::Lam("r".into(), Icit::Explicit, Rc::new(q));
                blib.elim_eq(&read.args, z.clone(), ey, en)?
            }
        };
        if self.under.is_some() {
            return Ok(proof);
        }
        // At the top: from `f lhs`, which computes to the `if` (through
        // `unfold` for `decreasing`), `J (w _ => f lhs = w) own proof`.
        let own = match self.d.kind {
            Kind::Decreasing { unfold, .. } => {
                let mut args = Vec::new();
                for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
                    if let Some(i) = self.d.param_of_tree_level(level) {
                        args.push((self.term(v)?, self.d.binders[i].icit));
                    }
                }
                apps(Term::Def(unfold), args)
            }
            _ => Term::Refl,
        };
        let lhs = match self.goal_here()? {
            Term::Eq(_, ref lhs, _) => (**lhs).clone(),
            _ => return skip("an equation's statement isn't an equation"),
        };
        let motive = Term::Lam(
            "w".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "e".into(),
                Icit::Explicit,
                Rc::new(Term::Eq(
                    None,
                    Rc::new(lhs.shift(&g, 2, 0)?),
                    Rc::new(Term::Var(1)),
                )),
            )),
        );
        Ok(Term::J(Rc::new(motive), Rc::new(own), Rc::new(proof)))
    }

    /// The position in the equation's variables of the arm's level `l`.
    fn shapes_tele(&self, l: &usize) -> Option<usize> {
        self.shape.tele.iter().position(|x| x == l)
    }

    /// Matches an earlier row's left-side term (at `depth`) with a value
    /// here, solving its variables.
    fn match_pv(&self, t: &Term, depth: usize, v: &PV, out: &mut HashMap<usize, PV>) -> R<()> {
        let v = self.resolve(v);
        match t.strip_loc() {
            Term::Var(i) => {
                out.insert(depth - 1 - i, v);
                Ok(())
            }
            Term::Ctor(d, c, args) => match v {
                PV::Ctor(d2, c2, vs) if *d == d2 && *c == c2 => {
                    for (a, w) in args.iter().zip(&vs) {
                        self.match_pv(a, depth, w, out)?;
                    }
                    Ok(())
                }
                PV::Nat(n) if self.g().env.builtins().nat == Some(*d) => {
                    let (c2, vs) = if n.bits() == 0 {
                        (0, vec![])
                    } else {
                        (1, vec![PV::Nat(Rc::new((*n).clone() - 1u32))])
                    };
                    if c2 != *c {
                        return skip("an earlier arm's leaf doesn't match its patterns");
                    }
                    for (a, w) in args.iter().zip(&vs) {
                        self.match_pv(a, depth, w, out)?;
                    }
                    Ok(())
                }
                _ => skip("an earlier arm's leaf doesn't match its patterns"),
            },
            _ => Ok(()),
        }
    }

    /// A term of an earlier row's shape, with its variables' values here.
    fn pv_in(&self, t: &Term, other: &Shape, jvals: &HashMap<usize, PV>) -> R<PV> {
        Ok(match t.strip_loc() {
            Term::Var(i) => jvals
                .get(&(other.depth - 1 - i))
                .cloned()
                .ok_or_else(|| Stop::Skip("an earlier arm's variable has no value here".into()))?,
            Term::Ctor(d, c, args) => PV::Ctor(
                *d,
                *c,
                args.iter()
                    .map(|a| self.pv_in(a, other, jvals))
                    .collect::<R<_>>()?,
            ),
            Term::Nat(n) => PV::Nat(n.clone()),
            Term::Refl => PV::Term(Term::Refl, self.depth()),
            _ => return skip("an overlap's pattern isn't constructors and variables"),
        })
    }

    /// A proof of `x = y` here: `rfl`, when they're the same up to the
    /// proofs in constructors' fields (a character `MkChar k p` against the
    /// literal `MkChar k rfl`), which the kernel's comparison skips.
    fn eq_proof(&self, x: &PV, y: &PV) -> R<Term> {
        let x = self.resolve(x);
        let y = self.resolve(y);
        if !self.same_but_proofs(&x, &y) {
            return skip("an overlap's equation isn't true by computation here");
        }
        Ok(Term::Refl)
    }

    /// Whether `x` and `y` are equal but for their constructors' proof
    /// fields.
    fn same_but_proofs(&self, x: &PV, y: &PV) -> bool {
        let g = self.g();
        let x = nat_as_ctor(&g, x);
        let y = nat_as_ctor(&g, y);
        if same_pv(&x, &y) {
            return true;
        }
        match (&x, &y) {
            (PV::Ctor(d, c, xs), PV::Ctor(d2, c2, ys))
                if d == d2 && c == c2 && xs.len() == ys.len() =>
            {
                xs.iter().zip(ys).enumerate().all(|(i, (a, b))| {
                    stitchwort_core::value::proof_field(&g, *d, *c, i) || self.same_but_proofs(a, b)
                })
            }
            _ => false,
        }
    }
}

/// A number as `Zero` or `Succ` of a number, to compare with constructors.
fn nat_as_ctor(g: &Ev, v: &PV) -> PV {
    match v {
        PV::Nat(n) => match g.env.builtins().nat {
            Some(nat) if n.bits() == 0 => PV::Ctor(nat, 0, Vec::new()),
            Some(nat) => PV::Ctor(nat, 1, vec![PV::Nat(Rc::new((**n).clone() - 1u32))]),
            None => v.clone(),
        },
        _ => v.clone(),
    }
}

fn same_pv(a: &PV, b: &PV) -> bool {
    match (a, b) {
        (PV::Var(x), PV::Var(y)) => x == y,
        // A number and the constructors it stands for.
        (PV::Nat(n), PV::Ctor(_, c, args)) | (PV::Ctor(_, c, args), PV::Nat(n)) => match c {
            0 => n.bits() == 0 && args.is_empty(),
            1 if n.bits() > 0 && args.len() == 1 => {
                same_pv(&PV::Nat(Rc::new((**n).clone() - 1u32)), &args[0])
            }
            _ => false,
        },
        (PV::Ctor(d, c, xs), PV::Ctor(d2, c2, ys)) => {
            d == d2
                && c == c2
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| same_pv(x, y))
        }
        (PV::Nat(x), PV::Nat(y)) => x == y,
        (PV::Term(x, dx), PV::Term(y, dy)) => dx == dy && stitchwort_core::value::same_term(x, y),
        _ => false,
    }
}

/// Whether `name` is a generated equation's: `f.eqK`, `f.eqK.orN`, or a
/// branch's, `f.eqK.ifTrue.some`, `f.eq.ifFalse` (the names are reserved
/// for them, D2176). `f.eq` alone counts: it is the start of a branch's.
pub fn is_equation_name(name: &str) -> bool {
    let parts: Vec<&str> = name.split('.').collect();
    let Some(at) = parts.iter().enumerate().skip(1).position(|(_, p)| {
        p.strip_prefix("eq")
            .is_some_and(|d| d.chars().all(|c| c.is_ascii_digit()))
    }) else {
        return false;
    };
    let at = at + 1;
    !parts[at - 1].is_empty()
        && parts[at + 1..].iter().all(|p| {
            p.starts_with(|c: char| c.is_ascii_lowercase())
                && p.chars().all(|c| c.is_ascii_alphanumeric())
        })
}

/// Whether `name` is a definition's generated functional induction,
/// `f.induct` (stage 2a), not a data type's `T.induct`
/// (`derive_induct.rs`).
pub fn is_function_induct(g: &stitchwort_core::Ev, name: &str) -> bool {
    name.strip_suffix(".induct")
        .is_some_and(|o| !o.is_empty() && !o.contains('%') && g.find_data(o).is_none())
}

/// Whether `name` is a generated theorem's: an equation (`f.eq2`) or a
/// definition's `f.induct`.
pub fn is_generated_name(g: &stitchwort_core::Ev, name: &str) -> bool {
    is_equation_name(name) || is_function_induct(g, name)
}

// ------------------------------------------------------------ E-NO-EQUATION

/// `E-NO-EQUATION` if `name` is an equation the source implies that wasn't
/// generated, with the reason (D2176, D2185).
pub(crate) fn no_equation(e: &Elaborator, name: &ast::Name) -> Option<Diagnostic> {
    let (owner, suffix) = reserved_suffix(&name.text)?;
    let Some((Global::Def(f), _)) = e.named(owner) else {
        return None;
    };
    let def = e.kernel.def(*f);
    let induct = suffix == "induct";
    let lazy = if def.theorem() && induct {
        Some("a theorem has no `induct`: it is made for a recursive definition".to_string())
    } else if def.theorem() {
        Some("a theorem's arms have no equations: nothing unfolds a proof".to_string())
    } else if def.instance() && induct {
        Some("an instance has no `induct`: it is made for a recursive definition".to_string())
    } else if def.instance() {
        Some(
            "an instance's arms have no equations: write the method as a named `def` the \
             instance points to, which gets them"
                .to_string(),
        )
    } else {
        None
    };
    let why = match lazy {
        Some(why) => why,
        None => e
            .tables
            .equation_skips
            .iter()
            .rev()
            .find(|(g, s, _)| g == f && s == suffix)?
            .2
            .clone(),
    };
    Some(
        Diagnostic::error(
            "E-NO-EQUATION",
            format!("`{}.{suffix}` isn't generated", e.kernel.def(*f).name()),
        )
        .with_label(name.span, why)
        .with_note(if induct {
            "`f.induct` is generated for a recursive definition where it can be stated and \
             proved (docs/proposals/function-equations.md §5); recurse in the proof instead, as \
             the definition does, with its equations for the steps"
        } else {
            "an equation for each arm is generated where it can be stated and proved \
             (docs/proposals/function-equations.md); prove this one by hand, or use \
             `f.unfold` and a `match`"
        }),
    )
}

impl Elaborator {
    /// The equations the source implies that weren't generated, by key,
    /// with the reason.
    pub fn equation_skips(&self) -> &[(DefId, String, String)] {
        &self.tables.equation_skips
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use stitchwort_core::globals::Kernel;
    use stitchwort_core::{Icit, Term};
    use stitchwort_syntax::{SourceMap, Span};

    use super::{zeta, zeta_size};

    fn rc(t: Term) -> Rc<Term> {
        Rc::new(t)
    }

    fn let_(v: Term, b: Term) -> Term {
        Term::Let("t".into(), rc(Term::Refl), rc(v), rc(b), false)
    }

    /// `f a a`, `f` being variable `f`.
    fn twice(f: usize, a: Term) -> Term {
        Term::App(
            rc(Term::App(rc(Term::Var(f)), rc(a.clone()), Icit::Explicit)),
            rc(a),
            Icit::Explicit,
        )
    }

    /// `zeta_size` counts what `zeta` builds: through `Loc`s, binders, a
    /// `let` of a variable (put in bare) and a chain of `let`s each using
    /// the last twice, whose substituted size doubles with each link.
    #[test]
    fn zeta_size_counts_what_zeta_builds() {
        let k = Kernel::default();
        let g = k.ev();
        let span = Span::point(SourceMap::new().add("t", ""), 0);
        let loc = |t: Term| Term::Loc(span, rc(t));
        // Under `f`, `x`: `let t1 := f x x; …; let tn := f t(n-1) t(n-1); tn`.
        let chain = |n: usize| {
            let mut body = loc(Term::Var(0));
            for i in (1..=n).rev() {
                // `ti` is under `f`, `x` and i - 1 `let`s.
                body = let_(loc(twice(i, loc(Term::Var(0)))), body);
            }
            body
        };
        let cases = [
            chain(1),
            chain(6),
            let_(loc(Term::Var(1)), loc(twice(1, loc(Term::Var(0))))),
            let_(
                twice(1, Term::Var(0)),
                Term::Lam("y".into(), Icit::Explicit, rc(twice(2, loc(Term::Var(1))))),
            ),
        ];
        for t in &cases {
            let built = zeta(&g, t).unwrap();
            let (size, var) = zeta_size(&g, t, &mut Vec::new()).unwrap();
            assert_eq!(size, built.subterms().count(), "{t:?}");
            assert_eq!(var, matches!(built.strip_loc(), Term::Var(_)), "{t:?}");
        }
        let (size, _) = zeta_size(&g, &chain(60), &mut Vec::new()).unwrap();
        assert!(size > 1 << 60, "{size}");
    }
}
