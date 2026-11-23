//! Pattern unification for metavariables, and zonking (substituting solutions
//! back into terms). Follows András Kovács' elaboration-zoo.

use std::rc::Rc;
use stitchwort_core::ProofMark;

use crate::check::quote_internal;
use stitchwort_core::budget::{Phase, ResourceError, Result};
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::proof_counts;
use stitchwort_core::value::{
    Closure, CompareAt, Elim, Head, Relation, ShapeKey, ShapeMemo, Spine, apply_icit, cast_at,
    conv, eval, expand_step, fire_cast, force, force_solved, is_call_field, is_eta_type, is_folded,
    matches_at_once, opens_by_tree, project, project_call, proof_field, proof_param,
    quote_as_written, quote_at_most, quote_folded, same_closure_solved, same_stuck_trees, sealed,
    underapplied, unfold_folded, unfold_folded_head, unfold_once, unfolds_head,
};
use stitchwort_core::{BigUint, DefId, Ev, Icit, Term, Value};
use stitchwort_core::{nat_add, native};

use crate::state::{Attempt, Scoped, ScopedCell, Stats};

/// What the unifier works on: the evaluator's context, the
/// metavariables (the attempt's store), and its own state, in the
/// [`Attempt`].
/// Derefs to the [`Ev`], so it is passed where one is wanted.
#[derive(Clone, Copy)]
pub(crate) struct Unifier<'a> {
    pub(crate) ev: Ev<'a>,
    pub(crate) store: &'a crate::state::MetaStore,
    pub(crate) attempt: &'a Attempt,
    pub(crate) stats: &'a Stats,
}

impl<'a> std::ops::Deref for Unifier<'a> {
    type Target = Ev<'a>;

    fn deref(&self) -> &Ev<'a> {
        &self.ev
    }
}

/// Makes `a` and `b` equal by solving metavariables, with `level` variables in
/// scope. `Ok(false)` if they can't be made equal; an error if it ran out of
/// resources before finding out. A `false` may be followed by trying another
/// way; an error never is.
///
/// The pairs still to unify are kept on a work list, depth first and left to
/// right as a recursive version would take them, so metavariables are solved
/// in the same order; a function type's codomain is only evaluated once its
/// domain has been unified, so it sees the solutions.
///
/// **Precondition: homogeneous values**, as for `value::conv`: `a` and `b`
/// have the same type, since two proofs are equal unlooked at (rule I).
/// Unlike the kernel's, a wrong "equal" here can't be unsound, since the
/// kernel checks what the elaborator builds, but it can solve an unknown
/// with a value of the wrong type: the callers of
/// docs/proposals/full-proof-irrelevance-audit.md §5's third group, which
/// may compare values of different types, live with that. **The level**
/// is above every free variable of `a` and `b`, as fresh variables are
/// made from it. And it isn't atomic: a pair that fails part-way keeps
/// what was solved before it, a whole proof solved by rule I included, so
/// a caller that tries another way after a `false` runs the first inside
/// `undo::transaction`.
#[track_caller]
pub(crate) fn unify(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let same = unify_in(g, level, a, b)?;
    if proof_counts::on() && both_proofs(g, a, b)? {
        proof_counts::record_caller(g, "unify", std::panic::Location::caller(), !same);
    }
    Ok(same)
}

/// Whether `v` is a proof (docs/core.md, "Proof marks"): the kernel's
/// marks ([`stitchwort_core::value::is_proof`]), and for an unsolved
/// unknown at the head, its type's sort, [`ProofMark::Unknown`] while that
/// isn't known.
pub(crate) fn is_proof(g: &Unifier<'_>, v: &Value) -> Result<ProofMark> {
    match stitchwort_core::value::is_proof(g, v) {
        ProofMark::Unknown => {}
        known => return Ok(known),
    }
    match v {
        Value::Neutral(Head::Meta(m), spine)
            if g.meta_solution(*m).is_none()
                && spine.iter().all(|e| matches!(e, Elim::App(..))) =>
        {
            meta_mark(g, *m)
        }
        _ => Ok(ProofMark::Unknown),
    }
}

/// Whether unknown `m`, applied to anything, is a proof: whether its type
/// ends in a proposition, read through its function types. Unknown while
/// the type's sort isn't known (an unknown type, a type variable).
///
/// Worked out once and kept on the unknown (the SW-4671 review's F3): a
/// decided mark for as long as no solution is taken back (the store's
/// `meta_epoch`; within an epoch solutions are only added, and they only
/// decide more), an unknown one until anything more is solved. So taking
/// a solution back can't leave a stale mark (the audit's condition G),
/// and the answer never depends on the budget: running out is an error,
/// passed on, not "unknown". The codomains are applied to variables far
/// above any in scope; the type is only looked at, never read back or
/// compared, and a cast's test inside it compares at the reserved levels
/// above even those (`value::RESERVED_LEVELS`).
fn meta_mark(g: &Unifier<'_>, m: usize) -> Result<ProofMark> {
    let epoch = g.store.meta_epoch.get();
    let solved = g.store.meta_trail.borrow().len();
    let (ty, scope, kept) = {
        let metas = g.store.metas.borrow();
        let Some((ty, scope)) = metas[m].ty.clone() else {
            return Ok(ProofMark::Unknown);
        };
        (ty, scope, metas[m].mark.get())
    };
    match kept {
        Some((e, _, mark)) if e == epoch && mark != ProofMark::Unknown => return Ok(mark),
        Some((e, t, mark)) if e == epoch && t == solved => return Ok(mark),
        _ => {}
    }
    let mut ty = ty;
    let mut mark = ProofMark::Unknown;
    for depth in 0..32 {
        ty = match force(g, ty)? {
            Value::Eq(..) => {
                mark = ProofMark::Proof;
                break;
            }
            Value::Data(d, _) => {
                mark = ProofMark::of_sort(g.data(d).sort());
                break;
            }
            Value::Sort(_) => {
                mark = ProofMark::NotProof;
                break;
            }
            Value::Pi(_, _, _, cod, binder) => {
                cod.apply(g, Value::var_marked(scope + 1_000_000 + depth, binder))?
            }
            _ => break,
        };
    }
    g.store.metas.borrow()[m]
        .mark
        .set(Some((epoch, solved, mark)));
    Ok(mark)
}

/// Whether `a` and `b` are both marked proofs ([`is_proof`]).
fn both_proofs(g: &Unifier<'_>, a: &Value, b: &Value) -> Result<bool> {
    Ok(is_proof(g, a)?.is_proof() && is_proof(g, b)?.is_proof())
}

/// Rule I in the unifier (docs/core.md, "Proof irrelevance"): two values
/// both marked proofs are equal, and nothing inside either is looked at or
/// solved, except that a side that is itself a solvable unknown (applied,
/// perhaps) is solved with the other, as at a proof position
/// ([`proof_position`]). `None` when they aren't both proofs.
fn by_rule_i(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<Option<bool>> {
    if !both_proofs(g, a, b)? {
        return Ok(None);
    }
    proof_counts::record(g, proof_counts::Kind::RuleI, 1);
    proof_position(g, level, a, b).map(Some)
}

/// An unsolved unknown at the head: a side the proof-position rule may
/// solve whole, which rule I keeps (docs/proposals/full-proof-irrelevance.md
/// §4.3).
fn flexible_head(g: &Unifier<'_>, v: &Value) -> bool {
    matches!(v, Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_none())
}

/// The proof counters' pairs of proofs open in [`run_tasks`]: how long the
/// work list was below the pair's own tasks, and the solution trail's
/// length before it.
fn close_proof_pairs(g: &Unifier<'_>, open: &mut Vec<(usize, usize)>, work_len: usize) {
    while let Some(&(base, trail)) = open.last()
        && work_len <= base
    {
        open.pop();
        let solved = g.store.meta_trail.borrow().len().saturating_sub(trail);
        if solved > 0 {
            proof_counts::record(g, proof_counts::Kind::SolvedInsideProofs, 1);
            proof_counts::record(g, proof_counts::Kind::SolvedUnknowns, solved as u64);
        }
    }
}

/// [`unify`] as a comparison of its own, inside another: no pair of it
/// waits ([`nested`]).
fn unify_in(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    nested(g, || {
        run(g, vec![Task::Values(level, a.clone(), b.clone())])
    })
}

/// Runs `f` with no pair waiting: a comparison inside another, or for a
/// caller that wants `true` or `false`, answers for itself, so a pair stuck
/// on a pending unknown in it fails it, as it always has; the comparison
/// around it decides whether the whole pair waits ([`unify_waiting`]).
fn nested<T>(g: &Unifier<'_>, f: impl FnOnce() -> Result<T>) -> Result<T> {
    let _waiting = Scoped::set(&g.attempt.waiting, None);
    f()
}

/// A pair that can't be decided yet ([`unify_waiting`]), with `level`
/// variables in scope.
#[derive(Clone)]
pub(crate) struct Waiting {
    pub(crate) level: usize,
    pub(crate) a: Value,
    pub(crate) b: Value,
}

/// What [`unify_waiting`] finds.
pub(crate) enum Answer {
    /// Equal, with what was solved to make them so.
    Yes,
    /// They can't be made equal.
    No,
    /// Equal but for these pairs, each failing only where a side is an
    /// unknown the queue still has to settle, or stuck on one: the rest is
    /// solved, and the pairs are decided once those unknowns are
    /// (docs/proposals/postponement.md, stage 6).
    Blocked(Vec<Waiting>),
}

/// Tri-state unification (docs/proposals/postponement.md, stage 6): as
/// [`unify`], except that a pair that fails where one side is an unknown
/// still pending in the queue ([`set_pending`]), or a neutral term mentioning
/// one, is set aside instead of failing the comparison, and the rest goes
/// on. Only the outer comparison sets pairs aside: one nested in it (a
/// call's arguments compared on their own) answers `true` or `false`, and
/// the pair it was part of is then the one set aside.
pub(crate) fn unify_waiting(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    pending: &HashSet<usize>,
) -> Result<Answer> {
    let waiting = Scoped::set(&g.attempt.waiting, Some(Vec::new()));
    let saved_pending = Scoped::set(&g.attempt.pending, pending.clone());
    let memo = Scoped::set(&g.attempt.call_memo, None);
    let result = run(g, vec![Task::Values(level, a.clone(), b.clone())]);
    drop(memo);
    drop(saved_pending);
    let waiting = waiting.finish().unwrap_or_default();
    Ok(match result? {
        false => Answer::No,
        true if waiting.is_empty() => Answer::Yes,
        true => Answer::Blocked(waiting),
    })
}

/// [`unify`] that goes on past a pair that differs, keeping what the other
/// pairs solved: for a caller that is about to report an error and wants
/// the unknowns the parts that do agree fix known first (a spec given as
/// `_` beside a parser that differs). Each solution makes its own pair
/// equal, whatever the pairs around it do. Whether a pair differed where
/// neither side is an unknown, or stuck on one: a clash that no solution
/// of an unknown can mend; and whether such a pair was a type (a sort, a
/// function type, a data type), where a solution beside it may have the
/// wrong type.
pub(crate) fn unify_what_agrees(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<Clashes> {
    nested(g, || {
        let _memo = Scoped::set(&g.attempt.call_memo, Some(CallMemo::default()));
        let mut work = vec![Task::Values(level, a.clone(), b.clone())];
        let mut clashes = Clashes::default();
        while let Some(task) = work.pop() {
            g.machine.budget.step()?;
            match task {
                Task::Open(..) => {}
                Task::Values(level, a, b) => {
                    let (x, y) = (a.clone(), b.clone());
                    let same = unify_step(g, level, &a, &b, &mut work)?
                        || values_differ(g, level, a, b, &mut work)?;
                    if !same && !(flexible(g, &x)? || flexible(g, &y)?) {
                        clashes.any = true;
                        clashes.types |= is_type(g, &x)? || is_type(g, &y)?;
                    }
                }
                task => {
                    other_task(g, task, &mut work)?;
                }
            }
        }
        Ok(clashes)
    })
}

/// What [`unify_what_agrees`] found.
#[derive(Default)]
pub(crate) struct Clashes {
    pub(crate) any: bool,
    pub(crate) types: bool,
}

fn is_type(g: &Unifier<'_>, v: &Value) -> Result<bool> {
    Ok(matches!(
        force(g, v.clone())?,
        Value::Sort(_) | Value::Pi(..) | Value::Data(..)
    ))
}

/// Whether `v` is an unknown applied, or stuck on one.
fn flexible(g: &Unifier<'_>, v: &Value) -> Result<bool> {
    Ok(matches!(force(g, v.clone())?, Value::Neutral(Head::Meta(_), _)) || blocked(g, v)?)
}

/// Whether the failing pair `a`, `b` waits ([`unify_waiting`]); set aside
/// if so.
fn sets_aside(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    if g.attempt.waiting.borrow().is_none() || g.attempt.pending.borrow().is_empty() {
        return Ok(false);
    }
    if !(on_pending(g, level, a)? || on_pending(g, level, b)?) {
        return Ok(false);
    }
    if let Some(w) = g.attempt.waiting.borrow_mut().as_mut() {
        w.push(Waiting {
            level,
            a: a.clone(),
            b: b.clone(),
        });
    }
    Ok(true)
}

/// [`on_pending`], with `pending` as the unknowns the queue still has to
/// settle: for a check that needs `v`'s shape (`queue::headed_by_pending`).
pub(crate) fn on_pending_in(
    g: &Unifier<'_>,
    level: usize,
    v: &Value,
    pending: &HashSet<usize>,
) -> Result<bool> {
    let _pending = Scoped::set(&g.attempt.pending, pending.clone());
    on_pending(g, level, v)
}

/// Whether `v` may yet become something else once the queue settles a
/// pending unknown: it is a pending unknown applied to anything, or it is
/// flexible (another unknown applied, a stuck call, a sum on either) and
/// mentions one. A constructor, a type former or a variable applied is
/// rigid, and a pair failing there fails for good.
fn on_pending(g: &Unifier<'_>, level: usize, v: &Value) -> Result<bool> {
    let v = match force(g, v.clone())? {
        Value::NatAdd(_, base) => force(g, (*base).clone())?,
        v => v,
    };
    match &v {
        Value::Neutral(Head::Meta(m), _) if pending(g, *m) => return Ok(true),
        Value::Neutral(Head::Meta(_) | Head::Def(_), _) => {}
        _ => return Ok(false),
    }
    if let Some(t) = quote_at_most(g, level, &v, KNOWN_CAP)? {
        return Ok(t
            .subterms()
            .any(|(t, _)| matches!(t, Term::Meta(m) if pending(g, *m))));
    }
    // Too large to read back cheaply (a call unfolded into a whole
    // proof's statement): look for each pending unknown, as the occurs
    // check does. There are few.
    let pending: Vec<usize> = g.attempt.pending.borrow().iter().copied().collect();
    for m in pending {
        if mentions_meta(g, level, m, &v)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Whether `m` is pending (`Attempt::pending`).
fn pending(g: &Unifier<'_>, m: usize) -> bool {
    g.attempt.pending.borrow().contains(&m)
}

/// Whether unknown `m` is frozen, equal only to itself: a helper's not
/// lifted yet (`MetaStore::meta_frozen`), or a placeholder its queued check
/// hasn't filled (D2016's end state, stage 6). Only the check fills a
/// placeholder (invariant 2); a comparison that meets one waits for it
/// ([`unify_waiting`]) or fails.
fn frozen(g: &Unifier<'_>, m: usize) -> bool {
    g.store.meta_frozen(m) || g.store.mirrors.is_unfilled(m)
}

/// If `m` is the placeholder of a number literal `k` waiting for its type
/// (`MetaStore::waiting_literals`) and `other` is the numeral `k` at a known
/// type, `Nat`'s `k` or `Int`'s `OfNat k`: the type the literal waits on,
/// and that type (D2110). Nothing else: not another numeral, not a value
/// that only computes to `k`, not a type the literal could have that
/// writes `k` differently (`Fin`, `Float`), so the literal's term at that
/// type is exactly `other`.
fn literal_seen_through(g: &Unifier<'_>, m: usize, other: &Value) -> Option<(Value, Value)> {
    // Only while it is frozen: its own fill solves it as any unknown.
    if !g.store.mirrors.is_unfilled(m) {
        return None;
    }
    let (k, waits_on) = g.store.mirrors.literal(m)?;
    let reg = &g.env.registry();
    let ty = match other {
        Value::Nat(n) if **n == *k => Value::Data(
            reg.data(stitchwort_core::registry::Builtin::Nat)?,
            Vec::new().into(),
        ),
        Value::Ctor(d, c, fields)
            if reg.ctor(stitchwort_core::registry::Builtin::OfNat) == Some((*d, *c))
                && matches!(&fields[..], [Value::Nat(n)] if **n == *k) =>
        {
            Value::Data(*d, Vec::new().into())
        }
        _ => return None,
    };
    Some((waits_on, ty))
}

/// [`unify`] for every pair on the work list.
///
/// A pair that fails while one side is a definition stuck on an unknown is
/// put aside and compared again after the rest, evaluated afresh, if the
/// rest solved anything: the unknown may be solved by then and the
/// definition compute. So `List.rangeFrom (Succ ?hi - ?lo) ?lo` against
/// `List.rangeFrom (n - 1) 2` solves `?lo` from the second arguments, and
/// then `?hi - 1` against `n - 1` solves `?hi` (SW-896). A pair put aside
/// fails for good if nothing was solved since. What a failed comparison
/// solved is kept, as it is when unification fails (callers that try again
/// build on it).
///
/// `mode` is where the comparison starts; a [`Task::Mode`] switches it for
/// the pairs above it on the list ([`push_in_shortcut`]).
fn run(g: &Unifier<'_>, work: Vec<Task>) -> Result<bool> {
    let _phase = g.machine.budget.phase(Phase::Unify);
    if g.attempt.call_memo.borrow().is_none() {
        return run_outermost(g, work);
    }
    run_tasks(g, work)
}

/// [`run`] for the outermost comparison, which keeps the record of calls
/// compared ([`CallMemo`]) while it runs. Out of line, so that the frame
/// nested comparisons stand on doesn't hold the record's guard.
#[inline(never)]
fn run_outermost(g: &Unifier<'_>, work: Vec<Task>) -> Result<bool> {
    let _memo = Scoped::set(&g.attempt.call_memo, Some(CallMemo::default()));
    run_tasks(g, work)
}

/// [`run`]'s work list, taken to the end or to the first pair that differs.
#[inline]
fn run_tasks(g: &Unifier<'_>, mut work: Vec<Task>) -> Result<bool> {
    // Only with the proof counters on: pairs of proofs whose tasks aren't
    // done (`close_proof_pairs`).
    let mut proof_pairs: Vec<(usize, usize)> = Vec::new();
    loop {
        if !proof_pairs.is_empty() {
            close_proof_pairs(g, &mut proof_pairs, work.len());
        }
        let Some(task) = work.pop() else { break };
        // A pair of calls compared to the end without failing.
        if let Task::Open(..) = task {
            continue;
        }
        g.machine.budget.step()?;
        // The pairs of values are the common task, and the one through
        // which a comparison recurses (calls compared by their arguments):
        // the rest are out of line, so that this frame stays small.
        let same = match task {
            Task::Values(level, a, b) => {
                if !open_calls(g, level, (&a, &b), &mut work)? {
                    record_different(g, &work);
                    return Ok(false);
                }
                let proofs = proof_counts::on() && both_proofs(g, &a, &b)?;
                if proofs && !flexible_head(g, &a) && !flexible_head(g, &b) {
                    proof_pairs.push((work.len(), g.store.meta_trail.borrow().len()));
                }
                let same = unify_step(g, level, &a, &b, &mut work)?
                    || values_differ(g, level, a, b, &mut work)?;
                if proofs && !same {
                    proof_counts::record(g, proof_counts::Kind::UnifyDifferentProofs, 1);
                }
                same
            }
            task => other_task(g, task, &mut work)?,
        };
        if !same {
            record_different(g, &work);
            return Ok(false);
        }
    }
    Ok(true)
}

/// [`run`] before comparing `a` and `b`, if they're calls whose comparison
/// is remembered: `false` if they're known to differ; otherwise the pair is
/// noted as open, below the tasks it adds.
#[inline(never)]
fn open_calls(
    g: &Unifier<'_>,
    level: usize,
    (a, b): (&Value, &Value),
    work: &mut Vec<Task>,
) -> Result<bool> {
    if let Some(at) = call_key(g, level, a, b)? {
        if known_different(g, &at, a, b)? {
            return Ok(false);
        }
        work.push(Task::Open(at, a.clone(), b.clone()));
    }
    Ok(true)
}

/// [`run`] after the outermost layers of `a` and `b` didn't unify: they're
/// compared again afresh, put aside, or differ.
#[inline(never)]
fn values_differ(
    g: &Unifier<'_>,
    level: usize,
    a: Value,
    b: Value,
    work: &mut Vec<Task>,
) -> Result<bool> {
    Ok(if stale(g, &a)? || stale(g, &b)? {
        work.push(Task::Values(
            level,
            afresh(g, level, &a)?,
            afresh(g, level, &b)?,
        ));
        true
    } else if blocked(g, &a)? || blocked(g, &b)? {
        let trail = g.store.meta_trail.borrow().len();
        work.insert(0, Task::Later(level, a, b, trail));
        true
    } else {
        note_unfilled(g, &a, &b)?;
        sets_aside(g, level, &a, &b)?
    })
}

/// [`run`]'s tasks other than a pair of values.
#[inline(never)]
fn other_task(g: &Unifier<'_>, task: Task, work: &mut Vec<Task>) -> Result<bool> {
    Ok(match task {
        Task::Open(..) | Task::Values(..) => unreachable!("taken by `run`"),
        Task::Proof(level, a, b) => proof_position(g, level, &a, &b)?,
        // Put aside, and nothing solved since: they differ, unless the
        // comparison may wait on them.
        Task::Later(level, a, b, trail) if g.store.meta_trail.borrow().len() <= trail => {
            note_unfilled(g, &a, &b)?;
            sets_aside(g, level, &a, &b)?
        }
        Task::Later(level, a, b, _) => {
            work.push(Task::Values(
                level,
                afresh(g, level, &a)?,
                afresh(g, level, &b)?,
            ));
            true
        }
        // Identical functions unify without solving anything
        // (`same_closure_solved`: a solved unknown is its solution).
        Task::Codomains(_, b1, b2, _) if same_closure_solved(g, &b1, &b2)? => true,
        Task::Codomains(level, b1, b2, mark) => {
            let fresh = Value::var_marked(level, mark);
            work.push(Task::Values(
                level + 1,
                b1.apply(g, fresh.clone())?,
                b2.apply(g, fresh)?,
            ));
            true
        }
    })
}

/// Counts a failing pair, `a` against `b`, if one side's head is an unfilled
/// placeholder, or a definition stuck on one.
fn note_unfilled(g: &Unifier<'_>, a: &Value, b: &Value) -> Result<()> {
    if !g.store.mirrors.any_unfilled() {
        return Ok(());
    }
    let is_unfilled = |m: usize| g.store.mirrors.is_unfilled(m);
    let unfilled = |v: &Value| -> Result<bool> {
        Ok(match force(g, v.clone())? {
            Value::Neutral(Head::Meta(m), _) => is_unfilled(m),
            Value::Neutral(Head::Def(_), spine) => {
                let mut stuck = false;
                for elim in spine.iter() {
                    if let Elim::App(arg, _) = elim
                        && let Value::Neutral(Head::Meta(m), _) = force(g, arg.clone())?
                    {
                        stuck |= is_unfilled(m);
                    }
                }
                stuck
            }
            _ => false,
        })
    };
    if unfilled(a)? || unfilled(b)? {
        Stats::bump(&g.stats.met_unfilled);
    }
    Ok(())
}

/// Notes the solutions made since the trail was `trail` long as made by
/// comparing two calls' arguments (`Attempt::lossy`).
fn note_lossy(g: &Unifier<'_>, trail: usize) {
    let made = g.store.meta_trail.borrow();
    if made.len() > trail {
        g.attempt.lossy.borrow_mut().extend(
            made[trail..]
                .iter()
                .enumerate()
                .map(|(i, (m, _))| (*m, trail + i)),
        );
    }
}

/// Whether metavariable `m`'s solution, as it now is, was made by comparing
/// two calls of a definition by their arguments (`Attempt::lossy`).
pub(crate) fn solved_lossily(g: &Unifier<'_>, m: usize) -> bool {
    let trail = g.store.meta_trail.borrow();
    let Some(at) = trail.iter().rposition(|(solved, _)| *solved == m) else {
        return false;
    };
    g.attempt.lossy.borrow().contains(&(m, at))
}

/// [`unify`], except that two calls of the same definition whose arguments
/// unify only by solving metavariables are equal with those solutions,
/// rather than compared by their unfoldings. `List.sumBy xs ?f` with an
/// unknown `Add` dictionary unfolds to a fold stuck on that dictionary, so
/// only its arguments can say `?f` is the function `List.sumBy xs g` has.
pub(crate) fn unify_solving_arguments(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<bool> {
    let _solving = ScopedCell::set(&g.attempt.solving_arguments, true);
    let _memo = Scoped::set(&g.attempt.call_memo, None);
    unify(g, level, a, b)
}

/// Whether `a` and `b`, two calls of the same definition, are equal by
/// their arguments, solving only unknowns that stand for whole arguments
/// of either call (`?doc`, perhaps applied to the variables in scope), at
/// least one of them against an argument that isn't an unknown:
/// `Lays ?doc indent place` against `Lays (Nest 2 x) indent place`. For a
/// caller whose plain comparison ([`unify`]) of the two failed: an unknown
/// that blocks one call's unfolding while the other's computes can't be
/// solved by comparing the unfoldings, but the arguments say what it is.
/// Nothing is solved if it fails, or if making the arguments equal would
/// solve any other unknown (a helper's, inside a function argument, say):
/// [`unify_solving_arguments`] in general can choose a solution that a
/// later comparison rejects where the unfoldings would have agreed.
pub(crate) fn unify_by_unknown_arguments(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<bool> {
    let (Value::Call(i1, s1, _), Value::Call(i2, s2, _)) = (a, b) else {
        return Ok(false);
    };
    if i1 != i2 {
        return Ok(false);
    }
    if s1.len() != s2.len() {
        return Ok(false);
    }
    let unknown = |arg: &Value| -> Result<Option<usize>> {
        Ok(match force_solved(g, arg.clone())? {
            Value::Neutral(Head::Meta(m), _) if !frozen(g, m) => Some(m),
            _ => None,
        })
    };
    // Whether an unknown applied to the variables in scope where it was
    // made has a type that is data: neither a function nor a type.
    let of_data = |arg: &Value, m: usize| -> Result<bool> {
        let Value::Neutral(_, spine) = force_solved(g, arg.clone())? else {
            return Ok(false);
        };
        let ty = g.store.metas.borrow()[m].ty.clone();
        Ok(match ty {
            Some((ty, scope)) if scope == spine.len() => {
                !matches!(force(g, ty)?, Value::Pi(..) | Value::Sort(..))
            }
            _ => false,
        })
    };
    // Whether an unknown applied to the variables in scope where it was
    // made is a thunk: a function of `()`, as a parser is.
    let thunk = |arg: &Value, m: usize| -> Result<bool> {
        let Value::Neutral(_, spine) = force_solved(g, arg.clone())? else {
            return Ok(false);
        };
        let ty = g.store.metas.borrow()[m].ty.clone();
        let Some((ty, _)) = ty.filter(|(_, scope)| *scope == spine.len()) else {
            return Ok(false);
        };
        let Value::Pi(_, _, domain, _, _) = force(g, ty)? else {
            return Ok(false);
        };
        let unit = g
            .env
            .registry()
            .data(stitchwort_core::registry::Builtin::UnitType);
        Ok(matches!(force(g, (*domain).clone())?, Value::Data(d, _) if Some(d) == unit))
    };
    let mut whole = HashSet::default();
    let mut against_known = false;
    let mut against_lambda = false;
    let mut data_against_known = false;
    for pair in s1.iter().zip(s2.iter()) {
        if let (Elim::App(x, _), Elim::App(y, _)) = pair {
            match (unknown(x)?, unknown(y)?) {
                (Some(m), None) | (None, Some(m)) => {
                    whole.insert(m);
                    let (unknown_arg, known) = if unknown(x)?.is_some() {
                        (x, y)
                    } else {
                        (y, x)
                    };
                    if matches!(force(g, known.clone())?, Value::Lam(..))
                        && !thunk(unknown_arg, m)?
                        && !eta_function(g, level, known)?
                    {
                        against_lambda = true;
                    } else {
                        against_known = true;
                        data_against_known |= of_data(unknown_arg, m)?;
                    }
                }
                (Some(m), Some(n)) => {
                    whole.insert(m);
                    whole.insert(n);
                }
                (None, None) => {}
            }
        }
    }
    // An unknown function (a parser, a spec) facing a lambda is usually
    // settled by more than one argument, and the elaborator has its own
    // order for those; so it is solved with that lambda here only when an
    // unknown that is data, not a function or a type, faces a known
    // argument too: `HangLays kinds ?doc indent pre ?post` against
    // `HangLays kinds BreakParent indent pre (place hang => …)`, where
    // `?doc` blocks the unfolding. A thunk facing `() => …` counts as
    // facing a known argument: it takes nothing the call could supply, so
    // only its body, which the lambda gives whole, is left to settle, and
    // `Parse.Follows ?same ?alike ?p ?q` against two parsers written
    // `() => …` has no data unknown to wait for. A lambda that only applies
    // a known function to its variables (`x y => SameNat x y`) is that
    // function, and counts as a known argument too.
    if !against_known || (against_lambda && !data_against_known) {
        return Ok(false);
    }
    let trail = g.store.meta_trail.borrow().len();
    let same = unify_solving_arguments(g, level, a, b)?;
    let only_whole = g.store.meta_trail.borrow()[trail..]
        .iter()
        .all(|(m, _)| whole.contains(m));
    if same && only_whole {
        return Ok(true);
    }
    undo_since(g, trail);
    Ok(false)
}

/// Whether `value`, with `level` variables in scope, is a lambda that
/// eta-contracts to a function that isn't one: `x y => SameNat x y`, which
/// is `SameNat`. Only a body that ends by applying something to the
/// innermost variable is read back to check the rest.
fn eta_function(g: &Ev, level: usize, value: &Value) -> Result<bool> {
    let mut body = force_solved(g, value.clone())?;
    let mut depth = 0;
    while let Value::Lam(_, _, closure, _) = body {
        body = force_solved(g, closure.apply(g, Value::var(level + depth))?)?;
        depth += 1;
    }
    // An unknown at the head (`x => ?f x`) is no known function.
    let spine = match &body {
        Value::Neutral(Head::Meta(_), _) => return Ok(false),
        Value::Neutral(_, spine) | Value::Call(_, spine, _) => spine,
        _ => return Ok(false),
    };
    let Some(Elim::App(last, _)) = spine.iter().last() else {
        return Ok(false);
    };
    let innermost = depth > 0
        && matches!(
            force_solved(g, last.clone())?,
            Value::Neutral(Head::Var(v, _, _), s) if v == level + depth - 1 && s.is_empty()
        );
    if !innermost {
        return Ok(false);
    }
    // A value too large to read back is no known function, not an error:
    // the comparison goes on to fail as it would without this check. Running
    // out of steps, stack or time stays an error.
    let budget = &g.machine.budget;
    let ran_out_in = budget.take_ran_out_in();
    budget.set_ran_out_in(ran_out_in);
    let too_large = budget.take_too_large();
    budget.set_too_large(too_large);
    let term = match crate::check::quote_folded(g, level, value) {
        Ok(term) => term,
        Err(ResourceError::Size(_)) if budget.exhausted().is_none() => {
            budget.take_too_large();
            budget.set_too_large(too_large);
            budget.take_ran_out_in();
            budget.set_ran_out_in(ran_out_in);
            return Ok(false);
        }
        Err(e) => return Err(e),
    };
    let Some(contracted) = eta_contract(g, &term)? else {
        return Ok(false);
    };
    // As bare, the function counts only if it isn't itself a lambda once
    // unfolded: `x y => Flip r x y` is `Flip r`, which unfolds to one.
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    Ok(!matches!(
        force(g, eval(g, &env, &contracted)?)?,
        Value::Lam(..)
    ))
}

/// `t` eta-contracted, if it is a lambda that only applies a function to
/// its variables (`x y => f x y` is `f`), where `f` mentions none of them.
pub(crate) fn eta_contract(g: &Ev, t: &Term) -> Result<Option<Term>> {
    let Term::Lam(_, icit, body, _) = t.strip_loc() else {
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

/// [`unify`], except that a helper's frozen metavariable in `awaited` (a
/// `match` or local definition not lifted yet) is taken as equal to
/// whatever it is compared with. If that succeeds, the comparison holds only
/// once the helpers are lifted: the caller compares again then.
pub(crate) fn unify_awaiting_helpers(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    awaited: HashSet<usize>,
) -> Result<bool> {
    let _awaited = Scoped::set(&g.attempt.awaited_helpers, Some(awaited));
    let _memo = Scoped::set(&g.attempt.call_memo, None);
    unify(g, level, a, b)
}

/// Whether `m` is a helper's frozen metavariable that
/// [`unify_awaiting_helpers`] is taking as equal to anything.
fn awaited_helper(g: &Unifier<'_>, m: usize) -> bool {
    g.attempt
        .awaited_helpers
        .borrow()
        .as_ref()
        .is_some_and(|set| set.contains(&m))
}

/// A comparison `CompIn ?e B ≟ T` whose `T` is blocked: a definition stuck on
/// an unknown or a variable, which may yet compute to a `Comp`
/// (docs/proposals/effect-polymorphism.md §5.C.1, step 5). `level` variables
/// are in scope.
#[derive(Clone)]
pub struct RowConstraint {
    pub level: usize,
    pub a: Value,
    pub b: Value,
}

/// [`unify`], except that a row comparison that can't be decided yet is put
/// aside rather than failing: the constraints put aside, if it succeeds.
/// The caller keeps them and retries them later; the term is well typed once
/// they're solved.
pub(crate) fn unify_postponing(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<Option<Vec<RowConstraint>>> {
    let postponed = Scoped::set(&g.attempt.postponed, Some(Vec::new()));
    let memo = Scoped::set(&g.attempt.call_memo, None);
    let result = unify(g, level, a, b);
    drop(memo);
    let postponed = postponed.finish().unwrap_or_default();
    Ok(result?.then_some(postponed))
}

/// What a value is at its outermost layer, when no solution of an unknown
/// can change it: it is apart from any value with another head, now and
/// after any unknown is solved. Shared by the row rule (`row_rule`: a type
/// apart from `Comp` makes a row unknown `Empty`) and the instance search
/// (`interfaces::rigidly_distinct`), so the two agree on what is apart
/// (docs/proposals/effect-polymorphism.md §5.C.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Rigid {
    /// A data type, applied.
    Data(stitchwort_core::DataId),
    /// A function type.
    Pi,
    /// A sort.
    Sort,
    /// An equation type.
    Eq,
    /// A variable in scope, applied or not: nothing substitutes for it while
    /// the declaration is elaborated, so it never computes.
    Var,
    /// A quotient type, `Quot A R`.
    Quot,
    /// A definition that never unfolds (an opaque primitive such as `Delay`,
    /// or an axiom), applied.
    Opaque(stitchwort_core::DefId),
}

/// The rigid head of `v`, an already forced value, or `None` if it has none
/// (an unknown, a definition stuck on something that may still compute, a
/// constructor, a function, a number, a stuck `Quot.lift`).
pub(crate) fn rigid_head(g: &Ev, v: &Value) -> Option<Rigid> {
    use stitchwort_core::term::QuotForm;
    Some(match v {
        Value::Data(d, _) => Rigid::Data(*d),
        Value::Pi(..) => Rigid::Pi,
        Value::Sort(_) => Rigid::Sort,
        Value::Eq(..) => Rigid::Eq,
        Value::Neutral(Head::Var(_, _, _), _) => Rigid::Var,
        Value::Neutral(Head::Quot(QuotForm::Type, _), spine)
            if spine.len() == QuotForm::Type.arity() =>
        {
            Rigid::Quot
        }
        // A primitive, or an opaque definition whose body is hidden here
        // (docs/proposals/opaque-definitions.md §6.4): it never computes.
        Value::Neutral(Head::Def(d), _) => {
            let def = g.def(*d);
            if stitchwort_core::value::body_seen(g, *d).is_some()
                || def.state() != stitchwort_core::globals::State::Final
            {
                return None;
            }
            Rigid::Opaque(*d)
        }
        _ => return None,
    })
}

/// What design C's rule says about `a ≟ b`, when one side is `CompIn ?e B`
/// for an unsolved row unknown `?e` (docs/proposals/effect-polymorphism.md
/// §5.C.1, D1123, D1124). `CompIn Empty B` is `B`, so `?e := Empty` is
/// always a solution; another exists only when the other side is, or may
/// become, a `Comp`. So:
///
/// - the other side apart from `Comp` (a data type, a function type, a sort,
///   an equation, a type variable, a quotient, an opaque primitive): `?e :=
///   Empty`, then `B ≟ T`;
/// - a `Comp` over a row with at least one ability (its operations headed
///   by `Plus`): `?e := Ops op res`, then `B ≟ A` (the callback is
///   effectful);
/// - `Comp NoOp NoRes A`, written by hand: passed as data, `?e := Empty`;
/// - a definition stuck on something unknown, or a `Comp` whose row is: blocked;
///   put aside under [`unify_postponing`], otherwise no;
/// - a `Delay` (a partial computation): no, as a row variable never stands
///   for `Partial`.
///
/// `None` when the rule doesn't apply: neither side is such a `CompIn`, or the
/// other side is an unknown (the ordinary unifier solves it with the
/// `CompIn` itself, committing nothing about `?e`) or another `CompIn` (the
/// spines are compared, as for any definition).
fn row_rule(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<Option<bool>> {
    use stitchwort_core::partial::Primitive;
    use stitchwort_core::registry::Builtin;
    if let Some(answer) = divergence_rule(g, level, a, b, work)? {
        return Ok(Some(answer));
    }
    let Some(comp_in) = g.env.registry().def(Builtin::CompIn) else {
        return Ok(None);
    };
    // `CompIn ?e B`: its row and its result.
    let unknown_row = |v: &Value| -> Result<Option<(Value, Value)>> {
        let Value::Neutral(Head::Def(d), spine) = v else {
            return Ok(None);
        };
        if *d != comp_in || spine.len() != 2 {
            return Ok(None);
        }
        let (Elim::App(row, _), Elim::App(result, _)) = (&spine[0], &spine[1]) else {
            return Ok(None);
        };
        Ok(match force(g, row.clone())? {
            Value::Neutral(Head::Meta(m), _) if !frozen(g, m) => {
                Some((row.clone(), result.clone()))
            }
            _ => None,
        })
    };
    let (row, result, other) = match (unknown_row(a)?, unknown_row(b)?) {
        (Some((row, result)), None) => (row, result, b),
        (None, Some((row, result))) => (row, result, a),
        _ => return Ok(None),
    };
    let is_comp_in = |v: &Value| matches!(v, Value::Neutral(Head::Def(d), _) if *d == comp_in);
    if matches!(other, Value::Neutral(Head::Meta(_), _)) || is_comp_in(other) {
        return Ok(None);
    }
    let (Some(comp), Some(plus), Some(no_op), Some(empty_row)) = (
        g.env.registry().data(Builtin::Comp),
        g.env.registry().data(Builtin::Plus),
        g.env.registry().data(Builtin::NoOp),
        crate::rows::empty_row(&g.ev),
    ) else {
        return Ok(None);
    };
    // Pushed last-first, so the row is solved first.
    let solve_with = |work: &mut Vec<Task>, row_value: Value, result_ty: Value, other_ty: Value| {
        work.push(Task::Values(level, result_ty, other_ty));
        work.push(Task::Values(level, row.clone(), row_value));
    };
    let blocked = |a: &Value, b: &Value| -> bool {
        match g.attempt.postponed.borrow_mut().as_mut() {
            Some(list) => {
                list.push(RowConstraint {
                    level,
                    a: a.clone(),
                    b: b.clone(),
                });
                true
            }
            None => false,
        }
    };
    let apart = match other {
        Value::Data(d, args) if *d == comp && args.len() == 3 => {
            return Ok(Some(match force(g, args[0].clone())? {
                // Effectful: the row is the `Comp`'s.
                Value::Data(p, _) if p == plus => {
                    match crate::rows::ops_row(&g.ev, args[0].clone(), args[1].clone()) {
                        Ok(value) => {
                            solve_with(work, value, result, args[2].clone());
                            true
                        }
                        Err(crate::rows::RowFault::Resource(e)) => return Err(e),
                        // Unreachable: the operations are headed by `Plus`.
                        Err(_) => false,
                    }
                }
                // `Comp NoOp NoRes A`: data.
                Value::Data(n, _) if n == no_op => {
                    solve_with(work, empty_row, result, other.clone());
                    true
                }
                _ => blocked(a, b),
            }));
        }
        // A partial computation: the tail of a row with abilities is total
        // (a bare `{e}` is a `CompD`, handled by `divergence_rule`).
        Value::Neutral(Head::Def(d), _)
            if g.env.builtins().primitive_id(Primitive::Delay) == Some(*d) =>
        {
            return Ok(Some(false));
        }
        _ => match rigid_head(&g.ev, other) {
            Some(_) => true,
            // A definition, or a `Quot.lift`, stuck on something that may
            // still compute: blocked.
            None if matches!(
                other,
                Value::Neutral(Head::Def(_), _)
                    | Value::Neutral(Head::Quot(stitchwort_core::QuotForm::Lift, _), _)
            ) =>
            {
                false
            }
            // Not a type: the rule has nothing to say.
            None => return Ok(None),
        },
    };
    if apart {
        solve_with(work, empty_row, result, other.clone());
        return Ok(Some(true));
    }
    Ok(Some(blocked(a, b)))
}

/// The rule for `CompD ?d E B ≟ T`, a computation type in a bare row whose
/// divergence is still unknown (docs/proposals/partial-stage-3.md §2.3,
/// D1213). `CompD Total E B` is `CompIn E B`, and `CompD MayDiverge E B` is
/// `Delay (rowOp E) (rowRes E) B`. So:
///
/// - a `Delay` (a partial callback or result): `?d := MayDiverge`, and `E`
///   is the `Delay`'s row, read as the `Comp` rule reads one;
/// - a type apart from `Delay` (a `Comp`, a `CompIn`, a data type, a
///   function type, …): `?d := Total`, then the comparison again, where the
///   row rule for `CompIn` settles `E`;
/// - a definition stuck on something unknown: blocked, as for `CompIn`.
///
/// `None` when it doesn't apply: neither side is such a `CompD`, or the
/// other side is an unknown or another `CompD`.
fn divergence_rule(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<Option<bool>> {
    use stitchwort_core::partial::Primitive;
    use stitchwort_core::registry::Builtin;
    let Some(comp_d) = g.env.registry().def(Builtin::CompD) else {
        return Ok(None);
    };
    let is_comp_d = |v: &Value| matches!(v, Value::Neutral(Head::Def(d), _) if *d == comp_d);
    // `CompD ?d E B`: its divergence, row and result.
    let unknown = |v: &Value| -> Result<Option<(Value, Value, Value)>> {
        let Value::Neutral(Head::Def(d), spine) = v else {
            return Ok(None);
        };
        if *d != comp_d || spine.len() != 3 {
            return Ok(None);
        }
        let (Elim::App(div, _), Elim::App(row, _), Elim::App(result, _)) =
            (&spine[0], &spine[1], &spine[2])
        else {
            return Ok(None);
        };
        Ok(match force(g, div.clone())? {
            Value::Neutral(Head::Meta(m), _) if !frozen(g, m) => {
                Some((div.clone(), row.clone(), result.clone()))
            }
            _ => None,
        })
    };
    let (div, row, result, other) = match (unknown(a)?, unknown(b)?) {
        (Some((d, r, t)), None) => (d, r, t, b),
        (None, Some((d, r, t))) => (d, r, t, a),
        (None, None) => {
            // A stuck `CompD`: its divergence is a variable.
            if is_comp_d(a) != is_comp_d(b) {
                g.attempt.note_rigid_divergence();
            }
            return Ok(None);
        }
        _ => return Ok(None),
    };
    if matches!(other, Value::Neutral(Head::Meta(_), _)) || is_comp_d(other) {
        return Ok(None);
    }
    let (Some((dd, total)), Some((_, may)), Some(plus), Some(no_op), Some(row_op), Some(empty)) = (
        g.env.registry().ctor(Builtin::DivTotal),
        g.env.registry().ctor(Builtin::DivMay),
        g.env.registry().data(Builtin::Plus),
        g.env.registry().data(Builtin::NoOp),
        g.env.registry().def(Builtin::RowOp),
        crate::rows::empty_row(&g.ev),
    ) else {
        return Ok(None);
    };
    let blocked = || -> bool {
        match g.attempt.postponed.borrow_mut().as_mut() {
            Some(list) => {
                list.push(RowConstraint {
                    level,
                    a: a.clone(),
                    b: b.clone(),
                });
                true
            }
            None => false,
        }
    };
    let delay = g.env.builtins().primitive_id(Primitive::Delay);
    if let Value::Neutral(Head::Def(d), spine) = other
        && Some(*d) == delay
    {
        let (Some(Elim::App(op, _)), Some(Elim::App(res, _)), Some(Elim::App(t, _))) =
            (spine.first(), spine.get(1), spine.get(2))
        else {
            return Ok(Some(false));
        };
        // The partial computation's row, as an `Effects`.
        let row_value = match force(g, op.clone())? {
            Value::Data(p, _) if p == plus => {
                match crate::rows::ops_row(&g.ev, op.clone(), res.clone()) {
                    Ok(value) => value,
                    Err(crate::rows::RowFault::Resource(e)) => return Err(e),
                    Err(_) => return Ok(Some(false)),
                }
            }
            Value::Data(n, _) if n == no_op => empty,
            Value::Neutral(Head::Def(id), tail) if id == row_op && tail.len() == 1 => {
                match &tail[0] {
                    Elim::App(x, _) => x.clone(),
                    _ => return Ok(Some(false)),
                }
            }
            _ => return Ok(Some(blocked())),
        };
        // Pushed last-first: the divergence, then the row, then the result.
        work.push(Task::Values(level, result, t.clone()));
        work.push(Task::Values(level, row, row_value));
        work.push(Task::Values(
            level,
            div,
            Value::Ctor(dd, may, Vec::new().into()),
        ));
        return Ok(Some(true));
    }
    let settled = rigid_head(&g.ev, other).is_some()
        || matches!(other, Value::Neutral(Head::Def(d), _)
            if Some(*d) == g.env.registry().def(Builtin::CompIn));
    if !settled {
        return Ok(match other {
            Value::Neutral(Head::Def(_), _)
            | Value::Neutral(Head::Quot(stitchwort_core::QuotForm::Lift, _), _) => Some(blocked()),
            _ => None,
        });
    }
    // Total: then compared again, as `CompIn E B`.
    let Some(comp_in) = g.env.registry().def(Builtin::CompIn) else {
        return Ok(None);
    };
    let comp_in = Value::Neutral(Head::Def(comp_in), Default::default());
    let comp_in = stitchwort_core::value::apply(g, comp_in, row)?;
    let comp_in = stitchwort_core::value::apply(g, comp_in, result)?;
    work.push(Task::Values(level, comp_in, other.clone()));
    work.push(Task::Values(
        level,
        div,
        Value::Ctor(dd, total, Vec::new().into()),
    ));
    Ok(Some(true))
}

/// The rules of `+` read backwards (SW-896; docs/proposals/nat-add-recursion.md
/// §10), for a sum stuck on an unknown: `a + ?m ≟ T`, or `?m + a ≟ T`, where
/// `a` mentions no unknown and `?m` is unsolved and applied to distinct
/// variables. `a` is then stuck for good (it's no number or constructor, or
/// the sum would have computed, and no solution can make it one), so `a + M`
/// is a `Succ` exactly when `M` is (R4, or R2 for `?m + a`), is `a` exactly
/// when `M` is `Zero` (R3, R1), and is otherwise a sum stuck on `M`. So:
///
/// - `T` is `k + a`, `k > 0`: `?m := k` (R4 `k` times, then R3);
/// - `T` is `k + t`, `k > 0`, and `t` doesn't mention `?m`: `?m := k + ?m'`
///   for a new `?m'`, then `a + ?m' ≟ t` (the one way to peel `k` `Succ`s);
/// - anything else (a number, another sum, a stuck call): `None`, and the
///   comparison goes on as before.
///
/// Every solution has that shape, so the rule chooses nothing a solution
/// could avoid; the kernel checks the result as always. `None` too when
/// the rule doesn't apply: the rules of `+` aren't bound, neither side is
/// such a sum, or the other side is an unknown (solved with the sum itself).
///
/// `a + ?m ≟ a` on its own, with no `Succ` to peel, is left alone, though
/// `?m := Zero` is its one solution: `rewrite` finds occurrences by
/// unification, and `Nat.powAdd 10 k _` would then find `Nat.pow 10 k` as
/// `Nat.pow 10 (k + 0)`, which no sum matched before `+` computed on its
/// second argument (2025 day 2's `multiplierSucc`). What the rule does
/// match, `a + ?m` against `k + a` or `Succ (a + t)`, is what matched as
/// written then (`x + 1` was stuck).
fn plus_rule(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<Option<bool>> {
    let Some(add) = g.env.builtins().nat_add_rule else {
        return Ok(None);
    };
    if let Some(sum) = stuck_sum(g, level, add, a)?
        && let Some(answer) = plus_rule_with(g, level, add, sum, b, work)?
    {
        return Ok(Some(answer));
    }
    match stuck_sum(g, level, add, b)? {
        Some(sum) => plus_rule_with(g, level, add, sum, a, work),
        None => Ok(None),
    }
}

/// Whether [`unify_abbreviation`] applies to `a` and `b`.
pub(crate) fn abbreviation_meets(g: &Unifier<'_>, a: &Value, b: &Value) -> Result<bool> {
    Ok(meeting(g, a, b, true)?.is_some())
}

/// A sum stuck on an unknown, as [`plus_rule`] takes it apart.
struct StuckSum {
    /// The side that mentions no unknown.
    known: Value,
    /// Whether the unknown is the first summand (`?m + a`).
    unknown_first: bool,
    m: usize,
    spine: Spine,
}

/// `v`, an already forced value, as a [`StuckSum`] of `add`, if it is one.
fn stuck_sum(g: &Unifier<'_>, level: usize, add: DefId, v: &Value) -> Result<Option<StuckSum>> {
    let Value::Neutral(Head::Def(d), spine) = v else {
        return Ok(None);
    };
    let [Elim::App(x, Icit::Explicit), Elim::App(y, Icit::Explicit)] = &spine[..] else {
        return Ok(None);
    };
    if *d != add {
        return Ok(None);
    }
    let unknown = |v: &Value| -> Result<Option<(usize, Spine)>> {
        Ok(match force(g, v.clone())? {
            Value::Neutral(Head::Meta(m), s) if !frozen(g, m) && distinct_variables(g, &s)? => {
                Some((m, s))
            }
            _ => None,
        })
    };
    let (known, unknown_first, (m, spine)) = match (unknown(x)?, unknown(y)?) {
        (None, Some(u)) => (x, false, u),
        (Some(u), None) => (y, true, u),
        _ => return Ok(None),
    };
    if mentions_unknown(g, level, known)? {
        return Ok(None);
    }
    Ok(Some(StuckSum {
        known: known.clone(),
        unknown_first,
        m,
        spine,
    }))
}

/// [`plus_rule`] for `sum ≟ other`.
fn plus_rule_with(
    g: &Unifier<'_>,
    level: usize,
    add: DefId,
    sum: StuckSum,
    other: &Value,
    work: &mut Vec<Task>,
) -> Result<Option<bool>> {
    if matches!(other, Value::Neutral(Head::Meta(_), _)) {
        return Ok(None);
    }
    // `x1 … xn => body`, for the unknown's spine.
    let solve_with = |body: Term| -> Result<()> {
        let mut solution = body;
        for elim in sum.spine.iter().rev() {
            let Elim::App(_, icit) = elim else {
                unreachable!("distinct variables are applications")
            };
            solution = Term::Lam("x".into(), *icit, Rc::new(solution), ProofMark::Unknown);
        }
        g.store.solve_meta(sum.m, eval(g, &[], &solution)?);
        Ok(())
    };
    let (k, rest) = native::view(g, other)?;
    match rest {
        // `k + a`: `?m := k`.
        Some(t) if k != BigUint::ZERO && conv(g, level, &sum.known, &t)? => {
            solve_with(Term::Nat(Rc::new(k)))?;
            Ok(Some(true))
        }
        // `k + t`: `?m := k + ?m'`, then `a + ?m' ≟ t`.
        Some(t) if k != BigUint::ZERO => {
            if mentions_meta(g, level, sum.m, &t)? {
                return Ok(None);
            }
            let span = g.store.metas.borrow()[sum.m].span;
            let fresh = g.store.new_meta(span);
            let n = sum.spine.len();
            let mut applied = Term::Meta(fresh);
            for (i, elim) in sum.spine.iter().enumerate() {
                let Elim::App(_, icit) = elim else {
                    unreachable!("distinct variables are applications")
                };
                applied = Term::app_icit(applied, Term::Var(n - 1 - i), *icit);
            }
            solve_with(native::nat_add_term(g, &k, applied))?;
            let fresh = Value::Neutral(Head::Meta(fresh), sum.spine.clone());
            let smaller = if sum.unknown_first {
                nat_add::call(add, fresh, sum.known)
            } else {
                nat_add::call(add, sum.known, fresh)
            };
            work.push(Task::Values(level, smaller, t));
            Ok(Some(true))
        }
        _ => Ok(None),
    }
}

/// Whether `spine` is distinct variables, as a pattern's is.
fn distinct_variables(g: &Ev, spine: &[Elim]) -> Result<bool> {
    let mut seen = HashSet::default();
    for elim in spine {
        let Elim::App(v, _) = elim else {
            return Ok(false);
        };
        match force(g, v.clone())? {
            Value::Neutral(Head::Var(l, _, _), s) if s.is_empty() && seen.insert(l) => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// The most nodes [`mentions_unknown`] reads back before giving up.
const KNOWN_CAP: u64 = 4096;

/// Whether `v` may mention an unknown: read back, it has one, or it's too
/// large to tell cheaply.
fn mentions_unknown(g: &Ev, level: usize, v: &Value) -> Result<bool> {
    Ok(match quote_at_most(g, level, v, KNOWN_CAP)? {
        Some(t) => t.subterms().any(|(t, _)| matches!(t, Term::Meta(_))),
        None => true,
    })
}

/// Whether `v` mentions unknown `m`, through the solutions of others too.
fn mentions_meta(g: &Unifier<'_>, level: usize, m: usize, v: &Value) -> Result<bool> {
    let renaming: HashMap<usize, usize> = (0..level).map(|l| (l, l)).collect();
    Ok(settle(rename(g, m, &renaming, level, level, v, true))?.is_none())
}

/// Unification still to do.
enum Task {
    Values(usize, Value, Value),
    /// Two values at a proof position, which the kernel skips
    /// ([`proof_position`]).
    Proof(usize, Value, Value),
    /// With the binder's proof mark, for the fresh variable.
    Codomains(usize, Closure, Closure, ProofMark),
    /// A pair put aside ([`run`]), with the length of the trail then.
    Later(usize, Value, Value, usize),
    /// Below the parts of a pair of calls of one definition still being
    /// compared: if the comparison fails while this is on the list, so did
    /// that pair ([`CallMemo`]).
    Open(ShapeKey<CallKey>, Value, Value),
}

// Two calls of one definition are compared by their arguments first, then
// by their unfoldings, and the unfoldings usually contain the arguments
// again: `Parse.exactly 35 p` against `Parse.exactly 36 p` compares the
// calls of the next level down once in the arguments and once more in the
// unfoldings, and so on down, about 2³⁵ comparisons in all. Outside solving
// from arguments, `unify_step` answers "different" for such a nested pair
// at once, inside a comparison of arguments (SW-1506), which is only a
// shortcut there. While solving from arguments it is more than that, so
// there the outermost comparison keeps a record of the pairs of calls found
// different in it instead, and a pair met again is answered at once: each
// pair is compared once, and the chain takes a step per level (SW-1521).
// The pairs are found again by their shapes (as `same_stuck_trees` finds
// pairs found equal), not their addresses: a call in a closure's body is
// built anew each time the closure is applied.
//
// Why it can't change an answer: a comparison is a function of the pair,
// the level, the mode, what has been solved and put aside, and the context
// the outermost comparison set up (`Attempt::pending`, `solving_arguments`,
// `awaited_helpers`; each entry point that sets them starts a record of its
// own). What has been solved is told by the `meta_epoch` and the length of
// the trail: within an epoch solutions are only added, and taking one back
// starts a new epoch. A pair is recorded only if it failed with nothing
// solved or put aside since its comparison started and nothing taken back,
// so comparing it again from there would fail the same way and leave
// nothing behind, which is what answering at once does. Only while no pair
// may wait (`Attempt::waiting` empty, as everywhere but the outermost
// comparison of `unify_waiting`): there a failing part can be set aside.
// A pair is recorded when the comparison it is part of fails: the work list
// is depth first, so the pairs whose `Task::Open` is still on it are those
// the failing part belongs to, and each on its own would have taken the
// same steps to the same failure. So a pair met again fails the whole
// comparison at once, as that failure did, rather than answering `false`
// for the pair alone (which [`run`] could still put aside as blocked). The
// record ends with the outermost comparison.

/// The pairs of calls of one definition found different during one
/// outermost comparison, filed by [`CallKey`] and found again by their
/// shapes (`ShapeMemo`); see the note above. Also the stuck sums found to
/// have nothing for rule E to read ([`reread_sum`]).
#[derive(Default)]
pub(crate) struct CallMemo {
    calls: ShapeMemo<CallKey>,
    sums: (Effects, nat_add::Unread),
}

/// What a pair of calls in a [`CallMemo`] is filed under besides its
/// shapes: level, the definition called, and what had been solved and put
/// aside when it was compared ([`Effects`]).
type CallKey = (usize, DefId, Effects);

/// What a comparison has done so far, as far as a later one can tell: the
/// `meta_epoch`, the length of the trail, and how many row constraints
/// [`unify_postponing`] has put aside.
type Effects = (u64, usize, usize);

fn effects(g: &Unifier<'_>) -> Effects {
    (
        g.store.meta_epoch.get(),
        g.store.meta_trail.borrow().len(),
        g.attempt.postponed.borrow().as_ref().map_or(0, Vec::len),
    )
}

/// `value` read by rule E (`nat_add::reread`), the sums found to have
/// nothing to read kept in the outermost comparison's [`CallMemo`] while
/// nothing is solved, taken back or put aside: a solution can give such a
/// sum's bottom something to unfold.
fn reread_sum(g: &Unifier<'_>, value: &Value) -> Result<Option<Value>> {
    let now = effects(g);
    // Taken out of the memo while the walk evaluates, and put back after.
    let mut unread = match g.attempt.call_memo.borrow_mut().as_mut() {
        Some(memo) if memo.sums.0 == now => std::mem::take(&mut memo.sums.1),
        _ => nat_add::Unread::default(),
    };
    let read = nat_add::reread(g, value, force, |x| unfold_folded(g, x), &mut unread)?;
    if let Some(memo) = g.attempt.call_memo.borrow_mut().as_mut()
        && effects(g) == now
    {
        memo.sums = (now, unread);
    }
    Ok(read)
}

/// Where `a` against `b` is filed in the [`CallMemo`] now, if they are
/// calls of one definition and the record applies: while solving from
/// arguments, and no pair may wait.
fn call_key(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<Option<ShapeKey<CallKey>>> {
    let (Value::Call(i1, _, _), Value::Call(i2, _, _)) = (a, b) else {
        return Ok(None);
    };
    if i1 != i2 || !g.attempt.solving_arguments.get() || g.attempt.waiting.borrow().is_some() {
        return Ok(None);
    }
    let mut memo = g.attempt.call_memo.borrow_mut();
    let Some(memo) = memo.as_mut() else {
        return Ok(None);
    };
    memo.calls
        .file(&g.ev, (level, *i1, effects(g)), a, b)
        .map(Some)
}

/// Whether `a` against `b`, filed at `at`, was found different
/// ([`CallMemo`]).
fn known_different(g: &Unifier<'_>, at: &ShapeKey<CallKey>, a: &Value, b: &Value) -> Result<bool> {
    match g.attempt.call_memo.borrow().as_ref() {
        Some(memo) => memo.calls.contains(&g.ev, at, a, b),
        None => Ok(false),
    }
}

/// Records as different the pairs whose comparison was open when the
/// comparison `work` is the rest of failed, those that solved nothing.
fn record_different(g: &Unifier<'_>, work: &[Task]) {
    let now = effects(g);
    let mut memo = g.attempt.call_memo.borrow_mut();
    let Some(memo) = memo.as_mut() else {
        return;
    };
    for task in work {
        if let Task::Open(at, a, b) = task
            && at.0.2 == now
        {
            memo.calls.insert(*at, a, b);
        }
    }
}

/// Whether `v` may be a definition stuck on an unknown, as far as can be
/// told cheaply: a call of one with an argument that is an unknown not
/// solved yet (or `k + ` one), or such a call itself, [`BLOCKED_DEPTH`]
/// calls deep at most; or a field of an unknown not solved yet, `?r.f`,
/// which is what such a call of an accessor is under record eta.
fn blocked(g: &Unifier<'_>, v: &Value) -> Result<bool> {
    blocked_within(g, v, BLOCKED_DEPTH)
}

/// How deep [`blocked`] looks.
const BLOCKED_DEPTH: usize = 3;

/// `v` read back and evaluated again, with every solution so far put in:
/// a computation stuck on an unknown solved since takes its steps.
fn afresh(g: &Unifier<'_>, level: usize, v: &Value) -> Result<Value> {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    eval(g, &env, &crate::check::quote_folded(g, level, v)?)
}

/// Whether `v` may be a definition stuck on an unknown that has been solved
/// since: a call of one with an argument that is a solved unknown (or `k +`
/// one), or such a call itself, [`BLOCKED_DEPTH`] calls deep at most.
/// [`force`] replaces a solved unknown only at the head, so such a call
/// stays stuck, though it reads back with the solution in: `pick ?b 5`,
/// with `?b` solved with `True` after `pick ?b` was applied to `5` (or `x
/// + y` through an `Add` dictionary solved late), prints as what it should
/// compute to, yet doesn't unify with it. [`afresh`] lets it compute.
fn stale(g: &Unifier<'_>, v: &Value) -> Result<bool> {
    stale_within(g, v, BLOCKED_DEPTH)
}

fn stale_within(g: &Unifier<'_>, v: &Value, depth: usize) -> Result<bool> {
    let Value::Neutral(Head::Def(_), spine) = force(g, v.clone())? else {
        return Ok(false);
    };
    for elim in spine.iter() {
        let Elim::App(arg, _) = elim else {
            continue;
        };
        let arg = match arg {
            Value::NatAdd(_, base) => &**base,
            other => other,
        };
        match arg {
            Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_some() => return Ok(true),
            Value::Neutral(Head::Def(_), _) | Value::Call(..)
                if depth > 1 && stale_within(g, arg, depth - 1)? =>
            {
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// Whether a spine may mention an unknown, solved or not, frozen or not:
/// `false` only if a look at no more than [`MENTION_LOOK`] parts finds
/// none. Closures, glued calls and the like aren't looked into, so they
/// count as mentioning one.
fn may_mention_meta(spine: &[Elim]) -> bool {
    let mut look = MENTION_LOOK;
    let mut todo: Vec<&Value> = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(x, _) => todo.push(x),
            _ => return true,
        }
    }
    while let Some(v) = todo.pop() {
        if look == 0 {
            return true;
        }
        look -= 1;
        match v {
            Value::Sort(_) | Value::Nat(_) | Value::Chars(_) | Value::Refl => {}
            Value::NatAdd(_, base) => todo.push(base),
            Value::Data(_, args) => todo.extend(args.iter()),
            Value::Ctor(_, _, fields) => todo.extend(fields.iter()),
            Value::Eq(t, x, y) => todo.extend([&**t, &**x, &**y]),
            Value::Neutral(Head::Var(..) | Head::Def(_), spine) => {
                for elim in spine.iter() {
                    match elim {
                        Elim::App(x, _) => todo.push(x),
                        _ => return true,
                    }
                }
            }
            _ => return true,
        }
    }
    false
}

/// How many parts [`may_mention_meta`] looks at.
const MENTION_LOOK: usize = 64;

fn blocked_within(g: &Unifier<'_>, v: &Value, depth: usize) -> Result<bool> {
    let spine = match force(g, v.clone())? {
        Value::Neutral(Head::Def(_), spine) => spine,
        // A field of an unknown, `?r.f` (or `?r.f x`, `(?m x).f`): rule 2
        // opens an accessor on an unknown record to this, where without eta
        // it stopped at the call `R.f ?r`, a definition stuck on `?r`. So it
        // counts as that call did, and no further: an unknown applied to
        // arguments only, `?m x`, is solved, not waited for. `force` has put
        // in a solved head, so `m` is unsolved.
        Value::Neutral(Head::Meta(m), spine)
            if spine.iter().any(|e| matches!(e, Elim::Proj(..))) =>
        {
            return Ok(!frozen(g, m));
        }
        _ => return Ok(false),
    };
    for elim in spine.iter() {
        let Elim::App(arg, _) = elim else {
            continue;
        };
        let arg = match force(g, arg.clone())? {
            Value::NatAdd(_, base) => force(g, (*base).clone())?,
            other => other,
        };
        match &arg {
            Value::Neutral(Head::Meta(m), _) if !frozen(g, *m) => return Ok(true),
            Value::Neutral(Head::Def(_), _) if depth > 1 && blocked_within(g, &arg, depth - 1)? => {
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// Unifies the outermost layer of `a` and `b`: `false` if they can't be made
/// equal there; otherwise pushes the pairs of parts still to unify.
///
/// The rules for two calls of one definition, which compare their arguments
/// (a recursion as deep as calls are nested in arguments), and the rest are
/// functions of their own, so that this frame, under every level of that
/// recursion, is small.
fn unify_step(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<bool> {
    if let Some(answer) = by_rule_i(g, level, a, b)? {
        return Ok(answer);
    }
    if let (Value::Call(i1, _, _), Value::Call(i2, _, _)) = (a, b)
        && i1 == i2
        && let Some(answer) = same_calls(g, level, a, b)?
    {
        return Ok(answer);
    }
    if let Some((a, b)) = solved_calls(g, a, b)?
        && let Some(answer) = same_calls(g, level, &a, &b)?
    {
        return Ok(answer);
    }
    unify_step_rest(g, level, a, b, work)
}

/// `a` and `b` with a solved unknown at either head replaced by its
/// solution, if that makes them two calls of the same definition: `?j x`,
/// solved as `bind (nat ()) k`, against `bind (?p ()) k'`. Compared as
/// calls, by [`same_calls`], as two calls written out are; otherwise
/// [`force`] would unfold both, and an unknown among the arguments (`?p`)
/// would meet what the other call's argument computes to inside the
/// unfolding, not the argument itself. Only while solving from arguments
/// ([`unify_solving_arguments`]): elsewhere [`same_calls`] keeps only a
/// match that solves nothing, so the look costs steps and rarely helps.
fn solved_calls(g: &Unifier<'_>, a: &Value, b: &Value) -> Result<Option<(Value, Value)>> {
    let solved =
        |v: &Value| matches!(v, Value::Neutral(Head::Meta(m), _) if g.meta_solution(*m).is_some());
    if !g.attempt.solving_arguments.get()
        || !(solved(a) || solved(b))
        || !matches!(a, Value::Call(..) | Value::Neutral(Head::Meta(_), _))
        || !matches!(b, Value::Call(..) | Value::Neutral(Head::Meta(_), _))
    {
        return Ok(None);
    }
    let (a, b) = (force_solved(g, a.clone())?, force_solved(g, b.clone())?);
    Ok(match (&a, &b) {
        (Value::Call(i1, _, _), Value::Call(i2, _, _)) if i1 == i2 => Some((a, b)),
        _ => None,
    })
}

/// [`unify_step`]'s rules for two calls `a` and `b` of the same definition:
/// the answer, or `None` to go on to the other rules.
#[inline(never)]
fn same_calls(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<Option<bool>> {
    let (Value::Call(_, s1, _), Value::Call(_, s2, _)) = (a, b) else {
        unreachable!("two calls of one definition");
    };
    // Two calls of the same definition (`Value::Call`): their arguments
    // first, as for dictionaries below; otherwise their unfoldings.
    if same_arguments_solving_nothing(g, level, s1, s2)? {
        return Ok(Some(true));
    }
    // Calls of one definition, one written with an unknown for each
    // argument (`f _ _`) and its unfolding stuck on them: the most general
    // instance is the other's arguments. `List.range ?a ?b` unfolds to
    // `List.rangeFrom (?b - ?a) ?a`, which against `List.rangeFrom (n - 1) 2`
    // would read `?b - ?a` against `n - 1` before `?a` is known, and
    // guess `?b := n`; the arguments `2` and `n + 1` say what was written
    // (SW-1379). What they solve is noted as lossy, like any solution made
    // from arguments.
    if (all_unknown_arguments(g, s1)? || all_unknown_arguments(g, s2)?)
        && (blocked(g, a)? || blocked(g, b)?)
    {
        let trail = g.store.meta_trail.borrow().len();
        if same_arguments(g, level, s1, s2)? {
            note_lossy(g, trail);
            return Ok(Some(true));
        }
    }
    // Inside the first rule's comparison of arguments, two calls of one
    // definition whose arguments differ are answered "different" without
    // unfolding them (SW-1506). That comparison is only a shortcut: when it
    // says "different", the calls around it are unfolded and compared,
    // and these two with them where they matter, so nothing is lost but the
    // shortcut. Without this, each level of such calls is compared twice
    // over, once by the arguments of the level around it and once in its
    // unfolding, so `Parse.exactly 35 p` against `Parse.exactly 36 p` takes
    // about 2³⁵ comparisons. Not while solving from arguments
    // (`unify_solving_arguments`): there the comparison of arguments can
    // solve an unknown the unfolding is stuck on, so it is more than a
    // shortcut, and `pick ?b (two 3)` against `pick True (two 4)` needs
    // `two 3` and `two 4` unfolded inside it
    // (examples/accept/unknown-solved-from-call-arguments.sw); there the
    // record of pairs found different ([`CallMemo`]) keeps it linear.
    if g.attempt.argument_checks.get() > 0 && !g.attempt.solving_arguments.get() {
        return Ok(Some(false));
    }
    Ok(None)
}

/// [`unify_step`] after the rules for two calls of one definition: the
/// rules that look at `a` and `b` as they are, then those that force them,
/// then their shapes. Each part is out of line, so that this frame, under
/// every level of a comparison that recurses through it, is small.
#[inline(never)]
fn unify_step_rest(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<bool> {
    if let Some(answer) = unforced_rules(g, level, a, b, work)? {
        return Ok(answer);
    }
    match forced_rules(g, level, (a, b), work)? {
        Forced::Answer(answer) => Ok(answer),
        Forced::Shapes(forced_a, forced_b) => {
            unify_shapes(g, level, (a, b), (&forced_a, &forced_b), work)
        }
    }
}

/// [`unify_step_rest`]'s rules for `a` and `b` before they're forced: the
/// answer, or `None` to go on.
#[inline(never)]
fn unforced_rules(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<Option<bool>> {
    if one_step_apart(g, level, a, b)? {
        return Ok(Some(true));
    }
    if let Some(records) = same_field_calls(g, level, a, b)? {
        work.push(records);
        return Ok(Some(true));
    }
    if meta_against_call(g, level, a, b)? {
        return Ok(Some(true));
    }
    Ok(None)
}

/// What [`forced_rules`] found.
enum Forced {
    Answer(bool),
    /// No rule applied: the forced values, to compare by their shapes.
    Shapes(Value, Value),
}

/// [`unify_step_rest`]'s rules for `a` and `b` forced, before their shapes:
/// folded dictionaries, sums and numbers, and rows.
#[inline(never)]
fn forced_rules(
    g: &Unifier<'_>,
    level: usize,
    (a, b): (&Value, &Value),
    work: &mut Vec<Task>,
) -> Result<Forced> {
    let a = force(g, a.clone())?;
    let b = force(g, b.clone())?;
    let is_meta = |v: &Value| matches!(v, Value::Neutral(Head::Meta(_), _));
    // A constructor against a stuck field of a call (`(f x).i`, folded) is
    // left to rule 1 below, which keeps the call in what it solves.
    let ctor_against_field = |x: &Value, y: &Value| {
        matches!(x, Value::Ctor(d, 0, _) if is_eta_type(&g.ev, *d))
            && matches!(y, Value::Neutral(Head::Def(_), s) if is_call_field(s))
    };
    // Dictionaries left folded by name (`Def::fold`), as in `conv`: the same
    // one's arguments first (what that solves is kept only if they all
    // unify), otherwise unfolded. A metavariable against one is solved with
    // it, by name, below. Before numbers, as in `conv`.
    if !is_meta(&a)
        && !is_meta(&b)
        && (is_folded(g, &a) || is_folded(g, &b))
        && !ctor_against_field(&a, &b)
        && !ctor_against_field(&b, &a)
    {
        if let (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) = (&a, &b)
            && i1 == i2
            && same_arguments(g, level, s1, s2)?
        {
            return Ok(Forced::Answer(true));
        }
        let a2 = unfold_folded(g, &a)?;
        let b2 = unfold_folded(g, &b)?;
        if a2.is_some() || b2.is_some() {
            work.push(Task::Values(level, a2.unwrap_or(a), b2.unwrap_or(b)));
            return Ok(Forced::Answer(true));
        }
    }
    // A folded call eliminated further by a `J` or an application, as the
    // folded rule above and as in `conv`: the same call's whole spines
    // first (what that solves is kept only if all of it unifies), otherwise
    // unfolded with the rest applied (a `Quot.lift` returning a function,
    // `bumpBy q 3`, against the lift written out).
    if !is_meta(&a) && !is_meta(&b) && (unfolds_head(g, &a) || unfolds_head(g, &b)) {
        if let (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) = (&a, &b)
            && i1 == i2
            && same_arguments(g, level, s1, s2)?
        {
            return Ok(Forced::Answer(true));
        }
        let a2 = unfold_folded_head(g, &a)?;
        let b2 = unfold_folded_head(g, &b)?;
        if a2.is_some() || b2.is_some() {
            work.push(Task::Values(level, a2.unwrap_or(a), b2.unwrap_or(b)));
            return Ok(Forced::Answer(true));
        }
    }
    // A cast that was stuck on an unknown in its ends, which has been
    // solved since so that they meet: its base (rule K). Asked before the
    // two are compared as stuck casts, by their parts.
    if let Some(a2) = fire_cast(g, &a)? {
        work.push(Task::Values(level, a2, b));
        return Ok(Forced::Answer(true));
    }
    if let Some(b2) = fire_cast(g, &b)? {
        work.push(Task::Values(level, a, b2));
        return Ok(Forced::Answer(true));
    }
    // A sum stuck on its first argument, with a folded call in its second,
    // as what R3 and R4 make of it (G2), as in `conv`.
    let reread = |v: &Value| reread_sum(g, v);
    if let Some(a2) = reread(&a)? {
        work.push(Task::Values(level, a2, b));
        return Ok(Forced::Answer(true));
    }
    if let Some(b2) = reread(&b)? {
        work.push(Task::Values(level, a, b2));
        return Ok(Forced::Answer(true));
    }
    // A sum stuck on an unknown, by the rules of `+` read backwards.
    if let Some(answer) = plus_rule(g, level, &a, &b, work)? {
        return Ok(Forced::Answer(answer));
    }
    // Numbers compare by their `k + x` forms (see `conv`): `3` and `Succ ?x`
    // unify by solving `?x` with `2`, and `Succ (x + ?d)` and `Succ (Succ x)`
    // by `plus_rule`.
    if !is_meta(&a) && !is_meta(&b) && (native::nat_like(g, &a) || native::nat_like(g, &b)) {
        return native::compare(
            g,
            &a,
            &b,
            |x, y| {
                work.push(Task::Values(level, x.clone(), y.clone()));
                Ok(true)
            },
            |x, v| {
                if is_meta(x) {
                    return unify(g, level, x, v);
                }
                // A folded call against a different count of `Succ`s, as
                // in `conv` (SW-2157).
                if let Some(x) = unfold_folded(g, x)? {
                    return nested(g, || run(g, vec![Task::Values(level, x, v.clone())]));
                }
                if let Some(x) = reread(x)? {
                    return nested(g, || run(g, vec![Task::Values(level, x, v.clone())]));
                }
                let mut work = Vec::new();
                match plus_rule(g, level, x, v, &mut work)? {
                    Some(true) => nested(g, || run(g, work)),
                    _ => Ok(false),
                }
            },
        )
        .map(Forced::Answer);
    }
    // A computation type over a row unknown, against a type that settles it
    // (design C's apartness rule).
    if let Some(answer) = row_rule(g, level, &a, &b, work)? {
        return Ok(Forced::Answer(answer));
    }
    Ok(Forced::Shapes(a, b))
}

/// [`unify_step_rest`] by the shapes of `a` and `b`, forced from `unforced_a`
/// and `unforced_b`.
#[inline(never)]
fn unify_shapes(
    g: &Unifier<'_>,
    level: usize,
    (unforced_a, unforced_b): (&Value, &Value),
    (a, b): (&Value, &Value),
    work: &mut Vec<Task>,
) -> Result<bool> {
    Ok(match (a, b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1, m1), Value::Pi(_, i2, a2, b2, m2)) => {
            if i1 != i2 {
                return Ok(false);
            }
            work.push(Task::Codomains(level, b1.clone(), b2.clone(), m1.or(*m2)));
            work.push(Task::Values(level, (**a1).clone(), (**a2).clone()));
            true
        }
        (Value::Lam(_, _, b1, _), Value::Lam(_, _, b2, _)) if same_closure_solved(g, b1, b2)? => {
            true
        }
        (Value::Lam(_, _, b1, m1), Value::Lam(_, _, b2, m2)) => {
            let fresh = Value::var_marked(level, m1.or(*m2));
            work.push(Task::Values(
                level + 1,
                b1.apply(g, fresh.clone())?,
                b2.apply(g, fresh)?,
            ));
            true
        }
        (Value::Lam(_, i, b, mark), other) | (other, Value::Lam(_, i, b, mark)) => {
            if !can_apply(other) {
                return Ok(false);
            }
            let fresh = Value::var_marked(level, *mark);
            work.push(Task::Values(
                level + 1,
                b.apply(g, fresh.clone())?,
                apply_icit(g, other.clone(), fresh, *i)?,
            ));
            true
        }
        // Proof positions as in `conv`: a data type's proof parameters, and
        // a constructor's proof fields.
        (Value::Data(d1, a1), Value::Data(d2, a2)) => {
            if d1 != d2 || a1.len() != a2.len() {
                return Ok(false);
            }
            for (k, (x, y)) in a1.iter().zip(a2.iter()).enumerate().rev() {
                work.push(if proof_param(g, *d1, k) {
                    Task::Proof(level, x.clone(), y.clone())
                } else {
                    Task::Values(level, x.clone(), y.clone())
                });
            }
            true
        }
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            if d1 != d2 || c1 != c2 || a1.len() != a2.len() {
                return Ok(false);
            }
            for (k, (x, y)) in a1.iter().zip(a2.iter()).enumerate().rev() {
                work.push(if proof_field(g, *d1, *c1, k) {
                    Task::Proof(level, x.clone(), y.clone())
                } else {
                    Task::Values(level, x.clone(), y.clone())
                });
            }
            true
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            push_equations(work, level, [&**t1, &**x1, &**y1], [&**t2, &**x2, &**y2]);
            true
        }
        (Value::Refl, Value::Refl) => true,
        // Compact lists, as in `conv`: two ranges by their characters.
        (Value::Chars(x), Value::Chars(y)) => x.as_slice() == y.as_slice(),
        // A pending placeholder applied twice (`?p a` against `?p b`, stage
        // 6): its term may ignore an argument, so different arguments don't
        // make the two differ. Its arguments are compared on their own, and
        // if they differ, the whole pair waits for the placeholder.
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2))
            if m1 == m2 && pending(g, *m1) =>
        {
            match spine_pairs(level, s1, s2) {
                Some(pairs) => nested(g, || run(g, pairs.into_iter().rev().collect()))?,
                None => false,
            }
        }
        // The same unknown applied twice: its arguments, pairwise.
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2)) if m1 == m2 => {
            match spine_pairs(level, s1, s2) {
                Some(pairs) => {
                    work.extend(pairs.into_iter().rev());
                    true
                }
                None => false,
            }
        }
        // Solving a metavariable is a leaf: it builds a solution from the
        // other side, or tries matching last arguments.
        // A frozen metavariable is rigid: against a metavariable that isn't,
        // that one is solved; against anything else, they differ.
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2))
            if frozen(g, *m1) != frozen(g, *m2) =>
        {
            let (m, spine, other) = if frozen(g, *m1) {
                (*m2, s2, a)
            } else {
                (*m1, s1, b)
            };
            solve(g, level, m, spine, other)? || first_order(g, level, m, spine, other)?
        }
        // A number literal waiting for its type (K4) against the same
        // numeral at a known type (D2110, step 4.3): `k` checked at `Nat` is
        // the numeral `k`, and at `Int` is `OfNat k`, whether it waited or
        // not, so its term is forced to be `other`. The placeholder is
        // solved with it, though frozen (only here: its check's fill then
        // finds it solved and compares, invariant 2), and the type it waits
        // on is compared with that type. A placeholder applied to more than
        // variables isn't a pattern: the pair fails, as for any frozen one.
        (Value::Neutral(Head::Meta(m), spine), other)
        | (other, Value::Neutral(Head::Meta(m), spine))
            if let Some((waits_on, ty)) = literal_seen_through(g, *m, other) =>
        {
            if solve(g, level, *m, spine, other)? {
                work.push(Task::Values(level, waits_on, ty));
                true
            } else {
                false
            }
        }
        (Value::Neutral(Head::Meta(m), _), _) | (_, Value::Neutral(Head::Meta(m), _))
            if frozen(g, *m) =>
        {
            let awaited =
                |v: &Value| matches!(v, Value::Neutral(Head::Meta(m), _) if awaited_helper(g, *m));
            awaited(a) || awaited(b)
        }
        (Value::Neutral(Head::Meta(_), _), Value::Neutral(..))
        | (Value::Neutral(..), Value::Neutral(Head::Meta(_), _))
            if same_field_records(g, level, a, b)? =>
        {
            true
        }
        (Value::Neutral(..), Value::Neutral(..))
            if let Some(records) = same_field_types(g, level, a, b)? =>
        {
            work.push(records);
            true
        }
        // Two unknowns, one of which may ignore arguments that aren't
        // variables (`Meta::ignorable`): the other is solved with it if it
        // can be, so that the one that may ignore stays unsolved, rather
        // than being solved with a pruned copy of the other that may not
        // (SW-3890).
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2))
            if g.store.meta_ignorable(*m1).is_some() != g.store.meta_ignorable(*m2).is_some() =>
        {
            let (m, spine, other, (n, n_spine, n_other)) = if g.store.meta_ignorable(*m1).is_some()
            {
                (*m2, s2, a, (*m1, s1, b))
            } else {
                (*m1, s1, b, (*m2, s2, a))
            };
            solve(g, level, m, spine, other)?
                || solve(g, level, n, n_spine, n_other)?
                || first_order(g, level, n, n_spine, n_other)?
        }
        (Value::Neutral(Head::Meta(m), spine), other)
        | (other, Value::Neutral(Head::Meta(m), spine)) => {
            solve(g, level, *m, spine, other)? || first_order(g, level, *m, spine, other)?
        }
        // A range against anything else but a metavariable (which is solved
        // with the range itself, above): its first cell, as a constructor.
        // So `Cons ?c ?tail ~ "ab"` solves `?c` with `MkChar 97 byComputing` and
        // `?tail` with the range `"b"`.
        (Value::Chars(_), _) => {
            work.push(Task::Values(level, expand_step(g, a.clone()), b.clone()));
            true
        }
        (_, Value::Chars(_)) => {
            work.push(Task::Values(level, a.clone(), expand_step(g, b.clone())));
            true
        }
        // Two stuck casts: by their ends' type, ends, motive and base, then
        // what is applied to them; never by their proofs, as in `conv`
        // (docs/proposals/full-proof-irrelevance-audit.md, finding B).
        (Value::Neutral(_, s1), Value::Neutral(_, s2))
            if cast_at(s1).is_some() && cast_at(s2).is_some() =>
        {
            let (i, j) = (cast_at(s1).unwrap(), cast_at(s2).unwrap());
            let (
                Elim::J {
                    motive: m1,
                    base: b1,
                    ends: Some(e1),
                    ..
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                    ends: Some(e2),
                    ..
                },
            ) = (&s1[i], &s2[j])
            else {
                unreachable!("found by cast_at")
            };
            match (s1.len() - i == s2.len() - j)
                .then(|| spine_pairs(level, &s1[i + 1..], &s2[j + 1..]))
                .flatten()
            {
                Some(rest) => {
                    work.extend(rest.into_iter().rev());
                    let pairs = [
                        (&**b1, &**b2),
                        (&**m1, &**m2),
                        (&e1.y, &e2.y),
                        (&e1.x, &e2.x),
                        (&e1.ty, &e2.ty),
                    ];
                    for (x, y) in pairs {
                        work.push(Task::Values(level, x.clone(), y.clone()));
                    }
                    true
                }
                None => false,
            }
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) if h1 == h2 => {
            same_heads(g, level, (a, b), (h1, s1, s2), work)?
        }
        // Two different definitions stuck on a `case`: by their case trees,
        // as in `conv` (`same_stuck_trees`). What that solves is kept only
        // if they're equal. Pairs of calls found equal are remembered for the
        // rest of the outermost such comparison, and forgotten if a solution
        // is taken back (a new `meta_epoch`), so a chain of helpers each
        // calling the next in several branches is compared once per level.
        (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2))
            if i1 != i2 && opens_by_tree(g, a) && opens_by_tree(g, b) =>
        {
            different_stuck_trees(g, level, (a, b), (s1, s2))?
        }
        // Record eta, rule 1, as in `conv` (docs/proposals/record-eta.md
        // §6.3, §8): a constructor of a type with eta against an unknown
        // value, field by field against its projections; so `{ row = ?r, ..
        // }` against `p` solves `?r` as `p.row`. Unknowns come first (their
        // arms are above). Not against a value stuck on an unsolved unknown,
        // which may still compute to a constructor (it waits, as before),
        // and not inside `first_order`, whose pairs needn't have one type
        // (the same-type contract rule 1 relies on).
        (Value::Ctor(d, 0, fs), n @ Value::Neutral(..))
        | (n @ Value::Neutral(..), Value::Ctor(d, 0, fs))
            if is_eta_type(&g.ev, *d) && !NO_ETA.with(|c| c.get()) && !blocked(g, n)? =>
        {
            // The fields of a call that computed to `n` are taken of the
            // call ([`project_call`]): the same values, by definition, with
            // the call kept in what they solve, as rule 2 keeps it.
            let unforced = if std::ptr::eq(n, a) {
                unforced_a
            } else {
                unforced_b
            };
            push_fields(g, level, (*d, fs), (n, unforced), work);
            true
        }
        _ => push_eta(&g.ev, level, a, b, work)?,
    })
}

/// The parts of two equations, `t1`, `x1`, `y1` of `x1 = y1` at `t1` and
/// those of the other, as pairs to unify, the first first.
#[inline(never)]
fn push_equations(work: &mut Vec<Task>, level: usize, xs: [&Value; 3], ys: [&Value; 3]) {
    // Pushed last-first, so they're unified first-first.
    for (x, y) in xs.iter().zip(ys).rev() {
        work.push(Task::Values(level, (*x).clone(), y.clone()));
    }
}

/// Record eta ([`unify_shapes`]): the fields `fs` of a constructor of `d`
/// against the projections of `n`, the neutral value forced from
/// `unforced`, as pairs to unify, the first first.
#[inline(never)]
fn push_fields(
    g: &Unifier<'_>,
    level: usize,
    (d, fs): (stitchwort_core::DataId, &[Value]),
    (n, unforced): (&Value, &Value),
    work: &mut Vec<Task>,
) {
    for (k, x) in fs.iter().enumerate().rev() {
        let projected = match unforced {
            call @ Value::Call(..) => project_call(d, k, call.clone()),
            _ => project(d, k, n.clone()),
        };
        work.push(if proof_field(g, d, 0, k) {
            Task::Proof(level, x.clone(), projected)
        } else {
            Task::Values(level, x.clone(), projected)
        });
    }
}

/// [`unify_shapes`] for two neutral values `a` and `b` with the same head
/// `h1`, applied to the spines `s1` and `s2`.
#[inline(never)]
fn same_heads(
    g: &Unifier<'_>,
    level: usize,
    (a, b): (&Value, &Value),
    (h1, s1, s2): (&Head, &Spine, &Spine),
    work: &mut Vec<Task>,
) -> Result<bool> {
    let def = match h1 {
        Head::Def(f) => Some(*f),
        _ => None,
    };
    Ok(
        if let Some(f) = def
            && sealed(g, f)
        {
            // A hidden opaque call, a proof (rule F), or a call of a member
            // of the group being checked: compared by its arguments, as
            // the kernel compares them.
            match spine_pairs(level, s1, s2) {
                Some(pairs) => nested(g, || run(g, pairs.into_iter().rev().collect()))?,
                None => false,
            }
        } else if underapplied(g, a).is_none() && underapplied(g, b).is_none() {
            // Eta for definitions doesn't apply, so the spines must match.
            // Calls stuck on an unknown may be equal without that, once it
            // is solved: their spines are compared here, so that if they
            // differ, the calls are put aside whole ([`run`]). A call
            // whose spine mentions an unknown, frozen or not and however
            // deep, may unfold once it's solved; only one stuck on an
            // unknown `blocked` sees is put aside.
            match spine_pairs(level, s1, s2) {
                Some(pairs) if matches!(h1, Head::Def(_)) && (blocked(g, a)? || blocked(g, b)?) => {
                    let trail = g.store.meta_trail.borrow().len();
                    let same = nested(g, || run(g, pairs.into_iter().rev().collect()))?;
                    note_lossy(g, trail);
                    same
                }
                Some(pairs)
                    if matches!(h1, Head::Def(_))
                        && (may_mention_meta(s1) || may_mention_meta(s2)) =>
                {
                    work.extend(pairs.into_iter().rev());
                    true
                }
                // Two calls of one definition stuck on a `case`, with no
                // unknown in sight: equal arguments make them equal, but
                // different ones don't make them different, so then
                // they're compared by their case trees, as `conv` does
                // (G6, docs/core.md). Whatever the failed try solved is
                // taken back first. A "different" is remembered only if
                // neither spine may mention an unknown (`same_stuck_trees`).
                Some(pairs) if opens_by_tree(g, a) && opens_by_tree(g, b) => {
                    let trail = g.store.meta_trail.borrow().len();
                    let arguments = |_: CompareAt<'_>| -> Result<bool> {
                        let spines = nested(g, || run(g, pairs.into_iter().rev().collect()))?;
                        if !spines {
                            undo_since(g, trail);
                        }
                        Ok(spines)
                    };
                    let same = same_stuck_trees(
                        g,
                        level,
                        a,
                        b,
                        Relation::Unify,
                        !NO_ETA.with(|c| c.get()) && !may_mention_meta(s1) && !may_mention_meta(s2),
                        arguments,
                        &mut |l, x, y| unify_in(g, l, x, y),
                    )?;
                    if !same {
                        undo_since(g, trail);
                    }
                    same
                }
                Some(pairs) => {
                    work.extend(pairs.into_iter().rev());
                    true
                }
                None => false,
            }
        } else {
            // A function: the spines, or else eta. The one place this
            // recurses, once per level of nested partially applied
            // definitions.
            let spines = match spine_pairs(level, s1, s2) {
                Some(pairs) => {
                    let mut same = true;
                    for pair in pairs {
                        if !unify_pair(g, pair)? {
                            same = false;
                            break;
                        }
                    }
                    same
                }
                None => false,
            };
            spines || push_eta(&g.ev, level, a, b, work)?
        },
    )
}

/// [`unify_shapes`] for two different definitions, `a` and `b` applied to
/// `s1` and `s2`, stuck on a `case`: by their case trees, as in `conv`.
#[inline(never)]
fn different_stuck_trees(
    g: &Unifier<'_>,
    level: usize,
    (a, b): (&Value, &Value),
    (s1, s2): (&Spine, &Spine),
) -> Result<bool> {
    let trail = g.store.meta_trail.borrow().len();
    let settled = !NO_ETA.with(|c| c.get()) && !may_mention_meta(s1) && !may_mention_meta(s2);
    let same = same_stuck_trees(
        g,
        level,
        a,
        b,
        Relation::Unify,
        settled,
        |_| Ok(false),
        &mut |l, x, y| unify_in(g, l, x, y),
    )?;
    if !same {
        undo_since(g, trail);
    }
    Ok(same)
}

thread_local! {
    /// Set while `first_order` pairs last arguments, whose types needn't
    /// agree: record eta is off there.
    static NO_ETA: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Record eta (docs/proposals/record-eta.md §8): the same field of an
/// unknown and of another value, `?b.items` against `b.items`, compared by
/// their records first. Rule 2 leaves a call stuck on `?b` at `?b.items`
/// while the same call on `b` runs on to `b.items`; without eta, both stopped
/// at a call of the projection function (`Bag.items ?b` against `Bag.items
/// b`), whose arguments were unified. This keeps that answer. One field
/// doesn't determine `?b`, so it's a first try only: undone if the records
/// don't unify, and what it solves is noted as lossy.
fn same_field_records(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) = (a, b) else {
        return Ok(false);
    };
    let (Some(Elim::Proj(d1, i1)), Some(Elim::Proj(d2, i2))) = (s1.last(), s2.last()) else {
        return Ok(false);
    };
    if (d1, i1) != (d2, i2) {
        return Ok(false);
    }
    // A stuck field of a call kept by name, `(f x).i` (`Frame::CallField`,
    // `is_folded`), is a `Def` head whose spine is the call's arguments and
    // then projections. Its record is the call `f x`, glued, which forces to
    // what `f x` computed to; as the neutral `f x` it would claim the call
    // is stuck itself, and so never equal to `?r.f` (`(Cavern.grid c).rows`
    // against `?c.grid.rows`). Any other `Def` head is a definition that is
    // stuck, and stays one without the projection.
    let record = |v: &Value, h: &Head, s: &Spine| {
        let spine = Spine::from(s[..s.len() - 1].to_vec());
        match h {
            Head::Def(id) if g.machine.glue.get() && is_folded(g, v) => {
                Value::Call(*id, spine, Default::default())
            }
            _ => Value::Neutral(*h, spine),
        }
    };
    let trail = g.store.meta_trail.borrow().len();
    let task = Task::Values(level, record(a, h1, s1), record(b, h2, s2));
    if nested(g, || run(g, vec![task]))? {
        note_lossy(g, trail);
        Ok(true)
    } else {
        undo_since(g, trail);
        Ok(false)
    }
}

/// Lazy delta, aimed narrowly (docs/proposals/proofs-about-definitions.md
/// §5 A, D2341): a call of one definition with an unknown for a whole
/// argument, `Effect.bind (?p ()) ?j`, against a call of another, `line ()`,
/// is equal to it if unfolding the other a step at a time, to its body with
/// its own calls still folded, reaches a call of the first definition whose
/// arguments unify with these. What that solves is kept, unlike for two
/// calls of one definition compared in [`unify_step`]'s first rule: the
/// unknown blocks the first call's computation while the other's goes on,
/// so comparing their unfoldings can't solve it.
///
/// Only the side with no such unknown is unfolded, at most
/// [`UNFOLD_STEPS`] times. `false`, with nothing solved, if the heads don't
/// meet or the arguments don't unify, and the caller compares the two as
/// before. A call whose unknowns are deeper, `List.sum [?x, ..?xs]`, can
/// take a step itself, so the unfoldings are compared as before: solving
/// from arguments there can choose another solution than they would.
fn one_step_apart(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    match meeting(g, a, b, false)? {
        Some((_, spine, args)) => same_arguments(g, level, &spine, &args),
        None => Ok(false),
    }
}

/// Where [`one_step_apart`] finds `a` and `b` meet: the definition, the
/// spine of the call with an unknown argument, and that of the other call
/// unfolded to one of the same definition. `abbreviation`: also where the
/// two compute to the same outer layer, if the other call is the
/// definition with arguments filled in, one unfolding away
/// ([`unify_abbreviation`]).
fn meeting(
    g: &Unifier<'_>,
    a: &Value,
    b: &Value,
    abbreviation: bool,
) -> Result<Option<(DefId, Spine, Spine)>> {
    let (Value::Call(i1, s1, _), Value::Call(i2, s2, _)) = (a, b) else {
        return Ok(None);
    };
    // Fields of calls aren't calls of their definition.
    if i1 == i2 || !g.machine.glue.get() || is_call_field(s1) || is_call_field(s2) {
        return Ok(None);
    }
    let (head, spine, mut other) = match (unknown_argument(g, s1)?, unknown_argument(g, s2)?) {
        (true, false) => (*i1, s1, b.clone()),
        (false, true) => (*i2, s2, a.clone()),
        _ => return Ok(None),
    };
    let steps = if !same_outer_layer(&force(g, a.clone())?, &force(g, b.clone())?) {
        UNFOLD_STEPS
    } else if abbreviation {
        1
    } else {
        return Ok(None);
    };
    for _ in 0..steps {
        let Value::Call(id, args, _) = &other else {
            return Ok(None);
        };
        other = unfold_once(g, *id, args.clone())?;
        if let Value::Call(id, args, _) = &other
            && *id == head
            && !is_call_field(args)
        {
            return Ok(Some((head, spine.clone(), args.clone())));
        }
    }
    Ok(None)
}

/// `a` against `b`, where one is a call with an unknown argument and the
/// other a call of another definition that is the first's with arguments
/// filled in (`ReadsIn ?inv ?p ?spec` against `Reads starting Written`,
/// `Reads` defined as `ReadsIn any`): `None` if they aren't, or else
/// whether their arguments unify, solving the unknowns. [`unify`] leaves
/// such pairs to their unfoldings when both compute to the same outer
/// layer, as these compute to `∀`s, and there `?inv.holds m` meets
/// `Unit`, which no first-order solution makes equal (SW-3534). Only the
/// elaborator's comparison with an expected type as written asks this,
/// after the plain comparison failed: inside [`unify`], solving from the
/// arguments where the unfoldings would also meet can choose another
/// solution (examples/accept/lazy-delta-deeper-unknown.sw).
pub(crate) fn unify_abbreviation(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<Option<bool>> {
    match meeting(g, a, b, true)? {
        Some((_, spine, args)) => Ok(Some(same_arguments(g, level, &spine, &args)?)),
        None => Ok(None),
    }
}

/// How many one-step unfoldings [`one_step_apart`] takes before giving up.
const UNFOLD_STEPS: usize = 4;

/// Whether two forced values have the same outermost layer, or one is an
/// unknown: then comparing them as they are takes a step (by their spines,
/// fields or bodies, or by solving the unknown), and [`one_step_apart`]
/// leaves them to that. `List.sum ?xs` and `aimedDepth b rest` both
/// compute to a `List.foldLeft` stuck on its list, whose spines solve
/// `?xs`; `Effect.bind (?p ()) ?j` is stuck on `?p ()` where `line ()`
/// computes further.
fn same_outer_layer(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Neutral(Head::Meta(_), _), _) | (_, Value::Neutral(Head::Meta(_), _)) => true,
        (Value::Neutral(h1, _), Value::Neutral(h2, _)) => h1 == h2,
        (Value::Ctor(d1, c1, _), Value::Ctor(d2, c2, _)) => d1 == d2 && c1 == c2,
        (Value::Data(d1, _), Value::Data(d2, _)) => d1 == d2,
        _ => std::mem::discriminant(a) == std::mem::discriminant(b),
    }
}

/// Whether `spine` has an argument, and each is an unsolved unknown (applied to
/// the context, perhaps) that isn't frozen.
fn all_unknown_arguments(g: &Unifier<'_>, spine: &[Elim]) -> Result<bool> {
    let mut any = false;
    for elim in spine {
        if let Elim::App(arg, _) = elim {
            match force_solved(g, arg.clone())? {
                Value::Neutral(Head::Meta(m), _) if !frozen(g, m) => any = true,
                _ => return Ok(false),
            }
        }
    }
    Ok(any)
}

/// Whether some argument in `spine` is, once solutions are put in, an
/// unknown that can still be solved, or one applied: `?p ()`, `?j`.
fn unknown_argument(g: &Unifier<'_>, spine: &[Elim]) -> Result<bool> {
    for elim in spine {
        if let Elim::App(arg, _) = elim
            && let Value::Neutral(Head::Meta(m), _) = force_solved(g, arg.clone())?
            && !frozen(g, m)
        {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Whether the spines of two calls of one definition unify, element by
/// element: the calls are glued or folded, and are compared by their
/// unfoldings if this fails, as the kernel does. Proof arguments are equal
/// by rule I, and unfolding never reads a proof (rules K, S and F), so this
/// agrees with unfolding. What that solves is kept only if they all do.
fn same_arguments(g: &Unifier<'_>, level: usize, s1: &[Elim], s2: &[Elim]) -> Result<bool> {
    let Some(pairs) = spine_pairs(level, s1, s2) else {
        return Ok(false);
    };
    let trail = g.store.meta_trail.borrow().len();
    for pair in pairs {
        if !unify_pair(g, pair)? {
            undo_since(g, trail);
            return Ok(false);
        }
    }
    Ok(true)
}

/// [`same_arguments`], but only if that solves no metavariable: two calls
/// whose arguments unify only by solving one are compared by their
/// unfoldings instead, with nothing solved, as without gluing. Solving
/// from the arguments can choose a different solution than the unfoldings
/// would (`Nat.div m d ?ok` against `Nat.div m d p` solves `?ok := p`,
/// where `Nat.div`'s unfolding doesn't mention the proof and leaves `?ok`
/// to `auto`), which would change elaborated terms; gluing doesn't change
/// them until folded read-back (docs/proposals/folded-calls.md §7, stage 2).
fn same_arguments_solving_nothing(
    g: &Unifier<'_>,
    level: usize,
    s1: &[Elim],
    s2: &[Elim],
) -> Result<bool> {
    let trail = g.store.meta_trail.borrow().len();
    let open = g.attempt.argument_checks.get();
    let same = {
        let _open = ScopedCell::set(&g.attempt.argument_checks, open + 1);
        same_arguments(g, level, s1, s2)?
    };
    if !same {
        return Ok(false);
    }
    if g.store.meta_trail.borrow().len() > trail && !g.attempt.solving_arguments.get() {
        undo_since(g, trail);
        return Ok(false);
    }
    Ok(true)
}

/// Undoes the metavariable solutions made since the trail was `len` long.
pub(crate) fn undo_since(g: &Unifier<'_>, len: usize) {
    let mut metas = g.store.metas.borrow_mut();
    let mut trail = g.store.meta_trail.borrow_mut();
    if trail.len() > len {
        g.store.metas_taken_back();
        g.attempt.forget_lossy_since(len);
    }
    while trail.len() > len {
        let (m, old) = trail.pop().expect("longer");
        if let Some(meta) = metas.get_mut(m) {
            meta.solution = old;
        }
    }
}

/// The pairs of values in two spines, or `None` if they differ in length or
/// their eliminations don't match. Proof arguments are paired like any
/// others, and rule I answers for them ([`unify_step`]).
fn spine_pairs(level: usize, s1: &[Elim], s2: &[Elim]) -> Option<Vec<Task>> {
    if s1.len() != s2.len() {
        return None;
    }
    let mut pairs = Vec::new();
    for pair in s1.iter().zip(s2) {
        match pair {
            (Elim::App(x, _), Elim::App(y, _)) => {
                pairs.push(Task::Values(level, x.clone(), y.clone()));
            }
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                    ..
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                    ..
                },
            ) => {
                pairs.push(Task::Values(level, (**m1).clone(), (**m2).clone()));
                pairs.push(Task::Values(level, (**b1).clone(), (**b2).clone()));
            }
            (Elim::Proj(d1, i1), Elim::Proj(d2, i2)) if d1 == d2 && i1 == i2 => {}
            _ => return None,
        }
    }
    Some(pairs)
}

/// One pair from [`spine_pairs`], unified on its own.
fn unify_pair(g: &Unifier<'_>, pair: Task) -> Result<bool> {
    match pair {
        Task::Values(l, x, y) => unify_in(g, l, &x, &y),
        Task::Proof(l, x, y) => proof_position(g, l, &x, &y),
        Task::Codomains(..) | Task::Later(..) | Task::Open(..) => {
            unreachable!("not from spine_pairs")
        }
    }
}

/// Two values at a position the kernel's comparison skips: a proof
/// (docs/proposals/proof-irrelevance.md §7.5). If the whole of one side is
/// an unknown that can be solved, it's solved with the other side, as
/// anywhere else: that keeps implicit proof arguments and `auto`'s
/// placeholders working, and the two have one type (§7.4), so the solution
/// is well typed. Otherwise the position is opaque: equal, without looking
/// inside either side or solving anything from what's there.
fn proof_position(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let a = force(g, a.clone())?;
    let b = force(g, b.clone())?;
    for (side, other) in [(&a, &b), (&b, &a)] {
        if let Value::Neutral(Head::Meta(m), spine) = side
            && !frozen(g, *m)
        {
            let trail = g.store.meta_trail.borrow().len();
            if solve(g, level, *m, spine, other)? {
                return Ok(true);
            }
            undo_since(g, trail);
        }
    }
    Ok(true)
}

/// Whether `v` can be applied to an argument. A comparison of values of
/// different types (the last arguments [`first_order`] pairs up, say) can
/// put a function against a constructor, which is simply unequal.
fn can_apply(v: &Value) -> bool {
    matches!(v, Value::Lam(..) | Value::Neutral(..) | Value::Call(..))
}

/// Eta for definitions: pushes both sides applied to a fresh variable, or
/// returns `false` if neither is a partially applied definition.
fn push_eta(g: &Ev, level: usize, a: &Value, b: &Value, work: &mut Vec<Task>) -> Result<bool> {
    let next = |v| stitchwort_core::value::next_parameter(g, v);
    let Some((icit, mark)) = next(a).or_else(|| next(b)) else {
        return Ok(false);
    };
    if !can_apply(a) || !can_apply(b) {
        return Ok(false);
    }
    let fresh = Value::var_marked(level, mark);
    work.push(Task::Values(
        level + 1,
        apply_icit(g, a.clone(), fresh.clone(), icit)?,
        apply_icit(g, b.clone(), fresh, icit)?,
    ));
    Ok(true)
}

/// When `?m … x = f … y` isn't a pattern (`x` isn't a variable), tries
/// matching the last arguments and then the rest: `?m … = f …` and `x = y`.
/// This finds *a* solution, not necessarily the most general one, which is
/// fine because the kernel re-checks the result.
///
/// Unlike every other rule here, this one pairs values that needn't have the
/// same type: `?p True = t ?g` (with `?p: Bool → Type` and `t: (Nat → Nat)
/// → Type`) would solve `?g: Nat → Nat` with `True`, and the elaborator
/// evaluates `?g 0` long before the kernel sees it (SW-919). So the pairs
/// are refused when their types are known to differ ([`apart`]).
fn first_order(
    g: &Unifier<'_>,
    level: usize,
    m: usize,
    spine: &[Elim],
    other: &Value,
) -> Result<bool> {
    let Value::Neutral(head, other_spine) = other else {
        return Ok(false);
    };
    let (Some((Elim::App(x, i1), rest1)), Some((Elim::App(y, i2), rest2))) =
        (spine.split_last(), other_spine.split_last())
    else {
        return Ok(false);
    };
    if i1 != i2 {
        return Ok(false);
    }
    let left = Value::Neutral(Head::Meta(m), rest1.to_vec().into());
    let right = Value::Neutral(*head, rest2.to_vec().into());
    // The heads' types first: `?le ?x ?z = all ys p` makes `?le ?x`'s
    // type, `?a → Bool` (with `?le: ?a → ?a → Bool`), the same as `all
    // ys`'s, `(b → Bool) → Bool`, so `?a` is `b → Bool`, and pairing `?x`
    // with `ys`, a `List b`, is refused below. Without it `?a` is unknown
    // when each pair is looked at, and both are taken, solving `?le` with a
    // function of another type (SW-4564).
    learn_types(g, level, &left, &right)?;
    let types_agree = learn_types(g, level, x, y)?;
    if apart(g, level, x, y)? || apart(g, level, &left, &right)? {
        return Ok(false);
    }
    // `x` and `y` needn't have one type here, so two proofs are equal by
    // rule I only once their types are known to agree; otherwise only if
    // they're the same proof. Else `?m h1 = f h2`, with `h1` and `h2`
    // proving different statements, would solve `?m := f` with the wrong
    // type (docs/proposals/full-proof-irrelevance-audit.md, finding D).
    if !types_agree && both_proofs(g, x, y)? && !stitchwort_core::value::same_value(x, y) {
        return Ok(false);
    }
    let mark = g.store.meta_trail.borrow().len();
    let outer = NO_ETA.with(|c| c.replace(true));
    let same = unify_in(g, level, x, y);
    NO_ETA.with(|c| c.set(outer));
    if !same? {
        return Ok(false);
    }
    // Pairing the last arguments can solve `?m` itself: `?m a b = f c ?m`
    // pairs `b` with `?m`. If that made it something that can't be applied
    // (a constructor, say), the two sides differ, and the solution is taken
    // back: comparing anything with `?m a` would apply it, and core panics
    // on that (SW-924, found by search).
    if !rest1.is_empty()
        && let Some(solved) = g.meta_solution(m)
        && !can_apply(&force(g, solved)?)
    {
        undo_since(g, mark);
        return Ok(false);
    }
    unify(g, level, &left, &right)
}

/// For [`first_order`], about to pair `a` with `b`: if both their types are
/// known in full ([`type_of`]), they are unified, so that the unknowns in
/// them (an unknown's recorded type `?a`) are solved before [`apart`]
/// looks at the next pair. Equal values have equal types, so a solution
/// found here is one the pairing needs anyway. If the types don't unify,
/// whatever that solved is taken back and nothing is learned: [`apart`]
/// still decides whether to refuse, as it did before. `true` when the two
/// types were known and unified.
fn learn_types(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let (Some(Known::Type(ta)), Some(Known::Type(tb))) = (type_of(g, a)?, type_of(g, b)?) else {
        return Ok(false);
    };
    let mark = g.store.meta_trail.borrow().len();
    if !unify(g, level, &ta, &tb)? {
        undo_since(g, mark);
        return Ok(false);
    }
    Ok(true)
}

/// What a value's type is known to be, for [`apart`]: the type itself, or
/// only its outermost form.
enum Known {
    Type(Value),
    Form(Rigid),
}

/// Whether values `a` and `b` (in a context of `level` variables) surely
/// have different types: both types are known, as far as their outermost
/// forms (and a function type's domain and codomain), and those differ. Only
/// a guard: `false` whenever either type is unknown.
fn apart(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let (Some(ta), Some(tb)) = (type_of(g, a)?, type_of(g, b)?) else {
        return Ok(false);
    };
    match (ta, tb) {
        (Known::Type(ta), Known::Type(tb)) => types_apart(g, level, &ta, &tb, 2),
        (Known::Type(t), Known::Form(f)) | (Known::Form(f), Known::Type(t)) => {
            Ok(form(g, &t)?.is_some_and(|tf| tf != f))
        }
        (Known::Form(fa), Known::Form(fb)) => Ok(fa != fb),
    }
}

/// Whether types `a` and `b` surely differ: their forms do, or (for
/// `depth` levels of function types) their domains or codomains do.
fn types_apart(g: &Unifier<'_>, level: usize, a: &Value, b: &Value, depth: usize) -> Result<bool> {
    let a = force(g, a.clone())?;
    let b = force(g, b.clone())?;
    if let (Value::Pi(_, i1, d1, c1, _), Value::Pi(_, i2, d2, c2, _)) = (&a, &b) {
        if i1 != i2 {
            return Ok(true);
        }
        if depth == 0 {
            return Ok(false);
        }
        let fresh = Value::var(level);
        return Ok(types_apart(g, level, d1, d2, depth - 1)?
            || types_apart(
                g,
                level + 1,
                &c1.apply(g, fresh.clone())?,
                &c2.apply(g, fresh)?,
                depth - 1,
            )?);
    }
    Ok(match (form(g, &a)?, form(g, &b)?) {
        (Some(fa), Some(fb)) => fa != fb,
        _ => false,
    })
}

/// The outermost form of type `ty`, if no solution of an unknown can change
/// it ([`rigid_head`]). A type variable doesn't count: an unknown's
/// recorded type is in the context it was made in, where its arguments may
/// since stand for other values.
fn form(g: &Ev, ty: &Value) -> Result<Option<Rigid>> {
    let ty = force(g, ty.clone())?;
    Ok(rigid_head(g, &ty).filter(|r| *r != Rigid::Var))
}

/// What's known of `v`'s type without a context: a constructor's, a
/// number's, a type's, a function's form; a definition's, or an unknown's
/// recorded one ([`stitchwort_core::globals::Meta::ty`]), applied to its
/// arguments. `None` for a variable, or anything else.
fn type_of(g: &Unifier<'_>, v: &Value) -> Result<Option<Known>> {
    let v = force(g, v.clone())?;
    let (ty, args) = match &v {
        Value::Ctor(d, ..) => return Ok(Some(Known::Form(Rigid::Data(*d)))),
        Value::Nat(_) | Value::NatAdd(..) => {
            return Ok(g.env.builtins().nat.map(|d| Known::Form(Rigid::Data(d))));
        }
        Value::Sort(_) | Value::Pi(..) | Value::Data(..) | Value::Eq(..) => {
            return Ok(Some(Known::Form(Rigid::Sort)));
        }
        Value::Refl => return Ok(Some(Known::Form(Rigid::Eq))),
        Value::Lam(..) => return Ok(Some(Known::Form(Rigid::Pi))),
        Value::Neutral(Head::Def(id), spine) | Value::Call(id, spine, _) => {
            (g.def(*id).ty_value().clone(), &spine[..])
        }
        Value::Neutral(Head::Meta(m), spine) => match g.store.meta_type(*m) {
            Some((ty, arity)) if arity <= spine.len() => (ty, &spine[arity..]),
            _ => return Ok(None),
        },
        _ => return Ok(None),
    };
    // The value so far, for a projection's later fields, whose types mention
    // the earlier ones.
    let (head, start) = match &v {
        Value::Neutral(h, spine) => (Some(*h), spine.len() - args.len()),
        _ => (None, 0),
    };
    let mut ty = ty;
    for (k, elim) in args.iter().enumerate() {
        match elim {
            Elim::App(arg, _) => {
                let Value::Pi(_, _, _, cod, _) = force(g, ty)? else {
                    return Ok(None);
                };
                ty = cod.apply(g, arg.clone())?;
            }
            Elim::Proj(d, i) => {
                let (Value::Data(d2, params), Some(head)) = (force(g, ty)?, head) else {
                    return Ok(None);
                };
                let data = g.data(*d);
                if d2 != *d || data.ctors().len() != 1 {
                    return Ok(None);
                }
                let Value::Neutral(_, spine) = &v else {
                    return Ok(None);
                };
                let record = Value::Neutral(head, Spine::from(spine[..start + k].to_vec()));
                let mut env: Vec<Value> = params.to_vec();
                for j in 0..*i {
                    env.push(project(*d, j, record.clone()));
                }
                let Some((_, field)) = data.ctors()[0].fields.get(*i) else {
                    return Ok(None);
                };
                ty = eval(g, &env, field)?;
            }
            _ => return Ok(None),
        }
    }
    Ok(Some(Known::Type(ty)))
}

/// The same field of two records of a type with parameters, whose records
/// don't unify yet, `(?d.decide ?x ?y).holds` against `(List.decEq f xs
/// ys).holds`: their types' parameters unified, and the records left to the
/// main comparison, which can put them aside until the unknown in the way
/// is solved. A projection doesn't keep its record type's parameters
/// (`Term::Proj`), where a call of the projection function did (`Decidable.holds
/// [p] d`), so without this the parameters' unknowns (`?x`, `?y`) would be
/// lost. Lossy, as [`same_field_records`] is: the pair it gives is a
/// sufficient condition, not a necessary one.
fn same_field_types(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<Option<Task>> {
    let (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) = (a, b) else {
        return Ok(None);
    };
    let (Some(Elim::Proj(d1, i1)), Some(Elim::Proj(d2, i2))) = (s1.last(), s2.last()) else {
        return Ok(None);
    };
    if (d1, i1) != (d2, i2) || g.data(*d1).params().is_empty() {
        return Ok(None);
    }
    // As in [`same_field_records`]: a stuck field of a call kept by name has
    // the call, glued, as its record.
    let record = |v: &Value, h: &Head, s: &Spine| {
        let spine = Spine::from(s[..s.len() - 1].to_vec());
        match h {
            Head::Def(id) if g.machine.glue.get() && is_folded(g, v) => {
                Value::Call(*id, spine, Default::default())
            }
            _ => Value::Neutral(*h, spine),
        }
    };
    let record_a = record(a, h1, s1);
    let record_b = record(b, h2, s2);
    let params = |v: &Value| -> Result<Option<Vec<Value>>> {
        let Some(Known::Type(ty)) = type_of(g, v)? else {
            return Ok(None);
        };
        Ok(match force(g, ty)? {
            Value::Data(d, args) if d == *d1 => Some(args.to_vec()),
            _ => None,
        })
    };
    let (Some(pa), Some(pb)) = (params(&record_a)?, params(&record_b)?) else {
        return Ok(None);
    };
    if pa.len() != pb.len() {
        return Ok(None);
    }
    let trail = g.store.meta_trail.borrow().len();
    let tasks: Vec<Task> = pa
        .into_iter()
        .zip(pb)
        .rev()
        .map(|(x, y)| Task::Values(level, x, y))
        .collect();
    if nested(g, || run(g, tasks))? && g.store.meta_trail.borrow().len() > trail {
        note_lossy(g, trail);
        Ok(Some(Task::Values(level, record_a, record_b)))
    } else {
        undo_since(g, trail);
        Ok(None)
    }
}

/// Two calls that reach one record's projection function,
/// `Decidable.holds [?p] r` against `Decidable.holds [p] d` where the second
/// computes on (to `Nat.equal m n`) and the first is stuck: the type's
/// parameters unified, and the records left to the main comparison, which
/// can put them aside until an unknown in the way is solved. So they meet
/// as they did before record eta, when both stopped at the call. The other
/// call may reach the projection by unfolding a step at a time, as in
/// [`one_step_apart`]: `near a b`, defined as `Succ a == b`, computes past
/// `Nat.decEq`'s record to `Nat.equal (Succ a) b`, which has lost the
/// decision, but its unfolding one step has it. Only when a parameter
/// mentions an unknown that this solves, and lossy, as for
/// [`same_field_records`]: one field doesn't determine a record. Without
/// it, `DecEq.sound e` for `e: (m == n) = True` on numbers can't find `m`
/// and `n`.
fn same_field_calls(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<Option<Task>> {
    if !matches!(a, Value::Call(..) | Value::Neutral(Head::Meta(_), _))
        || !matches!(b, Value::Call(..) | Value::Neutral(Head::Meta(_), _))
        || !g.machine.glue.get()
    {
        return Ok(None);
    }
    // A solved unknown (`Bool.orElim`'s `?a`, solved as `n == 3`) stands for
    // its solution, which keeps the call.
    let (a, b) = (&force_solved(g, a.clone())?, &force_solved(g, b.clone())?);
    let (Value::Call(i1, s1, _), Value::Call(i2, s2, _)) = (a, b) else {
        return Ok(None);
    };
    if g.attempt.argument_checks.get() > 0 || is_call_field(s1) || is_call_field(s2) {
        return Ok(None);
    }
    let (field, s1, mut other) = match (projection_of(g, *i1), projection_of(g, *i2)) {
        (Some(f), _) => (f, s1, b.clone()),
        (None, Some(f)) => (f, s2, a.clone()),
        (None, None) => return Ok(None),
    };
    let s2 = 'found: {
        for _ in 0..=UNFOLD_STEPS {
            let Value::Call(id, args, _) = &other else {
                return Ok(None);
            };
            if is_call_field(args) {
                return Ok(None);
            }
            if projection_of(g, *id) == Some(field) {
                break 'found args.clone();
            }
            other = unfold_once(g, *id, args.clone())?;
        }
        return Ok(None);
    };
    let np = g.data(field.0).params().len();
    if np == 0
        || s1.len() != np + 1
        || s2.len() != np + 1
        || !(may_mention_meta(s1) || may_mention_meta(&s2))
    {
        return Ok(None);
    }
    let arg = |e: &Elim| match e {
        Elim::App(v, _) => Some(v.clone()),
        _ => None,
    };
    let mut tasks = Vec::new();
    for (x, y) in s1[..np].iter().zip(&s2[..np]).rev() {
        let (Some(x), Some(y)) = (arg(x), arg(y)) else {
            return Ok(None);
        };
        tasks.push(Task::Values(level, x, y));
    }
    let (Some(r1), Some(r2)) = (arg(&s1[np]), arg(&s2[np])) else {
        return Ok(None);
    };
    let trail = g.store.meta_trail.borrow().len();
    if nested(g, || run(g, tasks))? && g.store.meta_trail.borrow().len() > trail {
        note_lossy(g, trail);
        Ok(Some(Task::Values(level, r1, r2)))
    } else {
        undo_since(g, trail);
        Ok(None)
    }
}

/// The record type of `id` and the field it gives, if it is a record's
/// generated projection: one `case` on its last parameter, a value of a
/// type with eta, giving one of the fields.
fn projection_of(g: &Unifier<'_>, id: DefId) -> Option<(stitchwort_core::DataId, usize)> {
    let mut body = g.def(id).body()?.strip_loc();
    while let Term::Lam(_, _, b, _) = body {
        body = b.strip_loc();
    }
    match body {
        Term::Case(0, d, branches) if is_eta_type(&g.ev, *d) && branches.len() == 1 => {
            let branch = &branches[0];
            match branch.body.as_deref().map(Term::strip_loc) {
                Some(Term::Var(k)) if *k < branch.names.len() => {
                    Some((*d, branch.names.len() - 1 - k))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// An unsolved metavariable against a glued call (`?x` against `invalid r`):
/// solved with the call itself, before anything forces it, so the solution
/// is written as the call ([`rename`]; docs/proposals/folded-calls.md,
/// stage 3). `false` if neither side is such a pair, or if solving fails;
/// [`unify_step`] then goes on as before, with the call unfolded (and
/// tries [`first_order`] too). The solution is the same one up to
/// unfolding, except that a call whose unfolding is a function isn't
/// eta-expanded first; the two are convertible.
fn meta_against_call(g: &Unifier<'_>, level: usize, a: &Value, b: &Value) -> Result<bool> {
    if !g.machine.glue.get()
        || !matches!(a, Value::Call(..) | Value::Neutral(Head::Meta(_), _))
        || !matches!(b, Value::Call(..) | Value::Neutral(Head::Meta(_), _))
    {
        return Ok(false);
    }
    let a = force_solved(g, a.clone())?;
    let b = force_solved(g, b.clone())?;
    let (m, spine, call) = match (&a, &b) {
        (Value::Neutral(Head::Meta(m), spine), call @ Value::Call(..))
        | (call @ Value::Call(..), Value::Neutral(Head::Meta(m), spine))
            if !frozen(g, *m) =>
        {
            (*m, spine, call)
        }
        _ => return Ok(false),
    };
    solve(g, level, m, spine, call)
}

/// Why a solution couldn't be built: there isn't one of the right shape, or
/// it ran out of resources finding out.
enum Fail {
    No,
    Out(ResourceError),
}

impl From<ResourceError> for Fail {
    fn from(e: ResourceError) -> Fail {
        Fail::Out(e)
    }
}

/// `Ok(Some(x))`, `Ok(None)` for no, or the resource error.
fn settle<T>(r: std::result::Result<T, Fail>) -> Result<Option<T>> {
    match r {
        Ok(x) => Ok(Some(x)),
        Err(Fail::No) => Ok(None),
        Err(Fail::Out(e)) => Err(e),
    }
}

/// Solves `?m spine = rhs`, where the spine must be distinct variables (a
/// "pattern"). The solution is `x1 … xn => rhs`, with the spine's variables
/// renamed to the lambda's parameters.
fn solve(g: &Unifier<'_>, level: usize, m: usize, spine: &[Elim], rhs: &Value) -> Result<bool> {
    let mut renaming = HashMap::default();
    let mut repeated = Vec::new();
    let mut icits = Vec::new();
    // An `auto` argument's unknown proof, inside a lambda that's been
    // applied to a term (`(t => c % 7) (f x)`), has that term in its spine.
    // When its statement doesn't depend on that position, a solution may
    // simply not mention it (SW-323).
    let ignorable = g.store.meta_ignorable(m);
    for elim in spine {
        match elim {
            Elim::App(arg, icit) => match force(g, arg.clone())? {
                Value::Neutral(Head::Var(l, _, _), s) if s.is_empty() => {
                    if renaming.insert(l, icits.len()).is_some() {
                        repeated.push(l);
                    }
                    icits.push(*icit);
                }
                _ if ignorable
                    .as_ref()
                    .is_some_and(|i| i.get(icits.len()) == Some(&true)) =>
                {
                    icits.push(*icit);
                }
                // The only value of its type (`()`, say): the solution
                // ignores it, so `?t () = f x` gives `?t := _ => f x`.
                Value::Ctor(d, _, fields) if fields.is_empty() && has_one_value(g, d) => {
                    icits.push(*icit);
                }
                _ if g.attempt.abstracting.get() => {
                    return solve_abstracting(g, level, m, spine, rhs);
                }
                _ => return Ok(false),
            },
            Elim::J { .. } | Elim::Proj(..) => return Ok(false),
        }
    }
    // A variable given twice (`?m x t x`: a proof's unknown, applied to every
    // variable in scope, inside a lambda applied to a variable already in
    // scope) is a solution only if the other side doesn't mention it: with
    // `?m x x = x` there are two solutions (`a b => a` and `a b => b`), so
    // neither is chosen, but with `?m x x = p`, `a b => p` is the one.
    for l in repeated {
        renaming.remove(&l);
    }
    let Some(mut solution) = settle(rename(g, m, &renaming, icits.len(), level, rhs, false))?
    else {
        return Ok(false);
    };
    for icit in icits.into_iter().rev() {
        solution = Term::Lam("x".into(), icit, Rc::new(solution), ProofMark::Unknown);
    }
    let value = eval(g, &[], &solution)?;
    g.store.solve_meta(m, value);
    Ok(true)
}

/// [`solve`] for `?m spine = rhs` where the spine is distinct variables but
/// for one argument `e`, a stuck computation ([`unify_abstracting`]): the
/// solution is `rhs` with each occurrence of `e` (as written) replaced by
/// the parameter in its place, as Lean's `kabstract` makes a motive.
/// `?j (peekIn modes 0 items)` against `Call left (rest => Done (isSome
/// LParen (peekIn modes 0 items) && piBinderAhead rest))` gives `?j := x =>
/// Call left (rest => Done (isSome LParen x && piBinderAhead rest))`.
///
/// Only where that is the one solution to take: `e` mentions no unknown,
/// and mentions a variable `v` that `?m` can't (`items`, bound inside the
/// other side). So no solution can keep any occurrence of `e`, and
/// replacing all of them is not a choice among several, as it would be for
/// an `e` that `?m` could mention (`?j (f a)` against `g (f a) (f a)` has
/// four solutions). That needs `v` to occur nowhere else in `rhs`: the
/// inner [`solve`]'s renaming refuses a solution that mentions it, so
/// nothing is solved then
/// (`examples/reject/continuation-abstracting-variable-outside.sw`). An
/// `rhs` with an unknown in it is refused too, since renaming would prune
/// that unknown's dependence on `v` (`?m e = F (?n v)` gives `?n := _ =>
/// …`, one solution of several: `?n` may use `v` through `e`). Nothing is
/// solved if `e` doesn't occur. If that finds nothing, the same is tried
/// with both sides' accessor calls written as projections
/// ([`accessors_as_projections`]), so a needle and a goal that spell a field
/// differently meet; the solution is then spelled with projections, and the
/// refusals above apply to the rewritten goal, which is convertible to the
/// original, so a variable or unknown found only in an argument the rewrite
/// drops doesn't count. Unlike [`solve`], the spine's other
/// arguments must be distinct variables: `()` and ignorable positions
/// aren't handled. The solution is checked by comparing `?m spine` with
/// `rhs` again.
fn solve_abstracting(
    g: &Unifier<'_>,
    level: usize,
    m: usize,
    spine: &[Elim],
    rhs: &Value,
) -> Result<bool> {
    let _once = ScopedCell::set(&g.attempt.abstracting, false);
    let mut seen = HashSet::default();
    let mut needle = None;
    for (at, elim) in spine.iter().enumerate() {
        let Elim::App(arg, icit) = elim else {
            return Ok(false);
        };
        match force_solved(g, arg.clone())? {
            Value::Neutral(Head::Var(l, _, _), s) if s.is_empty() => {
                if !seen.insert(l) {
                    return Ok(false);
                }
            }
            e @ (Value::Neutral(Head::Var(..) | Head::Def(_), _) | Value::Call(..))
                if needle.is_none() =>
            {
                if !matches!(
                    force(g, e.clone())?,
                    Value::Neutral(Head::Var(..) | Head::Def(_), _)
                ) {
                    return Ok(false);
                }
                needle = Some((at, *icit, e));
            }
            _ => return Ok(false),
        }
    }
    let Some((at, icit, e)) = needle else {
        return Ok(false);
    };
    // As written first, so a goal that matches keeps its solution as it is;
    // with accessors as projections only where that found nothing.
    for normalise in [false, true] {
        if abstract_once(g, level, m, spine, rhs, (at, icit, &e), &seen, normalise)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// One attempt of [`solve_abstracting`], for the spine's stuck argument
/// `(at, icit, e)` and its variables `seen`; `normalise` writes accessor
/// calls as projections on both sides first.
#[allow(clippy::too_many_arguments)]
fn abstract_once(
    g: &Unifier<'_>,
    level: usize,
    m: usize,
    spine: &[Elim],
    rhs: &Value,
    (at, icit, e): (usize, Icit, &Value),
    seen: &HashSet<usize>,
    normalise: bool,
) -> Result<bool> {
    let written = |t: Term| {
        if normalise {
            accessors_as_projections(g, &t)
        } else {
            Ok(t)
        }
    };
    let needle = written(quote_as_written(g, level, e)?)?;
    if needle.subterms().any(|(t, _)| matches!(t, Term::Meta(_)))
        || crate::matching::free_levels(&needle, level)
            .iter()
            .all(|l| seen.contains(l))
    {
        return Ok(false);
    }
    let hay = written(quote_as_written(g, level, rhs)?)?;
    if hay.subterms().any(|(t, _)| matches!(t, Term::Meta(_)))
        || !hay
            .subterms()
            .any(|(t, under)| crate::matching::same_shifted(&needle, t, under, 0))
    {
        return Ok(false);
    }
    let Ok(abstracted) = crate::check::abstract_needle(g, &hay, level, &needle, 1, &Term::Var(0))
    else {
        return Ok(false);
    };
    let env: Vec<Value> = (0..=level).map(Value::var).collect();
    let body = eval(g, &env, &abstracted)?;
    let mut opened = spine.to_vec();
    opened[at] = Elim::App(Value::var(level), icit);
    let trail = g.store.meta_trail.borrow().len();
    if solve(g, level + 1, m, &opened, &body)?
        && unify(
            g,
            level,
            &Value::Neutral(Head::Meta(m), spine.iter().cloned().collect()),
            rhs,
        )?
    {
        return Ok(true);
    }
    undo_since(g, trail);
    Ok(false)
}

/// `term` with each saturated call of a field-accessor-shaped definition
/// (`Mark.left {t} v`: a function whose body is a `case` on its last
/// parameter, with one branch returning a field) written as the primitive
/// projection it computes to (`v.2`), so that [`solve_abstracting`] finds a
/// needle written one way in a goal that holds the other: a goal stated with
/// accessors, after `Parse.runFrom` has run, reads the state's fields as
/// projections. The test is structural, so a hand-written definition of that
/// shape counts too. Only record types with eta, as the kernel only takes a
/// projection of those; the arguments before the record are dropped because
/// the body can't name them, whatever they are. Opaque definitions and ones
/// with a native are left alone: they aren't convertible to the projection.
fn accessors_as_projections(g: &Ev, term: &Term) -> Result<Term> {
    term.rewrite_up(g, &mut |t| {
        let (Term::Def(d), args) = t.spine() else {
            return Ok(None);
        };
        // An opaque definition never unfolds, and one with a native isn't
        // taken apart by record eta: neither is convertible to the projection.
        if g.def(*d).opaque() || stitchwort_core::value::eta_held(g, *d) {
            return Ok(None);
        }
        let Some(body) = g.def(*d).body() else {
            return Ok(None);
        };
        if body.count_lams() != args.len() || args.is_empty() {
            return Ok(None);
        }
        let Term::Case(0, data, branches) = body.peel_lams(args.len()).strip_loc() else {
            return Ok(None);
        };
        let [branch] = &**branches else {
            return Ok(None);
        };
        let Some(Term::Var(field)) = branch.body.as_ref().map(|b| b.strip_loc()) else {
            return Ok(None);
        };
        if !g.data(*data).eta() || *field >= branch.names.len() {
            return Ok(None);
        }
        let record = (*args[args.len() - 1]).clone();
        Ok(Some(Term::Proj(
            *data,
            branch.names.len() - 1 - field,
            Rc::new(record),
        )))
    })
}

/// [`unify_solving_arguments`], except that an unknown applied to variables
/// and one stuck computation `e`, as `?j e`, is solved by abstracting `e`
/// from the other side ([`solve_abstracting`]). For a caller whose other
/// comparisons have all failed: `Parse.followsThen`'s continuation `?j`,
/// once its first parser `?p` is known, meets `?j (?p ())` inside the
/// goal's parser, `?p ()` unfolded to a computation stuck on what the
/// parser read, where no pattern can solve it.
pub(crate) fn unify_abstracting(
    g: &Unifier<'_>,
    level: usize,
    a: &Value,
    b: &Value,
) -> Result<bool> {
    let _abstracting = ScopedCell::set(&g.attempt.abstracting, true);
    let _solving = ScopedCell::set(&g.attempt.solving_arguments, true);
    let _memo = Scoped::set(&g.attempt.call_memo, None);
    unify(g, level, a, b)
}

/// Whether data type `d` has exactly one value: one constructor, without
/// fields or indices (`()`).
fn has_one_value(g: &Ev, d: stitchwort_core::DataId) -> bool {
    let data = g.data(d);
    data.indices().is_empty() && data.ctors().len() == 1 && data.ctors()[0].fields.is_empty()
}

type Renamed<T> = std::result::Result<T, Fail>;

/// Quotes `value` (in a context of `cod` variables) into a term in a context of
/// `dom` variables, following `renaming`. Fails if `value` mentions `m` itself
/// (no circular solutions) or a variable the renaming doesn't cover.
///
/// A glued call is written as the call (docs/proposals/folded-calls.md,
/// stage 3), so a solution says `invalid r`, not what that computes to. If
/// its arguments can't be written (they mention `m` or a variable out of
/// scope, which its unfolding may not), its unfolding is written instead,
/// as without gluing. Inside a call's arguments (`in_call`), nothing is
/// pruned: the call may not need the argument, so pruning there would
/// solve a metavariable the unfolded solution leaves alone; stage 3
/// changes how solutions are written, not what is solved (as decided after
/// stage 2 for matching calls by their arguments). Such an argument fails
/// instead, and the unfolding is written.
///
/// The term written is a tree, while the value may share its parts (`grow n
/// (Node t t)`), so it can be exponentially larger: like [`quote`], it may
/// have at most the budget's size limit of nodes, or fails with
/// [`ResourceError::Size`] (SW-2409).
fn rename(
    g: &Unifier<'_>,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    value: &Value,
    in_call: bool,
) -> Renamed<Term> {
    let read = |at_once_as_written: bool| {
        let size = Sized {
            nodes: std::cell::Cell::new(0),
            limit: g.machine.budget.size_limit(),
            root_def: match value {
                Value::Neutral(Head::Def(id), _) | Value::Call(id, ..) => Some(id.0),
                _ => None,
            },
            at_once_as_written,
        };
        let renamed = rename_in(g, &size, m, renaming, dom, cod, value, in_call);
        g.machine.budget.note_readback(size.nodes.get());
        renamed
    };
    let budget = &g.machine.budget;
    let ran_out_in = budget.take_ran_out_in();
    budget.set_ran_out_in(ran_out_in);
    match read(false) {
        // A hypothesis's call that steps at once and computes to a huge
        // value (`q (grow 22 (Leaf x))`) would make the solution too large
        // to write: written as the call it is convertible, and small
        // (SW-4237).
        Err(Fail::Out(e @ ResourceError::Size(_))) if budget.exhausted().is_none() => {
            let noted = budget.take_too_large();
            let noted_in = budget.take_ran_out_in();
            match read(true) {
                Err(Fail::Out(ResourceError::Size(_))) if budget.exhausted().is_none() => {
                    budget.set_too_large(noted);
                    budget.set_ran_out_in(noted_in);
                    Err(Fail::Out(e))
                }
                Ok(term) => {
                    budget.set_too_large(noted);
                    budget.set_ran_out_in(ran_out_in);
                    Ok(term)
                }
                other => other,
            }
        }
        other => other,
    }
}

/// How many nodes [`rename`] has written, of how many it may.
struct Sized {
    nodes: std::cell::Cell<u64>,
    limit: u64,
    /// The definition whose call the whole value was, for the report.
    root_def: Option<usize>,
    /// Write a call that steps at once as the call too, as [`rename`]'s
    /// second try does when the first was too large.
    at_once_as_written: bool,
}

// `rename_in` recurses once per level of the value, and a value can be
// hundreds of levels deep (a list of 100 numbers computed out, in a goal a
// `match` is generalised over), so its own frame is kept small: it handles
// the forms a deep value is made of (calls, data, constructors and
// applied variables and definitions) and leaves the rest to
// `rename_other`, never inlined. In the playground the whole check must fit
// a stack of 320 KiB (`crates/web/build.rs`).
#[allow(clippy::too_many_arguments)]
fn rename_in(
    g: &Unifier<'_>,
    size: &Sized,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    value: &Value,
    in_call: bool,
) -> Renamed<Term> {
    g.machine.budget.step()?;
    let nodes = size.nodes.get() + 1;
    size.nodes.set(nodes);
    if nodes > size.limit {
        return Err(too_large(g, size));
    }
    let go = |v: &Value| rename_in(g, size, m, renaming, dom, cod, v, in_call);
    let value = match force_solved(g, value.clone())? {
        Value::Call(id, spine, unfolding)
            if size.at_once_as_written || !matches_at_once(g, id, &spine)? =>
        {
            match rename_call(g, size, m, renaming, dom, cod, id, &spine)? {
                Some(term) => return Ok(term),
                None => force(g, Value::Call(id, spine, unfolding))?,
            }
        }
        other => force(g, other)?,
    };
    let all = |args: &[Value]| -> Renamed<Vec<Rc<Term>>> {
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            out.push(Rc::new(go(a)?));
        }
        Ok(out)
    };
    Ok(match value {
        Value::Data(d, args) => Term::Data(d, all(&args)?),
        Value::Ctor(d, c, args) => Term::Ctor(d, c, all(&args)?),
        Value::Neutral(Head::Def(id), spine) => rename_spine(&go, Term::Def(id), &spine)?,
        Value::Neutral(Head::Var(l, _, _), spine) => {
            let new = *renaming.get(&l).ok_or(Fail::No)?;
            rename_spine(&go, Term::Var(dom - 1 - new), &spine)?
        }
        other => rename_other(g, size, m, renaming, dom, cod, other, in_call)?,
    })
}

/// The error for a value [`rename`] would write more than `size`'s limit of
/// nodes for.
#[cold]
#[inline(never)]
fn too_large(g: &Unifier<'_>, size: &Sized) -> Fail {
    g.machine.budget.set_too_large(size.root_def);
    g.machine.budget.note_ran_out();
    Fail::Out(ResourceError::Size(size.limit))
}

/// The call of `id` to `spine` as written, for [`rename_in`]: `None` if an
/// argument can't be ([`Fail::No`]), so that its unfolding is written instead.
#[allow(clippy::too_many_arguments)]
fn rename_call(
    g: &Unifier<'_>,
    size: &Sized,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    id: stitchwort_core::DefId,
    spine: &[Elim],
) -> Renamed<Option<Term>> {
    let mut term = Term::Def(id);
    for elim in spine {
        let (arg, icit) = match elim {
            Elim::App(arg, icit) => (arg, *icit),
            // A field of a call ([`stitchwort_core::value::project_call`]).
            Elim::Proj(d, i) => {
                term = Term::Proj(*d, *i, Rc::new(term));
                continue;
            }
            Elim::J { .. } => unreachable!("a call's spine has no `J`"),
        };
        match rename_in(g, size, m, renaming, dom, cod, arg, true) {
            Ok(arg) => term = Term::app_icit(term, arg, icit),
            Err(Fail::Out(e)) => return Err(Fail::Out(e)),
            Err(Fail::No) => return Ok(None),
        }
    }
    Ok(Some(term))
}

/// [`rename_in`] of a forced value of the forms it doesn't write itself.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn rename_other(
    g: &Unifier<'_>,
    size: &Sized,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    value: Value,
    in_call: bool,
) -> Renamed<Term> {
    let go = |v: &Value| rename_in(g, size, m, renaming, dom, cod, v, in_call);
    let under = |closure: &Closure| rename_under(g, size, m, renaming, dom, cod, closure, in_call);
    Ok(match value {
        Value::Sort(s) => Term::Sort(s),
        Value::Refl => Term::Refl,
        Value::Pi(x, i, a, b, _) => Term::Pi(
            x,
            i,
            Rc::new(go(&a)?),
            Rc::new(under(&b)?),
            ProofMark::Unknown,
        ),
        Value::Lam(x, i, b, _) => Term::Lam(x, i, Rc::new(under(&b)?), ProofMark::Unknown),
        Value::Nat(n) => Term::Nat(n),
        // Closed: nothing to rename, and no metavariable to occur.
        Value::Chars(c) => quote_internal(g, cod, &Value::Chars(c))?,
        Value::NatAdd(k, base) => native::nat_add_term(g, &k, go(&base)?),
        Value::Eq(t, a, b) => Term::Eq(Some(Rc::new(go(&t)?)), Rc::new(go(&a)?), Rc::new(go(&b)?)),
        Value::Neutral(Head::Meta(m2), spine) if m2 != m => {
            rename_meta(g, size, m, renaming, dom, cod, (m2, &spine), in_call)?
        }
        Value::Neutral(Head::Meta(_), _) => return Err(Fail::No),
        Value::Neutral(Head::Quot(form, _), spine) => {
            rename_quot(g, size, m, renaming, dom, cod, (form, &spine), in_call)?
        }
        Value::Data(..) | Value::Ctor(..) | Value::Neutral(..) => {
            unreachable!("written by `rename_in`")
        }
        // Handled above: the call, or else `force` gave its unfolding.
        Value::Call(..) => unreachable!("a forced value is never a call"),
        Value::Resumption(_) => unreachable!("a handler's resumption never reaches the checker"),
    })
}

/// [`rename_other`] of the body of a binder: its variable, `cod`, is
/// written as `dom`. Out of line, like the other arms with bodies of their
/// own, so that `rename_other`'s frame, on every level of a value under
/// binders, holds only what it passes on.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn rename_under(
    g: &Unifier<'_>,
    size: &Sized,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    closure: &Closure,
    in_call: bool,
) -> Renamed<Term> {
    let mut renaming = renaming.clone();
    renaming.insert(cod, dom);
    let body = closure.apply(g, Value::var(cod))?;
    rename_in(g, size, m, &renaming, dom + 1, cod + 1, &body, in_call)
}

/// [`rename_other`] of another unknown `m2` applied to `spine`, pruned of
/// variables the renaming doesn't cover if it can be.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn rename_meta(
    g: &Unifier<'_>,
    size: &Sized,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    (m2, spine): (usize, &[Elim]),
    in_call: bool,
) -> Renamed<Term> {
    let go = |v: &Value| rename_in(g, size, m, renaming, dom, cod, v, in_call);
    if !in_call && let Some((m3, kept)) = prune(g, m2, spine, renaming)? {
        let mut term = Term::Meta(m3);
        for elim in kept {
            let Elim::App(v, i) = elim else {
                unreachable!("pruned spines only contain applications")
            };
            term = Term::app_icit(term, go(&v)?, i);
        }
        return Ok(term);
    }
    rename_spine(&go, Term::Meta(m2), spine)
}

/// [`rename_other`] of a quotient form applied to `spine`: the form's own
/// arguments, then what applies its result.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn rename_quot(
    g: &Unifier<'_>,
    size: &Sized,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    (form, spine): (stitchwort_core::QuotForm, &[Elim]),
    in_call: bool,
) -> Renamed<Term> {
    let go = |v: &Value| rename_in(g, size, m, renaming, dom, cod, v, in_call);
    let n = spine
        .iter()
        .take(form.arity())
        .take_while(|e| matches!(e, Elim::App(..)))
        .count();
    let args = spine[..n]
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => go(v).map(Rc::new),
            Elim::J { .. } | Elim::Proj(..) => {
                unreachable!("counted applications")
            }
        })
        .collect::<Renamed<_>>()?;
    rename_spine(
        &go,
        Term::Quot(form, args, false, ProofMark::Unknown),
        &spine[n..],
    )
}

/// `head` applied to `spine`, each part renamed by `go` ([`rename`]).
fn rename_spine(go: &dyn Fn(&Value) -> Renamed<Term>, head: Term, spine: &[Elim]) -> Renamed<Term> {
    let mut term = head;
    for elim in spine {
        term = match elim {
            Elim::App(v, i) => Term::app_icit(term, go(v)?, *i),
            Elim::J {
                motive, base, ends, ..
            } => {
                // A cast keeps its ends on its proof, as the kernel puts
                // them there, so its solution still computes by rule K.
                let proof = match ends {
                    None => term,
                    Some(e) => Term::Ann(
                        Rc::new(term),
                        Rc::new(Term::Eq(
                            Some(Rc::new(go(&e.ty)?)),
                            Rc::new(go(&e.x)?),
                            Rc::new(go(&e.y)?),
                        )),
                    ),
                };
                Term::J(
                    Rc::new(go(motive)?),
                    Rc::new(go(base)?),
                    Rc::new(proof),
                    ProofMark::Unknown,
                )
            }
            Elim::Proj(d, i) => Term::Proj(*d, *i, Rc::new(term)),
        };
    }
    Ok(term)
}

/// `value`, with `level` variables in scope, as a term over only the first
/// `keep` of them, or `None` if it mentions a later one. An unknown applied
/// to a later variable is pruned, so that its solution can't mention it.
pub(crate) fn strengthen(
    g: &Unifier<'_>,
    level: usize,
    keep: usize,
    value: &Value,
) -> Result<Option<Term>> {
    let renaming: HashMap<usize, usize> = (0..keep).map(|l| (l, l)).collect();
    settle(rename(g, usize::MAX, &renaming, keep, level, value, false))
}

/// Prunes variable `level` from `value`'s spine, when `value` is an unknown
/// applied to distinct variables (`?m e g xs k`): `?m` is solved as a new
/// unknown applied to the others, so its solution can't mention `level`.
/// Anything else is left alone.
pub(crate) fn prune_variable(g: &Unifier<'_>, value: &Value, level: usize) -> Result<()> {
    let Value::Neutral(Head::Meta(m), spine) = force(g, value.clone())? else {
        return Ok(());
    };
    let mut renaming = HashMap::default();
    for elim in &spine {
        if let Elim::App(v, _) = elim
            && let Value::Neutral(Head::Var(l, _, _), s) = force(g, v.clone())?
            && s.is_empty()
            && l != level
        {
            renaming.insert(l, l);
        }
    }
    prune(g, m, &spine, &renaming)?;
    Ok(())
}

/// Pruning: `?m2 spine` appears in a solution, but some of its arguments are
/// variables the solution can't mention. If the spine is distinct variables,
/// `?m2` can't depend on those positions in any solution, so solve it as a new
/// metavariable applied to only the remaining arguments. Returns the new
/// metavariable and the arguments it keeps.
fn prune(
    g: &Unifier<'_>,
    m2: usize,
    spine: &[Elim],
    renaming: &HashMap<usize, usize>,
) -> Result<Option<(usize, Vec<Elim>)>> {
    if frozen(g, m2) {
        return Ok(None); // pruning would solve it
    }
    let mut levels = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(v, _) => match force(g, v.clone())? {
                Value::Neutral(Head::Var(l, _, _), s) if s.is_empty() && !levels.contains(&l) => {
                    levels.push(l);
                }
                _ => return Ok(None),
            },
            Elim::J { .. } | Elim::Proj(..) => return Ok(None),
        }
    }
    if levels.iter().all(|l| renaming.contains_key(l)) {
        return Ok(None);
    }
    let span = g.store.metas.borrow()[m2].span;
    let m3 = g.store.new_meta(span);
    let n = spine.len();
    let mut body = Term::Meta(m3);
    let mut kept = Vec::new();
    for (i, (elim, level)) in spine.iter().zip(&levels).enumerate() {
        if renaming.contains_key(level) {
            let Elim::App(_, icit) = elim else {
                unreachable!()
            };
            body = Term::app_icit(body, Term::Var(n - 1 - i), *icit);
            kept.push(elim.clone());
        }
    }
    for elim in spine.iter().rev() {
        let Elim::App(_, icit) = elim else {
            unreachable!()
        };
        body = Term::Lam("x".into(), *icit, Rc::new(body), ProofMark::Unknown);
    }
    g.store.solve_meta(m2, eval(g, &[], &body)?);
    Ok(Some((m3, kept)))
}

/// Why zonking failed.
#[derive(Debug, PartialEq, Eq)]
pub enum ZonkError {
    /// This metavariable is unsolved.
    Unsolved(usize),
    Resource(ResourceError),
}

impl From<ResourceError> for ZonkError {
    fn from(e: ResourceError) -> ZonkError {
        ZonkError::Resource(e)
    }
}

/// [`zonk_in`], keeping none, outside any `let`.
#[cfg(test)]
pub fn zonk(g: &Unifier<'_>, level: usize, term: &Term) -> std::result::Result<Term, ZonkError> {
    zonk_in(g, level, term, &|_| false, &[])
}

/// `term` (with `level` variables in scope, inside `lets`) with each
/// occurrence of a `let`'s value folded back to its variable.
pub(crate) fn refold(
    g: &Ev,
    term: Term,
    level: usize,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    let mut term = term;
    for (slot, scope, normal) in lets {
        // A normal form that mentions variables not in scope can't occur.
        let Some(by) = level.checked_sub(*scope) else {
            continue;
        };
        // The value, moved under `under` more binders, is compared without
        // making the moved copy.
        let hook = |t: &Term, under: usize| {
            crate::matching::same_shifted(normal, t, by + under, 0)
                .then(|| Term::Var(level + under - 1 - slot))
        };
        match fold_back(g, &term, 0, &hook) {
            Ok(Some(t)) => term = t,
            Ok(None) => {}
            Err(_) => {
                return Err(ZonkError::Resource(ResourceError::Nesting(
                    crate::check::PASS,
                )));
            }
        }
    }
    Ok(term)
}

/// [`refold`]'s pass: `term` (under `under` binders of the pass) with each
/// sub-term `hook` replaces replaced, outermost first, or `None` if it
/// replaces none. What's unchanged is shared, not rebuilt: most passes
/// find nothing to fold, and rebuilding (and then dropping) a large normal
/// form once per `let` in scope was most of the cost of lifting.
pub(crate) fn fold_back(
    g: &Ev,
    term: &Term,
    under: usize,
    hook: &dyn Fn(&Term, usize) -> Option<Term>,
) -> Result<Option<Term>> {
    g.machine.budget.nesting(crate::check::PASS)?;
    if let Some(t) = hook(term, under) {
        return Ok(Some(t));
    }
    // A child, folded; `None` if unchanged.
    let go = |t: &Rc<Term>, under| fold_back(g, t, under, hook).map(|t| t.map(Rc::new));
    // The children, if any changed.
    let all = |ts: &[Rc<Term>], under| -> Result<Option<Vec<Rc<Term>>>> {
        let mut out: Option<Vec<Rc<Term>>> = None;
        for (i, t) in ts.iter().enumerate() {
            if let Some(new) = go(t, under)? {
                out.get_or_insert_with(|| ts[..i].to_vec()).push(new);
            } else if let Some(out) = &mut out {
                out.push(t.clone());
            }
        }
        Ok(out)
    };
    let or = |new: Option<Rc<Term>>, old: &Rc<Term>| new.unwrap_or_else(|| old.clone());
    Ok(match term {
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => None,
        Term::Data(d, args) => all(args, under)?.map(|args| Term::Data(*d, args)),
        Term::Ctor(d, c, args) => all(args, under)?.map(|args| Term::Ctor(*d, *c, args)),
        Term::Pi(x, i, a, b, _) => match (go(a, under)?, go(b, under + 1)?) {
            (None, None) => None,
            (a2, b2) => Some(Term::Pi(
                x.clone(),
                *i,
                or(a2, a),
                or(b2, b),
                ProofMark::Unknown,
            )),
        },
        Term::Lam(x, i, b, _) => {
            go(b, under + 1)?.map(|b| Term::Lam(x.clone(), *i, b, ProofMark::Unknown))
        }
        Term::App(h, a, i) => match (go(h, under)?, go(a, under)?) {
            (None, None) => None,
            (h2, a2) => Some(Term::App(or(h2, h), or(a2, a), *i)),
        },
        Term::Ann(e, t) => match (go(e, under)?, go(t, under)?) {
            (None, None) => None,
            (e2, t2) => Some(Term::Ann(or(e2, e), or(t2, t))),
        },
        Term::Let(x, a, v, b, e, _) => match (go(a, under)?, go(v, under)?, go(b, under + 1)?) {
            (None, None, None) => None,
            (a2, v2, b2) => Some(Term::Let(
                x.clone(),
                or(a2, a),
                or(v2, v),
                or(b2, b),
                *e,
                ProofMark::Unknown,
            )),
        },
        Term::Case(ix, d, branches) => {
            let mut new: Vec<Option<Rc<Term>>> = Vec::with_capacity(branches.len());
            for b in branches.iter() {
                new.push(match &b.body {
                    Some(body) => go(body, under + b.names.len())?,
                    None => None,
                });
            }
            if new.iter().all(Option::is_none) {
                None
            } else {
                Some(Term::Case(
                    *ix,
                    *d,
                    branches
                        .iter()
                        .zip(new)
                        .map(|(b, n)| stitchwort_core::term::Branch {
                            names: b.names.clone(),
                            body: b.body.as_ref().map(|old| or(n, old)),
                        })
                        .collect(),
                ))
            }
        }
        Term::NumCase(ix, arms, default) => {
            let mut new: Vec<Option<Rc<Term>>> = Vec::with_capacity(arms.len());
            for a in arms.iter() {
                new.push(go(&a.body, under)?);
            }
            let default2 = go(default, under)?;
            if new.iter().all(Option::is_none) && default2.is_none() {
                None
            } else {
                Some(Term::NumCase(
                    *ix,
                    arms.iter()
                        .zip(new)
                        .map(|(a, n)| stitchwort_core::term::NumArm {
                            value: a.value.clone(),
                            body: or(n, &a.body),
                        })
                        .collect(),
                    or(default2, default),
                ))
            }
        }
        Term::Eq(t, a, b) => {
            let t2 = match t {
                Some(t) => go(t, under)?,
                None => None,
            };
            match (t2, go(a, under)?, go(b, under)?) {
                (None, None, None) => None,
                (t2, a2, b2) => Some(Term::Eq(
                    t.as_ref().map(|t| or(t2, t)),
                    or(a2, a),
                    or(b2, b),
                )),
            }
        }
        Term::J(m, b, p, _) => match (go(m, under)?, go(b, under)?, go(p, under)?) {
            (None, None, None) => None,
            (m2, b2, p2) => Some(Term::J(or(m2, m), or(b2, b), or(p2, p), ProofMark::Unknown)),
        },
        Term::Proj(d, i, t) => go(t, under)?.map(|t| Term::Proj(*d, *i, t)),
        Term::Quot(form, args, e, _) => {
            all(args, under)?.map(|args| Term::Quot(*form, args, *e, ProofMark::Unknown))
        }
        Term::Loc(span, t) => go(t, under)?.map(|t| Term::Loc(*span, t)),
    })
}

/// `f`'s result, if it's cheap to compute: a `let`'s value's normal form,
/// for [`refold`], which is only an optimisation. A value too large to
/// compute and compare quickly (a long list, say) isn't folded back; that's
/// also where folding would cost more than it saves. Whether it folds shows
/// in the elaborated term, so it is an attempt ([`Budget::attempt`]): its
/// limits are ones that are the same in every build, and its `stack` only
/// applies outside an operation (SW-962).
///
/// [`Budget::attempt`]: stitchwort_core::budget::Budget::attempt
pub(crate) fn cheaply<T>(g: &Ev, f: impl FnOnce() -> Result<T>) -> Option<T> {
    let _op = g.machine.budget.attempt(cheap_limits());
    f().ok()
}

/// [`cheaply`]'s limits: the same in every build, `stack` included (SW-962).
fn cheap_limits() -> stitchwort_core::Limits {
    stitchwort_core::Limits {
        work: 100_000,
        stack: 128 * 1024,
        size: 10_000,
        frames: 10_000,
        native_frames: 10_000,
    }
}

/// Whether a `let`'s value, as a normal form, is worth folding back, and
/// safe to: an alias of a variable, or a constant, costs nothing to compute
/// again, and a form whose type it doesn't fix can't be folded back
/// ([`type_fixed`]).
pub(crate) fn worth_folding(g: &Ev, normal: &Term) -> bool {
    !matches!(normal.strip_loc(), Term::Var(_) | Term::Nat(_)) && type_fixed(g, normal)
}

/// Whether every type `term` has, in its context, is the same up to
/// conversion. Folding an occurrence back to a `let`'s variable gives it
/// the variable's type, so a form that also has other types mustn't be
/// folded: with `let e: 2 = 2 := byComputing` in scope, the `Refl` witness
/// of a `Float` literal in a solution would become `e`, a proof of `2 = 2`
/// (SW-3887), and `let xs: List Nat := []` would take `[]: List Bool`. Not
/// fixed: `Refl`, a lambda (its parameter's type isn't written), a
/// constructor of a type with parameters its fields don't fix (`[]`,
/// `None`, `Left 1`), and the forms with no motive written (`match`, `J`).
/// Conservative: a form it can't tell about isn't fixed.
pub(crate) fn type_fixed(g: &Ev, term: &Term) -> bool {
    match term.strip_loc() {
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Data(..)
        | Term::Eq(..) => true,
        Term::Pi(_, _, a, b, _) => type_fixed(g, a) && type_fixed(g, b),
        Term::Ann(..) => true,
        Term::Let(_, _, _, body, _, _) => type_fixed(g, body),
        Term::Proj(_, _, record) => type_fixed(g, record),
        // A function's result type is its codomain at the arguments, which
        // the term writes, implicit ones included.
        Term::App(..) => match term.spine().0.strip_loc() {
            Term::Var(_) | Term::Def(_) => true,
            Term::Proj(_, _, record) => type_fixed(g, record),
            _ => false,
        },
        Term::Ctor(d, c, fields) => ctor_type_fixed(g, *d, *c, fields),
        Term::Refl
        | Term::Lam(..)
        | Term::Case(..)
        | Term::NumCase(..)
        | Term::J(..)
        | Term::Quot(..)
        | Term::Meta(_) => false,
        Term::Loc(..) => unreachable!("stripped"),
    }
}

/// [`type_fixed`] of constructor `c` of `d` applied to `fields`: its type
/// is `d` at its parameters (the indices follow from them and the fields),
/// and the term doesn't write the parameters, so each must be fixed by a
/// field whose own type is fixed and mentions it where conversion can't
/// lose it (`A` in `head: A` or `tail: List A`).
fn ctor_type_fixed(g: &Ev, d: stitchwort_core::DataId, c: usize, fields: &[Rc<Term>]) -> bool {
    let data = g.data(d);
    let np = data.params().len();
    if np == 0 {
        return true;
    }
    let Some(ctor) = data.ctors().get(c) else {
        return false;
    };
    let mut fixed = vec![false; np];
    for (i, ((_, ty), value)) in ctor.fields.iter().zip(fields).enumerate() {
        if !fixed.iter().all(|f| *f) && type_fixed(g, value) {
            // Field `i`'s type is in the context of the parameters and the
            // `i` fields before it: parameter `k` is `Var(np + i - 1 - k)`.
            for (k, f) in fixed.iter_mut().enumerate() {
                *f = *f || rigidly_mentions(ty, np + i - 1 - k);
            }
        }
    }
    fixed.into_iter().all(|f| f)
}

/// Whether type `ty` mentions variable `ix` where conversion keeps it: as
/// the type itself, or inside a data type's arguments or a function
/// type's parts, which conversion compares part by part.
fn rigidly_mentions(ty: &Term, ix: usize) -> bool {
    match ty.strip_loc() {
        Term::Var(i) => *i == ix,
        Term::Data(_, args) => args.iter().any(|a| rigidly_mentions(a, ix)),
        Term::Pi(_, _, a, b, _) => rigidly_mentions(a, ix) || rigidly_mentions(b, ix + 1),
        _ => false,
    }
}

/// A `let` that `term` is inside, in [`zonk_in`]: its level, how many
/// variables its value's normal form is in, and that normal form. That's
/// the context before the `let`, unless a case split has replaced a
/// variable its value uses by a constructor whose fields are bound after
/// the `let`: then it's a context that has those fields too. A `let` may
/// appear more than once, with its value read back in each form
/// ([`value_forms`]), since a solution may hold either.
pub(crate) type Around = (usize, usize, Rc<Term>);

/// `value` read back as written, folded and unfolded, each once: the forms
/// of a `let`'s value that [`refold`] looks for. A solution is written as
/// written ([`zonk_in`]) but falls back to the unfolding where a call can't
/// be written; one solved from a value read back folded holds that form;
/// and a decision's solution is found on the unfolded goal (D484). The
/// as-written form costs no computing, so it comes first; the other two
/// each run within [`cheap_limits`] of their own, and one that doesn't fit
/// is left out, so a value too large to unfold still folds back as written.
pub(crate) fn value_forms(g: &Ev, level: usize, value: &Value) -> Result<Vec<Term>> {
    if !g.machine.glue.get() {
        // No calls: the forms are the same.
        return Ok(vec![quote_internal(g, level, value)?]);
    }
    let mut forms = vec![quote_as_written(g, level, value)?];
    for folded in [true, false] {
        let read = || match folded {
            // Within `cheap_limits`: a form too large to read is left out, so
            // the fallback to the call as written is the `quote_as_written` above.
            #[allow(clippy::disallowed_methods)]
            true => quote_folded(g, level, value),
            false => quote_internal(g, level, value),
        };
        let form = (g.machine.budget).aside(cheap_limits(), read);
        // Cancelled, or out of the operation's own stack: passed on.
        if let Some(e) = g.machine.budget.exhausted() {
            return Err(e);
        }
        let Ok(form) = form else { continue };
        if !(forms.iter()).any(|f| stitchwort_core::value::same_term(f, &form)) {
            forms.push(form);
        }
    }
    Ok(forms)
}

/// Replaces solved metavariables in `term` (with `level` variables in scope,
/// inside the `let`s `lets`) by their solutions. Fails on an unsolved
/// metavariable, except those `keep` allows, which are left in place.
///
/// A metavariable's solution never mentions a `let`'s variable: it was
/// solved where the variable's value is its value (docs/proposals/let.md
/// §6.1 rule 2). So a solution that a program runs, such as a decision
/// procedure found for `if m < 3` after `let m := n + 1`, would compute the
/// value again (`n + 1 < 3`). Where the solution is put back inside the
/// `let`, occurrences of the value's normal form are folded back to the
/// variable, outermost `let` first (so a later one's value, which mentions
/// an earlier one, is recognised). That's the same term to the checker, and
/// the program shares the value; only a form whose type it fixes is folded
/// ([`worth_folding`]), since the variable has only the `let`'s type.
pub(crate) fn zonk_in(
    g: &Unifier<'_>,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    Ok(zonk_changed(g, level, term, keep, lets, 0, None)?.unwrap_or_else(|| term.clone()))
}

/// How deep [`zonk_changed`] recurses before it finds out, in one loop over
/// the rest of the term ([`Changing`]), which parts it would change, and
/// from then on recurses only into those. Shallow terms, nearly all of them,
/// never pay for the look.
const LOOK_AHEAD_DEPTH: usize = 32;

/// The nodes of a term that zonking may change, by address: each that is a
/// metavariable or an application [`empty_row_done`] takes apart, or has
/// one below it. Zonking computes nothing elsewhere, so any other node is
/// its own result. Found by a loop, where zonking recurses on the stack: a
/// deep normal form with its unknowns near the top (2024 day 22's
/// `Nat.iterate 2000 nextSecret x`, about 2,000 deep, read back to see what
/// an application's type still mentions) is zonked without going down it.
struct Changing(stitchwort_core::collections::HashSet<*const Term>);

impl Changing {
    fn of(g: &Ev, term: &Term) -> Changing {
        let mut changing = stitchwort_core::collections::HashSet::default();
        // Each node twice: on the way down, then once its children are done.
        let mut pending = vec![(term, false)];
        while let Some((t, children_done)) = pending.pop() {
            if children_done {
                let mut changes = matches!(t, Term::Meta(_)) || empty_row_done(g, t).is_some();
                t.for_each_child(|c, _| changes |= changing.contains(&(c as *const Term)));
                if changes {
                    changing.insert(t as *const Term);
                }
            } else {
                pending.push((t, true));
                t.for_each_child(|c, _| pending.push((c, false)));
            }
        }
        Changing(changing)
    }

    fn changes(&self, term: &Term) -> bool {
        self.0.contains(&(term as *const Term))
    }
}

/// The budget for unfolding a solution to lose an unknown its calls'
/// arguments mention ([`zonk_in`]): the same in every build, `stack`
/// included, as [`cheaply`]'s (SW-962).
fn unfolding_limits() -> stitchwort_core::Limits {
    stitchwort_core::Limits {
        work: 100_000,
        stack: 128 * 1024,
        size: 20_000,
        frames: 10_000,
        native_frames: 10_000,
    }
}

/// Whether `term` is a metavariable, or one applied to arguments. Not the
/// erased placeholder's read-back (`ELIDED`), which is no index into the
/// store and has no solution to substitute.
fn meta_headed(term: &Term) -> bool {
    let mut head = term.strip_loc();
    while let Term::App(f, _, _) = head {
        head = f.strip_loc();
    }
    matches!(head, Term::Meta(m) if *m != stitchwort_core::value::ELIDED)
}

/// The call a lifted helper's frozen metavariable stands for, or the term a
/// queued check filled its placeholder with (`queue.rs`), if `term` is that
/// metavariable applied to all the variables it is a function of: the call
/// (a term in those variables), and the arguments. A helper's metavariable
/// applied to nothing is read back instead, as it always has been.
fn lifted_call<'a>(g: &Unifier<'_>, term: &'a Term) -> Option<(Rc<Term>, bool, Vec<&'a Term>)> {
    let (head, args) = term.spine();
    let Term::Meta(m) = head else { return None };
    let (s, call, annotated) = g.store.lifted_calls.borrow().get(m).cloned()?;
    if args.is_empty() && g.store.meta_frozen(*m) {
        return None;
    }
    (g.meta_solution(*m).is_some() && s == args.len()).then_some((call, annotated, args))
}

/// A lifted helper's call, `?m x y` for the frozen metavariable `?m`, with
/// the call it was solved with put in, its variables replaced by the
/// arguments (zonked). Reading the solution back from its value instead
/// would write out what the call's arguments unfold to: a scrutinee
/// `findThing id xs` as `List.find (t => …) xs` with the calls in its
/// lambda, `Text.decEq` among them, unfolded too (SW-343).
fn zonk_call(
    g: &Unifier<'_>,
    level: usize,
    call: &Term,
    annotated: bool,
    args: &[&Term],
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    let n = args.len();
    // A call of no arguments that is a leaf other than an unknown (a waiting
    // literal's number, most often) has nothing in it to zonk or replace.
    if n == 0 && !matches!(call, Term::Meta(_)) {
        let mut leaf = true;
        call.for_each_child(|_, _| leaf = false);
        if leaf {
            return refold(g, call.clone(), level, lets);
        }
    }
    let mut zonked = Vec::with_capacity(n);
    for a in args {
        zonked.push(zonk_in(g, level, a, keep, lets)?);
    }
    // A helper's call is zonked before it is recorded; a queued check's term
    // (`queue.rs`) is recorded when its check returns, and may mention
    // unknowns solved since (a literal's type parameters, say): zonked here,
    // in its own variables.
    let zonked_call;
    let call = if (call.subterms()).any(|(t, _)| matches!(t, Term::Meta(_))) {
        zonked_call = zonk_in(g, n, call, keep, &[])?;
        &zonked_call
    } else {
        call
    };
    if let Some(m) = call.subterms().find_map(|(t, _)| match t {
        Term::Meta(m) if !keep(*m) => Some(*m),
        _ => None,
    }) {
        return Err(ZonkError::Unsolved(m));
    }
    // A queued check's term may annotate a `let`'s lambda it applies
    // (`annotated`, `queue::placeholder_call`); folded back to the `let`'s
    // variable, the annotation says nothing the variable's type doesn't,
    // and is dropped.
    let refold = |term: Term| {
        let term = refold(g, term, level, lets)?;
        if !annotated {
            return Ok(term);
        }
        Ok(unannotate_let_heads(g, &term, level, 0, lets)?.unwrap_or(term))
    };
    // A call of no arguments (a waiting literal's number, say) has no
    // variable to replace.
    if n == 0 {
        return refold(call.clone());
    }
    let failed = std::cell::Cell::new(false);
    let hook = |t: &Term, under: usize| {
        let Term::Var(ix) = t else { return None };
        if *ix < under {
            return None;
        }
        match zonked[n - 1 - (ix - under)].shift(g, under, 0) {
            Ok(t) => Some(t),
            Err(_) => {
                failed.set(true);
                None
            }
        }
    };
    let out = fold_back(g, call, 0, &hook);
    if failed.get() || out.is_err() {
        return Err(ZonkError::Resource(ResourceError::Nesting(
            crate::check::PASS,
        )));
    }
    let out = out.ok().flatten().unwrap_or_else(|| call.clone());
    refold(out)
}

/// `term` (under `under` binders, in `level` variables) with each annotated
/// `let` variable of `lets` applied to an argument, `(x : A) a`, as the
/// variable applied, `x a`: the kernel infers a variable's type, to which
/// `A`, having been checked, is convertible. `None` if there's none.
fn unannotate_let_heads(
    g: &Ev,
    term: &Term,
    level: usize,
    under: usize,
    lets: &[Around],
) -> Result<Option<Term>> {
    let failed = std::cell::RefCell::new(None);
    let hook = |t: &Term, under: usize| {
        let Term::App(h, a, i) = t else { return None };
        let Term::Ann(e, _) = h.strip_loc() else {
            return None;
        };
        let Term::Var(ix) = e.strip_loc() else {
            return None;
        };
        let slot = (level + under).checked_sub(ix + 1)?;
        if *ix < under || !lets.iter().any(|(s, _, _)| *s == slot) {
            return None;
        }
        match unannotate_let_heads(g, a, level, under, lets) {
            Ok(new) => Some(Term::App(
                e.clone(),
                new.map_or_else(|| a.clone(), Rc::new),
                *i,
            )),
            Err(err) => {
                failed.replace(Some(err));
                None
            }
        }
    };
    let out = fold_back(g, term, under, &hook)?;
    match failed.into_inner() {
        Some(err) => Err(err),
        None => Ok(out),
    }
}

/// [`zonk_in`]'s pass: `None` if `term` has nothing to replace. What's
/// unchanged is shared, not rebuilt: most of a large elaborated term has no
/// metavariables in it, and rebuilding it (and dropping the old copy) on
/// every pass cost more than the substitution itself.
fn zonk_changed(
    g: &Unifier<'_>,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
    depth: usize,
    changing: Option<&Changing>,
) -> std::result::Result<Option<Term>, ZonkError> {
    let found;
    let changing = match changing {
        None if depth >= LOOK_AHEAD_DEPTH => {
            found = Changing::of(g, term);
            Some(&found)
        }
        changing => changing,
    };
    if changing.is_some_and(|c| !c.changes(term)) {
        return Ok(None);
    }
    g.machine.budget.step()?;
    // A child, zonked; `None` if unchanged.
    let go = |t: &Rc<Term>, level| -> std::result::Result<Option<Rc<Term>>, ZonkError> {
        Ok(zonk_changed(g, level, t, keep, lets, depth + 1, changing)?.map(Rc::new))
    };
    let or = |new: Option<Rc<Term>>, old: &Rc<Term>| new.unwrap_or_else(|| old.clone());
    // The arguments, if any changed.
    let all = |ts: &[Rc<Term>]| -> std::result::Result<Option<Vec<Rc<Term>>>, ZonkError> {
        let mut out: Option<Vec<Rc<Term>>> = None;
        for (i, t) in ts.iter().enumerate() {
            if let Some(new) = go(t, level)? {
                out.get_or_insert_with(|| ts[..i].to_vec()).push(new);
            } else if let Some(out) = &mut out {
                out.push(t.clone());
            }
        }
        Ok(out)
    };
    Ok(match term {
        Term::Meta(_) | Term::App(..) if lifted_call(g, term).is_some() => {
            Some(zonk_lifted(g, level, term, keep, lets)?)
        }
        Term::Meta(_) | Term::App(..) if meta_headed(term) => {
            Some(zonk_solved(g, level, term, keep, lets)?)
        }
        Term::Let(..) => zonk_let(g, level, term, keep, lets, depth, changing)?,
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => None,
        Term::Data(d, args) => all(args)?.map(|args| Term::Data(*d, args)),
        Term::Ctor(d, c, args) => all(args)?.map(|args| Term::Ctor(*d, *c, args)),
        Term::Pi(x, i, a, b, _) => match (go(a, level)?, go(b, level + 1)?) {
            (None, None) => None,
            (a2, b2) => Some(Term::Pi(
                x.clone(),
                *i,
                or(a2, a),
                or(b2, b),
                ProofMark::Unknown,
            )),
        },
        Term::Lam(x, i, b, _) => {
            go(b, level + 1)?.map(|b| Term::Lam(x.clone(), *i, b, ProofMark::Unknown))
        }
        Term::App(f, a, i) => {
            let app = match (go(f, level)?, go(a, level)?) {
                (None, None) => None,
                (f2, a2) => Some(Term::App(or(f2, f), or(a2, a), *i)),
            };
            match empty_row_done(g, app.as_ref().unwrap_or(term)) {
                Some(value) => Some(value),
                None => app,
            }
        }
        Term::Ann(e, t) => match (go(e, level)?, go(t, level)?) {
            (None, None) => None,
            (e2, t2) => Some(Term::Ann(or(e2, e), or(t2, t))),
        },
        Term::Case(..) | Term::NumCase(..) => {
            zonk_cases(g, level, term, keep, lets, depth, changing)?
        }
        Term::Eq(t, a, b) => {
            let t2 = match t {
                Some(t) => go(t, level)?,
                None => None,
            };
            match (t2, go(a, level)?, go(b, level)?) {
                (None, None, None) => None,
                (t2, a2, b2) => Some(Term::Eq(
                    t.as_ref().map(|t| or(t2, t)),
                    or(a2, a),
                    or(b2, b),
                )),
            }
        }
        Term::J(m, b, p, _) => match (go(m, level)?, go(b, level)?, go(p, level)?) {
            (None, None, None) => None,
            (m2, b2, p2) => Some(Term::J(or(m2, m), or(b2, b), or(p2, p), ProofMark::Unknown)),
        },
        Term::Proj(d, i, t) => go(t, level)?.map(|t| Term::Proj(*d, *i, t)),
        Term::Quot(form, args, e, _) => {
            all(args)?.map(|args| Term::Quot(*form, args, *e, ProofMark::Unknown))
        }
        Term::Loc(span, t) => go(t, level)?.map(|t| Term::Loc(*span, t)),
    })
}

/// [`zonk_changed`] for an application of a lifted helper's unknown: the
/// call it stands for.
#[inline(never)]
fn zonk_lifted(
    g: &Unifier<'_>,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    let (call, annotated, args) = lifted_call(g, term).expect("just found");
    zonk_call(g, level, &call, annotated, &args, keep, lets)
}

/// [`zonk_changed`] for a term headed by an unknown: its solution
/// substituted.
#[inline(never)]
fn zonk_solved(
    g: &Unifier<'_>,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    let value = eval(g, &env, term)?;
    let unsolved = |t: &Term| {
        t.subterms().find_map(|(t, _)| match t {
            Term::Meta(m) if !keep(*m) => Some(*m),
            _ => None,
        })
    };
    // Read back as written: the solution substituted, its calls
    // kept as calls, even one that steps at once, so zonking
    // computes nothing a solution doesn't (docs/proposals/
    // folded-calls.md, stage 3; SW-2843).
    let mut solved = quote_as_written(g, level, &value)?;
    // A call's argument may mention an unknown its unfolding drops
    // (`const 0 []`, the list's element type unknown): then the
    // unfolding, as without gluing, but only within a small budget,
    // since a call that needs more to lose its unknown is better
    // reported unsolved than computed.
    if g.machine.glue.get() && unsolved(&solved).is_some() {
        let unfolded = g
            .machine
            .budget
            .aside(unfolding_limits(), || quote_internal(g, level, &value));
        // Running out of the side budget is "no unfolding"; the
        // operation running out, or being cancelled, is passed on.
        if let Some(e) = g.machine.budget.exhausted() {
            return Err(ZonkError::Resource(e));
        }
        match unfolded {
            Ok(unfolded) => solved = unfolded,
            Err(ResourceError::Work | ResourceError::Size(_) | ResourceError::Depth) => {}
            Err(e) => return Err(ZonkError::Resource(e)),
        }
    }
    if let Some(m) = unsolved(&solved) {
        return Err(ZonkError::Unsolved(m));
    }
    refold(g, solved, level, lets)
}

/// [`zonk_changed`] for a `let`.
#[inline(never)]
fn zonk_let(
    g: &Unifier<'_>,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
    depth: usize,
    changing: Option<&Changing>,
) -> std::result::Result<Option<Term>, ZonkError> {
    let Term::Let(x, a, v, b, e, _) = term else {
        unreachable!("a `let`");
    };
    let go = |t: &Rc<Term>, level| -> std::result::Result<Option<Rc<Term>>, ZonkError> {
        Ok(zonk_changed(g, level, t, keep, lets, depth + 1, changing)?.map(Rc::new))
    };
    let or = |new: Option<Rc<Term>>, old: &Rc<Term>| new.unwrap_or_else(|| old.clone());
    let a2 = go(a, level)?;
    let v2 = go(v, level)?;
    let v_now = v2.clone().unwrap_or_else(|| v.clone());
    let env: Vec<Value> = (0..level).map(Value::var).collect();
    let normals = cheaply(g, || value_forms(g, level, &eval(g, &env, &v_now)?));
    let mut normals: Vec<Term> = normals
        .unwrap_or_default()
        .into_iter()
        .filter(|n| worth_folding(g, n))
        .collect();
    // A solution can hold the value as elaborated: an annotated lambda
    // (`let check := r => 3 ∈ r.items`, `r`'s type found later), whose
    // read-backs, the bare lambda, `type_fixed` doesn't fold. The
    // annotation fixes its type as the `let`'s, so it folds as it is.
    if matches!(v_now.strip_loc(), Term::Ann(..))
        && !(normals.iter()).any(|n| stitchwort_core::value::same_term(n, &v_now))
    {
        normals.push(v_now.strip_loc().clone());
    }
    let b2 = if normals.is_empty() {
        go(b, level + 1)?
    } else {
        let mut inner = lets.to_vec();
        inner.extend(normals.into_iter().map(|n| (level, level, Rc::new(n))));
        zonk_changed(g, level + 1, b, keep, &inner, depth + 1, changing)?.map(Rc::new)
    };
    Ok(match (a2, v2, b2) {
        (None, None, None) => None,
        (a2, v2, b2) => Some(Term::Let(
            x.clone(),
            or(a2, a),
            or(v2, v),
            or(b2, b),
            *e,
            ProofMark::Unknown,
        )),
    })
}

/// [`zonk_changed`] for a `case` on a constructor or a number.
#[inline(never)]
fn zonk_cases(
    g: &Unifier<'_>,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
    depth: usize,
    changing: Option<&Changing>,
) -> std::result::Result<Option<Term>, ZonkError> {
    let go = |t: &Rc<Term>, level| -> std::result::Result<Option<Rc<Term>>, ZonkError> {
        Ok(zonk_changed(g, level, t, keep, lets, depth + 1, changing)?.map(Rc::new))
    };
    let or = |new: Option<Rc<Term>>, old: &Rc<Term>| new.unwrap_or_else(|| old.clone());
    Ok(match term {
        Term::Case(ix, d, branches) => {
            let mut new: Vec<Option<Rc<Term>>> = Vec::with_capacity(branches.len());
            for b in branches.iter() {
                new.push(match &b.body {
                    Some(body) => go(body, level + b.names.len())?,
                    None => None,
                });
            }
            if new.iter().all(Option::is_none) {
                None
            } else {
                Some(Term::Case(
                    *ix,
                    *d,
                    branches
                        .iter()
                        .zip(new)
                        .map(|(b, n)| stitchwort_core::term::Branch {
                            names: b.names.clone(),
                            body: b.body.as_ref().map(|old| or(n, old)),
                        })
                        .collect(),
                ))
            }
        }
        Term::NumCase(ix, arms, default) => {
            let mut new: Vec<Option<Rc<Term>>> = Vec::with_capacity(arms.len());
            for a in arms.iter() {
                new.push(go(&a.body, level)?);
            }
            let default2 = go(default, level)?;
            if new.iter().all(Option::is_none) && default2.is_none() {
                None
            } else {
                Some(Term::NumCase(
                    *ix,
                    arms.iter()
                        .zip(new)
                        .map(|(a, n)| stitchwort_core::term::NumArm {
                            value: a.value.clone(),
                            body: or(n, &a.body),
                        })
                        .collect(),
                    or(default2, default),
                ))
            }
        }
        _ => unreachable!("a `case`"),
    })
}

/// `v`, for `term` = `doneIn Empty v` or `doneD Total Empty v`: a pure
/// callback of an effect-polymorphic function, checked while its row (and
/// divergence, docs/proposals/partial-stage-3.md §2.2) was still unknown,
/// once the row is the empty one. The same term up to computation (`doneIn
/// Empty v` is `v`), as the plain function's callback is written, so what's
/// shown, hashed and followed by `decreasing` is the plain term.
fn empty_row_done(g: &Ev, term: &Term) -> Option<Term> {
    use stitchwort_core::Icit;
    use stitchwort_core::registry::Builtin;
    let Term::App(f, value, Icit::Explicit) = term else {
        return None;
    };
    let Term::App(head, row, Icit::Explicit) = f.strip_loc() else {
        return None;
    };
    let is_ctor = |t: &Term, b: Builtin| {
        matches!(t.strip_loc(), Term::Ctor(data, ctor, fields)
            if fields.is_empty() && g.env.registry().ctor(b) == Some((*data, *ctor)))
    };
    if !is_ctor(row, Builtin::RowEmpty) {
        return None;
    }
    let is_def = |t: &Term, b: Builtin| {
        matches!(t.strip_loc(), Term::App(d, _, Icit::Implicit)
            if matches!(d.strip_loc(), Term::Def(d) if g.env.registry().is_def(b, *d)))
    };
    let done = is_def(head, Builtin::DoneIn)
        || matches!(head.strip_loc(), Term::App(h, div, Icit::Explicit)
            if is_def(h, Builtin::DoneD) && is_ctor(div, Builtin::DivTotal));
    done.then(|| value.as_ref().clone())
}

/// Data types with proof positions, built in the kernel, for the unifier's
/// tests of proof irrelevance (docs/proposals/proof-irrelevance.md §8) here
/// and in `undo.rs`.
#[cfg(test)]
pub(crate) mod proof_fixture {
    use std::rc::Rc;

    use stitchwort_core::check::{self, CtorDecl};
    use stitchwort_core::{DataId, DefId, Icit, Kernel, ProofMark, Sort, Term};
    use stitchwort_syntax::{SourceMap, Span};

    /// - `N: Type = Z | S (n: N)`
    /// - `Q: Prop = MkQ (n: N)`, a proposition with a data field
    /// - `Box (a: Prop): Type = MkBox (x: a)`, a proof field
    /// - `T: Type = MkT (h: Q) (n: N)`, a proof field before data
    /// - `T2: Type = MkT2 (h: N) (n: N)`, `T` with both fields data
    /// - `pick (n: N) (b: Box Q): Q`, which unboxes at `Z`: `match n with
    ///   | Z => (match b with | MkBox x => x) | S m => MkQ m`
    /// - `pick2 (n: N) (b: Box Q): Q`, which unboxes at `S Z` instead
    /// - `ignores (n: N) (k: N) (h: Q): N := n`, which never reads `h`
    pub(crate) struct Proofs {
        pub(crate) n: DataId,
        pub(crate) q: DataId,
        pub(crate) boxed: DataId,
        pub(crate) t: DataId,
        pub(crate) t2: DataId,
        pub(crate) pick: DefId,
        pub(crate) pick2: DefId,
        pub(crate) ignores: DefId,
    }

    fn span() -> Span {
        Span::point(SourceMap::new().add("proofs", ""), 0)
    }

    fn data(g: &mut Kernel, name: &str, params: Vec<(&str, Term)>, sort: Sort) -> DataId {
        let params = params.into_iter().map(|(x, t)| (x.into(), t)).collect();
        check::declare_data(g, name.into(), name.into(), params, sort, span()).expect(name)
    }

    fn ctor(name: &str, fields: Vec<(&str, Term)>) -> CtorDecl {
        CtorDecl {
            name: name.into(),
            fields: fields
                .into_iter()
                .map(|(x, t)| (x.into(), t, span()))
                .collect(),
            result: Vec::new(),
            implicit: Vec::new(),
            braced: false,
        }
    }

    fn case(ix: usize, d: DataId, branches: Vec<(Vec<&str>, Term)>) -> Term {
        Term::Case(
            ix,
            d,
            branches
                .into_iter()
                .map(|(names, body)| stitchwort_core::term::Branch {
                    names: names.into_iter().map(Into::into).collect(),
                    body: Some(Rc::new(body)),
                })
                .collect(),
        )
    }

    pub(crate) fn build(g: &mut Kernel) -> Proofs {
        let n = data(g, "N", vec![], Sort::Type(0));
        let n_ty = Term::data(n, vec![]);
        check::define_ctors(
            g,
            n,
            vec![ctor("Z", vec![]), ctor("S", vec![("n", n_ty.clone())])],
        )
        .expect("N");
        let q = data(g, "Q", vec![], Sort::Prop);
        let q_ty = Term::data(q, vec![]);
        check::define_ctors(g, q, vec![ctor("MkQ", vec![("n", n_ty.clone())])]).expect("Q");
        let boxed = data(g, "Box", vec![("a", Term::Sort(Sort::Prop))], Sort::Type(0));
        check::define_ctors(g, boxed, vec![ctor("MkBox", vec![("x", Term::Var(0))])]).expect("Box");
        let t = data(g, "T", vec![], Sort::Type(0));
        let fields = vec![("h", q_ty.clone()), ("n", n_ty.clone())];
        check::define_ctors(g, t, vec![ctor("MkT", fields)]).expect("T");
        let t2 = data(g, "T2", vec![], Sort::Type(0));
        let fields = vec![("h", n_ty.clone()), ("n", n_ty.clone())];
        check::define_ctors(g, t2, vec![ctor("MkT2", fields)]).expect("T2");
        let pi = |x: &str, a: Term, b: Term| {
            Term::Pi(
                x.into(),
                Icit::Explicit,
                Rc::new(a),
                Rc::new(b),
                ProofMark::Unknown,
            )
        };
        let lam =
            |x: &str, b: Term| Term::Lam(x.into(), Icit::Explicit, Rc::new(b), ProofMark::Unknown);
        let pick_ty = pi(
            "n",
            n_ty,
            pi("b", Term::data(boxed, vec![q_ty.clone()]), q_ty.clone()),
        );
        let pick = check::declare_def(
            g,
            &"pick".into(),
            &"pick".into(),
            &pick_ty,
            false,
            false,
            span(),
        )
        .expect("pick declared");
        let body = lam(
            "n",
            lam(
                "b",
                case(
                    1,
                    n,
                    vec![
                        (vec![], case(0, boxed, vec![(vec!["x"], Term::Var(0))])),
                        (vec!["m"], Term::ctor(q, 0, vec![Term::Var(0)])),
                    ],
                ),
            ),
        );
        check::define_def(g, pick, &body).expect("pick");
        let pick2 = check::declare_def(
            g,
            &"pick2".into(),
            &"pick2".into(),
            &pick_ty,
            false,
            false,
            span(),
        )
        .expect("pick2 declared");
        let mq = |v| Term::ctor(q, 0, vec![v]);
        let body = lam(
            "n",
            lam(
                "b",
                case(
                    1,
                    n,
                    vec![
                        (vec![], mq(Term::ctor(n, 0, vec![]))),
                        (
                            vec!["m"],
                            case(
                                0,
                                n,
                                vec![
                                    (vec![], case(1, boxed, vec![(vec!["x"], Term::Var(0))])),
                                    (vec!["k"], mq(Term::Var(0))),
                                ],
                            ),
                        ),
                    ],
                ),
            ),
        );
        check::define_def(g, pick2, &body).expect("pick2");
        let n_ty = Term::data(n, vec![]);
        let ignores_ty = pi(
            "n",
            n_ty.clone(),
            pi("k", n_ty.clone(), pi("h", q_ty.clone(), n_ty)),
        );
        let ignores = check::declare_def(
            g,
            &"ignores".into(),
            &"ignores".into(),
            &ignores_ty,
            false,
            false,
            span(),
        )
        .expect("ignores declared");
        let body = lam("n", lam("k", lam("h", Term::Var(2))));
        check::define_def(g, ignores, &body).expect("ignores");
        Proofs {
            n,
            q,
            boxed,
            t,
            t2,
            pick,
            pick2,
            ignores,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Elaborator;
    use stitchwort_core::ProofMark;
    use stitchwort_core::registry::Builtin;
    use stitchwort_core::value::Apart;
    use stitchwort_core::{Icit, Sort};
    use stitchwort_syntax::{SourceMap, Span};

    /// A fresh unifier's state.
    #[derive(Default)]
    struct Fresh {
        g: stitchwort_core::Kernel,
        store: crate::state::MetaStore,
        attempt: Attempt,
        stats: Stats,
    }

    impl Fresh {
        fn unifier(&self) -> Unifier<'_> {
            Unifier {
                ev: Ev {
                    metas: &self.store,
                    ..self.g.ev()
                },
                store: &self.store,
                attempt: &self.attempt,
                stats: &self.stats,
            }
        }
    }

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    /// A fresh metavariable applied to the variables at `levels`.
    fn meta(g: &Unifier<'_>, levels: &[usize]) -> (usize, Value) {
        let m = g.store.new_meta(span());
        let spine = levels
            .iter()
            .map(|l| Elim::App(Value::var(*l), Icit::Explicit))
            .collect();
        (m, Value::Neutral(Head::Meta(m), spine))
    }

    fn ty() -> Value {
        Value::Sort(Sort::Type(0))
    }

    fn eq(a: Value, b: Value) -> Value {
        Value::Eq(Rc::new(ty()).into(), Rc::new(a).into(), Rc::new(b).into())
    }

    fn is_var(g: &Unifier<'_>, v: &Value, level: usize) -> bool {
        matches!(force(g, v.clone()).unwrap(), Value::Neutral(Head::Var(l, _, _), s) if l == level && s.is_empty())
    }

    /// Which lambdas `eta_contract` contracts, by de Bruijn index: `f` is
    /// free variable `f`, and a lambda only contracts when its body applies
    /// something that mentions none of its binders to all of them, in order,
    /// with matching implicitness.
    #[test]
    fn eta_contract_contracts_only_lambdas_that_apply_a_function_to_their_variables() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let var = |ix: usize| Rc::new(Term::Var(ix));
        let app = |f: Rc<Term>, a: Rc<Term>, icit: Icit| Rc::new(Term::App(f, a, icit));
        let lam = |icit: Icit, body: Rc<Term>| {
            Rc::new(Term::Lam("x".into(), icit, body, ProofMark::Unknown))
        };
        let (ex, im) = (Icit::Explicit, Icit::Implicit);
        let contracted = |t: Rc<Term>| eta_contract(g, &t).ok().unwrap();
        // `x y => f x y` is `f` (index 2 under two binders, 0 outside).
        let t = lam(ex, lam(ex, app(app(var(2), var(1), ex), var(0), ex)));
        assert!(matches!(contracted(t), Some(Term::Var(0))));
        // `x y => f y x` applies in the wrong order.
        let t = lam(ex, lam(ex, app(app(var(2), var(0), ex), var(1), ex)));
        assert!(contracted(t).is_none());
        // `x y => f y` is `x => f`: a lambda still.
        let t = lam(ex, lam(ex, app(var(2), var(0), ex)));
        assert!(contracted(t).is_none());
        // `x y => h x x y`: the function mentions `x`.
        let t = lam(
            ex,
            lam(
                ex,
                app(app(app(var(3), var(1), ex), var(1), ex), var(0), ex),
            ),
        );
        assert!(contracted(t).is_none());
        // `f x => f x`: the identity on `f`, whose application to `x` is not
        // a function of anything else.
        let t = lam(ex, lam(ex, app(var(1), var(0), ex)));
        assert!(contracted(t).is_none());
        // `{a} x => g {a} x` is `g`.
        let t = lam(im, lam(ex, app(app(var(2), var(1), im), var(0), ex)));
        assert!(matches!(contracted(t), Some(Term::Var(0))));
        // `{a} x => g a x`: the lambda's implicit binder is applied
        // explicitly.
        let t = lam(im, lam(ex, app(app(var(2), var(1), ex), var(0), ex)));
        assert!(contracted(t).is_none());
        // `x => f a x` is `f a`, for the free variables `f` and `a`.
        let t = lam(ex, app(app(var(2), var(1), ex), var(0), ex));
        assert!(matches!(
            contracted(t),
            Some(Term::App(ref f, ref a, _)) if matches!(**f, Term::Var(1)) && matches!(**a, Term::Var(0))
        ));
        // Not a lambda.
        assert!(contracted(app(var(1), var(0), ex)).is_none());
    }

    /// A `let` at level 0 whose value, after a case split, mentions the
    /// variable at level 1 (a constructor's field bound after it): its
    /// normal form is in a context of two variables, and folds back to the
    /// `let` only where both are in scope.
    #[test]
    fn a_let_whose_value_mentions_a_later_variable_folds_back_where_it_is_in_scope() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let pair =
            |a: usize, b: usize| Term::Eq(None, Rc::new(Term::Var(a)), Rc::new(Term::Var(b)));
        // `level 1 = level 0`, in a context of two variables.
        let lets: Vec<Around> = vec![(0, 2, Rc::new(pair(0, 1)))];
        let folded = |term: Term, level: usize| refold(g, term, level, &lets).ok().unwrap();
        assert!(matches!(folded(pair(0, 1), 2), Term::Var(1)));
        assert!(matches!(folded(pair(1, 2), 3), Term::Var(2)));
        // Under a binder of its own.
        let under = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(pair(1, 2)),
            ProofMark::Unknown,
        );
        assert!(matches!(
            folded(under, 2),
            Term::Lam(_, _, ref body, _) if matches!(**body, Term::Var(2))
        ));
        // With only the `let` in scope, nothing is folded.
        assert!(matches!(folded(pair(0, 0), 1), Term::Eq(..)));
    }

    // Proof irrelevance (docs/proposals/proof-irrelevance.md §7.5, §8)

    fn proofs() -> (Fresh, proof_fixture::Proofs) {
        let mut fresh = Fresh::default();
        let ids = proof_fixture::build(&mut fresh.g);
        (fresh, ids)
    }

    fn numeral(p: &proof_fixture::Proofs, k: usize) -> Value {
        (0..k).fold(Value::Ctor(p.n, 0, Vec::new().into()), |n, _| {
            Value::Ctor(p.n, 1, [n].into())
        })
    }

    /// Test 11: nothing is solved from inside a proof field, and a whole
    /// proof argument that is an unknown is solved.
    #[test]
    fn an_unknown_inside_a_proof_field_is_not_solved() {
        let (fresh, p) = proofs();
        let g = &fresh.unifier();
        let mk_box = |v: Value| Value::Ctor(p.boxed, 0, [v].into());
        let mk_q = |v: Value| Value::Ctor(p.q, 0, [v].into());
        let (m, m_value) = meta(g, &[]);
        assert!(unify(g, 0, &mk_box(mk_q(m_value)), &mk_box(mk_q(numeral(&p, 3)))).unwrap());
        assert!(g.meta_solution(m).is_none());
        // Paired: the whole field an unknown.
        let (whole, whole_value) = meta(g, &[]);
        let proof = mk_q(numeral(&p, 3));
        assert!(unify(g, 0, &mk_box(whole_value), &mk_box(proof.clone())).unwrap());
        assert!(conv(g, 0, &g.meta_solution(whole).expect("solved"), &proof).unwrap());
    }

    /// Test 11b: nothing read from inside a skipped proof reaches a later
    /// relevant field.
    #[test]
    fn nothing_flows_out_of_a_proof_field() {
        let (fresh, p) = proofs();
        let g = &fresh.unifier();
        let mk_q = |v: Value| Value::Ctor(p.q, 0, [v].into());
        let three = numeral(&p, 3);
        let (m, m_value) = meta(g, &[]);
        let (k, k_value) = meta(g, &[]);
        let lhs = Value::Ctor(p.t, 0, [mk_q(m_value.clone()), m_value].into());
        let rhs = Value::Ctor(p.t, 0, [mk_q(three.clone()), k_value].into());
        assert!(unify(g, 0, &lhs, &rhs).unwrap());
        let solved_as_three = |m: usize| {
            g.meta_solution(m)
                .is_some_and(|v| conv(g, 0, &v, &three).unwrap())
        };
        assert!(!solved_as_three(m) && !solved_as_three(k));
        // Paired: with the first field data, `?m := 3`, then `?k := 3`.
        let (m, m_value) = meta(g, &[]);
        let (k, k_value) = meta(g, &[]);
        let lhs = Value::Ctor(p.t2, 0, [m_value.clone(), m_value].into());
        let rhs = Value::Ctor(p.t2, 0, [three.clone(), k_value].into());
        assert!(unify(g, 0, &lhs, &rhs).unwrap());
        assert!(solved_as_three(m) && solved_as_three(k));
    }

    /// Test 28, under rule I: `pick` returns a proof, so `pick ?n (MkBox p)`
    /// and `pick ?n (MkBox q)` are equal unlooked at, and nothing inside is
    /// solved, even where the arguments would say what `?n` is (the
    /// inference E2 gives up, docs/proposals/full-proof-irrelevance.md §7).
    /// The kernel agrees at every solution: there both are proofs too.
    #[test]
    fn calls_of_a_proof_are_equal_by_rule_i() {
        let (fresh, p) = proofs();
        let g = &fresh.unifier();
        let proof = |l: usize| Value::var_marked(l, ProofMark::Proof);
        let call = |f: DefId, n: Value, x: Value| {
            let f = eval(g, &[], &Term::Def(f)).unwrap();
            let f = apply_icit(g, f, n, Icit::Explicit).unwrap();
            apply_icit(g, f, Value::Ctor(p.boxed, 0, [x].into()), Icit::Explicit).unwrap()
        };
        let z = || Value::Ctor(p.n, 0, Vec::new().into());
        let (n, n_value) = meta(g, &[]);
        let (a, b) = (
            call(p.pick, n_value.clone(), proof(0)),
            call(p.pick, n_value, proof(1)),
        );
        assert!(unify(g, 2, &a, &b).unwrap());
        assert!(g.meta_solution(n).is_none());
        let (n, n_value) = meta(g, &[2]);
        let a = call(p.pick, n_value, proof(0));
        assert!(unify(g, 3, &a, &call(p.pick, Value::var(2), proof(0))).unwrap());
        assert!(g.meta_solution(n).is_none());
        for f in [p.pick, p.pick2] {
            let (a, b) = (call(f, z(), proof(0)), call(f, z(), proof(1)));
            assert!(conv(g, 2, &a, &b).unwrap());
        }
    }

    /// An argument after a `J` is compared, as every argument is.
    #[test]
    fn an_argument_after_a_j_is_unified() {
        let (fresh, p) = proofs();
        let g = &fresh.unifier();
        let spine = |last: usize| {
            let elims = vec![
                Elim::App(Value::var(0), Icit::Explicit),
                Elim::J {
                    motive: Box::new(Value::var(1)),
                    base: Box::new(Value::var(2)),
                    result: ProofMark::Unknown,
                    ends: None,
                },
                Elim::App(Value::var(last), Icit::Explicit),
            ];
            Value::Neutral(Head::Def(p.ignores), elims.into())
        };
        assert!(!unify(g, 5, &spine(3), &spine(4)).unwrap());
    }

    #[test]
    fn solves_a_pattern() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?m x0 x1 = x1, so ?m = a b => b
        let (m, lhs) = meta(g, &[0, 1]);
        assert!(unify(g, 2, &lhs, &Value::var(1)).unwrap());
        let solution = g.meta_solution(m).expect("solved");
        let applied = apply_icit(
            g,
            apply_icit(g, solution, Value::var(5), Icit::Explicit).unwrap(),
            Value::var(7),
            Icit::Explicit,
        )
        .unwrap();
        assert!(is_var(g, &applied, 7));
    }

    /// A kernel with `first: Type -> Type -> Type := a b => a`, gluing on.
    fn with_first() -> (Fresh, stitchwort_core::DefId) {
        let mut fresh = Fresh::default();
        let g = &mut fresh.g;
        let ty_term = Term::Sort(Sort::Type(0));
        let arrow = |a: Term, b: Term| {
            Term::Pi(
                "_".into(),
                Icit::Explicit,
                Rc::new(a),
                Rc::new(b),
                ProofMark::Unknown,
            )
        };
        let fn_ty = arrow(ty_term.clone(), arrow(ty_term.clone(), ty_term));
        let id = stitchwort_core::check::declare_def(
            g,
            &"first".into(),
            &"first".into(),
            &fn_ty,
            false,
            false,
            span(),
        )
        .expect("declared");
        let body = Term::Lam(
            "a".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "b".into(),
                Icit::Explicit,
                Rc::new(Term::Var(1)),
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        );
        stitchwort_core::check::define_def(g, id, &body).expect("defined");
        g.machine.glue.set(true);
        (fresh, id)
    }

    /// `first x_a x_b`, glued, with `level` variables in scope.
    fn first_of(g: &Ev, id: stitchwort_core::DefId, level: usize, a: usize, b: usize) -> Value {
        let env: Vec<Value> = (0..level).map(Value::var).collect();
        let call = Term::app(
            Term::app(Term::Def(id), Term::Var(level - 1 - a)),
            Term::Var(level - 1 - b),
        );
        let value = eval(g, &env, &call).unwrap();
        assert!(matches!(value, Value::Call(..)));
        value
    }

    #[test]
    fn a_solution_is_written_with_the_call_folded() {
        let (fresh, id) = with_first();
        let g = &fresh.unifier();
        // ?m x0 x1 = first x0 x1, so ?m = a b => first a b, not a b => a.
        let (m, lhs) = meta(g, &[0, 1]);
        assert!(unify(g, 2, &lhs, &first_of(g, id, 2, 0, 1)).unwrap());
        #[allow(clippy::disallowed_methods)]
        let solution = quote_folded(g, 0, &g.meta_solution(m).expect("solved")).unwrap();
        assert!(
            solution
                .subterms()
                .any(|(t, _)| matches!(t, Term::Def(d) if *d == id)),
            "{solution:?}"
        );
    }

    /// An unknown only in an argument a call drops (`first x0 ?n`) doesn't
    /// stop the solution being zonked: the call is unfolded, within the
    /// fallback's budget, and the unknown goes with it.
    #[test]
    fn an_unknown_only_in_a_dropped_argument_is_unfolded_away() {
        let (fresh, id) = with_first();
        let g = &fresh.unifier();
        let (n, _) = meta(g, &[]);
        let (m, lhs) = meta(g, &[0]);
        let call = Term::app(Term::app(Term::Def(id), Term::Var(0)), Term::Meta(n));
        let call = eval(g, &[Value::var(0)], &call).unwrap();
        assert!(unify(g, 1, &lhs, &call).unwrap());
        let solution = quote_as_written(g, 0, &g.meta_solution(m).expect("solved")).unwrap();
        assert!(
            solution
                .subterms()
                .any(|(t, _)| matches!(t, Term::Meta(k) if *k == n)),
            "{solution:?}"
        );
        let zonked = zonk(g, 1, &Term::app(Term::Meta(m), Term::Var(0))).expect("unfolded");
        assert!(matches!(zonked, Term::Var(0)), "{zonked:?}");
        assert!(g.meta_solution(n).is_none());
    }

    #[test]
    fn a_call_whose_arguments_are_out_of_scope_is_written_unfolded() {
        let (fresh, id) = with_first();
        let g = &fresh.unifier();
        // ?m x0 = first x0 x1: `x1` can't be in the solution, but
        // `first x0 x1` unfolds to `x0`, so ?m = a => a.
        let (m, lhs) = meta(g, &[0]);
        assert!(unify(g, 2, &lhs, &first_of(g, id, 2, 0, 1)).unwrap());
        let solution = g.meta_solution(m).expect("solved");
        let applied = apply_icit(g, solution, Value::var(5), Icit::Explicit).unwrap();
        assert!(is_var(g, &applied, 5));
    }

    #[test]
    fn solves_from_either_side() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, rhs) = meta(g, &[]);
        assert!(unify(g, 0, &ty(), &rhs).unwrap());
        assert!(matches!(
            g.meta_solution(m),
            Some(Value::Sort(Sort::Type(0)))
        ));
    }

    #[test]
    fn refuses_a_circular_solution() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?m x0 = (?m x0 = x0) has no finite solution.
        let (m, lhs) = meta(g, &[0]);
        assert!(!unify(g, 1, &lhs, &eq(lhs.clone(), Value::var(0))).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn refuses_a_solution_mentioning_a_variable_out_of_scope() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?m only receives x0, so it can't be x1.
        let (m, lhs) = meta(g, &[0]);
        assert!(!unify(g, 2, &lhs, &Value::var(1)).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn refuses_a_spine_that_repeats_a_variable() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?m x0 x0 = x0 has two solutions (a b => a and a b => b), so neither is chosen.
        let (m, lhs) = meta(g, &[0, 0]);
        assert!(!unify(g, 1, &lhs, &Value::var(0)).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn solves_a_spine_that_repeats_a_variable_when_the_other_side_ignores_it() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?m x0 x0 = Type has one solution, `a b => Type`.
        let (m, lhs) = meta(g, &[0, 0]);
        assert!(unify(g, 1, &lhs, &ty()).unwrap());
        assert!(g.meta_solution(m).is_some());
    }

    /// `?m x0 (x0 = x0)`, the second argument not a variable.
    fn meta_with_a_term(g: &Unifier<'_>) -> (usize, Value) {
        let m = g.store.new_meta(span());
        let spine = [
            Elim::App(Value::var(0), Icit::Explicit),
            Elim::App(eq(Value::var(0), Value::var(0)), Icit::Explicit),
        ]
        .into_iter()
        .collect();
        (m, Value::Neutral(Head::Meta(m), spine))
    }

    #[test]
    fn solves_an_ignorable_argument_that_is_not_a_variable() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // A proof's unknown whose statement doesn't depend on its second
        // argument (SW-323): ?m x0 (x0 = x0) = x0 is solved by `a b => a`.
        let (m, lhs) = meta_with_a_term(g);
        g.store.set_meta_ignorable(m, Rc::from([false, true]));
        assert!(unify(g, 1, &lhs, &Value::var(0)).unwrap());
        let solution = g.meta_solution(m).expect("solved");
        let applied = apply_icit(
            g,
            apply_icit(g, solution, Value::var(5), Icit::Explicit).unwrap(),
            Value::var(7),
            Icit::Explicit,
        )
        .unwrap();
        assert!(is_var(g, &applied, 5));
    }

    #[test]
    fn an_unknown_that_may_ignore_is_left_for_the_other() {
        // ?a x0 = ?b x0 x1, either way round, where ?a may ignore x0: ?b is
        // solved with ?a, so ?a keeps what it may ignore (SW-3890). Solving
        // ?a instead would prune x1 from ?b into a new unknown without it.
        for flipped in [false, true] {
            let fresh = Fresh::default();
            let g = &fresh.unifier();
            let (a, lhs) = meta(g, &[0]);
            g.store.set_meta_ignorable(a, Rc::from([true]));
            let (b, rhs) = meta(g, &[0, 1]);
            let (l, r) = if flipped { (&rhs, &lhs) } else { (&lhs, &rhs) };
            assert!(unify(g, 2, l, r).unwrap());
            assert!(g.meta_solution(a).is_none());
            assert!(g.meta_solution(b).is_some());
        }
    }

    #[test]
    fn refuses_an_argument_that_is_not_a_variable_unless_ignorable() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, lhs) = meta_with_a_term(g);
        assert!(!unify(g, 1, &lhs, &Value::var(0)).unwrap());
        assert!(g.meta_solution(m).is_none());
        let (m, lhs) = meta_with_a_term(g);
        g.store.set_meta_ignorable(m, Rc::from([true, false]));
        assert!(!unify(g, 1, &lhs, &Value::var(0)).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn the_same_metavariable_needs_matching_arguments() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (_, a) = meta(g, &[0, 1]);
        let b = match &a {
            Value::Neutral(head, _) => Value::Neutral(
                *head,
                vec![
                    Elim::App(Value::var(1), Icit::Explicit),
                    Elim::App(Value::var(0), Icit::Explicit),
                ]
                .into(),
            ),
            _ => unreachable!(),
        };
        assert!(unify(g, 2, &a, &a.clone()).unwrap());
        assert!(!unify(g, 2, &a, &b).unwrap());
    }

    #[test]
    fn prunes_dependencies_that_a_solution_cannot_have() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?a = (?b x0 = Type), where ?a can't depend on x0. Pruning solves
        // ?b := _ => ?c, so the equation has the solution ?a := (?c = Type).
        let (a, lhs) = meta(g, &[]);
        let (b, b_applied) = meta(g, &[0]);
        assert!(unify(g, 1, &lhs, &eq(b_applied.clone(), ty())).unwrap());
        assert!(g.meta_solution(a).is_some());
        assert!(g.meta_solution(b).is_some());
        match force(g, b_applied).unwrap() {
            Value::Neutral(Head::Meta(c), spine) => {
                assert_ne!(c, b);
                assert!(spine.is_empty(), "?c doesn't depend on x0");
            }
            other => panic!("expected ?b x0 to reduce to a new metavariable, got {other:?}"),
        }
    }

    #[test]
    fn zonk_reports_an_unsolved_metavariable() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, _) = meta(g, &[]);
        assert_eq!(
            zonk(g, 0, &Term::Meta(m)).err(),
            Some(ZonkError::Unsolved(m))
        );
    }

    #[test]
    fn zonk_substitutes_and_normalises_a_solution() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, lhs) = meta(g, &[0]);
        assert!(unify(g, 1, &lhs, &Value::var(0)).unwrap());
        // ?m x0 with ?m = a => a zonks to x0.
        let term = Term::app(Term::Meta(m), Term::Var(0));
        let zonked = zonk(g, 1, &term).expect("solved");
        assert!(matches!(zonked, Term::Var(0)), "{zonked:?}");
    }

    /// An unknown solved with a deep value: constructors nested 200 deep
    /// around a variable, a field of another constructor, are written back
    /// as the same terms (`rename_in`, SW-3133).
    #[test]
    fn a_solution_is_written_back_from_a_deep_value() {
        let (fresh, p) = proofs();
        let g = &fresh.unifier();
        let depth = 200;
        let succs = (0..depth).fold(Value::var(0), |n, _| Value::Ctor(p.n, 1, [n].into()));
        let zero = Value::Ctor(p.n, 0, Vec::new().into());
        let rhs = Value::Ctor(p.t2, 0, [zero, succs].into());
        let (m, lhs) = meta(g, &[0]);
        assert!(unify(g, 1, &lhs, &rhs).unwrap());
        let solved = zonk(g, 1, &Term::app(Term::Meta(m), Term::Var(0))).expect("solved");
        let Term::Ctor(d, 0, fields) = &solved else {
            panic!("{solved:?}")
        };
        assert_eq!(*d, p.t2);
        assert!(matches!(*fields[0], Term::Ctor(_, 0, _)), "{solved:?}");
        let mut t: &Term = &fields[1];
        for _ in 0..depth {
            let Term::Ctor(d, 1, fields) = t else {
                panic!("{t:?}")
            };
            assert_eq!(*d, p.n);
            t = &fields[0];
        }
        assert!(matches!(t, Term::Var(0)), "{t:?}");
    }

    /// Past `LOOK_AHEAD_DEPTH`, zonking goes down only the parts with
    /// something to replace: all the way to an unknown at the bottom, and
    /// not into a deep part with none, which is kept as it was.
    #[test]
    fn zonk_goes_down_a_deep_term_only_where_it_changes() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, lhs) = meta(g, &[0]);
        assert!(unify(g, 1, &lhs, &Value::var(0)).unwrap());
        let solved = Term::app(Term::Meta(m), Term::Var(0));
        let wrap = |t: Term, n: usize| (0..n).fold(t, |t, _| Term::app(Term::Var(0), t));
        let zonked = zonk(g, 1, &wrap(solved.clone(), 100)).expect("solved");
        assert_eq!(
            format!("{zonked:?}"),
            format!("{:?}", wrap(Term::Var(0), 100))
        );
        let deep = Rc::new(wrap(Term::Var(0), 100_000));
        let term = Term::Ann(Rc::new(solved), deep.clone());
        let zonked = zonk(g, 1, &term).expect("solved");
        let Term::Ann(e, t) = &zonked else {
            panic!("an annotation")
        };
        assert!(matches!(**e, Term::Var(0)), "{e:?}");
        assert!(Rc::ptr_eq(t, &deep), "kept as it was");
    }

    /// `Empty` and `Effect.doneIn`, bound as the built-ins `empty_row_done`
    /// reads: a bare `Fresh` has neither.
    fn empty_row_fixture() -> (Fresh, stitchwort_core::DataId, DefId) {
        use stitchwort_core::check::{self, CtorDecl};
        let mut fresh = Fresh::default();
        let g = &mut fresh.g;
        let row = check::declare_data(
            g,
            "Effect.Effects".into(),
            "Effect.Effects".into(),
            Vec::new(),
            Sort::Type(0),
            span(),
        )
        .expect("the row data type");
        check::define_ctors(
            g,
            row,
            vec![CtorDecl {
                name: "Empty".into(),
                fields: Vec::new(),
                result: Vec::new(),
                implicit: Vec::new(),
                braced: false,
            }],
        )
        .expect("Empty");
        let done = check::declare_def(
            g,
            &"Effect.doneIn".into(),
            &"Effect.doneIn".into(),
            &Term::Sort(Sort::Type(0)),
            false,
            false,
            span(),
        )
        .expect("doneIn");
        check::define_def(g, done, &Term::Data(row, Vec::new())).expect("doneIn's body");
        assert_eq!(
            stitchwort_core::registry::bind_data(g, row),
            Some(Builtin::Row)
        );
        assert_eq!(
            stitchwort_core::registry::bind_def(g, done),
            Some(Builtin::DoneIn)
        );
        (fresh, row, done)
    }

    /// `doneIn Empty v` is another node `Changing` marks (`empty_row_done`):
    /// below the look-ahead depth and with no metavariable near it, zonking
    /// still goes down to it and replaces it with `v`, while a deeper part
    /// with nothing to change is kept as it was.
    #[test]
    fn zonk_goes_down_to_an_empty_row_done_below_the_look_ahead_depth() {
        let (fresh, row, done) = empty_row_fixture();
        let g = &fresh.unifier();
        let wrap = |t: Term, n: usize| (0..n).fold(t, |t, _| Term::app(Term::Var(0), t));
        let head = Term::App(
            Rc::new(Term::Def(done)),
            Rc::new(Term::Sort(Sort::Type(0))),
            Icit::Implicit,
        );
        let once = Term::App(
            Rc::new(head),
            Rc::new(Term::Ctor(row, 0, Vec::new())),
            Icit::Explicit,
        );
        let term = Term::App(Rc::new(once), Rc::new(Term::Var(0)), Icit::Explicit);
        assert!(
            matches!(empty_row_done(g, &term), Some(Term::Var(0))),
            "the fixture is the case `empty_row_done` takes apart"
        );
        let deep = Rc::new(wrap(term, 100));
        let before = g.machine.budget.total_work();
        let zonked = zonk(g, 1, &deep).expect("zonked");
        let steps = g.machine.budget.total_work() - before;
        assert_eq!(
            format!("{zonked:?}"),
            format!("{:?}", wrap(Term::Var(0), 100)),
            "`doneIn Empty v` is `v`, 100 levels down"
        );
        assert!(
            steps < 1_000,
            "went down only to the node that changes: {steps} steps"
        );
        // A sibling far deeper with nothing to change is kept, not rebuilt.
        let huge = Rc::new(wrap(Term::Var(0), 100_000));
        let ann = Term::Ann(deep.clone(), huge.clone());
        let zonked = zonk(g, 1, &ann).expect("zonked");
        let Term::Ann(e, t) = &zonked else {
            panic!("an annotation")
        };
        assert_eq!(format!("{e:?}"), format!("{:?}", wrap(Term::Var(0), 100)));
        assert!(Rc::ptr_eq(t, &huge), "kept as it was");
    }

    fn closed(g: &Unifier<'_>, t: &Term) -> Value {
        eval(g, &[], t).unwrap()
    }

    fn pi(i: Icit, a: Term, b: Term) -> Term {
        Term::Pi("x".into(), i, Rc::new(a), Rc::new(b), ProofMark::Unknown)
    }

    fn lam(b: Term) -> Term {
        Term::Lam("x".into(), Icit::Explicit, Rc::new(b), ProofMark::Unknown)
    }

    fn sort(i: u32) -> Term {
        Term::Sort(Sort::Type(i))
    }

    #[test]
    fn refuses_to_unify_things_that_differ_anywhere() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let refl_eq = |a: Term, b: Term| Term::Eq(Some(Rc::new(sort(1))), Rc::new(a), Rc::new(b));
        let differ = [
            (
                pi(Icit::Explicit, sort(0), sort(0)),
                pi(Icit::Explicit, sort(1), sort(0)),
            ),
            (
                pi(Icit::Explicit, sort(0), sort(0)),
                pi(Icit::Explicit, sort(0), sort(1)),
            ),
            (
                pi(Icit::Explicit, sort(0), sort(0)),
                pi(Icit::Implicit, sort(0), sort(0)),
            ),
            (lam(Term::Var(0)), lam(sort(0))),
            (lam(lam(Term::Var(1))), lam(lam(Term::Var(0)))),
            (refl_eq(sort(0), sort(0)), refl_eq(sort(1), sort(0))),
            (refl_eq(sort(0), sort(0)), refl_eq(sort(0), sort(1))),
            (Term::Refl, sort(0)),
        ];
        for (a, b) in &differ {
            assert!(
                !unify(g, 0, &closed(g, a), &closed(g, b)).unwrap(),
                "{a:?} vs {b:?}"
            );
            assert!(
                !unify(g, 0, &closed(g, b), &closed(g, a)).unwrap(),
                "{b:?} vs {a:?}"
            );
            assert!(
                unify(g, 0, &closed(g, a), &closed(g, a)).unwrap(),
                "{a:?} vs itself"
            );
        }
        // Eta: `x => f x` unifies with `f`, but `x y => f y x` doesn't.
        let f = Value::var(0);
        let eta = eval(
            g,
            std::slice::from_ref(&f),
            &lam(Term::app(Term::Var(1), Term::Var(0))),
        )
        .unwrap();
        assert!(unify(g, 1, &eta, &f).unwrap());
        assert!(unify(g, 1, &f, &eta).unwrap());
        let flipped = eval(
            g,
            std::slice::from_ref(&f),
            &lam(lam(Term::app(
                Term::app(Term::Var(2), Term::Var(0)),
                Term::Var(1),
            ))),
        )
        .unwrap();
        assert!(!unify(g, 1, &flipped, &f).unwrap());
    }

    #[test]
    fn spines_must_match_in_length_and_elements() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let x = Value::var(0);
        let applied = |args: Vec<usize>| {
            Value::Neutral(
                Head::Var(0, Apart::NONE, ProofMark::Unknown),
                args.into_iter()
                    .map(|l| Elim::App(Value::var(l), Icit::Explicit))
                    .collect(),
            )
        };
        assert!(unify(g, 3, &applied(vec![1, 2]), &applied(vec![1, 2])).unwrap());
        assert!(!unify(g, 3, &applied(vec![1, 2]), &applied(vec![2, 1])).unwrap());
        assert!(!unify(g, 3, &applied(vec![1]), &applied(vec![1, 2])).unwrap());
        assert!(!unify(g, 3, &x, &Value::var(1)).unwrap());
        let stuck = |motive: Value| {
            Value::Neutral(
                Head::Var(0, Apart::NONE, ProofMark::Unknown),
                vec![Elim::J {
                    motive: Box::new(motive),
                    base: Box::new(ty()),
                    result: ProofMark::Unknown,
                    ends: None,
                }]
                .into(),
            )
        };
        assert!(unify(g, 1, &stuck(ty()), &stuck(ty())).unwrap());
        assert!(!unify(g, 1, &stuck(ty()), &stuck(Value::Sort(Sort::Prop))).unwrap());
    }

    #[test]
    fn solutions_can_contain_binders() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // ?m x0 = (y => x0), so ?m = a => y => a.
        let (m, lhs) = meta(g, &[0]);
        let rhs = eval(g, &[Value::var(0)], &lam(Term::Var(1))).unwrap();
        assert!(unify(g, 1, &lhs, &rhs).unwrap());
        let solution = g.meta_solution(m).expect("solved");
        let applied = apply_icit(
            g,
            apply_icit(g, solution, Value::var(5), Icit::Explicit).unwrap(),
            Value::var(9),
            Icit::Explicit,
        )
        .unwrap();
        assert!(is_var(g, &applied, 5));
        // ?n x0 = ((y : Type) -> x0), a function type mentioning the argument.
        let (n, lhs) = meta(g, &[0]);
        let rhs = eval(
            g,
            &[Value::var(0)],
            &pi(Icit::Explicit, sort(0), Term::Var(1)),
        )
        .unwrap();
        assert!(unify(g, 1, &lhs, &rhs).unwrap());
        assert!(g.meta_solution(n).is_some());
    }

    #[test]
    fn pruning_keeps_the_arguments_a_solution_may_mention() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // With x0, x1, x2 in scope: ?a x0 x2 = (?b x0 x1 x2 = Type). ?b can't
        // depend on x1, but it may depend on x0 and x2, in that order.
        let (_, lhs) = meta(g, &[0, 2]);
        let (b, b_applied) = meta(g, &[0, 1, 2]);
        assert!(unify(g, 3, &lhs, &eq(b_applied.clone(), ty())).unwrap());
        assert!(g.meta_solution(b).is_some());
        match force(g, b_applied).unwrap() {
            Value::Neutral(Head::Meta(_), spine) => {
                let kept: Vec<bool> = spine
                    .iter()
                    .map(|e| matches!(e, Elim::App(v, _) if is_var(g, v, 0)))
                    .collect();
                assert_eq!(spine.len(), 2, "x1 was pruned");
                assert_eq!(kept, vec![true, false], "x0 first, then x2");
                assert!(matches!(&spine[1], Elim::App(v, _) if is_var(g, v, 2)));
            }
            other => panic!("expected a new metavariable, got {other:?}"),
        }
    }

    #[test]
    fn zonk_works_under_binders() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, lhs) = meta(g, &[]);
        assert!(unify(g, 0, &lhs, &ty()).unwrap());
        // x => ?m, inside a case branch with two fields.
        let term = lam(Term::Meta(m));
        assert!(
            matches!(zonk(g, 0, &term), Ok(Term::Lam(_, _, ref body, _)) if matches!(**body, Term::Sort(_)))
        );
        // ?id x0 = x0, used inside a case branch with two fields.
        let (id, id_applied) = meta(g, &[0]);
        assert!(unify(g, 1, &id_applied, &Value::var(0)).unwrap());
        let branch = Term::Case(
            0,
            stitchwort_core::DataId(0),
            vec![stitchwort_core::term::Branch {
                names: vec!["a".into(), "b".into()],
                body: Some(Rc::new(Term::app(Term::Meta(id), Term::Var(0)))),
            }]
            .into(),
        );
        match zonk(g, 1, &branch) {
            Ok(Term::Case(_, _, ref branches)) => {
                assert!(
                    matches!(branches[0].body.as_deref(), Some(Term::Var(0))),
                    "{:?}",
                    branches[0].body
                );
            }
            other => panic!("expected a case, got {other:?}"),
        }
    }

    // Compact lists (docs/proposals/compact-text.md): unifying against one
    // solves metavariables exactly as unifying against its expansion does.

    use stitchwort_core::chars::{self, Chars, CompactText};

    /// A kernel with `List` and `Char` registered as data types 0 and 1. (No
    /// declarations: unification only compares constructors.)
    fn text_globals() -> (Fresh, CompactText) {
        let mut fresh = Fresh::default();
        let text = CompactText::new(stitchwort_core::DataId(0), stitchwort_core::DataId(1));
        fresh.g.env.set_text_unchecked_for_tests(text.clone());
        (fresh, text)
    }

    fn compact(text: &str) -> Value {
        Value::Chars(Chars::whole(text.chars().collect()))
    }

    /// The expansion, built from constructors.
    fn expanded(t: &CompactText, text: &str) -> Value {
        let mut list = Value::Ctor(t.list, 0, Vec::new().into());
        for c in text.chars().rev() {
            list = Value::Ctor(t.list, 1, [chars::char_value(t, c), list].into());
        }
        list
    }

    fn cons(t: &CompactText, head: Value, tail: Value) -> Value {
        Value::Ctor(t.list, 1, [head, tail].into())
    }

    fn mk_char(t: &CompactText, code: Value, proof: Value) -> Value {
        Value::Ctor(t.char, 0, [code, proof].into())
    }

    fn quoted(g: &Unifier<'_>, v: Value) -> String {
        format!("{:?}", quote_internal(g, 0, &v).unwrap())
    }

    #[test]
    fn cons_of_metavariables_against_a_compact_list() {
        for compact_side in [true, false] {
            let (fresh, t) = text_globals();
            let g = &fresh.unifier();
            let t = &t;
            let (c, c_value) = meta(g, &[]);
            let (tail, tail_value) = meta(g, &[]);
            let lhs = cons(t, c_value, tail_value);
            let rhs = if compact_side {
                compact("ab")
            } else {
                expanded(t, "ab")
            };
            assert!(unify(g, 0, &lhs, &rhs).unwrap());
            let c = g.meta_solution(c).unwrap();
            let tail = g.meta_solution(tail).unwrap();
            assert_eq!(quoted(g, c), quoted(g, chars::char_value(t, 'a')));
            if compact_side {
                // The rest of the same range.
                assert!(matches!(&tail, Value::Chars(r) if r.as_slice() == ['b']));
            }
            assert!(stitchwort_core::value::conv(g, 0, &tail, &expanded(t, "b")).unwrap());
            // Consistent: the solved left side is the right side.
            assert!(unify(g, 0, &lhs, &compact("ab")).unwrap());
            assert!(!unify(g, 0, &lhs, &compact("ac")).unwrap());
        }
    }

    #[test]
    fn a_metavariable_is_solved_with_the_compact_list_itself() {
        let (fresh, _) = text_globals();
        let g = &fresh.unifier();
        let (m, lhs) = meta(g, &[]);
        assert!(unify(g, 0, &lhs, &compact("abc")).unwrap());
        assert_eq!(
            format!("{:?}", zonk(g, 0, &Term::Meta(m)).unwrap()),
            r#"Chars(Chars("abc"))"#
        );
    }

    /// `Cons (MkChar ?n ?p) Nil ~ "a"`, with `?n` solved before, after, or
    /// differently.
    #[test]
    fn character_and_proof_metavariables_before_and_after_solving() {
        for (first, expect) in [(None, true), (Some(97u32), true), (Some(98), false)] {
            for compact_side in [true, false] {
                let (fresh, t) = text_globals();
                let g = &fresh.unifier();
                let t = &t;
                let (n, n_value) = meta(g, &[]);
                let (p, p_value) = meta(g, &[]);
                if let Some(code) = first {
                    let code = stitchwort_core::native::nat_value(code.into());
                    assert!(unify(g, 0, &n_value, &code).unwrap());
                }
                let nil = Value::Ctor(t.list, 0, Vec::new().into());
                let lhs = cons(t, mk_char(t, n_value.clone(), p_value), nil);
                let rhs = if compact_side {
                    compact("a")
                } else {
                    expanded(t, "a")
                };
                assert_eq!(unify(g, 0, &lhs, &rhs).unwrap(), expect, "{first:?}");
                if expect {
                    assert_eq!(quoted(g, g.meta_solution(n).unwrap()), "Nat(97)");
                    assert_eq!(quoted(g, g.meta_solution(p).unwrap()), "Refl");
                    // Afterwards, `?n` can't be anything else.
                    let other = stitchwort_core::native::nat_value(98u32.into());
                    assert!(!unify(g, 0, &n_value, &other).unwrap());
                }
            }
        }
    }

    /// A rigid proof variable stays distinct from `byComputing`, against the compact
    /// list as against its expansion.
    #[test]
    fn a_rigid_proof_is_not_rfl() {
        let (fresh, t) = text_globals();
        let g = &fresh.unifier();
        let t = &t;
        let code = stitchwort_core::native::nat_value(97u32.into());
        let nil = Value::Ctor(t.list, 0, Vec::new().into());
        let lhs = cons(t, mk_char(t, code, Value::var(0)), nil);
        assert!(!unify(g, 1, &lhs, &compact("a")).unwrap());
        assert!(!unify(g, 1, &lhs, &expanded(t, "a")).unwrap());
        assert!(!unify(g, 1, &compact("a"), &lhs).unwrap());
    }

    #[test]
    fn compact_lists_unify_by_their_characters() {
        let (fresh, t) = text_globals();
        let g = &fresh.unifier();
        let t = &t;
        let ab: Rc<[char]> = "xaby".chars().collect();
        let middle = Value::Chars(Chars::new(ab, 1, 3).unwrap());
        assert!(unify(g, 0, &middle, &compact("ab")).unwrap());
        assert!(unify(g, 0, &middle, &expanded(t, "ab")).unwrap());
        assert!(!unify(g, 0, &middle, &compact("abc")).unwrap());
        assert!(!unify(g, 0, &middle, &expanded(t, "a")).unwrap());
        // A cons cell in front of a compact tail.
        let mixed = cons(t, chars::char_value(t, 'a'), compact("b"));
        assert!(unify(g, 0, &mixed, &compact("ab")).unwrap());
        assert!(unify(g, 0, &compact("ab"), &mixed).unwrap());
        assert!(!unify(g, 0, &mixed, &compact("ba")).unwrap());
    }

    #[test]
    fn identical_functions_unify_without_solving_anything() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        // `x => ?m y x`, twice, with different values for the variable
        // the body doesn't use.
        let (m, _) = meta(g, &[]);
        let body = || {
            Rc::new(Term::App(
                Rc::new(Term::App(
                    Rc::new(Term::Meta(m)),
                    Rc::new(Term::Var(1)),
                    Icit::Explicit,
                )),
                Rc::new(Term::Var(0)),
                Icit::Explicit,
            ))
        };
        let lam = |unused: usize| {
            Value::Lam(
                "x".into(),
                Icit::Explicit,
                Closure {
                    env: vec![Value::var(unused), Value::var(3)].into(),
                    body: body(),
                },
                ProofMark::Unknown,
            )
        };
        let before = g.machine.budget.total_work();
        assert!(unify(g, 4, &lam(0), &lam(1)).unwrap());
        // The shortcut charges a step per pair of parts it compares
        // (`value::identical_within`), and runs neither body.
        assert_eq!(
            g.machine.budget.total_work() - before,
            8,
            "the shortcut's walk, nothing run"
        );
        assert!(g.meta_solution(m).is_none());
    }

    /// SW-919: `?p t Type = t ?g` isn't a pattern; matching the last
    /// arguments pairs `Type` (a type) with `?g`. If `?g` is known to be a
    /// function, they can't be equal and nothing is solved; if its type is
    /// unknown, or a sort, the last arguments are matched as before.
    #[test]
    fn matching_last_arguments_refuses_values_of_different_types() {
        let attempt = |g_ty: Option<Value>| {
            let fresh = Fresh::default();
            let g = &fresh.unifier();
            let (p, _) = meta(g, &[]);
            let (m, unknown) = meta(g, &[]);
            if let Some(t) = g_ty {
                g.store.set_meta_type(m, t, 0);
            }
            let left = Value::Neutral(
                Head::Meta(p),
                vec![
                    Elim::App(Value::var(0), Icit::Explicit),
                    Elim::App(ty(), Icit::Explicit),
                ]
                .into(),
            );
            // `t`, the variable at level 0, applied to `?g`.
            let right = Value::Neutral(
                Head::Var(0, Apart::NONE, ProofMark::Unknown),
                vec![Elim::App(unknown, Icit::Explicit)].into(),
            );
            let same = unify(g, 1, &left, &right).unwrap();
            (
                same,
                g.meta_solution(m).is_some(),
                g.meta_solution(p).is_some(),
            )
        };
        let function = Value::Pi(
            "x".into(),
            Icit::Explicit,
            Rc::new(ty()).into(),
            Closure {
                env: Vec::new().into(),
                body: Rc::new(Term::Sort(Sort::Type(0))),
            },
            ProofMark::Unknown,
        );
        assert_eq!(attempt(Some(function)), (false, false, false));
        assert_eq!(attempt(None), (true, true, true));
        assert_eq!(
            attempt(Some(Value::Sort(Sort::Type(1)))),
            (true, true, true)
        );
    }

    /// SW-924: `?m x Type = t ?m` isn't a pattern; matching the last
    /// arguments pairs `Type` with `?m` itself and solves it, so `?m x` would
    /// apply `Type` (a panic in core, found by search). They differ instead.
    #[test]
    fn matching_last_arguments_that_solves_the_head_with_a_non_function_fails() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (m, unknown) = meta(g, &[]);
        let left = Value::Neutral(
            Head::Meta(m),
            vec![
                Elim::App(Value::var(0), Icit::Explicit),
                Elim::App(ty(), Icit::Explicit),
            ]
            .into(),
        );
        let right = Value::Neutral(
            Head::Var(0, Apart::NONE, ProofMark::Unknown),
            vec![Elim::App(unknown, Icit::Explicit)].into(),
        );
        assert!(!unify(g, 1, &left, &right).unwrap());
    }

    fn pending_of(ms: &[usize]) -> HashSet<usize> {
        ms.iter().copied().collect()
    }

    /// Stage 6: a pair that fails only at a pending unknown (here a
    /// placeholder, frozen until filled) is set aside, and the rest of the
    /// comparison goes on and keeps what it solves: `?p = ?x` against
    /// `Type = Type` is `Blocked` on `?p`, with `?x` solved.
    #[test]
    fn a_pair_on_a_pending_unknown_waits_and_the_rest_is_solved() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (p, placeholder) = meta(g, &[]);
        let (x, unknown) = meta(g, &[]);
        g.store.mirrors.set(p, None, None);
        let a = eq(placeholder.clone(), unknown);
        let b = eq(ty(), ty());
        assert!(
            !unify(g, 0, &a, &b).unwrap(),
            "frozen: the boolean form fails"
        );
        let answer = unify_waiting(g, 0, &a, &b, &pending_of(&[p])).unwrap();
        let Answer::Blocked(pairs) = answer else {
            panic!("blocked")
        };
        assert_eq!(pairs.len(), 1);
        assert!(matches!(force(g, pairs[0].a.clone()).unwrap(),
            Value::Neutral(Head::Meta(m), _) if m == p));
        assert!(g.meta_solution(p).is_none(), "never solved by unification");
        assert!(g.meta_solution(x).is_some(), "the rest is solved");
    }

    /// Stage 6: only a pending unknown makes a pair wait. A rigid mismatch
    /// is `No` even with pending unknowns elsewhere, and a pair stuck on an
    /// ordinary unknown fails as it always has; with nothing pending the
    /// answer is the boolean form's.
    #[test]
    fn only_pending_unknowns_make_a_comparison_wait() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (p, placeholder) = meta(g, &[]);
        let (q, other) = meta(g, &[]);
        g.store.mirrors.set(p, None, None);
        g.store.mirrors.set(q, None, None);
        let pending = pending_of(&[p]);
        // Type 0 against Type 1: rigid.
        let rigid = unify_waiting(g, 0, &ty(), &Value::Sort(Sort::Type(1)), &pending).unwrap();
        assert!(matches!(rigid, Answer::No));
        // A frozen unknown the queue doesn't own (`q` not pending).
        let a = eq(other.clone(), ty());
        let b = eq(ty(), ty());
        assert!(matches!(
            unify_waiting(g, 0, &a, &b, &pending).unwrap(),
            Answer::No
        ));
        // With `p` pending, the same shape waits.
        let a = eq(placeholder, ty());
        assert!(matches!(
            unify_waiting(g, 0, &a, &b, &pending).unwrap(),
            Answer::Blocked(_)
        ));
        assert!(matches!(
            unify_waiting(g, 0, &ty(), &ty(), &pending).unwrap(),
            Answer::Yes
        ));
    }

    /// Stage 6: a comparison nested in a pair answers for itself, so it is
    /// the outer pair that waits: `unify` inside `unify_waiting` sets nothing
    /// aside, and leaves the waiting state as it found it.
    #[test]
    fn a_nested_comparison_answers_for_itself() {
        let fresh = Fresh::default();
        let g = &fresh.unifier();
        let (p, placeholder) = meta(g, &[]);
        g.store.mirrors.set(p, None, None);
        let waiting = Scoped::set(&g.attempt.waiting, Some(Vec::new()));
        let pending = Scoped::set(&g.attempt.pending, pending_of(&[p]));
        assert!(!unify(g, 0, &placeholder, &ty()).unwrap());
        drop(pending);
        assert_eq!(waiting.finish().map(|w| w.len()), Some(0));
    }

    /// The core loaded, and `two`, a `decreasing` definition whose call
    /// stays folded: `test` runs on a thread with room for it.
    fn with_core_and_two(test: impl FnOnce(&Elaborator, DefId) + Send + 'static) {
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                let mut sources = SourceMap::new();
                let file = sources.add("<prelude>", crate::prelude());
                let module = stitchwort_syntax::parse_module(file, crate::prelude())
                    .expect("the core parses");
                let mut e = Elaborator::new();
                e.unit.loading_prelude = true;
                let errors = |ds: Vec<stitchwort_syntax::Diagnostic>| {
                    ds.into_iter()
                        .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
                        .collect::<Vec<_>>()
                };
                assert!(
                    errors(e.elaborate_module(&module)).is_empty(),
                    "the core checks"
                );
                e.finish_core().expect("a complete core");
                e.unit.loading_prelude = false;
                let text = "import Std (Nat)\n\ndef two (x: Nat): Nat\n    decreasing x\n:=\n  match x with\n    \
                    | Zero => 2\n    | Succ m => two m [decreasing := Nat.leRefl (Succ m)]\n";
                let file = sources.add("two", text);
                let module = stitchwort_syntax::parse_module(file, text).expect("parses");
                let found = errors(e.elaborate_module(&module));
                assert!(found.is_empty(), "{found:#?}");
                let two = e.lookup_def("two").expect("two");
                test(&e, two);
            })
            .expect("a thread")
            .join()
            .expect("the test passes");
    }

    /// Rule E's record of sums with nothing to read is dropped once an
    /// unknown in one is solved, and again once that's undone (SW-2875).
    #[test]
    fn a_sum_is_read_again_once_its_unknown_is_solved() {
        with_core_and_two(|e, two| {
            let g = &e.unifier();
            let add = g.env.registry().def(Builtin::Add).expect("Nat.add");
            let (m, unknown) = meta(g, &[]);
            let inner = nat_add::call(add, Value::var(1), unknown);
            let sum = nat_add::call(add, Value::var(0), inner);
            // One outermost comparison's record, as `run` keeps it.
            let _memo = Scoped::set(&g.attempt.call_memo, Some(CallMemo::default()));
            assert!(reread_sum(g, &sum).unwrap().is_none());
            let trail = g.store.meta_trail.borrow().len();
            let call = Term::app(Term::Def(two), Term::Nat(Rc::new(BigUint::from(0u32))));
            let folded = stitchwort_core::value::eval(g, &[], &call).unwrap();
            assert!(matches!(&folded, Value::Neutral(Head::Def(f), _) if *f == two));
            g.store.solve_meta(m, folded);
            let read = reread_sum(g, &sum)
                .unwrap()
                .expect("read once `?m` is solved");
            let (k, base) = native::view(g, &read).unwrap();
            assert_eq!(k, BigUint::from(2u32));
            let expected = nat_add::call(add, Value::var(0), Value::var(1));
            assert!(stitchwort_core::value::conv(g, 2, &base.expect("x + y"), &expected).unwrap());
            undo_since(g, trail);
            assert!(reread_sum(g, &sum).unwrap().is_none());
        });
    }
}
