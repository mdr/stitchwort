//! Undoing a failed attempt (docs/proposals/syntax-conveniences.md §7.3).
//!
//! The unifier isn't atomic: a comparison that fails part-way keeps the
//! solutions it made before failing. So anything that tries one way and,
//! if it doesn't work, another, runs the first inside a transaction.
//!
//! The elaborator's inference state, all of it reachable from a [`Ctx`].
//! Most of it is in [`crate::state::Attempt`], metavariables included,
//! whose `mark` and `restore` name every field; the rest is listed in
//! [`Snapshot`]:
//! - the metavariables (the attempt's `MetaStore`): their solutions are
//!   undone from its trail, and those created since are dropped;
//! - lifted helpers not yet resolved (`lift.rs`), and the local
//!   definitions' keys met so far (`local.rs`);
//! - pending auto obligations and defaulted-literal records;
//! - the queued checks and the resumption log of their states
//!   (`queue.rs`): an attempt undone takes back both the checks it queued
//!   and the resumptions it made, with the terms they filled in;
//! - with code navigation on, the local variables' types noted for printing
//!   (`nav.rs`), which may mention the metavariables dropped;
//! - the open goals noted (`goals.rs`), the `_`s noted as proofs, and a
//!   probe's steps, for the same reason;
//! - the local context and the current span;
//! - the unifier's note of solutions made by comparing arguments
//!   (`Attempt::lossy`), cut with the trail. Its other state is set around
//!   a single comparison by guards, which an attempt is wholly inside or
//!   outside of, except `Attempt::rigid_divergence`, which an undone
//!   attempt keeps on purpose (see the field).
//!
//! Warnings mostly aren't part of it: declaration-level code adds most of
//! them (it needs `&mut Elaborator`, which a `Ctx` doesn't have), and those
//! found while checking (`W-LAMBDA-SHADOW` and the like) stay true of the
//! code whatever the attempt. The exception is `W-NO-EFFECT`, judged from
//! the types the attempt knew: one found in an attempt undone is dropped,
//! and found again if the code is checked again. Nor are resource
//! budgets: running out of resources is an error that stops elaboration,
//! passed on without undoing anything, and what was used isn't refunded.
//!
//! A rule for every caller (docs/proposals/postponement.md §5.7, T1): an
//! attempt site has a fixed, finite list of alternatives, and repeats one
//! only in a loop that runs again on progress (an obligation solved, a
//! comparison settled). Elaboration ends because the attempts form a
//! finite tree; the step budget is a resource limit on top of that, not
//! what makes it end. A site that retries without a bound needs its own
//! argument that it ends.

use stitchwort_core::{ResourceError, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Ctx;
use crate::check::{Mark, Result};
use crate::state::AttemptMark;

/// The inference state at some point, to return to with [`Snapshot::restore`]:
/// the [`Attempt`](crate::state::Attempt)'s mark, and what is still outside
/// it (the local types and goals noted for presentation, the local context
/// and span).
pub(crate) struct Snapshot {
    mark: Mark,
    span: Span,
    attempt: AttemptMark,
    local_types: usize,
    goals: usize,
    steps: usize,
}

impl Snapshot {
    pub(crate) fn take(cx: &Ctx) -> Snapshot {
        Snapshot {
            mark: cx.mark(),
            span: cx.span,
            attempt: cx.e.attempt.mark(),
            local_types: cx.e.pending_local_types(),
            goals: cx.e.pending_goals(),
            steps: cx.e.pending_steps(),
        }
    }

    /// How many metavariables there were: those numbered below were made
    /// before the snapshot.
    pub(crate) fn metas(&self) -> usize {
        self.attempt.metas()
    }

    /// How many number literals had been made `Nat` at once
    /// (`numbers::Defaulted`).
    pub(crate) fn defaulted(&self) -> usize {
        self.attempt.defaulted()
    }

    /// Whether local definitions or `match`es have been drafted for lifting
    /// (`lift.rs`) since the snapshot was taken.
    pub(crate) fn drafted_since(&self, cx: &Ctx) -> bool {
        cx.e.attempt.drafts.borrow().len() > self.attempt.drafts()
    }

    /// The metavariables solved (or re-solved) since the snapshot was taken.
    pub(crate) fn solved_since(&self, cx: &Ctx) -> Vec<usize> {
        cx.e.attempt.store.meta_trail.borrow()[self.attempt.trail()..]
            .iter()
            .map(|(m, _)| *m)
            .collect()
    }

    /// Undoes everything done since the snapshot was taken.
    pub(crate) fn restore(self, cx: &mut Ctx) {
        cx.e.attempt.restore(self.attempt);
        cx.e.drop_local_types_since(self.local_types);
        cx.e.drop_goals_since(self.goals);
        cx.e.drop_steps_since(self.steps);
        cx.reset(self.mark);
        cx.span = self.span;
    }
}

/// Whether `e` means elaboration must stop, rather than that this way
/// didn't work.
pub(crate) fn fatal(e: &Diagnostic) -> bool {
    e.code == "E-RESOURCE"
}

/// Whether `e` is running out of resources in a way the declaration can go
/// on from: a value too large to read back, with the operation itself not
/// out of steps, stack or time (those are sticky, [`Budget::exhausted`]).
///
/// [`Budget::exhausted`]: stitchwort_core::budget::Budget::exhausted
///
/// A caller that goes on from it calls [`recovered`].
pub(crate) fn recoverable(cx: &Ctx, e: &Diagnostic) -> bool {
    // By its message, as the module's report recognises it: a nesting error
    // is also not marked exhausted, but is not a value too large to show.
    fatal(e)
        && ResourceError::is_size_message(&e.message)
        && cx.g().machine.budget.exhausted().is_none()
}

/// After going on from a [`recoverable`] error: the definition it noted as
/// too large is forgotten, so a later report doesn't name it.
pub(crate) fn recovered(cx: &Ctx) {
    cx.g().machine.budget.take_too_large();
}

/// Runs `f`, undoing everything it did unless it gives `Ok(Some(_))`.
/// `Ok(None)` means this way didn't work, so another may be tried; other
/// errors are passed on, after undoing, except running out of resources,
/// which is passed on as it is.
pub(crate) fn transaction<T>(
    cx: &mut Ctx,
    f: impl FnOnce(&mut Ctx) -> Result<Option<T>>,
) -> Result<Option<T>> {
    let snapshot = Snapshot::take(cx);
    let result = f(cx);
    match &result {
        Ok(Some(_)) => {}
        Err(e) if fatal(e) => {}
        _ => snapshot.restore(cx),
    }
    result
}

/// Runs `f`, or if it fails (other than by running out of resources),
/// undoes what it did and gives `None`.
pub(crate) fn attempt<T>(cx: &mut Ctx, f: impl FnOnce(&mut Ctx) -> Result<T>) -> Result<Option<T>> {
    transaction(cx, |cx| match f(cx) {
        Ok(found) => Ok(Some(found)),
        Err(e) if fatal(&e) => Err(e),
        Err(_) => Ok(None),
    })
}

/// Whether `a` and `b` unify; if they don't, nothing is solved.
pub(crate) fn unify(cx: &mut Ctx, a: &Value, b: &Value) -> Result<bool> {
    Ok(transaction(cx, |cx| Ok(cx.unify(a, b)?.then_some(())))?.is_some())
}

/// [`crate::unify::unify_solving_arguments`], undoing what it solved if it fails.
pub(crate) fn unify_solving_arguments(cx: &mut Ctx, a: &Value, b: &Value) -> Result<bool> {
    Ok(transaction(cx, |cx| {
        Ok(crate::unify::unify_solving_arguments(&cx.u(), cx.level(), a, b)?.then_some(()))
    })?
    .is_some())
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use stitchwort_core::budget::Limits;
    use stitchwort_core::value::{Elim, Head};
    use stitchwort_core::{Icit, Sort};
    use stitchwort_syntax::SourceMap;

    use super::*;
    use crate::Elaborator;

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    fn ty(n: u32) -> Value {
        Value::Sort(Sort::Type(n))
    }

    /// `a = b`: a value with two parts, unified left to right.
    fn eq(a: Value, b: Value) -> Value {
        Value::Eq(Rc::new(ty(5)).into(), Rc::new(a).into(), Rc::new(b).into())
    }

    /// A fresh metavariable applied to the variables at `levels`.
    fn meta(cx: &Ctx, levels: &[usize]) -> (usize, Value) {
        let m = cx.metas().new_meta(span());
        let spine = levels
            .iter()
            .map(|l| Elim::App(Value::var(*l), Icit::Explicit))
            .collect();
        (m, Value::Neutral(Head::Meta(m), spine))
    }

    fn solved(cx: &Ctx, m: usize) -> bool {
        cx.g().meta_solution(m).is_some()
    }

    #[test]
    fn a_comparison_that_fails_part_way_solves_nothing() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        // `?a = Type1` against `Type0 = Type0`: `?a := Type0`, then `Type1`
        // against `Type0` fails.
        let (a, lhs) = meta(&cx, &[]);
        let (lhs, rhs) = (eq(lhs, ty(1)), eq(ty(0), ty(0)));
        // The unifier on its own keeps the first solution (why the
        // transaction exists)...
        let before = Snapshot::take(&cx);
        assert!(!cx.unify(&lhs, &rhs).unwrap());
        assert!(solved(&cx, a));
        before.restore(&mut cx);
        assert!(!solved(&cx, a));
        // ...and inside one, nothing survives.
        assert!(!unify(&mut cx, &lhs, &rhs).unwrap());
        assert!(!solved(&cx, a));
        assert_eq!(cx.metas().metas.borrow().len(), 1);
    }

    /// Test 16 (docs/proposals/proof-irrelevance.md §7.4): `MkT ?p 1`
    /// against `MkT q 2`, field 0 a proof, solves the whole proof `?p := q`
    /// and then fails at field 1. Bare unification keeps the solution; the
    /// transaction takes it back.
    #[test]
    fn a_proof_solved_before_a_failure_is_undone() {
        let mut e = Elaborator::new();
        let p = crate::unify::proof_fixture::build(&mut e.kernel);
        let mut cx = Ctx::new(&e, span());
        let n = |k: usize| {
            (0..k).fold(Value::Ctor(p.n, 0, Vec::new().into()), |v, _| {
                Value::Ctor(p.n, 1, [v].into())
            })
        };
        let proof = Value::Ctor(p.q, 0, [n(0)].into());
        let (m, m_value) = meta(&cx, &[]);
        let mk_t = |h: Value, k: usize| Value::Ctor(p.t, 0, [h, n(k)].into());
        let (lhs, rhs) = (mk_t(m_value, 1), mk_t(proof.clone(), 2));
        let before = Snapshot::take(&cx);
        assert!(!cx.unify(&lhs, &rhs).unwrap());
        assert!(solved(&cx, m));
        before.restore(&mut cx);
        assert!(!unify(&mut cx, &lhs, &rhs).unwrap());
        assert!(!solved(&cx, m));
        // Paired: with the data fields equal, `?p := q`.
        assert!(unify(&mut cx, &lhs, &mk_t(proof, 1)).unwrap());
        assert!(solved(&cx, m));
    }

    #[test]
    fn metavariables_made_by_pruning_are_dropped() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        cx.bind_hidden("x".into(), ty(0));
        // `?a = Type1` against `(?b x0 = Type0) = Type0`, with `?a` unable to
        // depend on `x0`: pruning makes a new `?c` with `?b := _ => ?c`,
        // then `Type1` against `Type0` fails.
        let (a, a_value) = meta(&cx, &[]);
        let (b, b_applied) = meta(&cx, &[0]);
        let lhs = eq(a_value, ty(1));
        let rhs = eq(eq(b_applied, ty(0)), ty(0));
        let metas = cx.metas().metas.borrow().len();
        let trail = cx.metas().meta_trail.borrow().len();
        assert!(!unify(&mut cx, &lhs, &rhs).unwrap());
        assert!(!solved(&cx, a));
        assert!(!solved(&cx, b));
        assert_eq!(cx.metas().metas.borrow().len(), metas);
        assert_eq!(cx.metas().meta_trail.borrow().len(), trail);
        // The same comparison outside a transaction does prune.
        assert!(!cx.unify(&lhs, &rhs).unwrap());
        assert!(cx.metas().metas.borrow().len() > metas);
    }

    #[test]
    fn obligations_and_context_are_restored_but_work_is_not_refunded() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let _op = cx.g().machine.budget.operation(Limits::default());
        let level = cx.level();
        let work = cx.g().machine.budget.total_work();
        // The work done inside, whatever implicit_arg itself spends.
        let spent = std::cell::Cell::new(0);
        let found: Option<()> = transaction(&mut cx, |cx| {
            cx.bind("y", ty(0));
            crate::check::implicit_arg(cx, Icit::Auto, &ty(0));
            assert_eq!(cx.e.attempt.obligations.borrow().len(), 1);
            cx.g().machine.budget.step().unwrap();
            spent.set(cx.g().machine.budget.total_work());
            Ok(None)
        })
        .unwrap();
        assert!(found.is_none());
        assert_eq!(cx.level(), level);
        assert!(cx.lookup("y").is_none());
        assert!(cx.e.attempt.obligations.borrow().is_empty());
        assert!(cx.metas().metas.borrow().is_empty());
        assert!(spent.get() > work);
        assert_eq!(cx.g().machine.budget.total_work(), spent.get());
    }

    #[test]
    fn a_rigid_divergence_met_in_an_undone_attempt_still_counts() {
        // Deliberately sticky (SW-1147, `Attempt::rigid_divergence`): it only
        // asks `Elaborator::group` to check a failed body once more with the
        // signature's divergence total, so a meeting in an attempt that was
        // undone can cost a second check but never changes the answer.
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let found: Option<()> = transaction(&mut cx, |cx| {
            cx.e.attempt.note_rigid_divergence();
            Ok(None)
        })
        .unwrap();
        assert!(found.is_none());
        assert!(cx.e.attempt.take_rigid_divergence());
        // Taking it clears it, as `group` does before each body.
        assert!(!cx.e.attempt.take_rigid_divergence());
    }

    #[test]
    fn running_out_of_resources_is_passed_on_without_undoing() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let limits = Limits {
            work: 3,
            ..Limits::default()
        };
        let _op = cx.g().machine.budget.operation(limits);
        let (a, _) = meta(&cx, &[]);
        let result: Result<Option<()>> = transaction(&mut cx, |cx| {
            cx.metas().solve_meta(a, ty(0));
            loop {
                cx.g().machine.budget.step()?;
            }
        });
        assert_eq!(result.unwrap_err().code, "E-RESOURCE");
        assert!(solved(&cx, a), "nothing is undone");
        // Any other error means this way didn't work: undone.
        let (b, _) = meta(&cx, &[]);
        let found = attempt(&mut cx, |cx| -> Result<()> {
            cx.metas().solve_meta(b, ty(0));
            Err(Diagnostic::error("E-TYPE-MISMATCH", "no"))
        })
        .unwrap();
        assert!(found.is_none());
        assert!(!solved(&cx, b));
    }

    /// G2: a metavariable frozen inside an attempt is thawed when the
    /// attempt is undone, even an older one.
    #[test]
    fn an_undone_attempt_thaws_what_it_froze() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let (older, _) = meta(&cx, &[]);
        let before = Snapshot::take(&cx);
        let (newer, _) = meta(&cx, &[]);
        cx.metas().freeze_meta(older);
        cx.metas().freeze_meta(newer);
        before.restore(&mut cx);
        assert!(!cx.metas().meta_frozen(older));
        assert!(cx.metas().frozen_metas.borrow().is_empty());
    }
}
