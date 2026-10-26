//! Undoing a failed attempt (docs/proposals/syntax-conveniences.md §7.3).
//!
//! The unifier isn't atomic: a comparison that fails part-way keeps the
//! solutions it made before failing. So anything that tries one way and,
//! if it doesn't work, another, runs the first inside a transaction.
//!
//! The elaborator's inference state, all of it reachable from a [`Ctx`]:
//! - the metavariables (`Globals::metas`): their solutions are undone from
//!   `Globals::meta_trail`, and those created since are dropped;
//! - lifted helpers not yet resolved (`lift.rs`), and the local
//!   definitions' keys met so far (`local.rs`);
//! - pending auto obligations and defaulted-literal records (`Elaborator`);
//! - with code navigation on, the local variables' types noted for printing
//!   (`nav.rs`), which may mention the metavariables dropped;
//! - the open goals noted (`goals.rs`), and the `_`s noted as proofs, for
//!   the same reason;
//! - the local context and the current span.
//!
//! Warnings aren't part of it: only declaration-level code adds them (it
//! needs `&mut Elaborator`, which a `Ctx` doesn't have). Nor are resource
//! budgets: running out of resources is an error that stops elaboration,
//! passed on without undoing anything, and what was used isn't refunded.

use stitchwort_core::Value;
use stitchwort_syntax::{Diagnostic, Span};

use crate::Ctx;
use crate::check::{Mark, Result};

/// The inference state at some point, to return to with [`Snapshot::restore`].
pub(crate) struct Snapshot {
    mark: Mark,
    span: Span,
    metas: usize,
    trail: usize,
    obligations: usize,
    row_metas: usize,
    row_constraints: usize,
    defaulted: usize,
    drafts: usize,
    local_keys: usize,
    local_types: usize,
    goals: usize,
}

impl Snapshot {
    pub(crate) fn take(cx: &Ctx) -> Snapshot {
        let g = cx.g();
        Snapshot {
            mark: cx.mark(),
            span: cx.span,
            metas: g.metas.borrow().len(),
            trail: g.meta_trail.borrow().len(),
            obligations: cx.e.obligations.borrow().len(),
            row_metas: cx.e.row_metas.borrow().len(),
            row_constraints: cx.e.row_constraints.borrow().len(),
            defaulted: cx.e.defaulted.borrow().len(),
            drafts: cx.e.drafts.borrow().len(),
            local_keys: cx.e.local_keys.borrow().len(),
            local_types: cx.e.pending_local_types(),
            goals: cx.e.pending_goals(),
        }
    }

    /// Whether local definitions or `match`es have been drafted for lifting
    /// (`lift.rs`) since the snapshot was taken.
    pub(crate) fn drafted_since(&self, cx: &Ctx) -> bool {
        cx.e.drafts.borrow().len() > self.drafts
    }

    /// The metavariables solved (or re-solved) since the snapshot was taken.
    pub(crate) fn solved_since(&self, cx: &Ctx) -> Vec<usize> {
        cx.g().meta_trail.borrow()[self.trail..]
            .iter()
            .map(|(m, _)| *m)
            .collect()
    }

    /// Undoes everything done since the snapshot was taken.
    pub(crate) fn restore(self, cx: &mut Ctx) {
        let g = cx.g();
        {
            let mut metas = g.metas.borrow_mut();
            let mut trail = g.meta_trail.borrow_mut();
            // A call's kept unfolding may have used what's taken back here
            // (or a metavariable whose number is about to be reused).
            if trail.len() > self.trail || metas.len() > self.metas {
                g.metas_taken_back();
            }
            while trail.len() > self.trail {
                let (m, old) = trail.pop().expect("longer than the snapshot's");
                if let Some(meta) = metas.get_mut(m) {
                    meta.solution = old;
                }
            }
            metas.truncate(self.metas);
            g.frozen_metas.borrow_mut().retain(|m| *m < self.metas);
            g.lifted_calls.borrow_mut().retain(|m, _| *m < self.metas);
            g.print_labels
                .borrow_mut()
                .retain(|l| !matches!(l.head, stitchwort_core::Term::Meta(m) if m >= self.metas));
            cx.e.local_metas.borrow_mut().retain(|m, _| *m < self.metas);
            cx.e.local_defaults
                .borrow_mut()
                .retain(|h, _| h.before(self.metas));
            cx.e.proof_holes.borrow_mut().retain(|m| *m < self.metas);
        }
        cx.e.obligations.borrow_mut().truncate(self.obligations);
        cx.e.row_metas.borrow_mut().truncate(self.row_metas);
        cx.e.row_constraints
            .borrow_mut()
            .truncate(self.row_constraints);
        cx.e.defaulted.borrow_mut().truncate(self.defaulted);
        cx.e.drafts.borrow_mut().truncate(self.drafts);
        cx.e.local_keys.borrow_mut().truncate(self.local_keys);
        cx.e.drop_local_types_since(self.local_types);
        cx.e.drop_goals_since(self.goals);
        cx.reset(self.mark);
        cx.span = self.span;
    }
}

/// Whether `e` means elaboration must stop, rather than that this way
/// didn't work.
pub(crate) fn fatal(e: &Diagnostic) -> bool {
    e.code == "E-RESOURCE"
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
        Value::Eq(Rc::new(ty(5)), Rc::new(a), Rc::new(b))
    }

    /// A fresh metavariable applied to the variables at `levels`.
    fn meta(cx: &Ctx, levels: &[usize]) -> (usize, Value) {
        let m = cx.g().new_meta(span());
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
        assert_eq!(cx.g().metas.borrow().len(), 1);
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
        let metas = cx.g().metas.borrow().len();
        let trail = cx.g().meta_trail.borrow().len();
        assert!(!unify(&mut cx, &lhs, &rhs).unwrap());
        assert!(!solved(&cx, a));
        assert!(!solved(&cx, b));
        assert_eq!(cx.g().metas.borrow().len(), metas);
        assert_eq!(cx.g().meta_trail.borrow().len(), trail);
        // The same comparison outside a transaction does prune.
        assert!(!cx.unify(&lhs, &rhs).unwrap());
        assert!(cx.g().metas.borrow().len() > metas);
    }

    #[test]
    fn obligations_and_context_are_restored_but_work_is_not_refunded() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let _op = cx.g().budget.operation(Limits::default());
        let level = cx.level();
        let work = cx.g().budget.total_work();
        // The work done inside, whatever implicit_arg itself spends.
        let spent = std::cell::Cell::new(0);
        let found: Option<()> = transaction(&mut cx, |cx| {
            cx.bind("y", ty(0));
            crate::check::implicit_arg(cx, Icit::Auto, &ty(0));
            assert_eq!(cx.e.obligations.borrow().len(), 1);
            cx.g().budget.step().unwrap();
            spent.set(cx.g().budget.total_work());
            Ok(None)
        })
        .unwrap();
        assert!(found.is_none());
        assert_eq!(cx.level(), level);
        assert!(cx.lookup("y").is_none());
        assert!(cx.e.obligations.borrow().is_empty());
        assert!(cx.g().metas.borrow().is_empty());
        assert!(spent.get() > work);
        assert_eq!(cx.g().budget.total_work(), spent.get());
    }

    #[test]
    fn running_out_of_resources_is_passed_on_without_undoing() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let limits = Limits {
            work: 3,
            ..Limits::default()
        };
        let _op = cx.g().budget.operation(limits);
        let (a, _) = meta(&cx, &[]);
        let result: Result<Option<()>> = transaction(&mut cx, |cx| {
            cx.g().solve_meta(a, ty(0));
            loop {
                cx.g().budget.step()?;
            }
        });
        assert_eq!(result.unwrap_err().code, "E-RESOURCE");
        assert!(solved(&cx, a), "nothing is undone");
        // Any other error means this way didn't work: undone.
        let (b, _) = meta(&cx, &[]);
        let found = attempt(&mut cx, |cx| -> Result<()> {
            cx.g().solve_meta(b, ty(0));
            Err(Diagnostic::error("E-TYPE-MISMATCH", "no"))
        })
        .unwrap();
        assert!(found.is_none());
        assert!(!solved(&cx, b));
    }
}
