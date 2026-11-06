//! `rewrite` looks at the goal as written first (docs/proposals/goal-as-written.md,
//! stage 1).
//!
//! The usual search ([`super::replace_occurrences`]) reads the goal and the
//! rule's left side back unfolded, every call as what it computes to, so a
//! rule about `isSafe` is looked for as `List.all …` and the next goal has no
//! calls left in it. Here the same search runs over both read back folded
//! (calls as calls, [`Ctx::quote_folded`]), starting from the goal value as
//! it was bound, not forced: forcing unfolds an outer call. A candidate is
//! compared with the left side as usual, and also by the arguments of calls
//! of the same definition, which solves the rule's unknowns:
//! `rewrite isSafeCorrect _` finds `isSafe { levels = xs.reverse }`.
//!
//! The result is kept only if
//!
//! 1. nothing on this path failed: the folded motive is type-correct and
//!    computes back to the goal (a folded `x / d` carries its hidden proof
//!    `d ≠ 0`, which a motive abstracting `d` must abstract in the proof's
//!    type too, and which the unfolded goal never had), the premises are
//!    proved, and nothing ran out of resources; and
//! 2. no occurrence of the left side is left hidden ([`hidden_copy`]).
//!
//! Otherwise the caller does exactly what it did before. Lean's rule (rewrite
//! what is visible, leave hidden copies) was not taken: it breaks proofs that
//! rewrite a copy inside a definition (goal-as-written.md, option B).

use std::cell::{Cell, RefCell};

use stitchwort_core::{Term, Value};
use stitchwort_syntax::ast::RewriteRule;

use super::{
    Equation, Place, Replaced, Search, Shape, discharge, kernel_context, key,
    replace_occurrences_as,
};
use crate::check::{Ctx, Result};
use crate::lift::replace_with;
use crate::undo::{Snapshot, fatal};

/// The rewrite as written, if it found something and left no hidden copy.
/// `goal` is the unforced goal (or type of the target).
pub(super) fn first(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    remaining: &mut u64,
) -> Result<Option<Replaced>> {
    attempt(cx, rule, place, equation, goal, remaining, true)
}

/// The rewrite as written even if copies stay hidden, for when the usual
/// search found nothing at all.
pub(super) fn rescue(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    remaining: &mut u64,
) -> Result<Option<Replaced>> {
    attempt(cx, rule, place, equation, goal, remaining, false)
}

/// What an attempt came to, counted under `STITCHWORT_REWRITE_METRICS`.
enum Outcome {
    Kept,
    /// Found, but a copy of the left side is hidden in a call.
    Incomplete,
    /// Found nothing as written.
    Nothing,
    /// Something on the folded path failed.
    Failed,
    /// The motive has an unknown in it, so it could not be checked.
    Unchecked,
}

fn attempt(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    remaining: &mut u64,
    complete: bool,
) -> Result<Option<Replaced>> {
    let snapshot = Snapshot::take(cx);
    // A failed attempt costs the usual search nothing.
    let mut spare = *remaining;
    let tried = search(cx, rule, place, equation, goal, complete, &mut spare);
    let (outcome, kept) = match tried {
        Ok((Outcome::Kept, replaced)) => {
            *remaining = spare;
            (Outcome::Kept, replaced)
        }
        Ok((outcome, _)) => {
            snapshot.restore(cx);
            (outcome, None)
        }
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => {
            snapshot.restore(cx);
            (Outcome::Failed, None)
        }
    };
    if std::env::var_os("STITCHWORT_REWRITE_METRICS").is_some() {
        let name = match (&outcome, complete) {
            (Outcome::Kept, true) => "folded",
            (Outcome::Kept, false) => "rescued",
            (Outcome::Incomplete, _) => "incomplete",
            (Outcome::Nothing, _) => "nothing",
            (Outcome::Failed, _) => "failed",
            (Outcome::Unchecked, _) => "unchecked",
        };
        eprintln!("rewrite-as-written: {name} at={}", rule.proof.span().start);
    }
    Ok(kept)
}

fn search(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    complete: bool,
    remaining: &mut u64,
) -> Result<(Outcome, Option<Replaced>)> {
    let mut written = cx.quote_folded(goal)?;
    // The `auto` proofs a call carries are not in the unfolded goal, where
    // `rewrite_once` proves the pending ones first; here they show, and a
    // motive holding one cannot be checked.
    let pending: Vec<usize> = written
        .subterms()
        .filter_map(|(t, _)| {
            if let Term::Meta(m) = t {
                Some(*m)
            } else {
                None
            }
        })
        .collect();
    if !pending.is_empty() && cx.e.prove_now(&|m| pending.contains(&m))? {
        written = cx.quote_folded(goal)?;
    }
    let replaced = replace_occurrences_as(
        cx,
        rule,
        place,
        equation,
        goal,
        Shape::Whole(&written),
        0,
        false,
        true,
        remaining,
    )?;
    let Some(step) = &replaced.step else {
        return Ok((Outcome::Nothing, None));
    };
    // `check_motive` cannot check a motive with an unknown in it (the `J` is
    // checked whole once it is solved, after this choice is made), and a
    // folded motive can be ill-typed where the unfolded one is not: the
    // hidden proof of a division is `d ≠ 0`, not `x' ≠ 0`.
    if step
        .motive
        .subterms()
        .any(|(t, _)| matches!(t, Term::Meta(_)))
    {
        return Ok((Outcome::Unchecked, None));
    }
    if complete && hidden_copy(cx, rule, place, equation, &step.motive, remaining)? {
        return Ok((Outcome::Incomplete, None));
    }
    discharge(cx, rule, equation, 0, remaining)?;
    Ok((Outcome::Kept, Some(replaced)))
}

/// The completeness check: whether the left side still occurs in `motive`
/// (`x' _ => body`, the occurrences found as written replaced by `x'`) once
/// it is read back unfolded. One that does was inside a call the goal shows
/// as a call: replacing only the visible ones would leave the new goal with
/// a copy of the old left side, where today's search replaces all of them.
///
/// The occurrences are looked for as the usual search does, over the
/// unfolded term and the unfolded left side, so what counts as a copy is
/// exactly what that search would have replaced. Occurrences that mention
/// `x'` or a variable bound inside the goal are not candidates, here as
/// there. Whatever the check solves is undone.
fn hidden_copy(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    motive: &Term,
    remaining: &mut u64,
) -> Result<bool> {
    let snapshot = Snapshot::take(cx);
    let found = hidden_copy_in(cx, rule, place, equation, motive, remaining);
    snapshot.restore(cx);
    found
}

fn hidden_copy_in(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    motive: &Term,
    remaining: &mut u64,
) -> Result<bool> {
    let g = cx.g();
    let unfolded = cx.quote(&cx.eval(motive)?)?;
    let lhs_term = cx.quote(&equation.lhs)?;
    let Some(key) = key(&lhs_term, 0) else {
        // Nothing to compare by: don't trust the as-written result.
        return Ok(true);
    };
    let level = cx.level();
    let kcx = kernel_context(cx)?;
    let search = Search {
        kcx: RefCell::new(kcx),
        cx: RefCell::new(cx),
        rule,
        place,
        carrier: &equation.carrier,
        lhs: &equation.lhs,
        lhs_term: RefCell::new(lhs_term),
        key,
        recent: 0,
        by_instances: false,
        folded: false,
        rule_metas: equation.rule_metas,
        remaining: Cell::new(*remaining),
        stats: RefCell::new(Default::default()),
        error: RefCell::new(None),
        first: RefCell::new(None),
    };
    let moved = |l| Ok(Term::Var(level + 2 - 1 - l));
    let outcome = replace_with(&g, &unfolded, level, &moved, &|t, under| {
        search.visit(t, under)
    });
    *remaining = search.remaining.get();
    if let Some(e) = search.error.take() {
        return Err(e);
    }
    let matched = search.stats.take().matched;
    drop(search);
    outcome?;
    Ok(matched > 0)
}
