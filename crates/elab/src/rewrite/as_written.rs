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
//!
//! **When the checks run out** (stage 4, D2479). The completeness check, and
//! today's choice of instance for a rule with unknowns, read the goal back
//! unfolded, which can be too large to build (a call with a large literal,
//! `settle x 1000`, unfolds a thousand stuck `if`s) or use up the search
//! budget. Only when the usual search then fails the same way, so the
//! `rewrite` would end in `E-RESOURCE` (or `E-REWRITE-BUDGET`), is the
//! result as written used without the check that ran out
//! ([`unconfirmed`]), with `W-REWRITE-UNCONFIRMED` saying so. A rewrite
//! that checks today is never changed by this path.
//!
//! That is safe because nothing about soundness rests on the check: the
//! motive is type-checked here and the `J` it makes is checked by the kernel
//! like any other. What can go wrong is only that the result is not the one
//! today's search would have given if it could finish: a copy of the left
//! side left hidden inside a call, or a rule's unknowns solved at a
//! different instance. Either leaves a goal that a later step may fail to
//! prove, with that step's own error; neither can make a false goal check.

use stitchwort_core::{Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::RewriteRule;

use super::{
    Equation, Place, Replaced, Search, Shape, discharge, key, pending_metas, replace_occurrences,
    replace_occurrences_as,
};
use crate::check::{Ctx, Result};
use crate::lift::replace_with;
use crate::matching::same;
use crate::undo::{Snapshot, fatal, recoverable};

/// What [`first`] came to.
pub(super) enum First {
    Kept(Replaced),
    /// Found as written, but a check ran out of resources before it could
    /// say whether a copy is hidden: [`unconfirmed`] may use it if the usual
    /// search runs out too.
    RanOut,
    Not,
}

/// The rewrite as written, if it found something and left no hidden copy.
/// `goal` is the unforced goal (or type of the target).
pub(super) fn first(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    unfolded: (&Value, &Term),
    remaining: &mut u64,
) -> Result<First> {
    Ok(
        match attempt(
            cx,
            rule,
            place,
            equation,
            goal,
            Some(unfolded),
            remaining,
            Mode::Complete,
        )? {
            (Some(replaced), _) => First::Kept(replaced),
            (None, Outcome::RanOut) => First::RanOut,
            (None, _) => First::Not,
        },
    )
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
    attempt(
        cx,
        rule,
        place,
        equation,
        goal,
        None,
        remaining,
        Mode::Rescue,
    )
    .map(|(r, _)| r)
}

/// The rewrite as written, for when the usual search ran out of resources
/// (`E-RESOURCE` reading the goal back unfolded, or the search budget) and
/// would fail: the completeness check is made if it can be, and the result
/// is used unless it finds a hidden copy. `Some(true)` with it if the check
/// ran out, or the rule has unknowns whose instance today's search would
/// have chosen (it can't be asked): then the caller warns
/// ([`unconfirmed_warning`]). Why that is sound: the module's doc.
pub(super) fn unconfirmed(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    remaining: &mut u64,
) -> Result<Option<(Replaced, bool)>> {
    // As written: the unknowns are the call's arguments, and the left side
    // unfolded may be what is too large.
    let open = equation.open(&cx.quote_folded(&equation.lhs)?);
    let (kept, outcome) = attempt(
        cx,
        rule,
        place,
        equation,
        goal,
        None,
        remaining,
        Mode::Unconfirmed,
    )?;
    let ran_out = matches!(outcome, Outcome::Unconfirmed);
    Ok(kept.map(|replaced| (replaced, ran_out || open)))
}

/// `W-REWRITE-UNCONFIRMED`, for a rule used by [`unconfirmed`].
pub(super) fn unconfirmed_warning(
    rule: &RewriteRule,
    place: Place,
    cause: &Diagnostic,
) -> Diagnostic {
    let the = place.the();
    let why = match cause.code {
        "E-REWRITE-BUDGET" => {
            format!("the usual search, over what {the} computes to, ran out of its budget")
        }
        _ => format!(
            "{the} is too large once its calls are computed, so the usual search, over what it \
             computes to, couldn't run"
        ),
    };
    let warning = Diagnostic::warning(
        "W-REWRITE-UNCONFIRMED",
        "`rewrite` rewrote where the rule's left side is shown, without checking for copies of \
         it hidden inside calls",
    )
    .with_label(rule.span, "rewritten where it is shown")
    .with_note(why)
    .with_note(
        "a copy left inside a call (or an unknown of the rule solved differently) shows up as \
         an error in a later step; the proof itself is checked in full",
    );
    match cause.code {
        "E-REWRITE-BUDGET" => warning,
        _ => warning.with_note(
            "to let the full search run, make the large argument a variable: state a lemma for \
             any `n`",
        ),
    }
}

/// Whether `e` is a check running out: of resources ([`recoverable`]) or of
/// the `rewrite`'s search budget.
fn ran_out(cx: &Ctx, e: &Diagnostic) -> bool {
    e.code == "E-REWRITE-BUDGET" || recoverable(cx, e)
}

/// How much [`search`] checks.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// The completeness check, and today's instance for an open rule.
    Complete,
    /// Neither ([`rescue`]).
    Rescue,
    /// The completeness check if it can finish ([`unconfirmed`]).
    Unconfirmed,
}

/// What an attempt came to, counted under `STITCHWORT_REWRITE_METRICS`.
enum Outcome {
    Kept,
    /// Found, but a copy of the left side is hidden in a call.
    Incomplete,
    /// Found, but a check ran out of resources.
    RanOut,
    /// Kept by [`unconfirmed`] though a check ran out.
    Unconfirmed,
    /// Found nothing as written.
    Nothing,
    /// Something on the folded path failed.
    Failed,
    /// The motive has an unknown in it, so it could not be checked.
    Unchecked,
}

#[allow(clippy::too_many_arguments)]
fn attempt(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    unfolded: Option<(&Value, &Term)>,
    remaining: &mut u64,
    mode: Mode,
) -> Result<(Option<Replaced>, Outcome)> {
    let snapshot = Snapshot::take(cx);
    // A failed attempt costs the usual search nothing.
    let mut spare = *remaining;
    let tried = search(cx, rule, place, equation, goal, unfolded, mode, &mut spare);
    let (outcome, kept) = match tried {
        Ok((outcome @ (Outcome::Kept | Outcome::Unconfirmed), replaced)) => {
            *remaining = spare;
            (outcome, replaced)
        }
        Ok((outcome, _)) => {
            snapshot.restore(cx);
            (outcome, None)
        }
        Err(e) if mode == Mode::Complete && ran_out(cx, &e) => {
            snapshot.restore(cx);
            (Outcome::RanOut, None)
        }
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => {
            snapshot.restore(cx);
            (Outcome::Failed, None)
        }
    };
    if std::env::var_os("STITCHWORT_REWRITE_METRICS").is_some() {
        let name = match (&outcome, mode) {
            (Outcome::Kept, Mode::Rescue) => "rescued",
            (Outcome::Kept, _) => "folded",
            (Outcome::Unconfirmed, _) => "unconfirmed",
            (Outcome::RanOut, _) => "ran-out",
            (Outcome::Incomplete, _) => "incomplete",
            (Outcome::Nothing, _) => "nothing",
            (Outcome::Failed, _) => "failed",
            (Outcome::Unchecked, _) => "unchecked",
        };
        eprintln!("rewrite-as-written: {name} at={}", rule.proof.span().start);
    }
    Ok((kept, outcome))
}

#[allow(clippy::too_many_arguments)]
fn search(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    unfolded: Option<(&Value, &Term)>,
    mode: Mode,
    remaining: &mut u64,
) -> Result<(Outcome, Option<Replaced>)> {
    // Today's choice of instance, for a rule with unknowns, found before
    // anything is solved ([`todays_instance`]).
    let todays = match unfolded {
        Some((value, term))
            if mode == Mode::Complete && equation.open(&cx.quote(&equation.lhs)?) =>
        {
            todays_instance(cx, rule, place, equation, value, term, remaining)?
        }
        _ => None,
    };
    let mut written = cx.quote_folded(goal)?;
    // The `auto` proofs a call carries are not in the unfolded goal, where
    // `rewrite_once` proves the pending ones first; here they show, and a
    // motive holding one cannot be checked.
    let pending = pending_metas(&written);
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
    if let Some(todays) = &todays
        && !same(todays, &cx.quote(&equation.lhs)?)
    {
        return Ok((Outcome::Incomplete, None));
    }
    let mut outcome = Outcome::Kept;
    match mode {
        Mode::Complete => {
            if hidden_copy(cx, rule, place, equation, &step.motive, remaining)? {
                return Ok((Outcome::Incomplete, None));
            }
        }
        Mode::Rescue => {}
        Mode::Unconfirmed => {
            // The check is cut short by its own budget, so the rest stays
            // for the premises.
            let mut check = *remaining;
            match hidden_copy(cx, rule, place, equation, &step.motive, &mut check) {
                Ok(true) => return Ok((Outcome::Incomplete, None)),
                Ok(false) => *remaining = check,
                Err(e) if ran_out(cx, &e) => outcome = Outcome::Unconfirmed,
                Err(e) => return Err(e),
            }
        }
    }
    discharge(cx, rule, equation, 0, remaining)?;
    Ok((outcome, Some(replaced)))
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
    let search = Search::new(
        cx, rule, place, equation, lhs_term, key, 0, false, false, *remaining,
    )?;
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

/// The left side as today's search, over the unfolded goal, solves a rule's
/// unknowns: by the first occurrence in pre-order. `None` if it finds no
/// occurrence. Whatever it solves is undone.
///
/// The as-written search can pick a different instance (`comm _ _` finds
/// `add a b` where it is shown, but the unfolded goal has `add c (add a b)`
/// first), and the completeness check, which looks for further copies of
/// the instance already chosen, can't see that. A rewrite with a different
/// instance is not what the rule did before, so it is treated as incomplete.
fn todays_instance(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    term: &Term,
    remaining: &mut u64,
) -> Result<Option<Term>> {
    let snapshot = Snapshot::take(cx);
    let found = replace_occurrences(
        cx,
        rule,
        place,
        equation,
        goal,
        Shape::Whole(term),
        0,
        false,
        remaining,
    )
    .and_then(|replaced| {
        if replaced.step.is_some() {
            cx.quote(&equation.lhs).map(Some)
        } else {
            Ok(None)
        }
    });
    snapshot.restore(cx);
    found
}
