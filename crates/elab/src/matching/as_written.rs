//! A generalised `match` (and so `cases`) looks for its scrutinees in the
//! goal as written first (docs/proposals/goal-as-written.md, stage 2).
//!
//! The usual occurrence test ([`super::Generalise`]) reads the goal and the
//! variables' types back unfolded, every call as what it computes to, and
//! looks for the scrutinee's normal form syntactically. So the arms' goals
//! have no calls left in them, and a scrutinee written differently from the
//! goal (`xs.map (f a)` where the goal has `xs.map (y => f a y)`, AoC 2020
//! day 19) is not found at all. Here the same targets are read back folded
//! (calls as calls, [`Ctx::quote_folded`]) from the values as bound, and a
//! subterm is an occurrence if it has the scrutinee's head as written
//! ([`key`]) and is equal to it by computation, solving nothing
//! ([`Finder::occurrence`]). A scrutinee counts as found only where its
//! variable survives the generalised target's unfolding: one found inside
//! `keep 3 (isBig n)`, with `keep a b := a`, changes nothing the arms see.
//!
//! The result is kept only if it does what the usual test does, and more
//! only where that test missed an occurrence written differently:
//!
//! 1. **The copies.** Exactly the variables the usual test copies, plus one
//!    whose generalised type, unfolded, still holds a scrutinee's variable
//!    (an occurrence the usual test missed, which check 2 verifies), or
//!    whose unfolded type mentions such a copy. Never an extra `let`: its
//!    copy forgets the value (`let k: Ignore Nat (isBig n) := 5` would lose
//!    `k = 5` in the arms).
//! 2. **Completeness and the same instance.** Each generalised target (the
//!    goal, and the type of each variable copied here), read back unfolded,
//!    agrees with what the usual test makes of it ([`Finder::agree`]): the same
//!    term, except that where the usual result still has a subterm equal
//!    (by computation, solving nothing) to a scrutinee, this one may have
//!    the scrutinee's variable. So an occurrence hidden inside a call kept
//!    folded, which the usual test replaces and this one can't see, makes
//!    the two differ, and so does a call that computes on the scrutinee
//!    where the usual test found nothing to replace (`f s` with `s` a
//!    constructor: the usual goal has `f`'s result, this one would have `f
//!    x`, stuck). Nothing is open to choose: the scrutinees are known (the
//!    `match` waited for them, [`super::blocker`]), and a candidate that
//!    would solve an unknown to match is not an occurrence, so where both
//!    find something they find the same thing.
//!    A goal with no hit, where the usual test found no occurrence either,
//!    has the goal's normal form on both sides, so its pair is compared by
//!    conversion instead, without reading it back unfolded (SW-4637).
//! 3. The motive it makes is type-correct, checked now (the caller,
//!    [`super::generalised_now`]): a folded `x / d` carries its hidden
//!    proof `d ≠ 0`, which the unfolded goal doesn't have.
//! 4. Nothing on this path ran out of its budget or failed.
//!
//! Otherwise the caller does exactly what it did before. Check 2 is made
//! even when the usual test finds nothing anywhere (day 19's `match found:
//! xs.map (f a) |> .maximum`, where the goal has `y => f a y`): then every
//! occurrence found here must be one the usual test missed only because it
//! is written differently. A closed scrutinee that computes to a
//! constructor, `match h: isBig 20` against `pick (isBig 20) = 1`, has no
//! occurrence in the computed goal `1 = 1`, and abstracting the call as
//! written would give the arms `pick True = 1` and `pick False = 1`
//! instead of the goal unchanged: check 2 sees the difference (`pick x`,
//! stuck, against `1`), so the `match` refines nothing, as before.
//!
//! **When the usual test can't run** (stage 4, D2479). A goal or a
//! variable's type can be too large to read back unfolded (`solved:
//! start.settle plan 1000 |> … = Some answer` unfolds a thousand stuck
//! `if`s, AoC 2020 day 11), and the `match` then fails with `E-RESOURCE`.
//! Only there, [`unconfirmed`] runs this search without checks 1 and 2,
//! which need the usual test's result: the variables copied are those
//! whose types hold an occurrence as written (a `let` only where it is
//! still there unfolded), and an unfolding too large to build counts as
//! keeping the occurrence. Check 3 is made as always. The caller warns
//! (`W-MATCH-UNCONFIRMED`). It is safe because the motive is checked now
//! and by the kernel; what can go wrong is only a copy hidden inside a
//! call left unrefined, which makes an arm fail with its own error.
//!
//! Lean's rule (abstract what is visible, leave hidden copies) was not taken:
//! `std`'s `Result.traverseCons` and `List.foldMaxMember` rely on the copy a
//! `match` refines inside a definition (goal-as-written.md, option B; D2478).

use std::cell::RefCell;
use std::rc::Rc;
use stitchwort_core::ProofMark;

use stitchwort_core::{Ev, Icit, Term, Value};
use stitchwort_syntax::Diagnostic;

use super::{Generalise, Scrut, Skip, free_levels, is_var, same};
use crate::check::{Ctx, Result};
use crate::kernel;
use crate::lift::replace_with;
use crate::rewrite::{Key, kernel_context, key, mentions_bound, search_budget};
use crate::undo::{Snapshot, fatal, recoverable, recovered};

/// What the usual occurrence test made of the `match`, in its context.
pub(super) struct Today<'a> {
    /// Each scrutinee's normal form, `None` where it occurs nowhere.
    pub(super) occurrences: &'a [Option<&'a Term>],
    pub(super) copied: &'a [usize],
    /// The variables' types read back unfolded (`refl` for a skipped one).
    pub(super) type_terms: &'a [Term],
    /// The goal read back unfolded, or, unless `goal_exact`, with calls
    /// kept folded where no scrutinee can be hidden (`super::mixed_goal`):
    /// the same for the occurrence test, but not for check 2.
    pub(super) goal_term: &'a Term,
    pub(super) goal_exact: bool,
    /// Set where check 2 is reached without the goal read back unfolded:
    /// the caller reads it so and searches again.
    pub(super) needs_goal: &'a std::cell::Cell<bool>,
    /// The goal read back folded, when the usual test refines nothing in it
    /// ([`super::unrefined_goal`]).
    pub(super) goal_folded: Option<&'a Term>,
    /// The variables whose types the usual test left unread, since they
    /// can't hold a scrutinee ([`super::untouched`]): not read here either.
    pub(super) untouched: &'a [bool],
}

/// The generalisation as written: terms in the `match`'s context followed by
/// one variable per scrutinee (level `base + i` for scrutinee `i`), the
/// copies not yet substituted ([`moved`] does that).
pub(super) struct Written {
    pub(super) goal: Term,
    /// The variables to copy, in order, each with its generalised type.
    pub(super) copied: Vec<(usize, Term)>,
    /// Which scrutinees were found, in the goal or a copied variable's type.
    pub(super) found: Vec<bool>,
    /// [`Outcome::Kept`] or [`Outcome::Rescued`], for the count.
    pub(super) outcome: Outcome,
}

/// What an attempt came to, counted under `STITCHWORT_MATCH_METRICS`.
#[derive(Clone, Copy)]
pub(crate) enum Outcome {
    /// Agrees with the usual test (and perhaps found more).
    Kept,
    /// As [`Outcome::Kept`], found with the calls on the path to it
    /// unfolded ([`crate::unfold_path`]).
    Partial,
    /// The usual test found nothing anywhere; this did.
    Rescued,
    /// Found, but it disagrees with the usual test: a copy is hidden in a
    /// call, or a scrutinee's type mentions an extra copy.
    Incomplete,
    /// Found nothing as written.
    Nothing,
    /// Ran out of its budget, or something failed.
    Failed,
    /// The motive could not be checked now, or is ill-typed.
    Unchecked,
    /// Found, with the usual test unable to run ([`unconfirmed`]).
    Unconfirmed,
}

/// Prints `outcome` for the `match` at `span` when
/// `STITCHWORT_MATCH_METRICS` is set.
pub(super) fn report(outcome: Outcome, span: stitchwort_syntax::Span) {
    report_as("match-as-written", outcome, span);
}

/// Prints `outcome` for the guard whose condition is at `span`
/// ([`super::refined_guard`]) when `STITCHWORT_MATCH_METRICS` is set.
pub(super) fn report_guard(outcome: Outcome, span: stitchwort_syntax::Span) {
    report_as("guard-as-written", outcome, span);
}

/// Prints `outcome` for the transport along the equation of the `match`
/// whose scrutinee is at `span` ([`transport_target`]) when
/// `STITCHWORT_MATCH_METRICS` is set. [`Outcome::Unchecked`] is a target
/// found and agreeing whose transport didn't fit: the other side or the
/// kernel's check of the motive said no.
pub(crate) fn report_transport(outcome: Outcome, span: stitchwort_syntax::Span) {
    report_as("transport-as-written", outcome, span);
}

/// Prints that the `match` at `span` is made again without the partial
/// unfold ([`crate::unfold_path::retried`]) when `STITCHWORT_MATCH_METRICS`
/// is set.
pub(super) fn report_retried(span: stitchwort_syntax::Span) {
    crate::metrics::emit(
        "STITCHWORT_MATCH_METRICS",
        "match-retried: without-partial-unfold",
        span.start,
    );
}

/// Counts `outcome`, for a generalisation the caller kept, as a use of the
/// partial unfold if it is one, so that the `match` or `rewrite` around it
/// is retried without the step should it fail.
pub(crate) fn note_kept(outcome: Outcome) {
    if matches!(outcome, Outcome::Partial) {
        crate::unfold_path::note_kept();
    }
}

fn report_as(what: &str, outcome: Outcome, span: stitchwort_syntax::Span) {
    if !crate::metrics::wanted("STITCHWORT_MATCH_METRICS") {
        return;
    }
    let name = match outcome {
        Outcome::Kept => "folded",
        Outcome::Partial => "partial",
        Outcome::Rescued => "rescued",
        Outcome::Incomplete => "incomplete",
        Outcome::Nothing => "nothing",
        Outcome::Failed => "failed",
        Outcome::Unchecked => "unchecked",
        Outcome::Unconfirmed => "unconfirmed",
    };
    crate::metrics::emit(
        "STITCHWORT_MATCH_METRICS",
        &format!("{what}: {name}"),
        span.start,
    );
}

/// The generalisation as written, if it found something and passes checks
/// 1, 2 and 4 of the module's list (the caller makes check 3). Whatever it
/// solved or bound is undone either way: what it returns are terms.
#[allow(clippy::too_many_arguments)]
pub(super) fn first(
    cx: &mut Ctx,
    exprs: &[Scrut],
    today: &Today,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
    span: stitchwort_syntax::Span,
) -> Result<Option<Written>> {
    let mut outcome = Outcome::Failed;
    for &reading in readings() {
        let g = cx.g();
        let snapshot = Snapshot::take(cx);
        // Each attempt with its own budget: a failed one costs the next,
        // and the usual test, nothing.
        let mut remaining = search_budget(cx);
        let tried = g.machine.budget.limited(&mut remaining, || {
            search(cx, exprs, Some(today), goal, base, skip, reading)
        });
        snapshot.restore(cx);
        // Check 2 needs the goal read back unfolded: the caller reads it
        // and calls again, so this attempt counts for nothing.
        if today.needs_goal.get() {
            return Ok(None);
        }
        let now = match tried {
            Ok(Some(Ok(written))) => return Ok(Some(written)),
            Ok(Some(Err(outcome))) => outcome,
            // Over this attempt's own budget.
            Ok(None) => Outcome::Failed,
            // A check too large to make, where the usual test could run: its
            // result, as before stage 2.
            Err(e) if fatal(&e) && !recoverable(cx, &e) => return Err(e),
            Err(_) => {
                recovered(cx);
                Outcome::Failed
            }
        };
        match reading {
            Reading::Folded => outcome = now,
            // Counted as what the search as written came to.
            Reading::OnPath => {}
        }
        // Only an occurrence not shown, or one shown with a copy hidden,
        // can be on a path through calls.
        if !matches!(now, Outcome::Nothing | Outcome::Incomplete)
            || exprs.iter().any(|s| !s.on_path)
        {
            break;
        }
    }
    report(outcome, span);
    Ok(None)
}

/// The generalisation as written when the usual test couldn't run (the
/// module's "When the usual test can't run"): checks 1 and 2 aren't made.
/// Whatever it solved or bound is undone.
pub(super) fn unconfirmed(
    cx: &mut Ctx,
    exprs: &[Scrut],
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
    span: stitchwort_syntax::Span,
) -> Result<Option<Written>> {
    let g = cx.g();
    let snapshot = Snapshot::take(cx);
    let mut remaining = search_budget(cx);
    let tried = g.machine.budget.limited(&mut remaining, || {
        search(cx, exprs, None, goal, base, skip, Reading::Folded)
    });
    snapshot.restore(cx);
    let outcome = match tried {
        Ok(Some(Ok(written))) => return Ok(Some(written)),
        Ok(Some(Err(outcome))) => outcome,
        Ok(None) => Outcome::Failed,
        Err(e) if fatal(&e) && !recoverable(cx, &e) => return Err(e),
        Err(_) => {
            recovered(cx);
            Outcome::Failed
        }
    };
    report(outcome, span);
    Ok(None)
}

/// `W-MATCH-UNCONFIRMED`, for a `match` generalised by [`unconfirmed`],
/// whose (first) scrutinee is at `span`.
pub(super) fn unconfirmed_warning(span: stitchwort_syntax::Span) -> Diagnostic {
    Diagnostic::warning(
        "W-MATCH-UNCONFIRMED",
        "this `match` refined the goal and hypotheses as they are written, without checking \
         for copies of its expression hidden inside calls",
    )
    .with_label(
        span,
        "this is refined where the goal and hypotheses show it",
    )
    .with_note(
        "the goal or a hypothesis is too large once its calls are computed, so the usual \
         search, over what they compute to, couldn't run",
    )
    .with_note(
        "a copy left inside a call shows up as an error in an arm; the proof itself is \
         checked in full",
    )
    .with_note(
        "to let the full search run, make the large argument a variable: state a lemma for \
         any `n`",
    )
}

/// How [`search`] reads the goal and the variables' types.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reading {
    /// Back folded: calls as calls.
    Folded,
    /// Back folded, then with the calls on the path to a scrutinee hidden
    /// inside them unfolded ([`crate::unfold_path`]).
    OnPath,
}

/// The readings to try in turn: [`Reading::OnPath`] only while the partial
/// unfold is on ([`crate::unfold_path::enabled`]).
fn readings() -> &'static [Reading] {
    match crate::unfold_path::enabled() {
        true => &[Reading::Folded, Reading::OnPath],
        false => &[Reading::Folded],
    }
}

/// Checks 1, 2 and 4 against `today`, or (`None`, [`unconfirmed`]) only 4.
fn search<'e>(
    cx: &mut Ctx<'e>,
    exprs: &[Scrut],
    today: Option<&Today>,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
    reading: Reading,
) -> Result<std::result::Result<Written, Outcome>> {
    let g = cx.g();
    let e = exprs.len();
    let mut needles = Vec::new();
    for s in exprs {
        let value = cx.eval(&s.term)?;
        let written = cx.quote_folded(&value)?;
        let Some(key) = key(&written, 0) else {
            return Ok(Err(Outcome::Nothing));
        };
        needles.push(Needle {
            written,
            value,
            ty: s.ty.clone(),
            key,
        });
    }
    // From the values as bound, not forced: forcing unfolds an outer call.
    let mut goal_written = match today.and_then(|today| today.goal_folded) {
        Some(folded) => folded.clone(),
        None => cx.quote_folded(goal)?,
    };
    let untouched = |l: usize| today.is_some_and(|t| t.untouched.get(l).copied().unwrap_or(false));
    let mut types_written = (0..base)
        .map(
            |l| match skip.is_some_and(|skip| skip(cx, l)) || untouched(l) {
                true => Ok(None),
                false => cx.quote_folded(&cx.types[l]).map(Some),
            },
        )
        .collect::<Result<Vec<_>>>()?;
    if reading == Reading::OnPath {
        let keys: Vec<Key> = needles.iter().map(|n| n.key.clone()).collect();
        let level = cx.level();
        let relevant: Vec<usize> = needles
            .iter()
            .flat_map(|n| free_levels(&n.written, level))
            .collect();
        let kcx = RefCell::new(None);
        let oracle =
            |cx: &mut Ctx<'e>, t: &Term, under: usize| is_needle(cx, &kcx, &needles, t, under);
        let mut opened = false;
        if let Some(t) = crate::unfold_path::opened(cx, &goal_written, &keys, &relevant, &oracle)? {
            goal_written = t;
            opened = true;
        }
        for ty in types_written.iter_mut().flatten() {
            if let Some(t) = crate::unfold_path::opened(cx, ty, &keys, &relevant, &oracle)? {
                *ty = t;
                opened = true;
            }
        }
        // Nothing hidden on a path: the search as written has been made.
        if !opened {
            return Ok(Err(Outcome::Nothing));
        }
    }
    let is_let: Vec<bool> = (0..base).map(|l| cx.lets[l].is_some()).collect();
    let unrefined: Vec<bool> = (0..base)
        .map(|l| is_var(&cx.env[l], l) || is_let[l])
        .collect();
    let finder = Finder {
        cx: RefCell::new(cx),
        needles,
        base,
        depth: base + e,
        hits: RefCell::new(Vec::new()),
        error: RefCell::new(None),
        kcx: RefCell::new(None),
    };
    // Unfolded, or, without `today`, `Unfolded::TooLarge` where that is too
    // large to build.
    let unfold = |finder: &Finder, t: &Term| -> Result<Unfolded> {
        match finder.unfolded(t) {
            Ok(Some(t)) => Ok(Unfolded::Term(t)),
            Ok(None) => Ok(Unfolded::Misshapen),
            Err(e) if today.is_none() && recoverable(&finder.cx.borrow(), &e) => {
                recovered(&finder.cx.borrow());
                Ok(Unfolded::TooLarge)
            }
            Err(e) => Err(e),
        }
    };
    let hits_since = |finder: &Finder, before: usize| {
        let mut out = vec![false; e];
        for &i in &finder.hits.borrow()[before..] {
            out[i] = true;
        }
        out
    };
    let goal_generalised = finder.generalise(&g, &goal_written)?;
    // A scrutinee counts as found only where its variable survives
    // unfolding: one found inside a call that drops it (`keep 3 (isBig n)`,
    // with `keep a b := a`) replaces nothing the arms could see. A goal
    // with no hit has no scrutinee's variable to survive, and its unfolding
    // is wanted only for check 2, so it is built only if that is reached: a
    // goal that unfolds large, with the scrutinee only in a hypothesis or
    // nowhere, isn't read back unfolded a second time (SW-4600).
    let goal_hit = !finder.hits.borrow().is_empty();
    let (mut goal_unfolded, mut found) = match goal_hit {
        false => (None, vec![false; e]),
        true => match unfold(&finder, &goal_generalised)? {
            Unfolded::Term(t) => {
                let found = finder.survivors(&t);
                (Some(t), found)
            }
            Unfolded::Misshapen => return Ok(Err(Outcome::Incomplete)),
            Unfolded::TooLarge => (None, hits_since(&finder, 0)),
        },
    };
    // The variables to copy: exactly those the usual test copies, plus,
    // never a `let` (a copy forgets its value, SW-1628 review), one whose
    // type unfolded still holds a scrutinee's variable (an occurrence the
    // usual test missed, written differently, which check 2 verifies) or
    // whose unfolded type mentions such a copy, as the usual test's rule for
    // dependents reads it. A hit that vanishes on unfolding copies nothing.
    let mut copied: Vec<(usize, Term)> = Vec::new();
    let mut unfolded_types: Vec<Option<Term>> = Vec::new();
    for (l, ty) in types_written.iter().enumerate() {
        let Some(ty) = ty else { continue };
        if !unrefined[l] {
            continue;
        }
        let todays = today.is_some_and(|today| today.copied.contains(&l));
        let before = finder.hits.borrow().len();
        let generalised = finder.generalise(&g, ty)?;
        let hit = finder.hits.borrow().len() > before;
        // Without the usual test, by the type as written: its calls show
        // their arguments, where the unfolding's variables come from.
        let depends = free_levels(today.map_or(ty, |today| &today.type_terms[l]), base)
            .iter()
            .any(|f| copied.iter().any(|(c, _)| c == f));
        // Without the usual test a `let` is copied like any variable where
        // its type still holds a scrutinee unfolded (below), as the usual
        // test copies it.
        if !todays && ((is_let[l] && today.is_some()) || (!hit && !depends)) {
            continue;
        }
        let (unfolded, survivors) = match unfold(&finder, &generalised)? {
            Unfolded::Term(t) => {
                let survivors = finder.survivors(&t);
                (Some(t), survivors)
            }
            Unfolded::Misshapen => return Ok(Err(Outcome::Incomplete)),
            // Not known to survive: a `let` keeps its value, and anything
            // else is copied.
            Unfolded::TooLarge if is_let[l] => continue,
            Unfolded::TooLarge => (None, hits_since(&finder, before)),
        };
        if !todays && !depends && !survivors.iter().any(|&s| s) {
            continue;
        }
        for (f, s) in found.iter_mut().zip(survivors) {
            *f |= s;
        }
        copied.push((l, generalised));
        unfolded_types.push(unfolded);
    }
    if !found.iter().any(|&f| f) {
        return Ok(Err(Outcome::Nothing));
    }
    // As in the usual test: a scrutinee's type can't mention a copy (only
    // an extra copy can make it, so this disagrees with the usual test).
    if exprs.iter().any(|s| {
        free_levels(&s.ty_term, base)
            .iter()
            .any(|f| copied.iter().any(|(c, _)| c == f))
    }) {
        return Ok(Err(Outcome::Incomplete));
    }
    let Some(today) = today else {
        return Ok(Ok(Written {
            goal: goal_generalised,
            copied,
            found,
            outcome: Outcome::Unconfirmed,
        }));
    };
    // A goal with no hit, where the usual test found no occurrence either
    // (which a goal read with calls kept folded shows, `goal_exact` false):
    // both sides of its pair are then the goal's normal form, this one
    // computed from the goal read back folded. So its pair is checked by
    // conversion, which needn't read either back unfolded.
    let goal_converts = !goal_hit && !today.goal_exact && {
        let cx = finder.cx.borrow();
        stitchwort_core::value::conv(&g, base, &cx.eval(&goal_written)?, goal)?
    };
    if !today.goal_exact && !goal_converts {
        today.needs_goal.set(true);
        return Ok(Err(Outcome::Failed));
    }
    if !goal_hit && !goal_converts {
        goal_unfolded = match unfold(&finder, &goal_generalised)? {
            Unfolded::Term(t) => Some(t),
            Unfolded::Misshapen => return Ok(Err(Outcome::Incomplete)),
            Unfolded::TooLarge => None,
        };
    }
    let Some(unfolded_types) = unfolded_types.into_iter().collect::<Option<Vec<_>>>() else {
        unreachable!("only too large without the usual test")
    };
    let todays_found = !today.copied.is_empty()
        || (today.occurrences.iter().flatten()).any(|n| super::occurs(n, today.goal_term));
    // Check 2, on the goal and every copy's type.
    let todays = Generalise {
        base,
        depth: base + e,
        exprs: today.occurrences,
        copies: &Default::default(),
        transport: None,
    };
    let mut pairs = Vec::new();
    if !goal_converts {
        let Some(goal_unfolded) = goal_unfolded else {
            unreachable!("only too large without the usual test")
        };
        pairs.push((goal_unfolded, todays.apply(&g, today.goal_term)?));
    }
    for ((l, _), unfolded) in copied.iter().zip(unfolded_types) {
        pairs.push((unfolded, todays.apply(&g, &today.type_terms[*l])?));
    }
    for (unfolded, usual) in pairs {
        if !finder.agree(&g, &unfolded, &usual, 0)? {
            return Ok(Err(Outcome::Incomplete));
        }
    }
    Ok(Ok(Written {
        goal: goal_generalised,
        copied,
        found,
        outcome: match (todays_found, reading) {
            (true, Reading::Folded) => Outcome::Kept,
            (true, Reading::OnPath) => Outcome::Partial,
            (false, Reading::Folded) => Outcome::Rescued,
            // Where the usual test refines nothing, the arms keep the goal
            // as it is: a rescue through opened calls would replace an
            // occurrence written differently, and the arms' goals would no
            // longer be the ones the `match` gave before.
            (false, Reading::OnPath) => return Ok(Err(Outcome::Nothing)),
        },
    }))
}

/// Whether `t`, under `under` binders of a target in the `match`'s context,
/// is one of the scrutinees, by [`Finder::occurrence`]'s test, for
/// [`crate::unfold_path`].
fn is_needle<'e>(
    cx: &mut Ctx<'e>,
    kcx: &RefCell<Option<kernel::Ctx<'e>>>,
    needles: &[Needle],
    t: &Term,
    under: usize,
) -> Result<bool> {
    let Some(k) = key(t, under) else {
        return Ok(false);
    };
    let g = cx.g();
    let level = cx.level();
    let candidate = if under == 0 {
        t.clone()
    } else {
        replace_with(
            &g,
            t,
            level + under,
            &|l| Ok(Term::Var(level - 1 - l)),
            &|_, _| None,
        )?
    };
    for needle in needles.iter().filter(|n| n.key == k) {
        if is_occurrence(cx, kcx, needle, &candidate)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Whether `candidate`, a term in `cx`'s context, is `needle`: the same
/// term, or a term of the needle's type equal to it by computation
/// ([`Ctx::conv_now`], up to eta), which solves nothing, postpones nothing
/// and makes no unknown.
///
/// The type comes first: conversion compares values of one type only, and
/// a candidate is picked by its head alone, so a lambda can be offered for
/// a lambda of another type (`_ => False` for `x y => p x y`), where eta
/// would apply a constructor to an argument. `kcx` is the kernel's context
/// for `cx`, made the first time it is needed.
fn is_occurrence<'e>(
    cx: &Ctx<'e>,
    kcx: &RefCell<Option<kernel::Ctx<'e>>>,
    needle: &Needle,
    candidate: &Term,
) -> Result<bool> {
    if same(candidate, &needle.written) {
        return Ok(true);
    }
    let equal = (|| {
        if !has_type(cx, kcx, candidate, &needle.ty)? {
            return Ok(false);
        }
        let value = cx.eval(candidate)?;
        cx.conv_now(&value, &needle.value)
    })();
    match equal {
        Ok(equal) => Ok(equal),
        Err(e) if fatal(&e) => Err(e),
        Err(_) => Ok(false),
    }
}

/// Whether `term`, in `cx`'s context, has type `ty`, as the kernel finds:
/// its type inferred and compared with `ty`, or, for a term only checked
/// against a type (a function, a constructor), checked against `ty`.
/// `false` when that can't be told: an unknown in either, which the kernel
/// can't see.
fn has_type<'e>(
    cx: &Ctx<'e>,
    kcx: &RefCell<Option<kernel::Ctx<'e>>>,
    term: &Term,
    ty: &Value,
) -> Result<bool> {
    let g = cx.g();
    let mut slot = kcx.borrow_mut();
    let kcx = match &mut *slot {
        Some(kcx) => kcx,
        none => none.insert(kernel_context(cx)?),
    };
    match kernel::without_glue(&g, || kernel::infer(kcx, term)) {
        Ok((_, found)) => return cx.conv_now(&found, ty),
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => {}
    }
    let ty_term = cx.quote_folded(ty)?;
    let unknown = |t: &Term| t.subterms().any(|(t, _)| matches!(t, Term::Meta(_)));
    if unknown(term) || unknown(&ty_term) {
        return Ok(false);
    }
    let ty = cx.eval(&ty_term)?;
    match kernel::without_glue(&g, || kernel::check(kcx, term, &ty)) {
        Ok(_) => Ok(true),
        Err(e) if fatal(&e) => Err(e),
        Err(_) => Ok(false),
    }
}

/// A generalised target read back unfolded, in [`search`].
enum Unfolded {
    Term(Term),
    /// The read-back isn't the shape it should be.
    Misshapen,
    /// Too large to build (only looked past without the usual test).
    TooLarge,
}

/// SW-1562, goal-as-written.md stage 3: for the transport along a named
/// `match`'s equation `e = s` ([`Ctx::along_match_equation`]), `source` (a
/// type in the current context, one side of a mismatch) with every
/// occurrence of the scrutinee `e` (`lhs`, as the equation holds it, of type
/// `carrier`) replaced by a new variable after the context, found as
/// written: `source` and `e` read back folded, a candidate headed as `e` is
/// written, of `e`'s type and equal to it by computation, solving nothing
/// ([`Finder::occurrence`]). So a lemma's type that has `e` in another form
/// than the scrutinee's normal form (`xs.map (y => f a y)` for `xs.map (f
/// a)`), which the transport's syntactic test on normal forms misses, is
/// still rewritten.
///
/// `todays` is what the transport's own test makes of `source`: its normal
/// form with each syntactic occurrence of `e`'s normal form replaced by the
/// same variable (`todays_found` if there was one). The result is kept only
/// if it agrees with that, as stage 2's check 2 ([`Finder::agree`]): read
/// back unfolded, it is `todays` except that it may have the variable where
/// `todays` has a subterm equal to `e` (an occurrence written otherwise).
/// So everything the usual test replaces is replaced here too: an
/// occurrence hidden inside a call kept folded, which this can't see and
/// the usual test replaces, makes the two differ, and the caller then
/// transports as before. Nothing is replaced that isn't `e` by computation,
/// and since the usual test replaces every syntactic copy, the motive the
/// caller builds from this is the usual one up to computation and those
/// extra occurrences, with calls kept as calls.
///
/// Whatever the search solves or binds is undone, it runs within its own
/// budget, and every error but running out of resources overall is an
/// [`Outcome::Failed`]. Otherwise `Err` gives why nothing is kept, and the
/// caller makes the usual test.
pub(crate) fn transport_target(
    cx: &mut Ctx,
    lhs: &Value,
    carrier: &Value,
    source: &Value,
    todays: &Term,
    todays_found: bool,
) -> Result<std::result::Result<(Term, Outcome), Outcome>> {
    let mut outcome = Outcome::Failed;
    for &reading in readings() {
        let g = cx.g();
        let snapshot = Snapshot::take(cx);
        let mut remaining = search_budget(cx);
        let tried = g.machine.budget.limited(&mut remaining, || {
            transport_search(cx, lhs, carrier, source, todays, todays_found, reading)
        });
        snapshot.restore(cx);
        let now = match tried {
            Ok(Some(Ok(found))) => return Ok(Ok(found)),
            Ok(Some(Err(outcome))) => outcome,
            // Over this attempt's own budget.
            Ok(None) => Outcome::Failed,
            Err(e) if fatal(&e) => return Err(e),
            Err(_) => Outcome::Failed,
        };
        if reading == Reading::Folded {
            outcome = now;
        }
        if !matches!(now, Outcome::Nothing | Outcome::Incomplete) {
            break;
        }
    }
    Ok(Err(outcome))
}

fn transport_search<'e>(
    cx: &mut Ctx<'e>,
    lhs: &Value,
    carrier: &Value,
    source: &Value,
    todays: &Term,
    todays_found: bool,
    reading: Reading,
) -> Result<std::result::Result<(Term, Outcome), Outcome>> {
    let g = cx.g();
    let level = cx.level();
    let written = cx.quote_folded(lhs)?;
    let Some(key) = key(&written, 0) else {
        return Ok(Err(Outcome::Nothing));
    };
    let needles = vec![Needle {
        written,
        value: lhs.clone(),
        ty: carrier.clone(),
        key,
    }];
    let mut source_written = cx.quote_folded(source)?;
    if reading == Reading::OnPath {
        let relevant = free_levels(&needles[0].written, level);
        let kcx = RefCell::new(None);
        let oracle =
            |cx: &mut Ctx<'e>, t: &Term, under: usize| is_needle(cx, &kcx, &needles, t, under);
        let keys = [needles[0].key.clone()];
        match crate::unfold_path::opened(cx, &source_written, &keys, &relevant, &oracle)? {
            Some(t) => source_written = t,
            None => return Ok(Err(Outcome::Nothing)),
        }
    }
    let finder = Finder {
        cx: RefCell::new(cx),
        needles,
        base: level,
        depth: level + 1,
        hits: RefCell::new(Vec::new()),
        error: RefCell::new(None),
        kcx: RefCell::new(None),
    };
    let generalised = finder.generalise(&g, &source_written)?;
    if finder.hits.borrow().is_empty() {
        return Ok(Err(Outcome::Nothing));
    }
    let Some(unfolded) = finder.unfolded(&generalised)? else {
        return Ok(Err(Outcome::Incomplete));
    };
    // Found only inside a call that drops it: nothing to rewrite.
    if !finder.survivors(&unfolded)[0] {
        return Ok(Err(Outcome::Nothing));
    }
    if !finder.agree(&g, &unfolded, todays, 0)? {
        return Ok(Err(Outcome::Incomplete));
    }
    let outcome = match (todays_found, reading) {
        (true, Reading::Folded) => Outcome::Kept,
        (true, Reading::OnPath) => Outcome::Partial,
        (false, Reading::Folded) => Outcome::Rescued,
        // No rescue through opened calls, as in [`search`].
        (false, Reading::OnPath) => return Ok(Err(Outcome::Nothing)),
    };
    Ok(Ok((generalised, outcome)))
}

/// A scrutinee as the search looks for it.
struct Needle {
    /// Read back folded.
    written: Term,
    value: Value,
    /// The type of `value`, in the same context.
    ty: Value,
    key: Key,
}

/// The occurrence test as written, over terms in the `match`'s context
/// (`base` variables), giving terms with the scrutinees' variables after
/// them (`depth` = `base` + their number).
struct Finder<'c, 'e> {
    cx: RefCell<&'c mut Ctx<'e>>,
    needles: Vec<Needle>,
    base: usize,
    depth: usize,
    /// The scrutinees found, by index, in order.
    hits: RefCell<Vec<usize>>,
    error: RefCell<Option<stitchwort_syntax::Diagnostic>>,
    /// The kernel's context for `cx`, once made ([`is_occurrence`]).
    kcx: RefCell<Option<kernel::Ctx<'e>>>,
}

impl Finder<'_, '_> {
    /// `term` with every occurrence of a scrutinee replaced by its variable.
    fn generalise(&self, g: &Ev, term: &Term) -> Result<Term> {
        let depth = self.depth;
        let result = replace_with(
            g,
            term,
            self.base,
            &|l| Ok(Term::Var(depth - 1 - l)),
            &|t, under| self.visit(t, under),
        );
        if let Some(e) = self.error.take() {
            return Err(e);
        }
        result
    }

    fn visit(&self, t: &Term, under: usize) -> Option<Term> {
        if self.error.borrow().is_some() {
            return Some(t.clone());
        }
        let key = key(t, under)?;
        // A subterm mentioning a variable bound inside the target is not a
        // candidate, as in the usual test, where the scrutinee's free
        // variables never match a bound one.
        if mentions_bound(t, under) {
            return None;
        }
        for (i, needle) in self.needles.iter().enumerate() {
            if needle.key != key {
                continue;
            }
            match self.occurrence(i, t, under) {
                Ok(true) => {
                    self.hits.borrow_mut().push(i);
                    return Some(Term::Var(self.depth + under - 1 - (self.base + i)));
                }
                Ok(false) => {}
                Err(e) => {
                    *self.error.borrow_mut() = Some(e);
                    return Some(t.clone());
                }
            }
        }
        None
    }

    /// Whether `t`, under `under` binders of a target in the `match`'s
    /// context, is scrutinee `i` ([`is_occurrence`]). One that would need an
    /// unknown solved to match is not an occurrence: the usual test's
    /// syntactic comparison never solves anything, and a choice made by
    /// solving could differ from it.
    fn occurrence(&self, i: usize, t: &Term, under: usize) -> Result<bool> {
        let cx = self.cx.borrow();
        let g = cx.g();
        let level = cx.level();
        let candidate = if under == 0 {
            t.clone()
        } else {
            replace_with(
                &g,
                t,
                level + under,
                &|l| Ok(Term::Var(level - 1 - l)),
                &|_, _| None,
            )?
        };
        is_occurrence(&cx, &self.kcx, &self.needles[i], &candidate)
    }

    /// `written` (a generalised target, in `depth` variables) read back
    /// unfolded, in the same variables; `None` if the read-back isn't the
    /// shape it should be.
    fn unfolded(&self, written: &Term) -> Result<Option<Term>> {
        let e = self.depth - self.base;
        let cx = self.cx.borrow();
        // Under a binder per scrutinee, so that `eval` and `quote` see them
        // as variables.
        let mut lambdas = written.clone();
        for _ in 0..e {
            lambdas = Term::Lam(
                "s".into(),
                Icit::Explicit,
                Rc::new(lambdas),
                ProofMark::Unknown,
            );
        }
        let mut body = cx.quote_unfolded(&cx.eval(&lambdas)?)?;
        for _ in 0..e {
            let Term::Lam(_, _, inner, _) = &body else {
                return Ok(None);
            };
            body = inner.as_ref().clone();
        }
        Ok(Some(body))
    }

    /// Which scrutinees' variables occur in `unfolded` (in `depth`
    /// variables).
    fn survivors(&self, unfolded: &Term) -> Vec<bool> {
        let mut out = vec![false; self.depth - self.base];
        for level in free_levels(unfolded, self.depth) {
            if level >= self.base {
                out[level - self.base] = true;
            }
        }
        out
    }

    /// Check 2: whether `a` (a generalised target as written, read back
    /// unfolded by [`Finder::unfolded`]) agrees with `b` (the usual test's
    /// generalisation of the same target), both in `depth` variables, `a`
    /// and `b` being subterms under `under` binders of the target.
    ///
    /// Both are read back by the same rules from the same goal, so where
    /// they abstract the same subterms they are the same term. Where they
    /// differ, `a` may have a scrutinee's variable where `b` has a subterm
    /// that is that scrutinee written otherwise (an occurrence the
    /// syntactic test missed); any other difference fails.
    fn agree(&self, g: &Ev, a: &Term, b: &Term, under: usize) -> Result<bool> {
        if super::same(a, b) {
            return Ok(true);
        }
        let e = self.depth - self.base;
        let (a, b) = (a.strip_loc(), b.strip_loc());
        if let Term::Var(ix) = a
            && *ix >= under
            && *ix - under < e
        {
            // The variable of scrutinee `i`, where `b` must be scrutinee `i`
            // in a form the usual test didn't recognise, mentioning neither
            // a scrutinee's variable nor one bound inside the target.
            let i = e - 1 - (ix - under);
            let mentions_inner = b.subterms().any(|(t, binders)| match t {
                Term::Var(jx) | Term::Case(jx, ..) | Term::NumCase(jx, ..) => {
                    *jx >= binders && *jx - binders < under + e
                }
                _ => false,
            });
            if mentions_inner {
                return Ok(false);
            }
            // In the `match`'s context, from `under + e` binders deep.
            let depth = self.base + e + under;
            let base = self.base;
            let lowered =
                replace_with(g, b, depth, &|l| Ok(Term::Var(base - 1 - l)), &|_, _| None)?;
            return self.occurrence(i, &lowered, 0);
        }
        let all = |xs: &[Rc<Term>], ys: &[Rc<Term>], under| -> Result<bool> {
            if xs.len() != ys.len() {
                return Ok(false);
            }
            for (x, y) in xs.iter().zip(ys) {
                if !self.agree(g, x, y, under)? {
                    return Ok(false);
                }
            }
            Ok(true)
        };
        use Term::*;
        Ok(match (a, b) {
            (App(f1, a1, i), App(f2, a2, j)) => {
                i == j && self.agree(g, f1, f2, under)? && self.agree(g, a1, a2, under)?
            }
            (Lam(_, i, b1, _), Lam(_, j, b2, _)) => i == j && self.agree(g, b1, b2, under + 1)?,
            (Pi(_, i, a1, b1, _), Pi(_, j, a2, b2, _)) => {
                i == j && self.agree(g, a1, a2, under)? && self.agree(g, b1, b2, under + 1)?
            }
            (Data(d, xs), Data(e2, ys)) => d == e2 && all(xs, ys, under)?,
            (Ctor(d, c, xs), Ctor(e2, k, ys)) => d == e2 && c == k && all(xs, ys, under)?,
            (Eq(t1, a1, b1), Eq(t2, a2, b2)) => {
                let types = match (t1, t2) {
                    (Some(t1), Some(t2)) => self.agree(g, t1, t2, under)?,
                    (None, None) => true,
                    _ => false,
                };
                types && self.agree(g, a1, a2, under)? && self.agree(g, b1, b2, under)?
            }
            (Ann(e1, t1), Ann(e2, t2)) => {
                self.agree(g, e1, e2, under)? && self.agree(g, t1, t2, under)?
            }
            (Let(_, t1, v1, b1, _, _), Let(_, t2, v2, b2, _, _)) => {
                self.agree(g, t1, t2, under)?
                    && self.agree(g, v1, v2, under)?
                    && self.agree(g, b1, b2, under + 1)?
            }
            (J(m1, b1, p1, _), J(m2, b2, p2, _)) => {
                self.agree(g, m1, m2, under)?
                    && self.agree(g, b1, b2, under)?
                    && self.agree(g, p1, p2, under)?
            }
            (Quot(f1, xs, _, _), Quot(f2, ys, _, _)) => f1 == f2 && all(xs, ys, under)?,
            (Proj(d1, i1, t1), Proj(d2, i2, t2)) => {
                d1 == d2 && i1 == i2 && self.agree(g, t1, t2, under)?
            }
            _ => false,
        })
    }
}

/// `term`, from [`Written`] (in the `match`'s context and its scrutinees'
/// variables), in `depth` variables: each copied variable replaced by its
/// copy (`copies`, level to level).
pub(super) fn moved(
    g: &Ev,
    term: &Term,
    base: usize,
    scrutinees: usize,
    depth: usize,
    copies: &stitchwort_core::collections::HashMap<usize, usize>,
) -> Result<Term> {
    replace_with(
        g,
        term,
        base + scrutinees,
        &|l| {
            let new = match l < base {
                true => copies.get(&l).copied().unwrap_or(l),
                false => l,
            };
            Ok(Term::Var(depth - 1 - new))
        },
        &|_, _| None,
    )
}
