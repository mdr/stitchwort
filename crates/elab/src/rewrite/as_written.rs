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

use stitchwort_core::value::{Head, conv, eval, quote_at_most};
use stitchwort_core::{Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::RewriteRule;

use super::{
    Equation, Place, Reading, Replaced, Search, Shape, discharge, elaborate_rule, key,
    pending_metas, replace_occurrences, replace_occurrences_as,
};
use crate::check::{Ctx, Result};
use crate::lift::replace_with;
use crate::matching::same;
use crate::undo::{Snapshot, fatal, recoverable, recovered};

/// What [`first`] came to.
pub(super) enum First {
    Kept(Box<Replaced>),
    /// Found as written, but a check ran out of resources before it could
    /// say whether a copy is hidden: [`unconfirmed`] may use it if the usual
    /// search runs out too.
    RanOut,
    Not,
}

/// The rewrite as written, if it found something and left no hidden copy;
/// failing that, with `on_path`, the same with the calls on the path to an
/// occurrence hidden inside them unfolded ([`crate::unfold_path`]). `goal`
/// is the unforced goal (or type of the target), and `unfolded` the goal
/// forced and read back unfolded, which only a rule with unknowns needs
/// (to find today's instance). `rewrite repeatedly`'s
/// cheap pass, over the goal as written only, passes `on_path` false: there
/// a set's rules are only ever looked for, and opening calls would let them
/// fire where they didn't, and in a different order.
#[allow(clippy::too_many_arguments)]
pub(super) fn first(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    unfolded: Option<(&Value, &Term)>,
    remaining: &mut u64,
    on_path: bool,
) -> Result<First> {
    let (found, outcome) = attempt(
        cx,
        rule,
        place,
        equation,
        goal,
        unfolded,
        remaining,
        Mode::Complete,
        Reading::Folded,
        false,
    )?;
    if let Some(replaced) = found {
        report(&outcome, Mode::Complete, Reading::Folded, rule);
        return Ok(First::Kept(Box::new(replaced)));
    }
    // Not shown, or shown with a copy hidden: perhaps on a path through
    // calls, which the middle step unfolds ([`crate::unfold_path`]).
    if on_path
        && crate::unfold_path::enabled()
        && matches!(outcome, Outcome::Nothing | Outcome::Incomplete)
    {
        let (found, _) = attempt(
            cx,
            rule,
            place,
            equation,
            goal,
            unfolded,
            remaining,
            Mode::Complete,
            Reading::Folded,
            true,
        )?;
        if let Some(replaced) = found {
            crate::unfold_path::note_kept();
            report(&Outcome::Partial, Mode::Complete, Reading::Folded, rule);
            return Ok(First::Kept(Box::new(replaced)));
        }
    }
    report(&outcome, Mode::Complete, Reading::Folded, rule);
    Ok(match outcome {
        Outcome::RanOut => First::RanOut,
        _ => First::Not,
    })
}

/// The rewrite as written even if copies stay hidden, for when the usual
/// search found nothing at all: over the goal read back folded, and then,
/// if that finds nothing either, with every call kept as the goal is
/// printed (SW-3529). A call that computes at once, because an argument is
/// known (`printer.write indent " " 1`, whose `if` on `" "` decides), is
/// read back folded as what it steps to, so only the second reading finds
/// a rule about the call.
pub(super) fn rescue(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    remaining: &mut u64,
) -> Result<Option<Replaced>> {
    for reading in [Reading::Folded, Reading::AsWritten] {
        let (found, _) = attempt(
            cx,
            rule,
            place,
            equation,
            goal,
            None,
            remaining,
            Mode::Rescue,
            reading,
            false,
        )?;
        if found.is_some() {
            return Ok(found);
        }
    }
    Ok(None)
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
        Reading::Folded,
        false,
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
    /// Kept, found with the calls on the path to it unfolded
    /// ([`crate::unfold_path`]).
    Partial,
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
    reading: Reading,
    on_path: bool,
) -> Result<(Option<Replaced>, Outcome)> {
    let snapshot = Snapshot::take(cx);
    // A failed attempt costs the usual search nothing.
    let mut spare = *remaining;
    let tried = search(
        cx, rule, place, equation, goal, unfolded, mode, reading, on_path, &mut spare,
    );
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
            recovered(cx);
            (Outcome::RanOut, None)
        }
        // A rescue that runs out reading the goal back found nothing: the
        // error stays the `E-REWRITE-NOTHING` it was before the rescue.
        Err(e) if mode == Mode::Rescue && recoverable(cx, &e) => {
            snapshot.restore(cx);
            recovered(cx);
            (Outcome::Failed, None)
        }
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => {
            snapshot.restore(cx);
            (Outcome::Failed, None)
        }
    };
    // [`first`] counts its attempts together.
    if mode != Mode::Complete {
        report(&outcome, mode, reading, rule);
    }
    Ok((kept, outcome))
}

/// Prints `outcome` for `rule` when `STITCHWORT_REWRITE_METRICS` is set.
fn report(outcome: &Outcome, mode: Mode, reading: Reading, rule: &RewriteRule) {
    if !crate::metrics::wanted("STITCHWORT_REWRITE_METRICS") {
        return;
    }
    let name = match (outcome, mode) {
        (Outcome::Kept, Mode::Rescue) if reading == Reading::AsWritten => "rescued-as-written",
        (Outcome::Kept, Mode::Rescue) => "rescued",
        (Outcome::Kept, _) => "folded",
        (Outcome::Partial, _) => "partial",
        (Outcome::Unconfirmed, _) => "unconfirmed",
        (Outcome::RanOut, _) => "ran-out",
        (Outcome::Incomplete, _) => "incomplete",
        (Outcome::Nothing, _) => "nothing",
        (Outcome::Failed, _) => "failed",
        (Outcome::Unchecked, _) => "unchecked",
    };
    crate::metrics::emit(
        "STITCHWORT_REWRITE_METRICS",
        &format!("rewrite-as-written: {name}"),
        rule.proof.span().start,
    );
}

/// When [`search`] finds today's instance ([`todays_instance`]).
enum Todays<'a> {
    /// Found already, before anything was solved.
    Before(Option<Term>),
    /// Found after the search as written has found something, with the
    /// rule elaborated afresh, so that a try finding nothing as written
    /// (most of `rewrite repeatedly`'s) skips the search of the unfolded
    /// goal. Undecided where either instance keeps an unknown, since a
    /// fresh copy's unknown is never the same as the original's: then
    /// [`search`] starts again the first way.
    After(&'a Value, &'a Term),
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
    reading: Reading,
    on_path: bool,
    remaining: &mut u64,
) -> Result<(Outcome, Option<Replaced>)> {
    // Today's choice of instance, for a rule with unknowns, found before
    // anything is solved ([`todays_instance`]): unless the unfolded goal
    // has an unknown the search as written could solve, after it.
    let unfolded = match unfolded {
        Some(found)
            if mode == Mode::Complete && equation.open(&cx.quote_unfolded(&equation.lhs)?) =>
        {
            Some(found)
        }
        _ => None,
    };
    if let Some((value, term)) = unfolded
        && !has_meta(term)
    {
        let snapshot = Snapshot::take(cx);
        let budget = *remaining;
        let decided = search_with(
            cx,
            rule,
            place,
            equation,
            goal,
            Todays::After(value, term),
            mode,
            reading,
            on_path,
            remaining,
        )?;
        if let Some(decided) = decided {
            return Ok(decided);
        }
        snapshot.restore(cx);
        *remaining = budget;
    }
    let todays = match unfolded {
        Some((value, term)) => todays_instance(cx, rule, place, equation, value, term, remaining)?,
        None => None,
    };
    let decided = search_with(
        cx,
        rule,
        place,
        equation,
        goal,
        Todays::Before(todays),
        mode,
        reading,
        on_path,
        remaining,
    )?;
    Ok(decided.expect("decided with today's instance found first"))
}

/// The goal `written` with the calls on the path to an occurrence of the
/// left side hidden inside them unfolded ([`crate::unfold_path`]); `None`
/// if there are none. An occurrence is a candidate the search would take:
/// the same as the left side read back as `reading` says, or one that
/// unifies with it (perhaps by the arguments of calls of the same
/// definition), whatever that solves undone.
fn opened(
    cx: &mut Ctx,
    equation: &Equation,
    written: &Term,
    reading: Reading,
) -> Result<Option<Term>> {
    let lhs = reading.quote(cx, &equation.lhs)?;
    let Some(lhs_key) = key(&lhs, 0) else {
        return Ok(None);
    };
    let level = cx.level();
    let relevant = crate::matching::free_levels(&lhs, level);
    let oracle = |cx: &mut Ctx, t: &Term, under: usize| -> Result<bool> {
        let g = cx.g();
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
        if same(&candidate, &lhs) {
            return Ok(true);
        }
        let snapshot = Snapshot::take(cx);
        let found = cx.eval(&candidate).and_then(|value| {
            Ok(crate::undo::unify(cx, &value, &equation.lhs)?
                || crate::undo::unify_solving_arguments(cx, &value, &equation.lhs)?)
        });
        snapshot.restore(cx);
        match found {
            Ok(found) => Ok(found),
            Err(e) if fatal(&e) => Err(e),
            Err(_) => Ok(false),
        }
    };
    crate::unfold_path::opened(cx, written, &[lhs_key], &relevant, &oracle)
}

fn has_meta(term: &Term) -> bool {
    term.subterms().any(|(t, _)| matches!(t, Term::Meta(_)))
}

/// [`search`], with today's instance found as `todays` says; `None` if
/// that can't decide.
#[allow(clippy::too_many_arguments)]
fn search_with(
    cx: &mut Ctx,
    rule: &RewriteRule,
    place: Place,
    equation: &Equation,
    goal: &Value,
    todays: Todays,
    mode: Mode,
    reading: Reading,
    on_path: bool,
    remaining: &mut u64,
) -> Result<Option<(Outcome, Option<Replaced>)>> {
    let mut written = reading.quote(cx, goal)?;
    // The `auto` proofs a call carries are not in the unfolded goal, where
    // `rewrite_once` proves the pending ones first; here they show, and a
    // motive holding one cannot be checked.
    let pending = pending_metas(&written);
    if !pending.is_empty() && cx.e.prove_now(&|m| pending.contains(&m))? {
        written = reading.quote(cx, goal)?;
    }
    if on_path {
        match opened(cx, equation, &written, reading)? {
            Some(opened) => written = opened,
            None => return Ok(Some((Outcome::Nothing, None))),
        }
    }
    let replace = |cx: &mut Ctx, remaining: &mut u64| {
        replace_occurrences_as(
            cx,
            rule,
            place,
            equation,
            goal,
            Shape::Whole(&written),
            0,
            false,
            reading,
            remaining,
        )
    };
    let replaced = match mode {
        // Only where the usual search ran out, so that today this fails at
        // once: the motive's check and round trip compare a goal too large
        // to read back, which can be as slow, and the comparisons' budget
        // doesn't cover them. The completeness check after this is bounded
        // by the size of what it reads back.
        Mode::Unconfirmed => {
            let g = cx.g();
            let mut cap = super::UNCONFIRMED_BUDGET;
            match g
                .machine
                .budget
                .limited(&mut cap, || replace(cx, remaining))?
            {
                Some(replaced) => replaced,
                None => return Ok(Some((Outcome::Failed, None))),
            }
        }
        _ => replace(cx, remaining)?,
    };
    let Some(step) = &replaced.step else {
        return Ok(Some((Outcome::Nothing, None)));
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
        return Ok(Some((Outcome::Unchecked, None)));
    }
    let todays = match todays {
        Todays::Before(todays) => todays,
        Todays::After(value, term) => {
            let lhs = cx.quote_unfolded(&equation.lhs)?;
            if has_meta(&lhs) {
                return Ok(None);
            }
            let snapshot = Snapshot::take(cx);
            let found = elaborate_rule(cx, rule, place)
                .and_then(|fresh| todays_instance(cx, rule, place, &fresh, value, term, remaining));
            snapshot.restore(cx);
            match found? {
                Some(todays) if has_meta(&todays) => return Ok(None),
                todays => todays,
            }
        }
    };
    if let Some(todays) = &todays
        && !same(todays, &cx.quote_unfolded(&equation.lhs)?)
    {
        return Ok(Some((Outcome::Incomplete, None)));
    }
    let mut outcome = Outcome::Kept;
    match mode {
        Mode::Complete => {
            if hidden_copy(cx, rule, place, equation, &step.motive, remaining)? {
                return Ok(Some((Outcome::Incomplete, None)));
            }
        }
        Mode::Rescue => {}
        Mode::Unconfirmed => {
            // The check is cut short by its own budget, so the rest stays
            // for the premises.
            let mut check = *remaining;
            match hidden_copy(cx, rule, place, equation, &step.motive, &mut check) {
                Ok(true) => return Ok(Some((Outcome::Incomplete, None))),
                Ok(false) => *remaining = check,
                Err(e) if ran_out(cx, &e) => outcome = Outcome::Unconfirmed,
                Err(e) => return Err(e),
            }
        }
    }
    discharge(cx, rule, equation, 0, remaining)?;
    Ok(Some((outcome, Some(replaced))))
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
    // The left side first: where it is too large to read back, the check
    // can't be made, and the goal's unfolding, often as large, isn't built.
    let lhs_term = cx.quote_unfolded(&equation.lhs)?;
    // A variable can't be hidden inside a call: a definition is closed, so
    // its unfolding mentions a variable of the goal's only through the
    // arguments the call shows, where the search replaced it. So a motive
    // that doesn't mention the variable has no copy unfolded either, and
    // isn't read back unfolded: in a goal about a large program (the
    // equation of two runs' values, in a two-run walk) that read-back is
    // most of what the `rewrite` costs (SW-4469).
    if let Term::Var(ix) = lhs_term
        && key(&lhs_term, 0).is_some()
        && let Term::Lam(_, _, inner, _) = motive
        && let Term::Lam(_, _, body, _) = &**inner
        && !body.mentions(ix + 2)
    {
        return Ok(false);
    }
    let motive_value = cx.eval(motive)?;
    let unmentioned = match motive {
        Term::Lam(_, _, inner, _) => match &**inner {
            Term::Lam(_, _, body, _) => unmentioned(cx, &lhs_term, body),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    // A motive no larger unfolded than the left side is read back, as that
    // costs about what [`left_needs_any`] would.
    let small = match unmentioned.is_empty() {
        true => None,
        false => {
            let cap = (lhs_term.subterms().count() as u64).max(1000);
            quote_at_most(&g, cx.level(), &motive_value, cap)?
        }
    };
    let unfolded = match small {
        Some(unfolded) => unfolded,
        None if !unmentioned.is_empty()
            && left_needs_any(cx, equation, &lhs_term, &unmentioned)? =>
        {
            return Ok(false);
        }
        None => cx.quote_unfolded(&motive_value)?,
    };
    let Some(key) = key(&lhs_term, 0) else {
        // Nothing to compare by: don't trust the as-written result.
        return Ok(true);
    };
    let level = cx.level();
    let search = Search::new(
        cx,
        rule,
        place,
        equation,
        lhs_term,
        key,
        0,
        false,
        Reading::Unfolded,
        *remaining,
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

/// The variables of the context that the left side `lhs_term` (read back
/// unfolded) mentions and `body`, the motive's body under its `x'` and `_`,
/// doesn't, for [`left_needs_any`]; none where the left side has an unknown
/// or a `match` not lifted yet, since the search then compares by more than
/// conversion.
fn unmentioned(cx: &Ctx, lhs_term: &Term, body: &Term) -> Vec<usize> {
    if has_meta(lhs_term) || crate::lift::mentions_draft(cx, lhs_term) {
        return Vec::new();
    }
    let mut free: Vec<usize> = lhs_term
        .subterms()
        .filter_map(|(t, binders)| match t {
            Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) if *ix >= binders => {
                Some(ix - binders)
            }
            _ => None,
        })
        .collect();
    free.sort_unstable();
    free.dedup();
    free.retain(|ix| *ix < cx.level() && !body.mentions(ix + 2));
    free
}

/// Whether the left side `lhs_term` depends on one of `unmentioned`, the
/// variables the motive doesn't mention ([`unmentioned`]): then the motive
/// has no copy hidden, and isn't read back unfolded (in
/// `Float.Theory.roundGrid`, `rewrite n0` by `q * Nat.pow 2 e = 0` leaves a
/// motive about `roundRatio (Int.signed s x')`, 806k nodes unfolded,
/// SW-4606).
///
/// A copy is a part of the unfolded motive convertible with the left side,
/// and computing mentions no variable the term didn't, so a copy doesn't
/// mention `v` either. Mentioning `v` isn't enough for depending on it: a
/// proof, an inert argument, a field of a type with record eta, or an
/// argument a stuck call's case tree never reads can hold `v` and still be
/// equal to one without it. So the test is conversion itself: the left side
/// against itself with `v` renamed to a fresh variable. If those differ, a
/// copy `c` can't exist: renaming `v` leaves `c` as it is, so `c` would be
/// equal to both, and conversion is an equivalence (docs/core.md, G6) that
/// renaming a variable preserves. The two sides have one type, as
/// conversion needs, only if the left side's type doesn't mention `v`, so
/// such a `v` isn't tried.
fn left_needs_any(
    cx: &Ctx,
    equation: &Equation,
    lhs_term: &Term,
    unmentioned: &[usize],
) -> Result<bool> {
    let g = cx.g();
    let level = cx.level();
    let carrier = cx.quote_unfolded(&equation.carrier)?;
    let lhs = cx.eval(lhs_term)?;
    // A few tries: each costs a comparison of the left side with itself.
    for &ix in unmentioned.iter().take(4) {
        let slot = level - 1 - ix;
        let plain = matches!(&cx.env[slot],
            Value::Neutral(Head::Var(l, _, _), spine) if *l == slot && spine.is_empty());
        if !plain || carrier.mentions(ix) {
            continue;
        }
        let mut env = cx.env.clone();
        env[slot] = Value::var(level);
        let renamed = eval(&g, &env, lhs_term)?;
        if !conv(&g, level + 1, &lhs, &renamed)? {
            return Ok(true);
        }
    }
    Ok(false)
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
            cx.quote_unfolded(&equation.lhs).map(Some)
        } else {
            Ok(None)
        }
    });
    snapshot.restore(cx);
    found
}
