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
//! ([`key`]) and unifies with it, solving nothing.
//!
//! The result is kept only if it does what the usual test does, and more
//! only where that test missed an occurrence written differently:
//!
//! 1. Every variable the usual test copies is copied here too.
//! 2. **Completeness and the same instance.** Each generalised target (the
//!    goal, and the type of each variable copied here), read back unfolded,
//!    agrees with what the usual test makes of it ([`agrees`]): the same
//!    term, except that where the usual result still has a subterm equal
//!    (by unification, solving nothing) to a scrutinee, this one may have
//!    the scrutinee's variable. So an occurrence hidden inside a call kept
//!    folded, which the usual test replaces and this one can't see, makes
//!    the two differ, and so does a call that computes on the scrutinee
//!    where the usual test found nothing to replace (`f s` with `s` a
//!    constructor: the usual goal has `f`'s result, this one would have `f
//!    x`, stuck). Nothing is open to choose: the scrutinees are known (the
//!    `match` waited for them, [`super::blocker`]), and a candidate that
//!    would solve an unknown to match is not an occurrence, so where both
//!    find something they find the same thing.
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
//! Lean's rule (abstract what is visible, leave hidden copies) was not taken:
//! `std`'s `Result.traverseCons` and `List.foldMaxMember` rely on the copy a
//! `match` refines inside a definition (goal-as-written.md, option B; D2478).

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_core::{Ev, Icit, Term, Value};

use super::{Generalise, Scrut, Skip, free_levels, is_var, same};
use crate::check::{Ctx, Result};
use crate::lift::replace_with;
use crate::rewrite::{Key, key, mentions_bound, search_budget};
use crate::undo::{Snapshot, fatal};

/// What the usual occurrence test made of the `match`, in its context.
pub(super) struct Today<'a> {
    /// Each scrutinee's normal form, `None` where it occurs nowhere.
    pub(super) occurrences: &'a [Option<&'a Term>],
    pub(super) copied: &'a [usize],
    /// The variables' types read back unfolded (`refl` for a skipped one).
    pub(super) type_terms: &'a [Term],
    pub(super) goal_term: &'a Term,
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
pub(super) enum Outcome {
    /// Agrees with the usual test (and perhaps found more).
    Kept,
    /// The usual test found nothing anywhere; this did.
    Rescued,
    /// Found, but it disagrees with the usual test: a copy is hidden in a
    /// call, or a variable the usual test copies isn't copied here.
    Incomplete,
    /// Found nothing as written.
    Nothing,
    /// Ran out of its budget, or something failed.
    Failed,
    /// The motive could not be checked now, or is ill-typed.
    Unchecked,
}

/// Prints `outcome` for the `match` at `span` when
/// `STITCHWORT_MATCH_METRICS` is set.
pub(super) fn report(outcome: Outcome, span: stitchwort_syntax::Span) {
    if std::env::var_os("STITCHWORT_MATCH_METRICS").is_none() {
        return;
    }
    let name = match outcome {
        Outcome::Kept => "folded",
        Outcome::Rescued => "rescued",
        Outcome::Incomplete => "incomplete",
        Outcome::Nothing => "nothing",
        Outcome::Failed => "failed",
        Outcome::Unchecked => "unchecked",
    };
    eprintln!("match-as-written: {name} at={}", span.start);
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
    let g = cx.g();
    let snapshot = Snapshot::take(cx);
    let mut remaining = search_budget(cx);
    let tried = g.machine.budget.limited(&mut remaining, || {
        search(cx, exprs, today, goal, base, skip)
    });
    snapshot.restore(cx);
    let written = match tried {
        Ok(Some(Ok(written))) => return Ok(Some(written)),
        Ok(Some(Err(outcome))) => outcome,
        // Over this attempt's own budget.
        Ok(None) => Outcome::Failed,
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => Outcome::Failed,
    };
    report(written, span);
    Ok(None)
}

fn search(
    cx: &mut Ctx,
    exprs: &[Scrut],
    today: &Today,
    goal: &Value,
    base: usize,
    skip: Option<Skip>,
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
            key,
        });
    }
    // From the values as bound, not forced: forcing unfolds an outer call.
    let goal_written = cx.quote_folded(goal)?;
    let types_written = (0..base)
        .map(|l| match skip.is_some_and(|skip| skip(cx, l)) {
            true => Ok(None),
            false => cx.quote_folded(&cx.types[l]).map(Some),
        })
        .collect::<Result<Vec<_>>>()?;
    let unrefined: Vec<bool> = (0..base)
        .map(|l| is_var(&cx.env[l], l) || cx.lets[l].is_some())
        .collect();
    let finder = Finder {
        cx: RefCell::new(cx),
        needles,
        base,
        depth: base + e,
        hits: RefCell::new(Vec::new()),
        error: RefCell::new(None),
    };
    let goal_generalised = finder.generalise(&g, &goal_written)?;
    let mut found = vec![false; e];
    for &i in finder.hits.borrow().iter() {
        found[i] = true;
    }
    // The variables to copy, chosen as the usual test chooses them (by the
    // folded types: a call's unfolding can only drop free variables, so this
    // copies at least the dependents the unfolded types would give).
    let mut copied: Vec<(usize, Term)> = Vec::new();
    for (l, ty) in types_written.iter().enumerate() {
        let Some(ty) = ty else { continue };
        if !unrefined[l] {
            continue;
        }
        let before = finder.hits.borrow().len();
        let generalised = finder.generalise(&g, ty)?;
        let hits = finder.hits.borrow()[before..].to_vec();
        let depends = free_levels(ty, base)
            .iter()
            .any(|f| copied.iter().any(|(c, _)| c == f));
        if !hits.is_empty() || depends {
            for i in hits {
                found[i] = true;
            }
            copied.push((l, generalised));
        }
    }
    if !found.iter().any(|&f| f) {
        return Ok(Err(Outcome::Nothing));
    }
    // As in the usual test: a scrutinee's type can't mention a copy.
    if exprs.iter().any(|s| {
        free_levels(&s.ty_term, base)
            .iter()
            .any(|f| copied.iter().any(|(c, _)| c == f))
    }) {
        return Ok(Err(Outcome::Failed));
    }
    let todays_found = !today.copied.is_empty()
        || (today.occurrences.iter().flatten()).any(|n| super::occurs(n, today.goal_term));
    // Check 1.
    if (today.copied.iter()).any(|l| !copied.iter().any(|(c, _)| c == l)) {
        return Ok(Err(Outcome::Incomplete));
    }
    // Check 2, on the goal and every copy's type.
    let todays = Generalise {
        base,
        depth: base + e,
        exprs: today.occurrences,
        copies: &Default::default(),
    };
    let mut pairs = vec![(&goal_generalised, todays.apply(&g, today.goal_term)?)];
    for (l, ty) in &copied {
        pairs.push((ty, todays.apply(&g, &today.type_terms[*l])?));
    }
    for (written, usual) in pairs {
        if !finder.agrees(&g, written, &usual)? {
            return Ok(Err(Outcome::Incomplete));
        }
    }
    Ok(Ok(Written {
        goal: goal_generalised,
        copied,
        found,
        outcome: match todays_found {
            true => Outcome::Kept,
            false => Outcome::Rescued,
        },
    }))
}

/// A scrutinee as the search looks for it.
struct Needle {
    /// Read back folded.
    written: Term,
    value: Value,
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
    /// context, is scrutinee `i`: the same term, or one that unifies with
    /// it solving nothing (no unknown solved, made or left waiting). One
    /// that would solve something to match is not an occurrence: the usual
    /// test's syntactic comparison never solves anything, and a choice made
    /// by solving could differ from it.
    fn occurrence(&self, i: usize, t: &Term, under: usize) -> Result<bool> {
        let mut cx = self.cx.borrow_mut();
        let cx: &mut Ctx = &mut cx;
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
        let needle = &self.needles[i];
        if same(&candidate, &needle.written) {
            return Ok(true);
        }
        let snapshot = Snapshot::take(cx);
        let waiting = cx.e.attempt.queue.len();
        let unified = cx
            .eval(&candidate)
            .and_then(|value| cx.unify(&value, &needle.value));
        let quiet = snapshot.solved_since(cx).is_empty()
            && cx.metas().metas.borrow().len() == snapshot.metas()
            && cx.e.attempt.queue.len() == waiting;
        snapshot.restore(cx);
        match unified {
            Ok(unified) => Ok(unified && quiet),
            Err(e) if fatal(&e) => Err(e),
            Err(_) => Ok(false),
        }
    }

    /// Check 2: whether `written` (a generalised target as written), read
    /// back unfolded, agrees with `usual` (the usual test's generalisation
    /// of the same target, read back unfolded), both in `depth` variables.
    ///
    /// Both are read back by the same rules from the same goal, so where
    /// they abstract the same subterms they are the same term. Where they
    /// differ, `written` may have a scrutinee's variable where `usual` has a
    /// subterm that is that scrutinee written otherwise (an occurrence the
    /// syntactic test missed); any other difference fails.
    fn agrees(&self, g: &Ev, written: &Term, usual: &Term) -> Result<bool> {
        let e = self.depth - self.base;
        let unfolded = {
            let cx = self.cx.borrow();
            // Under a binder per scrutinee, so that `eval` and `quote` see
            // them as variables.
            let mut lambdas = written.clone();
            for _ in 0..e {
                lambdas = Term::Lam("s".into(), Icit::Explicit, Rc::new(lambdas));
            }
            let mut body = cx.quote(&cx.eval(&lambdas)?)?;
            for _ in 0..e {
                let Term::Lam(_, _, inner) = &body else {
                    return Ok(false);
                };
                body = inner.as_ref().clone();
            }
            body
        };
        self.agree(g, &unfolded, usual, 0)
    }

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
            (Lam(_, i, b1), Lam(_, j, b2)) => i == j && self.agree(g, b1, b2, under + 1)?,
            (Pi(_, i, a1, b1), Pi(_, j, a2, b2)) => {
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
            (Let(_, t1, v1, b1, _), Let(_, t2, v2, b2, _)) => {
                self.agree(g, t1, t2, under)?
                    && self.agree(g, v1, v2, under)?
                    && self.agree(g, b1, b2, under + 1)?
            }
            (J(m1, b1, p1), J(m2, b2, p2)) => {
                self.agree(g, m1, m2, under)?
                    && self.agree(g, b1, b2, under)?
                    && self.agree(g, p1, p2, under)?
            }
            (Quot(f1, xs, _), Quot(f2, ys, _)) => f1 == f2 && all(xs, ys, under)?,
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
