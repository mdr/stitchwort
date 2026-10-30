//! The postponement queue (docs/proposals/postponement.md §5). A check that
//! needs the head of a type that is still an unknown doesn't fail: it is
//! queued with its context, a placeholder unknown stands for its result in
//! the term built so far, and it waits on the unknown at that head (its
//! *blocker*). It is resumed at fixed points, once that unknown is solved:
//! - W1, the end of each application, for the checks queued while it was
//!   elaborated and only those (`check::apply_args_postponing`; D2014);
//! - W2, before helpers are lifted (`lift.rs`), so a check holding a
//!   `match` drafts it first;
//! - W3, each round of the obligations loop (`auto.rs`), so resuming and
//!   finding instances go round together;
//! - W4, the end of a declaration part ([`Elaborator::finish`]), which also
//!   applies defaults, one at a time by priority, and reports what is still
//!   stuck.
//!
//! The queue is per declaration, like the obligations: `clear_metas` and
//! `rewind` empty it, and a [`crate::undo::Snapshot`] restores it. What is
//! queued (stages 2 and 3 of §8; number literals are stage 4):
//! - K1, a record literal whose type is unknown (`records.rs`, `Literal`),
//!   whose default is SW-805's field-name rule;
//! - K2, a `.field` or dot call whose receiver's type view meets an
//!   unknown (`dot.rs`, `DotCall`), with its receiver kept by §5.5's rule;
//! - K3, a method section whose argument's type is unknown (`dot.rs`,
//!   `Section`), checked whole once it is known;
//! - a proposition's decision into a `Bool` where it holds a placeholder
//!   not filled yet (`check.rs`, `Decide`; D2035), which waits for it;
//! - a comparison, against an expected type or by `rfl`, that fails only
//!   at unknowns the queue still has to settle ([`compare_waiting`],
//!   [`Comparison`]; stage 6, tri-state unification): it waits for any of
//!   them, and has no term.
//!
//! A resume point with nothing queued in its scope costs a length
//! comparison.
//!
//! The queue's invariants (§5.1), and how each is kept here:
//! 1. *One placeholder, one occurrence*: [`queue`] makes a fresh unknown
//!    for each item, and a restore drops the items queued since, whose
//!    placeholders the restore drops too.
//! 2. *Only its item fills a placeholder*: only [`Elaborator::fill`],
//!    while the item runs. Until then the placeholder is frozen
//!    (`Globals::unfilled_placeholders`, D2016's end state): unification
//!    never solves it, and a comparison that meets it waits or fails. If
//!    anything else solved it first, the item's term must agree with that
//!    solution; zonking writes the item's term either way.
//! 3. *Isolation*: W1 resumes only the items queued since its application
//!    began; W2-W4 run between elaborations, never inside a check.
//! 4. *No re-entry*: an item's [`State`] is running while its check runs,
//!    and a resume point selects only waiting items.
//! 5. *Restore restores the queue*: the states change only through the
//!    resumption log, which a snapshot records with the items.
//! 6. *Kept subterms are stable*: K1 keeps nothing elaborated; K2 keeps its
//!    receiver as syntax where the blocker predates it, and as a term only
//!    where the receiver made the blocker, which [`kept_receiver`] checks
//!    made no choice from an unknown.
//! 7. *Defaults at quiescence only*: only W4 applies one, after the
//!    obligations loop has stopped making progress.
//! 8. *Placeholders are opaque to elaboration choices*: a placeholder is an
//!    unknown like any other to the code around it; the consumers that
//!    choose from a type's shape wait or decide at `finish` (§5.10). Debug
//!    assertions: the field-name rule chooses a literal's type only as W4's
//!    default ([`Queue::settling`]), and a resumed dot call has its implicit
//!    arguments inserted before it fills a placeholder that doesn't take
//!    them (`dot.rs`). Comparisons that fail at an unfilled placeholder are
//!    counted (`unify::met_unfilled`).
//!
//! The debug assertions below check 1-6 where they can be seen; the unit
//! tests at the end exercise each with items made directly, and K1, K2 and
//! K3 on small modules.
//!
//! Counters for later stages are printed with `STITCHWORT_TIMINGS`
//! ([`counts`]).

use std::cell::{Cell, RefCell};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::value::{Head, force};
use stitchwort_core::{Globals, Term, Value};
use stitchwort_syntax::Diagnostic;

use crate::Elaborator;
use crate::check::{Ctx, Result, Saved};
use crate::unify::Answer;

/// What a queued check does when it is resumed: one implementation per
/// kind of item (K1-K4, stages 2-4 of the note).
pub(crate) trait Check {
    /// Elaborates the item in its saved context, now that the head of what
    /// it waits on is known.
    fn resume(&self, cx: &mut Ctx) -> Result<Resumed>;

    /// The default it takes when nothing else decides (ladder step 3).
    fn default_priority(&self) -> Option<Priority> {
        None
    }

    /// Applies that default, which solves what the item waits on; whether
    /// it applied. One that doesn't apply is undone by the caller.
    fn apply_default(&self, _cx: &mut Ctx) -> Result<bool> {
        Ok(false)
    }

    /// Whether it may be resumed although the head of what it waits on is
    /// still unknown: a waiting comparison waits on any of several unknowns
    /// (stage 6, [`Comparison`]).
    fn wakes(&self, _g: &Globals) -> Result<bool> {
        Ok(false)
    }
}

/// What a resumed check gives.
pub(crate) enum Resumed {
    /// Its term, to fill its placeholder with.
    Done(Term),
    /// It holds, and has no term: a waiting comparison ([`Comparison`]),
    /// whose placeholder stands for nothing.
    Holds,
    /// It met another unknown (a `.field` at a later step of its view): it
    /// waits again, on the head of this type.
    Waiting(Value),
    /// As [`Resumed::Waiting`], resumed from now on by this check: a `.field`
    /// whose receiver, elaborated again, made the unknown it now waits on,
    /// and so keeps that receiver (`dot.rs`, `DotCall`). The change is a
    /// state's, so a restore takes it back with the resumption.
    WaitingAs(Value, Rc<dyn Check>),
}

/// The defaults, in the order the ladder tries them (D2013): SW-805's
/// field-name rule for a record literal, then `Nat` for a number.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum Priority {
    FieldNames,
    #[cfg_attr(not(test), expect(dead_code, reason = "K4's default, stage 4"))]
    Nat,
}

/// Where an item is (invariant 4). *Failed* lasts only while the error
/// propagates: either an attempt is undone, and with it the item's
/// resumption, or the declaration fails.
#[derive(Clone)]
pub(crate) enum State {
    /// On the head of this type, a value in the item's context; to be
    /// resumed by this check rather than the item's own, if there is one
    /// ([`Resumed::WaitingAs`]).
    Waiting(Value, Option<Rc<dyn Check>>),
    Running,
    Done,
    Failed,
}

pub(crate) struct Item {
    check: Rc<dyn Check>,
    saved: Saved,
    /// The placeholder: its unknown applied to the context's variables
    /// (`Ctx::fresh_meta`), and that unknown.
    placeholder: Term,
    meta: usize,
    /// The placeholder's type.
    ty: Value,
    /// The error its site raised before it could wait, reported if it is
    /// still waiting at the end.
    error: Diagnostic,
    /// Whether it has been counted as reaching the end of an application
    /// still waiting.
    crossed: Cell<bool>,
    /// Whether it is a waiting comparison (stage 6, [`Comparison`]), whose
    /// placeholder stands for nothing.
    constraint: bool,
}

/// The current declaration's queued checks, in creation order, with their
/// states. A state changes only through [`Queue::set`], which keeps what it
/// replaced in the resumption log, as `Globals::meta_trail` does for
/// solutions: so restoring a snapshot (which records both lengths) undoes
/// the resumptions made since along with the items queued since.
#[derive(Default)]
pub(crate) struct Queue {
    items: RefCell<Vec<Rc<Item>>>,
    states: RefCell<Vec<State>>,
    log: RefCell<Vec<(usize, State)>>,
    /// Whether the end of a declaration part (W4) is settling the queue:
    /// the only place a default may be applied (invariants 7 and 8).
    settling: Cell<bool>,
}

/// The queue's lengths at a snapshot.
#[derive(Clone, Copy)]
pub(crate) struct Mark {
    items: usize,
    log: usize,
}

impl Queue {
    pub(crate) fn len(&self) -> usize {
        self.items.borrow().len()
    }

    /// Whether W4 is settling the queue, the only place a default is
    /// applied: a choice an item's default makes (the field-name rule) is
    /// made from nothing else having said what the item is, never from a
    /// placeholder's apparent shape in the middle of elaboration
    /// (invariant 8).
    pub(crate) fn settling(&self) -> bool {
        self.settling.get()
    }

    pub(crate) fn mark(&self) -> Mark {
        Mark {
            items: self.len(),
            log: self.log.borrow().len(),
        }
    }

    /// Back to `mark`: each state changed since is put back, newest first,
    /// and the items queued since are dropped. A fill taken back takes its
    /// term out of the placeholder table (`Globals::lifted_calls`). `metas`
    /// is the length the metavariables are restored to.
    pub(crate) fn restore(&self, mark: Mark, g: &Globals, metas: usize) {
        let changed = self.len() > mark.items || self.log.borrow().len() > mark.log;
        {
            let items = self.items.borrow();
            let mut states = self.states.borrow_mut();
            let mut log = self.log.borrow_mut();
            while log.len() > mark.log {
                let (i, old) = log.pop().expect("longer than the mark's");
                if matches!(states[i], State::Done) {
                    g.lifted_calls.borrow_mut().remove(&items[i].meta);
                }
                states[i] = old;
            }
        }
        self.items.borrow_mut().truncate(mark.items);
        self.states.borrow_mut().truncate(mark.items);
        debug_assert!(
            self.items.borrow().iter().all(|item| item.meta < metas),
            "an item outlived its placeholder (invariant 1)"
        );
        if changed {
            self.sync_unfilled(g);
        }
    }

    /// Empties the queue; `Globals::clear_metas` empties the placeholders
    /// it tells the unifier of.
    pub(crate) fn clear(&self) {
        self.items.borrow_mut().clear();
        self.states.borrow_mut().clear();
        self.log.borrow_mut().clear();
    }

    /// Tells the unifier which placeholders aren't filled yet
    /// (`Globals::unfilled_placeholders`): they are frozen until filled
    /// (D2016), and a comparison that fails at one is counted
    /// (`unify::met_unfilled`).
    fn sync_unfilled(&self, g: &Globals) {
        let items = self.items.borrow();
        let states = self.states.borrow();
        let mut unfilled = g.unfilled_placeholders.borrow_mut();
        unfilled.clear();
        unfilled.extend(
            (0..items.len())
                .filter(|&i| !matches!(states[i], State::Done) && !items[i].constraint)
                .map(|i| items[i].meta),
        );
    }

    fn item(&self, i: usize) -> Rc<Item> {
        self.items.borrow()[i].clone()
    }

    pub(crate) fn state(&self, i: usize) -> State {
        self.states.borrow()[i].clone()
    }

    fn set(&self, i: usize, state: State, g: &Globals) {
        let old = std::mem::replace(&mut self.states.borrow_mut()[i], state);
        self.log.borrow_mut().push((i, old));
        self.sync_unfilled(g);
    }

    fn waiting(&self, i: usize) -> Option<Value> {
        match &self.states.borrow()[i] {
            State::Waiting(needs, _) => Some(needs.clone()),
            _ => None,
        }
    }

    /// What resumes item `i`, or gives its default: its own check, or the
    /// one it waits as.
    fn check(&self, i: usize) -> Rc<dyn Check> {
        match &self.states.borrow()[i] {
            State::Waiting(_, Some(check)) => check.clone(),
            _ => self.items.borrow()[i].check.clone(),
        }
    }

    fn any_waiting(&self) -> bool {
        (self.states.borrow().iter()).any(|s| matches!(s, State::Waiting(..)))
    }

    /// How many times item `i` has been resumed since the queue was last
    /// cleared, counting resumptions undone only if they still are.
    #[cfg(test)]
    fn resumptions(&self, i: usize) -> usize {
        (self.log.borrow().iter())
            .filter(|(j, old)| *j == i && matches!(old, State::Waiting(..)))
            .count()
    }
}

/// Queues `check`, which waits on the head of `needs`, with a placeholder
/// of type `ty` for its result, and `error` for its site's error if it
/// stays stuck: the placeholder's term, which stands for the result in the
/// term being built.
pub(crate) fn queue(
    cx: &Ctx,
    check: Rc<dyn Check>,
    needs: Value,
    ty: Value,
    error: Diagnostic,
) -> Result<Term> {
    debug_assert!(!ready(cx.g(), &needs)?, "an item waits on an unknown head");
    let placeholder = cx.fresh_meta();
    let Term::Meta(meta) = *placeholder.spine().0 else {
        unreachable!("a fresh metavariable")
    };
    let q = &cx.e.queue;
    q.items.borrow_mut().push(Rc::new(Item {
        check,
        saved: cx.save(),
        placeholder: placeholder.clone(),
        meta,
        ty,
        error,
        crossed: Cell::new(false),
        constraint: false,
    }));
    q.states.borrow_mut().push(State::Waiting(needs, None));
    q.sync_unfilled(cx.g());
    count(&QUEUED);
    Ok(placeholder)
}

/// A placeholder that `v` mentions whose check hasn't filled it, and that
/// unification hasn't solved either, if any: for a choice that must wait for
/// it (invariant 8; `check::decide_to_bool`). Free while nothing waits.
pub(crate) fn unfilled_in(cx: &Ctx, v: &Value) -> Result<Option<usize>> {
    let q = &cx.e.queue;
    let unfilled: Vec<usize> = {
        let (items, states) = (q.items.borrow(), q.states.borrow());
        (0..items.len())
            .filter(|&i| !matches!(states[i], State::Done) && !items[i].constraint)
            .map(|i| items[i].meta)
            .filter(|&m| cx.g().meta_solution(m).is_none())
            .collect()
    };
    if unfilled.is_empty() {
        return Ok(None);
    }
    let term = crate::interfaces::scanned(cx, v)?;
    let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    Ok(term.subterms().find_map(|(t, _)| match t {
        Term::Meta(m) if unfilled.contains(m) => Some(*m),
        _ => None,
    }))
}

/// The unknowns the queue still has to settle (stage 6): each placeholder
/// not filled yet that unification hasn't solved, and the unknown each
/// waiting item waits on. Each is solved by the end of the declaration, by
/// an item's resumption or default, or its item is reported stuck; so a
/// comparison that fails only on one of them can wait for it.
fn pending(cx: &Ctx) -> Result<HashSet<usize>> {
    let g = cx.g();
    let q = &cx.e.queue;
    let mut pending = HashSet::default();
    for i in 0..q.len() {
        let state = q.state(i);
        if matches!(state, State::Done) {
            continue;
        }
        let item = q.item(i);
        if !item.constraint && g.meta_solution(item.meta).is_none() {
            pending.insert(item.meta);
        }
        if let State::Waiting(needs, _) = state
            && let Some(m) = head_meta(g, &needs)?
        {
            pending.insert(m);
        }
    }
    Ok(pending)
}

/// How a waiting comparison reports that it fails: as the check against an
/// expected type it came from, or as `rfl` (the two callers of
/// [`compare_waiting`]).
#[derive(Clone, Copy)]
pub(crate) enum Failure {
    Mismatch,
    Refl,
}

impl Failure {
    /// The error of `found` against `expected`, as its caller reports it.
    fn error(self, cx: &mut Ctx, found: &Value, expected: &Value) -> Result<Diagnostic> {
        Ok(match self {
            Failure::Mismatch => match crate::effects::partial_mismatch(cx, found, expected)? {
                Some(d) => d,
                None => crate::numbers::explain_default(cx, cx.mismatch(expected, found), &[found]),
            },
            Failure::Refl => crate::check::refl_error(cx, found, expected),
        })
    }
}

/// Stage 6 (docs/proposals/postponement.md, "Stage 6: design"): `found`
/// against `expected`, where every other way has failed, compared again by
/// tri-state unification (`unify::unify_waiting`). If it fails only at
/// pairs stuck on unknowns the queue still has to settle ([`pending`]),
/// what it could solve stays solved and the rest waits, as a queued
/// [`Comparison`] that is resumed once one of those unknowns is solved:
/// `true`. Otherwise nothing is changed: `false`, and the caller reports
/// its error as before.
pub(crate) fn compare_waiting(
    cx: &mut Ctx,
    found: &Value,
    expected: &Value,
    failure: Failure,
) -> Result<bool> {
    if cx.e.queue.len() == 0 {
        return Ok(false);
    }
    let pending = pending(cx)?;
    if pending.is_empty() {
        return Ok(false);
    }
    let snapshot = crate::undo::Snapshot::take(cx);
    match crate::unify::unify_waiting(cx.g(), cx.level(), found, expected, &pending)? {
        Answer::Yes => Ok(true),
        Answer::No => {
            snapshot.restore(cx);
            Ok(false)
        }
        Answer::Blocked(pairs) => {
            let comparison = Comparison {
                pairs,
                blockers: Vec::new(),
                found: found.clone(),
                expected: expected.clone(),
                failure,
            };
            let blockers = comparison.blockers(cx, &pending)?;
            let Some(&first) = blockers.first() else {
                snapshot.restore(cx);
                return Ok(false);
            };
            let error = failure.error(cx, found, expected)?;
            let comparison = Comparison {
                blockers,
                ..comparison
            };
            queue_constraint(cx, Rc::new(comparison), first, error)?;
            count(&WAITED);
            Ok(true)
        }
    }
}

/// A comparison waiting for unknowns the queue still has to settle (stage
/// 6, [`compare_waiting`]): the pairs that couldn't be decided, what was
/// compared, and how its caller reports a failure. Resumed once one of its
/// blockers is solved: each pair is compared again, and it holds, fails
/// with its caller's error against the types now known, or waits again on
/// what it is still stuck on.
struct Comparison {
    pairs: Vec<crate::unify::Waiting>,
    /// The pending unknowns its pairs mention, any of which wakes it.
    blockers: Vec<usize>,
    found: Value,
    expected: Value,
    failure: Failure,
}

impl Comparison {
    /// The pending unknowns the pairs mention, in order, each once.
    fn blockers(&self, cx: &Ctx, pending: &HashSet<usize>) -> Result<Vec<usize>> {
        let mut found = Vec::new();
        for pair in &self.pairs {
            for side in [&pair.a, &pair.b] {
                let term = stitchwort_core::value::quote(cx.g(), pair.level, side)?;
                for (t, _) in term.subterms() {
                    if let Term::Meta(m) = t
                        && pending.contains(m)
                        && !found.contains(m)
                    {
                        found.push(*m);
                    }
                }
            }
        }
        Ok(found)
    }
}

impl Check for Comparison {
    fn resume(&self, cx: &mut Ctx) -> Result<Resumed> {
        // Evaluated afresh: a call stuck on a placeholder when it was made
        // stays a stuck value, and computes only when evaluated again with
        // the placeholder filled (as `unify::run`'s pairs put aside are).
        let found = cx.eval(&cx.quote_folded(&self.found)?)?;
        let expected = cx.eval(&cx.quote_folded(&self.expected)?)?;
        let (found, expected) = (&found, &expected);
        // Its caller's own ways first, as when it was made: a dictionary
        // that the filled placeholder lets be found may be what's in the
        // way now.
        let holds = match self.failure {
            Failure::Mismatch => crate::check::unifies_with_instances(cx, found, expected)?,
            Failure::Refl => {
                crate::undo::unify(cx, found, expected)?
                    || crate::check::refl_after_instances(cx, found, expected)?
            }
        };
        if holds {
            return Ok(Resumed::Holds);
        }
        let pending = pending(cx)?;
        let still =
            match crate::unify::unify_waiting(cx.g(), cx.level(), found, expected, &pending)? {
                Answer::Yes => return Ok(Resumed::Holds),
                Answer::No => return Err(self.failure.error(cx, found, expected)?),
                Answer::Blocked(pairs) => pairs,
            };
        let again = Comparison {
            pairs: still,
            blockers: Vec::new(),
            found: self.found.clone(),
            expected: self.expected.clone(),
            failure: self.failure,
        };
        let blockers = again.blockers(cx, &pending)?;
        let Some(&first) = blockers.first() else {
            return Err(self.failure.error(cx, &self.found, &self.expected)?);
        };
        Ok(Resumed::WaitingAs(
            on(first),
            Rc::new(Comparison { blockers, ..again }),
        ))
    }

    fn wakes(&self, g: &Globals) -> Result<bool> {
        Ok(self.blockers.iter().any(|&m| g.meta_solution(m).is_some()))
    }
}

/// The unknown `m`, as a value with nothing applied.
fn on(m: usize) -> Value {
    Value::Neutral(Head::Meta(m), Default::default())
}

/// Queues `check`, a comparison with no term of its own, waiting on unknown
/// `blocker`, with `error` if it stays stuck.
fn queue_constraint(
    cx: &Ctx,
    check: Rc<dyn Check>,
    blocker: usize,
    error: Diagnostic,
) -> Result<()> {
    let placeholder = cx.fresh_meta();
    let Term::Meta(meta) = *placeholder.spine().0 else {
        unreachable!("a fresh metavariable")
    };
    let q = &cx.e.queue;
    q.items.borrow_mut().push(Rc::new(Item {
        check,
        saved: cx.save(),
        placeholder,
        meta,
        ty: Value::Sort(stitchwort_core::Sort::Prop),
        error,
        crossed: Cell::new(false),
        constraint: true,
    }));
    q.states
        .borrow_mut()
        .push(State::Waiting(on(blocker), None));
    q.sync_unfilled(cx.g());
    Ok(())
}

/// Whether the head of `needs` is known.
fn ready(g: &Globals, needs: &Value) -> Result<bool> {
    Ok(head_meta(g, needs)?.is_none())
}

/// The unknown at the head of `v`, if it is one.
fn head_meta(g: &Globals, v: &Value) -> Result<Option<usize>> {
    Ok(match force(g, v.clone())? {
        Value::Neutral(Head::Meta(m), _) => Some(m),
        _ => None,
    })
}

/// The item's term as a call of its placeholder: in the variables the
/// placeholder is applied to, the first outermost, so that zonking can put
/// it in place of the placeholder applied to any arguments, as it does for
/// a lifted helper's call (`unify::zonk_call`). A `let`'s variable or one a
/// case split replaced, which the placeholder isn't applied to, is replaced
/// by its value. `None` if that value isn't in those variables either:
/// zonking then reads the placeholder's solution back, as for any unknown.
fn placeholder_call(cx: &Ctx, placeholder: &Term, term: &Term) -> Result<Option<(usize, Term)>> {
    let g = cx.g();
    let depth = cx.level();
    let spine: Vec<usize> = (placeholder.spine().1.iter())
        .map(|a| match a.strip_loc() {
            Term::Var(ix) => depth - 1 - ix,
            _ => unreachable!("a placeholder is applied to variables"),
        })
        .collect();
    let s = spine.len();
    let applied = |level: usize| -> Result<Term> {
        match spine.iter().position(|&l| l == level) {
            Some(j) => Ok(Term::Var(s - 1 - j)),
            None => Err(Diagnostic::error(
                "E-MALFORMED",
                "internal error: a filled placeholder's term uses a variable it isn't applied to",
            )),
        }
    };
    let variable = |level: usize| -> Result<Term> {
        applied(level).or_else(|_| {
            let value = cx.quote_folded(&cx.env[level])?;
            crate::lift::replace_with(g, &value, depth, &applied, &|_, _| None)
        })
    };
    match crate::lift::replace_with(g, term, depth, &variable, &|_, _| None) {
        Ok(call) => Ok(Some((s, call))),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(_) => Ok(None),
    }
}

impl Elaborator {
    /// W1: the end of an application, which began with `from` items
    /// queued. Resumes those queued since that can be, and only those
    /// (invariant 3).
    pub(crate) fn resume_application(&self, from: usize) -> Result<()> {
        debug_assert!(
            from <= self.queue.len(),
            "an application's checks outlived it (invariant 3)"
        );
        if self.queue.len() == from {
            return Ok(());
        }
        self.resume_from(from)?;
        // Each placeholder still unfilled here is one a comparison may meet
        // before its item can say what it is (the stage-6 trigger, §5.13).
        for i in from..self.queue.len() {
            let item = self.queue.item(i);
            if self.queue.waiting(i).is_some() && !item.crossed.replace(true) {
                count(&CROSSED);
            }
        }
        Ok(())
    }

    /// Ladder step 1: resumes every waiting item from `from` on whose
    /// blocker is solved, in creation order, again while any is: whether
    /// any was.
    pub(crate) fn resume_from(&self, from: usize) -> Result<bool> {
        if self.queue.len() <= from {
            return Ok(false);
        }
        debug_assert!(
            (from..self.queue.len()).all(|i| !matches!(self.queue.state(i), State::Running)),
            "a resume point reached a running item (invariant 4, T3)"
        );
        let mut any = false;
        loop {
            let mut progress = false;
            let mut i = from;
            while i < self.queue.len() {
                if let Some(needs) = self.queue.waiting(i)
                    && (ready(&self.globals, &needs)?
                        || self.queue.check(i).wakes(&self.globals)?)
                {
                    self.resume_item(i)?;
                    progress = true;
                }
                i += 1;
            }
            if !progress {
                return Ok(any);
            }
            any = true;
        }
    }

    /// Resumes item `i`, running until its check returns.
    fn resume_item(&self, i: usize) -> Result<()> {
        let item = self.queue.item(i);
        let check = self.queue.check(i);
        let replaced = match self.queue.state(i) {
            State::Waiting(_, replaced) => replaced,
            _ => None,
        };
        self.queue.set(i, State::Running, &self.globals);
        count(&RESUMED);
        let mut cx = item.saved.ctx(self);
        let waits = |needs: &Value| {
            debug_assert!(
                !ready(&self.globals, needs).unwrap_or(false),
                "an item waits again only on an unknown head"
            );
            count(&REQUEUED);
        };
        let resumed = check.resume(&mut cx).and_then(|resumed| match resumed {
            Resumed::Done(term) => self.fill(&mut cx, i, &item, &term).map(|()| State::Done),
            Resumed::Holds => Ok(State::Done),
            Resumed::Waiting(needs) => {
                waits(&needs);
                Ok(State::Waiting(needs, replaced))
            }
            Resumed::WaitingAs(needs, check) => {
                waits(&needs);
                Ok(State::Waiting(needs, Some(check)))
            }
        });
        match resumed {
            Ok(state) => {
                self.queue.set(i, state, &self.globals);
                Ok(())
            }
            Err(e) => {
                self.queue.set(i, State::Failed, &self.globals);
                Err(e)
            }
        }
    }

    /// Fills item `i`'s placeholder with its term (invariant 2): if
    /// unification has solved the placeholder already (D2016), the term
    /// must agree with that solution, or that is the item's error, at its
    /// span; either way the term goes in the placeholder table, so that
    /// zonking writes it rather than the solution read back, which would
    /// write out what its calls unfold to (§5.10).
    fn fill(&self, cx: &mut Ctx, i: usize, item: &Item, term: &Term) -> Result<()> {
        let g = &self.globals;
        debug_assert!(
            matches!(self.queue.state(i), State::Running),
            "only its own running item fills a placeholder (invariant 2)"
        );
        debug_assert!(
            !g.lifted_calls.borrow().contains_key(&item.meta),
            "a placeholder is filled once (invariant 1)"
        );
        if g.meta_solution(item.meta).is_some() {
            count(&SOLVED_FIRST);
            if crate::unify::solved_lossily(g, item.meta) {
                count(&LOSSY);
            }
        }
        let value = cx.eval(term)?;
        let placeholder = cx.eval(&item.placeholder)?;
        g.unfilled_placeholders.borrow_mut().remove(&item.meta);
        if !cx.unify(&placeholder, &value)? {
            count(&DISAGREED);
            return Err(cx.mismatch(&placeholder, &value));
        }
        match placeholder_call(cx, &item.placeholder, term)? {
            Some((s, call)) => {
                g.lifted_calls
                    .borrow_mut()
                    .insert(item.meta, (s, Rc::new(call)));
            }
            None => count(&READ_BACK),
        }
        Ok(())
    }

    /// W2, before helpers are lifted: the resume points of the obligations
    /// loop, if anything is waiting, so that a queued check holding a
    /// `match` has drafted it.
    pub(crate) fn resume_before_lifting(&self) -> Result<()> {
        if self.queue.any_waiting() {
            self.solve_obligations_until_stuck()?;
        }
        Ok(())
    }

    /// W4, the end of a declaration part: the obligations loop, which
    /// resumes (W3), then while anything still waits, one default and the
    /// loop again; then the error of what is still stuck, if anything is.
    /// Otherwise what [`Elaborator::solve_obligations_until_stuck`] gives.
    pub(crate) fn settle_queue(&self) -> Result<Option<Diagnostic>> {
        let mut stuck = self.solve_obligations_until_stuck()?;
        let settling = self.queue.settling.replace(true);
        let defaulted = (|| -> Result<()> {
            while self.queue.any_waiting() && self.apply_default()? {
                stuck = self.solve_obligations_until_stuck()?;
            }
            Ok(())
        })();
        self.queue.settling.set(settling);
        defaulted?;
        match self.stuck_report()? {
            Some(error) => Err(error),
            None => Ok(stuck),
        }
    }

    /// Ladder step 3: the first default that applies, by priority and then
    /// creation order, among the waiting items: whether one did.
    fn apply_default(&self) -> Result<bool> {
        let mut candidates: Vec<(Priority, usize)> = (0..self.queue.len())
            .filter(|&i| self.queue.waiting(i).is_some())
            .filter_map(|i| Some((self.queue.check(i).default_priority()?, i)))
            .collect();
        candidates.sort();
        for (_, i) in candidates {
            let item = self.queue.item(i);
            let mut cx = item.saved.ctx(self);
            let snapshot = crate::undo::Snapshot::take(&cx);
            if self.queue.check(i).apply_default(&mut cx)? {
                debug_assert!(
                    (self.queue.waiting(i))
                        .is_none_or(|needs| ready(&self.globals, &needs).unwrap_or(true)),
                    "a default solves what its item waits on"
                );
                count(&DEFAULTED);
                return Ok(true);
            }
            snapshot.restore(&mut cx);
        }
        Ok(false)
    }

    /// Ladder step 4: the items still waiting, reported by independent root
    /// (§5.9). An item depends on another if it waits on that one's
    /// placeholder or on the unknown that is its type; items so linked, or
    /// waiting on the same unknown, are one group. Each group is reported
    /// once, by its first item, in creation order, that depends on no
    /// waiting item; the first group's error is returned, and the next two
    /// go where a failing definition reports more errors after its own
    /// (`branch_errors`). The rest are taken as consequences.
    fn stuck_report(&self) -> Result<Option<Diagnostic>> {
        let g = &self.globals;
        let mut waiting: Vec<(usize, Option<usize>)> = Vec::new();
        for i in 0..self.queue.len() {
            if let Some(needs) = self.queue.waiting(i) {
                waiting.push((i, head_meta(g, &needs)?));
            }
        }
        if waiting.is_empty() {
            return Ok(None);
        }
        STUCK.fetch_add(waiting.len(), Ordering::Relaxed);
        // The waiting item each unknown is the placeholder or the type of.
        let mut made_by: HashMap<usize, usize> = HashMap::default();
        for (w, &(i, _)) in waiting.iter().enumerate() {
            let item = self.queue.item(i);
            if !item.constraint {
                made_by.insert(item.meta, w);
            }
            if let Some(m) = head_meta(g, &item.ty)? {
                made_by.entry(m).or_insert(w);
            }
        }
        let mut group: Vec<usize> = (0..waiting.len()).collect();
        fn find(group: &mut [usize], mut w: usize) -> usize {
            while group[w] != w {
                group[w] = group[group[w]];
                w = group[w];
            }
            w
        }
        let mut depends = vec![false; waiting.len()];
        let mut first_on: HashMap<usize, usize> = HashMap::default();
        for (w, &(_, blocker)) in waiting.iter().enumerate() {
            let Some(blocker) = blocker else { continue };
            let mut join = |other: usize| {
                let (a, b) = (find(&mut group, w), find(&mut group, other));
                group[a.max(b)] = a.min(b);
            };
            if let Some(&other) = made_by.get(&blocker)
                && other != w
            {
                depends[w] = true;
                join(other);
            }
            join(*first_on.entry(blocker).or_insert(w));
        }
        // Each group's report, in the order of its first item.
        let mut reports: Vec<(usize, usize)> = Vec::new();
        for w in 0..waiting.len() {
            let root = find(&mut group, w);
            match reports.iter_mut().find(|(r, _)| *r == root) {
                Some(report) if depends[report.1] && !depends[w] => report.1 = w,
                Some(_) => {}
                None => reports.push((root, w)),
            }
        }
        let mut errors =
            (reports.iter()).map(|&(_, w)| self.queue.item(waiting[w].0).error.clone());
        let first = errors.next();
        self.branch_errors.borrow_mut().extend(errors.take(2));
        Ok(first)
    }
}

static QUEUED: AtomicUsize = AtomicUsize::new(0);
static RESUMED: AtomicUsize = AtomicUsize::new(0);
static DEFAULTED: AtomicUsize = AtomicUsize::new(0);
static STUCK: AtomicUsize = AtomicUsize::new(0);
static CROSSED: AtomicUsize = AtomicUsize::new(0);
static SOLVED_FIRST: AtomicUsize = AtomicUsize::new(0);
static LOSSY: AtomicUsize = AtomicUsize::new(0);
static DISAGREED: AtomicUsize = AtomicUsize::new(0);
static READ_BACK: AtomicUsize = AtomicUsize::new(0);
static REQUEUED: AtomicUsize = AtomicUsize::new(0);
static KEPT: AtomicUsize = AtomicUsize::new(0);
static KEPT_CHOSE: AtomicUsize = AtomicUsize::new(0);
static LAMBDA_POSTPONED: AtomicUsize = AtomicUsize::new(0);
static RETRIED: AtomicUsize = AtomicUsize::new(0);
static WAITED: AtomicUsize = AtomicUsize::new(0);

/// A lambda argument tried in place, failed, and checked again after the
/// application's later arguments (`check::apply_args_postponing`): the
/// path §5.11 removes once its count is 0 in accepted code.
pub(crate) fn note_lambda_postponed() {
    count(&LAMBDA_POSTPONED);
}

/// An application, group, list or `if` elaborated a second time with number
/// literals checked last (`check::retrying`), because the first time failed:
/// the path §5.11 removes once number literals wait (K4).
pub(crate) fn note_retried() {
    count(&RETRIED);
}

fn count(counter: &AtomicUsize) {
    counter.fetch_add(1, Ordering::Relaxed);
}

/// Invariant 6 for a `.field` whose receiver is kept as a term (K2,
/// docs/proposals/postponement.md §5.5): the receiver, elaborated since
/// `before`, made none of the choices of §5.10 from an unknown's shape that
/// a type known later could make otherwise: no number literal made `Nat`
/// at once (`numbers::Defaulted`), and no operator left with a generic
/// dictionary. Counted (`kept`, and `kept chose` for one that did), and
/// asserted in a debug build.
pub(crate) fn kept_receiver(cx: &Ctx, before: &crate::undo::Snapshot) {
    count(&KEPT);
    let defaulted = cx.e.defaulted.borrow().len() > before.defaulted();
    let generic = (cx.e.operator_dictionaries.borrow().keys()).any(|&m| m >= before.metas());
    if defaulted || generic {
        count(&KEPT_CHOSE);
    }
    debug_assert!(
        !defaulted && !generic,
        "a receiver kept as a term chose from an unknown (invariant 6)"
    );
}

/// The queue's counters over the process, attempts undone included, for
/// `STITCHWORT_TIMINGS` (`timings.rs`) and the stages after this one
/// (docs/proposals/postponement.md, "As built (stage 1)" to "(stage 3)"):
/// items queued, resumed, defaulted and reported stuck; items that reached
/// the end of their application still waiting (`crossed W1`, the stage-6
/// trigger); comparisons that failed at an unfilled placeholder (`met
/// unfilled`, its other half, `unify::met_unfilled`); fills whose
/// placeholder unification had solved first (`solved first`), and of
/// those, solved by comparing two calls' arguments (`lossy`, the caveat to
/// D2016's P1); fills that disagreed with that solution; fills whose term
/// couldn't be written as a call of the placeholder, so zonking reads the
/// solution back (`read back`); resumptions that met another unknown and
/// waited again (`requeued`); and `.field`s queued with their receiver
/// kept as a term (`kept`), of which those whose receiver made a choice
/// from an unknown (`kept chose`, invariant 6; 0 expected); and lambda
/// arguments tried in place, failed and checked again after the later
/// arguments (`lambda postponed`, the path §5.11 removes in stage 5); and
/// elaborations run a second time with number literals last (`retried`,
/// `check::retrying`, which K4 makes unneeded); and comparisons queued to
/// wait for unknowns the queue still has to settle (`waited`, stage 6).
pub fn counts() -> [(&'static str, usize); 16] {
    let get = |c: &AtomicUsize| c.load(Ordering::Relaxed);
    [
        ("queued", get(&QUEUED)),
        ("resumed", get(&RESUMED)),
        ("defaulted", get(&DEFAULTED)),
        ("stuck", get(&STUCK)),
        ("crossed W1", get(&CROSSED)),
        ("met unfilled", crate::unify::met_unfilled()),
        ("solved first", get(&SOLVED_FIRST)),
        ("lossy", get(&LOSSY)),
        ("disagreed", get(&DISAGREED)),
        ("read back", get(&READ_BACK)),
        ("requeued", get(&REQUEUED)),
        ("kept", get(&KEPT)),
        ("kept chose", get(&KEPT_CHOSE)),
        ("lambda postponed", get(&LAMBDA_POSTPONED)),
        ("retried", get(&RETRIED)),
        ("waited", get(&WAITED)),
    ]
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use stitchwort_core::{DataId, DefId, Sort};
    use stitchwort_syntax::ast::Expr;
    use stitchwort_syntax::{SourceMap, Span};

    use super::*;
    use crate::undo::Snapshot;

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    fn ty(n: u32) -> Value {
        Value::Sort(Sort::Type(n))
    }

    fn anything() -> Term {
        Term::Sort(Sort::Type(0))
    }

    /// A fresh unknown, standing for a value that depends on nothing.
    fn unknown(cx: &Ctx) -> (usize, Value) {
        let m = cx.g().new_meta(cx.span);
        (m, Value::Neutral(Head::Meta(m), Default::default()))
    }

    /// What the probes did, in order.
    type Log = Rc<RefCell<Vec<String>>>;

    /// An item made by hand: resumed, it notes so, elaborates `inner` if
    /// there is one, and gives `term`; its default, if it has one, solves
    /// the unknown given with `Type`.
    struct Probe {
        name: &'static str,
        log: Log,
        term: Term,
        inner: Option<Expr>,
        default: Option<(Priority, usize)>,
        /// Whether its check reaches a resume point whose scope holds the
        /// item itself, which none may.
        nested: bool,
        /// What it waits on next, the first time it is resumed (a `.field`
        /// meeting another unknown at a later step of its view).
        then: RefCell<Option<Value>>,
    }

    impl Check for Probe {
        fn resume(&self, cx: &mut Ctx) -> Result<Resumed> {
            self.log.borrow_mut().push(format!("resumed {}", self.name));
            if let Some(inner) = &self.inner {
                crate::check::infer(cx, inner)?;
            }
            if self.nested {
                cx.e.resume_from(0)?;
            }
            if let Some(next) = self.then.take() {
                return Ok(Resumed::Waiting(next));
            }
            Ok(Resumed::Done(self.term.clone()))
        }

        fn default_priority(&self) -> Option<Priority> {
            self.default.map(|(p, _)| p)
        }

        fn apply_default(&self, cx: &mut Ctx) -> Result<bool> {
            let Some((_, blocker)) = self.default else {
                return Ok(false);
            };
            self.log.borrow_mut().push(format!("default {}", self.name));
            cx.g().solve_meta(blocker, ty(0));
            Ok(true)
        }
    }

    fn probe(name: &'static str, log: &Log, term: Term) -> Probe {
        Probe {
            name,
            log: log.clone(),
            term,
            inner: None,
            default: None,
            nested: false,
            then: RefCell::new(None),
        }
    }

    fn error(name: &str) -> Diagnostic {
        Diagnostic::error("E-CANNOT-INFER", name).with_label(span(), "here")
    }

    /// Queues `probe`, waiting on `needs`, with a placeholder of a fresh
    /// unknown type: the placeholder's term.
    fn push(cx: &Ctx, probe: Probe, needs: Value) -> Term {
        let (_, result) = unknown(cx);
        let error = error(probe.name);
        queue(cx, Rc::new(probe), needs, result, error).expect("queued")
    }

    fn meta_of(placeholder: &Term) -> usize {
        match placeholder.spine().0 {
            Term::Meta(m) => *m,
            _ => unreachable!("a placeholder"),
        }
    }

    fn waiting(e: &Elaborator, i: usize) -> bool {
        matches!(e.queue.state(i), State::Waiting(..))
    }

    fn done(e: &Elaborator, i: usize) -> bool {
        matches!(e.queue.state(i), State::Done)
    }

    fn expression(text: &str) -> Expr {
        let mut sources = SourceMap::new();
        let file = sources.add("test", text);
        stitchwort_syntax::parse_expression(file, text).expect("parses")
    }

    /// Invariants 1 and 5: an item queued inside an attempt that is undone
    /// leaves no item and no placeholder, and queueing it again makes a new
    /// one. A resumption inside an attempt undone is taken back, with its
    /// fill: the item is waiting again, and its placeholder unsolved.
    #[test]
    fn restoring_takes_back_items_resumptions_and_fills() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let before = Snapshot::take(&cx);
        let (_, needs) = unknown(&cx);
        let first = push(&cx, probe("a", &log, anything()), needs);
        assert_eq!(e.queue.len(), 1);
        before.restore(&mut cx);
        assert_eq!(e.queue.len(), 0);
        assert!(e.globals.metas.borrow().len() <= meta_of(&first));
        // Again: a new item, with its own placeholder.
        let (blocker, needs) = unknown(&cx);
        let again = push(&cx, probe("a", &log, anything()), needs);
        assert_eq!(e.queue.len(), 1);
        let placeholder = meta_of(&again);
        // Resumed inside an attempt that is then undone.
        let attempt = Snapshot::take(&cx);
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert!(e.globals.lifted_calls.borrow().contains_key(&placeholder));
        assert!(e.globals.meta_solution(placeholder).is_some());
        attempt.restore(&mut cx);
        assert!(waiting(&e, 0));
        assert_eq!(e.queue.resumptions(0), 0);
        assert!(!e.globals.lifted_calls.borrow().contains_key(&placeholder));
        assert!(e.globals.meta_solution(placeholder).is_none());
        assert_eq!(e.queue.len(), 1);
        // Resumed again, for good.
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.queue.resumptions(0), 1);
        assert_eq!(*log.borrow(), ["resumed a", "resumed a"]);
    }

    /// Invariant 5: the queue is per declaration, and a session rewound
    /// has none.
    #[test]
    fn clearing_and_rewinding_empty_the_queue() {
        let mut e = Elaborator::new();
        let mark = e.mark();
        let log = Log::default();
        {
            let cx = Ctx::new(&e, span());
            let (_, needs) = unknown(&cx);
            push(&cx, probe("a", &log, anything()), needs);
        }
        assert_eq!(e.queue.len(), 1);
        e.rewind(&mark);
        assert_eq!(e.queue.len(), 0);
        {
            let cx = Ctx::new(&e, span());
            let (_, needs) = unknown(&cx);
            push(&cx, probe("b", &log, anything()), needs);
        }
        e.clear_metas();
        assert_eq!(e.queue.len(), 0);
        assert!(e.queue.log.borrow().is_empty());
    }

    /// States: an item resumed that meets another unknown waits again, on
    /// that one, and is resumed once that is solved too; what it waits on
    /// is what the stuck report goes by meanwhile.
    #[test]
    fn an_item_that_meets_another_unknown_waits_again() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (first, needs) = unknown(&cx);
        let (second, next) = unknown(&cx);
        let a = probe("a", &log, anything());
        *a.then.borrow_mut() = Some(next);
        push(&cx, a, needs);
        e.globals.solve_meta(first, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(waiting(&e, 0));
        assert!(!e.resume_from(0).unwrap());
        e.globals.solve_meta(second, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.queue.resumptions(0), 2);
    }

    /// Invariant 4: an item whose check contains an application is resumed
    /// once. The application's end (W1) sees only what was queued inside
    /// it, which the running item wasn't.
    #[test]
    fn an_item_whose_check_has_an_application_is_resumed_once() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, needs) = unknown(&cx);
        let mut a = probe("a", &log, anything());
        a.inner = Some(expression("((x: Type 1) => x) Type"));
        push(&cx, a, needs);
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.queue.resumptions(0), 1);
        assert_eq!(*log.borrow(), ["resumed a"]);
    }

    /// Invariant 4: a resume point whose scope holds a running item, which
    /// none may (T3). A debug build's assertion says so; in a release build
    /// the item still isn't selected again.
    #[test]
    #[cfg_attr(debug_assertions, should_panic(expected = "running item"))]
    fn a_running_item_is_never_selected_again() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, needs) = unknown(&cx);
        let mut a = probe("a", &log, anything());
        a.nested = true;
        push(&cx, a, needs);
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert_eq!(e.queue.resumptions(0), 1);
        assert_eq!(*log.borrow(), ["resumed a"]);
    }

    /// Invariant 3: the end of an application resumes the items queued
    /// while it was elaborated, not one queued before it began, even when
    /// that one's blocker is solved by then.
    #[test]
    fn the_end_of_an_application_resumes_only_its_own_items() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let (outer_blocker, needs) = unknown(&cx);
        push(&cx, probe("outer", &log, anything()), needs);
        e.globals.solve_meta(outer_blocker, ty(1));
        // An application elaborated now ends with a resume point, for what
        // it queued: nothing.
        crate::check::infer(&mut cx, &expression("((x: Type 1) => x) Type")).unwrap();
        assert!(waiting(&e, 0));
        // One queued inside an application that began after `outer` was.
        let start = e.queue.len();
        let (inner_blocker, needs) = unknown(&cx);
        push(&cx, probe("inner", &log, anything()), needs);
        e.globals.solve_meta(inner_blocker, ty(1));
        e.resume_application(start).unwrap();
        assert!(waiting(&e, 0));
        assert!(done(&e, 1));
        // The end of the application `outer` was queued in.
        e.resume_application(0).unwrap();
        assert!(done(&e, 0));
        assert_eq!(*log.borrow(), ["resumed inner", "resumed outer"]);
    }

    /// Invariant 7 and D2013: defaults only at the end (W4), one at a time,
    /// by priority before creation order, each followed by resuming.
    #[test]
    fn defaults_apply_one_at_a_time_field_names_before_nat() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (n, needs) = unknown(&cx);
        let mut number = probe("number", &log, anything());
        number.default = Some((Priority::Nat, n));
        push(&cx, number, needs);
        let (r, needs) = unknown(&cx);
        let mut record = probe("record", &log, anything());
        record.default = Some((Priority::FieldNames, r));
        push(&cx, record, needs);
        // No other resume point applies a default.
        e.resume_application(0).unwrap();
        assert!(!e.resume_from(0).unwrap());
        e.resume_before_lifting().unwrap();
        assert!(log.borrow().is_empty());
        assert!(e.settle_queue().unwrap().is_none());
        assert_eq!(
            *log.borrow(),
            [
                "default record",
                "resumed record",
                "default number",
                "resumed number"
            ]
        );
    }

    /// §5.9: what still waits at the end is reported once per independent
    /// root, at most three. `b` waits on `a`'s placeholder and `c` on `b`'s
    /// type, so of those only `a` is reported; `d`, `e`, `f` and `g` are
    /// independent, and only `d` and `e` fit.
    #[test]
    fn stuck_items_are_reported_by_root_at_most_three() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (_, needs) = unknown(&cx);
        let a = push(&cx, probe("a", &log, anything()), needs);
        let (b_type, b_ty) = unknown(&cx);
        let on_a = cx.eval(&a).unwrap();
        queue(
            &cx,
            Rc::new(probe("b", &log, anything())),
            on_a,
            b_ty,
            error("b"),
        )
        .unwrap();
        let on_b = Value::Neutral(Head::Meta(b_type), Default::default());
        push(&cx, probe("c", &log, anything()), on_b);
        for name in ["d", "e", "f", "g"] {
            let (_, needs) = unknown(&cx);
            push(&cx, probe(name, &log, anything()), needs);
        }
        let reported = e.settle_queue().expect_err("stuck");
        assert_eq!(reported.message, "a");
        let more: Vec<String> = (e.branch_errors.borrow().iter())
            .map(|d| d.message.clone())
            .collect();
        assert_eq!(more, ["d", "e"]);
        assert!(log.borrow().is_empty());
    }

    /// A context at a span of its own, to tell the item's span from others.
    fn at_span() -> Span {
        let mut sources = SourceMap::new();
        let file = sources.add("test", "items here");
        Span::new(file, 6, 10)
    }

    /// Invariant 2 and D2016's end state (stage 6): unification can't solve
    /// a placeholder its item hasn't filled, which is frozen. If anything
    /// else has solved it, a fill with a term not equal to that solution is
    /// the item's mismatch, at the item's own span (the fill's guard).
    #[test]
    fn a_fill_that_disagrees_with_unification_is_the_items_error() {
        let (e, n, two, _) = numbers();
        let at = at_span();
        let cx = Ctx::new(&e, at);
        let log = Log::default();
        let (blocker, needs) = unknown(&cx);
        let placeholder = push(&cx, probe("a", &log, Term::Def(two)), needs);
        let solved = cx.eval(&placeholder).unwrap();
        let zero = cx.eval(&Term::ctor(n, 0, Vec::new())).unwrap();
        assert!(!cx.unify(&solved, &zero).unwrap(), "frozen until filled");
        e.globals.solve_meta(meta_of(&placeholder), zero);
        e.globals.solve_meta(blocker, ty(1));
        let disagreed = DISAGREED.load(Ordering::Relaxed);
        let error = e.resume_from(0).expect_err("disagrees");
        assert_eq!(error.code, "E-TYPE-MISMATCH");
        assert_eq!(error.labels[0].span, at);
        assert!(matches!(e.queue.state(0), State::Failed));
        assert!(DISAGREED.load(Ordering::Relaxed) > disagreed);
    }

    const NUMBERS: &str = "type N: Type =\n  | Z\n  | S (n: N)\n\n\
        def two: N := S (S Z)\n\n\
        def pred: N → N → N\n  | Z, b => Z\n  | S a, b => a\n";

    /// [`NUMBERS`] elaborated, with no library, and the elaborator glued,
    /// as while a declaration is checked.
    fn numbers() -> (Elaborator, DataId, DefId, DefId) {
        let mut sources = SourceMap::new();
        let file = sources.add("test", NUMBERS);
        let module = stitchwort_syntax::parse_module(file, NUMBERS).expect("parses");
        let mut e = Elaborator::new();
        // As the prelude, which needn't have every built-in.
        e.loading_prelude = true;
        let errors: Vec<_> = (e.elaborate_module(&module).into_iter())
            .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "{errors:#?}");
        e.loading_prelude = false;
        e.globals.glue.set(true);
        let n = DataId(
            (e.globals.datas.iter())
                .position(|d| d.path.rsplit('.').next() == Some("N"))
                .expect("N"),
        );
        let def = |name: &str| {
            let found =
                (e.globals.defs.iter()).position(|d| d.path.rsplit('.').next() == Some(name));
            DefId(found.unwrap_or_else(|| panic!("{name} defined")))
        };
        let (two, pred) = (def("two"), def("pred"));
        (e, n, two, pred)
    }

    /// Invariant 2: a placeholder solved with a value before its item
    /// fills it (by nothing but a direct solution: unification can't, as it
    /// is frozen), filled with a term equal to that value, zonks to the
    /// item's term, a call kept folded: `two`, not `S (S Z)` (the
    /// `Day06.offRouteFree` case of §6.3).
    #[test]
    fn a_filled_placeholder_zonks_to_the_items_term() {
        let (e, _, two, _) = numbers();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, needs) = unknown(&cx);
        let placeholder = push(&cx, probe("a", &log, Term::Def(two)), needs);
        // Solved first, with `S (S Z)`.
        let unfolded = cx.quote(&cx.eval(&Term::Def(two)).unwrap()).unwrap();
        assert!(!matches!(unfolded.strip_loc(), Term::Def(_)));
        let solved = cx.eval(&placeholder).unwrap();
        let value = cx.eval(&unfolded).unwrap();
        assert!(!cx.unify(&solved, &value).unwrap(), "frozen until filled");
        e.globals.solve_meta(meta_of(&placeholder), value);
        e.globals.solve_meta(blocker, ty(1));
        let first = SOLVED_FIRST.load(Ordering::Relaxed);
        assert!(e.resume_from(0).unwrap());
        assert!(SOLVED_FIRST.load(Ordering::Relaxed) > first);
        let zonked = crate::unify::zonk_in(cx.g(), 0, &placeholder, &|_| false, &[]).unwrap();
        assert!(
            matches!(zonked.strip_loc(), Term::Def(d) if *d == two),
            "{zonked:?}"
        );
    }

    /// Invariant 2: the item's term is written in the variables its
    /// placeholder is applied to, wherever it is: `?p x y` filled with
    /// `S y` zonks to `S y`, and to `S two` applied to `Z` and `two`.
    #[test]
    fn a_filled_placeholder_is_its_term_in_the_arguments_it_is_given() {
        let (e, n, two, _) = numbers();
        let mut cx = Ctx::new(&e, span());
        cx.bind("x", Value::Data(n, Vec::new()));
        cx.bind("y", Value::Data(n, Vec::new()));
        let log = Log::default();
        let succ = |t: Term| Term::ctor(n, 1, vec![t]);
        let (blocker, needs) = unknown(&cx);
        let placeholder = push(&cx, probe("a", &log, succ(Term::Var(0))), needs);
        assert_eq!(placeholder.spine().1.len(), 2);
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        let zonk = |t: &Term, level| crate::unify::zonk_in(cx.g(), level, t, &|_| false, &[]);
        let here = zonk(&placeholder, 2).unwrap();
        assert_eq!(format!("{here:?}"), format!("{:?}", succ(Term::Var(0))));
        let p = Term::Meta(meta_of(&placeholder));
        let zero = Term::ctor(n, 0, Vec::new());
        let elsewhere = Term::app(Term::app(p, zero), Term::Def(two));
        let there = zonk(&elsewhere, 0).unwrap();
        assert_eq!(format!("{there:?}"), format!("{:?}", succ(Term::Def(two))));
    }

    /// The caveat to D2016's P1, gone with stage 6: comparing two calls of a
    /// definition stuck on an unknown compares their arguments, which for a
    /// definition that isn't injective guesses. `pred` ignores its second
    /// argument; with `x` a variable, `pred x ?p` against `pred x Z` (both
    /// stuck on `x`) used to solve the placeholder `?p` with `Z`, a guess
    /// the fill then disagreed with. Frozen, the placeholder is never
    /// guessed: the comparison fails, or, tri-state, waits for it; its item
    /// then fills it with `two`, with no disagreement.
    #[test]
    fn a_frozen_placeholder_is_never_guessed_by_comparing_calls() {
        let (e, n, two, pred) = numbers();
        let mut cx = Ctx::new(&e, at_span());
        cx.bind("x", Value::Data(n, Vec::new()));
        let log = Log::default();
        let (blocker, needs) = unknown(&cx);
        let placeholder = push(&cx, probe("a", &log, Term::Def(two)), needs);
        let p = meta_of(&placeholder);
        let zero = Term::ctor(n, 0, Vec::new());
        let call = |t: Term| {
            let applied = Term::app(Term::app(Term::Def(pred), Term::Var(0)), t);
            cx.eval(&applied).unwrap()
        };
        let (a, b) = (call(placeholder.clone()), call(zero));
        assert!(!cx.unify(&a, &b).unwrap());
        assert!(cx.g().meta_solution(p).is_none());
        let pending = pending(&cx).unwrap();
        assert!(pending.contains(&p));
        let answer = crate::unify::unify_waiting(cx.g(), 1, &a, &b, &pending).unwrap();
        assert!(matches!(answer, Answer::Blocked(ref pairs) if pairs.len() == 1));
        assert!(cx.g().meta_solution(p).is_none());
        e.globals.solve_meta(blocker, ty(1));
        let lossy = LOSSY.load(Ordering::Relaxed);
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(LOSSY.load(Ordering::Relaxed), lossy);
    }

    /// Stage 6: an item `a` of type `N` whose term is `term`, waiting on a
    /// fresh unknown (its blocker, returned), in `cx`; and its placeholder's
    /// value.
    fn waiting_item(cx: &Ctx, log: &Log, term: Term) -> (usize, Value) {
        let (blocker, needs) = unknown(cx);
        let placeholder = push(cx, probe("a", log, term), needs);
        (blocker, cx.eval(&placeholder).unwrap())
    }

    /// Stage 6: a comparison that fails only at an unfilled placeholder
    /// waits, as a queued comparison, instead of failing; it is woken once
    /// the placeholder is filled, after its item, and holds.
    #[test]
    fn a_comparison_on_a_placeholder_waits_and_holds_once_it_is_filled() {
        let (e, _, two, _) = numbers();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, placeholder) = waiting_item(&cx, &log, Term::Def(two));
        let value = cx.eval(&Term::Def(two)).unwrap();
        let waited = WAITED.load(Ordering::Relaxed);
        assert!(compare_waiting(&mut cx, &placeholder, &value, Failure::Mismatch).unwrap());
        assert_eq!(e.queue.len(), 2);
        assert!(waiting(&e, 1));
        assert!(WAITED.load(Ordering::Relaxed) > waited);
        // Nothing solved yet: neither resumes.
        assert!(!e.resume_from(0).unwrap());
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0) && done(&e, 1));
        assert_eq!(*log.borrow(), ["resumed a"]);
    }

    /// Stage 6: a side that is a call stuck on the placeholder, `pred ?p Z`
    /// against `S Z`, computes once the placeholder is filled with `two`:
    /// the comparison is made again on its sides evaluated afresh, not on
    /// the stuck values it began waiting with.
    #[test]
    fn a_waiting_comparison_computes_its_sides_again() {
        let (e, n, two, pred) = numbers();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, placeholder) = waiting_item(&cx, &log, Term::Def(two));
        let ph = cx.quote(&placeholder).unwrap();
        let zero = Term::ctor(n, 0, Vec::new());
        let stuck = Term::app(Term::app(Term::Def(pred), ph), zero.clone());
        let stuck = cx.eval(&stuck).unwrap();
        let one = cx.eval(&Term::ctor(n, 1, vec![zero])).unwrap();
        assert!(compare_waiting(&mut cx, &stuck, &one, Failure::Mismatch).unwrap());
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0) && done(&e, 1));
    }

    /// Stage 6: a waiting comparison that the filled placeholder makes
    /// false fails with its caller's error, at its own span, against the
    /// types now known (§5.9); `rfl`'s is `E-REFL`.
    #[test]
    fn a_waiting_comparison_that_fails_reports_its_callers_error() {
        let (e, n, two, _) = numbers();
        let at = at_span();
        let mut cx = Ctx::new(&e, at);
        let log = Log::default();
        let (blocker, placeholder) = waiting_item(&cx, &log, Term::Def(two));
        let zero = cx.eval(&Term::ctor(n, 0, Vec::new())).unwrap();
        assert!(compare_waiting(&mut cx, &placeholder, &zero, Failure::Refl).unwrap());
        e.globals.solve_meta(blocker, ty(1));
        let error = e.resume_from(0).expect_err("two isn't zero");
        assert_eq!(error.code, "E-REFL");
        assert_eq!(error.labels[0].span, at);
        assert!(done(&e, 0));
        assert!(matches!(e.queue.state(1), State::Failed));
    }

    /// Stage 6: a rigid mismatch doesn't wait, and nothing it solved is
    /// kept; with nothing queued, nothing waits either.
    #[test]
    fn a_comparison_that_can_never_hold_does_not_wait() {
        let (e, n, two, _) = numbers();
        let mut cx = Ctx::new(&e, span());
        let zero = cx.eval(&Term::ctor(n, 0, Vec::new())).unwrap();
        let two = cx.eval(&Term::Def(two)).unwrap();
        assert!(!compare_waiting(&mut cx, &two, &zero, Failure::Mismatch).unwrap());
        assert_eq!(e.queue.len(), 0);
        let log = Log::default();
        let (_, placeholder) = waiting_item(&cx, &log, anything());
        let (x, unknown_value) = unknown(&cx);
        let a = Value::Eq(
            Rc::new(ty(0)),
            Rc::new(unknown_value),
            Rc::new(zero.clone()),
        );
        let b = Value::Eq(Rc::new(ty(0)), Rc::new(placeholder), Rc::new(two));
        assert!(!compare_waiting(&mut cx, &a, &b, Failure::Mismatch).unwrap());
        assert_eq!(e.queue.len(), 1);
        assert!(cx.g().meta_solution(x).is_none(), "undone");
    }

    /// Stage 6 and invariant 5: a waiting comparison made inside an attempt
    /// that is undone goes with it; one woken there is waiting again after.
    #[test]
    fn restoring_takes_back_a_waiting_comparison() {
        let (e, _, two, _) = numbers();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, placeholder) = waiting_item(&cx, &log, Term::Def(two));
        let value = cx.eval(&Term::Def(two)).unwrap();
        let before = Snapshot::take(&cx);
        assert!(compare_waiting(&mut cx, &placeholder, &value, Failure::Mismatch).unwrap());
        assert_eq!(e.queue.len(), 2);
        before.restore(&mut cx);
        assert_eq!(e.queue.len(), 1);
        assert!(compare_waiting(&mut cx, &placeholder, &value, Failure::Mismatch).unwrap());
        let woken = Snapshot::take(&cx);
        e.globals.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 1));
        woken.restore(&mut cx);
        assert!(waiting(&e, 0) && waiting(&e, 1));
    }

    /// Stage 6 and §5.9: a comparison still waiting at the end waits on a
    /// stuck item's placeholder, so the item is the root that is reported,
    /// and the comparison is a consequence.
    #[test]
    fn a_stuck_comparison_is_reported_through_the_item_it_waits_on() {
        let (e, _, two, _) = numbers();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let (_, placeholder) = waiting_item(&cx, &log, Term::Def(two));
        let value = cx.eval(&Term::Def(two)).unwrap();
        assert!(compare_waiting(&mut cx, &placeholder, &value, Failure::Refl).unwrap());
        let reported = e.settle_queue().expect_err("stuck");
        assert_eq!(reported.message, "a");
        assert!(e.branch_errors.borrow().is_empty());
    }

    /// Records and a type-level identity for the K1 and K2 tests: `P` and
    /// `Q` have the same field, `Only` is the one record with `only`.
    const RECORDS: &str = "type N: Type =\n  | Z\n  | S (n: N)\n\n\
        type P = { row: N }\n\n\
        type Q = { row: N }\n\n\
        type Only = { only: N }\n\n\
        def Id (a: Type): Type := a\n";

    /// `source` elaborated, with no library, glued as while a declaration
    /// is checked; and a type's value by its short name.
    fn module(source: &str) -> (Elaborator, impl Fn(&Elaborator, &str) -> Value) {
        let mut sources = SourceMap::new();
        let file = sources.add("test", source);
        let module = stitchwort_syntax::parse_module(file, source).expect("parses");
        let mut e = Elaborator::new();
        e.loading_prelude = true;
        let errors: Vec<_> = (e.elaborate_module(&module).into_iter())
            .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "{errors:#?}");
        // Still as the prelude, so that its names are in scope by their
        // short names, as in a declaration after them.
        e.globals.glue.set(true);
        let data = |e: &Elaborator, name: &str| {
            let d = (e.globals.datas.iter())
                .position(|d| d.path.rsplit('.').next() == Some(name))
                .unwrap_or_else(|| panic!("{name} declared"));
            Value::Data(DataId(d), Vec::new())
        };
        (e, data)
    }

    fn zonked(cx: &Ctx, term: &Term) -> String {
        let zonked = crate::unify::zonk_in(cx.g(), cx.level(), term, &|_| false, &[]).unwrap();
        format!("{:?}", zonked.strip_loc())
    }

    /// K1: a record literal whose type is unknown waits (no
    /// `E-CANNOT-INFER`, though `P` and `Q` both have its field), and once
    /// the type is known is checked at it: its placeholder zonks to the
    /// literal of that type.
    #[test]
    fn a_record_literal_waits_for_its_type() {
        let (e, data) = module(RECORDS);
        let mut cx = Ctx::new(&e, span());
        let (term, ty) = crate::check::infer(&mut cx, &expression("{ row = Z }")).unwrap();
        assert_eq!(e.queue.len(), 1);
        assert!(waiting(&e, 0));
        assert!(head_meta(cx.g(), &ty).unwrap().is_some());
        assert!(cx.unify(&ty, &data(&e, "Q")).unwrap());
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        let Value::Data(q, _) = data(&e, "Q") else {
            unreachable!()
        };
        assert!(
            zonked(&cx, &term).starts_with(&format!("Ctor({q:?}, 0")),
            "{}",
            zonked(&cx, &term)
        );
    }

    /// K1's default (D2013): at the end, the one record type with exactly
    /// the literal's fields; where there are two, nothing is chosen and the
    /// literal is reported with the field-name rule's error.
    #[test]
    fn a_record_literal_takes_its_field_names_type_only_at_the_end() {
        let (e, data) = module(RECORDS);
        let mut cx = Ctx::new(&e, span());
        let (_, ty) = crate::check::infer(&mut cx, &expression("{ only = Z }")).unwrap();
        // Not at an application's end, nor before lifting.
        e.resume_application(0).unwrap();
        e.resume_before_lifting().unwrap();
        assert!(waiting(&e, 0));
        assert!(e.settle_queue().unwrap().is_none());
        assert!(done(&e, 0));
        assert!(cx.conv_now(&ty, &data(&e, "Only")).unwrap());
        e.clear_metas();
        let mut cx = Ctx::new(&e, span());
        crate::check::infer(&mut cx, &expression("{ row = Z }")).unwrap();
        let error = e.settle_queue().expect_err("two types have `row`");
        assert_eq!(error.code, "E-CANNOT-INFER");
        assert!(
            (error.notes.iter()).any(|n| n.contains("more than one record type")),
            "{error:?}"
        );
    }

    /// K2 with the blocker made before the receiver (a variable's type):
    /// the receiver is kept as syntax, and the call is elaborated from the
    /// start once the type is known, to the projection applied to `p`.
    #[test]
    fn a_field_on_a_variable_of_unknown_type_waits_as_syntax() {
        let (e, data) = module(RECORDS);
        let mut cx = Ctx::new(&e, span());
        let (blocker, ty) = unknown(&cx);
        cx.bind("p", ty);
        let metas = e.globals.metas.borrow().len();
        let (term, _) = crate::check::infer(&mut cx, &expression("p.row")).unwrap();
        assert_eq!(e.queue.len(), 1);
        // What inferring the receiver made was undone: the item's
        // placeholder and its type are all that is new.
        assert_eq!(e.globals.metas.borrow().len(), metas + 2);
        assert_eq!(
            head_meta(cx.g(), &e.queue.waiting(0).unwrap()).unwrap(),
            Some(blocker)
        );
        e.globals.solve_meta(blocker, data(&e, "P"));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        let text = zonked(&cx, &term);
        assert!(
            text.starts_with("App(Def(") && text.contains("Var(0)"),
            "{text}"
        );
    }

    /// K2 with the blocker made by the receiver (a record literal waiting,
    /// K1): the receiver's term is kept, the `.row` waits on the literal's
    /// type, and the literal's default lets both finish.
    #[test]
    fn a_field_on_a_waiting_literal_keeps_the_literal() {
        let (e, _) = module(RECORDS);
        let mut cx = Ctx::new(&e, span());
        let kept = KEPT.load(Ordering::Relaxed);
        crate::check::infer(&mut cx, &expression("({ only = Z }).only")).unwrap();
        // The literal, and the `.only` on it; the literal queued while the
        // prefix form was tried was undone with it.
        assert_eq!(e.queue.len(), 2);
        assert!(KEPT.load(Ordering::Relaxed) > kept);
        assert!(e.settle_queue().unwrap().is_none());
        assert!(done(&e, 0) && done(&e, 1));
    }

    /// K2 resumed that meets another unknown (§5.7, T4's second measure)
    /// waits again, on that one: `p : ?A z`, a `.row` waiting on `?A`; then
    /// `?A` is solved as `z => ?B`, so `p`'s type is `?B`, still unknown.
    #[test]
    fn a_field_meeting_another_unknown_waits_again() {
        let (e, data) = module(RECORDS);
        let mut cx = Ctx::new(&e, span());
        cx.bind("z", data(&e, "N"));
        let applied = cx.fresh_meta();
        let Term::Meta(first) = *applied.spine().0 else {
            unreachable!("a fresh metavariable")
        };
        cx.bind("p", cx.eval(&applied).unwrap());
        crate::check::infer(&mut cx, &expression("p.row")).unwrap();
        assert_eq!(
            head_meta(cx.g(), &e.queue.waiting(0).unwrap()).unwrap(),
            Some(first)
        );
        let (second, b) = unknown(&cx);
        let mut outer = Ctx::new(&e, span());
        outer.bind("z", data(&e, "N"));
        assert!(outer.unify(&outer.eval(&applied).unwrap(), &b).unwrap());
        let requeued = REQUEUED.load(Ordering::Relaxed);
        assert!(e.resume_from(0).unwrap());
        assert!(REQUEUED.load(Ordering::Relaxed) > requeued);
        assert!(waiting(&e, 0));
        assert_eq!(
            head_meta(cx.g(), &e.queue.waiting(0).unwrap()).unwrap(),
            Some(second)
        );
        e.globals.solve_meta(second, data(&e, "P"));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.queue.resumptions(0), 2);
    }

    /// Invariant 6's assertion: a receiver kept as a term must have made no
    /// choice of §5.10 from an unknown, such as leaving an operator with a
    /// generic dictionary. Made by hand here: a debug build's assertion
    /// says so; a release build counts it.
    #[test]
    #[cfg_attr(debug_assertions, should_panic(expected = "invariant 6"))]
    fn a_kept_receiver_that_chose_from_an_unknown_is_caught() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let before = Snapshot::take(&cx);
        let (m, _) = unknown(&cx);
        (e.operator_dictionaries.borrow_mut()).insert(m, (DefId(0), 0));
        let chose = KEPT_CHOSE.load(Ordering::Relaxed);
        kept_receiver(&cx, &before);
        assert!(KEPT_CHOSE.load(Ordering::Relaxed) > chose);
    }

    /// [`RECORDS`], with a function on `P` that takes an argument after its
    /// receiver, for sections that stay lambdas.
    fn sections() -> String {
        format!("{RECORDS}\ndef P.plus (p: P) (n: N): N := n\n")
    }

    /// A section `source`, inferred: its term, and the type it takes, whose
    /// domain is what it waits on.
    fn section(cx: &mut Ctx, source: &str) -> (Term, Value) {
        let (term, ty) = crate::check::infer(cx, &expression(source)).unwrap();
        let Value::Pi(_, _, dom, _) = force(cx.g(), ty).unwrap() else {
            unreachable!("a section's type is a function's")
        };
        (term, (*dom).clone())
    }

    /// K3: a section whose argument's type is unknown waits, as a whole
    /// (nothing in it is elaborated before then: no `.row` is queued inside
    /// it), and once that type is known is checked at it: `.row` on a `P`
    /// is `P.row` itself, not `x => P.row x` (D506), as it is with the type
    /// known from the start.
    #[test]
    fn a_section_waits_and_is_the_function_itself() {
        let source = sections();
        let (e, data) = module(&source);
        let mut cx = Ctx::new(&e, span());
        let (term, dom) = section(&mut cx, ".row");
        assert_eq!(e.queue.len(), 1);
        assert!(waiting(&e, 0));
        assert!(cx.unify(&dom, &data(&e, "P")).unwrap());
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.queue.len(), 1);
        let text = zonked(&cx, &term);
        assert!(text.starts_with("Ann(") && text.contains("Def("), "{text}");
        assert!(!text.contains("Lam("), "{text}");
    }

    /// K3: a section with an argument after its receiver stays the lambda
    /// `x => P.plus x Z` once its argument's type is known.
    #[test]
    fn a_section_with_an_argument_waits_and_is_a_lambda() {
        let source = sections();
        let (e, data) = module(&source);
        let mut cx = Ctx::new(&e, span());
        let (term, dom) = section(&mut cx, "(.plus Z)");
        assert!(waiting(&e, 0));
        assert!(cx.unify(&dom, &data(&e, "P")).unwrap());
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        let text = zonked(&cx, &term);
        assert!(text.contains("Lam(\"%section\""), "{text}");
    }

    /// K3: a section nothing ever applies is reported at the end with the
    /// section's message; so is one whose argument's type is known but meets
    /// an unknown further along its view (`Id ?a`), where the `.row` inside
    /// the lambda is what waits (K2, carrying the section's message).
    #[test]
    fn a_section_nothing_fixes_is_reported_with_its_message() {
        for source in [".row", "(.row: Id _ -> N)"] {
            let module_source = sections();
            let (e, _) = module(&module_source);
            let mut cx = Ctx::new(&e, span());
            crate::check::infer(&mut cx, &expression(source)).unwrap();
            assert_eq!(e.queue.len(), 1, "{source}");
            let error = e.settle_queue().expect_err("stuck");
            assert_eq!(error.code, "E-CANNOT-INFER", "{source}");
            assert_eq!(
                error.message, "can't tell what `.row` is applied to",
                "{source}"
            );
        }
    }
}
