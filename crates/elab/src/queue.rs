//! The postponement queue (docs/proposals/postponement.md §5). A check that
//! needs the head of a type that is still an unknown doesn't fail: it is
//! queued with its context, a placeholder unknown stands for its result in
//! the term built so far, and it waits on the unknown at that head (its
//! *blocker*). It is resumed at fixed points, once that unknown is solved:
//! - W1, the end of each application, for the checks queued while it was
//!   elaborated and only those (`check::apply_args_postponing`; D2014);
//! - W2, before helpers are lifted (`lift.rs`), so a check holding a
//!   `match` drafts it first, and the part's defaults are applied as at W4
//!   (helpers are lifted at the end of a part, just before W4);
//! - W3, each round of the obligations loop (`auto.rs`), so resuming and
//!   finding instances go round together;
//! - W4, the end of a declaration part ([`Elaborator::finish`]), which also
//!   applies defaults, one at a time by priority, and reports what is still
//!   stuck;
//! - a `calc`'s own checks after each step (`calc.rs`; stage 7, D2126),
//!   once the step has said the chain's type, without defaults;
//! - and a `rewrite` rule's own checks, settled before the rule is looked
//!   for in the goal, defaults included, scoped to the rule
//!   ([`Elaborator::settle_rule`]; D2087).
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
//!   them, and has no term;
//! - a generalising `match` whose scrutinee or a variable's type in scope
//!   holds an unsolved unknown, or whose expected type holds one the queue
//!   has to settle (`matching.rs`, `WaitingMatch`; step 4.0 of stage 4,
//!   D2090): it waits, whole, and has no default; its own type, which its
//!   alternatives fix, is pending meanwhile ([`Check::settles_type`]); still
//!   waiting at the end, it reports the unknown as finishing would
//!   ([`Check::stuck_error`]);
//! - a `rewrite`, `cases`, `omega` or `ring` that failed while its goal
//!   held an unknown the declaration will still settle ([`search_pending`]:
//!   the queue's, and the unknown of an obligation not proved yet, such as
//!   an operator's dictionary), whole ([`tactic_or_wait`], `WaitingTactic`;
//!   step 4.2, and rule 2 of stage 7 for `omega` and `ring`): resumed, it
//!   tries again on the goal now known. A search that would succeed does so
//!   at once; only failure waits.
//!
//! A resume point with nothing queued in its scope costs a length
//! comparison.
//!
//! Errors from checks that wait (step 4.1 of stage 4, D2091):
//! - a construct that turns the errors of a check inside it into its own (a
//!   `calc` step's `E-CALC-STEP`, a callback argument's notes) runs that
//!   check in [`framed`], with an [`ErrorFrame`]: the items still waiting
//!   when it returns keep the frame, and an error they give later, at a
//!   resume point or stuck at the end, goes through it, innermost first, as
//!   it would have inline; what an item queues while it is resumed keeps the
//!   item's frames;
//! - an unfilled placeholder prints as the source its check stands for
//!   ([`Check::display`], `QueueMirrors::syntax`), not as `?N`.
//!
//! The queue's invariants (§5.1), and how each is kept here:
//! 1. *One placeholder, one occurrence*: [`queue`] makes a fresh unknown
//!    for each item, and a restore drops the items queued since, whose
//!    placeholders the restore drops too.
//! 2. *Only its item fills a placeholder*: only [`Elaborator::fill`],
//!    while the item runs. Until then the placeholder is frozen
//!    (`QueueMirrors::unfilled`, D2016's end state): unification
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
//! 7. *Defaults at quiescence only* (restated, D2087): a default is applied
//!    only once resuming, obligations and row comparisons have stopped
//!    making progress, at one of three points: the end of a declaration
//!    part (W4, [`Elaborator::settle_queue`]); a part about to be lifted
//!    (W2, [`Elaborator::resume_before_lifting`]); and a closed pattern, a
//!    `rewrite` rule or a fact given to `omega` or `ring`, whose own
//!    checks and only those are settled before its search
//!    ([`Elaborator::settle_rule`], [`Elaborator::settled_fact`]; the
//!    second since stage 7, D2126). Nothing else applies one: a
//!    `match`, `cases` and the searches wait instead. [`Queue::settling`]
//!    is set at those three points only, and a default asserts it; the
//!    rule's settle asserts it is closed (nothing outside the rule waits on
//!    what its checks wait on).
//! 8. *Placeholders are opaque to elaboration choices*: a placeholder is an
//!    unknown like any other to the code around it; the consumers that
//!    choose from a type's shape wait or decide at `finish` (§5.10). Debug
//!    assertions: the field-name rule chooses a literal's type only as a
//!    default at one of invariant 7's points ([`Queue::settling`]), and a
//!    resumed dot call has its implicit
//!    arguments inserted before it fills a placeholder that doesn't take
//!    them (`dot.rs`). Comparisons that fail at an unfilled placeholder are
//!    counted (`Stats::met_unfilled`).
//!
//! The debug assertions below check 1-6 where they can be seen; the unit
//! tests at the end exercise each with items made directly, and K1, K2 and
//! K3 on small modules.
//!
//! Counters for later stages are printed with `STITCHWORT_TIMINGS`
//! ([`counts`]).

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::PlaceholderText;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{Ev, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::Expr;

use crate::Elaborator;
use crate::check::{Ctx, Result, Saved};
use crate::state::Stats;
use crate::unify::Answer;
use std::sync::atomic::{AtomicUsize, Ordering};

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
    fn wakes(&self, _g: &Ev) -> Result<bool> {
        Ok(false)
    }

    /// Its error if it is still waiting at the end, on `blocker` (the
    /// unknown at the head of what it waits on, if one is): `None` for the
    /// error its site raised before it could wait. A `match` waiting on an
    /// ordinary unknown reports that unknown as finishing would
    /// (`matching.rs`, `WaitingMatch`). A check queued without its site's
    /// error ([`queue_without_error`]) always gives one here.
    fn stuck_error(&self, _e: &Elaborator, _blocker: Option<usize>) -> Option<Diagnostic> {
        None
    }

    /// Whether resuming it settles the unknown at the head of its type,
    /// which is then one the queue still has to settle ([`pending`]): a
    /// waiting `match` whose type is inferred, which its alternatives fix
    /// (`matching.rs`, `WaitingMatch`).
    fn settles_type(&self) -> bool {
        false
    }

    /// The source its placeholder stands for, shown in messages while the
    /// check waits (D2091): `r.items` for a waiting `.field`, the literal
    /// for a record literal. Asked once, when it is queued. A check with a
    /// [`Check::literal`] is shown as that number instead.
    fn display(&self, _cx: &Ctx) -> Option<String> {
        None
    }

    /// Whether what fills its placeholder is a literal, cheap to compute
    /// (a number literal waiting for its type, K4): a decision's search
    /// then keeps the placeholder as an operand, as it keeps a literal,
    /// rather than binding it (`bind::operand`).
    fn literal(&self) -> Option<Rc<num_bigint::BigUint>> {
        None
    }
}

/// Whether `term` is the placeholder of a check whose term is a literal
/// ([`Check::literal`]), not filled yet: a waiting number.
pub(crate) fn waiting_literal(e: &Elaborator, term: &Term) -> bool {
    let Term::Meta(m) = term.strip_loc().spine().0 else {
        return false;
    };
    e.attempt.store.mirrors.is_literal(*m)
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
    Nat,
}

/// Where an item is (invariant 4). *Failed* lasts only while the error
/// propagates: either an attempt is undone, and with it the item's
/// resumption, or the declaration fails.
#[derive(Clone)]
pub(crate) enum State {
    /// On the head of the type the item was queued waiting on, to be
    /// resumed by its own check (`None`); or as a resumption left it
    /// ([`Again`]). Small, as the queue keeps one per item and the
    /// resumption log one per change (SW-1048).
    Waiting(Option<Rc<Again>>),
    Running,
    Done,
    Failed,
}

/// How an item waits after a resumption that met another unknown
/// ([`Resumed::Waiting`], [`Resumed::WaitingAs`]).
pub(crate) struct Again {
    /// On the head of this type, a value in the item's context.
    needs: Value,
    /// To be resumed by this check rather than the item's own, if there is
    /// one ([`Resumed::WaitingAs`]).
    check: Option<Rc<dyn Check>>,
}

pub(crate) struct Item {
    check: Rc<dyn Check>,
    /// What it was queued waiting on: it waits on the head of this type, a
    /// value in its context, until a resumption says otherwise
    /// ([`State::Waiting`]).
    needs: Value,
    saved: Saved,
    /// The placeholder: its unknown applied to the context's variables
    /// (`Ctx::fresh_meta`), and that unknown.
    placeholder: Term,
    meta: usize,
    /// The placeholder's type.
    ty: Value,
    /// The error its site raised before it could wait, reported if it is
    /// still waiting at the end; `None` for a check that makes its own
    /// ([`queue_without_error`]). Boxed, as few are ever reported.
    error: Option<Box<Diagnostic>>,
    /// Whether it has been counted as reaching the end of an application
    /// still waiting.
    crossed: Cell<bool>,
    /// Whether it is a waiting comparison (stage 6, [`Comparison`]), whose
    /// placeholder stands for nothing.
    constraint: bool,
    /// How its placeholder is shown while unfilled ([`Check::display`]).
    display: Option<stitchwort_core::globals::PlaceholderSyntax>,
    /// The error frames of the constructs it was made inside that returned
    /// while it still waited, innermost first ([`framed`]).
    frames: RefCell<Vec<Rc<Frame>>>,
    /// The frames of the item being resumed when it was queued, innermost
    /// first: it was made inside those constructs too.
    outer: Rc<[Rc<Frame>]>,
}

impl Item {
    /// Every error frame it was made inside, innermost first.
    fn all_frames(&self) -> Rc<[Rc<Frame>]> {
        let own = self.frames.borrow();
        if own.is_empty() {
            return self.outer.clone();
        }
        own.iter().chain(self.outer.iter()).cloned().collect()
    }
}

/// The current declaration's queued checks, in creation order, with their
/// states. A state changes only through [`Queue::set`], which keeps what it
/// replaced in the resumption log, as `MetaStore::meta_trail` does for
/// solutions: so restoring a snapshot (which records both lengths) undoes
/// the resumptions made since along with the items queued since.
#[derive(Default)]
pub(crate) struct Queue {
    items: RefCell<Vec<Rc<Item>>>,
    states: RefCell<Vec<State>>,
    log: RefCell<Vec<(usize, State)>>,
    /// Whether the queue is being settled at one of the points where a
    /// default may be applied (invariants 7 and 8): W4, W2, or a `rewrite`
    /// rule's own checks.
    settling: Cell<bool>,
    frames: Frames,
    /// No names: what a placeholder applied to no variable is shown with
    /// (`Item::display`), made once rather than per item.
    no_names: Rc<[stitchwort_core::Name]>,
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

    /// Whether the queue is being settled at one of invariant 7's points
    /// (W4, W2, a `rewrite` rule's own checks), the only places a default
    /// is applied: a choice an item's default makes (the field-name rule)
    /// is made from nothing else having said what the item is, never from
    /// a placeholder's apparent shape in the middle of elaboration
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
    /// term out of the placeholder table (`MetaStore::lifted_calls`). `metas`
    /// is the length the metavariables are restored to.
    pub(crate) fn restore(&self, mark: Mark, g: &crate::state::MetaStore, metas: usize) {
        let changed = self.len() > mark.items || self.log.borrow().len() > mark.log;
        let mut resumed = Vec::new();
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
                resumed.push(i);
            }
        }
        // The items dropped leave the tables the unifier reads; those whose
        // state went back are put in step with it.
        let dropped: Vec<usize> = self.items.borrow()[mark.items.min(self.len())..]
            .iter()
            .map(|item| item.meta)
            .collect();
        self.items.borrow_mut().truncate(mark.items);
        self.states.borrow_mut().truncate(mark.items);
        for m in dropped {
            Self::forget(g, m);
        }
        for i in resumed {
            if i < mark.items {
                self.sync_item(g, i);
            }
        }
        debug_assert!(
            self.items.borrow().iter().all(|item| item.meta < metas),
            "an item outlived its placeholder (invariant 1)"
        );
        let _ = changed;
    }

    /// Empties the queue; `MetaStore::clear_metas` empties the placeholders
    /// it tells the unifier of.
    pub(crate) fn clear(&self) {
        self.items.borrow_mut().clear();
        self.states.borrow_mut().clear();
        self.log.borrow_mut().clear();
    }

    /// Tells the unifier which placeholders aren't filled yet
    /// (`QueueMirrors::unfilled`): they are frozen until filled
    /// (D2016), and a comparison that fails at one is counted
    /// (`Stats::met_unfilled`).
    fn sync_item(&self, g: &crate::state::MetaStore, i: usize) {
        let item = self.item(i);
        if matches!(self.states.borrow()[i], State::Done) || item.constraint {
            Self::forget(g, item.meta);
            return;
        }
        g.mirrors.set(
            item.meta,
            item.display.clone(),
            item.check.literal().map(|k| (k, item.ty.clone())),
        );
    }

    /// Takes placeholder `m` out of the tables [`Queue::sync_item`] keeps.
    fn forget(g: &crate::state::MetaStore, m: usize) {
        g.mirrors.forget(m);
    }

    fn item(&self, i: usize) -> Rc<Item> {
        self.items.borrow()[i].clone()
    }

    pub(crate) fn state(&self, i: usize) -> State {
        self.states.borrow()[i].clone()
    }

    fn set(&self, i: usize, state: State, g: &crate::state::MetaStore) {
        let old = std::mem::replace(&mut self.states.borrow_mut()[i], state);
        self.log.borrow_mut().push((i, old));
        self.sync_item(g, i);
    }

    /// What item `i` waits on the head of, if it is waiting.
    fn waiting(&self, i: usize) -> Option<Value> {
        match &self.states.borrow()[i] {
            State::Waiting(None) => Some(self.items.borrow()[i].needs.clone()),
            State::Waiting(Some(again)) => Some(again.needs.clone()),
            _ => None,
        }
    }

    /// What resumes item `i`, or gives its default: its own check, or the
    /// one it waits as.
    fn check(&self, i: usize) -> Rc<dyn Check> {
        match &self.states.borrow()[i] {
            State::Waiting(Some(again)) if let Some(check) = &again.check => check.clone(),
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
    queue_item(cx, check, needs, ty, Some(Box::new(error)))
}

/// [`queue`] for a check whose [`Check::stuck_error`] always gives its
/// error, so that none is made unless it is reported: a number literal
/// waiting for its type, of which a list may queue thousands (SW-1048).
pub(crate) fn queue_without_error(
    cx: &Ctx,
    check: Rc<dyn Check>,
    needs: Value,
    ty: Value,
) -> Result<Term> {
    queue_item(cx, check, needs, ty, None)
}

fn queue_item(
    cx: &Ctx,
    check: Rc<dyn Check>,
    needs: Value,
    ty: Value,
    error: Option<Box<Diagnostic>>,
) -> Result<Term> {
    debug_assert!(!ready(&cx.g(), &needs)?, "an item waits on an unknown head");
    // A number literal's value mentions no variable, so where its type
    // mentions none either, neither does its placeholder (D2126): applied to
    // the variables, after a substitution (a `match`, a β-step) it would
    // meet its value applied to terms that aren't variables, which only the
    // fill could solve. A type that is an unknown applied to nothing (most
    // often) mentions none, and isn't read back to see so.
    let literal = check.literal();
    let closed = literal.is_some()
        && (matches!(&ty, Value::Neutral(Head::Meta(_), spine) if spine.is_empty()) || {
            let t = cx.quote(&ty)?;
            (0..cx.level()).all(|i| !t.mentions(i))
        });
    let placeholder = if closed {
        let m = cx.metas().new_meta(cx.span);
        cx.metas().set_meta_type(m, ty.clone(), 0);
        Term::Meta(m)
    } else {
        cx.fresh_meta_of(&ty)
    };
    let Term::Meta(meta) = *placeholder.spine().0 else {
        unreachable!("a fresh metavariable")
    };
    let q = &cx.e.attempt.queue;
    // Shown as its source only applied to the variables it was made with,
    // by name: applied to others (a lambda's parameter given an argument),
    // the source would name the wrong variables.
    // A number is shown as the number (D2091).
    let text = match literal {
        Some(k) => Some(PlaceholderText::Number(k)),
        None => (check.display(cx)).map(|text| PlaceholderText::Source(Rc::from(text))),
    };
    let display = text.map(|text| {
        let args = placeholder.spine().1;
        if args.is_empty() {
            return (q.no_names.clone(), text);
        }
        let depth = cx.level();
        let names: Rc<[stitchwort_core::Name]> = (args.iter())
            .map(|a| match a.strip_loc() {
                Term::Var(ix) => cx.names[depth - 1 - ix].clone(),
                _ => unreachable!("a placeholder is applied to variables"),
            })
            .collect();
        (names, text)
    });
    let saved = cx.save_sharing(q.items.borrow().last().map(|item| &item.saved));
    q.items.borrow_mut().push(Rc::new(Item {
        check,
        needs,
        saved,
        placeholder: placeholder.clone(),
        meta,
        ty,
        error,
        crossed: Cell::new(false),
        constraint: false,
        display,
        frames: RefCell::default(),
        outer: q.frames.resuming.borrow().clone(),
    }));
    q.states.borrow_mut().push(State::Waiting(None));
    q.sync_item(cx.metas(), q.len() - 1);
    count(&cx.e.session.stats.queued);
    Ok(placeholder)
}

/// [`syntax`], bracketed if it is an application or an operator's.
pub(crate) fn atom(e: &Expr) -> String {
    let text = syntax(e);
    match e {
        Expr::App(..) | Expr::Binary(..) | Expr::Neg(..) | Expr::Pipe(..) => {
            format!("({text})")
        }
        _ => text,
    }
}

/// `expr` as written, near enough for a message to show a waiting check's
/// placeholder by (D2091): names, numbers, fields, applications, operators
/// and record literals in full, anything larger as `…`.
pub(crate) fn syntax(expr: &Expr) -> String {
    use stitchwort_syntax::ast::{Bracket, SECTION};
    fn fields(fields: &[(stitchwort_syntax::ast::Name, Expr)]) -> String {
        let fields: Vec<String> = (fields.iter())
            .map(|(name, value)| match value {
                Expr::Var(v) if v.text == name.text => name.text.clone(),
                _ => format!("{} = {}", name.text, syntax(value)),
            })
            .collect();
        format!("{{ {} }}", fields.join(", "))
    }
    match expr {
        Expr::Var(name) => name.text.clone(),
        Expr::Num(k, _) => k.to_string(),
        Expr::Float(text, _) => text.clone(),
        Expr::Str(text, _) => format!("{text:?}"),
        Expr::Char(c, _) => format!("{c:?}"),
        Expr::Unit(_) => "()".into(),
        Expr::Hole(_) => "_".into(),
        Expr::Bracketed(e, _) | Expr::Interpolated(e, _) => syntax(e),
        Expr::App(f, a) => format!("{} {}", syntax(f), atom(a)),
        Expr::NamedArg(name, value, _, bracket) => match bracket {
            Bracket::Round => format!("({} := {})", name.text, syntax(value)),
            Bracket::Square => format!("[{} := {}]", name.text, syntax(value)),
        },
        Expr::Binary(op, a, b) => format!("{} {} {}", atom(a), op.symbol(), atom(b)),
        Expr::Neg(e, ..) => format!("-{}", atom(e)),
        Expr::Field(recv, name) => match &**recv {
            // A method section's lambda's parameter: `.f a`.
            Expr::Var(v) if v.text == SECTION => format!(".{}", name.text),
            recv => format!("{}.{}", atom(recv), name.text),
        },
        // `.f a` is `%section => %section.f a`.
        Expr::Lam(params, body, _) if params.len() == 1 && params[0].text == SECTION => {
            format!("({})", syntax(body))
        }
        Expr::Tuple(a, b, _) => format!("({}, {})", syntax(a), syntax(b)),
        Expr::Spread(list, _) => format!("..{}", syntax(list)),
        Expr::List(items, _) => {
            let items: Vec<String> = items.iter().map(syntax).collect();
            format!("[{}]", items.join(", "))
        }
        Expr::Record {
            base: None,
            fields: fs,
            ..
        } => fields(fs),
        Expr::Record {
            base: Some(base),
            fields: fs,
            ..
        } => format!("{{ {} | {}", syntax(base), &fields(fs)[2..]),
        Expr::CtorFields {
            ctor, fields: fs, ..
        } => format!("{} {}", ctor.text, fields(fs)),
        _ => "…".into(),
    }
}

/// A construct that turns the errors of a check inside it into its own (a
/// code, a label, a note): a `calc` step's `E-CALC-STEP`, a callback
/// argument's notes (step 4.1 of stage 4, D2091). Its mapping is run on the
/// error inline, as before, and also on the error of a check queued inside
/// it that fails after it has returned, at a resume point or stuck at the
/// end ([`framed`]), so the error reads as it would have inline.
pub(crate) trait ErrorFrame {
    /// `e`, an error of a check inside the construct, as the construct
    /// reports it; `cx` is the context the construct ran in.
    fn map(&self, cx: &mut Ctx, e: Diagnostic) -> Diagnostic;
}

/// A construct's error frame, kept by the items still waiting when it
/// returned: its mapping, and the context it ran in.
pub(crate) struct Frame {
    id: u64,
    saved: Saved,
    map: Box<dyn ErrorFrame>,
}

/// The error frames of the constructs being elaborated.
#[derive(Default)]
struct Frames {
    /// The ids of the constructs running ([`framed`]), innermost last.
    active: RefCell<Vec<u64>>,
    next: Cell<u64>,
    /// While an item is resumed, its frames: those of the items it queues,
    /// and active, since its constructs are what is running again.
    resuming: RefCell<Rc<[Rc<Frame>]>>,
}

/// Runs `body`, a check inside a construct whose errors it maps by the
/// frame `frame` makes: an error `body` returns is mapped at once, and the
/// items `body` queued that still wait when it returns keep the frame, which
/// maps their errors if they fail later (rule 1 of D2091). The frame is made
/// only when it is needed, in the context the construct runs in, so a frame
/// costs nothing where nothing fails or waits. The resumption log doesn't
/// record the frames an item is given (invariant 5): they are given only to
/// items queued since the construct began, which a restore to a snapshot
/// taken before it drops, and a snapshot taken inside it is restored inside
/// it, before they are given.
pub(crate) fn framed<T, F: ErrorFrame + 'static>(
    cx: &mut Ctx,
    body: impl FnOnce(&mut Ctx) -> Result<T>,
    frame: impl FnOnce(&mut Ctx) -> F,
) -> Result<T> {
    let frames = &cx.e.attempt.queue.frames;
    let id = frames.next.get();
    frames.next.set(id + 1);
    let from = cx.e.attempt.queue.len();
    frames.active.borrow_mut().push(id);
    let result = body(cx);
    let frames = &cx.e.attempt.queue.frames;
    {
        let mut active = frames.active.borrow_mut();
        debug_assert_eq!(active.last(), Some(&id), "frames nest");
        active.pop();
    }
    match result {
        Err(e) if !crate::undo::fatal(&e) => Err(frame(cx).map(cx, e)),
        Err(e) => Err(e),
        Ok(t) => {
            let q = &cx.e.attempt.queue;
            let waiting: Vec<usize> = (from.min(q.len())..q.len())
                .filter(|&i| !matches!(q.state(i), State::Done))
                .collect();
            if !waiting.is_empty() {
                let map = Box::new(frame(cx));
                let q = &cx.e.attempt.queue;
                let frame = Rc::new(Frame {
                    id,
                    saved: cx.save(),
                    map,
                });
                for i in waiting {
                    q.item(i).frames.borrow_mut().push(frame.clone());
                }
            }
            Ok(t)
        }
    }
}

impl Elaborator {
    /// `e`, the error of `item`, through the frames it was made inside,
    /// innermost first, except those still running: their constructs map it
    /// themselves as it passes through them, as inline.
    fn through_frames(&self, item: &Item, mut e: Diagnostic) -> Diagnostic {
        let frames = item.all_frames();
        if frames.is_empty() || crate::undo::fatal(&e) {
            return e;
        }
        let running = |id: u64| {
            let f = &self.attempt.queue.frames;
            f.active.borrow().contains(&id) || f.resuming.borrow().iter().any(|r| r.id == id)
        };
        for frame in frames.iter().filter(|f| !running(f.id)) {
            let mut cx = frame.saved.ctx(self);
            e = frame.map.map(&mut cx, e);
        }
        e
    }
}

/// A placeholder that `v` mentions whose check hasn't filled it, and that
/// unification hasn't solved either, if any: for a choice that must wait for
/// it (invariant 8; `check::decide_to_bool`). Free while nothing waits.
pub(crate) fn unfilled_in(cx: &Ctx, v: &Value) -> Result<Option<usize>> {
    let q = &cx.e.attempt.queue;
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
    // Calls read back as calls: a placeholder is among a call's arguments
    // or in a local's value (which evaluation substitutes), never in what a
    // global definition's body computes to, so unfolding one only costs
    // (`List.any [1, 2] (n => n < cost)` computed `cost` while the literals
    // waited: crates/bench/tests/check_work.rs, SW-1051).
    let term = cx.quote_folded(v)?;
    unfilled_among(cx, &term, &unfilled)
}

/// [`unfilled_in`] for the term `term` as written, not its value: the
/// placeholders among its own subterms, not those inside what its
/// variables or calls stand for. It computes nothing, so it costs nothing
/// on a term whose value is large to compute (step 4.3: `bananasBySequence
/// 50 buyers == …`).
pub(crate) fn unfilled_in_term(cx: &Ctx, term: &Term) -> Result<Option<usize>> {
    let q = &cx.e.attempt.queue;
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
    unfilled_among(cx, term, &unfilled)
}

/// The first of the placeholders `unfilled` that `term`, with the solved
/// unknowns written in, mentions.
fn unfilled_among(cx: &Ctx, term: &Term, unfilled: &[usize]) -> Result<Option<usize>> {
    let term = cx.e.zonk_keeping(term, cx.level(), &|_| true)?;
    Ok(term.subterms().find_map(|(t, _)| match t {
        Term::Meta(m) if unfilled.contains(m) => Some(*m),
        _ => None,
    }))
}

/// The unknowns the queue still has to settle (stage 6): each placeholder
/// not filled yet that unification hasn't solved, the unknown each
/// waiting item waits on, and the unknown at the head of a waiting item's
/// type where its resumption settles it ([`Check::settles_type`], a waiting
/// `match`). Each is solved by the end of the declaration, by
/// an item's resumption or default, or its item is reported stuck; so a
/// comparison that fails only on one of them can wait for it.
pub(crate) fn pending(cx: &Ctx) -> Result<HashSet<usize>> {
    let g = cx.g();
    let q = &cx.e.attempt.queue;
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
        if let Some(needs) = q.waiting(i) {
            if let Some(m) = head_meta(&g, &needs)? {
                pending.insert(m);
            }
            if q.check(i).settles_type()
                && let Some(m) = head_meta(&g, &item.ty)?
            {
                pending.insert(m);
            }
        }
    }
    Ok(pending)
}

/// The unknowns a proof search treats as ones the declaration will still
/// settle (step 4.2; docs/proposals/postponement.md, "Every part that reads
/// a term's shape"): the queue's ([`pending`]), and the unknown of each
/// obligation not proved yet (an operator's dictionary, an instance, an
/// `auto` argument), which the obligations loop (W3, W4) solves or
/// reports. Not the unknowns in an obligation's type (`Add ?T`'s `?T`):
/// finding the instance doesn't settle those.
pub(crate) fn search_pending(cx: &Ctx) -> Result<HashSet<usize>> {
    let g = cx.g();
    let mut pending = pending(cx)?;
    for ob in cx.e.attempt.obligations.borrow().iter() {
        if let Term::Meta(m) = ob.meta.spine().0
            && g.meta_solution(*m).is_none()
        {
            pending.insert(*m);
        }
    }
    Ok(pending)
}

/// An unknown of [`search_pending`] that `v` mentions, if any. Free while
/// nothing is queued and no obligation waits.
pub(crate) fn search_pending_in(cx: &Ctx, v: &Value) -> Result<Option<usize>> {
    if cx.e.attempt.queue.len() == 0 && cx.e.attempt.obligations.borrow().is_empty() {
        return Ok(None);
    }
    let pending = search_pending(cx)?;
    if pending.is_empty() {
        return Ok(None);
    }
    let term = crate::interfaces::scanned(cx, v)?;
    let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    Ok(term.subterms().find_map(|(t, _)| match t {
        Term::Meta(m) if pending.contains(m) => Some(*m),
        _ => None,
    }))
}

/// Whether `v`'s shape may still change once the queue settles an unknown
/// it still has to ([`pending`]): `v` is one, applied, or is flexible (a
/// call stuck, an unknown applied) and mentions one (`unify::on_pending`).
/// A check against it that needs its shape (`rfl` needs an equation) can
/// wait for it through a comparison. Free while nothing is queued.
pub(crate) fn headed_by_pending(cx: &Ctx, v: &Value) -> Result<bool> {
    if cx.e.attempt.queue.len() == 0 {
        return Ok(false);
    }
    let pending = pending(cx)?;
    if pending.is_empty() {
        return Ok(false);
    }
    Ok(crate::unify::on_pending_in(
        &cx.u(),
        cx.level(),
        v,
        &pending,
    )?)
}

/// A tactic run against a goal: `rewrite`'s, `cases`', `omega`'s, `ring`'s.
pub(crate) type Tactic = fn(&mut Ctx, &Expr, &Value) -> Result<Term>;

/// `run`, a tactic, against `expected` (step 4.2 of stage 4; `omega` and
/// `ring` by rule 2 of stage 7). It is tried
/// at once; if it fails while the goal holds an unknown the declaration
/// will still settle ([`search_pending_in`]), what it did is undone and it
/// waits for that unknown, whole, as a queued [`WaitingTactic`]: its
/// search can't see through the unknown, and can't wait in the middle. A
/// search that succeeds proves the statement whatever it found, so only
/// failure needs to wait. Otherwise its result or error is as before.
pub(crate) fn tactic_or_wait(
    cx: &mut Ctx,
    expr: &Expr,
    expected: &Value,
    run: Tactic,
) -> Result<Term> {
    let before = crate::undo::Snapshot::take(cx);
    match run(cx, expr, expected) {
        Err(e) if !crate::undo::fatal(&e) => {
            before.restore(cx);
            let Some(m) = search_pending_in(cx, expected)? else {
                return Err(e);
            };
            let check = WaitingTactic {
                expr: expr.clone(),
                expected: expected.clone(),
                run,
            };
            count(&cx.e.session.stats.tactic_waited);
            queue(cx, Rc::new(check), on(m), expected.clone(), e)
        }
        result => result,
    }
}

/// A tactic waiting for an unknown in its goal ([`tactic_or_wait`]): its
/// syntax, the goal, and the tactic. Resumed, it runs on the goal now
/// known; if it fails while the goal still holds an unknown the
/// declaration will settle, it waits again; otherwise its error is its
/// own, against the goal now known.
struct WaitingTactic {
    expr: Expr,
    expected: Value,
    run: Tactic,
}

impl Check for WaitingTactic {
    fn resume(&self, cx: &mut Ctx) -> Result<Resumed> {
        // Evaluated afresh, as a waiting comparison's sides are: what was
        // stuck on the unknown computes now.
        let expected = cx.eval(&cx.quote_folded(&self.expected)?)?;
        let before = crate::undo::Snapshot::take(cx);
        match (self.run)(cx, &self.expr, &expected) {
            Ok(term) => Ok(Resumed::Done(term)),
            Err(e) if !crate::undo::fatal(&e) => {
                before.restore(cx);
                match search_pending_in(cx, &expected)? {
                    Some(m) => Ok(Resumed::Waiting(on(m))),
                    None => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    fn display(&self, _cx: &Ctx) -> Option<String> {
        Some(match &self.expr {
            Expr::Cases { .. } => "(cases …)".into(),
            Expr::Omega { .. } => "(omega …)".into(),
            Expr::Ring { .. } => "(ring …)".into(),
            _ => "(rewrite …)".into(),
        })
    }
}

/// The proof searches whose runs on a goal holding an unknown the
/// declaration will still settle are counted (step 4.2), to decide whether
/// they should try and then wait as `rewrite` and `cases` do.
#[derive(Clone, Copy)]
pub(crate) enum Search {
    Omega,
    Ring,
    Auto,
}

impl Search {
    /// Its counters: runs on such a goal, and of those, failures.
    fn counters(self, stats: &Stats) -> (&AtomicUsize, &AtomicUsize) {
        match self {
            Search::Omega => (&stats.omega_pending, &stats.omega_pending_failed),
            Search::Ring => (&stats.ring_pending, &stats.ring_pending_failed),
            Search::Auto => (&stats.auto_pending, &stats.auto_pending_failed),
        }
    }
}

/// `run`, the search `search` on `goal`, counted if `goal` holds an unknown
/// of [`search_pending`] (and if it then fails); its result unchanged.
pub(crate) fn counted_search<T>(
    cx: &mut Ctx,
    goal: &Value,
    search: Search,
    run: impl FnOnce(&mut Ctx) -> Result<T>,
) -> Result<T> {
    let pending = search_pending_in(cx, goal)?.is_some();
    let result = run(cx);
    if pending {
        let (ran, failed) = search.counters(&cx.e.session.stats);
        count(ran);
        if result.is_err() {
            count(failed);
        }
    }
    result
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
    if cx.e.attempt.queue.len() == 0 {
        return Ok(false);
    }
    let pending = pending(cx)?;
    if pending.is_empty() {
        return Ok(false);
    }
    let snapshot = crate::undo::Snapshot::take(cx);
    match crate::unify::unify_waiting(&cx.u(), cx.level(), found, expected, &pending)? {
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
            count(&cx.e.session.stats.waited);
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
                let term = stitchwort_core::value::quote(&cx.g(), pair.level, side)?;
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
            match crate::unify::unify_waiting(&cx.u(), cx.level(), found, expected, &pending)? {
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

    fn wakes(&self, g: &Ev) -> Result<bool> {
        Ok(self.blockers.iter().any(|&m| g.meta_solution(m).is_some()))
    }
}

/// The unknown `m`, as a value with nothing applied.
pub(crate) fn on(m: usize) -> Value {
    Value::Neutral(Head::Meta(m), Default::default())
}

/// Queues `check`, a comparison with no term of its own, waiting on unknown
/// `blocker`, with `error` if it stays stuck.
pub(crate) fn queue_constraint(
    cx: &Ctx,
    check: Rc<dyn Check>,
    blocker: usize,
    error: Diagnostic,
) -> Result<()> {
    // Untyped: it stands for no value.
    let placeholder = cx.fresh_meta();
    let Term::Meta(meta) = *placeholder.spine().0 else {
        unreachable!("a fresh metavariable")
    };
    let q = &cx.e.attempt.queue;
    let saved = cx.save_sharing(q.items.borrow().last().map(|item| &item.saved));
    q.items.borrow_mut().push(Rc::new(Item {
        check,
        needs: on(blocker),
        saved,
        placeholder,
        meta,
        ty: Value::Sort(stitchwort_core::Sort::Prop),
        error: Some(Box::new(error)),
        crossed: Cell::new(false),
        constraint: true,
        display: None,
        frames: RefCell::default(),
        outer: q.frames.resuming.borrow().clone(),
    }));
    q.states.borrow_mut().push(State::Waiting(None));
    q.sync_item(cx.metas(), q.len() - 1);
    Ok(())
}

/// Whether the head of `needs` is known.
fn ready(g: &Ev, needs: &Value) -> Result<bool> {
    Ok(head_meta(g, needs)?.is_none())
}

/// The unknown at the head of `v`, if it is one.
fn head_meta(g: &Ev, v: &Value) -> Result<Option<usize>> {
    // A resume point asks this of every waiting item, so the two common
    // answers are read off without computing: an unknown not solved, or
    // one applied to nothing solved with a type (a list's element type).
    if let Value::Neutral(Head::Meta(m), spine) = v {
        match &g.meta_solution(*m) {
            None => return Ok(Some(*m)),
            Some(Value::Data(..) | Value::Pi(..) | Value::Sort(_)) if spine.is_empty() => {
                return Ok(None);
            }
            Some(_) => {}
        }
    }
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
/// by its value. Where that value is a lambda applied to arguments, it is
/// annotated with its type: zonking folds it back to the variable if it
/// can (and drops the annotation), and otherwise the kernel, which infers
/// no type for a lambda, still has one (SW-2439); the `bool` says whether
/// there is such an annotation. `None` if a value isn't in the
/// placeholder's variables either: zonking then reads the placeholder's
/// solution back, as for any unknown.
fn placeholder_call(
    cx: &Ctx,
    placeholder: &Term,
    term: &Term,
) -> Result<Option<(usize, Term, bool)>> {
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
    let value = |level: usize| cx.quote_folded(&cx.env[level]);
    let variable = |level: usize| -> Result<Term> {
        applied(level).or_else(|_| {
            crate::lift::replace_with(&g, &value(level)?, depth, &applied, &|_, _| None)
        })
    };
    let annotated = Cell::new(false);
    let head = |level: usize| -> Result<Option<Term>> {
        if spine.contains(&level) || !lambda(&value(level)?) {
            return Ok(None);
        }
        let ty = cx.quote_folded(&cx.types[level])?;
        let ty = crate::lift::replace_with(&g, &ty, depth, &variable, &|_, _| None)?;
        annotated.set(true);
        Ok(Some(ty))
    };
    match crate::lift::replace_annotating_heads(&g, term, depth, &variable, &head) {
        Ok(call) => Ok(Some((s, call, annotated.get()))),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(_) => Ok(None),
    }
}

/// Whether `term` is a lambda, under any `let`s.
fn lambda(term: &Term) -> bool {
    match term.strip_loc() {
        Term::Lam(..) => true,
        Term::Let(_, _, _, body, _) => lambda(body),
        _ => false,
    }
}

impl Elaborator {
    /// The terms the checks filled their placeholders with, with their
    /// operators specialised as the declaration's own term is at the end
    /// ([`Elaborator::specialise_operators`], §5.10): a check resumed late
    /// (a decision waiting for a literal, step 4.3) may have left an
    /// operator generic whose dictionary was found after it. Zonking writes
    /// these terms in place of the placeholders, so they are specialised
    /// before it.
    pub(crate) fn specialise_fills(&self) -> Result<()> {
        if self.attempt.operator_dictionaries.borrow().is_empty() {
            return Ok(());
        }
        for i in 0..self.attempt.queue.len() {
            let m = self.attempt.queue.item(i).meta;
            let Some((s, call, annotated)) =
                self.attempt.store.lifted_calls.borrow().get(&m).cloned()
            else {
                continue;
            };
            if let Some(call) = self.specialise_operators(&call, s)? {
                (self.attempt.store.lifted_calls.borrow_mut())
                    .insert(m, (s, Rc::new(call), annotated));
            }
        }
        Ok(())
    }

    /// W1: the end of an application, which began with `from` items
    /// queued. Resumes those queued since that can be, and only those
    /// (invariant 3).
    pub(crate) fn resume_application(&self, from: usize) -> Result<()> {
        debug_assert!(
            from <= self.attempt.queue.len(),
            "an application's checks outlived it (invariant 3)"
        );
        if self.attempt.queue.len() == from {
            return Ok(());
        }
        self.resume_from(from)?;
        // Each placeholder still unfilled here is one a comparison may meet
        // before its item can say what it is (the stage-6 trigger, §5.13).
        for i in from..self.attempt.queue.len() {
            let item = self.attempt.queue.item(i);
            if self.attempt.queue.waiting(i).is_some() && !item.crossed.replace(true) {
                count(&self.session.stats.crossed);
            }
        }
        Ok(())
    }

    /// Ladder step 1: resumes every waiting item from `from` on whose
    /// blocker is solved, in creation order, again while any is: whether
    /// any was.
    pub(crate) fn resume_from(&self, from: usize) -> Result<bool> {
        if self.attempt.queue.len() <= from {
            return Ok(false);
        }
        debug_assert!(
            (from..self.attempt.queue.len())
                .all(|i| !matches!(self.attempt.queue.state(i), State::Running)),
            "a resume point reached a running item (invariant 4, T3)"
        );
        let mut any = false;
        loop {
            let mut progress = false;
            let mut i = from;
            while i < self.attempt.queue.len() {
                if let Some(needs) = self.attempt.queue.waiting(i)
                    && (ready(&self.ev(), &needs)?
                        || self.attempt.queue.check(i).wakes(&self.ev())?)
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
        let item = self.attempt.queue.item(i);
        let check = self.attempt.queue.check(i);
        let replaced = match self.attempt.queue.state(i) {
            State::Waiting(Some(again)) => again.check.clone(),
            _ => None,
        };
        self.attempt
            .queue
            .set(i, State::Running, &self.attempt.store);
        count(&self.session.stats.resumed);
        self.caches.keep_dot_owner(&check);
        // What it queues while it runs is made inside its constructs too.
        let outer = (self.attempt.queue.frames.resuming).replace(item.all_frames());
        let mut cx = item.saved.ctx(self);
        let waits = |needs: &Value| {
            debug_assert!(
                !ready(&self.ev(), needs).unwrap_or(false),
                "an item waits again only on an unknown head"
            );
            count(&self.session.stats.requeued);
        };
        let resumed = check.resume(&mut cx).and_then(|resumed| match resumed {
            Resumed::Done(term) => self.fill(&mut cx, i, &item, &term).map(|()| State::Done),
            Resumed::Holds => Ok(State::Done),
            Resumed::Waiting(needs) => {
                waits(&needs);
                Ok(State::Waiting(Some(Rc::new(Again {
                    needs,
                    check: replaced,
                }))))
            }
            Resumed::WaitingAs(needs, check) => {
                waits(&needs);
                Ok(State::Waiting(Some(Rc::new(Again {
                    needs,
                    check: Some(check),
                }))))
            }
        });
        self.attempt.queue.frames.resuming.replace(outer);
        match resumed {
            Ok(state) => {
                self.attempt.queue.set(i, state, &self.attempt.store);
                Ok(())
            }
            Err(e) => {
                self.attempt
                    .queue
                    .set(i, State::Failed, &self.attempt.store);
                Err(self.through_frames(&item, e))
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
        let g = &self.unifier();
        debug_assert!(
            matches!(self.attempt.queue.state(i), State::Running),
            "only its own running item fills a placeholder (invariant 2)"
        );
        debug_assert!(
            !g.store.lifted_calls.borrow().contains_key(&item.meta),
            "a placeholder is filled once (invariant 1)"
        );
        // A number at `Nat` filling a placeholder applied to nothing, not
        // solved (most waiting literals): unifying them solves it with the
        // number, and its call is the number. Done so here, without
        // computing either side or reading the number back (SW-1048).
        if let (Term::Meta(_), Term::Nat(k)) = (&item.placeholder, term)
            && g.store.metas.borrow()[item.meta].solution.is_none()
        {
            g.store.mirrors.filling(item.meta);
            g.store.solve_meta(item.meta, Value::Nat(k.clone()));
            (g.store.lifted_calls.borrow_mut())
                .insert(item.meta, (0, Rc::new(term.clone()), false));
            return Ok(());
        }
        if g.meta_solution(item.meta).is_some() {
            count(&cx.e.session.stats.solved_first);
            if crate::unify::solved_lossily(g, item.meta) {
                count(&cx.e.session.stats.lossy);
            }
        }
        let value = cx.eval(term)?;
        let placeholder = cx.eval(&item.placeholder)?;
        g.store.mirrors.filling(item.meta);
        if !cx.unify(&placeholder, &value)? {
            count(&cx.e.session.stats.disagreed);
            return Err(cx.mismatch(&placeholder, &value));
        }
        match placeholder_call(cx, &item.placeholder, term)? {
            Some((s, call, annotated)) => {
                g.store
                    .lifted_calls
                    .borrow_mut()
                    .insert(item.meta, (s, Rc::new(call), annotated));
            }
            None => count(&cx.e.session.stats.read_back),
        }
        Ok(())
    }

    /// W2, before helpers are lifted: the resume points of the obligations
    /// loop, if anything is waiting, so that a queued check holding a
    /// `match` has drafted it; then, as at W4, while anything still waits,
    /// one default and the loop again (invariant 7, D2087). Helpers are
    /// lifted at the end of a declaration part, just before its `finish`
    /// (every caller of `lift` and `lift_signature`), so nothing else in the
    /// part is elaborated after this: it is the part's own quiescence, and a
    /// `match` whose type only a default says needs it before its helper is
    /// made. What still waits is reported at W4.
    pub(crate) fn resume_before_lifting(&self) -> Result<()> {
        if !self.attempt.queue.any_waiting() {
            return Ok(());
        }
        self.solve_obligations_until_stuck()?;
        self.defaults_from(0, |e| e.solve_obligations_until_stuck().map(drop))
    }

    /// W4, the end of a declaration part: the obligations loop, which
    /// resumes (W3), then while anything still waits, one default and the
    /// loop again; then the error of what is still stuck, if anything is.
    /// Otherwise what [`Elaborator::solve_obligations_until_stuck`] gives.
    pub(crate) fn settle_queue(&self) -> Result<Option<Diagnostic>> {
        let mut stuck = self.solve_obligations_until_stuck()?;
        self.defaults_from(0, |e| {
            stuck = e.solve_obligations_until_stuck()?;
            Ok(())
        })?;
        match self.stuck_report()? {
            Some(error) => Err(error),
            None => Ok(stuck),
        }
    }

    /// Ladder step 3 at one of invariant 7's points, for the items from
    /// `from` on: while any of them waits, one default among them and then
    /// `again` (the ladder's steps 1 and 2 at that point), with
    /// [`Queue::settling`] set throughout.
    fn defaults_from(&self, from: usize, mut again: impl FnMut(&Self) -> Result<()>) -> Result<()> {
        let settling = self.attempt.queue.settling.replace(true);
        let defaulted = (|| -> Result<()> {
            while (from..self.attempt.queue.len()).any(|i| self.attempt.queue.waiting(i).is_some())
                && self.apply_default(from)?
            {
                again(self)?;
            }
            Ok(())
        })();
        self.attempt.queue.settling.set(settling);
        defaulted
    }

    /// A `rewrite` rule's own checks, those queued since `from` while the
    /// rule was elaborated, settled before its equation is looked for in
    /// the goal (D2087): ladder step 1 for them, then while any still
    /// waits, one default among them by priority and step 1 again; what
    /// still waits is left for W4 to report. A search for occurrences can't
    /// wait for what its own pattern holds, so the rule is a closed
    /// elaboration of its own: it is elaborated with no expected type, so
    /// what its checks wait on was made inside it and nothing outside it
    /// mentions that before the search reads it (asserted for each default,
    /// below the `metas` it began with). Items queued before the rule are
    /// not touched (invariant 3). Whether anything was resumed or
    /// defaulted.
    pub(crate) fn settle_rule(cx: &Ctx, from: usize, metas: usize) -> Result<bool> {
        Self::settle_closed(cx, from, Some(metas))
    }

    /// A fact given to `omega` or `ring` (`omega [h]`, `ring [2 * h]`),
    /// inferred, with its own checks settled as a `rewrite` rule's are
    /// ([`Elaborator::settle_rule`]): the search reads the fact's type at
    /// once and can't wait for it, so a literal in it that nothing else
    /// types is `Nat` before the search reads it, as it was before
    /// inferred literals waited (stage 7, D2126). Its type is computed
    /// again if anything was settled.
    pub(crate) fn settled_fact(cx: &mut Ctx, fact: &Expr) -> Result<(Term, Value)> {
        let metas = cx.metas().metas.borrow().len();
        let queued = cx.e.attempt.queue.len();
        let (term, ty) = crate::check::infer(cx, fact)?;
        let (term, ty) = crate::check::insert(cx, term, ty)?;
        if Self::settle_rule(cx, queued, metas)? {
            return Ok((term, cx.eval(&cx.quote_folded(&ty)?)?));
        }
        Ok((term, ty))
    }

    /// The error of the first check of a settled search pattern that still
    /// waits, as it would be reported stuck at W4: a reading of the pattern
    /// with such a check (`_ ++ _ = _`, whose `++` waits to be told texts
    /// or lists, stage 7) doesn't elaborate, so its search isn't run with a
    /// placeholder standing for a choice not made.
    pub(crate) fn pattern_stuck(&self) -> Result<Option<Diagnostic>> {
        self.waiting_error(|_| true)
    }

    /// The error of the waiting check whose placeholder is unknown `m`, as
    /// it would be reported stuck: a `rewrite` rule whose side is headed by
    /// it (`(rfl: (_ ++ _) = (_ ++ _))`, its `++` waiting to be told texts
    /// or lists) reports what its own check couldn't decide, not only that
    /// the side's head is unknown.
    pub(crate) fn waiting_error_for(&self, m: usize) -> Result<Option<Diagnostic>> {
        self.waiting_error(|item| item.meta == m)
    }

    /// The error of the first waiting check `which` picks, as it would be
    /// reported stuck at W4.
    fn waiting_error(&self, which: impl Fn(&Item) -> bool) -> Result<Option<Diagnostic>> {
        for i in 0..self.attempt.queue.len() {
            let item = self.attempt.queue.item(i);
            if let Some(needs) = self.attempt.queue.waiting(i)
                && !item.constraint
                && which(&item)
            {
                let blocker = head_meta(&self.ev(), &needs)?;
                let error = self.stuck_error(i, &item, blocker);
                return Ok(Some(self.through_frames(&item, error)));
            }
        }
        Ok(None)
    }

    /// The error of item `i` still waiting on `blocker`: what the check
    /// resuming it says ([`Check::stuck_error`]), else its site's error,
    /// else (queued without one, [`queue_without_error`]) what its own
    /// check says.
    fn stuck_error(&self, i: usize, item: &Item, blocker: Option<usize>) -> Diagnostic {
        (self.attempt.queue.check(i).stuck_error(self, blocker))
            .or_else(|| item.error.as_deref().cloned())
            .or_else(|| item.check.stuck_error(self, blocker))
            .expect("a check queued without its site's error makes its own")
    }

    /// A search pattern, the whole of what its elaboration made (`search.rs`):
    /// settled as a rule is ([`Elaborator::settle_rule`]). It is closed by
    /// construction (nothing else is elaborated with it); its holes' types,
    /// which the rule's check would count as outside, are its own.
    pub(crate) fn settle_pattern(cx: &Ctx) -> Result<bool> {
        Self::settle_closed(cx, 0, None)
    }

    /// [`Elaborator::settle_rule`], with invariant 7's closed check for a
    /// rule that began at unknown `metas`.
    fn settle_closed(cx: &Ctx, from: usize, metas: Option<usize>) -> Result<bool> {
        let e = cx.e;
        if e.attempt.queue.len() <= from {
            return Ok(false);
        }
        let mut any = e.resume_from(from)?;
        if (from..e.attempt.queue.len()).any(|i| e.attempt.queue.waiting(i).is_some()) {
            count(&e.session.stats.rule_settled);
        }
        #[cfg(debug_assertions)]
        if let Some(metas) = metas {
            e.assert_rule_closed(cx, from, metas)?;
        }
        let metas = metas.unwrap_or(0);
        e.defaults_from(from, |e| {
            any = true;
            count(&e.session.stats.rule_defaulted);
            e.resume_from(from).map(drop)
        })?;
        // The dictionaries the rule's operators need whose types are now
        // known (`m + 1` on a number whose type only a waiting literal
        // said: its `Add`), found as `check::compare` finds them: only the
        // rule's own (made at or after `metas`), and only those whose type
        // has no unknown left, so the answer can't depend on when.
        let own: Vec<usize> = (e.attempt.obligations.borrow().iter())
            .filter_map(|ob| match ob.meta.spine().0 {
                Term::Meta(m) if *m >= metas => Some(*m),
                _ => None,
            })
            .collect();
        if !own.is_empty() {
            any |= e.solve_ready_instances_keeping(&[], Some(&own))?;
        }
        Ok(any)
    }

    /// Invariant 7's closed pattern, for [`Elaborator::settle_rule`]: each
    /// rule check that waits, waits on an unknown made inside the rule (at
    /// or after `metas`) that no variable's type in scope mentions and no
    /// check queued before the rule waits on.
    #[cfg(debug_assertions)]
    fn assert_rule_closed(&self, cx: &Ctx, from: usize, metas: usize) -> Result<()> {
        let g = &self.ev();
        let blocker = |i: usize| -> Result<Option<usize>> {
            match self.attempt.queue.waiting(i) {
                Some(needs) => head_meta(g, &needs),
                None => Ok(None),
            }
        };
        let mut outside: HashSet<usize> = HashSet::default();
        for i in 0..from {
            outside.extend(blocker(i)?);
        }
        for ty in &cx.types {
            let term = crate::interfaces::scanned(cx, ty)?;
            let term = self.zonk_keeping(&term, cx.level(), &|_| true)?;
            for (t, _) in term.subterms() {
                if let Term::Meta(m) = t {
                    outside.insert(*m);
                }
            }
        }
        for i in from..self.attempt.queue.len() {
            if self.attempt.queue.check(i).default_priority().is_none() {
                continue;
            }
            if let Some(m) = blocker(i)? {
                debug_assert!(
                    m >= metas && !outside.contains(&m),
                    "a rewrite rule's default would settle an unknown from outside it (invariant 7)"
                );
            }
        }
        Ok(())
    }

    /// Ladder step 3: the first default that applies, by priority and then
    /// creation order, among the waiting items from `from` on: whether one
    /// did.
    fn apply_default(&self, from: usize) -> Result<bool> {
        debug_assert!(
            self.attempt.queue.settling(),
            "a default outside invariant 7's points"
        );
        let mut candidates: Vec<(Priority, usize)> = (from..self.attempt.queue.len())
            .filter(|&i| self.attempt.queue.waiting(i).is_some())
            .filter_map(|i| Some((self.attempt.queue.check(i).default_priority()?, i)))
            .collect();
        candidates.sort();
        for (_, i) in candidates {
            let item = self.attempt.queue.item(i);
            let mut cx = item.saved.ctx(self);
            let snapshot = crate::undo::Snapshot::take(&cx);
            if self.attempt.queue.check(i).apply_default(&mut cx)? {
                debug_assert!(
                    (self.attempt.queue.waiting(i))
                        .is_none_or(|needs| ready(&self.ev(), &needs).unwrap_or(true)),
                    "a default solves what its item waits on"
                );
                count(&self.session.stats.defaulted);
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
        let g = &self.ev();
        let mut waiting: Vec<(usize, Option<usize>)> = Vec::new();
        for i in 0..self.attempt.queue.len() {
            if let Some(needs) = self.attempt.queue.waiting(i) {
                waiting.push((i, head_meta(g, &needs)?));
            }
        }
        if waiting.is_empty() {
            return Ok(None);
        }
        (self.session.stats.stuck).fetch_add(waiting.len(), Ordering::Relaxed);
        // The waiting item each unknown is the placeholder or the type of.
        let mut made_by: HashMap<usize, usize> = HashMap::default();
        for (w, &(i, _)) in waiting.iter().enumerate() {
            let item = self.attempt.queue.item(i);
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
        let mut errors = (reports.iter()).map(|&(_, w)| {
            let (i, blocker) = waiting[w];
            let item = self.attempt.queue.item(i);
            let error = self.stuck_error(i, &item, blocker);
            self.through_frames(&item, error)
        });
        let first = errors.next();
        self.attempt
            .branch_errors
            .borrow_mut()
            .extend(errors.take(2));
        Ok(first)
    }
}

/// A generalising `match` queued to wait for an unknown its generalisation
/// would read (`matching.rs`, `WaitingMatch`; step 4.0 of stage 4).
pub(crate) fn note_match_waited(e: &Elaborator) {
    count(&e.session.stats.match_waited);
}

/// A `match`'s motive check left for when its helper is lifted, because the
/// expected type or a copied variable's type held an unknown that only its
/// alternatives may solve (`matching.rs`, `check_motive`).
pub(crate) fn note_motive_later(e: &Elaborator) {
    count(&e.session.stats.motive_later);
}

/// An application, group, list or `if` elaborated a second time with number
/// literals checked last (`check::retrying`), because the first time failed:
/// the path §5.11 meant to remove once number literals wait (K4); kept by
/// stage 5 for the two gaps `check::retrying` names.
pub(crate) fn note_retried(e: &Elaborator) {
    count(&e.session.stats.retried);
}

/// A leaf of a number group or comparison that couldn't be inferred, so it
/// was undone and checked later against the type the other leaves gave
/// (`numbers::speculate`): one of the three "infer the other side" catches.
pub(crate) fn note_leaf_uninferred(e: &Elaborator) {
    count(&e.session.stats.leaf_uninferred);
}

fn count(counter: &AtomicUsize) {
    Stats::bump(counter);
}

/// Invariant 6 for a `.field` whose receiver is kept as a term (K2,
/// docs/proposals/postponement.md §5.5): the receiver, elaborated since
/// `before`, made none of the choices of §5.10 from an unknown's shape that
/// a type known later could make otherwise: no number literal made `Nat`
/// at once (`numbers::Defaulted`). Counted (`kept`, and `kept chose` for one
/// that did), and asserted in a debug build.
///
/// An operator left with a generic dictionary is not such a choice: its
/// projection is made when the declaration is zonked
/// ([`Elaborator::specialise_operators`]), so its term is the one a type
/// known at once gives (`((x => x * x) 3).toInt`, whose `x * x` waits for
/// the literal's default, is `Nat.mul x x`).
pub(crate) fn kept_receiver(cx: &Ctx, before: &crate::undo::Snapshot) {
    count(&cx.e.session.stats.kept);
    let defaulted = cx.e.attempt.defaulted.borrow().len() > before.defaulted();
    if defaulted {
        count(&cx.e.session.stats.kept_chose);
    }
    debug_assert!(
        !defaulted,
        "a receiver kept as a term chose from an unknown (invariant 6)"
    );
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
        let m = cx.metas().new_meta(cx.span);
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
        /// Whether it is a number literal (`Check::literal`).
        literal: bool,
        /// Its placeholder's source text (`Check::display`).
        shown: Option<&'static str>,
    }

    impl Check for Probe {
        fn literal(&self) -> Option<Rc<num_bigint::BigUint>> {
            self.literal.then(|| Rc::new(7u32.into()))
        }

        fn display(&self, _cx: &Ctx) -> Option<String> {
            self.shown.map(String::from)
        }

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
            cx.metas().solve_meta(blocker, ty(0));
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
            literal: false,
            shown: None,
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
        matches!(e.attempt.queue.state(i), State::Waiting(..))
    }

    fn done(e: &Elaborator, i: usize) -> bool {
        matches!(e.attempt.queue.state(i), State::Done)
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
        assert_eq!(e.attempt.queue.len(), 1);
        before.restore(&mut cx);
        assert_eq!(e.attempt.queue.len(), 0);
        assert!(e.attempt.store.metas.borrow().len() <= meta_of(&first));
        // Again: a new item, with its own placeholder.
        let (blocker, needs) = unknown(&cx);
        let again = push(&cx, probe("a", &log, anything()), needs);
        assert_eq!(e.attempt.queue.len(), 1);
        let placeholder = meta_of(&again);
        // Resumed inside an attempt that is then undone.
        let attempt = Snapshot::take(&cx);
        e.attempt.store.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert!(
            e.attempt
                .store
                .lifted_calls
                .borrow()
                .contains_key(&placeholder)
        );
        assert!(e.attempt.store.meta_solution(placeholder).is_some());
        attempt.restore(&mut cx);
        assert!(waiting(&e, 0));
        assert_eq!(e.attempt.queue.resumptions(0), 0);
        assert!(
            !e.attempt
                .store
                .lifted_calls
                .borrow()
                .contains_key(&placeholder)
        );
        assert!(e.attempt.store.meta_solution(placeholder).is_none());
        assert_eq!(e.attempt.queue.len(), 1);
        // Resumed again, for good.
        e.attempt.store.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.attempt.queue.resumptions(0), 1);
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
        assert_eq!(e.attempt.queue.len(), 1);
        e.rewind(&mark);
        assert_eq!(e.attempt.queue.len(), 0);
        {
            let cx = Ctx::new(&e, span());
            let (_, needs) = unknown(&cx);
            push(&cx, probe("b", &log, anything()), needs);
        }
        e.clear_metas();
        assert_eq!(e.attempt.queue.len(), 0);
        assert!(e.attempt.queue.log.borrow().is_empty());
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
        e.attempt.store.solve_meta(first, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(waiting(&e, 0));
        assert!(!e.resume_from(0).unwrap());
        e.attempt.store.solve_meta(second, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.attempt.queue.resumptions(0), 2);
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
        e.attempt.store.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.attempt.queue.resumptions(0), 1);
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
        e.attempt.store.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        assert_eq!(e.attempt.queue.resumptions(0), 1);
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
        e.attempt.store.solve_meta(outer_blocker, ty(1));
        // An application elaborated now ends with a resume point, for what
        // it queued: nothing.
        crate::check::infer(&mut cx, &expression("((x: Type 1) => x) Type")).unwrap();
        assert!(waiting(&e, 0));
        // One queued inside an application that began after `outer` was.
        let start = e.attempt.queue.len();
        let (inner_blocker, needs) = unknown(&cx);
        push(&cx, probe("inner", &log, anything()), needs);
        e.attempt.store.solve_meta(inner_blocker, ty(1));
        e.resume_application(start).unwrap();
        assert!(waiting(&e, 0));
        assert!(done(&e, 1));
        // The end of the application `outer` was queued in.
        e.resume_application(0).unwrap();
        assert!(done(&e, 0));
        assert_eq!(*log.borrow(), ["resumed inner", "resumed outer"]);
    }

    /// Two probes with defaults, a number and then a record, waiting.
    fn two_with_defaults(cx: &Ctx, log: &Log) {
        let (n, needs) = unknown(cx);
        let mut number = probe("number", log, anything());
        number.default = Some((Priority::Nat, n));
        push(cx, number, needs);
        let (r, needs) = unknown(cx);
        let mut record = probe("record", log, anything());
        record.default = Some((Priority::FieldNames, r));
        push(cx, record, needs);
    }

    /// The order D2013 gives: one default at a time, by priority before
    /// creation order, each followed by resuming.
    const IN_ORDER: [&str; 4] = [
        "default record",
        "resumed record",
        "default number",
        "resumed number",
    ];

    /// Invariant 7 (restated, D2087) and D2013: W4 applies defaults, one at
    /// a time, by priority before creation order, each followed by
    /// resuming; W1 and resuming alone apply none.
    #[test]
    fn defaults_apply_one_at_a_time_field_names_before_nat() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        two_with_defaults(&cx, &log);
        e.resume_application(0).unwrap();
        assert!(!e.resume_from(0).unwrap());
        assert!(log.borrow().is_empty());
        assert!(e.settle_queue().unwrap().is_none());
        assert_eq!(*log.borrow(), IN_ORDER);
    }

    /// Invariant 7: W2, before lifting, is a part's own quiescence and
    /// applies the defaults as W4 does, so a `match`'s helper is made with
    /// its type known; W4 then has nothing left.
    #[test]
    fn defaults_apply_before_lifting() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        two_with_defaults(&cx, &log);
        e.resume_before_lifting().unwrap();
        assert_eq!(*log.borrow(), IN_ORDER);
        assert!(!e.attempt.queue.settling(), "settling only while W2 runs");
        assert!(e.settle_queue().unwrap().is_none());
        assert_eq!(log.borrow().len(), 4);
    }

    /// Invariant 7's closed pattern (D2087): a `rewrite` rule's own items,
    /// those queued since the rule began, are resumed and defaulted before
    /// its search; an item queued before the rule is neither resumed nor
    /// defaulted there (invariant 3), though its blocker is solved too.
    #[test]
    fn a_rules_own_items_are_settled_and_only_those() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (outer_blocker, needs) = unknown(&cx);
        let mut outer = probe("outer", &log, anything());
        outer.default = Some((Priority::FieldNames, outer_blocker));
        push(&cx, outer, needs.clone());
        let from = e.attempt.queue.len();
        let metas = cx.metas().metas.borrow().len();
        // Ready already: resumed, no default needed.
        let (ready, ready_needs) = unknown(&cx);
        push(&cx, probe("ready", &log, anything()), ready_needs);
        cx.metas().solve_meta(ready, ty(0));
        let (r, needs) = unknown(&cx);
        let mut rule = probe("rule", &log, anything());
        rule.default = Some((Priority::FieldNames, r));
        push(&cx, rule, needs);
        assert!(Elaborator::settle_rule(&cx, from, metas).unwrap());
        assert_eq!(
            *log.borrow(),
            ["resumed ready", "default rule", "resumed rule"]
        );
        assert!(waiting(&e, 0) && done(&e, 1) && done(&e, 2));
        assert!(!e.attempt.queue.settling());
        // Nothing of the rule's left: settling again does nothing.
        assert!(!Elaborator::settle_rule(&cx, from, metas).unwrap());
        assert!(e.settle_queue().unwrap().is_none());
        assert_eq!(log.borrow()[3..], ["default outer", "resumed outer"]);
    }

    /// The closed pattern's assertion: a rule whose own item waits on an
    /// unknown made before the rule would settle something outside it.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "from outside it (invariant 7)")]
    fn a_rules_default_on_an_outside_unknown_is_caught() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let log = Log::default();
        let (outside, needs) = unknown(&cx);
        let from = e.attempt.queue.len();
        let metas = cx.metas().metas.borrow().len();
        let mut rule = probe("rule", &log, anything());
        rule.default = Some((Priority::FieldNames, outside));
        push(&cx, rule, needs);
        let _ = Elaborator::settle_rule(&cx, from, metas);
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
        let more: Vec<String> = (e.attempt.branch_errors.borrow().iter())
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
        e.attempt.store.solve_meta(meta_of(&placeholder), zero);
        e.attempt.store.solve_meta(blocker, ty(1));
        let disagreed = e.session.stats.disagreed.load(Ordering::Relaxed);
        let error = e.resume_from(0).expect_err("disagrees");
        assert_eq!(error.code, "E-TYPE-MISMATCH");
        assert_eq!(error.labels[0].span, at);
        assert!(matches!(e.attempt.queue.state(0), State::Failed));
        assert!(e.session.stats.disagreed.load(Ordering::Relaxed) > disagreed);
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
        e.unit.loading_prelude = true;
        let errors: Vec<_> = (e.elaborate_module(&module).into_iter())
            .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "{errors:#?}");
        e.unit.loading_prelude = false;
        e.kernel.machine.glue.set(true);
        let n = DataId(
            (e.kernel.env.datas().iter())
                .position(|d| d.path().rsplit('.').next() == Some("N"))
                .expect("N"),
        );
        let def = |name: &str| {
            let found = (e.kernel.env.defs().iter())
                .position(|d| d.path().rsplit('.').next() == Some(name));
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
        e.attempt.store.solve_meta(meta_of(&placeholder), value);
        e.attempt.store.solve_meta(blocker, ty(1));
        let first = e.session.stats.solved_first.load(Ordering::Relaxed);
        assert!(e.resume_from(0).unwrap());
        assert!(e.session.stats.solved_first.load(Ordering::Relaxed) > first);
        let zonked = crate::unify::zonk_in(&cx.u(), 0, &placeholder, &|_| false, &[]).unwrap();
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
        cx.bind("x", Value::Data(n, Vec::new().into()));
        cx.bind("y", Value::Data(n, Vec::new().into()));
        let log = Log::default();
        let succ = |t: Term| Term::ctor(n, 1, vec![t]);
        let (blocker, needs) = unknown(&cx);
        let placeholder = push(&cx, probe("a", &log, succ(Term::Var(0))), needs);
        assert_eq!(placeholder.spine().1.len(), 2);
        e.attempt.store.solve_meta(blocker, ty(1));
        assert!(e.resume_from(0).unwrap());
        let zonk = |t: &Term, level| crate::unify::zonk_in(&cx.u(), level, t, &|_| false, &[]);
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
        cx.bind("x", Value::Data(n, Vec::new().into()));
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
        let answer = crate::unify::unify_waiting(&cx.u(), 1, &a, &b, &pending).unwrap();
        assert!(matches!(answer, Answer::Blocked(ref pairs) if pairs.len() == 1));
        assert!(cx.g().meta_solution(p).is_none());
        e.attempt.store.solve_meta(blocker, ty(1));
        let lossy = e.session.stats.lossy.load(Ordering::Relaxed);
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.session.stats.lossy.load(Ordering::Relaxed), lossy);
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
        let waited = e.session.stats.waited.load(Ordering::Relaxed);
        assert!(compare_waiting(&mut cx, &placeholder, &value, Failure::Mismatch).unwrap());
        assert_eq!(e.attempt.queue.len(), 2);
        assert!(waiting(&e, 1));
        assert!(e.session.stats.waited.load(Ordering::Relaxed) > waited);
        // Nothing solved yet: neither resumes.
        assert!(!e.resume_from(0).unwrap());
        e.attempt.store.solve_meta(blocker, ty(1));
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
        e.attempt.store.solve_meta(blocker, ty(1));
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
        e.attempt.store.solve_meta(blocker, ty(1));
        let error = e.resume_from(0).expect_err("two isn't zero");
        assert_eq!(error.code, "E-REFL");
        assert_eq!(error.labels[0].span, at);
        assert!(done(&e, 0));
        assert!(matches!(e.attempt.queue.state(1), State::Failed));
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
        assert_eq!(e.attempt.queue.len(), 0);
        let log = Log::default();
        let (_, placeholder) = waiting_item(&cx, &log, anything());
        let (x, unknown_value) = unknown(&cx);
        let a = Value::Eq(
            Rc::new(ty(0)).into(),
            Rc::new(unknown_value).into(),
            Rc::new(zero.clone()).into(),
        );
        let b = Value::Eq(
            Rc::new(ty(0)).into(),
            Rc::new(placeholder).into(),
            Rc::new(two).into(),
        );
        assert!(!compare_waiting(&mut cx, &a, &b, Failure::Mismatch).unwrap());
        assert_eq!(e.attempt.queue.len(), 1);
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
        assert_eq!(e.attempt.queue.len(), 2);
        before.restore(&mut cx);
        assert_eq!(e.attempt.queue.len(), 1);
        assert!(compare_waiting(&mut cx, &placeholder, &value, Failure::Mismatch).unwrap());
        let woken = Snapshot::take(&cx);
        e.attempt.store.solve_meta(blocker, ty(1));
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
        assert!(e.attempt.branch_errors.borrow().is_empty());
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
        e.unit.loading_prelude = true;
        let errors: Vec<_> = (e.elaborate_module(&module).into_iter())
            .filter(|d| d.severity == stitchwort_syntax::Severity::Error)
            .collect();
        assert!(errors.is_empty(), "{errors:#?}");
        // Still as the prelude, so that its names are in scope by their
        // short names, as in a declaration after them.
        e.kernel.machine.glue.set(true);
        let data = |e: &Elaborator, name: &str| {
            let d = (e.kernel.env.datas().iter())
                .position(|d| d.path().rsplit('.').next() == Some(name))
                .unwrap_or_else(|| panic!("{name} declared"));
            Value::Data(DataId(d), Vec::new().into())
        };
        (e, data)
    }

    fn zonked(cx: &Ctx, term: &Term) -> String {
        let zonked = crate::unify::zonk_in(&cx.u(), cx.level(), term, &|_| false, &[]).unwrap();
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
        assert_eq!(e.attempt.queue.len(), 1);
        assert!(waiting(&e, 0));
        assert!(head_meta(&cx.g(), &ty).unwrap().is_some());
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
        // Not at an application's end.
        e.resume_application(0).unwrap();
        assert!(waiting(&e, 0));
        assert!(e.settle_queue().unwrap().is_none());
        assert!(done(&e, 0));
        assert!(cx.conv_now(&ty, &data(&e, "Only")).unwrap());
        // Before lifting, a part's quiescence, too (invariant 7, D2087).
        e.clear_metas();
        let mut cx = Ctx::new(&e, span());
        let (_, ty) = crate::check::infer(&mut cx, &expression("{ only = Z }")).unwrap();
        e.resume_before_lifting().unwrap();
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
        let metas = e.attempt.store.metas.borrow().len();
        let (term, _) = crate::check::infer(&mut cx, &expression("p.row")).unwrap();
        assert_eq!(e.attempt.queue.len(), 1);
        // What inferring the receiver made was undone: the item's
        // placeholder and its type are all that is new.
        assert_eq!(e.attempt.store.metas.borrow().len(), metas + 2);
        assert_eq!(
            head_meta(&cx.g(), &e.attempt.queue.waiting(0).unwrap()).unwrap(),
            Some(blocker)
        );
        e.attempt.store.solve_meta(blocker, data(&e, "P"));
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
        let kept = e.session.stats.kept.load(Ordering::Relaxed);
        crate::check::infer(&mut cx, &expression("({ only = Z }).only")).unwrap();
        // The literal, and the `.only` on it; the literal queued while the
        // prefix form was tried was undone with it.
        assert_eq!(e.attempt.queue.len(), 2);
        assert!(e.session.stats.kept.load(Ordering::Relaxed) > kept);
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
            head_meta(&cx.g(), &e.attempt.queue.waiting(0).unwrap()).unwrap(),
            Some(first)
        );
        let (second, b) = unknown(&cx);
        let mut outer = Ctx::new(&e, span());
        outer.bind("z", data(&e, "N"));
        assert!(outer.unify(&outer.eval(&applied).unwrap(), &b).unwrap());
        let requeued = e.session.stats.requeued.load(Ordering::Relaxed);
        assert!(e.resume_from(0).unwrap());
        assert!(e.session.stats.requeued.load(Ordering::Relaxed) > requeued);
        assert!(waiting(&e, 0));
        assert_eq!(
            head_meta(&cx.g(), &e.attempt.queue.waiting(0).unwrap()).unwrap(),
            Some(second)
        );
        e.attempt.store.solve_meta(second, data(&e, "P"));
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.attempt.queue.resumptions(0), 2);
    }

    /// Invariant 6's assertion: a receiver kept as a term must have made no
    /// choice of §5.10 from an unknown, such as making a number literal
    /// `Nat` at once. Made by hand here: a debug build's assertion says so;
    /// a release build counts it.
    #[test]
    #[cfg_attr(debug_assertions, should_panic(expected = "invariant 6"))]
    fn a_kept_receiver_that_chose_from_an_unknown_is_caught() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        let before = Snapshot::take(&cx);
        let (m, _) = unknown(&cx);
        let defaulted = crate::numbers::Defaulted::literal(m, span(), 1);
        e.attempt.defaulted.borrow_mut().push(defaulted);
        let chose = e.session.stats.kept_chose.load(Ordering::Relaxed);
        kept_receiver(&cx, &before);
        assert!(e.session.stats.kept_chose.load(Ordering::Relaxed) > chose);
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
        let Value::Pi(_, _, dom, _) = force(&cx.g(), ty).unwrap() else {
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
        assert_eq!(e.attempt.queue.len(), 1);
        assert!(waiting(&e, 0));
        assert!(cx.unify(&dom, &data(&e, "P")).unwrap());
        assert!(e.resume_from(0).unwrap());
        assert!(done(&e, 0));
        assert_eq!(e.attempt.queue.len(), 1);
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
            assert_eq!(e.attempt.queue.len(), 1, "{source}");
            let error = e.settle_queue().expect_err("stuck");
            assert_eq!(error.code, "E-CANNOT-INFER", "{source}");
            assert_eq!(
                error.message, "can't tell what `.row` is applied to",
                "{source}"
            );
        }
    }

    /// An item whose check fails once resumed, or, given an unknown,
    /// queues another such item waiting on it and holds.
    struct Failing {
        /// What the item it queues when resumed waits on, and an unknown
        /// to solve once it is queued (so it is resumed in the same pass).
        then: RefCell<Option<(Value, Option<usize>)>>,
    }

    impl Check for Failing {
        fn resume(&self, cx: &mut Ctx) -> Result<Resumed> {
            match self.then.take() {
                Some((needs, solve)) => {
                    push_failing(cx, needs, None);
                    if let Some(m) = solve {
                        cx.metas().solve_meta(m, ty(0));
                    }
                    Ok(Resumed::Holds)
                }
                None => {
                    Err(Diagnostic::error("E-TYPE-MISMATCH", "fails").with_label(span(), "here"))
                }
            }
        }
    }

    fn push_failing(cx: &Ctx, needs: Value, then: Option<(Value, Option<usize>)>) {
        let failing = Failing {
            then: RefCell::new(then),
        };
        let (_, result) = unknown(cx);
        queue(cx, Rc::new(failing), needs, result, error("stuck")).expect("queued");
    }

    /// An error frame that notes its name on the errors it maps.
    struct Tag(&'static str);

    impl ErrorFrame for Tag {
        fn map(&self, _cx: &mut Ctx, e: Diagnostic) -> Diagnostic {
            e.with_note(self.0)
        }
    }

    /// The notes `e` has, which the tags left.
    fn notes(e: &Diagnostic) -> Vec<&str> {
        e.notes.iter().map(String::as_str).collect()
    }

    /// Rule 1 of D2091: a check queued inside a construct that fails after
    /// the construct returned, at a resume point, is reported through the
    /// construct's mapping, as an error inside it inline is; innermost
    /// first when constructs nest.
    #[test]
    fn an_item_failing_after_its_construct_returned_goes_through_its_frames() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        // Inline: the mapping, once.
        let inline = framed(
            &mut cx,
            |_| -> Result<()> { Err(error("inline")) },
            |_| Tag("a"),
        );
        assert_eq!(notes(&inline.unwrap_err()), ["a"]);
        // Later: through both frames, the inner one first.
        let (blocker, needs) = unknown(&cx);
        framed(
            &mut cx,
            |cx| {
                framed(
                    cx,
                    |cx| {
                        push_failing(cx, needs, None);
                        Ok(())
                    },
                    |_| Tag("inner"),
                )
            },
            |_| Tag("outer"),
        )
        .unwrap();
        e.attempt.store.solve_meta(blocker, ty(0));
        let later = e.resume_from(0).expect_err("fails");
        assert_eq!(notes(&later), ["inner", "outer"]);
    }

    /// A frame still running when its item fails is left to the construct,
    /// which maps the error as it passes: applied once, not twice.
    #[test]
    fn a_frame_still_running_maps_its_items_error_once() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let (blocker, needs) = unknown(&cx);
        let result = framed(
            &mut cx,
            |cx| {
                framed(
                    cx,
                    |cx| {
                        push_failing(cx, needs, None);
                        Ok(())
                    },
                    |_| Tag("inner"),
                )?;
                // A resume point inside the outer construct.
                cx.metas().solve_meta(blocker, ty(0));
                cx.e.resume_from(0)?;
                Ok(())
            },
            |_| Tag("outer"),
        );
        assert_eq!(notes(&result.unwrap_err()), ["inner", "outer"]);
    }

    /// An item still waiting at the end is reported through its frames too.
    #[test]
    fn a_stuck_item_is_reported_through_its_frames() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let (_, needs) = unknown(&cx);
        let queued = |cx: &mut Ctx| {
            push_failing(cx, needs, None);
            Ok(())
        };
        framed(&mut cx, queued, |_| Tag("a")).unwrap();
        let stuck = e.settle_queue().expect_err("stuck");
        assert_eq!(
            (stuck.message.as_str(), notes(&stuck)),
            ("stuck", vec!["a"])
        );
    }

    /// What an item queues while it is resumed was made inside its
    /// constructs too: it keeps their frames, applied once whether it fails
    /// during that resumption or after it.
    #[test]
    fn an_item_queued_by_a_resumed_item_keeps_its_frames() {
        for during in [false, true] {
            let e = Elaborator::new();
            let mut cx = Ctx::new(&e, span());
            let (first, needs) = unknown(&cx);
            let (second, next) = unknown(&cx);
            let queued = |cx: &mut Ctx| {
                // During: the item it queues is ready as soon as it is queued.
                push_failing(cx, needs, Some((next, during.then_some(second))));
                Ok(())
            };
            framed(&mut cx, queued, |_| Tag("a")).unwrap();
            e.attempt.store.solve_meta(first, ty(0));
            let error = match e.resume_from(0) {
                Err(error) => error,
                Ok(_) => {
                    assert!(!during);
                    assert_eq!(e.attempt.queue.len(), 2);
                    e.attempt.store.solve_meta(second, ty(0));
                    e.resume_from(0).expect_err("fails")
                }
            };
            assert_eq!(notes(&error), ["a"], "during: {during}");
        }
    }

    /// Rule 2 of D2091: a waiting check's placeholder prints as the source
    /// it stands for while it waits, and as its term once filled.
    #[test]
    fn a_waiting_placeholder_prints_as_its_source() {
        let (e, data) = module(RECORDS);
        let mut cx = Ctx::new(&e, span());
        let (blocker, ty) = unknown(&cx);
        cx.bind("p", ty);
        let (term, _) = crate::check::infer(&mut cx, &expression("p.row")).unwrap();
        assert_eq!(e.attempt.queue.len(), 1);
        let shown = |cx: &Ctx| cx.show(&cx.eval(&term).unwrap());
        assert_eq!(shown(&cx), "p.row");
        e.attempt.store.solve_meta(blocker, data(&e, "P"));
        assert!(e.resume_from(0).unwrap());
        assert!(e.attempt.store.mirrors.keys()[1].is_empty());
        assert_eq!(shown(&cx), "p.row");
        // Taken back with its item.
        let before = Snapshot::take(&cx);
        let (_, other) = unknown(&cx);
        cx.bind("q", other);
        crate::check::infer(&mut cx, &expression("q.row")).unwrap();
        assert_eq!(e.attempt.store.mirrors.keys()[1].len(), 1);
        before.restore(&mut cx);
        assert!(e.attempt.store.mirrors.keys()[1].is_empty());
    }
    fn mirrors(e: &Elaborator) -> [Vec<usize>; 3] {
        e.attempt.store.mirrors.keys()
    }

    /// An attempt that queues a new item (made by `make`), resumes the
    /// older one to done, and resumes another to wait again, then fails:
    /// the mirrors are as they were. Returns them before, inside the
    /// attempt and after.
    fn mirrors_over_an_undone_attempt(make: impl Fn(&mut Probe)) -> [[Vec<usize>; 3]; 3] {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        let log = Log::default();
        let (blocker, needs) = unknown(&cx);
        let (other, other_needs) = unknown(&cx);
        let mut older = probe("older", &log, anything());
        make(&mut older);
        push(&cx, older, needs);
        let mut again = probe("again", &log, anything());
        make(&mut again);
        *again.then.borrow_mut() = Some(other_needs.clone());
        push(&cx, again, other_needs);
        let before = mirrors(&e);
        let attempt = Snapshot::take(&cx);
        // Queued inside the attempt.
        let (_, fresh) = unknown(&cx);
        let mut new = probe("new", &log, anything());
        make(&mut new);
        push(&cx, new, fresh);
        // Resumed to done, and resumed to wait on something else.
        e.attempt.store.solve_meta(blocker, ty(1));
        e.attempt.store.solve_meta(other, ty(1));
        assert!(e.resume_from(0).unwrap());
        let inside = mirrors(&e);
        attempt.restore(&mut cx);
        [before, inside, mirrors(&e)]
    }

    #[test]
    fn an_undone_attempt_restores_the_unfilled_placeholders() {
        let [before, inside, after] = mirrors_over_an_undone_attempt(|_| {});
        assert_eq!(before[0].len(), 2);
        assert_ne!(inside[0], before[0]);
        assert_eq!(after[0], before[0]);
    }

    #[test]
    fn an_undone_attempt_restores_the_placeholder_syntax() {
        let [before, inside, after] = mirrors_over_an_undone_attempt(|p| p.shown = Some("x.row"));
        assert_eq!(before[1].len(), 2);
        assert_ne!(inside[1], before[1]);
        assert_eq!(after[1], before[1]);
    }

    #[test]
    fn an_undone_attempt_restores_the_waiting_literals() {
        let [before, inside, after] = mirrors_over_an_undone_attempt(|p| p.literal = true);
        assert_eq!(before[2].len(), 2);
        assert_ne!(inside[2], before[2]);
        assert_eq!(after[2], before[2]);
    }
}
