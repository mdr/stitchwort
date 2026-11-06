//! [`MetaStore`]: the elaborator's metavariables, their solutions and the
//! tables kept beside them (docs/proposals/globals-split.md §2.1). A part of
//! the [`Attempt`](super::Attempt): `undo::Snapshot` marks and restores it,
//! and `Attempt::reset` empties it with the rest of a declaration's
//! inference state.
//!
//! The evaluator reads only solutions and the epoch, through
//! [`stitchwort_core::Metas`]; the printer reads the placeholder and label
//! tables through the elaborator's [`stitchwort_core::Shown`]. The kernel's
//! admission never sees the store.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::{PlaceholderSyntax, PrintLabel};
use stitchwort_core::{BigUint, Term, Value};
use stitchwort_syntax::Span;

/// A metavariable created by the elaborator. Solutions are closed values
/// (functions of the variables in scope where the metavariable was created).
#[derive(Clone)]
pub struct Meta {
    pub solution: Option<Value>,
    /// Where it was created, for "can't work out" errors.
    pub span: Span,
    /// For the unknown proof of an `auto` argument, one entry per argument
    /// it's applied to (the variables in scope where it was made): whether
    /// neither its statement nor the type of a later variable depends on
    /// that one. Unification may solve it ignoring such an argument where
    /// that argument isn't a variable (SW-323: a proof inside a lambda,
    /// once the lambda is applied to a term).
    pub ignorable: Option<Rc<[bool]>>,
    /// Its type, where whoever made it knew it: the type of the unknown
    /// applied to the first `.1` arguments of its spine (the variables in
    /// scope where it was made), in that context. Unification reads it only
    /// to refuse pairing values whose types plainly differ (SW-919), so it
    /// may be missing.
    pub ty: Option<(Value, usize)>,
    /// For a message that prints it as `?N`: which argument of which call it
    /// stands for ("the argument `b` of `lem`").
    pub origin: Option<Rc<str>>,
}

pub struct MetaStore {
    /// The metavariables of the declaration being elaborated. The kernel's
    /// admission never reads them; the elaborator's uses of the checker as
    /// a typing oracle do (globals-split.md §3.6).
    pub metas: RefCell<Vec<Meta>>,
    /// Every metavariable solution made, newest last, with what it replaced:
    /// how the elaborator undoes a failed attempt (`undo.rs`). Cleared
    /// with `metas`.
    pub meta_trail: RefCell<Vec<(usize, Option<Value>)>>,
    /// Metavariables standing for a lifted `match` whose helper isn't made
    /// yet (docs/proposals/syntax-conveniences.md §4.10): unification never
    /// solves them, so each is equal only to itself. The elaborator solves
    /// them directly once the helpers are declared. Few, so a list; cleared
    /// with `metas`.
    pub frozen_metas: RefCell<Vec<usize>>,
    /// For a frozen metavariable once solved with its helper's call: how many
    /// variables the call is a function of, and the call itself (a term in
    /// them). Zonking puts this term in, instead of reading the solution
    /// value back, which would write out what the arguments of the call
    /// unfold to. The queued checks keep the term each filled its
    /// placeholder with here too, for the same reason. Cleared with `metas`.
    pub lifted_calls: RefCell<HashMap<usize, (usize, Rc<Term>)>>,
    /// What the queue tells the unifier and the printer of its
    /// placeholders ([`QueueMirrors`]). Written only by the queue.
    pub mirrors: QueueMirrors,
    /// How the printer shows calls of local definitions while their owner
    /// is checked (docs/proposals/syntax-conveniences.md §2.5): `go a b`,
    /// not the lifted call with its captures. Cleared with `metas`. Only
    /// affects messages.
    pub print_labels: RefCell<Vec<PrintLabel>>,
    /// Counts the times metavariable solutions were taken back (undone or
    /// cleared), from 1: 0 is the epoch of values made with no
    /// metavariables at all ([`stitchwort_core::Metas::epoch`]). A call's
    /// kept unfolding records the count it was computed at, and is
    /// computed again if the count has moved since: it may have used a
    /// solution that's gone.
    pub meta_epoch: Cell<u64>,
}

impl Default for MetaStore {
    fn default() -> Self {
        MetaStore {
            metas: Default::default(),
            meta_trail: Default::default(),
            frozen_metas: Default::default(),
            lifted_calls: Default::default(),
            mirrors: Default::default(),
            print_labels: Default::default(),
            meta_epoch: Cell::new(1),
        }
    }
}

impl stitchwort_core::Metas for MetaStore {
    fn solution(&self, m: usize) -> Option<Value> {
        self.meta_solution(m)
    }

    fn epoch(&self) -> u64 {
        self.meta_epoch.get()
    }
}

/// How many metavariables there were and how long the trail was: where a
/// [`MetaStore::restore`] goes back to.
#[derive(Clone, Copy)]
pub(crate) struct MetasMark {
    pub(crate) metas: usize,
    pub(crate) trail: usize,
    /// How many were frozen: a list that only grows, so cut to its length
    /// (a freeze of an older metavariable inside the attempt goes too).
    frozen: usize,
}

impl MetaStore {
    pub fn meta_solution(&self, m: usize) -> Option<Value> {
        self.metas.borrow()[m].solution.clone()
    }

    pub fn new_meta(&self, span: Span) -> usize {
        let mut metas = self.metas.borrow_mut();
        metas.push(Meta {
            solution: None,
            span,
            ignorable: None,
            ty: None,
            origin: None,
        });
        metas.len() - 1
    }

    /// Records what unknown `m` stands for (see [`Meta::origin`]).
    pub fn set_meta_origin(&self, m: usize, origin: Rc<str>) {
        self.metas.borrow_mut()[m].origin = Some(origin);
    }

    /// See [`Meta::origin`].
    pub fn meta_origin(&self, m: usize) -> Option<Rc<str>> {
        self.metas.borrow()[m].origin.clone()
    }

    /// Records metavariable `m`'s type (see [`Meta::ty`]): `ty`, the type
    /// of `m` applied to its first `arity` arguments.
    pub fn set_meta_type(&self, m: usize, ty: Value, arity: usize) {
        self.metas.borrow_mut()[m].ty = Some((ty, arity));
    }

    /// See [`Meta::ty`].
    pub fn meta_type(&self, m: usize) -> Option<(Value, usize)> {
        self.metas.borrow()[m].ty.clone()
    }

    /// Records which arguments metavariable `m` may ignore (see
    /// [`Meta::ignorable`]).
    pub fn set_meta_ignorable(&self, m: usize, ignorable: Rc<[bool]>) {
        self.metas.borrow_mut()[m].ignorable = Some(ignorable);
    }

    /// See [`Meta::ignorable`].
    pub fn meta_ignorable(&self, m: usize) -> Option<Rc<[bool]>> {
        self.metas.borrow()[m].ignorable.clone()
    }

    /// Whether metavariable `m` is frozen (see [`MetaStore::frozen_metas`]).
    pub fn meta_frozen(&self, m: usize) -> bool {
        self.frozen_metas.borrow().contains(&m)
    }

    /// Freezes metavariable `m` (see [`MetaStore::frozen_metas`]).
    pub fn freeze_meta(&self, m: usize) {
        self.frozen_metas.borrow_mut().push(m);
    }

    pub fn solve_meta(&self, m: usize, solution: Value) {
        let old = self.metas.borrow_mut()[m].solution.replace(solution);
        self.meta_trail.borrow_mut().push((m, old));
    }

    /// Records that metavariable solutions have been taken back (see
    /// [`MetaStore::meta_epoch`]).
    pub fn metas_taken_back(&self) {
        self.meta_epoch.set(self.meta_epoch.get() + 1);
    }

    /// Where the store is now, for [`MetaStore::restore`].
    pub(crate) fn mark(&self) -> MetasMark {
        MetasMark {
            metas: self.metas.borrow().len(),
            trail: self.meta_trail.borrow().len(),
            frozen: self.frozen_metas.borrow().len(),
        }
    }

    /// Takes back the solutions made since `mark` and drops the
    /// metavariables made since, with the entries of the tables keyed by
    /// them. The queue's [`QueueMirrors`] are put back by the queue's own
    /// restore (`Attempt::restore`).
    pub(crate) fn restore(&self, mark: MetasMark) {
        let MetaStore {
            metas,
            meta_trail,
            frozen_metas,
            lifted_calls,
            print_labels,
            // Put back by the queue's own restore, item by item
            // (`Queue::restore`, which `Attempt::restore` calls next).
            mirrors: _,
            meta_epoch: _,
        } = self;
        let mut metas = metas.borrow_mut();
        let mut trail = meta_trail.borrow_mut();
        // A call's kept unfolding may have used what's taken back here
        // (or a metavariable whose number is about to be reused).
        if trail.len() > mark.trail || metas.len() > mark.metas {
            self.metas_taken_back();
        }
        while trail.len() > mark.trail {
            let (m, old) = trail.pop().expect("longer than the mark's");
            if let Some(meta) = metas.get_mut(m) {
                meta.solution = old;
            }
        }
        metas.truncate(mark.metas);
        frozen_metas.borrow_mut().truncate(mark.frozen);
        lifted_calls.borrow_mut().retain(|m, _| *m < mark.metas);
        print_labels
            .borrow_mut()
            .retain(|l| !matches!(l.head, Term::Meta(m) if m >= mark.metas));
    }

    /// Forgets every metavariable (and the record of their solutions).
    pub fn clear_metas(&self) {
        let MetaStore {
            metas,
            meta_trail,
            frozen_metas,
            lifted_calls,
            mirrors,
            print_labels,
            // Bumped: no kept unfolding is trusted after.
            meta_epoch: _,
        } = self;
        self.metas_taken_back();
        metas.borrow_mut().clear();
        frozen_metas.borrow_mut().clear();
        lifted_calls.borrow_mut().clear();
        mirrors.clear();
        meta_trail.borrow_mut().clear();
        print_labels.borrow_mut().clear();
    }
}

/// What the queue (`queue.rs`) keeps in the store for the unifier and the
/// printer about its placeholders, one entry per placeholder whose check
/// hasn't filled it. All of it is a function of the queue's items and
/// states, written by `Queue::sync_item` alone and put back by
/// `Queue::restore`, which syncs each item whose state went back and
/// forgets those dropped (globals-split.md step 8f, G2; the tests in
/// `queue.rs` check that an attempt undone leaves each table as it was).
/// The fields are private so that a new table has to say how it is
/// written, forgotten and emptied: [`QueueMirrors::set`], `forget` and
/// `clear` destructure the struct.
#[derive(Default)]
pub struct QueueMirrors {
    /// The placeholders of the queued checks that their checks haven't
    /// filled yet: frozen to unification, as `frozen_metas` are, until
    /// filled (docs/proposals/postponement.md, D2016, stage 6).
    unfilled: RefCell<HashSet<usize>>,
    /// How the printer shows a placeholder of those while it is unfilled:
    /// as the source its check stands for (`r.items`, a record literal),
    /// not as an unknown (D2091), with the names of the variables it is
    /// applied to: it is shown so only while applied to those, which then
    /// aren't shown. Only affects messages.
    syntax: RefCell<HashMap<usize, PlaceholderSyntax>>,
    /// The unfilled placeholders of number literals waiting for their type
    /// (K4, step 4.3): the literal, and the type it waits on. A comparison
    /// meeting one against the same numeral at a known type takes that type
    /// (D2110; `unify`).
    literals: RefCell<HashMap<usize, (Rc<BigUint>, Value)>>,
}

impl QueueMirrors {
    /// Whether placeholder `m` is unfilled.
    pub fn is_unfilled(&self, m: usize) -> bool {
        self.unfilled.borrow().contains(&m)
    }

    /// Whether any placeholder is unfilled.
    pub fn any_unfilled(&self) -> bool {
        !self.unfilled.borrow().is_empty()
    }

    /// How `m` is shown while unfilled, if as source.
    pub fn syntax(&self, m: usize) -> Option<PlaceholderSyntax> {
        self.syntax.borrow().get(&m).cloned()
    }

    /// The literal `m` stands for and the type it waits on.
    pub fn literal(&self, m: usize) -> Option<(Rc<BigUint>, Value)> {
        self.literals.borrow().get(&m).cloned()
    }

    /// Whether `m` is the placeholder of a waiting number literal.
    pub fn is_literal(&self, m: usize) -> bool {
        self.literals.borrow().contains_key(&m)
    }

    /// Notes `m` as unfilled, with how it is shown and the literal it
    /// stands for (replacing what was noted of it).
    pub(crate) fn set(
        &self,
        m: usize,
        syntax: Option<PlaceholderSyntax>,
        literal: Option<(Rc<BigUint>, Value)>,
    ) {
        let QueueMirrors {
            unfilled,
            syntax: shown,
            literals,
        } = self;
        unfilled.borrow_mut().insert(m);
        match syntax {
            Some(syntax) => {
                shown.borrow_mut().insert(m, syntax);
            }
            None => {
                shown.borrow_mut().remove(&m);
            }
        }
        match literal {
            Some(literal) => {
                literals.borrow_mut().insert(m, literal);
            }
            None => {
                literals.borrow_mut().remove(&m);
            }
        }
    }

    /// Notes that `m`'s check is filling it: it is no longer frozen, and
    /// the rest of what is noted stays until the check's state is set
    /// (`Queue::set`), which syncs it.
    pub(crate) fn filling(&self, m: usize) {
        self.unfilled.borrow_mut().remove(&m);
    }

    /// Takes `m` out of every table.
    pub(crate) fn forget(&self, m: usize) {
        let QueueMirrors {
            unfilled,
            syntax,
            literals,
        } = self;
        unfilled.borrow_mut().remove(&m);
        syntax.borrow_mut().remove(&m);
        literals.borrow_mut().remove(&m);
    }

    fn clear(&self) {
        let QueueMirrors {
            unfilled,
            syntax,
            literals,
        } = self;
        unfilled.borrow_mut().clear();
        syntax.borrow_mut().clear();
        literals.borrow_mut().clear();
    }

    /// The keys of the three tables, sorted, for tests.
    #[cfg(test)]
    pub(crate) fn keys(&self) -> [Vec<usize>; 3] {
        let sorted = |mut v: Vec<usize>| {
            v.sort();
            v
        };
        [
            sorted(self.unfilled.borrow().iter().copied().collect()),
            sorted(self.syntax.borrow().keys().copied().collect()),
            sorted(self.literals.borrow().keys().copied().collect()),
        ]
    }
}
