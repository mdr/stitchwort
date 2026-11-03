//! [`Attempt`]: the inference state of the declaration being elaborated
//! that a failed attempt takes back (`undo.rs`), and that is emptied before
//! each declaration (`Elaborator::clear_metas`).
//!
//! The metavariables themselves are still in `Globals` (`metas`,
//! `meta_trail`, `frozen_metas`, `lifted_calls`, the placeholder tables):
//! they move here with the `Globals` split (D2260). Until then
//! `undo::Snapshot` marks and restores them, and passes their lengths to
//! [`Attempt::restore`] for the tables keyed by metavariable.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::{DefId, Globals, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::unify::{RowConstraint, Waiting};
use crate::{auto, defaults, lift, numbers, queue, rows};

#[derive(Default)]
pub(crate) struct Attempt {
    /// Auto arguments still to be proved in the current declaration.
    pub(crate) obligations: RefCell<Vec<auto::Obligation>>,
    /// Row unknowns made for row-polymorphic functions' implicit row
    /// parameters in the current declaration: defaulted to the empty row if
    /// nothing else decides them (docs/proposals/effect-polymorphism.md
    /// §5.C.1, D1123).
    pub(crate) row_metas: RefCell<Vec<rows::RowMeta>>,
    /// Row comparisons put aside until more is known (`unify_postponing`),
    /// retried with the obligations.
    pub(crate) row_constraints: RefCell<Vec<rows::Postponed>>,
    /// Checks waiting for an unknown type to be known, resumed as it is
    /// (`queue.rs`; docs/proposals/postponement.md).
    pub(crate) queue: queue::Queue,
    /// Comparisons that met a helper not lifted yet, compared again once it
    /// is (`lift::await_helpers`).
    pub(crate) awaiting_helpers: RefCell<Vec<lift::AwaitingHelpers>>,
    /// Metavariables that literals made `Nat` in the current declaration.
    pub(crate) defaulted: RefCell<Vec<numbers::Defaulted>>,
    /// Record literals in the current declaration whose type the
    /// field-name rule chose at its end (`records.rs`), and that type's
    /// name: an implicit argument left unsolved after one is reported at it
    /// (SW-946).
    pub(crate) defaulted_records: RefCell<Vec<(Span, String)>>,
    /// Helpers elaborated in the current declaration and not yet lifted
    /// (`lift.rs`).
    pub(crate) drafts: RefCell<Vec<lift::Draft>>,
    /// The keys of the local definitions met in the current declaration,
    /// for `E-DUPLICATE`. Not emptied by [`Attempt::reset`]: the code that
    /// starts a declaration's local definitions empties it.
    pub(crate) local_keys: RefCell<Vec<(String, Span)>>,
    /// `W-LAMBDA-SHADOW` warnings, found while checking a lambda, where only
    /// a shared reference to the elaborator is at hand. One per lambda
    /// (checking can reach the same lambda twice); drained with `warnings`.
    /// Also others found while checking, such as `W-NO-EFFECT` (one per
    /// statement line, dropped when an attempt is undone, `undo.rs`).
    /// Swapped out while a library file is loaded (`library::Context`), and
    /// not emptied by [`Attempt::reset`].
    pub(crate) lambda_warnings: RefCell<Vec<Diagnostic>>,
    /// Errors from the other bad branches of a case whose first bad branch's
    /// error is the one returned. Where only a shared reference to the
    /// elaborator is at hand; a definition that fails reports them after its
    /// own error, and one that succeeds (the check was an attempt that was
    /// undone) drops them. Not emptied by [`Attempt::reset`]: the
    /// declaration's code drains it.
    pub(crate) branch_errors: RefCell<Vec<Diagnostic>>,
    /// The frozen metavariables standing for local definitions, with their
    /// names, for messages.
    pub(crate) local_metas: RefCell<HashMap<usize, String>>,
    /// Names for unknowns, newest last: an unknown type solved with what an
    /// alias unfolds to (`List Nat`) where the alias (`Counts`) was
    /// expected, with the alias. Only dot notation reads it, for a variable
    /// of that type (`counts.size`), so terms keep the unfolded type
    /// (SW-858, D2092). A list, so an attempt undone truncates it.
    pub(crate) meta_names: RefCell<Vec<(usize, Value)>>,
    /// The dictionaries of operators (`==`, `+`, `<`, …) that weren't found
    /// when the operator was elaborated, by metavariable: the method called
    /// and the field of its interface it projects. One found to be a global
    /// instance by the end is written as that instance's field, as it is
    /// when found at once (`interfaces::specialise_operators`).
    pub(crate) operator_dictionaries: RefCell<HashMap<usize, (DefId, usize)>>,
    /// The dictionaries found in scope (§5.5 step 4: a local variable, or
    /// a superclass path from one), by metavariable, each with the length
    /// of `Globals::meta_trail` before it was solved, so a snapshot's
    /// restore drops those it undoes. Such an operator dictionary stays
    /// generic at the end, even when its solution (a `let`'s value, written
    /// in place of the variable) has since become a global instance's
    /// record: [`crate::Elaborator::specialise_operators`].
    pub(crate) local_dictionaries: RefCell<HashMap<usize, usize>>,
    /// The parameter defaults of the local definitions in scope, by what
    /// their name stands for (`defaults::LocalHead`).
    pub(crate) local_defaults: RefCell<HashMap<defaults::LocalHead, Rc<defaults::LocalDefaults>>>,
    /// The metavariables standing for a `_` written where a proof goes:
    /// `E-UNSOLVED` suggests `?` for them (D641). Cleared with the
    /// metavariables.
    pub(crate) proof_holes: RefCell<stitchwort_core::collections::HashSet<usize>>,
    /// The metavariables standing for the types of an unannotated lambda's
    /// parameters, with the parameters' names, for messages. Cleared with
    /// the metavariables.
    pub(crate) parameter_metas: RefCell<HashMap<usize, String>>,
    /// The instance steps each obligation tree has taken so far (§5.5 step
    /// 7), by its first metavariable. Not restored when an attempt is
    /// undone: steps spent aren't refunded. Emptied with the metavariables
    /// ([`Attempt::reset`]), whose numbers it is keyed by: so it lasts as
    /// long as they do, which is less than a declaration (SW-1149).
    pub(crate) instance_steps: RefCell<HashMap<usize, usize>>,

    // The unifier's own state (`unify.rs`, through `unify::Unifier`).
    /// While `unify::unify_postponing` runs: the row constraints it put
    /// aside. Set and put back by a guard (`state::Scoped`), so not marked.
    pub(crate) postponed: RefCell<Option<Vec<RowConstraint>>>,
    /// Set when a computation whose divergence is a signature's variable
    /// (`{e} a` for a bare `e`) met something it couldn't be compared with
    /// as it stands: a body that then fails may check with `e` total
    /// (docs/proposals/partial-stage-3.md §2.2, D1215). Taken before and
    /// after each body ([`Attempt::take_rigid_divergence`], in
    /// `Elaborator::group`).
    ///
    /// Not restored when an attempt is undone, nor emptied by
    /// [`Attempt::reset`] or a rewind: a meeting anywhere in the body
    /// counts, in an attempt that was undone too. That is how it behaved as
    /// a thread-local; whether it is intended isn't recorded
    /// (elaborator-state.md F7).
    pub(crate) rigid_divergence: Cell<bool>,
    /// While `unify::unify_awaiting_helpers` runs: the frozen metavariables
    /// of the helpers not lifted yet, taken as equal to whatever they meet.
    /// Set by a guard.
    pub(crate) awaited_helpers: RefCell<Option<HashSet<usize>>>,
    /// While `unify::unify_solving_arguments` runs. Set by a guard.
    pub(crate) solving_arguments: Cell<bool>,
    /// The solutions made while comparing two calls of a definition stuck
    /// on an unknown by their arguments (`unify::unify_step`): each
    /// metavariable and its place in `Globals::meta_trail`. Equal arguments
    /// are enough for equal calls, not needed for them, so for a definition
    /// that isn't injective such a solution is one of several. Only counted
    /// (`unify::solved_lossily`, for `queue.rs`), never acted on. Cut at the
    /// trail's length when solutions are taken back; not emptied by a
    /// rewind (as when it was a thread-local: the next declaration's
    /// [`Attempt::reset`] empties it).
    pub(crate) lossy: RefCell<Vec<(usize, usize)>>,
    /// While `unify::unify_waiting` runs: the unknowns the queue still has
    /// to settle (`queue::pending`), on which a pair may wait. Set by a
    /// guard.
    pub(crate) pending: RefCell<HashSet<usize>>,
    /// While `unify::unify_waiting` runs, outside any comparison nested in
    /// it: the pairs set aside. Set by a guard.
    pub(crate) waiting: RefCell<Option<Vec<Waiting>>>,
}

/// Where an [`Attempt`] was: lengths only, so taking one allocates nothing.
/// The tables keyed by metavariable need no entry: they are cut by the
/// metavariables' own mark, which `undo::Snapshot` keeps.
#[derive(Clone, Copy)]
pub(crate) struct Mark {
    obligations: usize,
    row_metas: usize,
    row_constraints: usize,
    queue: queue::Mark,
    awaiting_helpers: usize,
    defaulted: usize,
    defaulted_records: usize,
    drafts: usize,
    local_keys: usize,
    /// How many warnings were noted: a `W-NO-EFFECT` found in an attempt
    /// undone is dropped, since it was judged with what the attempt assumed.
    lambda_warnings: usize,
    branch_errors: usize,
    meta_names: usize,
}

impl Mark {
    /// How many number literals had been made `Nat` at once
    /// (`numbers::Defaulted`).
    pub(crate) fn defaulted(&self) -> usize {
        self.defaulted
    }

    /// How many helpers had been drafted (`lift.rs`).
    pub(crate) fn drafts(&self) -> usize {
        self.drafts
    }
}

impl Attempt {
    /// Where this is now, to [`Attempt::restore`] to.
    pub(crate) fn mark(&self) -> Mark {
        let Attempt {
            obligations,
            row_metas,
            row_constraints,
            queue,
            awaiting_helpers,
            defaulted,
            defaulted_records,
            drafts,
            local_keys,
            lambda_warnings,
            branch_errors,
            meta_names,
            // Keyed by metavariable (or by trail position): cut at the
            // metavariables' mark.
            local_metas: _,
            operator_dictionaries: _,
            local_dictionaries: _,
            local_defaults: _,
            proof_holes: _,
            parameter_metas: _,
            // Cut at the trail's mark.
            lossy: _,
            // Not restored (see the fields).
            rigid_divergence: _,
            instance_steps: _,
            // Each set and put back by a guard around one call, which an
            // attempt is either inside or outside of whole.
            postponed: _,
            awaited_helpers: _,
            solving_arguments: _,
            pending: _,
            waiting: _,
        } = self;
        Mark {
            obligations: obligations.borrow().len(),
            row_metas: row_metas.borrow().len(),
            row_constraints: row_constraints.borrow().len(),
            queue: queue.mark(),
            awaiting_helpers: awaiting_helpers.borrow().len(),
            defaulted: defaulted.borrow().len(),
            defaulted_records: defaulted_records.borrow().len(),
            drafts: drafts.borrow().len(),
            local_keys: local_keys.borrow().len(),
            lambda_warnings: lambda_warnings.borrow().len(),
            branch_errors: branch_errors.borrow().len(),
            meta_names: meta_names.borrow().len(),
        }
    }

    /// Back to `mark`, once the metavariables have been put back: `metas`
    /// is how many there are now and `trail` how long `Globals::meta_trail`
    /// is, both as at the mark.
    pub(crate) fn restore(&self, mark: Mark, g: &Globals, metas: usize, trail: usize) {
        let Attempt {
            obligations,
            row_metas,
            row_constraints,
            queue,
            awaiting_helpers,
            defaulted,
            defaulted_records,
            drafts,
            local_keys,
            lambda_warnings,
            branch_errors,
            local_metas,
            meta_names,
            operator_dictionaries,
            local_dictionaries,
            local_defaults,
            proof_holes,
            parameter_metas,
            lossy,
            // As in `mark`.
            rigid_divergence: _,
            instance_steps: _,
            postponed: _,
            awaited_helpers: _,
            solving_arguments: _,
            pending: _,
            waiting: _,
        } = self;
        lossy.borrow_mut().retain(|(_, at)| *at < trail);
        local_metas.borrow_mut().retain(|m, _| *m < metas);
        operator_dictionaries.borrow_mut().retain(|m, _| *m < metas);
        local_dictionaries.borrow_mut().retain(|_, at| *at < trail);
        local_defaults.borrow_mut().retain(|h, _| h.before(metas));
        proof_holes.borrow_mut().retain(|m| *m < metas);
        parameter_metas.borrow_mut().retain(|m, _| *m < metas);
        obligations.borrow_mut().truncate(mark.obligations);
        row_metas.borrow_mut().truncate(mark.row_metas);
        row_constraints.borrow_mut().truncate(mark.row_constraints);
        queue.restore(mark.queue, g, metas);
        awaiting_helpers
            .borrow_mut()
            .truncate(mark.awaiting_helpers);
        defaulted.borrow_mut().truncate(mark.defaulted);
        defaulted_records
            .borrow_mut()
            .truncate(mark.defaulted_records);
        drafts.borrow_mut().truncate(mark.drafts);
        local_keys.borrow_mut().truncate(mark.local_keys);
        meta_names.borrow_mut().truncate(mark.meta_names);
        // The errors of other bad branches of an attempt undone here.
        branch_errors.borrow_mut().truncate(mark.branch_errors);
        let mut i = 0;
        lambda_warnings.borrow_mut().retain(|w| {
            i += 1;
            i <= mark.lambda_warnings || w.code != crate::no_effect::CODE
        });
    }

    /// Empties what a declaration leaves, before the next one
    /// (`Elaborator::clear_metas`, with the metavariables).
    pub(crate) fn reset(&self) {
        let Attempt {
            obligations,
            row_metas,
            row_constraints,
            queue,
            awaiting_helpers,
            defaulted,
            defaulted_records,
            drafts,
            local_metas,
            meta_names,
            operator_dictionaries,
            local_dictionaries,
            local_defaults,
            proof_holes,
            parameter_metas,
            lossy,
            instance_steps,
            // Each emptied by the code that uses it, as the field says.
            local_keys: _,
            lambda_warnings: _,
            branch_errors: _,
            rigid_divergence: _,
            // Set only inside a call, by a guard.
            postponed: _,
            awaited_helpers: _,
            solving_arguments: _,
            pending: _,
            waiting: _,
        } = self;
        proof_holes.borrow_mut().clear();
        parameter_metas.borrow_mut().clear();
        drafts.borrow_mut().clear();
        local_metas.borrow_mut().clear();
        meta_names.borrow_mut().clear();
        operator_dictionaries.borrow_mut().clear();
        local_dictionaries.borrow_mut().clear();
        local_defaults.borrow_mut().clear();
        obligations.borrow_mut().clear();
        row_metas.borrow_mut().clear();
        row_constraints.borrow_mut().clear();
        queue.clear();
        awaiting_helpers.borrow_mut().clear();
        defaulted.borrow_mut().clear();
        defaulted_records.borrow_mut().clear();
        lossy.borrow_mut().clear();
        instance_steps.borrow_mut().clear();
    }

    /// Empties everything, for `Elaborator::rewind`.
    pub(crate) fn rewind(&mut self) {
        let Attempt {
            obligations,
            row_metas,
            row_constraints,
            queue,
            awaiting_helpers,
            defaulted,
            defaulted_records,
            drafts,
            local_keys,
            lambda_warnings,
            branch_errors,
            local_metas,
            meta_names,
            operator_dictionaries,
            local_dictionaries,
            local_defaults,
            proof_holes,
            parameter_metas,
            instance_steps,
            // Left as they are, as when they were thread-locals: see the
            // fields.
            lossy: _,
            rigid_divergence: _,
            // Set only inside a call, by a guard.
            postponed: _,
            awaited_helpers: _,
            solving_arguments: _,
            pending: _,
            waiting: _,
        } = self;
        obligations.get_mut().clear();
        row_metas.get_mut().clear();
        row_constraints.get_mut().clear();
        queue.clear();
        awaiting_helpers.get_mut().clear();
        defaulted.get_mut().clear();
        defaulted_records.get_mut().clear();
        drafts.get_mut().clear();
        local_keys.get_mut().clear();
        lambda_warnings.get_mut().clear();
        branch_errors.get_mut().clear();
        local_metas.get_mut().clear();
        meta_names.get_mut().clear();
        operator_dictionaries.get_mut().clear();
        local_dictionaries.get_mut().clear();
        local_defaults.get_mut().clear();
        proof_holes.get_mut().clear();
        parameter_metas.get_mut().clear();
        instance_steps.get_mut().clear();
    }

    /// Notes that a computation with a variable divergence couldn't be
    /// compared or moved as it stands ([`Attempt::rigid_divergence`]).
    pub(crate) fn note_rigid_divergence(&self) {
        self.rigid_divergence.set(true);
    }

    /// Whether [`Attempt::note_rigid_divergence`] was called since the last
    /// call of this, which clears it.
    pub(crate) fn take_rigid_divergence(&self) -> bool {
        self.rigid_divergence.replace(false)
    }

    /// Forgets what was noted in [`Attempt::lossy`] of the solutions from
    /// place `len` of the trail on, as they are taken back.
    pub(crate) fn forget_lossy_since(&self, len: usize) {
        self.lossy.borrow_mut().retain(|(_, at)| *at < len);
    }
}
