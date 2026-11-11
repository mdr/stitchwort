//! What the evaluator, the printer and the checker read: the environment,
//! the machine's modes and caches, and, through two small traits, the
//! elaborator's metavariable solutions and printing hints
//! (docs/proposals/globals-split.md §3, D2291).
//!
//! The kernel's admission builds its own [`Ev`] with [`NoMetas`] and
//! [`NoShown`] (`check.rs`), so no solution the elaborator made is
//! reachable from it. The elaborator builds one over its meta store for
//! everything else, including its use of the checker as a typing oracle,
//! which is outside the trusted base (§3.6).

use std::rc::Rc;

use crate::caches::EvalCaches;
use crate::env::Env;
use crate::globals::UpdateShown;
use crate::globals::{CallDefaults, Data, Def, ParamDefaults, PlaceholderSyntax, PrintLabel};
use crate::machine::Machine;
use crate::term::{DataId, DefId, Name};
use crate::value::Value;

/// The metavariable solutions the evaluator reads.
pub trait Metas {
    /// Metavariable `m`'s solution, if it has one.
    fn solution(&self, m: usize) -> Option<Value>;

    /// Counts the times solutions were taken back. A call's kept unfolding
    /// records the epoch it was computed at; one from another epoch may have
    /// used a solution that's gone. 0 means "made with no metavariables",
    /// valid in any store, so a store's own epochs start at 1.
    fn epoch(&self) -> u64;
}

/// No metavariables: what the kernel's admission evaluates with.
pub struct NoMetas;

impl Metas for NoMetas {
    fn solution(&self, _m: usize) -> Option<Value> {
        None
    }

    fn epoch(&self) -> u64 {
        0
    }
}

/// The elaborator's hints for messages: how the printer shows its
/// placeholders, local definitions and generated helpers, and the flag it
/// sets when a message shows a failed definition. Each affects messages
/// only. The defaults are what the kernel's messages use: no hints.
pub trait Shown {
    /// How an unfilled placeholder `m` of a queued check is shown.
    fn placeholder(&self, _m: usize) -> Option<PlaceholderSyntax> {
        None
    }

    /// Whether there are any labels ([`Shown::print_label`]): a fast path.
    fn has_print_labels(&self) -> bool {
        false
    }

    /// The first local definition's label `found` accepts, as its name, the
    /// number of variables its head is applied to first, and its defaults
    /// (see [`PrintLabel`]).
    fn print_label(
        &self,
        _found: &mut dyn FnMut(&PrintLabel) -> bool,
    ) -> Option<(Name, usize, Option<Rc<CallDefaults>>)> {
        None
    }

    /// How a call of the record update helper `id` is shown.
    fn update_shown(&self, _id: DefId) -> Option<Rc<UpdateShown>> {
        None
    }

    /// For a lifted `match`'s helper `id`: which of its parameters are the
    /// scrutinees, in the order written. A call of it is shown as the
    /// `match` (`(match s₁, s₂ with …)`), not by the helper's internal name.
    fn match_columns(&self, _id: DefId) -> Option<Rc<[usize]>> {
        None
    }

    /// Records that the printer showed a call of lifted `match` helper `id`
    /// as `text`, so a message that contains `text` can say where that
    /// `match` is (`Elaborator::explain_lifted`).
    fn note_match_shown(&self, _id: DefId, _text: &str) {}

    /// The parameter defaults of definition `id`'s header.
    fn param_defaults(&self, _id: DefId) -> Option<Rc<ParamDefaults>> {
        None
    }

    /// Whether a message's showing a failed definition is still worth
    /// recording ([`Shown::note_failed_mentioned`]): not when nobody
    /// records it, or it already has been.
    fn wants_failed_mention(&self) -> bool {
        false
    }

    /// Records that a message showed a term that uses a failed definition.
    fn note_failed_mentioned(&self) {}

    /// Whether a term that mentions final definition `id` may be stuck on
    /// an open goal's assumption: `id` is checked assuming the goal holds
    /// and computes (docs/core.md "Assumptions (open goals)"). The printer
    /// then computes the shown term to see ([`Shown::note_stuck_on_goal`]).
    fn waits_on_goal(&self, _id: DefId) -> bool {
        false
    }

    /// Whether a message's showing a term stuck on an open goal's
    /// assumption is still worth recording ([`Shown::note_stuck_on_goal`]).
    fn wants_stuck_mention(&self) -> bool {
        false
    }

    /// Records that a message showed a term that, computed, is stuck on an
    /// open goal's assumption: whatever went wrong can't be decided until
    /// the goal is filled. `goals` are the assumptions it is stuck on.
    fn note_stuck_on_goal(&self, _goals: &[DefId]) {}
}

/// No hints.
pub struct NoShown;

impl Shown for NoShown {}

/// What the evaluator reads, by reference: built by value from four
/// borrows and passed as `&Ev`.
#[derive(Clone, Copy)]
pub struct Ev<'a> {
    pub env: &'a Env,
    pub machine: &'a Machine,
    pub caches: &'a EvalCaches,
    pub metas: &'a dyn Metas,
    pub shown: &'a dyn Shown,
}

impl<'a> Ev<'a> {
    /// The kernel's: no metavariables and no hints.
    pub fn kernel(env: &'a Env, machine: &'a Machine, caches: &'a EvalCaches) -> Ev<'a> {
        Ev {
            env,
            machine,
            caches,
            metas: &NoMetas,
            shown: &NoShown,
        }
    }

    pub fn def(&self, id: DefId) -> &'a Def {
        self.env.def(id)
    }

    pub fn data(&self, id: DataId) -> &'a Data {
        self.env.data(id)
    }

    pub fn find_data(&self, name: &str) -> Option<DataId> {
        self.env
            .datas()
            .iter()
            .position(|d| &*d.name == name)
            .map(DataId)
    }

    pub fn meta_solution(&self, m: usize) -> Option<Value> {
        self.metas.solution(m)
    }
}
