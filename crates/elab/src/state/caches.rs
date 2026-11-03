//! [`Caches`]: memo tables, each derivable from the rest of the state, so
//! the elaborator is correct if any of them is emptied at any time
//! ([`Caches::clear`]; `Options::clear_caches_per_declaration` empties them
//! before every declaration, and the rewind test runs a sample that way).
//! An entry may be wrong only in being missing.
//!
//! None is encoded for the check cache or dumped. A rewind keeps each as
//! far as its entries stay true: the two dot-call tables are put back as
//! they were at the mark (their keys are addresses within a source epoch),
//! the tables by definition are cut to the definitions that remain, and the
//! rest are emptied. `Globals::hashes` (content hashes) is a cache too, but
//! lives in `core` until the `Globals` split (step 8).

use std::cell::RefCell;

use stitchwort_core::DataId;
use stitchwort_core::DefId;
use stitchwort_core::collections::{HashMap, HashSet};

use crate::{auto, congruence, dot, effects};

#[derive(Default)]
pub(crate) struct Caches {
    /// What each receiver's dot call was found to call, by the receiver
    /// expression and the field written after it: so a chain `x.f.g.h` finds
    /// each head once instead of inferring the receiver again at every
    /// level (`dot::prefix_form`).
    pub(crate) dot_heads: RefCell<HashMap<dot::CallKey, (dot::TyHead, DefId)>>,
    /// Dot calls whose prefix form failed, with the metavariable state it
    /// failed in: not tried again until that changes (`dot::infer_call`).
    pub(crate) dot_failed: RefCell<HashSet<(dot::CallKey, usize, usize)>>,
    /// Each definition's congruence lemmas for `rewrite`
    /// (`congruence::candidates`), with how many definitions there were
    /// when they were looked up: a later declaration may add one.
    pub(crate) cong_candidates: RefCell<HashMap<DefId, (usize, congruence::Candidates)>>,
    /// For each definition, by `DefId`, once worked out: the data type its
    /// result type is (after all its parameters), if it is one. The decision
    /// search (`auto::decision_procedures`) reads it instead of evaluating
    /// every definition's type each time. Only worked out for a final
    /// definition, whose type, and everything it refers to, never changes;
    /// definitions are only ever added, so an entry never goes stale.
    pub(crate) result_heads: RefCell<Vec<Option<Option<DataId>>>>,
    /// The candidates `auto::decision_procedures` tries after the current
    /// module's own definitions, in order, once worked out, with what the
    /// order was worked out from (`auto::DecisionOrder`).
    pub(crate) decision_order: RefCell<Option<auto::DecisionOrder>>,
    /// Whether a call of final definition `id` with `n` explicit arguments
    /// reaches a computation type (`effects::def_performs_after`), once
    /// worked out: asked for every call in every expression checked, and
    /// fixed once the definition is, like `result_heads`.
    pub(crate) performs: RefCell<HashMap<effects::PerformsKey, bool>>,
}

/// What a rewind mark keeps of [`Caches`]: the tables whose keys don't
/// identify a definition.
pub(crate) struct Mark {
    dot_heads: HashMap<dot::CallKey, (dot::TyHead, DefId)>,
    dot_failed: HashSet<(dot::CallKey, usize, usize)>,
}

impl Caches {
    /// Empties every cache. The elaborator gives the same results.
    pub(crate) fn clear(&mut self) {
        let Caches {
            dot_heads,
            dot_failed,
            cong_candidates,
            result_heads,
            decision_order,
            performs,
        } = self;
        dot_heads.get_mut().clear();
        dot_failed.get_mut().clear();
        cong_candidates.get_mut().clear();
        result_heads.get_mut().clear();
        *decision_order.get_mut() = None;
        performs.get_mut().clear();
    }

    pub(crate) fn mark(&self) -> Mark {
        let Caches {
            dot_heads,
            dot_failed,
            // Cut by definition at a rewind, or emptied.
            cong_candidates: _,
            result_heads: _,
            decision_order: _,
            performs: _,
        } = self;
        Mark {
            dot_heads: dot_heads.borrow().clone(),
            dot_failed: dot_failed.borrow().clone(),
        }
    }

    /// Puts the caches back to a mark taken when there were `defs`
    /// definitions in the world that remains.
    pub(crate) fn rewind(&mut self, mark: &Mark, defs: usize) {
        let Caches {
            dot_heads,
            dot_failed,
            cong_candidates,
            result_heads,
            decision_order,
            performs,
        } = self;
        *dot_heads.get_mut() = mark.dot_heads.clone();
        *dot_failed.get_mut() = mark.dot_failed.clone();
        cong_candidates.get_mut().clear();
        result_heads.get_mut().truncate(defs);
        // It may list definitions declared since the mark, whose numbers the
        // next declarations reuse.
        *decision_order.get_mut() = None;
        performs.get_mut().retain(|(id, ..), _| id.0 < defs);
    }
}
