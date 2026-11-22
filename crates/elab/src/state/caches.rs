//! [`Caches`]: memo tables, each derivable from the rest of the state, so
//! the elaborator is correct if any of them is emptied at any time
//! ([`Caches::clear`]; `Options::clear_caches_per_declaration` empties them
//! before every declaration, and the rewind test runs a sample that way).
//! An entry may be wrong only in being missing.
//!
//! None is encoded for the check cache or dumped. A rewind keeps each as
//! far as its entries stay true: the tables by definition are cut to the
//! definitions that remain, and the rest are emptied, the two dot-call
//! tables included. Their keys are syntax nodes' identities, and a
//! namespace checked again after the rewind may check the same nodes in a
//! world that has changed, so a mark would have to copy them (2 MB a mark
//! on the AoC project, 15,000 rows: most of what a language server's mark
//! cost, elaborator-state.md §9 F11); the namespaces checked again fill
//! them again, at no measured cost (SW-1179). They are also emptied before
//! each declaration, which bounds their size.
//! The content hashes are a cache too, but live in `core`, in the kernel's
//! `EvalCaches`.

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
    /// level (`dot::prefix_form`). `None` where the receiver's type has no
    /// such member, with no unknown in the way.
    pub(crate) dot_heads: RefCell<HashMap<dot::CallKey, Option<(dot::TyHead, DefId)>>>,
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

/// What a rewind mark keeps of [`Caches`]: nothing (see the module's
/// comment).
pub(crate) struct Mark;

impl Caches {
    /// Empties every cache. The elaborator gives the same results.
    pub(crate) fn clear(&mut self) {
        self.forget_dot_calls();
        let Caches {
            dot_heads: _,
            dot_failed: _,
            cong_candidates,
            result_heads,
            decision_order,
            performs,
        } = self;
        cong_candidates.get_mut().clear();
        result_heads.get_mut().clear();
        *decision_order.get_mut() = None;
        performs.get_mut().clear();
    }

    /// Empties the dot-call tables. Done before each declaration
    /// ([`crate::Elaborator::glued`]), to keep them small, and so that
    /// syntax checked again later starts afresh. Their keys are syntax
    /// nodes' identities, which a node made later never shares, so they
    /// need no emptying for one declaration's entries to be kept from the
    /// next one's calls (SW-1800).
    pub(crate) fn forget_dot_calls(&mut self) {
        self.dot_heads.get_mut().clear();
        self.dot_failed.get_mut().clear();
    }

    pub(crate) fn mark(&self) -> Mark {
        Mark
    }

    /// Puts the caches back to a mark taken when there were `defs`
    /// definitions in the world that remains: what may no longer be true
    /// goes.
    pub(crate) fn rewind(&mut self, _: &Mark, defs: usize) {
        // What is checked next may be the same syntax in a changed world.
        self.forget_dot_calls();
        let Caches {
            dot_heads: _,
            dot_failed: _,
            cong_candidates,
            result_heads,
            decision_order,
            performs,
        } = self;
        cong_candidates.get_mut().clear();
        result_heads.get_mut().truncate(defs);
        // It may list definitions declared since the mark, whose numbers the
        // next declarations reuse.
        *decision_order.get_mut() = None;
        performs.get_mut().retain(|(id, ..), _| id.0 < defs);
    }
}
