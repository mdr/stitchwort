//! The evaluator's own state: its modes and the resource limits of the
//! operation in progress (docs/proposals/globals-split.md §2).
//!
//! None of it is environment (the declarations) or inference state (the
//! metavariables). The session owns one `Machine`. Each mode has one home
//! here: [`Machine::glue`], [`Machine::transparent`] and
//! [`Machine::erasure`]'s flags are set around a call by a guard and put
//! back; the budget belongs to the operation.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::term::DefId;

#[derive(Default)]
pub struct Machine {
    /// Resource limits for the operation in progress.
    pub budget: crate::budget::Budget,
    /// Whether running erases proofs and types (`erase.rs`). Never in effect
    /// while checking.
    pub erasure: crate::erase::Erasure,
    /// Whether evaluation keeps a definition applied to all its arguments
    /// as the call, a [`Value::Call`](crate::value::Value::Call), unfolding
    /// it only when something looks inside (glued evaluation,
    /// docs/proposals/folded-calls.md). Off unless the elaborator turns it
    /// on; the kernel is entered with it off and turns it on only to check
    /// a definition's body (D483, `check.rs` `admit_group`); never while a
    /// program runs.
    pub glue: Cell<bool>,
    /// The opaque definitions whose bodies may be used now, sorted: the
    /// transparency set of the declaration being checked
    /// (docs/proposals/opaque-definitions.md §6.4). Any other opaque
    /// definition is neutral while checking ([`crate::value::hidden`]). The
    /// kernel sets it for each check it makes ([`Transparency::set`]), and
    /// puts back what was there. Shared, so a guard can hold it while the
    /// session is borrowed mutably.
    pub transparent: Transparency,
    /// The sets of numbers a variable is known not to be, which
    /// [`crate::value::Apart`] names: in a number case's default arm, the
    /// matched variable is none of its arms' numbers
    /// (docs/proposals/literal-match-facts.md). Only added to, so a name
    /// never changes what it stands for. Each set is sorted. Kept on
    /// rewind: a name stays valid as long as any value holding one lives.
    pub apart_sets: RefCell<Vec<Rc<[num_bigint::BigUint]>>>,
}

impl Machine {
    /// Back to between operations, as a rewind needs: the budget is reset
    /// (its cancellation flag stays) and the transparency set emptied. The
    /// erasure switches and `apart_sets` stay.
    pub fn reset(&self) {
        self.budget.reset();
        *self.transparent.0.borrow_mut() = Rc::default();
    }
}

/// The current transparency set ([`Machine::transparent`]).
#[derive(Clone, Default)]
pub struct Transparency(pub(crate) Rc<RefCell<Rc<[DefId]>>>);

impl Transparency {
    /// Makes `set` (sorted) the transparency set until the guard returned is
    /// dropped, when the set there was comes back.
    #[must_use]
    pub fn set(&self, set: Rc<[DefId]>) -> TransparencyGuard {
        let was = self.0.replace(set);
        TransparencyGuard {
            cell: self.clone(),
            was: Some(was),
        }
    }

    /// Whether the set is empty now: every opaque definition is hidden.
    pub fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }

    /// Whether `id` is in the set now.
    pub fn contains(&self, id: DefId) -> bool {
        self.0.borrow().binary_search(&id).is_ok()
    }
}

/// Puts back the transparency set there was ([`Transparency::set`]).
pub struct TransparencyGuard {
    cell: Transparency,
    was: Option<Rc<[DefId]>>,
}

impl Drop for TransparencyGuard {
    fn drop(&mut self) {
        if let Some(was) = self.was.take() {
            *self.cell.0.borrow_mut() = was;
        }
    }
}
