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

use num_bigint::BigUint;

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
    /// a definition's body (D483, `check.rs` `admit_group`) and its
    /// signature (`declare_def`, SW-1779); never while a program runs.
    pub glue: Cell<bool>,
    /// Whether the kernel is checking: set by [`in_kernel_modes`] for the
    /// admission function it runs. Gluing alone doesn't say so, since the
    /// kernel turns it on for a body and a signature; a mode that changes
    /// what the elaborator's values look like but must leave the kernel's
    /// evaluation as it is tests this too (record eta's fields of folded
    /// calls, `value::eta_fields`).
    pub kernel: Cell<bool>,
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
    /// (docs/proposals/literal-match-facts.md). Kept on rewind: a name
    /// stays valid as long as any value holding one lives.
    pub apart_sets: RefCell<ApartSets>,
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

/// Runs `f` in the kernel's own modes, then puts the caller's back
/// (D2294): gluing off, the transparency set empty and erasure off. Every
/// admission function runs in them, so what the kernel accepts never
/// depends on the modes its caller left; it then turns gluing on for a
/// body and sets a declaration's transparency set itself. The budget stays
/// the caller's: resource limits and cancellation apply to the whole
/// operation. The kernel returns errors as values, so `f` returns rather
/// than unwinds, and nothing needs a guard.
pub(crate) fn in_kernel_modes<T>(
    g: &mut crate::globals::Kernel,
    f: impl FnOnce(&mut crate::globals::Kernel) -> T,
) -> T {
    let m = &g.machine;
    let glue = m.glue.replace(false);
    let kernel = m.kernel.replace(true);
    let transparent = m.transparent.0.replace(Rc::default());
    let erasure = m.erasure.stop();
    let out = f(g);
    let m = &g.machine;
    m.glue.set(glue);
    m.kernel.set(kernel);
    *m.transparent.0.borrow_mut() = transparent;
    m.erasure.put_back(erasure);
    out
}

/// The sets [`crate::value::Apart`] names, each named once: the name of
/// set `i` is `i + 1`, and naming a set already here gives back its name,
/// so a session that matches numbers on every request doesn't grow. Only
/// added to, so a name never changes what it stands for, and two names are
/// equal exactly when their sets are.
#[derive(Default)]
pub struct ApartSets {
    sets: Vec<Rc<[BigUint]>>,
    names: crate::collections::HashMap<Rc<[BigUint]>, u32>,
}

impl ApartSets {
    /// The name of `numbers` (sorted, without duplicates), never 0.
    pub fn name(&mut self, numbers: Rc<[BigUint]>) -> u32 {
        if let Some(&name) = self.names.get(&numbers) {
            return name;
        }
        self.sets.push(numbers.clone());
        let name = u32::try_from(self.sets.len()).expect("fewer than 2^32 sets of numbers");
        self.names.insert(numbers, name);
        name
    }

    /// The set named `name`, which [`ApartSets::name`] gave.
    pub fn get(&self, name: u32) -> Rc<[BigUint]> {
        self.sets[name as usize - 1].clone()
    }

    /// How many sets are named.
    pub fn len(&self) -> usize {
        self.sets.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sets.is_empty()
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
