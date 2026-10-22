//! Erasure when running programs: proofs and types aren't computed.
//!
//! `stitchwort run` and `stitchwort test` evaluate with the same machine as
//! the checker (`value.rs`), but while [`Erasure::running`] is in effect it
//! skips what can't affect the result, as JS extraction does (DESIGN.md §12):
//!
//! 1. an argument of a definition whose parameter is erased (its type is a
//!    proposition, or a type former such as `Type` or `Nat -> Type`) isn't
//!    evaluated: it's the [`erased`] placeholder;
//! 2. likewise a constructor's erased fields (`Ctor::field_erased`);
//! 3. a definition whose result is erased (a theorem, a proof-producing
//!    function, a type-level function) isn't run once it has all its
//!    arguments: its value is the placeholder;
//! 4. `J` on the placeholder takes its base (in a closed program every proof
//!    of an equation is `refl`, so that's where `J` would go);
//! 5. a `case` on the placeholder, for a type in `Prop`, takes the first
//!    branch with placeholder fields (its only possible one: if it's
//!    impossible, every branch is, and the run fails as unreachable;
//!    docs/proposals/indexed-families.md §6.8).
//!
//! Why it's safe: a proof or a type never decides which way a computation of
//! data goes. Nothing matches on a type, and matching on a proof to produce
//! data is allowed only for a proposition with at most one constructor whose
//! fields are all proofs (`E-PROP-ELIM`, docs/core.md, Lean's subsingleton
//! elimination), so there's only one branch to take, and everything it binds
//! from the proof is erased again. `J`'s only branch is its base. So the run
//! with erasure takes the same branches as the one without, with values that
//! differ only where they're proofs or types, which are never printed or
//! compared (`print` takes `Text`, a test is a `Bool`). Proofs are already
//! checked (and total) when the program runs, so skipping them can't hide a
//! failure. Like JS, a proof in a position that isn't erased (passed through
//! a polymorphic function, say) is still the placeholder if it was made by
//! rule 3, and is only ever passed along.
//!
//! The checker never runs with erasure: conversion compares values that are
//! open terms, where proofs do matter for typing. Erasure is set only by the
//! driver around running a program or a test.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::check;
use crate::globals::{Globals, State};
use crate::term::DefId;
use crate::value::{Head, Spine, Value};

/// The level of the placeholder's variable: never a real one.
const ERASED: usize = usize::MAX - 1;

/// What stands for an erased value: a variable no binder has.
pub fn erased() -> Value {
    Value::Neutral(Head::Var(ERASED), Spine::new())
}

/// Whether `value` is the placeholder (possibly applied to arguments).
pub fn is_erased(value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Var(ERASED), _))
}

/// Which parts of a definition are erased.
pub struct DefErasure {
    /// For each parameter of its type, whether it's erased.
    pub params: Box<[bool]>,
    /// Whether its result (after all the parameters) is.
    pub result: bool,
}

#[derive(Default)]
pub struct Erasure {
    /// Whether the machine is erasing now.
    active: Cell<bool>,
    /// Whether a program or test is running now ([`Erasure::running`]),
    /// erasing or not.
    program: Cell<bool>,
    /// Off only to compare runs with and without erasure, in tests.
    disabled: Cell<bool>,
    /// Each definition's, worked out on first use (from its type, which
    /// never changes once it's final).
    defs: RefCell<Vec<Option<Rc<DefErasure>>>>,
}

/// Erasure in effect until dropped.
pub struct Running<'g> {
    erasure: &'g Erasure,
    was: bool,
    was_program: bool,
}

impl Drop for Running<'_> {
    fn drop(&mut self) {
        self.erasure.active.set(self.was);
        self.erasure.program.set(self.was_program);
    }
}

impl Erasure {
    /// Forgets what was worked out for the definitions from `defs` on, when
    /// they are removed again ([`Globals::rewind`]).
    pub(crate) fn forget_from(&self, defs: usize) {
        self.defs.borrow_mut().truncate(defs);
    }

    /// Erases until the result is dropped: for running a program or test.
    pub fn running(&self) -> Running<'_> {
        let was = self.active.replace(!self.disabled.get());
        let was_program = self.program.replace(true);
        Running {
            erasure: self,
            was,
            was_program,
        }
    }

    /// Whether a program or test is running now, erasing or not (erasure is
    /// [`Erasure::set_disabled`] to compare the two): then dictionaries and
    /// theorems don't stay folded and calls aren't glued, as they do while
    /// checking. So a run without erasure computes its proofs.
    pub fn program_running(&self) -> bool {
        self.program.get()
    }

    /// Whether the machine is erasing now.
    pub fn active(&self) -> bool {
        self.active.get()
    }

    /// Turns erasure off (or back on) for later runs: for tests comparing
    /// the two.
    pub fn set_disabled(&self, disabled: bool) {
        self.disabled.set(disabled);
    }
}

/// Which parts of definition `id` are erased, or `None` if it isn't final.
pub fn of_def(g: &Globals, id: DefId) -> Option<Rc<DefErasure>> {
    if let Some(Some(known)) = g.erasure.defs.borrow().get(id.0) {
        return Some(known.clone());
    }
    let def = g.def(id);
    if def.state != State::Final {
        return None;
    }
    // The type is evaluated normally: erasing inside it would change what
    // the telescope sees.
    let was = g.erasure.active.replace(false);
    let tel = check::telescope(g, &def.ty_value, def.span);
    g.erasure.active.set(was);
    let Ok(tel) = tel else {
        // Out of resources (nothing else can fail: the type is checked).
        // Erasing nothing is safe, and the machine stops at its next step.
        return Some(Rc::new(DefErasure {
            params: Box::new([]),
            result: false,
        }));
    };
    let erasure = Rc::new(DefErasure {
        params: tel.params.iter().map(|(_, _, e)| *e).collect(),
        result: tel.result_erased,
    });
    let mut defs = g.erasure.defs.borrow_mut();
    if defs.len() <= id.0 {
        defs.resize(id.0 + 1, None);
    }
    defs[id.0] = Some(erasure.clone());
    Some(erasure)
}
