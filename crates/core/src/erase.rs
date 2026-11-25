//! Erasure when running programs: proofs and types aren't computed.
//!
//! `stitchwort run` and `stitchwort test` evaluate with the same machine as
//! the checker (`value.rs`), but while [`Erasure::running`] is in effect it
//! skips what can't affect the result, as JS extraction does (DESIGN.md §12):
//!
//! 1. an argument of a definition whose parameter is erased (its type is a
//!    proposition, or a type former such as `Type` or `Nat -> Type`) isn't
//!    evaluated: it's the [`erased`] placeholder. A definition's parameters
//!    are read in one view, its type under its own transparency set
//!    ([`def_telescope`]), so one written behind an opaque nickname the
//!    definition unfolds counts, as it does for the runtimes;
//! 2. likewise a constructor's erased fields (`Ctor::field_erased`);
//! 3. a definition whose result is erased (a theorem, a proof-producing
//!    function, a type-level function) isn't run once it has all its
//!    arguments, and a proof definition (`Def::proof`: its type is a
//!    proposition, so a call of it is a proof however many arguments it
//!    has) isn't run at any number of arguments: its value is the
//!    placeholder;
//! 4. `J` on the placeholder takes its base: equality proofs are erased
//!    while running, and `J` uses the erased representation of its base.
//!    That is sound because any proof of `x = y` means `x` and `y` are the
//!    same value in the model (the erasure-preservation contract,
//!    docs/proposals/map-equality.md §7.4.4, D863). The kernel's evaluator
//!    doesn't erase: there a cast into data whose ends agree computes by
//!    rule K whatever its proof, and any other `J` stays stuck on an opaque
//!    proof, such as `Quot.sound` between two different representatives;
//! 5. a `case` on the placeholder, for a type in `Prop`, takes the first
//!    branch with placeholder fields (its only possible one: if it's
//!    impossible, every branch is, and the run fails as unreachable;
//!    docs/proposals/indexed-families.md §6.8);
//! 6. quotients follow the flags the checker sets on them (D921,
//!    docs/proposals/map-equality.md §7.4): `Quot.ind`, `Quot.sound` and a
//!    `Quot.lift` whose result is erased (a proof or a type former) are the
//!    placeholder, their arguments not evaluated; a `Quot.mk` whose
//!    representative is erased (a type, say) holds the placeholder as its
//!    representative, and a lift on it still applies its function. A proof
//!    made by `Quot.sound` or `Quot.ind` is then erased like any other, and
//!    `J` on it takes its base by rule 4: in the model, `Quot.mk a` and
//!    `Quot.mk b` for related `a` and `b` are the same value (the class of
//!    `a`), so the contract holds for them too.
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
//! failure.
//!
//! An open goal's assumption that is a proof is erased too, and the
//! argument above holds for it only if its goal is true: it is the one proof
//! that isn't checked. Under a false goal the run can treat a value as the
//! wrong type (`J` on `h : 2 = 3` takes its base), reach a branch that has
//! no body, or not terminate (an assumed `decreasing` goal). So every `J`
//! that takes its base on the placeholder is noted
//! ([`Erasure::take_transported`]), and a test that relies on an
//! assumption gives no result if its run noted one (docs/core.md
//! "Assumptions (open goals)", Running).
//!
//! Like JS, a proof in a position that isn't erased (passed through
//! a polymorphic function, say) is still the placeholder if it was made by
//! rule 3, and is only ever passed along.
//!
//! The checker never runs with erasure. Conversion never compares two
//! proofs (rule I), but it evaluates open terms, where a cast along a
//! hypothesis whose ends differ (`h: n = m`) must stay stuck: erasure would
//! take its base, as a run may, since in a run the ends are equal values.
//! Erasure is set only by the driver around running a program or a test.

use crate::ev::Ev;
use crate::term::ProofMark;
use std::cell::Cell;
use std::rc::Rc;

use crate::budget::Result;
use crate::check;
use crate::globals::{Def, State};
use crate::term::DefId;
use crate::value::{Apart, Head, Spine, Value};
use stitchwort_syntax::Diagnostic;

/// The level of the placeholder's variable: never a real one.
pub(crate) const ERASED: usize = usize::MAX - 1;

/// What stands for an erased value: a variable no binder has.
pub fn erased() -> Value {
    Value::Neutral(
        Head::Var(ERASED, Apart::NONE, ProofMark::Unknown),
        Spine::new(),
    )
}

/// Whether `value` is the placeholder (possibly applied to arguments).
pub fn is_erased(value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Var(ERASED, _, _), _))
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
    /// Whether `J` has taken its base on the placeholder (rule 4) since
    /// [`Erasure::take_transported`] last asked: the one step whose result
    /// is right only if the erased proof is true, which a run that relies
    /// on an assumption can't promise.
    transported: Cell<bool>,
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

    /// Neither erasing nor running a program, until [`Erasure::put_back`]
    /// is given what this returns: how the kernel's admission checks,
    /// whatever its caller was doing (D2294; "the checker never runs with
    /// erasure").
    pub(crate) fn stop(&self) -> (bool, bool) {
        (self.active.replace(false), self.program.replace(false))
    }

    /// Puts back the modes [`Erasure::stop`] found.
    pub(crate) fn put_back(&self, (active, program): (bool, bool)) {
        self.active.set(active);
        self.program.set(program);
    }

    /// Whether a program or test is running now, erasing or not (erasure is
    /// [`Erasure::set_disabled`] to compare the two): then dictionaries
    /// don't stay folded, theorems and opaque definitions aren't sealed, and
    /// calls aren't glued, as they are while checking. So a run without erasure computes its proofs.
    pub fn program_running(&self) -> bool {
        self.program.get()
    }

    /// Whether the machine is erasing now.
    pub fn active(&self) -> bool {
        self.active.get()
    }

    /// Notes that `J` took its base on the placeholder.
    pub(crate) fn note_transport(&self) {
        self.transported.set(true);
    }

    /// Whether `J` has taken its base on the placeholder since this was
    /// last asked, clearing it.
    pub fn take_transported(&self) -> bool {
        self.transported.replace(false)
    }

    /// Turns erasure off (or back on) for later runs: for tests comparing
    /// the two.
    pub fn set_disabled(&self, disabled: bool) {
        self.disabled.set(disabled);
    }
}

/// Runs `f`, which reads definition `def`'s type, in the one view every
/// reader of its parameters shares: the type under the definition's own
/// transparency set ([`check::def_type`]), glued, not erasing (erasing
/// inside it would change what a telescope sees) and with no program
/// running. That is the type its body was checked against, so it shows at
/// least as many parameters as the body has lambdas, even when some of them
/// are behind an opaque nickname the definition unfolds (`f: Fun unfolding
/// Fun := m => ...`). With every opaque definition hidden it would show
/// fewer, and a runtime that cut a call's erasure mask to that length
/// would disagree with the body's lambdas (SW-3933). The view depends only
/// on the definition (its type, and its transparency set, which is made
/// from its hashed `unfolding` list) and the environment, never on the
/// caller's modes, so the answers remembered per definition below are the
/// same on a cold check and a cached replay (SW-3916).
fn in_own_view<T>(g: &Ev, def: &Def, f: impl FnOnce() -> T) -> T {
    let modes = g.machine.erasure.stop();
    let glue = g.machine.glue.replace(true);
    let set = g.machine.transparent.set(def.transparent.clone());
    let result = f();
    drop(set);
    g.machine.glue.set(glue);
    g.machine.erasure.put_back(modes);
    result
}

/// Definition `id`'s parameters and result, in the view its body was
/// checked in ([`in_own_view`]): what erasure here, `Replay::of_def`, and
/// the runtimes' lowering (`rt` `def_shape`, `specialise`, `js`) all read,
/// so a call and the definition's body agree on which arguments are passed.
pub fn def_telescope(g: &Ev, id: DefId) -> std::result::Result<check::Telescope, Diagnostic> {
    let def = g.def(id);
    in_own_view(g, def, || {
        check::telescope(g, &check::def_type(g, def)?, def.span)
    })
}

/// Which parts of definition `id` are erased, or `None` if it isn't final.
pub fn of_def(g: &Ev, id: DefId) -> Option<Rc<DefErasure>> {
    if let Some(Some(known)) = g.caches.erasure_defs.borrow().get(id.0) {
        return Some(known.clone());
    }
    let def = g.def(id);
    if def.state != State::Final {
        return None;
    }
    let tel = def_telescope(g, id);
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
    let mut defs = g.caches.erasure_defs.borrow_mut();
    if defs.len() <= id.0 {
        defs.resize(id.0 + 1, None);
    }
    defs[id.0] = Some(erasure.clone());
    Some(erasure)
}

/// Which parts of a definition are proofs: the subset of [`DefErasure`]
/// that excludes types. The content hash without proofs
/// ([`crate::hash::proofless_hash`]) leaves out exactly these, since a run
/// never computes them (rules 1 and 3 above).
pub struct ProofPositions {
    /// For each parameter of its type, whether its type is a proposition.
    pub params: Box<[bool]>,
    /// Whether its result (after all the parameters) is a proof.
    pub result: bool,
}

/// Which parts of definition `id` are proofs, or `None` if it isn't final.
/// Out of resources, nothing is a proof (which only makes more differences
/// count) and the answer isn't remembered, as [`of_def`]'s isn't. A reader
/// whose result is remembered or decides something uses
/// [`try_proof_positions`], which passes the running out on.
pub fn proof_positions(g: &Ev, id: DefId) -> Option<Rc<ProofPositions>> {
    try_proof_positions(g, id).unwrap_or_else(|_| {
        Some(Rc::new(ProofPositions {
            params: Box::new([]),
            result: false,
        }))
    })
}

/// [`proof_positions`], with running out as an error instead of the
/// fallback "nothing is a proof": a proofless hash built on the fallback
/// would be remembered, and then depend on which call came first.
pub fn try_proof_positions(g: &Ev, id: DefId) -> Result<Option<Rc<ProofPositions>>> {
    if let Some(Some(known)) = g.caches.proof_positions.borrow().get(id.0) {
        return Ok(Some(known.clone()));
    }
    let def = g.def(id);
    if def.state != State::Final {
        return Ok(None);
    }
    // Reading the type of an already-checked definition can fail only by
    // running out of resources (as [`of_def`] takes it), whichever kind.
    let (params, result) = in_own_view(g, def, || {
        check::proof_telescope(g, &check::def_type(g, def)?, def.span)
    })?;
    let positions = Rc::new(ProofPositions {
        params: params.into(),
        result,
    });
    let mut known = g.caches.proof_positions.borrow_mut();
    if known.len() <= id.0 {
        known.resize(id.0 + 1, None);
    }
    known[id.0] = Some(positions.clone());
    Ok(Some(positions))
}
