//! The native effect runtime (docs/proposals/effect-runtime.md §9, D1162;
//! stage 4b): what replaces the library's `bind`, `foldComp`, `translate`
//! and `runPure` on the machine.
//!
//! The library defines computations as a tree (`Effect.Comp`: `Done` and
//! `Call`). Since stage R2 only those four functions take one apart at run
//! time (and the runner, which takes the result of `main` apart), so the
//! machine replaces them with natives that agree with the tree's equations:
//!
//! - `bind c k` calls `k x` directly when `c` is `Done x`: the machine's
//!   frames are on the heap, so the direct call costs no Rust stack, and
//!   this is an explicit invariant of this backend (§9.1.4), not an
//!   optimisation. Otherwise it builds a third kind of node, `Bind c k`
//!   (tag [`crate::ir::Shapes::bind_node`]), and calls nothing.
//! - One loop (`State::eff_run` in [`crate::machine`]) runs a computation
//!   for a [`Handler`], keeping the continuations of the `Bind`s it has
//!   entered on a persistent linked list in the heap (cells `[k, next]`,
//!   `Erased` for the empty list), until the computation is `Done` with
//!   nothing pending or reaches an operation. The loop runs on the
//!   machine's own frames: applying a continuation pushes a frame whose
//!   result comes back to the loop (`Ret::Eff`), as `Text.fold` does, so
//!   nothing nests in Rust.
//! - Capturing the continuation at an operation is keeping a pointer to the
//!   pending list, which is never changed, so a [`Resume`] can be resumed
//!   any number of times, and later.
//! - A fold resumes lazily where its carrier is a computation (the rule of
//!   §9.2, [`carrier`]): `k y` is `Bind (Done y) (z => fold (rest z))`, run
//!   by whoever runs the clause's result, instead of a call that runs the
//!   rest of the handled computation inside the clause.
//!
//! So a run costs a constant per `bind` and per operation and handler
//! crossed, and the frames pending grow only with the program's own
//! non-tail calls.

use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::{DataId, DefId, Globals, Term};

use crate::erasure::def_shape;
use crate::ir::Shapes;
use crate::value::{Fields, Fun, Value};

/// The natives of the effect runtime.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EffectOp {
    /// `bind c k`.
    Bind,
    /// `foldComp done call c`, resuming by calling (the tree's equation).
    Fold,
    /// The same, resuming lazily: for a fold whose carrier is a
    /// computation.
    FoldLazy,
    /// `row`, then `foldComp done call c`: for a fold whose carrier is
    /// `CompIn row t` with `row` a run-time value. Lazy unless `row` is
    /// `Empty`.
    FoldIn,
    /// A state-passing handler's fold, its clauses rewritten by
    /// [`crate::fusion`]: the state's function, run as a loop with the state
    /// in a variable. For a carrier `CompIn Empty (S -> R)`.
    FoldState,
    /// The same for a carrier `Comp NoOp NoRes (S -> R)`: the result, and
    /// `k`'s, are `Done` of the state's function.
    FoldStateComp,
    /// `translate m c`.
    Translate,
    /// `runPure c`.
    RunPure,
}

impl EffectOp {
    /// Every effect native, in a fixed order: native code names one by its
    /// place here (`native_abi::sw_eff_begin`, `sw_eff_state`), not by an
    /// address.
    pub const ALL: [EffectOp; 8] = [
        EffectOp::Bind,
        EffectOp::Fold,
        EffectOp::FoldLazy,
        EffectOp::FoldIn,
        EffectOp::FoldState,
        EffectOp::FoldStateComp,
        EffectOp::Translate,
        EffectOp::RunPure,
    ];

    /// Its place in [`EffectOp::ALL`].
    pub fn index(self) -> u32 {
        EffectOp::ALL
            .iter()
            .position(|op| *op == self)
            .expect("every effect native is listed") as u32
    }

    pub fn arity(self) -> u32 {
        match self {
            EffectOp::RunPure => 1,
            EffectOp::Bind | EffectOp::Translate => 2,
            EffectOp::Fold | EffectOp::FoldLazy | EffectOp::FoldState | EffectOp::FoldStateComp => {
                3
            }
            EffectOp::FoldIn => 4,
        }
    }
}

/// How a `foldComp` call's handler resumes, from the fold's carrier.
pub enum Carrier<'t> {
    /// A computation: resume lazily.
    Tree,
    /// `CompIn e t` for a row `e` that's a run-time value: a computation
    /// unless `e` is `Empty`, so the fold tests it.
    Row(&'t Term),
    /// Anything else (a plain type at the empty row, a `Delay`): resume by
    /// calling, as the tree's equation says.
    Value,
}

/// Which library definitions the runtime replaces, if the core's effect
/// machinery is loaded with the shapes it was written for. All four or
/// none: a library `foldComp` couldn't take apart a `Bind` node.
pub struct EffectNatives {
    natives: HashMap<DefId, EffectOp>,
    fold: DefId,
    comp: DataId,
    comp_in: Option<DefId>,
    /// `Effects`, and the index of its `Ops`.
    row: Option<(DataId, usize)>,
}

impl EffectNatives {
    pub fn new(g: &Globals) -> Option<EffectNatives> {
        let r = &g.registry;
        let mut natives = HashMap::default();
        for (b, op) in [
            (Builtin::Bind, EffectOp::Bind),
            (Builtin::FoldComp, EffectOp::Fold),
            (Builtin::Translate, EffectOp::Translate),
            (Builtin::RunPure, EffectOp::RunPure),
        ] {
            let id = r.loaded_def(b)?;
            let shape = def_shape(g, id, false).ok()?;
            let runtime = shape.mask().iter().filter(|erased| !**erased).count();
            if shape.result_erased || shape.partial || runtime != op.arity() as usize {
                return None;
            }
            natives.insert(id, op);
        }
        let comp = r.loaded_data(Builtin::Comp)?;
        let sig_map = r.loaded_data(Builtin::SigMap)?;
        let runtime_fields = |d: DataId, c: usize| {
            g.data(d).ctors[c]
                .field_erased
                .iter()
                .filter(|erased| !**erased)
                .count()
        };
        let data = g.data(comp);
        if data.record
            || data.ctors.len() != 2
            || data.unboxed_field().is_some()
            || runtime_fields(comp, 0) != 1
            || runtime_fields(comp, 1) != 2
            || g.data(sig_map).ctors.len() != 1
            || runtime_fields(sig_map, 0) != 2
        {
            return None;
        }
        let row = r.loaded_data(Builtin::Row).and_then(|d| {
            let ops = g.data(d).ctors.iter().position(|c| &*c.name == "Ops")?;
            Some((d, ops))
        });
        Some(EffectNatives {
            natives,
            fold: r.loaded_def(Builtin::FoldComp)?,
            comp,
            comp_in: r.loaded_def(Builtin::CompIn),
            row,
        })
    }

    /// The native that replaces `id`, if any.
    pub fn native(&self, id: DefId) -> Option<EffectOp> {
        self.natives.get(&id).copied()
    }

    /// Whether `id` is `Effect.foldComp`.
    pub fn is_fold(&self, id: DefId) -> bool {
        id == self.fold
    }

    /// How a fold whose carrier (its fourth, erased, argument) is `carrier`
    /// resumes (§9.2 of the note). The elaborator's carrier for `handle` is
    /// `comp_type` of the enclosing row (crates/elab/src/effects.rs):
    /// `Comp …` for a row with an ability or the closed empty row,
    /// `CompIn e t` for a bare row variable, and a `Delay` in a partial
    /// context. An empty-row variant has `CompIn Empty t` there.
    pub fn carrier<'t>(&self, carrier: &'t Term) -> Carrier<'t> {
        let (head, args) = carrier.spine();
        match head.strip_loc() {
            Term::Data(d, _) if *d == self.comp => Carrier::Tree,
            Term::Def(id) if Some(*id) == self.comp_in && args.len() == 2 => {
                match (args[0].strip_loc(), self.row) {
                    (Term::Ctor(d, c, _), Some((row, ops))) if *d == row && *c == ops => {
                        Carrier::Tree
                    }
                    (Term::Var(_), _) => Carrier::Row(args[0]),
                    _ => Carrier::Value,
                }
            }
            _ => Carrier::Value,
        }
    }
}

/// What the run loop does with what it reaches: the four natives, and the
/// runner's stepping.
#[derive(Debug)]
pub enum Handler {
    /// `foldComp done call`: `done v` at the end, `call o k` at an
    /// operation, with `k` resuming lazily if `lazy`.
    Fold {
        done: Value,
        call: Value,
        lazy: bool,
    },
    /// A state-passing handler ([`EffectOp::FoldState`]): `done v s` at the
    /// end; at an operation, `call o k jump s`, whose result, if it's a
    /// jump, goes on with the rest of the computation in the same loop. The
    /// state itself is the loop's (`EffRet`'s), not the handler's.
    State {
        done: Value,
        call: Value,
        /// The carrier is a computation: `k`'s result is `Done` of the
        /// state's function.
        comp: bool,
    },
    /// `translate (MkSigMap inject reply)`.
    Translate { inject: Value, reply: Value },
    /// `runPure`: the result at the end; no operation can happen.
    RunPure,
    /// The runner's: the computation up to its first operation, as `Done`
    /// or `Call` (`main`'s `IO` runner, [`crate::run`]).
    Step,
}

/// A resumption: the rest of a computation after operation `op`, with the
/// continuations pending there, for its handler. Never changed.
#[derive(Debug)]
pub struct Resume {
    pub handler: Rc<Handler>,
    /// The operation's own continuation (`Call`'s second field).
    pub rest: Value,
    /// The pending list where the operation was reached.
    pub pending: Value,
    /// The operation, for a `translate`'s reply; otherwise erased.
    pub op: Value,
}

/// A state-passing handler's function of the state, before it's given one:
/// the loop from computation `arg` (if `rest` is `Erased`) or from `rest
/// arg` (a resumption's), with `pending` after it.
#[derive(Debug)]
pub struct StateRun {
    pub handler: Rc<Handler>,
    pub rest: Value,
    pub arg: Value,
    pub pending: Value,
}

impl StateRun {
    pub(crate) fn take_children(&mut self, out: &mut Vec<Value>) {
        take_handler(&mut self.handler, out);
        crate::value::take_from(std::slice::from_mut(&mut self.rest), out);
        crate::value::take_from(std::slice::from_mut(&mut self.arg), out);
        crate::value::take_from(std::slice::from_mut(&mut self.pending), out);
    }
}

fn take_handler(handler: &mut Rc<Handler>, out: &mut Vec<Value>) {
    if let Some(handler) = Rc::get_mut(handler) {
        match handler {
            Handler::Fold { done, call, .. } | Handler::State { done, call, .. } => {
                crate::value::take_from(std::slice::from_mut(done), out);
                crate::value::take_from(std::slice::from_mut(call), out);
            }
            Handler::Translate { inject, reply } => {
                crate::value::take_from(std::slice::from_mut(inject), out);
                crate::value::take_from(std::slice::from_mut(reply), out);
            }
            Handler::RunPure | Handler::Step => {}
        }
    }
}

impl Resume {
    pub(crate) fn take_children(&mut self, out: &mut Vec<Value>) {
        take_handler(&mut self.handler, out);
        crate::value::take_from(std::slice::from_mut(&mut self.rest), out);
        crate::value::take_from(std::slice::from_mut(&mut self.pending), out);
        crate::value::take_from(std::slice::from_mut(&mut self.op), out);
    }
}

/// Counts of the runtime's work, for tests: like the JS runtime's
/// (`Options::effect_counters` in `crates/js`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EffectCounts {
    /// Iterations of the run loop.
    pub steps: u64,
    /// Continuations pushed onto, and popped off, a pending list.
    pub pushes: u64,
    pub pops: u64,
    /// Operations reaching a fold or a `translate`.
    pub routes: u64,
    /// Lazy resumptions made (a resumption called in a lazy fold).
    pub resumes: u64,
    /// `Bind` nodes made by `bind` (not by a lazy resumption).
    pub binds: u64,
    /// Resumptions a state-passing handler made as a jump of its loop
    /// (stage 4d), not as a call.
    pub jumps: u64,
}

// ------------------------------------------------- shared with native code
//
// The leaves of the effect runtime that the machine (`crate::machine`) and
// native code's helpers (`crate::native_abi`) both use, so the two can't
// drift. They are here, not in the machine's module, so that an executable
// built with `--native` links none of the machine (stage NO6 of
// docs/proposals/native-only.md).

/// What a state-passing handler's clause returned, for its loop
/// ([`state_step`]).
pub(crate) enum StateStep {
    /// Not a jump: the handler's result.
    Value(Value),
    /// A jump `y s′`: the loop goes on from `rest y` with state `s′`; the
    /// jump's own value (`jumped`) is dropped once that has begun.
    Jump {
        handler: Rc<Handler>,
        rest: Value,
        pending: Value,
        y: Value,
        state: Value,
        jumped: Rc<Fun>,
    },
}

/// A state-passing handler's clause returned `v` for the operation whose
/// resumption is `resume`: a jump `v′ s′` goes on with the loop from `rest
/// v′` with state `s′`, on no new frame; anything else is the handler's
/// result. The values taken apart in the machine's order; shared with
/// native code's `native_abi::sw_state_step` (stage NO3 of
/// docs/proposals/native-only.md), so the two can't drift.
pub(crate) fn state_step(counts: &mut EffectCounts, v: Value, resume: Rc<Resume>) -> StateStep {
    let Value::Fun(mut f) = v else {
        return StateStep::Value(v);
    };
    if !matches!(&*f, Fun::Jumped(..)) {
        return StateStep::Value(Value::Fun(f));
    }
    let (y, state) = match Rc::get_mut(&mut f) {
        Some(Fun::Jumped(y, state)) => (std::mem::take(y), std::mem::take(state)),
        _ => match &*f {
            Fun::Jumped(y, state) => (y.clone(), state.clone()),
            _ => unreachable!("a jump"),
        },
    };
    counts.jumps += 1;
    let (handler, rest, pending) = match Rc::try_unwrap(resume) {
        Ok(Resume {
            handler,
            rest,
            pending,
            ..
        }) => (handler, rest, pending),
        Err(resume) => (
            resume.handler.clone(),
            resume.rest.clone(),
            resume.pending.clone(),
        ),
    };
    StateStep::Jump {
        handler,
        rest,
        pending,
        y,
        state,
        jumped: f,
    }
}

/// Field `i` of a constructor's cell: moved out if this is the only
/// reference to the cell, otherwise copied.
#[inline]
pub(crate) fn field(mut fields: Fields, i: usize) -> Value {
    match Rc::get_mut(&mut fields.0) {
        Some(slice) => std::mem::take(&mut slice[i]),
        None => fields[i].clone(),
    }
}

/// The two fields of a constructor's cell, as [`field`] takes one.
#[inline]
pub(crate) fn pair(mut fields: Fields) -> (Value, Value) {
    match Rc::get_mut(&mut fields.0) {
        Some(slice) => (std::mem::take(&mut slice[0]), std::mem::take(&mut slice[1])),
        None => (fields[0].clone(), fields[1].clone()),
    }
}

/// A state-passing handler's fold (`op`: `FoldState` or `FoldStateComp`)
/// on the arguments `arg` gives in order (`done`, `call`, the computation):
/// its function of the state, as the machine's `effect` makes it; shared
/// with native code's `native_abi::sw_eff_state` (stage NO3 of
/// docs/proposals/native-only.md), so the two can't drift.
pub(crate) fn state_handler(s: &Shapes, op: EffectOp, mut arg: impl FnMut() -> Value) -> Value {
    let (done, call, c) = (arg(), arg(), arg());
    let comp = op == EffectOp::FoldStateComp;
    let handler = Rc::new(Handler::State { done, call, comp });
    let run = StateRun {
        handler,
        rest: Value::Erased,
        arg: c,
        pending: Value::Erased,
    };
    state_fn(s, comp, run)
}

/// A state-passing handler's function of the state, `Done` of it if the
/// handler's carrier is a computation.
fn state_fn(s: &Shapes, comp: bool, run: StateRun) -> Value {
    let f = Value::Fun(Rc::new(Fun::StateRun(Rc::new(run))));
    if comp { Value::data(s.done, [f]) } else { f }
}

/// The handler and the computation of `op` (`foldComp` and its lazy
/// variants, `translate` or `runPure`) on the arguments `arg` gives in
/// order, taken apart as the machine's `effect` takes them; shared with
/// native code's `native_abi::sw_eff_begin` (stage NO2 of
/// docs/proposals/native-only.md), so the two can't drift.
pub(crate) fn handler_for(
    s: &Shapes,
    op: EffectOp,
    mut arg: impl FnMut() -> Value,
) -> (Rc<Handler>, Value) {
    match op {
        EffectOp::Fold | EffectOp::FoldLazy | EffectOp::FoldIn => {
            let lazy = match op {
                EffectOp::FoldLazy => true,
                EffectOp::FoldIn => arg().tag() != Some(s.row_empty),
                _ => false,
            };
            let (done, call, c) = (arg(), arg(), arg());
            (Rc::new(Handler::Fold { done, call, lazy }), c)
        }
        EffectOp::Translate => {
            let (m, c) = (arg(), arg());
            let Value::Data(_, m) = m else {
                panic!("internal error: a `SigMap` that isn't `MkSigMap`")
            };
            let (inject, reply) = pair(m);
            (Rc::new(Handler::Translate { inject, reply }), c)
        }
        EffectOp::RunPure => (Rc::new(Handler::RunPure), arg()),
        _ => unreachable!("an effect native that runs a loop"),
    }
}

/// A lazy resumption `resume` called with `y`: `Bind (Done y) r`, `r` the
/// same resumption, not lazy (the machine's `resume`, and native code's
/// apply, `native_abi::sw_apply_prepare`).
#[inline]
pub(crate) fn resume_lazily(
    s: &Shapes,
    counts: &mut EffectCounts,
    resume: &Rc<Resume>,
    y: Value,
) -> Value {
    counts.resumes += 1;
    let k = Value::Fun(Rc::new(Fun::Resume(resume.clone(), false)));
    Value::data(s.bind_node, [Value::data(s.done, [y]), k])
}

// The effect runtime's function values that only build a value (leaves:
// they call no program code), shared by `State::enter` and native code's
// apply (`native_abi::sw_apply_prepare`), so the two can't drift.

/// `DoneK y`: `Done y`.
#[inline]
pub(crate) fn done_k(s: &Shapes, y: Value) -> Value {
    Value::data(s.done, [y])
}

/// A state-passing handler's `k y` (`StateK`): the loop from `rest y`, as a
/// function of the state.
#[inline]
pub(crate) fn state_k(s: &Shapes, resume: &Resume, y: Value) -> Value {
    let Handler::State { comp, .. } = &*resume.handler else {
        unreachable!("a state-passing handler's resumption")
    };
    let run = StateRun {
        handler: resume.handler.clone(),
        rest: resume.rest.clone(),
        arg: y,
        pending: resume.pending.clone(),
    };
    state_fn(s, *comp, run)
}

/// A state-passing handler's `jump v s` (`JumpK`): the jump, for its loop
/// to find (`state_step`).
#[inline]
pub(crate) fn jump_k(v: Value, s: Value) -> Value {
    Value::Fun(Rc::new(Fun::Jumped(v, s)))
}

/// A resumption of a handler around partial code (`DelayK`): `k y` is a
/// `Delay`, and runs nothing (the runner steps it).
#[inline]
pub(crate) fn delay_k(capture: &Rc<crate::run::Capture>, y: Value) -> Value {
    let resumed = crate::value::Delay::Resumed(capture.clone(), y);
    Value::Delay(Rc::new(resumed))
}
