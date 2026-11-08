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
use stitchwort_core::{DataId, DefId, Ev, Term};

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
    /// `row`, the fold's [`Forwards`] (a text), then `foldComp done call
    /// c`: [`EffectOp::FoldIn`] (lazy if `row` isn't `Empty`, so `Erased`
    /// for a carrier that is a computation) for a fold some of whose
    /// clauses only forward their operation, which the loop then skips
    /// (stage B of docs/proposals/operations-in-place.md).
    FoldForwarding,
    /// `translate m c`.
    Translate,
    /// `runPure c`.
    RunPure,
}

impl EffectOp {
    /// Every effect native, in a fixed order: native code names one by its
    /// place here (`native_abi::sw_eff_begin`, `sw_eff_state`), not by an
    /// address.
    pub const ALL: [EffectOp; 9] = [
        EffectOp::Bind,
        EffectOp::Fold,
        EffectOp::FoldLazy,
        EffectOp::FoldIn,
        EffectOp::FoldState,
        EffectOp::FoldStateComp,
        EffectOp::Translate,
        EffectOp::RunPure,
        EffectOp::FoldForwarding,
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
            EffectOp::FoldForwarding => 5,
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
    pub fn new(g: &Ev) -> Option<EffectNatives> {
        let r = &g.env.registry();
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
        let runtime_fields = |d: DataId, c: usize| crate::erasure::stored_count(g, d, c);
        let data = g.data(comp);
        if data.record()
            || data.ctors().len() != 2
            || data.unboxed_field().is_some()
            || runtime_fields(comp, 0) != 1
            || runtime_fields(comp, 1) != 2
            || g.data(sig_map).ctors().len() != 1
            || runtime_fields(sig_map, 0) != 2
        {
            return None;
        }
        let row = r.loaded_data(Builtin::Row).and_then(|d| {
            let ops = g.data(d).ctors().iter().position(|c| &*c.name == "Ops")?;
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
        /// The clauses the loop skips, if any.
        forwards: Option<Rc<str>>,
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
    /// Operations that reached a fold whose clause for them only performs
    /// an operation outwards and resumes with its answer, and went on as
    /// that operation without the clause being called (not counted in
    /// `routes`).
    pub forwards: u64,
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
        EffectOp::Fold | EffectOp::FoldLazy | EffectOp::FoldIn | EffectOp::FoldForwarding => {
            let lazy = match op {
                EffectOp::FoldLazy => true,
                EffectOp::FoldIn | EffectOp::FoldForwarding => arg().tag() != Some(s.row_empty),
                _ => false,
            };
            let (done, call) = (arg(), arg());
            let forwards = match op {
                EffectOp::FoldForwarding => match arg() {
                    Value::Text(table) => Some(table),
                    _ => panic!("internal error: a fold's forwards that aren't a text"),
                },
                _ => None,
            };
            let c = arg();
            let handler = Handler::Fold {
                done,
                call,
                lazy,
                forwards,
            };
            (Rc::new(handler), c)
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

// ------------------------------------------- skipped forwarding clauses
//
// Stage B of docs/proposals/operations-in-place.md. A clause `x, k => bind
// (Call O (r => Done r)) k` (`optional`'s `span`: `k (Parse.span passes)`)
// gives `Call O (y => k y)`, whatever its handler's state: the tree says
// `foldComp d c (Call o rest) = c o (y => foldComp d c (rest y))`, so the
// fold's result is `Call O r`, `r` the eager resumption from where the
// operation was. The loop gives exactly that, without calling the clause,
// and the operation goes on to whoever consumes the fold's result, as the
// clause's would have. Nothing about the handlers between changes, so
// masking, multi-shot and stored resumptions and error exits are as they
// were; only the clause's own work (its frame, `Call`, `Bind` node, closure
// and lazy resumption) is gone.

/// How a Forward clause's operation is built from the one the clause was
/// given (`L` of the handled ability's operation): from the outside in,
/// `L`s and `R`s (`Plus`'s tags), then a constructor of the outer ability.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reperform {
    pub wraps: Vec<u32>,
    pub ctor: u32,
    pub field: Field,
}

/// How a generated forward renames an operation of the other abilities:
/// one with `from`'s `L`s and `R`s outermost (`Plus`'s tags, 0 and 1) goes
/// out with `to`'s in their place. Built from the elaborator's row
/// mappings, whose replies all give the answer back as it is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub from: Vec<u32>,
    pub to: Vec<u32>,
}

/// What a fold's loop skips: each clause's [`Reperform`], if it is one,
/// in the order of the ability's constructors, and the generated forward's
/// rules if it is skipped too.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Skips {
    pub clauses: Vec<Option<Reperform>>,
    pub rules: Option<Vec<Rule>>,
}

/// The run-time field of a [`Reperform`]'s constructor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Field {
    /// None: the operation is the constructor's tag.
    None,
    /// The given operation's one run-time field, the clause's argument.
    Arg,
    /// `()`.
    Unit,
}

/// A fold's skippable clauses, as the text the lowering passes to
/// [`EffectOp::FoldForwarding`], read in place at each operation (no
/// allocation when the handler is made). Two hex digits give the record
/// width `w`; then one record of `w` bytes per clause, in the order of the
/// ability's constructors: `-` for a clause that isn't skipped, else the
/// field (`n`, `a` or `u`), the constructor's tag in four hex digits, and
/// the wraps' tags as hex digits, padded with `.`. If the generated
/// forward is skipped too, `|` and its [`Rule`]s follow, each `from`'s
/// digits, `:`, `to`'s and `;`.
pub struct Forwards;

impl Forwards {
    /// The text for `skips`; `None` if a tag doesn't fit the format.
    pub fn encode(skips: &Skips) -> Option<String> {
        let clauses = &skips.clauses;
        let wraps = clauses
            .iter()
            .flatten()
            .map(|r| r.wraps.len())
            .max()
            .unwrap_or(0);
        let width = 5 + wraps;
        if width > 0xff {
            return None;
        }
        let mut out = format!("{width:02x}");
        for clause in clauses {
            let Some(r) = clause else {
                out.push_str(&"-".repeat(width));
                continue;
            };
            if r.ctor > 0xffff || r.wraps.iter().any(|w| *w > 0xf) {
                return None;
            }
            out.push(match r.field {
                Field::None => 'n',
                Field::Arg => 'a',
                Field::Unit => 'u',
            });
            out.push_str(&format!("{:04x}", r.ctor));
            for w in &r.wraps {
                out.push(char::from_digit(*w, 16).expect("checked"));
            }
            out.push_str(&".".repeat(wraps - r.wraps.len()));
        }
        if let Some(rules) = &skips.rules {
            out.push('|');
            for rule in rules {
                for (part, end) in [(&rule.from, ':'), (&rule.to, ';')] {
                    for t in part {
                        out.push(char::from_digit(*t, 16).filter(|_| *t < 2)?);
                    }
                    out.push(end);
                }
            }
        }
        Some(out)
    }
}

fn hex(bytes: &[u8]) -> Option<u32> {
    bytes
        .iter()
        .try_fold(0u32, |n, b| Some(n * 16 + char::from(*b).to_digit(16)?))
}

/// The operation that clause `o`'s handler (`table`, [`Forwards`]) would
/// perform for it, if that clause is skipped: `Ok` of it, or `Err(o)` back.
/// When the record rebuilds `o` itself (the same constructor, under one
/// `L`, with the argument), `o` is reused.
pub(crate) fn forwarded(s: &Shapes, table: &str, o: Value) -> Result<Value, Value> {
    let bytes = table.as_bytes();
    let Value::Data(tag, fields) = &o else {
        return Err(o);
    };
    if *tag != s.left {
        return renamed(s, bytes, o);
    }
    let inner = &fields[0];
    let Some(ctor) = inner.tag() else {
        return Err(o);
    };
    let Some(width) = bytes.get(..2).and_then(hex) else {
        return Err(o);
    };
    let at = 2 + ctor as usize * width as usize;
    let Some(record) = bytes.get(at..at + width as usize) else {
        return Err(o);
    };
    let (field, rest) = (record[0], &record[1..]);
    let Some(outer) = hex(&rest[..4]) else {
        return Err(o);
    };
    let wraps = &rest[4..];
    let wraps = &wraps[..wraps.iter().position(|b| *b == b'.').unwrap_or(wraps.len())];
    let arg = match (field, inner) {
        (b'a', Value::Data(_, f)) if f.len() == 1 => {
            if outer == ctor && wraps.len() == 1 && hex(wraps) == Some(s.left) {
                return Ok(o);
            }
            Some(f[0].clone())
        }
        (b'u', _) => Some(Value::Tag(s.unit)),
        (b'n', _) => None,
        _ => return Err(o),
    };
    let mut op = match arg {
        Some(a) => Value::data(outer, [a]),
        None => Value::Tag(outer),
    };
    for w in wraps.iter().rev() {
        let w = char::from(*w).to_digit(16).expect("encoded");
        op = Value::data(w, [op]);
    }
    Ok(op)
}

/// An operation `R o′` of the other abilities, renamed by the fold's
/// generated forward as its rules say (after the table's `|`): `Ok` of
/// `inject o′`, or `Err` of the operation back if the forward isn't skipped
/// or no rule matches.
fn renamed(s: &Shapes, bytes: &[u8], o: Value) -> Result<Value, Value> {
    let Some(at) = bytes.iter().position(|b| *b == b'|') else {
        return Err(o);
    };
    let Value::Data(tag, fields) = &o else {
        return Err(o);
    };
    if *tag != s.right {
        return Err(o);
    }
    for rule in bytes[at + 1..].split(|b| *b == b';') {
        let Some(colon) = rule.iter().position(|b| *b == b':') else {
            continue;
        };
        let (from, to) = (&rule[..colon], &rule[colon + 1..]);
        // `o′` under `from`'s wraps.
        let mut inner = &fields[0];
        let mut matched = true;
        for t in from {
            match inner {
                Value::Data(tag, f) if u32::from(*t - b'0') == *tag && f.len() == 1 => {
                    inner = &f[0];
                }
                _ => {
                    matched = false;
                    break;
                }
            }
        }
        if !matched {
            continue;
        }
        if from == to {
            let Value::Data(_, fields) = o else {
                unreachable!("matched above")
            };
            return Ok(field(fields, 0));
        }
        let mut op = inner.clone();
        for t in to.iter().rev() {
            op = Value::data(u32::from(*t - b'0'), [op]);
        }
        return Ok(op);
    }
    Err(o)
}

/// The fold `resume`'s handler skipped its clause for an operation, which
/// goes on as `o`: `Call o r`, `r` the resumption, eager.
#[inline]
pub(crate) fn skipped(
    s: &Shapes,
    counts: &mut EffectCounts,
    o: Value,
    resume: Rc<Resume>,
) -> Value {
    counts.forwards += 1;
    let r = Value::Fun(Rc::new(Fun::Resume(resume, false)));
    Value::data(s.call, [o, r])
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
