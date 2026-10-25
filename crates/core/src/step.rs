//! Running a partial computation: `step`, the run mode of `Delay`
//! (docs/proposals/partial.md §7.4).
//!
//! The kernel gives `Delay` no meaning: its constants never compute
//! (`partial.rs`). The runner gives it one, through `step`, which runs a
//! `Delay` value up to its next *observation*:
//!
//! - `Now v`: it finished, with `v`;
//! - `Later rest`: one tick, a recursive call was requested; `rest` is the
//!   rest of the computation, suspended, with nothing of the call run yet;
//! - `Call op`: an operation for the host, which `step` never performs: the
//!   runner performs it and resumes the step with the reply.
//!
//! This is the stack-safe machine of `crates/partial-model/src/machine.rs`,
//! on the evaluator's values, with the same frames and the same rules. A
//! `Delay` value is one of the five constants applied to all its arguments
//! (`now v`, `lift c`, `bindD d k`, `mapSig m d`, `pfix f x`), and building
//! one runs nothing: `pfix f x` holds `f` and `x`, and `f x` runs only when
//! it's stepped. Pending work is an explicit stack of frames on the heap:
//!
//! - `Bind k`: the continuation of a `bindD`;
//! - `Map m`: a `mapSig`, translating operations on the way out and replies
//!   on the way back;
//! - `Tie f`: the description `f` of a `pfix`, which answers the requests
//!   `L (Recur y)` that reach it with `pfix f y`;
//! - `Await`: a caller waiting for a recursive call's result, with its
//!   continuation and its own frames;
//! - `Handle`: a handler, `foldD done call`, waiting below the computation
//!   it handles (docs/proposals/partial-handlers.md §5.1).
//!
//! The rules (the equations of §7.4.2, which the model transcribes as its
//! reference): entering `pfix f x` runs the body `f x` under `Tie f`, with no
//! tick; a request reaching a `Tie` is exactly one `Later`, whose rest enters
//! the callee and then returns to the caller; other operations pass through
//! a `Tie` with their reply unchanged. A request in tail position (nothing
//! pending above the caller's `Tie`, and the continuation `y => Done y`)
//! keeps no frame, so a loop runs in constant space.
//!
//! Handlers (`foldD done call d`, the sixth constant): stepping one pushes a
//! `Handle` frame and steps `d` above it. `Now v` reaching it runs `done v`;
//! a `Later` suspends the whole machine, handler included, so it passes the
//! handler by as one tick. *Every* operation that reaches a `Handle` frame
//! is captured, the ones the handler only forwards included (its `call`
//! re-issues them, below it), so an operation never passes a handler: a
//! `Tie` only answers requests with no handler above it, and an `Await`'s
//! `upper` never holds a `Handle` frame. Capture moves the frames above the
//! handler into the resumption `k` (a [`Value::Resumption`], given to `call`
//! as the argument of a partly applied `foldD`, so applying it builds the
//! value `foldD k y` and runs nothing); stepping `k y` puts the handler and
//! the frames back on top of the stack, moving them if nothing else holds
//! them and copying them otherwise (a handler that resumes more than once).
//! The frames need no adjusting: an `Await`'s indices are into its own
//! `upper`, and a `Tie` holds no position. Only the operation's own `back`,
//! the `Map` frames it passed, indexes the stack: it's rebased onto the
//! captured frames. This is the model's `capture` and `restore`
//! (`crates/partial-model/src/machine.rs`).
//!
//! Each transition is a step of the operation's budget, and the frame stack
//! is bounded by its frame limit. Trusted for "runs what was written", not
//! for consistency: a bug here could run a program wrongly, but never make
//! the checker accept something false, since nothing computed here is given
//! back to it.

use std::rc::Rc;

use crate::budget::Result;
use crate::globals::Globals;
use crate::partial::Primitive;
use crate::registry::Builtin;
use crate::term::{DataId, DefId, Term};
use crate::value::{Elim, Head, Spine, Value, apply, force};

/// The prelude declarations a `Delay` is built from.
#[derive(Clone, Copy)]
struct Shapes {
    comp: DataId,
    plus: DataId,
    rec: DataId,
    now: DefId,
    lift: DefId,
    bind: DefId,
    map_sig: DefId,
    pfix: DefId,
    fold_d: Option<DefId>,
}

impl Shapes {
    fn new(g: &Globals) -> Shapes {
        let data = |b: Builtin| g.registry.data(b).expect("the prelude declares it");
        let prim = |p: Primitive| {
            g.builtins
                .primitive_id(p)
                .expect("the prelude declares the partial constants")
        };
        Shapes {
            comp: data(Builtin::Comp),
            plus: data(Builtin::Plus),
            rec: data(Builtin::Rec),
            now: prim(Primitive::Now),
            lift: prim(Primitive::Lift),
            bind: prim(Primitive::BindD),
            map_sig: prim(Primitive::MapSig),
            pfix: prim(Primitive::Pfix),
            fold_d: g.builtins.primitive_id(Primitive::FoldD),
        }
    }
}

/// What a `Call`'s rest does with the reply.
#[derive(Clone)]
enum Cont {
    /// `y => Done y`. Kept apart so a tail request can be recognised.
    Done,
    Fn(Value),
}

#[derive(Clone)]
enum Frame {
    Bind(Value),
    /// A `mapSig`'s mapping: `MkSigMap inject reply`.
    Map(Value, Value),
    Tie(Value),
    /// A caller waiting for a recursive call's result `v`: `v` is
    /// translated back through `upper`'s `Map` frames (those `back` lists,
    /// with each operation as it was before that frame translated it),
    /// `upper` is put back (it starts with the caller's `Tie`), and the
    /// caller goes on with `cont v`. Operations from the callee pass it by.
    Await {
        cont: Cont,
        upper: Vec<Frame>,
        back: Vec<(usize, Value)>,
    },
    /// A handler, `foldD done call`: `Now v` reaching it runs `done v`, a
    /// `Later` passes it by (the whole machine suspends), and an operation
    /// reaching it captures the frames above it as the resumption.
    Handle {
        done: Value,
        call: Value,
    },
}

/// What an operation reaching a `Handle` frame captured, the inside of a
/// resumption `k`: the handler, the frames above it, the operation's
/// continuation, and the `Map` frames it passed (indices into `frames`), so
/// the reply can be translated back. Stepping `k y` puts the handler and
/// these frames back on top of the stack, wherever it is then, and goes on
/// with `cont` of `y` translated.
#[derive(Clone)]
pub struct Capture {
    done: Value,
    call: Value,
    frames: Vec<Frame>,
    cont: Cont,
    back: Vec<(usize, Value)>,
}

impl std::fmt::Debug for Capture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<resumption of {} frames>", self.frames.len())
    }
}

enum Focus {
    /// Run a `Delay` value.
    Eval(Value),
    /// Enter `pfix f x`: run `f x` under `Tie f`.
    Enter(Value, Value),
    /// A `Comp` value, from `lift` or a continuation.
    Comp(Value),
    /// A result, for the frame on top.
    Ret(Value),
}

/// A suspended computation: what to do next, and the pending frames.
pub struct Machine {
    focus: Focus,
    frames: Vec<Frame>,
    shapes: Shapes,
}

/// What one step observes.
pub enum Obs {
    /// Finished, with this value.
    Now(Value),
    /// One tick: a recursive call was requested. The rest is suspended.
    Later(Machine),
    /// An operation (of the computation's row) for the host. Nothing has
    /// been performed: the step goes on when the host replies.
    Call(Value, Pending),
}

/// The rest of a step, waiting for an operation's reply.
pub struct Pending {
    machine: Machine,
    cont: Cont,
    back: Vec<(usize, Value)>,
}

impl Pending {
    /// Continues the step with the host's reply to the operation.
    pub fn reply(self, g: &Globals, reply: Value) -> Result<Obs> {
        let mut m = self.machine;
        let reply = translate_back(g, &m.frames, &self.back, reply)?;
        m.focus = Focus::Comp(apply_cont(g, &m.shapes, &self.cont, reply)?);
        m.run(g)
    }
}

impl Machine {
    /// A machine about to run `delay`, a closed value of a `Delay` type.
    pub fn start(g: &Globals, delay: Value) -> Machine {
        Machine {
            focus: Focus::Eval(delay),
            frames: Vec::new(),
            shapes: Shapes::new(g),
        }
    }

    /// `step`: runs to the next observation.
    pub fn step(self, g: &Globals) -> Result<Obs> {
        self.run(g)
    }

    /// How many frames are pending: memory on the heap, not host stack.
    pub fn frames(&self) -> usize {
        self.frames.len()
    }

    fn run(mut self, g: &Globals) -> Result<Obs> {
        let s = self.shapes;
        loop {
            g.budget.step()?;
            g.budget.frames(self.frames.len())?;
            self.focus = match std::mem::replace(&mut self.focus, Focus::Ret(Value::Refl)) {
                Focus::Eval(d) => {
                    let (prim, args) = match constant(g, &s, d)? {
                        Built::Constant(prim, args) => (prim, args),
                        Built::Resumed(capture, reply) => {
                            self.restore(g, capture, reply)?;
                            continue;
                        }
                    };
                    match prim {
                        Primitive::Now => Focus::Ret(args[3].clone()),
                        Primitive::Lift => Focus::Comp(args[3].clone()),
                        Primitive::BindD => {
                            self.frames.push(Frame::Bind(args[5].clone()));
                            Focus::Eval(args[4].clone())
                        }
                        Primitive::MapSig => {
                            let Value::Ctor(_, 0, m) = force(g, args[5].clone())? else {
                                panic!("internal error: a `SigMap` that isn't `MkSigMap`")
                            };
                            self.frames.push(Frame::Map(m[0].clone(), m[1].clone()));
                            Focus::Eval(args[6].clone())
                        }
                        // Building `pfix f x` ran nothing; stepping it
                        // enters the body. No tick.
                        Primitive::Pfix => Focus::Enter(args[4].clone(), args[5].clone()),
                        // Entering a handler: its frame waits below the
                        // handled computation. No tick.
                        Primitive::FoldD => {
                            self.frames.push(Frame::Handle {
                                done: args[6].clone(),
                                call: args[7].clone(),
                            });
                            Focus::Eval(args[8].clone())
                        }
                        Primitive::Delay => unreachable!("a type isn't a value"),
                    }
                }
                Focus::Enter(f, x) => {
                    self.frames.push(Frame::Tie(f.clone()));
                    Focus::Eval(apply(g, f, x)?)
                }
                Focus::Comp(c) => match force(g, c)? {
                    Value::Ctor(d, 0, fields) if d == s.comp => Focus::Ret(fields[0].clone()),
                    Value::Ctor(d, 1, fields) if d == s.comp => {
                        let cont = cont(&s, &fields[1]);
                        match self.route(g, fields[0].clone(), cont)? {
                            Routed::Obs(obs) => return Ok(obs),
                            Routed::Handled(m) => {
                                self = *m;
                                continue;
                            }
                        }
                    }
                    _ => panic!("internal error: `lift` of something that isn't a computation"),
                },
                Focus::Ret(v) => match self.frames.pop() {
                    None => return Ok(Obs::Now(v)),
                    Some(Frame::Bind(k)) => Focus::Eval(apply(g, k, v)?),
                    Some(Frame::Handle { done, .. }) => Focus::Eval(apply(g, done, v)?),
                    Some(Frame::Map(..) | Frame::Tie(_)) => Focus::Ret(v),
                    Some(Frame::Await { cont, upper, back }) => {
                        let v = translate_back(g, &upper, &back, v)?;
                        self.frames.extend(upper);
                        Focus::Comp(apply_cont(g, &s, &cont, v)?)
                    }
                },
            };
        }
    }

    /// Operation `op` leaves the focus: it's passed outwards through the
    /// frames. A `Handle` captures it (no tick); a `Tie` answers a recursion
    /// request (one tick); one that reaches the bottom is returned to the
    /// host, unperformed.
    fn route(mut self, g: &Globals, mut op: Value, cont: Cont) -> Result<Routed> {
        let s = self.shapes;
        let mut back: Vec<(usize, Value)> = Vec::new();
        let mut j = self.frames.len();
        while j > 0 {
            j -= 1;
            match &self.frames[j] {
                Frame::Bind(_) | Frame::Await { .. } => {}
                Frame::Handle { .. } => {
                    self.capture(g, j, op, cont, back)?;
                    return Ok(Routed::Handled(Box::new(self)));
                }
                Frame::Map(inject, _) => {
                    let target = apply(g, inject.clone(), op.clone())?;
                    back.push((j, std::mem::replace(&mut op, target)));
                }
                Frame::Tie(f) => {
                    let Value::Ctor(d, side, fields) = force(g, op)? else {
                        panic!("internal error: an operation outside `Plus` reached a `pfix`")
                    };
                    debug_assert_eq!(d, s.plus);
                    if side == 1 {
                        op = fields[0].clone();
                        continue;
                    }
                    let Value::Ctor(r, 0, request) = force(g, fields[0].clone())? else {
                        panic!("internal error: a recursion request that isn't `Recur`")
                    };
                    debug_assert_eq!(r, s.rec);
                    let f = f.clone();
                    // `Later (bindD (pfix f y) (\v -> tie f (resume (cont v))))`.
                    let upper = self.frames.split_off(j);
                    debug_assert!(
                        !upper.iter().any(|f| matches!(f, Frame::Handle { .. })),
                        "a recursion request passed a handler"
                    );
                    let tail = upper.len() == 1 && matches!(cont, Cont::Done) && back.is_empty();
                    if !tail {
                        let back = back.into_iter().map(|(k, src)| (k - j, src)).collect();
                        self.frames.push(Frame::Await { cont, upper, back });
                    }
                    // A tail call keeps no frame: the caller's `Tie` would
                    // only pass the result on, and the callee installs its
                    // own.
                    self.focus = Focus::Enter(f, request[0].clone());
                    return Ok(Routed::Obs(Obs::Later(self)));
                }
            }
        }
        Ok(Routed::Obs(Obs::Call(
            op,
            Pending {
                machine: self,
                cont,
                back,
            },
        )))
    }

    /// `op` reached the `Handle` frame at `h`: the frames above it become
    /// the resumption `k`, and the machine goes on with `call op k`, below
    /// the handler.
    fn capture(
        &mut self,
        g: &Globals,
        h: usize,
        op: Value,
        cont: Cont,
        back: Vec<(usize, Value)>,
    ) -> Result<()> {
        let frames = self.frames.split_off(h + 1);
        let Some(Frame::Handle { done, call }) = self.frames.pop() else {
            unreachable!("a capture at a frame that isn't a `Handle`")
        };
        // `back` indexes the stack; the captured frames started at `h + 1`.
        let back = back
            .into_iter()
            .map(|(j, src)| (j - (h + 1), src))
            .collect();
        let capture = Capture {
            done,
            call: call.clone(),
            frames,
            cont,
            back,
        };
        let fold_d = self
            .shapes
            .fold_d
            .expect("a `Handle` frame comes from `foldD`");
        let mut spine = Spine::new();
        spine.push(Elim::App(
            Value::Resumption(Rc::new(capture)),
            crate::term::Icit::Explicit,
        ));
        let k = Value::Neutral(Head::Def(fold_d), spine);
        self.focus = Focus::Eval(apply(g, apply(g, call, op)?, k)?);
        Ok(())
    }

    /// Stepping `k y`: the handler and the captured frames go back on top
    /// of the stack, and the handled computation goes on with `y`. The
    /// frames are moved if nothing else holds the resumption, and copied if
    /// something does: it may be resumed again
    /// (docs/proposals/partial-handlers.md §5.2).
    fn restore(&mut self, g: &Globals, capture: Rc<Capture>, reply: Value) -> Result<()> {
        let capture = Rc::try_unwrap(capture).unwrap_or_else(|shared| (*shared).clone());
        let reply = translate_back(g, &capture.frames, &capture.back, reply)?;
        self.frames.push(Frame::Handle {
            done: capture.done,
            call: capture.call,
        });
        self.frames.extend(capture.frames);
        self.focus = Focus::Comp(apply_cont(g, &self.shapes, &capture.cont, reply)?);
        Ok(())
    }
}

/// Where an operation went.
// Boxing `Obs` would add an allocation per operation on the hot path; the value
// is built and matched at once, so the size difference is never stored.
#[allow(clippy::large_enum_variant)]
enum Routed {
    /// Out of this step: a tick, or an operation for the host.
    Obs(Obs),
    /// A handler took it: the machine goes on with the handler's clause.
    Handled(Box<Machine>),
}

/// What a `Delay` value is built by.
enum Built {
    /// One of the constants, with all its arguments.
    Constant(Primitive, Vec<Value>),
    /// A resumption applied to a reply, `k y`: `foldD` applied to just a
    /// [`Value::Resumption`], then `y`.
    Resumed(Rc<Capture>, Value),
}

/// A `Delay` value: the constant it's built by, and its arguments, or a
/// resumption applied to a reply.
fn constant(g: &Globals, s: &Shapes, d: Value) -> Result<Built> {
    let Value::Neutral(Head::Def(id), spine) = force(g, d)? else {
        panic!("internal error: running something that isn't a `Delay`")
    };
    let prim = [
        (s.now, Primitive::Now),
        (s.lift, Primitive::Lift),
        (s.bind, Primitive::BindD),
        (s.map_sig, Primitive::MapSig),
        (s.pfix, Primitive::Pfix),
    ]
    .into_iter()
    .chain(s.fold_d.map(|c| (c, Primitive::FoldD)))
    .find_map(|(c, p)| (c == id).then_some(p));
    let mut args: Vec<Value> = spine
        .into_vec()
        .into_iter()
        .map(|e| match e {
            Elim::App(v, _) => v,
            Elim::J { .. } => panic!("internal error: a `Delay` stuck on `J`"),
        })
        .collect();
    match prim {
        Some(p) if args.len() == p.arity() => Ok(Built::Constant(p, args)),
        Some(Primitive::FoldD) if args.len() == 2 && matches!(&args[0], Value::Resumption(_)) => {
            let reply = args.pop().expect("two arguments");
            let Some(Value::Resumption(capture)) = args.pop() else {
                unreachable!("checked above")
            };
            Ok(Built::Resumed(capture, reply))
        }
        _ => panic!("internal error: running something that isn't a `Delay`"),
    }
}

/// The continuation of a `Call`.
fn cont(s: &Shapes, rest: &Value) -> Cont {
    // `y => Done y`, as the elaborator writes a request or an operation.
    if let Value::Lam(_, _, closure) = rest {
        let mut body = closure.body.as_ref();
        while let Term::Loc(_, t) | Term::Ann(t, _) = body {
            body = t;
        }
        if let Term::Ctor(d, 0, fields) = body
            && *d == s.comp
            && let [field] = &fields[..]
            && matches!(field.strip_loc(), Term::Var(0))
        {
            return Cont::Done;
        }
    }
    Cont::Fn(rest.clone())
}

fn apply_cont(g: &Globals, s: &Shapes, cont: &Cont, v: Value) -> Result<Value> {
    match cont {
        Cont::Done => Ok(Value::Ctor(s.comp, 0, [v].into())),
        Cont::Fn(rest) => apply(g, rest.clone(), v),
    }
}

/// Translates a reply back through the `Map` frames an operation passed
/// (`back`, innermost first, so they're undone outermost first).
fn translate_back(
    g: &Globals,
    frames: &[Frame],
    back: &[(usize, Value)],
    mut v: Value,
) -> Result<Value> {
    for (j, src) in back.iter().rev() {
        match &frames[*j] {
            Frame::Map(_, reply) => v = apply(g, apply(g, reply.clone(), src.clone())?, v)?,
            _ => unreachable!("a translation recorded for a frame that isn't a `Map`"),
        }
    }
    Ok(v)
}
