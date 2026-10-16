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
//!   continuation and its own frames.
//!
//! The rules (the equations of §7.4.2, which the model transcribes as its
//! reference): entering `pfix f x` runs the body `f x` under `Tie f`, with no
//! tick; a request reaching a `Tie` is exactly one `Later`, whose rest enters
//! the callee and then returns to the caller; other operations pass through
//! a `Tie` with their reply unchanged. A request in tail position (nothing
//! pending above the caller's `Tie`, and the continuation `\y -> Done y`)
//! keeps no frame, so a loop runs in constant space.
//!
//! Each transition is a step of the operation's budget, and the frame stack
//! is bounded by its frame limit. Trusted for "runs what was written", not
//! for consistency: a bug here could run a program wrongly, but never make
//! the checker accept something false, since nothing computed here is given
//! back to it.

use crate::budget::Result;
use crate::globals::Globals;
use crate::partial::Primitive;
use crate::term::{DataId, DefId, Term};
use crate::value::{Elim, Head, Value, apply, force};

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
}

impl Shapes {
    fn new(g: &Globals) -> Shapes {
        let data = |name: &str| g.find_data(name).expect("the prelude declares it");
        let prim = |p: Primitive| {
            g.builtins
                .primitive_id(p)
                .expect("the prelude declares the partial constants")
        };
        Shapes {
            comp: data("Comp"),
            plus: data("Plus"),
            rec: data("Rec"),
            now: prim(Primitive::Now),
            lift: prim(Primitive::Lift),
            bind: prim(Primitive::BindD),
            map_sig: prim(Primitive::MapSig),
            pfix: prim(Primitive::Pfix),
        }
    }
}

/// What a `Call`'s rest does with the reply.
enum Cont {
    /// `\y -> Done y`. Kept apart so a tail request can be recognised.
    Done,
    Fn(Value),
}

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
                    let (prim, args) = constant(g, &s, d)?;
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
                        return self.route(g, fields[0].clone(), cont);
                    }
                    _ => panic!("internal error: `lift` of something that isn't a computation"),
                },
                Focus::Ret(v) => match self.frames.pop() {
                    None => return Ok(Obs::Now(v)),
                    Some(Frame::Bind(k)) => Focus::Eval(apply(g, k, v)?),
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
    /// frames. A `Tie` answers a recursion request (one tick); one that
    /// reaches the bottom is returned to the host, unperformed.
    fn route(mut self, g: &Globals, mut op: Value, cont: Cont) -> Result<Obs> {
        let s = self.shapes;
        let mut back: Vec<(usize, Value)> = Vec::new();
        let mut j = self.frames.len();
        while j > 0 {
            j -= 1;
            match &self.frames[j] {
                Frame::Bind(_) | Frame::Await { .. } => {}
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
                    let tail = upper.len() == 1 && matches!(cont, Cont::Done) && back.is_empty();
                    if !tail {
                        let back = back.into_iter().map(|(k, src)| (k - j, src)).collect();
                        self.frames.push(Frame::Await { cont, upper, back });
                    }
                    // A tail call keeps no frame: the caller's `Tie` would
                    // only pass the result on, and the callee installs its
                    // own.
                    self.focus = Focus::Enter(f, request[0].clone());
                    return Ok(Obs::Later(self));
                }
            }
        }
        Ok(Obs::Call(
            op,
            Pending {
                machine: self,
                cont,
                back,
            },
        ))
    }
}

/// A `Delay` value: the constant it's built by, and its arguments.
fn constant(g: &Globals, s: &Shapes, d: Value) -> Result<(Primitive, Vec<Value>)> {
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
    .find_map(|(c, p)| (c == id).then_some(p));
    let args: Vec<Value> = spine
        .into_iter()
        .map(|e| match e {
            Elim::App(v, _) => v,
            Elim::J { .. } => panic!("internal error: a `Delay` stuck on `J`"),
        })
        .collect();
    match prim {
        Some(p) if args.len() == p.arity() => Ok((p, args)),
        _ => panic!("internal error: running something that isn't a `Delay`"),
    }
}

/// The continuation of a `Call`.
fn cont(s: &Shapes, rest: &Value) -> Cont {
    // `\y -> Done y`, as the elaborator writes a request or an operation.
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
