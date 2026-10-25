//! A stack-safe implementation of `step`: an abstract machine with an explicit
//! frame stack on the heap, in the style of ITrees' `interp_mrec` (a
//! recursion request extends the pending computation with the requested body
//! and the caller's continuation).
//!
//! It implements draft 3's equations ([`crate::reference`]): entering
//! `pfix f x` runs `f x` without a tick, and each recursion request produces
//! exactly one `Later` *before* the callee's body runs. The `Later`'s rest is
//! an explicit suspended machine state, so building it runs nothing.
//!
//! `step` never performs an operation: a `Call` that no `Tie` frame answers is
//! returned to the caller as [`Obs::Call`], with a [`Pending`] state that the
//! caller resumes with the reply. The machine has no access to a host.
//!
//! Handlers (`foldD`, `docs/proposals/partial-handlers.md` §5.1): stepping
//! `foldD done call d` pushes a `Handle` frame and steps `d` above it. `Now v`
//! reaching it runs `done v`; a `Later` suspends the whole machine, handler
//! included, so it passes the handler by as one tick. *Every* operation that
//! reaches a `Handle` frame is captured (the handler's `call` forwards what it
//! doesn't handle), so operations never pass one: a `Tie` below a handler
//! only sees a request after the handler has re-issued it, and an `Await`'s
//! `upper` never contains a `Handle` frame. Capture moves the frames above the
//! handler into the resumption; restoring moves them back, or copies them if
//! the resumption may be called again (multi-shot).

use std::cell::Cell;
use std::rc::Rc;

use crate::delay::{Comp, Cont, Delay, Handler, Kont, Node, SigMap};
use crate::val::Val;

#[derive(Clone)]
enum Frame {
    /// The continuation of a `bindD`.
    Bind(Kont),
    /// A `mapSig`: operations leaving it are translated.
    Map(SigMap),
    /// A `tie f`: answers `L (Recur y)` requests with `pfix f y`.
    Tie(Kont),
    /// A caller waiting for a recursive call's result: when the callee
    /// returns `v`, translate `v` back through `upper`'s `Map` frames, put
    /// `upper` back (it starts with the caller's `Tie`), and continue with
    /// `cont v`. Operations from the callee pass through it unchanged.
    ///
    /// Its `back` indexes `upper`, not the stack, so the frame means the same
    /// wherever it sits: a `Handle` frame can capture it and put it back at
    /// another depth (partial-handlers.md §5.1).
    Await {
        cont: Cont,
        upper: Vec<Frame>,
        back: Vec<(usize, Val)>,
    },
    /// A `foldD done call`: `Now v` reaching it runs `done v`, a `Later`
    /// passes it by (the whole machine suspends), and an operation reaching it
    /// captures the frames above it as the resumption.
    Handle { done: Kont, call: Handler },
}

/// What an operation reaching a `Handle` frame captured: the frames above the
/// handler, the operation's continuation, and the `Map` frames it passed
/// (indices into `frames`), so the reply can be translated back. Applying
/// the resumption to `y` puts the handler and these frames back on top of the
/// stack, wherever it is then, and continues with `cont` on `y` translated.
#[derive(Clone)]
pub(crate) struct Capture {
    done: Kont,
    call: Handler,
    frames: Vec<Frame>,
    cont: Cont,
    back: Vec<(usize, Val)>,
}

#[derive(Clone)]
enum Focus {
    Eval(Delay),
    Comp(Comp),
    Ret(Val),
    Hole,
}

/// A machine state: what to do next, and the pending frames.
#[derive(Clone)]
pub struct Machine {
    focus: Focus,
    frames: Vec<Frame>,
}

/// Execution budget for one call into the machine (a runner policy, not
/// semantics).
pub struct Work {
    pub used: u64,
    pub limit: u64,
    pub cancel: Option<Rc<Cell<bool>>>,
    /// The deepest the frame stack got: frames live on the heap, so this is
    /// memory, not host stack.
    pub peak_frames: usize,
    /// How many times a resumption's captured frames were copied, because
    /// the resumption could still be called again (multi-shot handlers).
    pub copies: u64,
}

impl Work {
    pub fn unlimited() -> Work {
        Work {
            used: 0,
            limit: u64::MAX,
            cancel: None,
            peak_frames: 0,
            copies: 0,
        }
    }

    pub fn limited(limit: u64) -> Work {
        Work {
            limit,
            ..Work::unlimited()
        }
    }
}

/// Why the machine stopped before reaching an observation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stop {
    OutOfWork,
    Cancelled,
}

/// What one `step` observes, as the runner sees it. A segment is the sequence
/// of `Call`s ending in `Now` or `Later`.
pub enum Obs {
    Now(Val),
    /// One tick: a recursive call was requested; the rest is suspended.
    Later(Delay),
    /// An operation for the host. Nothing has been performed.
    Call(Val, Pending),
}

/// Where an operation went.
enum Routed {
    /// Out of this `step`: a tick, or an operation for the host.
    Obs(Obs),
    /// A handler took it; the machine continues with the handler's clause.
    Handled(Machine),
}

/// The rest of a segment, waiting for an operation's reply.
pub struct Pending {
    machine: Machine,
    cont: Cont,
    back: Vec<(usize, Val)>,
}

impl Pending {
    /// Continue the segment with the host's reply to the operation.
    pub fn reply(self, v: Val, work: &mut Work) -> Result<Obs, Stop> {
        let mut m = self.machine;
        let v = translate_back(&m.frames, &self.back, v);
        m.focus = Focus::Comp(self.cont.apply(v));
        m.run(work)
    }
}

/// `step d`: run until the next `Now`, `Later` or host operation.
pub fn step(d: Delay, work: &mut Work) -> Result<Obs, Stop> {
    Machine {
        focus: Focus::Eval(d),
        frames: Vec::new(),
    }
    .run(work)
}

/// Translate a reply back through the `Map` frames an operation passed
/// (outermost first).
fn translate_back(frames: &[Frame], back: &[(usize, Val)], mut v: Val) -> Val {
    for (j, src) in back.iter().rev() {
        match &frames[*j] {
            Frame::Map(m) => v = (m.res)(src, v),
            _ => unreachable!("translation recorded for a frame that isn't a Map"),
        }
    }
    v
}

/// Take a node out of a `Delay`, without cloning a suspended machine when the
/// `Delay` isn't shared.
enum Taken {
    Node(Delay),
    Machine(Machine),
}

fn take(d: Delay) -> Taken {
    if !matches!(&*d.0, Node::Suspended(_)) {
        return Taken::Node(d);
    }
    match Rc::try_unwrap(d.0) {
        Ok(mut node) => match &mut node {
            Node::Suspended(m) => Taken::Machine(std::mem::replace(
                &mut **m,
                Machine {
                    focus: Focus::Hole,
                    frames: Vec::new(),
                },
            )),
            _ => Taken::Node(Delay(Rc::new(node))),
        },
        Err(rc) => match &*rc {
            Node::Suspended(m) => Taken::Machine((**m).clone()),
            _ => Taken::Node(Delay(rc)),
        },
    }
}

impl Machine {
    fn run(mut self, work: &mut Work) -> Result<Obs, Stop> {
        loop {
            work.used += 1;
            if work.used > work.limit {
                return Err(Stop::OutOfWork);
            }
            if work.used.is_multiple_of(1024)
                && let Some(c) = &work.cancel
                && c.get()
            {
                return Err(Stop::Cancelled);
            }
            work.peak_frames = work.peak_frames.max(self.frames.len());
            match std::mem::replace(&mut self.focus, Focus::Hole) {
                Focus::Hole => unreachable!("the machine ran with no focus"),
                Focus::Eval(d) if matches!(&*d.0, Node::Restore(..)) => {
                    let Node::Restore(capture, reply) = &*d.0 else {
                        unreachable!()
                    };
                    let (capture, reply) = (capture.clone(), reply.clone());
                    // Drop the node first, so the capture is unshared if
                    // nothing else (the resumption itself) holds it.
                    drop(d);
                    self.restore(capture, reply, work);
                }
                Focus::Eval(d) => match take(d) {
                    Taken::Machine(m) => {
                        // Resuming at the top level (the runner) is O(1).
                        if self.frames.is_empty() {
                            self.frames = m.frames;
                        } else {
                            self.frames.extend(m.frames);
                        }
                        self.focus = m.focus;
                    }
                    Taken::Node(d) => match &*d.0 {
                        Node::Now(v) => self.focus = Focus::Ret(v.clone()),
                        Node::Lift(c) => self.focus = Focus::Comp(c.clone()),
                        Node::Bind(inner, k) => {
                            self.frames.push(Frame::Bind(k.clone()));
                            self.focus = Focus::Eval(inner.clone());
                        }
                        Node::MapSig(m, inner) => {
                            self.frames.push(Frame::Map(m.clone()));
                            self.focus = Focus::Eval(inner.clone());
                        }
                        // Entering a `pfix`: the body runs now, in this step,
                        // under a `Tie` that answers its requests. No tick.
                        Node::Pfix(f, x) => {
                            self.frames.push(Frame::Tie(f.clone()));
                            self.focus = Focus::Eval(f(x.clone()));
                        }
                        Node::Tie(f, inner) => {
                            self.frames.push(Frame::Tie(f.clone()));
                            self.focus = Focus::Eval(inner.clone());
                        }
                        // Entering a handler: its frame waits below the
                        // handled computation. No tick.
                        Node::FoldD(done, call, inner) => {
                            self.frames.push(Frame::Handle {
                                done: done.clone(),
                                call: call.clone(),
                            });
                            self.focus = Focus::Eval(inner.clone());
                        }
                        Node::Resume(_) => panic!("a reference-stepper state given to the machine"),
                        Node::Suspended(_) => unreachable!("handled by take"),
                        Node::Restore(..) => unreachable!("handled above"),
                    },
                },
                Focus::Comp(Comp::Done(v)) => self.focus = Focus::Ret(v),
                Focus::Comp(Comp::Call(op, cont)) => match self.route(op, cont) {
                    Routed::Obs(obs) => return Ok(obs),
                    Routed::Handled(m) => self = m,
                },
                Focus::Ret(v) => match self.frames.pop() {
                    None => return Ok(Obs::Now(v)),
                    Some(Frame::Bind(k)) => self.focus = Focus::Eval(k(v)),
                    Some(Frame::Handle { done, .. }) => self.focus = Focus::Eval(done(v)),
                    Some(Frame::Map(_)) | Some(Frame::Tie(_)) => self.focus = Focus::Ret(v),
                    Some(Frame::Await { cont, upper, back }) => {
                        let v = translate_back(&upper, &back, v);
                        self.frames.extend(upper);
                        self.focus = Focus::Comp(cont.apply(v));
                    }
                },
            }
        }
    }

    /// An operation leaves the focus: pass it outwards through the frames.
    /// Either a `Handle` captures it (no tick), a `Tie` answers it as a
    /// recursion request (one tick), or it reaches the bottom and is returned
    /// to the host, unperformed.
    fn route(self, mut op: Val, cont: Cont) -> Routed {
        let mut back: Vec<(usize, Val)> = Vec::new();
        let mut j = self.frames.len();
        while j > 0 {
            j -= 1;
            match &self.frames[j] {
                Frame::Bind(_) | Frame::Await { .. } => {}
                Frame::Handle { .. } => return Routed::Handled(self.capture(j, op, cont, back)),
                Frame::Map(m) => {
                    let target = (m.op)(&op);
                    back.push((j, std::mem::replace(&mut op, target)));
                }
                Frame::Tie(f) => match op {
                    Val::R(o) => op = (*o).clone(),
                    Val::L(y) => {
                        let f = f.clone();
                        return Routed::Obs(self.request(j, f, (*y).clone(), cont, back));
                    }
                    other => panic!("an operation outside `Plus` reached a tie: {other:?}"),
                },
            }
        }
        Routed::Obs(Obs::Call(
            op,
            Pending {
                machine: self,
                cont,
                back,
            },
        ))
    }

    /// `op` reached the `Handle` frame at `h`: take the frames above it as the
    /// resumption `k` and continue with `call op k`, below the handler.
    ///
    /// The frames taken may include `Tie` and `Await` frames (the handled
    /// program was inside a recursive call). They need no adjusting: an
    /// `Await`'s indices are into its own `upper`, and a `Tie` holds no
    /// position. Only `back`, the `Map` frames `op` passed, indexes the
    /// stack, so it's rebased onto the captured slice.
    fn capture(mut self, h: usize, op: Val, cont: Cont, back: Vec<(usize, Val)>) -> Machine {
        let frames = self.frames.split_off(h + 1);
        let Some(Frame::Handle { done, call }) = self.frames.pop() else {
            unreachable!("capture at a frame that isn't a Handle")
        };
        let back = back
            .into_iter()
            .map(|(j, src)| (j - (h + 1), src))
            .collect();
        let capture = Rc::new(Capture {
            done,
            call: call.clone(),
            frames,
            cont,
            back,
        });
        let k: Kont = Rc::new(move |y| Delay::restore(capture.clone(), y));
        self.focus = Focus::Eval(call(op, k));
        self
    }

    /// `k y`: put the handler and the captured frames back on top of the
    /// stack and continue the handled program with `y`. If the resumption
    /// may still be called again, the frames are copied (§5.2); otherwise
    /// they're moved.
    fn restore(&mut self, capture: Rc<Capture>, reply: Val, work: &mut Work) {
        let capture = Rc::try_unwrap(capture).unwrap_or_else(|shared| {
            work.copies += 1;
            (*shared).clone()
        });
        let reply = translate_back(&capture.frames, &capture.back, reply);
        self.frames.push(Frame::Handle {
            done: capture.done,
            call: capture.call,
        });
        self.frames.extend(capture.frames);
        self.focus = Focus::Comp(capture.cont.apply(reply));
    }

    /// `Recur y` reached the `Tie` at `i`:
    /// `Later (bindD (pfix f y) (\v -> tie f (resume (cont v))))`.
    fn request(mut self, i: usize, f: Kont, y: Val, cont: Cont, back: Vec<(usize, Val)>) -> Obs {
        let upper = self.frames.split_off(i);
        debug_assert!(
            !upper.iter().any(|f| matches!(f, Frame::Handle { .. })),
            "a request passed a handler"
        );
        let tail = upper.len() == 1 && cont.is_done() && back.is_empty();
        if !tail {
            let back = back.into_iter().map(|(j, src)| (j - i, src)).collect();
            self.frames.push(Frame::Await { cont, upper, back });
        }
        // A tail call needs no frame: the caller's `tie f` would only pass the
        // result on, and `pfix f y` installs its own.
        self.focus = Focus::Eval(Delay::pfix(f, y));
        Obs::Later(Delay::suspended(self))
    }
}
