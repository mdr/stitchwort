//! Running a program's `main` on the machine, performing its `IO`
//! operations for real: what `stitchwort run` does
//! (`stitchwort_driver::run`), with the same reading and writing
//! ([`crate::host`]) and the same errors.
//!
//! `main ()` is a partial computation, a `Delay` value. It's stepped as
//! `stitchwort_core::step` steps one (the stack-safe machine of
//! docs/proposals/partial.md §7.4, with the same frames and rules), on the
//! machine's values: the machine computes each function application the
//! stepping needs (a `bindD`'s continuation, a `pfix` body, a continuation
//! of an operation), and the stepping performs each `IO` operation that
//! reaches the bottom and feeds the reply back. Each stretch between two
//! operations or ticks has its own step budget, as for the reference
//! runner.
//!
//! Handlers around partial code (`foldD done call d`,
//! docs/proposals/partial-handlers.md §5.1) are the reference runner's
//! (`stitchwort_core::step`), on these frames: stepping one pushes a
//! `Handle` frame and steps `d` above it; `Now v` reaching it runs `done v`;
//! a tick passes it by. Every operation that reaches it is captured, the
//! ones the handler only forwards included: the frames above it, with their
//! marks, become the resumption `k` ([`Fun::DelayK`]), and `call op k` runs
//! below it. Stepping `k y` ([`Delay::Resumed`]) puts the handler and the
//! frames back on top of the stack, moving them if nothing else holds `k`,
//! and copying them otherwise (a handler that resumes more than once,
//! §5.2). The marks are stack positions, so capture rebases the ones above
//! the handler onto the captured frames and restore adds the new base back;
//! an `Await`'s own marks and translations are relative to its `Tie`, so
//! they mean the same at any depth.

use std::io::{BufRead, Write};
use std::rc::Rc;

use stitchwort_core::ResourceError;

use crate::host::{RunError, read_all, read_line};
use crate::ir::{MainRow, Program};
use crate::machine::{Limits, Machine};
use crate::value::{Delay, Fun, Value};

/// How a run ended, when nothing went wrong.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// `main` finished.
    Finished,
    /// The tick limit was reached: inconclusive.
    OutOfTicks,
}

/// What a run may do, beyond its resource limits.
#[derive(Clone, Copy, Debug, Default)]
pub struct Policy {
    /// Stop (inconclusively) when the run needs a tick beyond this many: a
    /// limit of `n` allows exactly `n` ticks.
    pub max_ticks: Option<u64>,
}

/// Runs `program` (lowered by [`crate::lower_main`]), reading lines from
/// `input` and printing to `output`, and flushes `output` at the end, as
/// `Session::run_main` does: the same reading contract, and output flushed
/// before every read. On an error, what was printed before it is flushed
/// too.
pub fn run_main(
    program: &Program,
    limits: Limits,
    input: &mut impl BufRead,
    output: &mut impl Write,
) -> Result<(), RunError> {
    match run_main_with(program, limits, &Policy::default(), input, output) {
        Ok(_) => output.flush().map_err(RunError::Write),
        Err(e) => {
            let _ = output.flush();
            Err(e)
        }
    }
}

/// Runs `program` as [`run_main`] does, within `policy`. Doesn't flush
/// `output`.
pub fn run_main_with(
    program: &Program,
    limits: Limits,
    policy: &Policy,
    input: &mut impl BufRead,
    output: &mut impl Write,
) -> Result<Outcome, RunError> {
    run_main_counting(program, limits, policy, input, output).0
}

/// How much work routing operations took in a run: for tests of the
/// invariant that routing never looks at ordinary frames one by one
/// (docs/proposals/effect-runtime.md §9.1.6).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RouteCounts {
    /// Operations that reached the runner: performed, or recursion requests.
    pub operations: u64,
    /// Frames routing looked at: only `Map` and `Tie` frames, each once per
    /// operation that crossed it or stopped at it.
    pub visited: u64,
    /// The frames below the focus at each operation, summed: what scanning
    /// them all, as routing did before stage 4c, would have looked at.
    pub below: u64,
    /// Operations a handler around partial code captured (`foldD`).
    pub captured: u64,
    /// Resumptions whose frames were copied rather than moved, because the
    /// resumption could still be called again
    /// (docs/proposals/partial-handlers.md §5.2): only a handler that
    /// resumes more than once copies.
    pub copies: u64,
}

/// Runs `program` as [`run_main_with`] does, and says how much work routing
/// took, however the run ended.
pub fn run_main_counting(
    program: &Program,
    limits: Limits,
    policy: &Policy,
    input: &mut impl BufRead,
    output: &mut impl Write,
) -> (Result<Outcome, RunError>, RouteCounts) {
    let mut machine = Machine::new(program, limits);
    let delay = match machine.entry() {
        Ok(delay) => delay,
        Err(e) => return (Err(e.into()), RouteCounts::default()),
    };
    let mut runner = Runner {
        m: machine,
        frames: Vec::new(),
        marks: Vec::new(),
        limits,
        lines: 0,
        ticks: 0,
        policy: *policy,
        counts: RouteCounts::default(),
    };
    let result = runner.run(delay, input, output);
    (result, runner.counts)
}

/// Steps `delay`, a partial computation that performs nothing (a test that
/// runs partial code, D1183), to its result on `machine`, as [`run_main`]
/// steps `main`: the same stepping, budget per stretch and lack of a tick
/// limit.
pub fn run_partial(machine: Machine<'_>, limits: Limits, delay: Value) -> Result<Value, RunError> {
    let mut runner = Runner {
        m: machine,
        frames: Vec::new(),
        marks: Vec::new(),
        limits,
        lines: 0,
        ticks: 0,
        policy: Policy::default(),
        counts: RouteCounts::default(),
    };
    let finished = runner.drive(delay, &mut std::io::empty(), &mut std::io::sink())?;
    Ok(finished.expect("no tick limit"))
}

/// What a `Call`'s rest does with the reply.
#[derive(Clone)]
pub(crate) enum Cont {
    /// `y => Done y`. Kept apart so a tail request can be recognised.
    Done,
    Fn(Value),
}

#[derive(Clone)]
pub(crate) enum Frame {
    Bind(Value),
    /// A `mapSig`'s mapping: `inject`, `reply`.
    Map(Value, Value),
    Tie(Value),
    /// A caller waiting for a recursive call's result (`step.rs`): the
    /// frames that were above the `Tie` (from the `Tie` up), their marks,
    /// and the translations the request passed, all relative to the `Tie`.
    Await {
        cont: Cont,
        upper: Vec<Frame>,
        marks: Vec<usize>,
        back: Vec<(usize, Value)>,
    },
    /// A handler around partial code, `foldD done call`: `Now v` reaching
    /// it runs `done v`, a tick passes it by, and an operation reaching it
    /// captures the frames above it as the resumption.
    Handle {
        done: Value,
        call: Value,
    },
}

/// What an operation reaching a `Handle` frame captured, the inside of a
/// resumption `k` ([`Fun::DelayK`]): the handler, the frames above it and
/// their marks (relative to the first of them), the operation's
/// continuation, and the `Map` frames it passed (indices into `frames`), so
/// the reply can be translated back.
#[derive(Clone)]
pub struct Capture {
    done: Value,
    call: Value,
    frames: Vec<Frame>,
    marks: Vec<usize>,
    cont: Cont,
    back: Vec<(usize, Value)>,
}

impl std::fmt::Debug for Capture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<resumption of {} frames>", self.frames.len())
    }
}

impl Capture {
    /// Moves the values it holds into `out`, so that dropping it frees
    /// nothing more than itself (`value.rs`: freeing never recurses).
    pub(crate) fn take_children(&mut self, out: &mut Vec<Value>) {
        out.push(std::mem::take(&mut self.done));
        out.push(std::mem::take(&mut self.call));
        if let Cont::Fn(rest) = &mut self.cont {
            out.push(std::mem::take(rest));
        }
        out.extend(self.back.drain(..).map(|(_, src)| src));
        let mut frames = std::mem::take(&mut self.frames);
        while let Some(frame) = frames.pop() {
            match frame {
                Frame::Bind(v) | Frame::Tie(v) => out.push(v),
                Frame::Map(inject, reply) => out.extend([inject, reply]),
                Frame::Handle { done, call } => out.extend([done, call]),
                Frame::Await {
                    cont, upper, back, ..
                } => {
                    if let Cont::Fn(rest) = cont {
                        out.push(rest);
                    }
                    out.extend(back.into_iter().map(|(_, src)| src));
                    frames.extend(upper);
                }
            }
        }
    }
}

enum Focus {
    Eval(Value),
    Enter(Value, Value),
    Comp(Value),
    Ret(Value),
}

struct Runner<'p> {
    m: Machine<'p>,
    frames: Vec<Frame>,
    /// Where the `Map`, `Tie` and `Handle` frames are in `frames`, bottom
    /// first: the
    /// only frames an operation has business with, so routing walks these
    /// and never the `Bind` and `Await` frames between them
    /// (docs/proposals/effect-runtime.md §9.1.6). A deep non-tail recursion
    /// leaves an `Await` per level, which routing used to look at for every
    /// operation.
    marks: Vec<usize>,
    limits: Limits,
    lines: usize,
    ticks: u64,
    policy: Policy,
    counts: RouteCounts,
}

impl Runner<'_> {
    /// Pushes `frame`, marking it if routing needs it.
    fn push(&mut self, frame: Frame) {
        if matches!(frame, Frame::Map(..) | Frame::Tie(_) | Frame::Handle { .. }) {
            self.marks.push(self.frames.len());
        }
        self.frames.push(frame);
    }

    /// One transition of the stepping: a step, within the frame limit.
    fn step(&mut self, steps: &mut u64) -> Result<(), ResourceError> {
        *steps += 1;
        if *steps > self.limits.steps {
            return Err(ResourceError::Work);
        }
        if self.frames.len() > self.limits.frames {
            return Err(ResourceError::Depth);
        }
        Ok(())
    }

    fn run(
        &mut self,
        delay: Value,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<Outcome, RunError> {
        match self.drive(delay, input, output)? {
            Some(_) => Ok(Outcome::Finished),
            None => Ok(Outcome::OutOfTicks),
        }
    }

    /// Steps `delay` to its result, or `None` at the tick limit.
    fn drive(
        &mut self,
        delay: Value,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<Option<Value>, RunError> {
        let s = *self.m.shapes();
        let mut focus = Focus::Eval(delay);
        let mut steps = 0;
        loop {
            self.step(&mut steps)?;
            focus = match focus {
                Focus::Eval(d) => {
                    let Value::Delay(d) = d else {
                        panic!("internal error: running {d:?}, which isn't a `Delay`")
                    };
                    if let Delay::Resumed(capture, reply) = &*d {
                        let (capture, reply) = (capture.clone(), reply.clone());
                        // Dropped first, so the capture is unshared if
                        // nothing else (the resumption itself) holds it.
                        drop(d);
                        focus = self.restore(capture, reply)?;
                        continue;
                    }
                    match &*d {
                        Delay::Now(v) => Focus::Ret(v.clone()),
                        Delay::Lift(c) => Focus::Comp(c.clone()),
                        Delay::Bind(d, k) => {
                            self.push(Frame::Bind(k.clone()));
                            Focus::Eval(d.clone())
                        }
                        Delay::Map(m, d) => {
                            let Value::Data(_, m) = m else {
                                panic!("internal error: a `SigMap` that isn't `MkSigMap`")
                            };
                            self.push(Frame::Map(m[0].clone(), m[1].clone()));
                            Focus::Eval(d.clone())
                        }
                        // Building `pfix f x` ran nothing; stepping it
                        // enters the body. No tick.
                        Delay::Pfix(f, x) => Focus::Enter(f.clone(), x.clone()),
                        // Entering a handler: its frame waits below the
                        // handled computation. No tick.
                        Delay::Fold(done, call, d) => {
                            self.push(Frame::Handle {
                                done: done.clone(),
                                call: call.clone(),
                            });
                            Focus::Eval(d.clone())
                        }
                        Delay::Resumed(..) => unreachable!("handled above"),
                    }
                }
                Focus::Enter(f, x) => {
                    self.push(Frame::Tie(f.clone()));
                    Focus::Eval(self.m.call(f, vec![x])?)
                }
                Focus::Comp(c) => match c {
                    // A `Bind` node of the effect runtime: run up to its
                    // first operation, with what it has pending kept in the
                    // operation's continuation, not in these frames, so
                    // routing never sees it (docs/proposals/effect-runtime.md
                    // §9.1.6).
                    Value::Data(t, _) if t == s.bind_node => Focus::Comp(self.m.step_comp(c)?),
                    Value::Data(t, fields) if t == s.done => Focus::Ret(fields[0].clone()),
                    Value::Data(t, fields) if t == s.call => {
                        let cont = match &fields[1] {
                            Value::Fun(f) if matches!(**f, Fun::DoneK) => Cont::Done,
                            rest => Cont::Fn(rest.clone()),
                        };
                        let op = fields[0].clone();
                        drop(fields);
                        match self.route(op, cont, input, output)? {
                            Routed::Handled(next) => next,
                            Routed::Performed(next) => {
                                // A new stretch.
                                steps = 0;
                                next
                            }
                            Routed::Tick(next) => {
                                // A limit of `n` allows exactly `n` ticks (docs/proposals/partial.md
                                // §7.4.3): stop on needing the next one.
                                if self.policy.max_ticks.is_some_and(|max| self.ticks >= max) {
                                    return Ok(None);
                                }
                                self.ticks += 1;
                                // A new stretch.
                                steps = 0;
                                self.m.reset_steps();
                                next
                            }
                        }
                    }
                    other => {
                        panic!("internal error: `lift` of {other:?}, which isn't a computation")
                    }
                },
                Focus::Ret(v) => match self.frames.pop() {
                    None => return Ok(Some(v)),
                    Some(Frame::Bind(k)) => Focus::Eval(self.m.call(k, vec![v])?),
                    Some(Frame::Handle { done, .. }) => {
                        self.marks.pop();
                        Focus::Eval(self.m.call(done, vec![v])?)
                    }
                    Some(Frame::Map(..) | Frame::Tie(_)) => {
                        self.marks.pop();
                        Focus::Ret(v)
                    }
                    Some(Frame::Await {
                        cont,
                        upper,
                        marks,
                        back,
                    }) => {
                        let v = self.translate_back(&upper, &back, v)?;
                        let base = self.frames.len();
                        self.frames.extend(upper);
                        self.marks.extend(marks.into_iter().map(|j| j + base));
                        Focus::Comp(self.apply_cont(&cont, v)?)
                    }
                },
            };
        }
    }

    fn apply_cont(&mut self, cont: &Cont, v: Value) -> Result<Value, ResourceError> {
        match cont {
            Cont::Done => Ok(Value::data(self.m.shapes().done, [v])),
            Cont::Fn(rest) => self.m.call(rest.clone(), vec![v]),
        }
    }

    /// Translates a reply back through the `Map` frames an operation passed
    /// (`back`, innermost first, so they're undone outermost first).
    fn translate_back(
        &mut self,
        frames: &[Frame],
        back: &[(usize, Value)],
        mut v: Value,
    ) -> Result<Value, ResourceError> {
        for (j, src) in back.iter().rev() {
            match &frames[*j] {
                Frame::Map(_, reply) => v = self.m.call(reply.clone(), vec![src.clone(), v])?,
                _ => unreachable!("a translation recorded for a frame that isn't a `Map`"),
            }
        }
        Ok(v)
    }

    /// Operation `op` leaves the focus, outwards through the frames: a
    /// `Tie` answers a recursion request (one tick); one that reaches the
    /// bottom is performed, and the reply goes back. Only the marked frames
    /// are looked at, so the work is the number of `Map`s and `Tie`s
    /// crossed, however many other frames there are.
    fn route(
        &mut self,
        mut op: Value,
        cont: Cont,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<Routed, RunError> {
        let s = *self.m.shapes();
        self.counts.operations += 1;
        self.counts.below += self.frames.len() as u64;
        let mut back: Vec<(usize, Value)> = Vec::new();
        let mut p = self.marks.len();
        while p > 0 {
            p -= 1;
            let j = self.marks[p];
            self.counts.visited += 1;
            match &self.frames[j] {
                Frame::Bind(_) | Frame::Await { .. } => {
                    unreachable!("a mark on a frame that isn't a `Map`, a `Tie` or a `Handle`")
                }
                Frame::Handle { .. } => {
                    return Ok(Routed::Handled(self.capture(p, op, cont, back)?));
                }
                Frame::Map(inject, _) => {
                    let inject = inject.clone();
                    let target = self.m.call(inject, vec![op.clone()])?;
                    back.push((j, std::mem::replace(&mut op, target)));
                }
                Frame::Tie(f) => {
                    let (side, inner) = match &op {
                        Value::Data(t, fields) => (*t, fields[0].clone()),
                        other => panic!("internal error: an operation {other:?} reached a `pfix`"),
                    };
                    if side == s.right {
                        op = inner;
                        continue;
                    }
                    debug_assert_eq!(side, s.left);
                    let request = match &inner {
                        Value::Data(t, fields) if *t == s.recur => fields[0].clone(),
                        other => panic!("internal error: a recursion request {other:?}"),
                    };
                    let f = f.clone();
                    let upper = self.frames.split_off(j);
                    let marks = self.marks.split_off(p);
                    debug_assert!(
                        !upper.iter().any(|f| matches!(f, Frame::Handle { .. })),
                        "a recursion request passed a handler"
                    );
                    let tail = upper.len() == 1 && matches!(cont, Cont::Done) && back.is_empty();
                    if !tail {
                        let marks = marks.into_iter().map(|k| k - j).collect();
                        let back = back.into_iter().map(|(k, src)| (k - j, src)).collect();
                        self.push(Frame::Await {
                            cont,
                            upper,
                            marks,
                            back,
                        });
                    }
                    return Ok(Routed::Tick(Focus::Enter(f, request)));
                }
            }
        }
        // For the host.
        let reply = self.perform(op, input, output)?;
        self.m.reset_steps();
        let frames = std::mem::take(&mut self.frames);
        let reply = self.translate_back(&frames, &back, reply);
        self.frames = frames;
        Ok(Routed::Performed(Focus::Comp(
            self.apply_cont(&cont, reply?)?,
        )))
    }

    /// `op` reached the `Handle` frame marked at `p`: the frames above it
    /// become the resumption `k`, and the stepping goes on with `call op k`,
    /// below the handler.
    ///
    /// The frames need no adjusting: an `Await`'s marks and translations are
    /// relative to its own `Tie`, and a `Tie` holds no position. What indexes
    /// the stack is rebased onto the captured frames: their marks, and
    /// `back`, the `Map` frames `op` passed.
    fn capture(
        &mut self,
        p: usize,
        op: Value,
        cont: Cont,
        back: Vec<(usize, Value)>,
    ) -> Result<Focus, RunError> {
        self.counts.captured += 1;
        let base = self.marks[p] + 1;
        let frames = self.frames.split_off(base);
        let marks = self
            .marks
            .split_off(p + 1)
            .into_iter()
            .map(|j| j - base)
            .collect();
        self.marks.pop();
        let Some(Frame::Handle { done, call }) = self.frames.pop() else {
            unreachable!("a capture at a frame that isn't a `Handle`")
        };
        let back = back.into_iter().map(|(j, src)| (j - base, src)).collect();
        let capture = Capture {
            done,
            call: call.clone(),
            frames,
            marks,
            cont,
            back,
        };
        let k = Value::Fun(Rc::new(Fun::DelayK(Rc::new(capture))));
        Ok(Focus::Eval(self.m.call(call, vec![op, k])?))
    }

    /// Stepping `k y`: the handler and the captured frames go back on top
    /// of the stack, and the handled computation goes on with `y`. The
    /// frames are moved if nothing else holds the resumption, and copied if
    /// something does: it may be resumed again
    /// (docs/proposals/partial-handlers.md §5.2).
    fn restore(&mut self, capture: Rc<Capture>, reply: Value) -> Result<Focus, RunError> {
        let capture = Rc::try_unwrap(capture).unwrap_or_else(|shared| {
            self.counts.copies += 1;
            (*shared).clone()
        });
        let Capture {
            done,
            call,
            frames,
            marks,
            cont,
            back,
        } = capture;
        let reply = self.translate_back(&frames, &back, reply)?;
        self.push(Frame::Handle { done, call });
        let base = self.frames.len();
        self.frames.extend(frames);
        self.marks.extend(marks.into_iter().map(|j| j + base));
        Ok(Focus::Comp(self.apply_cont(&cont, reply)?))
    }

    /// Performs operation `op`, of `{IO}` or `{Fail, IO}` (the program's
    /// [`MainRow`]): its reply. `Fail.stop msg` stops the run with
    /// [`RunError::Failed`]; it returns `Empty`, so there's nothing to resume
    /// with (docs/proposals/partial-stage-2.md).
    fn perform(
        &mut self,
        op: Value,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<Value, RunError> {
        let s = *self.m.shapes();
        let side = |v: &Value| match v {
            Value::Data(t, fields) if *t == s.left || *t == s.right => (*t, fields[0].clone()),
            other => panic!("internal error: an operation {other:?} outside `IO` and `Fail`"),
        };
        let io = match (self.m.program().main_row, side(&op)) {
            (MainRow::Io, (t, io)) if t == s.left => io,
            (MainRow::FailIo, (t, stop)) if t == s.left => {
                let Value::Data(tag, fields) = &stop else {
                    panic!("internal error: a `Fail` operation {stop:?}")
                };
                debug_assert_eq!(*tag, s.stop);
                return Err(RunError::Failed(
                    crate::prims::text_of(&fields[0]).to_string(),
                ));
            }
            (MainRow::FailIo, (_, rest)) => match side(&rest) {
                (t, io) if t == s.left => io,
                _ => panic!("internal error: an operation {op:?} outside `IO` and `Fail`"),
            },
            _ => panic!("internal error: an operation {op:?} outside `IO`"),
        };
        let tag = io.tag().expect("an `IO` operation");
        Ok(if tag == s.print {
            let Value::Data(_, fields) = &io else {
                unreachable!("`print` has a field")
            };
            let text = crate::prims::text_of(&fields[0]);
            output
                .write_all(text.as_bytes())
                .and_then(|()| output.write_all(b"\n"))
                .map_err(RunError::Write)?;
            Value::Tag(s.unit)
        } else if tag == s.read_line {
            output.flush().map_err(RunError::Write)?;
            match read_line(input, &mut self.lines)? {
                Some(line) => Value::data(s.some, [Value::Text(line.into())]),
                None => Value::Tag(s.none),
            }
        } else if tag == s.read_all {
            output.flush().map_err(RunError::Write)?;
            Value::Text(read_all(input, &mut self.lines)?.into())
        } else if tag == s.random_seed {
            Value::Nat(crate::host::random_seed())
        } else {
            panic!("internal error: an unknown `IO` operation {io:?}")
        })
    }
}

/// Where an operation went.
enum Routed {
    /// It was performed: go on with this.
    Performed(Focus),
    /// It was a recursion request: one tick, then this.
    Tick(Focus),
    /// A handler around partial code took it: its clause, then this.
    Handled(Focus),
}
