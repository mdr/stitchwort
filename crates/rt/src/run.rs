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

use std::io::{BufRead, Write};

use stitchwort_core::ResourceError;

use crate::host::{RunError, read_all, read_line};
use crate::ir::Program;
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
    /// Stop (inconclusively) once this many ticks have happened. For tests.
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
    let mut machine = Machine::new(program, limits);
    let delay = machine.entry()?;
    let mut runner = Runner {
        m: machine,
        frames: Vec::new(),
        limits,
        lines: 0,
        ticks: 0,
        policy: *policy,
    };
    runner.run(delay, input, output)
}

/// What a `Call`'s rest does with the reply.
enum Cont {
    /// `y => Done y`. Kept apart so a tail request can be recognised.
    Done,
    Fn(Value),
}

enum Frame {
    Bind(Value),
    /// A `mapSig`'s mapping: `inject`, `reply`.
    Map(Value, Value),
    Tie(Value),
    /// A caller waiting for a recursive call's result (`step.rs`).
    Await {
        cont: Cont,
        upper: Vec<Frame>,
        back: Vec<(usize, Value)>,
    },
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
    limits: Limits,
    lines: usize,
    ticks: u64,
    policy: Policy,
}

impl Runner<'_> {
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
                    match &*d {
                        Delay::Now(v) => Focus::Ret(v.clone()),
                        Delay::Lift(c) => Focus::Comp(c.clone()),
                        Delay::Bind(d, k) => {
                            self.frames.push(Frame::Bind(k.clone()));
                            Focus::Eval(d.clone())
                        }
                        Delay::Map(m, d) => {
                            let Value::Data(_, m) = m else {
                                panic!("internal error: a `SigMap` that isn't `MkSigMap`")
                            };
                            self.frames.push(Frame::Map(m[0].clone(), m[1].clone()));
                            Focus::Eval(d.clone())
                        }
                        // Building `pfix f x` ran nothing; stepping it
                        // enters the body. No tick.
                        Delay::Pfix(f, x) => Focus::Enter(f.clone(), x.clone()),
                    }
                }
                Focus::Enter(f, x) => {
                    self.frames.push(Frame::Tie(f.clone()));
                    Focus::Eval(self.m.call(f, vec![x])?)
                }
                Focus::Comp(c) => match c {
                    Value::Data(t, fields) if t == s.done => Focus::Ret(fields[0].clone()),
                    Value::Data(t, fields) if t == s.call => {
                        let cont = match &fields[1] {
                            Value::Fun(f) if matches!(**f, Fun::DoneK) => Cont::Done,
                            rest => Cont::Fn(rest.clone()),
                        };
                        let op = fields[0].clone();
                        drop(fields);
                        match self.route(op, cont, input, output)? {
                            Routed::Performed(next) => {
                                // A new stretch.
                                steps = 0;
                                next
                            }
                            Routed::Tick(next) => {
                                self.ticks += 1;
                                if self.policy.max_ticks.is_some_and(|max| self.ticks >= max) {
                                    return Ok(Outcome::OutOfTicks);
                                }
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
                    None => return Ok(Outcome::Finished),
                    Some(Frame::Bind(k)) => Focus::Eval(self.m.call(k, vec![v])?),
                    Some(Frame::Map(..) | Frame::Tie(_)) => Focus::Ret(v),
                    Some(Frame::Await { cont, upper, back }) => {
                        let v = self.translate_back(&upper, &back, v)?;
                        self.frames.extend(upper);
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
    /// bottom is performed, and the reply goes back.
    fn route(
        &mut self,
        mut op: Value,
        cont: Cont,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<Routed, RunError> {
        let s = *self.m.shapes();
        let mut back: Vec<(usize, Value)> = Vec::new();
        let mut j = self.frames.len();
        while j > 0 {
            j -= 1;
            match &self.frames[j] {
                Frame::Bind(_) | Frame::Await { .. } => {}
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
                    let tail = upper.len() == 1 && matches!(cont, Cont::Done) && back.is_empty();
                    if !tail {
                        let back = back.into_iter().map(|(k, src)| (k - j, src)).collect();
                        self.frames.push(Frame::Await { cont, upper, back });
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

    /// Performs operation `op` of `{IO}`, which is `Plus IO NoOp`: its
    /// reply.
    fn perform(
        &mut self,
        op: Value,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<Value, RunError> {
        let s = *self.m.shapes();
        let io = match &op {
            Value::Data(t, fields) if *t == s.left => fields[0].clone(),
            other => panic!("internal error: an operation {other:?} outside `IO`"),
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
}
