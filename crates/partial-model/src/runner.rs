//! The runner (`stitchwort run`, the playground) and a fuel observer.
//!
//! The runner is the only code that performs operations: it steps a `Delay`,
//! hands each `Call` to the [`Host`], and resumes the segment with the reply.
//! It counts *semantic* ticks (`Later`s) separately from its *policies*
//! (work per step, total work, output, cancellation), which bound host
//! resources and never change what a program means.

use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;

use crate::delay::Delay;
use crate::machine::{self, Obs, Stop, Work};
use crate::reference::{self, Rules, Seg};
use crate::val::Val;

/// Operation tags of the model's host signature.
pub const PRINT: u32 = 0;
pub const READ_LINE: u32 = 1;
/// A foreign function: `#2((name, argument))`.
pub const FOREIGN: u32 = 2;

/// One thing the runner saw, in order.
#[derive(Clone, Debug, PartialEq)]
pub enum Event {
    /// An operation and the host's reply.
    Op(Val, Val),
    /// A `Later`: one recursive call.
    Tick,
}

pub enum HostReply {
    Reply(Val),
    /// The host call doesn't return (a foreign function that loops, or a read
    /// that blocks). Only the runner can be stuck here, never `step`.
    Blocked,
}

pub trait Perform {
    fn perform(&mut self, op: &Val) -> HostReply;
}

/// A foreign function's name and implementation.
pub type Foreign = (String, fn(Val) -> Val);

/// Scripted input, collected output, and foreign functions by name.
#[derive(Default)]
pub struct Script {
    pub input: VecDeque<String>,
    pub output: Vec<String>,
    /// Number of host calls performed, to show where operations run.
    pub performed: u64,
    /// Foreign functions; one not listed here never returns.
    pub foreign: Vec<Foreign>,
}

impl Script {
    pub fn with_input(lines: &[&str]) -> Script {
        Script {
            input: lines.iter().map(|l| l.to_string()).collect(),
            ..Script::default()
        }
    }
}

impl Perform for Script {
    fn perform(&mut self, op: &Val) -> HostReply {
        self.performed += 1;
        match op {
            Val::Tag(PRINT, t) => {
                self.output.push(t.as_text().to_string());
                HostReply::Reply(Val::Unit)
            }
            Val::Tag(READ_LINE, _) => HostReply::Reply(match self.input.pop_front() {
                Some(l) => Val::right(Val::text(&l)), // Just l
                None => Val::left(Val::Unit),         // Nothing
            }),
            Val::Tag(FOREIGN, call) => {
                let (name, arg) = call.as_pair();
                let name = name.as_text();
                match self.foreign.iter().find(|(n, _)| **n == *name) {
                    Some((_, f)) => HostReply::Reply(f(arg)),
                    None => HostReply::Blocked,
                }
            }
            other => panic!("unknown host operation {other:?}"),
        }
    }
}

/// Runner policies. None of them is part of the semantics.
#[derive(Clone)]
pub struct Policy {
    /// Stop when a run needs a tick beyond this many: `n` allows exactly `n` (an inconclusive test, not a failure).
    pub max_ticks: Option<u64>,
    /// Machine transitions allowed within one step (`E-RESOURCE`).
    pub max_work_per_step: u64,
    pub max_total_work: u64,
    pub max_output_bytes: usize,
    pub cancel: Option<Rc<Cell<bool>>>,
}

impl Default for Policy {
    fn default() -> Policy {
        Policy {
            max_ticks: None,
            max_work_per_step: 10_000_000,
            max_total_work: u64::MAX,
            max_output_bytes: 256 * 1024,
            cancel: None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    Finished(Val),
    OutOfTicks,
    OutOfWorkInStep,
    OutOfTotalWork,
    OutOfOutput,
    Cancelled,
    /// The host didn't return from this operation.
    Blocked(Val),
}

#[derive(Debug)]
pub struct Report {
    pub outcome: Outcome,
    pub ticks: u64,
    /// Calls to `step` (observations), including the one that saw `Now`.
    pub steps: u64,
    pub work: u64,
    pub peak_frames: usize,
    pub trace: Vec<Event>,
}

/// Run a `Delay` with the machine, performing its operations on `host`.
pub fn run(d: Delay, host: &mut dyn Perform, policy: &Policy) -> Report {
    let mut r = Report {
        outcome: Outcome::Cancelled,
        ticks: 0,
        steps: 0,
        work: 0,
        peak_frames: 0,
        trace: Vec::new(),
    };
    let mut output = 0usize;
    let mut d = d;
    r.outcome = 'outer: loop {
        let mut work = Work {
            used: 0,
            limit: policy.max_work_per_step,
            cancel: policy.cancel.clone(),
            peak_frames: 0,
        };
        r.steps += 1;
        let mut obs = machine::step(d, &mut work);
        loop {
            match obs {
                Err(stop) => {
                    r.work += work.used;
                    break 'outer match stop {
                        Stop::OutOfWork => Outcome::OutOfWorkInStep,
                        Stop::Cancelled => Outcome::Cancelled,
                    };
                }
                Ok(Obs::Call(op, pending)) => {
                    if let Val::Tag(PRINT, t) = &op {
                        output += t.as_text().len();
                        if output > policy.max_output_bytes {
                            break 'outer Outcome::OutOfOutput;
                        }
                    }
                    if policy.cancel.as_ref().is_some_and(|c| c.get()) {
                        break 'outer Outcome::Cancelled;
                    }
                    match host.perform(&op) {
                        HostReply::Blocked => break 'outer Outcome::Blocked(op),
                        HostReply::Reply(v) => {
                            r.trace.push(Event::Op(op, v.clone()));
                            obs = pending.reply(v, &mut work);
                        }
                    }
                }
                Ok(Obs::Now(v)) => {
                    r.work += work.used;
                    r.peak_frames = r.peak_frames.max(work.peak_frames);
                    break 'outer Outcome::Finished(v);
                }
                Ok(Obs::Later(rest)) => {
                    r.work += work.used;
                    r.peak_frames = r.peak_frames.max(work.peak_frames);
                    if policy.max_ticks.is_some_and(|max| r.ticks >= max) {
                        break 'outer Outcome::OutOfTicks;
                    }
                    r.ticks += 1;
                    r.trace.push(Event::Tick);
                    if r.work > policy.max_total_work {
                        break 'outer Outcome::OutOfTotalWork;
                    }
                    d = rest;
                    break;
                }
            }
        }
    };
    r
}

/// Run with the reference equations (not stack-safe; small inputs only).
pub fn run_reference(rules: Rules, d: Delay, host: &mut dyn Perform, max_ticks: u64) -> Report {
    let mut r = Report {
        outcome: Outcome::OutOfTicks,
        ticks: 0,
        steps: 0,
        work: 0,
        peak_frames: 0,
        trace: Vec::new(),
    };
    let mut d = d;
    r.outcome = 'outer: loop {
        r.steps += 1;
        let mut seg = reference::step(rules, &d);
        loop {
            match seg {
                Seg::Now(v) => break 'outer Outcome::Finished(v),
                Seg::Later(rest) => {
                    if r.ticks >= max_ticks {
                        break 'outer Outcome::OutOfTicks;
                    }
                    r.ticks += 1;
                    r.trace.push(Event::Tick);
                    d = rest;
                    break;
                }
                Seg::Call(op, k) => match host.perform(&op) {
                    HostReply::Blocked => break 'outer Outcome::Blocked(op),
                    HostReply::Reply(v) => {
                        r.trace.push(Event::Op(op, v.clone()));
                        seg = k(v);
                    }
                },
            }
        }
    };
    r
}

/// What a fuel-bounded observation returns.
#[derive(Clone, Debug, PartialEq)]
pub enum Fuel {
    /// `Done (Just v)` or `Done Nothing` (out of fuel).
    Done(Option<Val>),
    /// The computation asked for a host operation. A pure observer can't
    /// perform it: it's returned as data (the `Call` of the result `Comp`).
    Op(Val),
}

/// `runFor n d` with draft 3's convention: `n` is the number of `Later`s that
/// may be crossed; seeing `Now` costs nothing. So `runFor n d` succeeds iff
/// `d` finishes after at most `n` recursive calls. This is the stage-2
/// observer, modelled here only to measure counts; stage 1 doesn't have it.
pub fn run_for(fuel: u64, d: Delay) -> Fuel {
    let mut d = d;
    let mut left = fuel;
    loop {
        match machine::step(d, &mut Work::unlimited()) {
            Err(_) => unreachable!("unlimited work"),
            Ok(Obs::Now(v)) => return Fuel::Done(Some(v)),
            Ok(Obs::Call(op, _)) => return Fuel::Op(op),
            Ok(Obs::Later(rest)) => {
                if left == 0 {
                    return Fuel::Done(None);
                }
                left -= 1;
                d = rest;
            }
        }
    }
}

/// Counts for a computation without operations: `(laters, steps)`, where
/// `steps` counts every observation including the last one.
pub fn counts(rules: Rules, d: Delay) -> (u64, u64) {
    let r = run_reference(rules, d, &mut Script::default(), u64::MAX);
    assert!(matches!(r.outcome, Outcome::Finished(_)), "{:?}", r.outcome);
    (r.ticks, r.steps)
}
