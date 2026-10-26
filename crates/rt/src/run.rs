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
//!
//! A run can also stop when it asks for input that isn't there yet, and go
//! on when it is ([`LiveRun`], docs/proposals/playground-live-keys.md):
//! since nothing of the program's is on the Rust stack, stopping is
//! returning from the stepping loop with the waiting operation kept.

mod live;

use std::io::{self, BufRead, Read, Write};
use std::rc::Rc;

use stitchwort_core::ResourceError;

use crate::host::{NoTerminal, RunError, Terminal, read_all, read_bytes, read_line, write_text};
use crate::ir::{MainRow, Program, Shapes};
use crate::machine::Machine;
use crate::native_abi::{NativeExecutor, NativeIslands};
use crate::shared::Limits;
use crate::value::{Delay, Fun, Value};

pub use live::{Advanced, LimitScope, LiveLimits, LiveRun};

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
    run_main_on(program, limits, input, output, &mut NoTerminal)
}

/// [`run_main`] with `terminal` for `IO.console` and `IO.keysMode`
/// (docs/proposals/terminal-io.md §4.6): what `stitchwort run` passes on a
/// Unix terminal. Keys mode is left on if the run ends without leaving it;
/// putting the terminal back is the caller's job.
pub fn run_main_on(
    program: &Program,
    limits: Limits,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> Result<(), RunError> {
    let result = run_inner(program, limits, &Policy::default(), input, output, terminal).0;
    match result {
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
    run_main_counting_on(program, limits, policy, input, output, &mut NoTerminal)
}

/// [`run_main_counting`] with `terminal` for `IO.console` and
/// `IO.keysMode`, as [`run_main_on`].
pub fn run_main_counting_on(
    program: &Program,
    limits: Limits,
    policy: &Policy,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> (Result<Outcome, RunError>, RouteCounts) {
    run_inner(program, limits, policy, input, output, terminal)
}

/// What the runner runs the program's code with (stage NO4 of
/// docs/proposals/native-only.md): the machine ([`Machine`]), or native
/// code (`native_abi::NativeExecutor`). The runner steps the `Delay` that
/// `main` returns and performs its operations; every function application
/// that stepping needs, and every computation it takes apart, is the
/// executor's. Each call starts from the runner, so nothing nests.
pub trait Executor {
    /// The value of the program's entry: `main ()`, a `Delay`.
    fn entry(&mut self) -> Result<Value, ResourceError>;
    /// `f` applied to `args`, as the machine's `apply` applies it.
    fn call(&mut self, f: Value, args: Vec<Value>) -> Result<Value, ResourceError>;
    /// Computation `c` run up to its first operation: `Done v`, or `Call o
    /// rest` with whatever was pending in `c` inside `rest`
    /// ([`Machine::step_comp`]).
    fn step_comp(&mut self, c: Value) -> Result<Value, ResourceError>;
    /// Starts a new stretch of steps (after an operation or a tick).
    fn reset_steps(&mut self);
    /// The program's shapes.
    fn shapes(&self) -> &Shapes;
    /// The row of the operations `main ()` leaves to the runner.
    fn main_row(&self) -> MainRow;
    /// After the run stopped for recursing too deeply: which functions had
    /// the most pending calls, if known.
    fn depth_report(&self) -> Option<String>;
}

/// Runs `program` as [`run_main_on`] does, as native code: `code`, every
/// body `main` reaches compiled for `image` (its entry included), with the
/// runner on a [`NativeExecutor`] (stage NO4 of
/// docs/proposals/native-only.md) and the machine running nothing. The code
/// runs on a stack of `stack_size` bytes (`native_abi::native_stack`: the
/// caller's thread has that many). Flushes `output`.
#[allow(clippy::too_many_arguments)]
pub fn run_main_native(
    program: &Program,
    image: crate::code::Image,
    code: Box<dyn NativeIslands>,
    limits: Limits,
    stack_size: usize,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> Result<(), RunError> {
    let executor = NativeExecutor::new(program, image, code, limits, stack_size);
    run_native_on(executor, limits, input, output, terminal)
}

/// Runs the program `outline` describes as [`run_main_native`] does, as its
/// native `code`, which owns the tables it reads: what an executable built
/// with `--native` runs, with no program, image or machine (stage NO6 of
/// docs/proposals/native-only.md). Flushes `output`.
#[allow(clippy::too_many_arguments)]
pub fn run_main_linked(
    outline: crate::linked::Outline,
    code: Box<dyn NativeIslands>,
    limits: Limits,
    stack_size: usize,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> Result<(), RunError> {
    let executor = NativeExecutor::from_outline(outline, code, limits, stack_size);
    run_native_on(executor, limits, input, output, terminal)
}

/// Runs `executor`'s program, then flushes `output`.
fn run_native_on(
    executor: NativeExecutor,
    limits: Limits,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> Result<(), RunError> {
    let result = run_on(
        executor,
        limits,
        &Policy::default(),
        input,
        output,
        terminal,
    )
    .0;
    match result {
        Ok(_) => output.flush().map_err(RunError::Write),
        Err(e) => {
            let _ = output.flush();
            Err(e)
        }
    }
}

fn run_inner(
    program: &Program,
    limits: Limits,
    policy: &Policy,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> (Result<Outcome, RunError>, RouteCounts) {
    let image = crate::code::compile(program);
    let machine = Machine::with_image(program, image, limits);
    run_on(machine, limits, policy, input, output, terminal)
}

/// [`run_inner`] on `executor`.
fn run_on<E: Executor>(
    mut executor: E,
    limits: Limits,
    policy: &Policy,
    input: &mut impl BufRead,
    output: &mut impl Write,
    terminal: &mut dyn Terminal,
) -> (Result<Outcome, RunError>, RouteCounts) {
    let delay = match executor.entry() {
        Ok(delay) => delay,
        Err(e) => return (Err(entry_error(&executor, e)), RouteCounts::default()),
    };
    let mut runner = Runner::new(executor, limits, *policy, Box::new(terminal));
    let result = runner.run(delay, &mut Blocking(input), output);
    let result = result.map_err(|e| runner.explain(e));
    (result, runner.counts)
}

/// Computing the entry failed with `e`: the error, naming the function that
/// recursed too deeply if that was it.
fn entry_error(executor: &impl Executor, e: ResourceError) -> RunError {
    match (e, executor.depth_report()) {
        (ResourceError::Depth, Some(report)) => RunError::Deep(report),
        (e, _) => e.into(),
    }
}

/// Steps `delay`, a partial computation that performs nothing (a test that
/// runs partial code, D1183), to its result on `machine`, as [`run_main`]
/// steps `main`: the same stepping, budget per stretch and lack of a tick
/// limit.
pub fn run_partial(machine: Machine<'_>, limits: Limits, delay: Value) -> Result<Value, RunError> {
    let mut runner = Runner::new(machine, limits, Policy::default(), Box::new(NoTerminal));
    let driven = runner
        .drive(
            Focus::Eval(delay),
            &mut Blocking(&mut io::empty()),
            &mut io::sink(),
        )
        .map_err(|e| runner.explain(e))?;
    match driven {
        Driven::Finished(v) => Ok(v),
        Driven::OutOfTicks | Driven::Waiting => unreachable!("no tick limit, and no input"),
    }
}

/// What a read of the input needs before it can be done without waiting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReadNeed {
    /// `readBytes`: one read's bytes, or the end of the input.
    Bytes,
    /// `readLine`: a whole line, or the end of the input.
    Line,
    /// `readAll`: the end of the input.
    All,
}

/// The input a run reads. An input that never waits ([`Blocking`]) is
/// read whenever the program asks; one that can (a live run's) is read
/// only once the read can be done whole, so that a read never stops
/// part-way through having taken some of its bytes.
trait RunInput: BufRead {
    /// Whether a read may have to wait: if not, `ready` is never asked.
    const PAUSES: bool;

    /// Whether a read needing `need` can be done now, without waiting.
    fn ready(&mut self, need: ReadNeed) -> bool;
}

/// An input read as it comes: a read that has to wait blocks, as standard
/// input does. What every run but a live one reads.
struct Blocking<'a, I: ?Sized>(&'a mut I);

impl<I: BufRead + ?Sized> Read for Blocking<'_, I> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }

    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> io::Result<usize> {
        self.0.read_to_end(buf)
    }
}

impl<I: BufRead + ?Sized> BufRead for Blocking<'_, I> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.0.fill_buf()
    }

    fn consume(&mut self, n: usize) {
        self.0.consume(n);
    }

    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> io::Result<usize> {
        self.0.read_until(byte, buf)
    }
}

impl<I: BufRead + ?Sized> RunInput for Blocking<'_, I> {
    const PAUSES: bool = false;

    fn ready(&mut self, _need: ReadNeed) -> bool {
        true
    }
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

struct Runner<'t, E> {
    /// What runs the program's code: the machine, or native code
    /// ([`Executor`]).
    m: E,
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
    /// What `IO.console` and `IO.keysMode` do.
    terminal: Box<dyn Terminal + 't>,
    /// A read that couldn't be done yet: the operation, as it reached the
    /// bottom, its continuation, and the `Map` frames it passed. Routing
    /// is done, so going on is performing it ([`Runner::perform_and_go_on`]).
    waiting: Option<HostOp>,
    /// When the frame limit was hit here: what the pending frames were.
    deepest: Option<String>,
}

/// An operation for the host, routed but not performed.
struct HostOp {
    op: Value,
    cont: Cont,
    back: Vec<(usize, Value)>,
}

/// How [`Runner::drive`] stopped.
enum Driven {
    /// The computation's result.
    Finished(Value),
    /// The tick limit was reached.
    OutOfTicks,
    /// A read had to wait: the operation is in [`Runner::waiting`].
    Waiting,
}

impl<'t, E: Executor> Runner<'t, E> {
    fn new(
        m: E,
        limits: Limits,
        policy: Policy,
        terminal: Box<dyn Terminal + 't>,
    ) -> Runner<'t, E> {
        Runner {
            m,
            frames: Vec::new(),
            marks: Vec::new(),
            limits,
            lines: 0,
            ticks: 0,
            policy,
            counts: RouteCounts::default(),
            terminal,
            waiting: None,
            deepest: None,
        }
    }

    /// `e`, with which functions or frames were pending if it is the
    /// recursion limit.
    fn explain(&self, e: RunError) -> RunError {
        if !matches!(e, RunError::Resource(ResourceError::Depth)) {
            return e;
        }
        match self.m.depth_report().or_else(|| self.deepest.clone()) {
            Some(report) => RunError::Deep(report),
            None => e,
        }
    }

    /// What the pending frames are, by kind: the effect runtime's own, for a
    /// recursion that isn't in a pure function.
    #[cold]
    fn note_deepest(&mut self) {
        let (mut binds, mut maps, mut ties, mut awaits, mut handlers) = (0, 0, 0, 0, 0);
        for frame in &self.frames {
            match frame {
                Frame::Bind(_) => binds += 1,
                Frame::Map(..) => maps += 1,
                Frame::Tie(_) => ties += 1,
                Frame::Await { .. } => awaits += 1,
                Frame::Handle { .. } => handlers += 1,
            }
        }
        let mut parts = Vec::new();
        for (n, what) in [
            (
                binds,
                "effectful calls waiting for a result (a recursion that isn't a tail call)",
            ),
            (awaits, "recursive calls waiting for a result"),
            (ties, "recursive functions"),
            (maps, "ability translations"),
            (handlers, "handlers"),
        ] {
            if n > 0 {
                parts.push(format!("{n} {what}"));
            }
        }
        self.deepest = Some(format!("the effect runtime's frames: {}", parts.join(", ")));
    }

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
            self.note_deepest();
            return Err(ResourceError::Depth);
        }
        Ok(())
    }

    fn run(
        &mut self,
        delay: Value,
        input: &mut impl RunInput,
        output: &mut impl Write,
    ) -> Result<Outcome, RunError> {
        match self.drive(Focus::Eval(delay), input, output)? {
            Driven::Finished(_) => Ok(Outcome::Finished),
            Driven::OutOfTicks => Ok(Outcome::OutOfTicks),
            Driven::Waiting => unreachable!("an input that waits in a run that can't"),
        }
    }

    /// Steps from `focus`, at the start of a stretch, to the result, the
    /// tick limit, or a read that has to wait.
    fn drive(
        &mut self,
        mut focus: Focus,
        input: &mut impl RunInput,
        output: &mut impl Write,
    ) -> Result<Driven, RunError> {
        let s = *self.m.shapes();
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
                            Routed::Waiting => return Ok(Driven::Waiting),
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
                                    return Ok(Driven::OutOfTicks);
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
                    None => return Ok(Driven::Finished(v)),
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
    fn route<I: RunInput>(
        &mut self,
        mut op: Value,
        cont: Cont,
        input: &mut I,
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
        // For the host, once it can be done without waiting. Asking only
        // looks at the operation, so a run that waits here and goes on
        // later does exactly what one that never waited does. What a read
        // does before reading is done before waiting, so the host sees the
        // output and the screen as the program left them; performing the
        // read later does it again, which changes nothing.
        if I::PAUSES
            && let Some(need) = self.read_need(&op)
            && !input.ready(need)
        {
            self.before_read(need, output)?;
            self.waiting = Some(HostOp { op, cont, back });
            return Ok(Routed::Waiting);
        }
        self.perform_and_go_on(HostOp { op, cont, back }, input, output)
    }

    /// Performs a routed operation for the host, and goes on with the reply
    /// translated back through the `Map` frames it passed.
    fn perform_and_go_on(
        &mut self,
        routed: HostOp,
        input: &mut impl RunInput,
        output: &mut impl Write,
    ) -> Result<Routed, RunError> {
        let HostOp { op, cont, back } = routed;
        let reply = self.perform(op, input, output)?;
        self.m.reset_steps();
        let frames = std::mem::take(&mut self.frames);
        let reply = self.translate_back(&frames, &back, reply);
        self.frames = frames;
        Ok(Routed::Performed(Focus::Comp(
            self.apply_cont(&cont, reply?)?,
        )))
    }

    /// What a read does before reading: `readLine` and `readAll` leave keys
    /// mode (D1260), and every read flushes the output. Doing it twice is
    /// doing it once (`Terminal::keys_mode` does nothing if it's already
    /// so).
    fn before_read(&mut self, need: ReadNeed, output: &mut impl Write) -> Result<(), RunError> {
        if need != ReadNeed::Bytes {
            self.terminal.keys_mode(false, output)?;
        }
        output.flush().map_err(RunError::Write)
    }

    /// What reading input `op` needs, if it's a read: the decoding of
    /// [`Runner::perform`], looking at the operation without taking it
    /// apart (so it takes no reference, and the allocation trace is that
    /// of a run that doesn't ask).
    fn read_need(&self, op: &Value) -> Option<ReadNeed> {
        fn split(v: &Value) -> Option<(u32, &Value)> {
            match v {
                Value::Data(t, fields) => Some((*t, &fields[0])),
                _ => None,
            }
        }
        let s = self.m.shapes();
        let (side, io) = split(op)?;
        let io = match self.m.main_row() {
            MainRow::Io => io,
            // `L (stop msg)` isn't a read; `R (L io)` is `io`.
            MainRow::FailIo if side == s.left => return None,
            MainRow::FailIo => split(io)?.1,
        };
        let tag = io.tag()?;
        if tag == s.read_bytes {
            Some(ReadNeed::Bytes)
        } else if tag == s.read_line {
            Some(ReadNeed::Line)
        } else if tag == s.read_all {
            Some(ReadNeed::All)
        } else {
            None
        }
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
        let io = match (self.m.main_row(), side(&op)) {
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
        let field = || match &io {
            Value::Data(_, fields) => fields[0].clone(),
            _ => unreachable!("an `IO` operation has a field"),
        };
        Ok(if tag == s.print {
            // `print`, `readLine` and `readAll` leave keys mode first (D1260).
            self.terminal.keys_mode(false, output)?;
            let text = crate::prims::text_of(&field()).clone();
            output
                .write_all(text.as_bytes())
                .and_then(|()| output.write_all(b"\n"))
                .map_err(RunError::Write)?;
            Value::Tag(s.unit)
        } else if tag == s.read_line {
            self.before_read(ReadNeed::Line, output)?;
            match read_line(input, &mut self.lines)? {
                Some(line) => Value::data(s.some, [Value::Text(line.into())]),
                None => Value::Tag(s.none),
            }
        } else if tag == s.read_all {
            self.before_read(ReadNeed::All, output)?;
            Value::Text(read_all(input, &mut self.lines)?.into())
        } else if tag == s.console {
            let console = self.terminal.console();
            let flag = |b: bool| Value::Tag(if b { s.true_ } else { s.false_ });
            Value::data(
                s.console_record,
                [
                    flag(console.input_is_terminal),
                    flag(console.output_is_terminal),
                    Value::Nat(console.columns),
                    Value::Nat(console.rows),
                ],
            )
        } else if tag == s.keys_mode {
            let on = matches!(field(), Value::Tag(t) if t == s.true_);
            self.terminal.keys_mode(on, output)?;
            Value::Tag(s.unit)
        } else if tag == s.read_bytes {
            self.before_read(ReadNeed::Bytes, output)?;
            match read_bytes(input, &mut self.lines)? {
                Some(bytes) => {
                    let mut list = Value::Tag(s.nil);
                    for &b in bytes.iter().rev() {
                        list = Value::data(s.cons, [Value::Nat(b.into()), list]);
                    }
                    Value::data(s.some, [list])
                }
                None => Value::Tag(s.none),
            }
        } else if tag == s.write {
            write_text(output, crate::prims::text_of(&field()))?;
            Value::Tag(s.unit)
        } else if tag == s.random_seed {
            Value::Nat(crate::host::random_seed())
        } else {
            panic!("internal error: an unknown `IO` operation {io:?}")
        })
    }
}

/// Where an operation went.
enum Routed {
    /// It's a read that has to wait: it's in [`Runner::waiting`].
    Waiting,
    /// It was performed: go on with this.
    Performed(Focus),
    /// It was a recursion request: one tick, then this.
    Tick(Focus),
    /// A handler around partial code took it: its clause, then this.
    Handled(Focus),
}
