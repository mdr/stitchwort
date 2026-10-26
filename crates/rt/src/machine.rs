//! The machine (docs/proposals/fast-runtime.md, stage 2): runs the code of
//! [`crate::code`] with its own frame stack on the heap, so a program's
//! recursion never recurses in Rust. Deep recursion costs heap memory, the
//! same in the CLI and in WebAssembly, and is bounded by the frame limit.
//!
//! - **Registers.** All frames' registers are one `Vec`; a frame is a
//!   window of it from its `base`. A call puts the arguments in the new
//!   window's first registers.
//! - **Calls.** A saturated call of a known global pushes a frame directly.
//!   A call of a function value goes through `apply` (eval/apply): too few
//!   arguments make a partial application; too many call it with as many
//!   as it takes, then apply the result to the rest ([`Ret::Apply`]).
//!   `apply`, `enter` and the effect natives take their arguments on top of
//!   the registers, above the top frame's window, where a pushed frame's
//!   window then starts: a call allocates no vector of arguments.
//! - **Tail calls** replace the current frame, so a loop runs in constant
//!   space.
//! - **Returns.** Each frame says where its result goes ([`Ret`]): a
//!   register of its caller, the host, a constant's cache, the rest of an
//!   over-application, or the next step of `Text.fold`.
//! - **Constants** are computed when first used, then kept.
//! - **Limits.** Each frame entered is a step; the steps between two
//!   operations or ticks, and the frames, are bounded by [`Limits`], as for
//!   the reference evaluator, and running out is a [`ResourceError`].

use std::rc::Rc;

use smallvec::SmallVec;

use stitchwort_core::ResourceError;

use crate::code::{Image, Instr, MOVE, NO_REG, compile};
use crate::effect::{
    EffectCounts, EffectOp, Handler, Resume, StateRun, StateStep, delay_k, done_k, field,
    handler_for, jump_k, pair, resume_lazily, state_handler, state_k, state_step,
};
use crate::ir::{GlobalId, GlobalKind, PrimOp, Program, Shapes};
use crate::natives::TextNative;
use crate::prims;
pub use crate::shared::Limits;
use crate::shared::{arity, body_name, deepest};
use crate::value::{Fields, Fun, Value};

/// Where a frame's result goes.
enum Ret {
    /// To this register (an index into all registers) of the caller.
    Reg(u32),
    /// Back to the host: the run ends.
    Host,
    /// Constant `g`'s value: kept, and put in register `to`.
    Const { g: u32, to: u32 },
    /// Constant `g`'s value, for the host.
    ConstHost(u32),
    /// Applied to these arguments, with the result going to the `Ret`.
    Apply(Box<(Vec<Value>, Ret)>),
    /// The accumulator of a `Text.fold`, for its next step.
    Fold(Box<Fold>),
    /// A computation, for the effect runtime's loop to go on with
    /// ([`crate::effect`]).
    Eff(Box<EffRet>),
    /// The argument of this function, with the result going to the `Ret`.
    Then(Box<(Value, Ret)>),
    /// An operation, a `translate` has mapped: `Call` of it and this
    /// resumption goes to the `Ret`.
    Inject(Box<(Value, Ret)>),
    /// A state-passing handler's clause's result, for the operation whose
    /// resumption this is: a jump goes on with the loop, anything else goes
    /// to the `Ret`.
    Step(Box<(Rc<Resume>, Ret)>),
}

/// The effect runtime's loop, waiting for a continuation's computation:
/// its handler, what is still pending after it, the state (a state-passing
/// handler's; otherwise erased), and where the loop's result goes.
struct EffRet {
    handler: Rc<Handler>,
    pending: Value,
    state: Value,
    ret: Ret,
}

/// A `Text.fold f z t` in progress: `f` is applied to each character of
/// `t[..end]` and the accumulator, from the last.
struct Fold {
    f: Value,
    text: Rc<str>,
    end: usize,
    ret: Ret,
}

struct Frame {
    code: u32,
    pc: u32,
    base: u32,
    /// The closure whose code this is, for what it captured.
    env: Option<Rc<Fun>>,
    ret: Ret,
}

pub(crate) struct State {
    regs: Vec<Value>,
    frames: Vec<Frame>,
    /// Each global's value, once known: a constant's, or a function value.
    pub(crate) globals: Vec<Option<Value>>,
    pub(crate) steps: u64,
    limits: Limits,
    scratch: Vec<Value>,
    /// The effect runtime's work so far.
    pub(crate) counts: EffectCounts,
    /// When the frame limit was hit: the codes with the most pending frames,
    /// and how many each had ([`Machine::depth_report`]).
    deepest: Vec<(u32, usize)>,
    /// Instructions executed so far by [`run`], added to the thread's total
    /// ([`instructions_executed`]) as each run ends.
    executed: u64,
}

/// The program a machine runs: borrowed, or shared with whatever else holds
/// it (a live run that outlives its caller's borrow, [`crate::run::LiveRun`]).
enum Held<'p> {
    Borrowed(&'p Program),
    Shared(Rc<Program>),
}

impl std::ops::Deref for Held<'_> {
    type Target = Program;

    fn deref(&self) -> &Program {
        match self {
            Held::Borrowed(program) => program,
            Held::Shared(program) => program,
        }
    }
}

/// A program, compiled, with its state between runs (the constants
/// computed so far).
pub struct Machine<'p> {
    program: Held<'p>,
    image: Image,
    st: State,
}

type Result<T> = std::result::Result<T, ResourceError>;

/// A delivery: a value and where it goes.
type Pending = Option<(Value, Ret)>;

impl<'p> Machine<'p> {
    pub fn new(program: &'p Program, limits: Limits) -> Machine<'p> {
        Machine::holding(Held::Borrowed(program), limits)
    }

    /// [`Machine::new`] for a program it shares, so it borrows nothing.
    pub fn shared(program: Rc<Program>, limits: Limits) -> Machine<'static> {
        Machine::holding(Held::Shared(program), limits)
    }

    /// [`Machine::new`] with `image`, the program's compiled image
    /// (`code::compile`), already made.
    pub fn with_image(program: &'p Program, image: Image, limits: Limits) -> Machine<'p> {
        Machine::holding_image(Held::Borrowed(program), image, limits)
    }

    fn holding(program: Held<'p>, limits: Limits) -> Machine<'p> {
        // Built before `program` moves in.
        let image = compile(&program);
        Machine::holding_image(program, image, limits)
    }

    fn holding_image(program: Held<'p>, image: Image, limits: Limits) -> Machine<'p> {
        Machine {
            image,
            st: State {
                regs: Vec::new(),
                frames: Vec::new(),
                globals: vec![None; program.globals.len()],
                steps: 0,
                limits,
                scratch: Vec::new(),
                counts: EffectCounts::default(),
                deepest: Vec::new(),
                executed: 0,
            },
            program,
        }
    }

    /// The effect runtime's work so far ([`crate::effect`]), for tests.
    pub fn effect_counts(&self) -> EffectCounts {
        self.st.counts
    }

    pub fn reset_effect_counts(&mut self) {
        self.st.counts = EffectCounts::default();
    }

    /// Computation `c` run up to its first operation: `Done v`, or
    /// `Call o rest` with whatever was pending in `c` inside `rest`. For a
    /// runner that takes computations apart (the `IO` runner, [`crate::run`]),
    /// since a computation may be a `Bind` node.
    pub fn step_comp(&mut self, c: Value) -> Result<Value> {
        let pending = self.st.eff_run(
            &self.program,
            &self.image,
            c,
            Value::Erased,
            Rc::new(Handler::Step),
            Value::Erased,
            Ret::Host,
        );
        self.finish(pending)
    }

    /// After the run stopped for recursing too deeply: which functions had
    /// the most pending calls, as "`List.append` (120000 calls), …". A
    /// function value that isn't a definition is "a lambda".
    pub fn depth_report(&self) -> Option<String> {
        crate::shared::depth_report(&self.st.deepest, |code| {
            body_name(
                &self.image.global_code,
                self.image.entry_code,
                |g| &self.program.globals[g].name,
                code,
            )
        })
    }

    /// The compiled code it runs.
    pub fn image(&self) -> &Image {
        &self.image
    }

    pub fn shapes(&self) -> &Shapes {
        &self.program.shapes
    }

    /// The program it runs.
    pub fn program(&self) -> &Program {
        &self.program
    }

    /// Starts a new stretch of steps (after an operation or a tick).
    pub fn reset_steps(&mut self) {
        self.st.steps = 0;
    }

    /// The value of the program's entry.
    pub fn entry(&mut self) -> Result<Value> {
        let code = self.image.entry_code;
        let pushed = self.st.push(&self.image, code, 0, None, Ret::Host);
        self.finish(pushed.map(|()| None))
    }

    /// The value of global `g`.
    pub fn global(&mut self, g: GlobalId) -> Result<Value> {
        if let Some(v) = &self.st.globals[g.0 as usize] {
            return Ok(v.clone());
        }
        match &self.program.globals[g.0 as usize].kind {
            GlobalKind::Constant { .. } => {
                let code = self.image.global_code[g.0 as usize].expect("a constant has code");
                let pushed = self
                    .st
                    .push(&self.image, code, 0, None, Ret::ConstHost(g.0));
                self.finish(pushed.map(|()| None))
            }
            _ => Ok(self.st.function_value(&self.program, g.0)),
        }
    }

    /// `f` applied to `args`.
    pub fn call(&mut self, f: Value, args: impl IntoIterator<Item = Value>) -> Result<Value> {
        let n = self.st.put_args(args);
        let pending = self.st.apply(&self.program, &self.image, f, n, Ret::Host);
        self.finish(pending)
    }

    /// Runs until the host gets a value; on an error, the pending frames
    /// are dropped.
    fn finish(&mut self, pending: Result<Pending>) -> Result<Value> {
        let result = pending.and_then(|p| run(&self.program, &self.image, &mut self.st, p));
        count_instructions(std::mem::take(&mut self.st.executed));
        if result.is_err() {
            self.st.release_failed();
        }
        result
    }
}

thread_local! {
    static EXECUTED: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many instructions the machine has executed on this thread so far,
/// summed as each run ends: what `run --native --verbose` reports, which is
/// 0 when the machine ran nothing (stage NO4 of
/// docs/proposals/native-only.md). In every build, since the test tiers run
/// release binaries; an increment per instruction, in the machine's state,
/// is little next to the instruction.
pub fn instructions_executed() -> u64 {
    EXECUTED.with(std::cell::Cell::get)
}

/// Adds a run's instructions to the thread's total.
fn count_instructions(n: u64) {
    EXECUTED.with(|total| total.set(total.get() + n));
}

impl crate::run::Executor for Machine<'_> {
    fn entry(&mut self) -> Result<Value> {
        Machine::entry(self)
    }

    fn call(&mut self, f: Value, args: Vec<Value>) -> Result<Value> {
        Machine::call(self, f, args)
    }

    fn step_comp(&mut self, c: Value) -> Result<Value> {
        Machine::step_comp(self, c)
    }

    fn reset_steps(&mut self) {
        Machine::reset_steps(self);
    }

    fn shapes(&self) -> &Shapes {
        Machine::shapes(self)
    }

    fn main_row(&self) -> crate::ir::MainRow {
        self.program().main_row
    }

    fn depth_report(&self) -> Option<String> {
        Machine::depth_report(self)
    }
}

impl State {
    /// After a failed run: drops everything pending, outermost first: every
    /// frame's closure and pending return, then every register, then a
    /// tail call's fetched arguments.
    fn release_failed(&mut self) {
        self.frames.clear();
        self.regs.clear();
        self.scratch.clear();
    }

    /// A function value for global `g` (a function or a native), or a
    /// native without runtime arguments (`Delay`, a type): erased.
    fn function_value(&mut self, program: &Program, g: u32) -> Value {
        if let Some(v) = &self.globals[g as usize] {
            return v.clone();
        }
        let v = match &program.globals[g as usize].kind {
            GlobalKind::Native(op) if op.arity() == 0 => Value::Erased,
            _ => Value::Fun(Rc::new(Fun::Global(g))),
        };
        self.globals[g as usize] = Some(v.clone());
        v
    }

    /// Records which functions the pending frames belong to: the three with
    /// the most.
    #[cold]
    fn note_deepest(&mut self) {
        self.deepest = deepest(self.frames.iter().map(|frame| frame.code));
    }

    #[inline]
    fn enter_frame(&mut self) -> Result<()> {
        self.steps += 1;
        if self.steps > self.limits.steps {
            return Err(ResourceError::Work);
        }
        if self.frames.len() >= self.limits.frames {
            self.note_deepest();
            return Err(ResourceError::Depth);
        }
        Ok(())
    }

    /// Puts `args` on top of the registers, for `apply`, `enter` or
    /// `effect`: how many.
    fn put_args(&mut self, args: impl IntoIterator<Item = Value>) -> usize {
        let before = self.regs.len();
        self.regs.extend(args);
        self.regs.len() - before
    }

    /// Takes the `n` arguments on top of the registers.
    fn take_args(&mut self, n: usize) -> std::vec::Drain<'_, Value> {
        let at = self.regs.len() - n;
        self.regs.drain(at..)
    }

    /// Pushes a frame for `code` with the `n` arguments on top of the
    /// registers, which become its first registers.
    fn push(
        &mut self,
        image: &Image,
        code: u32,
        n: usize,
        env: Option<Rc<Fun>>,
        ret: Ret,
    ) -> Result<()> {
        let base = self.regs.len() - n;
        if let Err(e) = self.enter_frame() {
            // Dropped as when the arguments were a vector passed here.
            drop(ret);
            drop(env);
            self.regs.truncate(base);
            return Err(e);
        }
        self.regs.resize(
            base + image.codes[code as usize].regs as usize,
            Value::Erased,
        );
        self.frames.push(Frame {
            code,
            pc: 0,
            base: u32::try_from(base).expect("registers fit"),
            env,
            ret,
        });
        Ok(())
    }

    /// Replaces the top frame by one for `code`, with the arguments in
    /// `scratch`.
    fn replace(&mut self, image: &Image, code: u32, env: Option<Rc<Fun>>) -> Result<()> {
        self.steps += 1;
        if self.steps > self.limits.steps {
            return Err(ResourceError::Work);
        }
        let frame = self.frames.last_mut().expect("a frame");
        let base = frame.base as usize;
        frame.code = code;
        frame.pc = 0;
        frame.env = env;
        release(&mut self.regs, base);
        self.regs.append(&mut self.scratch);
        self.regs.resize(
            base + image.codes[code as usize].regs as usize,
            Value::Erased,
        );
        Ok(())
    }

    /// `f` applied to the `n` arguments on top of the registers
    /// (eval/apply), which it takes: a value for `ret` now, or a frame
    /// pushed that will return it there.
    fn apply(
        &mut self,
        program: &Program,
        image: &Image,
        f: Value,
        n: usize,
        ret: Ret,
    ) -> Result<Pending> {
        let Value::Fun(fun) = &f else {
            panic!("internal error: applied {f:?}, which isn't a function")
        };
        let (head, held): (&Value, &[Value]) = match &**fun {
            Fun::Pap { head, args } => (head, args),
            _ => (&f, &[]),
        };
        let arity = arity(program, head);
        let total = held.len() + n;
        let at = self.regs.len() - n;
        if !held.is_empty() {
            // The held arguments go below the new ones.
            self.regs.extend(held.iter().cloned());
            self.regs[at..].rotate_right(held.len());
        }
        if total < arity {
            let pap = Fun::Pap {
                head: head.clone(),
                args: self.regs.drain(at..).collect(),
            };
            return Ok(Some((Value::Fun(Rc::new(pap)), ret)));
        }
        let ret = if total > arity {
            let rest = self.regs.drain(at + arity..).collect();
            Ret::Apply(Box::new((rest, ret)))
        } else {
            ret
        };
        self.enter(program, image, head, arity, ret)
    }

    /// Calls `head` (not a partial application) with the `n` arguments on
    /// top of the registers, exactly as many as it takes.
    fn enter(
        &mut self,
        program: &Program,
        image: &Image,
        head: &Value,
        n: usize,
        ret: Ret,
    ) -> Result<Pending> {
        let Value::Fun(fun) = head else {
            unreachable!("a function")
        };
        match &**fun {
            Fun::Global(g) => match &program.globals[*g as usize].kind {
                GlobalKind::Native(PrimOp::Text(TextNative::TextFold)) => {
                    // `Text.fold text initial f`.
                    let mut args = self.take_args(n);
                    let (t, z, f) = (
                        args.next().expect("3"),
                        args.next().expect("3"),
                        args.next().expect("3"),
                    );
                    drop(args);
                    self.fold_start(program, image, f, z, &t, ret)
                }
                GlobalKind::Native(PrimOp::Effect(op)) => self.effect(program, image, *op, n, ret),
                GlobalKind::Native(op) => {
                    let at = self.regs.len() - n;
                    let refs: SmallVec<[&Value; 4]> = self.regs[at..].iter().collect();
                    let v = prims::eval(&program.shapes, *op, &refs);
                    drop(refs);
                    self.regs.truncate(at);
                    Ok(Some((v, ret)))
                }
                _ => {
                    let code = image.global_code[*g as usize].expect("a function has code");
                    self.push(image, code, n, None, ret)?;
                    Ok(None)
                }
            },
            Fun::Closure { lambda, .. } => {
                let code = image.lambda_code[*lambda as usize];
                self.push(image, code, n, Some(fun.clone()), ret)?;
                Ok(None)
            }
            Fun::DoneK => {
                let y = self.regs.pop().expect("one argument");
                Ok(Some((done_k(&program.shapes, y), ret)))
            }
            Fun::Resume(resume, lazy) => {
                let y = self.regs.pop().expect("one argument");
                self.resume(program, image, resume, *lazy, y, ret)
            }
            // A state-passing handler's loop, given the state.
            Fun::StateRun(run) => {
                let state = self.regs.pop().expect("one argument");
                let StateRun {
                    handler,
                    rest,
                    arg,
                    pending,
                } = &**run;
                let handler = handler.clone();
                if matches!(rest, Value::Erased) {
                    return self.eff_run(
                        program,
                        image,
                        arg.clone(),
                        pending.clone(),
                        handler,
                        state,
                        ret,
                    );
                }
                let after = Ret::Eff(Box::new(EffRet {
                    handler,
                    pending: pending.clone(),
                    state,
                    ret,
                }));
                let rest = rest.clone();
                self.regs.push(arg.clone());
                self.apply(program, image, rest, 1, after)
            }
            // A state-passing handler's `k y`: the loop from `rest y`, as a
            // function of the state.
            Fun::StateK(resume) => {
                let y = self.regs.pop().expect("one argument");
                Ok(Some((state_k(&program.shapes, resume, y), ret)))
            }
            Fun::JumpK => {
                let mut args = self.take_args(n);
                let (v, s) = (args.next().expect("2"), args.next().expect("2"));
                drop(args);
                Ok(Some((jump_k(v, s), ret)))
            }
            Fun::Jumped(..) => panic!("internal error: a jump applied"),
            Fun::DelayK(capture) => {
                let y = self.regs.pop().expect("one argument");
                Ok(Some((delay_k(capture, y), ret)))
            }
            Fun::Pap { .. } => unreachable!("a partial application's head"),
        }
    }

    fn fold_start(
        &mut self,
        program: &Program,
        image: &Image,
        f: Value,
        z: Value,
        t: &Value,
        ret: Ret,
    ) -> Result<Pending> {
        let text = prims::text_of(t).clone();
        let end = text.len();
        self.fold_step(program, image, z, Fold { f, text, end, ret })
    }

    fn fold_step(
        &mut self,
        program: &Program,
        image: &Image,
        acc: Value,
        mut fold: Fold,
    ) -> Result<Pending> {
        let Some(c) = fold.text[..fold.end].chars().next_back() else {
            return Ok(Some((acc, fold.ret)));
        };
        fold.end -= c.len_utf8();
        let f = fold.f.clone();
        self.regs.push(prims::char_value(&program.shapes, c));
        self.regs.push(acc);
        self.apply(program, image, f, 2, Ret::Fold(Box::new(fold)))
    }

    // ------------------------------------------------- the effect runtime

    /// One of the effect runtime's natives applied to the `n` arguments on
    /// top of the registers ([`crate::effect`]): a value for `ret` now, or a
    /// frame pushed that will return it there.
    fn effect(
        &mut self,
        program: &Program,
        image: &Image,
        op: EffectOp,
        n: usize,
        ret: Ret,
    ) -> Result<Pending> {
        let s = &program.shapes;
        let args: SmallVec<[Value; 4]> = self.take_args(n).collect();
        let mut args = args.into_iter();
        let mut arg = || args.next().expect("an effect native's arguments");
        match op {
            EffectOp::Bind => {
                let (c, k) = (arg(), arg());
                match c {
                    // `bind (Done x) k = k x`, a direct call: the backend's
                    // invariant (docs/proposals/effect-runtime.md §9.1.4).
                    Value::Data(tag, fields) if tag == s.done => {
                        let x = field(fields, 0);
                        self.regs.push(x);
                        self.apply(program, image, k, 1, ret)
                    }
                    c => {
                        self.counts.binds += 1;
                        Ok(Some((Value::data(s.bind_node, [c, k]), ret)))
                    }
                }
            }
            EffectOp::Fold
            | EffectOp::FoldLazy
            | EffectOp::FoldIn
            | EffectOp::Translate
            | EffectOp::RunPure => {
                let (handler, c) = handler_for(s, op, arg);
                self.eff_run(
                    program,
                    image,
                    c,
                    Value::Erased,
                    handler,
                    Value::Erased,
                    ret,
                )
            }
            EffectOp::FoldState | EffectOp::FoldStateComp => {
                Ok(Some((state_handler(s, op, arg), ret)))
            }
        }
    }

    /// The run loop: computation `c`, with the continuations `pending`
    /// (cells `[k, next]`, never changed once made; `Erased` when empty)
    /// waiting for its result, for `handler`. `Bind` nodes push their
    /// continuation; `Done` pops one and applies it, on a frame whose result
    /// comes back here (`Ret::Eff`), or ends the loop; an operation ends it.
    /// `state` is a state-passing handler's state, erased for the others.
    #[allow(clippy::too_many_arguments)]
    fn eff_run(
        &mut self,
        program: &Program,
        image: &Image,
        mut c: Value,
        mut pending: Value,
        handler: Rc<Handler>,
        state: Value,
        ret: Ret,
    ) -> Result<Pending> {
        let s = &program.shapes;
        loop {
            self.counts.steps += 1;
            self.steps += 1;
            if self.steps > self.limits.steps {
                return Err(ResourceError::Work);
            }
            let Value::Data(tag, fields) = c else {
                panic!("internal error: running {c:?}, which isn't a computation")
            };
            if tag == s.bind_node {
                self.counts.pushes += 1;
                let (inner, k) = pair(fields);
                pending = Value::data(0, [k, pending]);
                c = inner;
            } else if tag == s.done {
                if let Value::Data(_, cell) = pending {
                    self.counts.pops += 1;
                    let (k, next) = pair(cell);
                    let x = field(fields, 0);
                    let after = Ret::Eff(Box::new(EffRet {
                        handler,
                        pending: next,
                        state,
                        ret,
                    }));
                    self.regs.push(x);
                    return self.apply(program, image, k, 1, after);
                }
                return match &*handler {
                    Handler::Fold { done, .. } => {
                        let done = done.clone();
                        self.regs.push(field(fields, 0));
                        self.apply(program, image, done, 1, ret)
                    }
                    // `done v s`.
                    Handler::State { done, .. } => {
                        let done = done.clone();
                        let then = Ret::Apply(Box::new((vec![state], ret)));
                        self.regs.push(field(fields, 0));
                        self.apply(program, image, done, 1, then)
                    }
                    Handler::RunPure => Ok(Some((field(fields, 0), ret))),
                    Handler::Translate { .. } | Handler::Step => {
                        Ok(Some((Value::Data(tag, fields), ret)))
                    }
                };
            } else {
                debug_assert_eq!(tag, s.call);
                return self.eff_call(program, image, fields, pending, handler, state, ret);
            }
        }
    }

    /// The run loop reached operation `Call o rest` (`fields`), with
    /// `pending` after it.
    #[allow(clippy::too_many_arguments)]
    fn eff_call(
        &mut self,
        program: &Program,
        image: &Image,
        fields: Fields,
        pending: Value,
        handler: Rc<Handler>,
        state: Value,
        ret: Ret,
    ) -> Result<Pending> {
        let s = &program.shapes;
        if let Handler::Step = &*handler
            && matches!(pending, Value::Erased)
        {
            // Nothing pending: the operation as it is, so that the runner
            // can tell a request in tail position by its `rest`.
            return Ok(Some((Value::Data(s.call, fields), ret)));
        }
        let (o, rest) = pair(fields);
        let resume = |handler, op| {
            Rc::new(Resume {
                handler,
                rest,
                pending,
                op,
            })
        };
        match &*handler {
            Handler::Fold { call, lazy, .. } => {
                self.counts.routes += 1;
                let (call, lazy) = (call.clone(), *lazy);
                let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, Value::Erased), lazy)));
                self.regs.extend([o, k]);
                self.apply(program, image, call, 2, ret)
            }
            // `call o k jump s`, its result back to `Ret::Step`.
            Handler::State { call, .. } => {
                self.counts.routes += 1;
                let call = call.clone();
                let resume = resume(handler, Value::Erased);
                let k = Value::Fun(Rc::new(Fun::StateK(resume.clone())));
                let jump = Value::Fun(Rc::new(Fun::JumpK));
                let then = Ret::Step(Box::new((resume, ret)));
                self.regs.extend([o, k, jump, state]);
                self.apply(program, image, call, 4, then)
            }
            Handler::Translate { inject, .. } => {
                self.counts.routes += 1;
                let inject = inject.clone();
                let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, o.clone()), false)));
                self.regs.push(o);
                self.apply(program, image, inject, 1, Ret::Inject(Box::new((k, ret))))
            }
            Handler::Step => {
                let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, Value::Erased), false)));
                Ok(Some((Value::data(s.call, [o, k]), ret)))
            }
            Handler::RunPure => panic!("internal error: an operation reached `runPure`"),
        }
    }

    /// Resumption `resume` called with `y`. A lazy one suspends: it gives
    /// `Bind (Done y) r`, `r` the same resumption, not lazy, for whoever runs
    /// the clause's result to resume. Otherwise the rest of the computation
    /// is run for the same handler, from where the operation was.
    fn resume(
        &mut self,
        program: &Program,
        image: &Image,
        resume: &Rc<Resume>,
        lazy: bool,
        y: Value,
        ret: Ret,
    ) -> Result<Pending> {
        if lazy {
            let c = resume_lazily(&program.shapes, &mut self.counts, resume, y);
            return Ok(Some((c, ret)));
        }
        let after = Ret::Eff(Box::new(EffRet {
            handler: resume.handler.clone(),
            pending: resume.pending.clone(),
            state: Value::Erased,
            ret,
        }));
        match &*resume.handler {
            // `x => translate m (rest (reply o x))`.
            Handler::Translate { reply, .. } => {
                let then = Ret::Then(Box::new((resume.rest.clone(), after)));
                self.regs.extend([resume.op.clone(), y]);
                self.apply(program, image, reply.clone(), 2, then)
            }
            _ => {
                let rest = resume.rest.clone();
                self.regs.push(y);
                self.apply(program, image, rest, 1, after)
            }
        }
    }

    /// A state-passing handler's clause returned `v` for the operation
    /// whose resumption is `resume`: a jump `v′ s′` goes on with the loop
    /// from `rest v′` with state `s′`, on no new frame; anything else is the
    /// handler's result.
    fn state_step(
        &mut self,
        program: &Program,
        image: &Image,
        v: Value,
        resume: Rc<Resume>,
        ret: Ret,
    ) -> Result<Pending> {
        match state_step(&mut self.counts, v, resume) {
            StateStep::Value(v) => Ok(Some((v, ret))),
            StateStep::Jump {
                handler,
                rest,
                pending,
                y,
                state,
                jumped,
            } => {
                let after = Ret::Eff(Box::new(EffRet {
                    handler,
                    pending,
                    state,
                    ret,
                }));
                self.regs.push(y);
                let pending = self.apply(program, image, rest, 1, after);
                // As before this was shared: the jump dropped last.
                drop(jumped);
                pending
            }
        }
    }
}

/// Runs until a value reaches the host: first delivers `pending`, then
/// runs the top frame.
fn run(program: &Program, image: &Image, st: &mut State, mut pending: Pending) -> Result<Value> {
    let s = &program.shapes;
    'outer: loop {
        if let Some((v, ret)) = pending.take() {
            match ret {
                Ret::Reg(r) => st.regs[r as usize] = v,
                Ret::Host => return Ok(v),
                Ret::Const { g, to } => {
                    st.globals[g as usize] = Some(v.clone());
                    st.regs[to as usize] = v;
                }
                Ret::ConstHost(g) => {
                    st.globals[g as usize] = Some(v.clone());
                    return Ok(v);
                }
                Ret::Apply(rest) => {
                    let (args, ret) = *rest;
                    let n = st.put_args(args);
                    pending = st.apply(program, image, v, n, ret)?;
                    continue;
                }
                Ret::Fold(fold) => {
                    pending = st.fold_step(program, image, v, *fold)?;
                    continue;
                }
                Ret::Eff(e) => {
                    let EffRet {
                        handler,
                        pending: after,
                        state,
                        ret,
                    } = *e;
                    pending = st.eff_run(program, image, v, after, handler, state, ret)?;
                    continue;
                }
                Ret::Then(then) => {
                    let (f, ret) = *then;
                    st.regs.push(v);
                    pending = st.apply(program, image, f, 1, ret)?;
                    continue;
                }
                Ret::Inject(inject) => {
                    let (k, ret) = *inject;
                    pending = Some((Value::data(s.call, [v, k]), ret));
                    continue;
                }
                Ret::Step(step) => {
                    let (resume, ret) = *step;
                    pending = st.state_step(program, image, v, resume, ret)?;
                    continue;
                }
            }
        }
        let top = st.frames.last().expect("a frame to run");
        let code = &image.codes[top.code as usize];
        let base = top.base as usize;
        let mut pc = top.pc as usize;
        macro_rules! reg {
            ($r:expr) => {
                st.regs[base + $r as usize]
            };
        }
        macro_rules! ops {
            ($o:expr) => {
                &code.ops[$o.start as usize..($o.start + $o.len) as usize]
            };
        }
        // Saves the position, before the frame calls something.
        macro_rules! save {
            () => {
                st.frames.last_mut().expect("a frame").pc = pc as u32
            };
        }
        // An operand: moved out if it's marked `MOVE`, otherwise copied.
        macro_rules! get {
            ($r:expr) => {{
                let r = $r;
                if r & MOVE != 0 {
                    std::mem::take(&mut st.regs[base + (r & !MOVE) as usize])
                } else {
                    st.regs[base + r as usize].clone()
                }
            }};
        }
        macro_rules! args {
            ($o:expr) => {
                ops!($o).iter().map(|r| get!(*r)).collect::<Vec<Value>>()
            };
        }
        loop {
            let instr = code.instrs[pc];
            pc += 1;
            st.executed += 1;
            match instr {
                Instr::Move { dst, src } => {
                    let v = reg!(src).clone();
                    reg!(dst) = v;
                }
                Instr::Const { dst, k } => reg!(dst) = image.pool[k as usize].clone(),
                Instr::Captured { dst, i } => {
                    let v = match st.frames.last().and_then(|f| f.env.as_deref()) {
                        Some(Fun::Closure { captures, .. }) => captures[i as usize].clone(),
                        _ => panic!("internal error: a capture outside a closure"),
                    };
                    reg!(dst) = v;
                }
                Instr::Global { dst, g } => {
                    if let Some(v) = &st.globals[g as usize] {
                        let v = v.clone();
                        reg!(dst) = v;
                        continue;
                    }
                    if let GlobalKind::Constant { .. } = program.globals[g as usize].kind {
                        save!();
                        let code = image.global_code[g as usize].expect("a constant has code");
                        let to = u32::try_from(base + dst as usize).expect("registers fit");
                        st.push(image, code, 0, None, Ret::Const { g, to })?;
                        continue 'outer;
                    }
                    let v = st.function_value(program, g);
                    reg!(dst) = v;
                }
                Instr::Call { dst, g, args } => {
                    save!();
                    st.enter_frame()?;
                    let callee = image.global_code[g as usize].expect("a function has code");
                    let new_base = st.regs.len();
                    for r in ops!(args) {
                        let v = get!(*r);
                        st.regs.push(v);
                    }
                    st.regs.resize(
                        new_base + image.codes[callee as usize].regs as usize,
                        Value::Erased,
                    );
                    st.frames.push(Frame {
                        code: callee,
                        pc: 0,
                        base: u32::try_from(new_base).expect("registers fit"),
                        env: None,
                        ret: Ret::Reg(u32::try_from(base + dst as usize).expect("fits")),
                    });
                    continue 'outer;
                }
                Instr::TailCall { g, args } => {
                    let callee = image.global_code[g as usize].expect("a function has code");
                    for r in ops!(args) {
                        let v = get!(*r);
                        st.scratch.push(v);
                    }
                    st.replace(image, callee, None)?;
                    continue 'outer;
                }
                Instr::Prim {
                    dst,
                    op: PrimOp::Effect(op),
                    args,
                } => {
                    save!();
                    for r in ops!(args) {
                        let v = get!(*r);
                        st.regs.push(v);
                    }
                    let to = u32::try_from(base + dst as usize).expect("fits");
                    pending = st.effect(program, image, op, args.len as usize, Ret::Reg(to))?;
                    continue 'outer;
                }
                Instr::TailPrim {
                    op: PrimOp::Effect(op),
                    args,
                } => {
                    for r in ops!(args) {
                        let v = get!(*r);
                        st.scratch.push(v);
                    }
                    let frame = st.frames.pop().expect("a frame");
                    release(&mut st.regs, base);
                    st.regs.append(&mut st.scratch);
                    pending = st.effect(program, image, op, args.len as usize, frame.ret)?;
                    continue 'outer;
                }
                Instr::TailPrim { op, .. } => {
                    panic!("internal error: a tail `{}`", op.name())
                }
                Instr::Prim { dst, op, args } => {
                    let o = ops!(args);
                    if op == PrimOp::Text(TextNative::TextFold) {
                        save!();
                        // `Text.fold text initial f`.
                        let t = reg!(o[0]).clone();
                        let (z, f) = (reg!(o[1]).clone(), reg!(o[2]).clone());
                        let to = u32::try_from(base + dst as usize).expect("fits");
                        pending = st.fold_start(program, image, f, z, &t, Ret::Reg(to))?;
                        continue 'outer;
                    }
                    let v = match o {
                        [a] => prims::eval(s, op, &[&reg!(*a)]),
                        [a, b] => prims::eval(s, op, &[&reg!(*a), &reg!(*b)]),
                        [a, b, c] => prims::eval(s, op, &[&reg!(*a), &reg!(*b), &reg!(*c)]),
                        _ => {
                            let refs: Vec<&Value> =
                                o.iter().map(|r| &st.regs[base + *r as usize]).collect();
                            prims::eval(s, op, &refs)
                        }
                    };
                    reg!(dst) = v;
                }
                Instr::Pap { dst, g, args } => {
                    let held = args!(args);
                    let head = st.function_value(program, g);
                    reg!(dst) = Value::Fun(Rc::new(Fun::Pap {
                        head,
                        args: held.into(),
                    }));
                }
                Instr::Apply { dst, f, args } => {
                    save!();
                    let fv = get!(f);
                    let to = u32::try_from(base + dst as usize).expect("fits");
                    // A closure or a global function given exactly the
                    // arguments it takes: its frame is pushed directly.
                    if let Some((callee, env)) = exact(program, image, &fv, args.len) {
                        st.enter_frame()?;
                        let new_base = st.regs.len();
                        for r in ops!(args) {
                            let v = get!(*r);
                            st.regs.push(v);
                        }
                        st.regs.resize(
                            new_base + image.codes[callee as usize].regs as usize,
                            Value::Erased,
                        );
                        st.frames.push(Frame {
                            code: callee,
                            pc: 0,
                            base: u32::try_from(new_base).expect("registers fit"),
                            env,
                            ret: Ret::Reg(to),
                        });
                        continue 'outer;
                    }
                    for r in ops!(args) {
                        let v = get!(*r);
                        st.regs.push(v);
                    }
                    pending = st.apply(program, image, fv, args.len as usize, Ret::Reg(to))?;
                    continue 'outer;
                }
                Instr::TailApply { f, args } => {
                    let fv = get!(f);
                    if let Some((callee, env)) = exact(program, image, &fv, args.len) {
                        for r in ops!(args) {
                            let v = get!(*r);
                            st.scratch.push(v);
                        }
                        st.replace(image, callee, env)?;
                        continue 'outer;
                    }
                    for r in ops!(args) {
                        let v = get!(*r);
                        st.scratch.push(v);
                    }
                    let frame = st.frames.pop().expect("a frame");
                    release(&mut st.regs, base);
                    st.regs.append(&mut st.scratch);
                    pending = st.apply(program, image, fv, args.len as usize, frame.ret)?;
                    continue 'outer;
                }
                Instr::Closure { dst, lambda, args } => {
                    let captures = args!(args);
                    reg!(dst) = Value::Fun(Rc::new(Fun::Closure {
                        lambda,
                        captures: captures.into(),
                    }));
                }
                Instr::Ctor { dst, tag, args } => {
                    let fields: Rc<[Value]> = ops!(args).iter().map(|r| get!(*r)).collect();
                    crate::alloc_trace::alloc(tag, &fields);
                    reg!(dst) = Value::Data(tag, Fields(fields));
                }
                Instr::CtorReuse {
                    dst,
                    tag,
                    args,
                    token,
                } => {
                    let o = ops!(args);
                    let v = match std::mem::take(&mut reg!(token)) {
                        Value::Data(_, mut cell) if cell.len() == o.len() && unique(&cell.0) => {
                            for (i, r) in o.iter().enumerate() {
                                let v = get!(*r);
                                Rc::get_mut(&mut cell.0).expect("unique")[i] = v;
                            }
                            crate::alloc_trace::reuse(tag, &cell.0);
                            Value::Data(tag, cell)
                        }
                        _ => {
                            let fields: Rc<[Value]> = o.iter().map(|r| get!(*r)).collect();
                            crate::alloc_trace::alloc(tag, &fields);
                            Value::Data(tag, Fields(fields))
                        }
                    };
                    reg!(dst) = v;
                }
                Instr::Take { dst, src } => {
                    let v = std::mem::take(&mut reg!(src));
                    reg!(dst) = v;
                }
                Instr::Drop { reg } => reg!(reg) = Value::Erased,
                Instr::Unpack { src, fields, token } => {
                    let pairs = ops!(fields);
                    let Value::Data(tag, mut cell) = std::mem::take(&mut reg!(src)) else {
                        panic!("internal error: unpacking a value that isn't a constructor")
                    };
                    if let Some(slice) = Rc::get_mut(&mut cell.0) {
                        for p in pairs.as_chunks::<2>().0 {
                            st.regs[base + p[1] as usize] =
                                std::mem::take(&mut slice[p[0] as usize]);
                        }
                        if token != NO_REG {
                            // Empty the cell: what the arm doesn't use is
                            // freed now.
                            for v in slice.iter_mut() {
                                *v = Value::Erased;
                            }
                            reg!(token) = Value::Data(tag, cell);
                        }
                    } else {
                        for p in pairs.as_chunks::<2>().0 {
                            st.regs[base + p[1] as usize] = cell[p[0] as usize].clone();
                        }
                        if token != NO_REG {
                            reg!(token) = Value::Erased;
                        }
                    }
                }
                Instr::DropReuse { src, token } => {
                    let v = match std::mem::take(&mut reg!(src)) {
                        Value::Data(tag, mut cell) if unique(&cell.0) => {
                            for v in Rc::get_mut(&mut cell.0).expect("unique").iter_mut() {
                                *v = Value::Erased;
                            }
                            Value::Data(tag, cell)
                        }
                        _ => Value::Erased,
                    };
                    reg!(token) = v;
                }
                Instr::Switch { src, table } => {
                    let tag = reg!(src).tag().expect("a constructor");
                    pc = code.tables[table as usize][tag as usize] as usize;
                }
                Instr::Field { dst, src, i } => {
                    let v = match &reg!(src) {
                        Value::Data(_, fields) => fields[i as usize].clone(),
                        other => panic!("internal error: field {i} of {other:?}"),
                    };
                    reg!(dst) = v;
                }
                Instr::NatCase { src, zero } => {
                    if let Value::Nat(0) = reg!(src) {
                        pc = zero as usize;
                    }
                }
                Instr::NatPred { dst, src } => {
                    let v = match &reg!(src) {
                        Value::Nat(n) => Value::Nat(n - 1),
                        other => Value::nat(other.to_biguint() - 1u32),
                    };
                    reg!(dst) = v;
                }
                Instr::IntCase { src, neg } => {
                    let negative = match &reg!(src) {
                        Value::Int(i) => *i < 0,
                        Value::BigInt(i) => i.sign() == num_bigint::Sign::Minus,
                        other => panic!("internal error: an `Int` match on {other:?}"),
                    };
                    if negative {
                        pc = neg as usize;
                    }
                }
                Instr::IntOfNat { dst, src } => {
                    let v = prims::int_to_nat(&reg!(src));
                    reg!(dst) = v;
                }
                Instr::IntNegSucc { dst, src } => {
                    let v = prims::int_neg_succ(&reg!(src));
                    reg!(dst) = v;
                }
                Instr::TextChars { dst, src } => {
                    let v = prims::chars(s, prims::text_of(&reg!(src)));
                    reg!(dst) = v;
                }
                Instr::NumSwitch { src, table } => {
                    pc = prims::num_switch(&code.num_tables[table as usize], &reg!(src)) as usize;
                }
                Instr::JumpIfFalse { cond, target } => match reg!(cond).tag() {
                    Some(t) if t == s.true_ => {}
                    Some(t) if t == s.false_ => pc = target as usize,
                    _ => panic!("internal error: `if` on {:?}", reg!(cond)),
                },
                Instr::Test { op, args, target } => {
                    use crate::natives::IntNative;
                    use stitchwort_core::native::Native;
                    let o = ops!(args);
                    // Numbers that fit a word are compared here; anything
                    // else as the native computes it.
                    let fast = match o {
                        [a, b] => match (op, &reg!(*a), &reg!(*b)) {
                            (PrimOp::Nat(Native::Leq), Value::Nat(x), Value::Nat(y)) => {
                                Some(x <= y)
                            }
                            (PrimOp::Nat(Native::EqNat), Value::Nat(x), Value::Nat(y)) => {
                                Some(x == y)
                            }
                            (PrimOp::IntEqual, Value::Int(x), Value::Int(y)) => Some(x == y),
                            (PrimOp::Int(IntNative::IntLess), Value::Int(x), Value::Int(y)) => {
                                Some(x < y)
                            }
                            (PrimOp::Int(IntNative::IntLeq), Value::Int(x), Value::Int(y)) => {
                                Some(x <= y)
                            }
                            _ => None,
                        },
                        _ => None,
                    };
                    let holds = match fast {
                        Some(holds) => holds,
                        None => {
                            let refs: Vec<&Value> =
                                o.iter().map(|r| &st.regs[base + *r as usize]).collect();
                            match prims::eval(s, op, &refs).tag() {
                                Some(t) if t == s.true_ => true,
                                Some(t) if t == s.false_ => false,
                                other => panic!("internal error: a test made {other:?}"),
                            }
                        }
                    };
                    if !holds {
                        pc = target as usize;
                    }
                }
                Instr::Jump { target } => pc = target as usize,
                Instr::Return { src } => {
                    let v = std::mem::take(&mut reg!(src));
                    let frame = st.frames.pop().expect("a frame");
                    release(&mut st.regs, base);
                    pending = Some((v, frame.ret));
                    continue 'outer;
                }
                Instr::Unreachable => panic!("internal error: reached unreachable code"),
            }
        }
    }
}

/// Drops the registers from `base` on (a frame's, when it ends). Most hold
/// nothing that needs freeing (moved out, or a number or a tag), so those
/// are checked inline rather than each going through `Value`'s drop.
#[inline]
fn release(regs: &mut Vec<Value>, base: usize) {
    while regs.len() > base {
        let v = regs.pop().expect("a register");
        if v.owns() {
            drop(v);
        } else {
            std::mem::forget(v);
        }
    }
}

/// Whether this is the only reference to the cell, so that it can be
/// changed in place.
#[inline]
fn unique(cell: &Rc<[Value]>) -> bool {
    Rc::strong_count(cell) == 1 && Rc::weak_count(cell) == 0
}

/// The code to run for `f` applied to exactly `n` arguments, and its
/// closure, if `f` is a closure or a global function (not a native) that
/// takes `n`.
#[inline]
fn exact(program: &Program, image: &Image, f: &Value, n: u32) -> Option<(u32, Option<Rc<Fun>>)> {
    let Value::Fun(fun) = f else { return None };
    match &**fun {
        Fun::Closure { lambda, .. } if program.lambdas[*lambda as usize].params == n => {
            Some((image.lambda_code[*lambda as usize], Some(fun.clone())))
        }
        Fun::Global(g) => match &program.globals[*g as usize].kind {
            GlobalKind::Function { params, .. } if *params == n => Some((
                image.global_code[*g as usize].expect("a function has code"),
                None,
            )),
            _ => None,
        },
        _ => None,
    }
}
