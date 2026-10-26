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

use stitchwort_core::{Limits as CoreLimits, ResourceError};

use crate::code::{Image, Instr, MOVE, NO_REG, compile};
use crate::effect::{EffectCounts, EffectOp, Handler, Resume, StateRun};
use crate::ir::{GlobalId, GlobalKind, PrimOp, Program, Shapes};
use crate::native_abi::{NativeIslands, NativeOut, NativeRun, TailRequest};
use crate::natives::TextNative;
use crate::prims;
use crate::value::{Fields, Fun, Value};

/// How much a run may use.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Frames entered (calls) between two operations or ticks.
    pub steps: u64,
    /// Frames pending at once: how deeply a program may recurse.
    pub frames: usize,
}

impl Limits {
    /// The reference evaluator's limits: its work limit as steps, and its
    /// frame limit.
    pub fn from_core(limits: CoreLimits) -> Limits {
        Limits {
            steps: limits.work,
            frames: limits.frames,
        }
    }
}

impl Default for Limits {
    fn default() -> Limits {
        Limits::from_core(CoreLimits::default())
    }
}

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
    /// Native code for some of the program's bodies (`crate::native_abi`),
    /// if the run uses it. Shared, since native code calls back into the
    /// machine (a nested run, [`nested`]), which can call native code again.
    native: Option<Rc<dyn NativeIslands>>,
    /// For each body (by code index): whether native code runs it, so that
    /// every frame the machine would push for it is a call of native code
    /// instead.
    native_codes: Box<[bool]>,
    /// Frames pending below the machine's own: native code's, under a
    /// nested run ([`nested`]). The frame limit counts both.
    frame_base: usize,
    /// A call of native code `enter` decided on, which the run loop makes
    /// before anything else: as a frame `enter` pushes runs only once its
    /// Rust callers have returned (dropping the function value and whatever
    /// else they hold), so does the native call, and the allocation traces
    /// are the same.
    deferred: Option<Box<Deferred>>,
    /// When the frame limit was hit: the codes with the most pending frames,
    /// and how many each had ([`Machine::depth_report`]).
    deepest: Vec<(u32, usize)>,
}

/// A native call `enter` put off ([`State::deferred`]): the body, the
/// closure for a lambda's, the arguments and where the result goes.
type Deferred = (u32, Option<Rc<Fun>>, Vec<Value>, Ret);

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

    fn holding(program: Held<'p>, limits: Limits) -> Machine<'p> {
        // Built before `program` moves in.
        Machine {
            image: compile(&program),
            st: State {
                regs: Vec::new(),
                frames: Vec::new(),
                globals: vec![None; program.globals.len()],
                steps: 0,
                limits,
                scratch: Vec::new(),
                counts: EffectCounts::default(),
                native: None,
                native_codes: Box::default(),
                frame_base: 0,
                deferred: None,
                deepest: Vec::new(),
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
        if self.st.deepest.is_empty() {
            return None;
        }
        let name = |code: u32| -> String {
            if let Some(g) = self.image.global_code.iter().position(|c| *c == Some(code)) {
                return format!("`{}`", self.program.globals[g].name);
            }
            if code == self.image.entry_code {
                return "the program's entry".to_string();
            }
            "an anonymous function".to_string()
        };
        let parts: Vec<String> = self
            .st
            .deepest
            .iter()
            // Only the ones with a real share (the entry has one frame).
            .filter(|&&(_, count)| count * 10 >= self.st.deepest[0].1)
            .map(|&(code, count)| format!("{} ({count} frames pending)", name(code)))
            .collect();
        Some(parts.join(", "))
    }

    /// The compiled code it runs.
    pub fn image(&self) -> &Image {
        &self.image
    }

    /// Runs the bodies `native` has code for as native code, wherever the
    /// machine would push a frame for one (`crate::native_abi`).
    pub fn set_native(&mut self, native: Box<dyn NativeIslands>) {
        self.st.native_codes = (0..self.image.codes.len() as u32)
            .map(|code| native.compiled(code))
            .collect();
        self.st.native = Some(Rc::from(native));
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
        let pushed = self.st.push(&self.image, code, Vec::new(), None, Ret::Host);
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
                    .push(&self.image, code, Vec::new(), None, Ret::ConstHost(g.0));
                self.finish(pushed.map(|()| None))
            }
            _ => Ok(self.st.function_value(&self.program, g.0)),
        }
    }

    /// `f` applied to `args`.
    pub fn call(&mut self, f: Value, args: Vec<Value>) -> Result<Value> {
        let pending = self
            .st
            .apply(&self.program, &self.image, f, args, Ret::Host);
        self.finish(pending)
    }

    /// Runs until the host gets a value; on an error, the pending frames
    /// are dropped.
    fn finish(&mut self, pending: Result<Pending>) -> Result<Value> {
        let result = pending.and_then(|p| run(&self.program, &self.image, &mut self.st, p));
        if result.is_err() {
            self.st.frames.clear();
            self.st.regs.clear();
            self.st.scratch.clear();
        }
        result
    }
}

impl State {
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
        let mut counts: stitchwort_core::collections::HashMap<u32, usize> = Default::default();
        for frame in &self.frames {
            *counts.entry(frame.code).or_insert(0) += 1;
        }
        let mut counts: Vec<(u32, usize)> = counts.into_iter().collect();
        counts.sort_by_key(|&(code, count)| (std::cmp::Reverse(count), code));
        counts.truncate(3);
        self.deepest = counts;
    }

    #[inline]
    fn enter_frame(&mut self) -> Result<()> {
        self.steps += 1;
        if self.steps > self.limits.steps {
            return Err(ResourceError::Work);
        }
        if self.frame_base + self.frames.len() >= self.limits.frames {
            self.note_deepest();
            return Err(ResourceError::Depth);
        }
        Ok(())
    }

    /// Pushes a frame for `code` with arguments `args`.
    fn push(
        &mut self,
        image: &Image,
        code: u32,
        args: Vec<Value>,
        env: Option<Rc<Fun>>,
        ret: Ret,
    ) -> Result<()> {
        self.enter_frame()?;
        let base = self.regs.len();
        self.regs.extend(args);
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

    /// `f` applied to `args` (eval/apply): a value for `ret` now, or a
    /// frame pushed that will return it there.
    fn apply(
        &mut self,
        program: &Program,
        image: &Image,
        f: Value,
        args: Vec<Value>,
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
        let total = held.len() + args.len();
        let mut all = if held.is_empty() {
            args
        } else {
            let mut all = held.to_vec();
            all.extend(args);
            all
        };
        if total < arity {
            let pap = Fun::Pap {
                head: head.clone(),
                args: all.into(),
            };
            return Ok(Some((Value::Fun(Rc::new(pap)), ret)));
        }
        let ret = if total > arity {
            let rest = all.split_off(arity);
            Ret::Apply(Box::new((rest, ret)))
        } else {
            ret
        };
        self.enter(program, image, head, all, ret)
    }

    /// Calls `head` (not a partial application) with exactly the arguments
    /// it takes.
    fn enter(
        &mut self,
        program: &Program,
        image: &Image,
        head: &Value,
        args: Vec<Value>,
        ret: Ret,
    ) -> Result<Pending> {
        let Value::Fun(fun) = head else {
            unreachable!("a function")
        };
        match &**fun {
            Fun::Global(g) => match &program.globals[*g as usize].kind {
                GlobalKind::Native(PrimOp::Text(TextNative::TextFold)) => {
                    // `Text.fold text initial f`.
                    let mut args = args.into_iter();
                    let (t, z, f) = (
                        args.next().expect("3"),
                        args.next().expect("3"),
                        args.next().expect("3"),
                    );
                    self.fold_start(program, image, f, z, &t, ret)
                }
                GlobalKind::Native(PrimOp::Effect(op)) => {
                    self.effect(program, image, *op, args, ret)
                }
                GlobalKind::Native(op) => {
                    let refs: Vec<&Value> = args.iter().collect();
                    Ok(Some((prims::eval(&program.shapes, *op, &refs), ret)))
                }
                _ => {
                    let code = image.global_code[*g as usize].expect("a function has code");
                    if self.native_codes.get(code as usize) == Some(&true) {
                        self.enter_frame()?;
                        self.deferred = Some(Box::new((code, None, args, ret)));
                        return Ok(None);
                    }
                    self.push(image, code, args, None, ret)?;
                    Ok(None)
                }
            },
            Fun::Closure { lambda, .. } => {
                let code = image.lambda_code[*lambda as usize];
                if self.native_codes.get(code as usize) == Some(&true) {
                    self.enter_frame()?;
                    self.deferred = Some(Box::new((code, Some(fun.clone()), args, ret)));
                    return Ok(None);
                }
                self.push(image, code, args, Some(fun.clone()), ret)?;
                Ok(None)
            }
            Fun::DoneK => Ok(Some((Value::data_vec(program.shapes.done, args), ret))),
            Fun::Resume(resume, lazy) => {
                let y = args.into_iter().next().expect("one argument");
                self.resume(program, image, resume, *lazy, y, ret)
            }
            // A state-passing handler's loop, given the state.
            Fun::StateRun(run) => {
                let state = args.into_iter().next().expect("one argument");
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
                self.apply(program, image, rest.clone(), vec![arg.clone()], after)
            }
            // A state-passing handler's `k y`: the loop from `rest y`, as a
            // function of the state.
            Fun::StateK(resume) => {
                let y = args.into_iter().next().expect("one argument");
                let Handler::State { comp, .. } = &*resume.handler else {
                    unreachable!("a state-passing handler's resumption")
                };
                let run = StateRun {
                    handler: resume.handler.clone(),
                    rest: resume.rest.clone(),
                    arg: y,
                    pending: resume.pending.clone(),
                };
                Ok(Some((state_fn(&program.shapes, *comp, run), ret)))
            }
            Fun::JumpK => {
                let mut args = args.into_iter();
                let (v, s) = (args.next().expect("2"), args.next().expect("2"));
                Ok(Some((Value::Fun(Rc::new(Fun::Jumped(v, s))), ret)))
            }
            Fun::Jumped(..) => panic!("internal error: a jump applied"),
            // A resumption of a handler around partial code: `k y` is a
            // `Delay`, and runs nothing (the runner steps it).
            Fun::DelayK(capture) => {
                let y = args.into_iter().next().expect("one argument");
                let resumed = crate::value::Delay::Resumed(capture.clone(), y);
                Ok(Some((Value::Delay(Rc::new(resumed)), ret)))
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
        let args = vec![prims::char_value(&program.shapes, c), acc];
        self.apply(program, image, f, args, Ret::Fold(Box::new(fold)))
    }

    // ------------------------------------------------------- native code

    /// A call of body `code`'s native code, its frame already counted
    /// (`enter_frame`), with `args` and, for a lambda's body, its closure
    /// `env`: the result for `ret`, or what native code asked for in its
    /// place (a tail request) begun.
    fn native_call(
        &mut self,
        program: &Program,
        image: &Image,
        code: u32,
        env: Option<Rc<Fun>>,
        args: Vec<Value>,
        ret: Ret,
    ) -> Result<Pending> {
        let frames = (self.frame_base + self.frames.len() + 1) as u64;
        match self.cross(program, image, code, env, args, frames)? {
            NativeOut::Value(v) => Ok(Some((v, ret))),
            NativeOut::Tail(request) => self.perform(program, image, request, ret),
        }
    }

    /// [`State::replace`] for a body native code runs: the step, the top
    /// frame's closure dropped and its registers released, then the native
    /// call in its place, with the arguments in `scratch`. Its result goes
    /// where the frame's would have.
    fn native_replace(
        &mut self,
        program: &Program,
        image: &Image,
        code: u32,
        env: Option<Rc<Fun>>,
    ) -> Result<Pending> {
        self.steps += 1;
        if self.steps > self.limits.steps {
            return Err(ResourceError::Work);
        }
        let mut frame = self.frames.pop().expect("a frame");
        let base = frame.base as usize;
        // As `replace` drops it: before the registers.
        frame.env = None;
        release(&mut self.regs, base);
        let args = std::mem::take(&mut self.scratch);
        let frames = (self.frame_base + self.frames.len() + 1) as u64;
        match self.cross(program, image, code, env, args, frames)? {
            NativeOut::Value(v) => Ok(Some((v, frame.ret))),
            NativeOut::Tail(request) => self.perform(program, image, request, frame.ret),
        }
    }

    /// Hands a call to native code (`crate::native_abi`), with `frames`
    /// pending, its own included.
    fn cross(
        &mut self,
        program: &Program,
        image: &Image,
        code: u32,
        env: Option<Rc<Fun>>,
        args: Vec<Value>,
        frames: u64,
    ) -> Result<NativeOut> {
        let native = self.native.clone().expect("native code");
        let mut run = NativeRun {
            program,
            image,
            state: self as *mut State,
            steps: self.steps,
            frames,
            limits: self.limits,
            request: None,
        };
        let out = native.call(code, env, args, &mut run);
        self.steps = run.steps;
        out
    }

    /// What native code asked the machine to do in a tail position
    /// (`native_abi::TailRequest`), begun, its result for `ret`: as the
    /// machine's `TailApply` or `TailPrim` would have, after popping the
    /// frame. The frame's closure is dropped once it's begun, as the
    /// machine drops the popped frame's.
    fn perform(
        &mut self,
        program: &Program,
        image: &Image,
        request: TailRequest,
        ret: Ret,
    ) -> Result<Pending> {
        match request {
            TailRequest::Apply { f, args, env } => {
                let pending = self.enter(program, image, head_of(&f), args, ret);
                drop(f);
                drop(env);
                pending
            }
            TailRequest::Effect { op, args, env } => {
                let pending = self.effect(program, image, op, args, ret);
                drop(env);
                pending
            }
        }
    }

    // ------------------------------------------------- the effect runtime

    /// One of the effect runtime's natives applied to `args`
    /// ([`crate::effect`]): a value for `ret` now, or a frame pushed that
    /// will return it there.
    fn effect(
        &mut self,
        program: &Program,
        image: &Image,
        op: EffectOp,
        args: Vec<Value>,
        ret: Ret,
    ) -> Result<Pending> {
        let s = &program.shapes;
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
                        self.apply(program, image, k, vec![x], ret)
                    }
                    c => {
                        self.counts.binds += 1;
                        Ok(Some((Value::data(s.bind_node, [c, k]), ret)))
                    }
                }
            }
            EffectOp::Fold | EffectOp::FoldLazy | EffectOp::FoldIn => {
                let lazy = match op {
                    EffectOp::FoldLazy => true,
                    EffectOp::FoldIn => arg().tag() != Some(s.row_empty),
                    _ => false,
                };
                let (done, call, c) = (arg(), arg(), arg());
                let handler = Rc::new(Handler::Fold { done, call, lazy });
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
                let (done, call, c) = (arg(), arg(), arg());
                let comp = op == EffectOp::FoldStateComp;
                let handler = Rc::new(Handler::State { done, call, comp });
                let run = StateRun {
                    handler,
                    rest: Value::Erased,
                    arg: c,
                    pending: Value::Erased,
                };
                Ok(Some((state_fn(s, comp, run), ret)))
            }
            EffectOp::Translate => {
                let (m, c) = (arg(), arg());
                let Value::Data(_, m) = m else {
                    panic!("internal error: a `SigMap` that isn't `MkSigMap`")
                };
                let (inject, reply) = pair(m);
                let handler = Rc::new(Handler::Translate { inject, reply });
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
            EffectOp::RunPure => {
                let c = arg();
                let handler = Rc::new(Handler::RunPure);
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
                    return self.apply(program, image, k, vec![x], after);
                }
                return match &*handler {
                    Handler::Fold { done, .. } => {
                        let done = done.clone();
                        self.apply(program, image, done, vec![field(fields, 0)], ret)
                    }
                    // `done v s`.
                    Handler::State { done, .. } => {
                        let done = done.clone();
                        let then = Ret::Apply(Box::new((vec![state], ret)));
                        self.apply(program, image, done, vec![field(fields, 0)], then)
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
                self.apply(program, image, call, vec![o, k], ret)
            }
            // `call o k jump s`, its result back to `Ret::Step`.
            Handler::State { call, .. } => {
                self.counts.routes += 1;
                let call = call.clone();
                let resume = resume(handler, Value::Erased);
                let k = Value::Fun(Rc::new(Fun::StateK(resume.clone())));
                let jump = Value::Fun(Rc::new(Fun::JumpK));
                let then = Ret::Step(Box::new((resume, ret)));
                self.apply(program, image, call, vec![o, k, jump, state], then)
            }
            Handler::Translate { inject, .. } => {
                self.counts.routes += 1;
                let inject = inject.clone();
                let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, o.clone()), false)));
                self.apply(
                    program,
                    image,
                    inject,
                    vec![o],
                    Ret::Inject(Box::new((k, ret))),
                )
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
        let s = &program.shapes;
        if lazy {
            self.counts.resumes += 1;
            let k = Value::Fun(Rc::new(Fun::Resume(resume.clone(), false)));
            let c = Value::data(s.bind_node, [Value::data(s.done, [y]), k]);
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
                let args = vec![resume.op.clone(), y];
                self.apply(program, image, reply.clone(), args, then)
            }
            _ => self.apply(program, image, resume.rest.clone(), vec![y], after),
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
        let Value::Fun(mut f) = v else {
            return Ok(Some((v, ret)));
        };
        if !matches!(&*f, Fun::Jumped(..)) {
            return Ok(Some((Value::Fun(f), ret)));
        }
        let (y, state) = match Rc::get_mut(&mut f) {
            Some(Fun::Jumped(y, state)) => (std::mem::take(y), std::mem::take(state)),
            _ => match &*f {
                Fun::Jumped(y, state) => (y.clone(), state.clone()),
                _ => unreachable!("a jump"),
            },
        };
        self.counts.jumps += 1;
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
        let after = Ret::Eff(Box::new(EffRet {
            handler,
            pending,
            state,
            ret,
        }));
        self.apply(program, image, rest, vec![y], after)
    }
}

/// The function a function value calls: a partial application's head, or
/// the value itself.
fn head_of(f: &Value) -> &Value {
    match f {
        Value::Fun(fun) => match &**fun {
            Fun::Pap { head, .. } => head,
            _ => f,
        },
        _ => f,
    }
}

/// What native code asks the machine to run for it ([`nested`]): what the
/// machine runs on its frames, which native code doesn't compile.
pub(crate) enum Work {
    /// One of the effect runtime's natives, on its arguments.
    Effect(EffectOp, Vec<Value>),
    /// `Text.fold text initial f`.
    Fold(Value, Value, Value),
    /// A function value native code has no code for (a resumption, a
    /// native that runs on frames, a body that isn't compiled), entered
    /// with exactly the arguments its head takes (a partial application's
    /// joined to the new ones). The function value is dropped once it's
    /// entered, as `apply` drops it.
    Enter(Value, Vec<Value>),
    /// A tail request a callee made, performed where the caller is.
    Perform(TailRequest),
}

/// Runs `work` for native code to its value: a run of the machine nested
/// on top of whatever is pending, with `frames` frames pending below it
/// (native code's and the machine's), and the steps so far `steps`
/// (updated). The machine's frames are on the heap, so the run nests in
/// Rust only by this call; whatever it calls that has native code runs
/// natively again. On an error, the frames it pushed are dropped.
pub(crate) fn nested(
    crossing: &mut NativeRun<'_>,
    frames: u64,
    steps: &mut u64,
    work: Work,
) -> Result<Value> {
    let (program, image) = (crossing.program, crossing.image);
    // SAFETY: the machine's state, which the machine doesn't touch while
    // native code runs (it's waiting in `State::cross`), and which only
    // this nested run uses until it returns.
    #[allow(unsafe_code)]
    let st = unsafe { &mut *crossing.state };
    let saved = st.frame_base;
    let (frames_at, regs_at) = (st.frames.len(), st.regs.len());
    st.frame_base = (frames as usize).saturating_sub(frames_at);
    st.steps = *steps;
    let begun = match work {
        Work::Effect(op, args) => st.effect(program, image, op, args, Ret::Host),
        Work::Fold(t, z, f) => st.fold_start(program, image, f, z, &t, Ret::Host),
        Work::Enter(f, args) => {
            let pending = st.enter(program, image, head_of(&f), args, Ret::Host);
            drop(f);
            pending
        }
        Work::Perform(request) => st.perform(program, image, request, Ret::Host),
    };
    let result = begun.and_then(|pending| run(program, image, st, pending));
    if result.is_err() {
        st.frames.truncate(frames_at);
        st.regs.truncate(regs_at);
        st.scratch.clear();
        st.deferred = None;
    }
    st.frame_base = saved;
    *steps = st.steps;
    result
}

/// Field `i` of a constructor's cell: moved out if this is the only
/// reference to the cell, otherwise copied.
pub(crate) fn field(mut fields: Fields, i: usize) -> Value {
    match Rc::get_mut(&mut fields.0) {
        Some(slice) => std::mem::take(&mut slice[i]),
        None => fields[i].clone(),
    }
}

/// The two fields of a constructor's cell, as [`field`] takes one.
fn pair(mut fields: Fields) -> (Value, Value) {
    match Rc::get_mut(&mut fields.0) {
        Some(slice) => (std::mem::take(&mut slice[0]), std::mem::take(&mut slice[1])),
        None => (fields[0].clone(), fields[1].clone()),
    }
}

/// A state-passing handler's function of the state, `Done` of it if the
/// handler's carrier is a computation.
fn state_fn(s: &Shapes, comp: bool, run: StateRun) -> Value {
    let f = Value::Fun(Rc::new(Fun::StateRun(Rc::new(run))));
    if comp { Value::data(s.done, [f]) } else { f }
}

/// The arity of a function value that isn't a partial application.
pub(crate) fn arity(program: &Program, head: &Value) -> usize {
    let Value::Fun(fun) = head else {
        unreachable!("a function")
    };
    match &**fun {
        Fun::Global(g) => program.globals[*g as usize].kind.params() as usize,
        Fun::Closure { lambda, .. } => program.lambdas[*lambda as usize].params as usize,
        Fun::DoneK | Fun::Resume(..) | Fun::StateRun(_) | Fun::StateK(_) | Fun::DelayK(_) => 1,
        Fun::JumpK => 2,
        Fun::Jumped(..) => panic!("internal error: a jump applied"),
        Fun::Pap { .. } => unreachable!("a partial application's head"),
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
                    pending = st.apply(program, image, v, args, ret)?;
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
                    pending = st.apply(program, image, f, vec![v], ret)?;
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
        if let Some(deferred) = st.deferred.take() {
            let (code, env, args, ret) = *deferred;
            pending = st.native_call(program, image, code, env, args, ret)?;
            continue;
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
                        st.push(image, code, Vec::new(), None, Ret::Const { g, to })?;
                        continue 'outer;
                    }
                    let v = st.function_value(program, g);
                    reg!(dst) = v;
                }
                Instr::Call { dst, g, args } => {
                    save!();
                    st.enter_frame()?;
                    let callee = image.global_code[g as usize].expect("a function has code");
                    // The crossing into native code (`crate::native_abi`).
                    if st.native_codes.get(callee as usize) == Some(&true) {
                        let values = args!(args);
                        let to = u32::try_from(base + dst as usize).expect("fits");
                        pending =
                            st.native_call(program, image, callee, None, values, Ret::Reg(to))?;
                        continue 'outer;
                    }
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
                    if st.native_codes.get(callee as usize) == Some(&true) {
                        pending = st.native_replace(program, image, callee, None)?;
                        continue 'outer;
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
                    let args = args!(args);
                    let to = u32::try_from(base + dst as usize).expect("fits");
                    pending = st.effect(program, image, op, args, Ret::Reg(to))?;
                    continue 'outer;
                }
                Instr::TailPrim {
                    op: PrimOp::Effect(op),
                    args,
                } => {
                    let args = args!(args);
                    let frame = st.frames.pop().expect("a frame");
                    release(&mut st.regs, base);
                    pending = st.effect(program, image, op, args, frame.ret)?;
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
                        if st.native_codes.get(callee as usize) == Some(&true) {
                            let values = args!(args);
                            drop(fv);
                            pending =
                                st.native_call(program, image, callee, env, values, Ret::Reg(to))?;
                            continue 'outer;
                        }
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
                    let args = args!(args);
                    pending = st.apply(program, image, fv, args, Ret::Reg(to))?;
                    continue 'outer;
                }
                Instr::TailApply { f, args } => {
                    let fv = get!(f);
                    if let Some((callee, env)) = exact(program, image, &fv, args.len) {
                        for r in ops!(args) {
                            let v = get!(*r);
                            st.scratch.push(v);
                        }
                        if st.native_codes.get(callee as usize) == Some(&true) {
                            drop(fv);
                            pending = st.native_replace(program, image, callee, env)?;
                            continue 'outer;
                        }
                        st.replace(image, callee, env)?;
                        continue 'outer;
                    }
                    let args = args!(args);
                    let frame = st.frames.pop().expect("a frame");
                    release(&mut st.regs, base);
                    pending = st.apply(program, image, fv, args, frame.ret)?;
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
