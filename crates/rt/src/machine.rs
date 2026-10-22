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

use crate::code::{Image, Instr, compile};
use crate::ir::{GlobalId, GlobalKind, PrimOp, Program, Shapes};
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

struct State {
    regs: Vec<Value>,
    frames: Vec<Frame>,
    /// Each global's value, once known: a constant's, or a function value.
    globals: Vec<Option<Value>>,
    steps: u64,
    limits: Limits,
    scratch: Vec<Value>,
}

/// A program, compiled, with its state between runs (the constants
/// computed so far).
pub struct Machine<'p> {
    program: &'p Program,
    image: Image,
    st: State,
}

type Result<T> = std::result::Result<T, ResourceError>;

/// A delivery: a value and where it goes.
type Pending = Option<(Value, Ret)>;

impl<'p> Machine<'p> {
    pub fn new(program: &'p Program, limits: Limits) -> Machine<'p> {
        Machine {
            program,
            image: compile(program),
            st: State {
                regs: Vec::new(),
                frames: Vec::new(),
                globals: vec![None; program.globals.len()],
                steps: 0,
                limits,
                scratch: Vec::new(),
            },
        }
    }

    pub fn shapes(&self) -> &Shapes {
        &self.program.shapes
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
            _ => Ok(self.st.function_value(self.program, g.0)),
        }
    }

    /// `f` applied to `args`.
    pub fn call(&mut self, f: Value, args: Vec<Value>) -> Result<Value> {
        let pending = self.st.apply(self.program, &self.image, f, args, Ret::Host);
        self.finish(pending)
    }

    /// Runs until the host gets a value; on an error, the pending frames
    /// are dropped.
    fn finish(&mut self, pending: Result<Pending>) -> Result<Value> {
        let result = pending.and_then(|p| run(self.program, &self.image, &mut self.st, p));
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

    #[inline]
    fn enter_frame(&mut self) -> Result<()> {
        self.steps += 1;
        if self.steps > self.limits.steps {
            return Err(ResourceError::Work);
        }
        if self.frames.len() >= self.limits.frames {
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
        self.regs.truncate(base);
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
                    let mut args = args.into_iter();
                    let (f, z, t) = (
                        args.next().expect("3"),
                        args.next().expect("3"),
                        args.next().expect("3"),
                    );
                    self.fold_start(program, image, f, z, &t, ret)
                }
                GlobalKind::Native(op) => {
                    let refs: Vec<&Value> = args.iter().collect();
                    Ok(Some((prims::eval(&program.shapes, *op, &refs), ret)))
                }
                _ => {
                    let code = image.global_code[*g as usize].expect("a function has code");
                    self.push(image, code, args, None, ret)?;
                    Ok(None)
                }
            },
            Fun::Closure { lambda, .. } => {
                let code = image.lambda_code[*lambda as usize];
                self.push(image, code, args, Some(fun.clone()), ret)?;
                Ok(None)
            }
            Fun::DoneK => Ok(Some((Value::data_vec(program.shapes.done, args), ret))),
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
}

/// The arity of a function value that isn't a partial application.
fn arity(program: &Program, head: &Value) -> usize {
    let Value::Fun(fun) = head else {
        unreachable!("a function")
    };
    match &**fun {
        Fun::Global(g) => program.globals[*g as usize].kind.params() as usize,
        Fun::Closure { lambda, .. } => program.lambdas[*lambda as usize].params as usize,
        Fun::DoneK => 1,
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
        macro_rules! args {
            ($o:expr) => {
                ops!($o)
                    .iter()
                    .map(|r| st.regs[base + *r as usize].clone())
                    .collect::<Vec<Value>>()
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
                    let new_base = st.regs.len();
                    for r in ops!(args) {
                        let v = st.regs[base + *r as usize].clone();
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
                        let v = st.regs[base + *r as usize].clone();
                        st.scratch.push(v);
                    }
                    st.replace(image, callee, None)?;
                    continue 'outer;
                }
                Instr::Prim { dst, op, args } => {
                    let o = ops!(args);
                    if op == PrimOp::Text(TextNative::TextFold) {
                        save!();
                        let (f, z) = (reg!(o[0]).clone(), reg!(o[1]).clone());
                        let t = reg!(o[2]).clone();
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
                    let fv = reg!(f).clone();
                    let args = args!(args);
                    let to = u32::try_from(base + dst as usize).expect("fits");
                    pending = st.apply(program, image, fv, args, Ret::Reg(to))?;
                    continue 'outer;
                }
                Instr::TailApply { f, args } => {
                    let fv = reg!(f).clone();
                    let args = args!(args);
                    let frame = st.frames.pop().expect("a frame");
                    st.regs.truncate(base);
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
                    let fields: Rc<[Value]> = ops!(args)
                        .iter()
                        .map(|r| st.regs[base + *r as usize].clone())
                        .collect();
                    reg!(dst) = Value::Data(tag, Fields(fields));
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
                Instr::Jump { target } => pc = target as usize,
                Instr::Return { src } => {
                    let v = std::mem::take(&mut reg!(src));
                    let frame = st.frames.pop().expect("a frame");
                    st.regs.truncate(base);
                    pending = Some((v, frame.ret));
                    continue 'outer;
                }
                Instr::Unreachable => panic!("internal error: reached unreachable code"),
            }
        }
    }
}
