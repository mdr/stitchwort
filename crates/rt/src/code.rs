//! The machine's code: each body of the IR (a global function's or
//! constant's, a lambda's, the entry) compiled to a flat list of register
//! instructions ([`Instr`]).
//!
//! A frame is a window of registers: the IR's slots first (the parameters
//! in `0..params`), then temporaries for intermediate results. Each
//! instruction names the registers it reads and writes; a call's arguments
//! are a list of registers ([`Ops`], an index into [`Code::ops`]), so a
//! variable is passed without being copied first. Control flow inside a body
//! is jumps; calls, returns and tail calls go through the machine's own
//! frame stack, never the Rust stack.
//!
//! **Moves and reuse** (stage 4, Perceus/Lean-style; fast-runtime.md "As
//! built (stage 4)"). The compiler knows which slots are read later
//! (liveness over the IR), so:
//!
//! - an operand read for the last time is *moved* out of its register
//!   ([`MOVE`] on the register), not copied: the value's reference count
//!   doesn't go up, so a list passed on is still uniquely owned;
//! - a variable that a branch doesn't need is dropped as the branch starts
//!   ([`Instr::Drop`]), so what it held is freed (or becomes unique) early;
//! - a `match` whose scrutinee the arm doesn't need again takes the fields
//!   out ([`Instr::Unpack`]): when the cell is uniquely owned, they're moved,
//!   and if the arm builds a constructor with as many fields, the cell is
//!   kept as a *reuse token* that [`Instr::CtorReuse`] fills in place
//!   instead of allocating. A cell that is shared is never changed: its
//!   fields are copied and it's left alone. The same holds for a variable
//!   known to be a constructor (from an enclosing match) that the branch
//!   drops ([`Instr::DropReuse`]).

use std::collections::HashMap;

use num_bigint::BigUint;

use crate::ir::{Expr, Lit, MatchKind, PrimOp, Program, Slot};
use crate::value::Value;

/// A register: an index into the current frame.
pub type Reg = u32;

/// On a register in [`Code::ops`] (or [`Instr::Apply`]'s function): the
/// value is moved out of the register, which isn't read again.
pub const MOVE: Reg = 1 << 31;

/// No register: a [`Instr::Unpack`] that keeps no reuse token.
pub const NO_REG: Reg = u32::MAX;

/// A list of registers: `len` entries of [`Code::ops`] from `start`.
#[derive(Clone, Copy, Debug)]
pub struct Ops {
    pub start: u32,
    pub len: u32,
}

#[derive(Clone, Copy, Debug)]
pub enum Instr {
    Move {
        dst: Reg,
        src: Reg,
    },
    /// Moves the value: `src` isn't read again.
    Take {
        dst: Reg,
        src: Reg,
    },
    /// Drops the register's value: it isn't read again.
    Drop {
        reg: Reg,
    },
    /// A value from the program's constant pool.
    Const {
        dst: Reg,
        k: u32,
    },
    /// A value the current closure captured.
    Captured {
        dst: Reg,
        i: u32,
    },
    /// A global's value: a constant's (computed on first use), or a
    /// function or native as a function value.
    Global {
        dst: Reg,
        g: u32,
    },
    /// A call of a global function with all its arguments.
    Call {
        dst: Reg,
        g: u32,
        args: Ops,
    },
    /// The same, in tail position: the callee replaces this frame.
    TailCall {
        g: u32,
        args: Ops,
    },
    Prim {
        dst: Reg,
        op: PrimOp,
        args: Ops,
    },
    /// An effect runtime native ([`PrimOp::Effect`]) in tail position: what
    /// it calls replaces this frame.
    TailPrim {
        op: PrimOp,
        args: Ops,
    },
    /// A global function or native with too few arguments.
    Pap {
        dst: Reg,
        g: u32,
        args: Ops,
    },
    /// A function value applied to arguments (eval/apply).
    Apply {
        dst: Reg,
        f: Reg,
        args: Ops,
    },
    TailApply {
        f: Reg,
        args: Ops,
    },
    Closure {
        dst: Reg,
        lambda: u32,
        args: Ops,
    },
    /// A constructor with at least one field.
    Ctor {
        dst: Reg,
        tag: u32,
        args: Ops,
    },
    /// The same, in the cell held by `token` if it's a uniquely owned cell
    /// with as many fields (left by [`Instr::Unpack`] or
    /// [`Instr::DropReuse`]); otherwise a new one. The token is used up.
    CtorReuse {
        dst: Reg,
        tag: u32,
        args: Ops,
        token: Reg,
    },
    /// Jumps to `tables[table][tag]`, by the constructor's tag.
    Switch {
        src: Reg,
        table: u32,
    },
    /// Field `i` of a constructor.
    Field {
        dst: Reg,
        src: Reg,
        i: u32,
    },
    /// Takes the constructor out of `src` (not read again) and puts its
    /// fields in registers: `fields` is pairs of a field's index and its
    /// register. If the cell is uniquely owned, the fields are moved out,
    /// and the cell, emptied, is the reuse token in `token` (unless
    /// `token` is [`NO_REG`]); otherwise they're copied and `token` is
    /// left empty.
    Unpack {
        src: Reg,
        fields: Ops,
        token: Reg,
    },
    /// Drops `src`'s value (not read again), keeping its cell as a reuse
    /// token in `token` if it's a uniquely owned constructor cell.
    DropReuse {
        src: Reg,
        token: Reg,
    },
    /// Jumps to `zero` if the `Nat` is zero.
    NatCase {
        src: Reg,
        zero: u32,
    },
    /// The `Nat` one less (it isn't zero).
    NatPred {
        dst: Reg,
        src: Reg,
    },
    /// Jumps to `neg` if the `Int` is negative.
    IntCase {
        src: Reg,
        neg: u32,
    },
    /// The `Int` (not negative) as a `Nat`.
    IntOfNat {
        dst: Reg,
        src: Reg,
    },
    /// `-x - 1` of the `Int` (negative), as a `Nat`.
    IntNegSucc {
        dst: Reg,
        src: Reg,
    },
    /// A `Text`'s characters, as a `List Char`.
    TextChars {
        dst: Reg,
        src: Reg,
    },
    /// Jumps by a `Nat`'s value: [`Code::num_tables`].
    NumSwitch {
        src: Reg,
        table: u32,
    },
    JumpIfFalse {
        cond: Reg,
        target: u32,
    },
    /// `if %op(args) then …` for a native test ([`is_test`]): jumps to
    /// `target` if it's false, without making a `Bool` (a combined
    /// `Prim` and `JumpIfFalse`).
    Test {
        op: PrimOp,
        args: Ops,
        target: u32,
    },
    Jump {
        target: u32,
    },
    Return {
        src: Reg,
    },
    Unreachable,
}

/// A [`Instr::NumSwitch`]'s targets.
#[derive(Debug)]
pub struct NumTable {
    pub small: Vec<(u64, u32)>,
    pub big: Vec<(BigUint, u32)>,
    pub default: u32,
}

/// One body's code.
#[derive(Debug)]
pub struct Code {
    pub instrs: Vec<Instr>,
    pub ops: Vec<Reg>,
    pub tables: Vec<Box<[u32]>>,
    pub num_tables: Vec<NumTable>,
    /// The frame's registers, slots and temporaries.
    pub regs: u32,
    /// How many arguments it takes, in registers `0..params`.
    pub params: u32,
}

/// What the machine runs: the code of every body, and the constants.
pub struct Image {
    pub codes: Vec<Code>,
    /// Each global's code, for a function or constant.
    pub global_code: Vec<Option<u32>>,
    pub lambda_code: Vec<u32>,
    pub entry_code: u32,
    /// The constant pool: literals, and values like `y => Done y`.
    pub pool: Vec<Value>,
}

/// The pool's first entries.
pub const ERASED: u32 = 0;
pub const DONE_K: u32 = 1;

/// Compiles every body of `program`.
pub fn compile(program: &Program) -> Image {
    let mut pool = vec![
        Value::Erased,
        Value::Fun(std::rc::Rc::new(crate::value::Fun::DoneK)),
    ];
    let mut codes = Vec::new();
    let mut global_code = Vec::with_capacity(program.globals.len());
    for global in &program.globals {
        use crate::ir::GlobalKind;
        let code = match &global.kind {
            GlobalKind::Function { params, body } => Some(Compiler::body(
                program, &mut pool, *params, body.frame, &body.expr,
            )),
            GlobalKind::Constant { body } => Some(Compiler::body(
                program, &mut pool, 0, body.frame, &body.expr,
            )),
            GlobalKind::Native(_) => None,
        };
        global_code.push(code.map(|c| {
            codes.push(c);
            u32::try_from(codes.len() - 1).expect("codes fit")
        }));
    }
    let mut lambda_code = Vec::with_capacity(program.lambdas.len());
    for lambda in &program.lambdas {
        codes.push(Compiler::body(
            program,
            &mut pool,
            lambda.params,
            lambda.body.frame,
            &lambda.body.expr,
        ));
        lambda_code.push(u32::try_from(codes.len() - 1).expect("codes fit"));
    }
    codes.push(Compiler::body(
        program,
        &mut pool,
        0,
        program.entry.frame,
        &program.entry.expr,
    ));
    let entry_code = u32::try_from(codes.len() - 1).expect("codes fit");
    Image {
        codes,
        global_code,
        lambda_code,
        entry_code,
        pool,
    }
}

/// A native that makes a `Bool`, which [`Instr::Test`] tests directly.
pub fn is_test(op: PrimOp) -> bool {
    use crate::natives::{IntNative, TextNative};
    use stitchwort_core::native::Native;
    matches!(
        op,
        PrimOp::Nat(Native::Leq | Native::EqNat)
            | PrimOp::IntEqual
            | PrimOp::TextEqual
            | PrimOp::Int(IntNative::IntLeq | IntNative::IntLess)
            | PrimOp::Text(TextNative::TextIsEmpty)
    )
}

// ---------------------------------------------------------------- liveness

/// A set of slots.
#[derive(Clone, Default)]
struct Slots(Vec<u64>);

impl Slots {
    fn insert(&mut self, s: Slot) {
        let i = (s / 64) as usize;
        if self.0.len() <= i {
            self.0.resize(i + 1, 0);
        }
        self.0[i] |= 1 << (s % 64);
    }

    fn remove(&mut self, s: Slot) {
        if let Some(w) = self.0.get_mut((s / 64) as usize) {
            *w &= !(1 << (s % 64));
        }
    }

    fn contains(&self, s: Slot) -> bool {
        self.0
            .get((s / 64) as usize)
            .is_some_and(|w| w & (1 << (s % 64)) != 0)
    }

    fn add(&mut self, other: &Slots) {
        if self.0.len() < other.0.len() {
            self.0.resize(other.0.len(), 0);
        }
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            *a |= b;
        }
    }

    fn iter(&self) -> impl Iterator<Item = Slot> + '_ {
        self.0.iter().enumerate().flat_map(|(i, w)| {
            (0..64)
                .filter(move |b| w & (1 << b) != 0)
                .map(move |b| u32::try_from(i * 64 + b).expect("slots fit"))
        })
    }
}

/// The slots each expression in `e` reads, by its address: computed once
/// per body, bottom up, so that asking at every level of a deeply nested
/// expression (a long list literal) stays linear.
type Uses = HashMap<*const Expr, Slots>;

fn fill(e: &Expr, cache: &mut Uses) -> Slots {
    let mut out = Slots::default();
    let mut add = |x: &Expr, cache: &mut Uses| out.add(&fill(x, cache));
    match e {
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => {}
        Expr::Call(_, args)
        | Expr::Prim(_, args)
        | Expr::PartialApp(_, args)
        | Expr::Closure(_, args)
        | Expr::Ctor(_, _, args) => args.iter().for_each(|a| add(a, cache)),
        Expr::Apply(f, args) => {
            add(f, cache);
            args.iter().for_each(|a| add(a, cache));
        }
        Expr::Let(_, value, body) => {
            add(value, cache);
            add(body, cache);
        }
        Expr::Match(scrutinee, _, arms) => {
            add(scrutinee, cache);
            arms.iter().for_each(|arm| add(&arm.body, cache));
        }
        Expr::NumSwitch(scrutinee, arms, default) => {
            add(scrutinee, cache);
            arms.iter().for_each(|(_, body)| add(body, cache));
            add(default, cache);
        }
        Expr::If(cond, then, otherwise) => {
            add(cond, cache);
            add(then, cache);
            add(otherwise, cache);
        }
    }
    if let Expr::Local(s) = e {
        out.insert(*s);
    }
    cache.insert(e as *const Expr, out.clone());
    out
}

/// How many constructors with `n` fields `e` builds on one path at most:
/// how many reuse tokens of that size it could use.
fn builds(e: &Expr, n: usize) -> usize {
    let all = |es: &[Expr]| es.iter().map(|a| builds(a, n)).sum::<usize>();
    match e {
        Expr::Ctor(_, _, args) => usize::from(args.len() == n) + all(args),
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => 0,
        Expr::Call(_, args)
        | Expr::Prim(_, args)
        | Expr::PartialApp(_, args)
        | Expr::Closure(_, args) => all(args),
        Expr::Apply(f, args) => builds(f, n) + all(args),
        Expr::Let(_, value, body) => builds(value, n) + builds(body, n),
        Expr::Match(_, _, arms) => arms
            .iter()
            .map(|arm| builds(&arm.body, n))
            .max()
            .unwrap_or(0),
        Expr::NumSwitch(_, arms, default) => arms
            .iter()
            .map(|(_, body)| builds(body, n))
            .max()
            .unwrap_or(0)
            .max(builds(default, n)),
        Expr::If(cond, then, otherwise) => {
            builds(cond, n) + builds(then, n).max(builds(otherwise, n))
        }
    }
}

// ---------------------------------------------------------------- compiler

struct Compiler<'a> {
    program: &'a Program,
    pool: &'a mut Vec<Value>,
    code: Code,
    /// The next free temporary.
    next: Reg,
    /// The first temporary: registers below are the IR's slots.
    first_temp: Reg,
    /// The slots bound in the current scope.
    bound: Slots,
    /// Slots known to hold a constructor with this many fields (from an
    /// enclosing match), innermost last.
    known: Vec<(Slot, usize)>,
    /// Registers that may hold a reuse token for a constructor with this
    /// many fields, innermost last.
    tokens: Vec<(usize, Reg)>,
    /// The slots each expression of the body reads.
    cache: Uses,
}

impl<'a> Compiler<'a> {
    fn body(
        program: &'a Program,
        pool: &'a mut Vec<Value>,
        params: u32,
        frame: u32,
        expr: &Expr,
    ) -> Code {
        let mut bound = Slots::default();
        for p in 0..params {
            bound.insert(p);
        }
        let mut cx = Compiler {
            program,
            pool,
            code: Code {
                instrs: Vec::new(),
                ops: Vec::new(),
                tables: Vec::new(),
                num_tables: Vec::new(),
                regs: frame,
                params,
            },
            next: frame,
            first_temp: frame,
            bound,
            known: Vec::new(),
            tokens: Vec::new(),
            cache: HashMap::new(),
        };
        fill(expr, &mut cx.cache);
        let dst = cx.temp();
        cx.expr(expr, dst, true, &Slots::default());
        cx.code
    }

    /// Adds the slots `e` reads to `out`.
    fn uses(&self, e: &Expr, out: &mut Slots) {
        out.add(&self.cache[&(e as *const Expr)]);
    }

    fn uses_of(&self, e: &Expr) -> Slots {
        self.cache[&(e as *const Expr)].clone()
    }

    fn temp(&mut self) -> Reg {
        let r = self.next;
        self.next += 1;
        self.code.regs = self.code.regs.max(self.next);
        r
    }

    fn emit(&mut self, instr: Instr) -> usize {
        self.code.instrs.push(instr);
        self.code.instrs.len() - 1
    }

    fn here(&self) -> u32 {
        u32::try_from(self.code.instrs.len()).expect("code fits")
    }

    fn constant(&mut self, v: Value) -> u32 {
        self.pool.push(v);
        u32::try_from(self.pool.len() - 1).expect("pool fits")
    }

    fn push_ops(&mut self, regs: impl IntoIterator<Item = Reg>) -> Ops {
        let start = u32::try_from(self.code.ops.len()).expect("ops fit");
        self.code.ops.extend(regs);
        let len = u32::try_from(self.code.ops.len()).expect("ops fit") - start;
        Ops { start, len }
    }

    /// The register holding `e`'s value: a slot that `e` reads, or a new
    /// temporary that it's computed into. `live` is what's read after it.
    fn operand(&mut self, e: &Expr, live: &Slots) -> Reg {
        if let Expr::Local(s) = e {
            return *s;
        }
        let t = self.temp();
        self.expr(e, t, false, live);
        t
    }

    /// The registers holding the values of `es`, computed in order, for an
    /// instruction that reads them all at once; `live` is what's read after
    /// that instruction. With `moves`, each register read for the last time
    /// is marked [`MOVE`].
    fn operands(&mut self, es: &[&Expr], live: &Slots, moves: bool) -> Vec<Reg> {
        // after[j]: what's read after es[j] is computed (the instruction
        // reads the slots of the `Local` operands before it, too).
        let mut after = vec![live.clone(); es.len()];
        for j in (0..es.len().saturating_sub(1)).rev() {
            let mut a = after[j + 1].clone();
            self.uses(es[j + 1], &mut a);
            after[j] = a;
        }
        let mut locals = Slots::default();
        let mut regs = Vec::with_capacity(es.len());
        for (j, e) in es.iter().enumerate() {
            if let Expr::Local(s) = e {
                regs.push(*s);
                locals.insert(*s);
                continue;
            }
            let mut l = std::mem::take(&mut after[j]);
            l.add(&locals);
            let t = self.temp();
            self.expr(e, t, false, &l);
            regs.push(t);
        }
        if moves {
            for j in 0..regs.len() {
                let r = regs[j];
                let last = !regs[j + 1..].contains(&r);
                let dead = r >= self.first_temp || !live.contains(r);
                if last && dead {
                    regs[j] |= MOVE;
                }
            }
        }
        regs
    }

    fn operand_ops(&mut self, es: &[Expr], live: &Slots, moves: bool) -> Ops {
        let es: Vec<&Expr> = es.iter().collect();
        let regs = self.operands(&es, live, moves);
        self.push_ops(regs)
    }

    /// Writes `dst`, then returns it if `tail`.
    fn simple(&mut self, instr: Instr, dst: Reg, tail: bool) {
        self.emit(instr);
        if tail {
            self.emit(Instr::Return { src: dst });
        }
    }

    /// Compiles `e`: its value goes to `dst`; or, in tail position, the
    /// code returns it (or tail-calls what computes it) and never falls
    /// through. `live` is the slots read after `e`.
    fn expr(&mut self, e: &Expr, dst: Reg, tail: bool, live: &Slots) {
        // Temporaries used for this expression's operands are free again
        // once it's computed.
        let mark = self.next;
        match e {
            Expr::Local(s) => {
                if tail {
                    self.emit(Instr::Return { src: *s });
                } else if *s != dst {
                    if live.contains(*s) {
                        self.emit(Instr::Move { dst, src: *s });
                    } else {
                        self.emit(Instr::Take { dst, src: *s });
                    }
                }
            }
            Expr::Captured(i) => self.simple(Instr::Captured { dst, i: *i }, dst, tail),
            Expr::Global(g) => self.simple(Instr::Global { dst, g: g.0 }, dst, tail),
            Expr::Erased => self.simple(Instr::Const { dst, k: ERASED }, dst, tail),
            Expr::DoneK => self.simple(Instr::Const { dst, k: DONE_K }, dst, tail),
            Expr::Lit(lit) => {
                let v = match lit {
                    Lit::Nat(n) => Value::nat(n.clone()),
                    Lit::Int(n) => Value::int(n.clone()),
                    Lit::Text(t) => Value::Text(t.clone()),
                    Lit::Chars(t) => crate::prims::chars(&self.program.shapes, t),
                    Lit::Float(bits) => Value::float(f64::from_bits(*bits)),
                };
                let k = self.constant(v);
                self.simple(Instr::Const { dst, k }, dst, tail);
            }
            Expr::Call(g, args) => {
                let args = self.operand_ops(args, live, true);
                if tail {
                    self.emit(Instr::TailCall { g: g.0, args });
                } else {
                    self.emit(Instr::Call { dst, g: g.0, args });
                }
            }
            // The effect runtime's natives call functions: in tail position
            // the call replaces the frame, as a tail call does.
            Expr::Prim(op @ PrimOp::Effect(_), args) => {
                let args = self.operand_ops(args, live, true);
                if tail {
                    self.emit(Instr::TailPrim { op: *op, args });
                } else {
                    self.emit(Instr::Prim { dst, op: *op, args });
                }
            }
            Expr::Prim(op, args) => {
                let args = self.operand_ops(args, live, false);
                self.simple(Instr::Prim { dst, op: *op, args }, dst, tail);
            }
            Expr::PartialApp(g, args) => {
                let args = self.operand_ops(args, live, true);
                self.simple(Instr::Pap { dst, g: g.0, args }, dst, tail);
            }
            Expr::Apply(f, args) => {
                let mut es: Vec<&Expr> = vec![f];
                es.extend(args.iter());
                let regs = self.operands(&es, live, true);
                let f = regs[0];
                let args = self.push_ops(regs[1..].iter().copied());
                if tail {
                    self.emit(Instr::TailApply { f, args });
                } else {
                    self.emit(Instr::Apply { dst, f, args });
                }
            }
            Expr::Closure(l, captures) => {
                let args = self.operand_ops(captures, live, true);
                self.simple(
                    Instr::Closure {
                        dst,
                        lambda: l.0,
                        args,
                    },
                    dst,
                    tail,
                );
            }
            Expr::Ctor(_, c, fields) => {
                if fields.is_empty() {
                    let k = self.constant(Value::Tag(*c));
                    self.simple(Instr::Const { dst, k }, dst, tail);
                } else {
                    let args = self.operand_ops(fields, live, true);
                    let n = fields.len();
                    let claimed = self.tokens.iter().rposition(|(m, _)| *m == n);
                    let instr = match claimed.map(|i| self.tokens.remove(i)) {
                        Some((_, token)) => Instr::CtorReuse {
                            dst,
                            tag: *c,
                            args,
                            token,
                        },
                        None => Instr::Ctor { dst, tag: *c, args },
                    };
                    self.simple(instr, dst, tail);
                }
            }
            Expr::Let(slot, value, body) => {
                let mut l = live.clone();
                self.uses(body, &mut l);
                self.expr(value, *slot, false, &l);
                self.bound.insert(*slot);
                self.expr(body, dst, tail, live);
                self.bound.remove(*slot);
            }
            Expr::If(cond, then, otherwise) => {
                let mut inside = self.uses_of(then);
                self.uses(otherwise, &mut inside);
                let mut l = live.clone();
                l.add(&inside);
                let jump = match &**cond {
                    Expr::Prim(op, args) if is_test(*op) => {
                        let args = self.operand_ops(args, &l, false);
                        self.emit(Instr::Test {
                            op: *op,
                            args,
                            target: 0,
                        })
                    }
                    _ => {
                        let cond_reg = self.operand(cond, &l);
                        self.emit(Instr::JumpIfFalse {
                            cond: cond_reg,
                            target: 0,
                        })
                    }
                };
                self.uses(cond, &mut inside);
                self.branch(then, &inside, live, &[], dst, tail);
                let end = (!tail).then(|| self.emit(Instr::Jump { target: 0 }));
                let here = self.here();
                self.patch(jump, here);
                self.branch(otherwise, &inside, live, &[], dst, tail);
                if let Some(end) = end {
                    let here = self.here();
                    self.patch(end, here);
                }
            }
            Expr::Match(scrutinee, kind, arms) => {
                let mut inside = Slots::default();
                for arm in arms {
                    self.uses(&arm.body, &mut inside);
                }
                let mut l = live.clone();
                l.add(&inside);
                let src = self.operand(scrutinee, &l);
                self.uses(scrutinee, &mut inside);
                let mut ends = Vec::new();
                match kind {
                    MatchKind::Data(t) => {
                        let ty = &self.program.types[t.0 as usize];
                        let single = ty.ctors.len() == 1;
                        let switch = (!single).then(|| {
                            let table = u32::try_from(self.code.tables.len()).expect("fits");
                            self.code
                                .tables
                                .push(vec![0; arms.len()].into_boxed_slice());
                            self.emit(Instr::Switch { src, table });
                            table
                        });
                        for arm in arms {
                            if let Some(table) = switch {
                                let here = self.here();
                                self.code.tables[table as usize][arm.ctor as usize] = here;
                            }
                            let arity = self.program.types[t.0 as usize].ctors[arm.ctor as usize]
                                .fields
                                .len();
                            let arm_uses = self.uses_of(&arm.body);
                            let dead = src >= self.first_temp
                                || (!arm_uses.contains(src) && !live.contains(src));
                            let tokens = self.tokens.clone();
                            let known = self.known.len();
                            if dead && arity > 0 {
                                let token = if builds(&arm.body, arity) > 0 {
                                    let token = self.temp();
                                    self.tokens.push((arity, token));
                                    token
                                } else {
                                    NO_REG
                                };
                                let fields =
                                    self.push_ops(arm.fields.iter().flat_map(|(i, s)| [*i, *s]));
                                self.emit(Instr::Unpack { src, fields, token });
                            } else {
                                for (i, slot) in &arm.fields {
                                    self.emit(Instr::Field {
                                        dst: *slot,
                                        src,
                                        i: *i,
                                    });
                                }
                                if dead {
                                    self.emit(Instr::Drop { reg: src });
                                } else if arity > 0 && src < self.first_temp {
                                    self.known.push((src, arity));
                                }
                            }
                            let fields: Vec<Slot> = arm.fields.iter().map(|(_, s)| *s).collect();
                            // A scrutinee taken apart is gone: nothing drops it again.
                            let gone = dead && self.bound.contains(src);
                            if gone {
                                self.bound.remove(src);
                            }
                            self.branch(&arm.body, &inside, live, &fields, dst, tail);
                            if gone {
                                self.bound.insert(src);
                            }
                            if !tail {
                                ends.push(self.emit(Instr::Jump { target: 0 }));
                            }
                            self.tokens = tokens;
                            self.known.truncate(known);
                        }
                    }
                    MatchKind::Nat => {
                        let case = self.emit(Instr::NatCase { src, zero: 0 });
                        let fields: Vec<Slot> = arms[1].fields.iter().map(|(_, s)| *s).collect();
                        if let Some(slot) = fields.first() {
                            self.emit(Instr::NatPred { dst: *slot, src });
                        }
                        self.arm(&arms[1].body, &inside, live, &fields, dst, tail, &mut ends);
                        let here = self.here();
                        self.patch(case, here);
                        self.arm(&arms[0].body, &inside, live, &[], dst, tail, &mut ends);
                    }
                    MatchKind::Int => {
                        let case = self.emit(Instr::IntCase { src, neg: 0 });
                        let fields: Vec<Slot> = arms[0].fields.iter().map(|(_, s)| *s).collect();
                        if let Some(slot) = fields.first() {
                            self.emit(Instr::IntOfNat { dst: *slot, src });
                        }
                        self.arm(&arms[0].body, &inside, live, &fields, dst, tail, &mut ends);
                        let here = self.here();
                        self.patch(case, here);
                        let fields: Vec<Slot> = arms[1].fields.iter().map(|(_, s)| *s).collect();
                        if let Some(slot) = fields.first() {
                            self.emit(Instr::IntNegSucc { dst: *slot, src });
                        }
                        self.arm(&arms[1].body, &inside, live, &fields, dst, tail, &mut ends);
                    }
                    MatchKind::Text => {
                        let fields: Vec<Slot> = arms[0].fields.iter().map(|(_, s)| *s).collect();
                        if let Some(slot) = fields.first() {
                            self.emit(Instr::TextChars { dst: *slot, src });
                        }
                        self.arm(&arms[0].body, &inside, live, &fields, dst, tail, &mut ends);
                    }
                }
                let here = self.here();
                for end in ends {
                    self.patch(end, here);
                }
            }
            Expr::NumSwitch(scrutinee, arms, default) => {
                let mut inside = Slots::default();
                for (_, body) in arms {
                    self.uses(body, &mut inside);
                }
                self.uses(default, &mut inside);
                let mut l = live.clone();
                l.add(&inside);
                let src = self.operand(scrutinee, &l);
                self.uses(scrutinee, &mut inside);
                let table = u32::try_from(self.code.num_tables.len()).expect("fits");
                self.code.num_tables.push(NumTable {
                    small: Vec::new(),
                    big: Vec::new(),
                    default: 0,
                });
                self.emit(Instr::NumSwitch { src, table });
                let mut ends = Vec::new();
                for (n, body) in arms {
                    let here = self.here();
                    let t = &mut self.code.num_tables[table as usize];
                    match u64::try_from(n) {
                        Ok(small) => t.small.push((small, here)),
                        Err(_) => t.big.push((n.clone(), here)),
                    }
                    self.arm(body, &inside, live, &[], dst, tail, &mut ends);
                }
                let here = self.here();
                self.code.num_tables[table as usize].default = here;
                self.arm(default, &inside, live, &[], dst, tail, &mut ends);
                let here = self.here();
                for end in ends {
                    self.patch(end, here);
                }
            }
            Expr::Unreachable => {
                self.emit(Instr::Unreachable);
            }
        }
        self.next = mark;
    }

    /// One arm of a branch: unless it's in tail position, it jumps to the
    /// end afterwards (patched later).
    #[allow(clippy::too_many_arguments)]
    fn arm(
        &mut self,
        body: &Expr,
        inside: &Slots,
        live: &Slots,
        fields: &[Slot],
        dst: Reg,
        tail: bool,
        ends: &mut Vec<usize>,
    ) {
        self.branch(body, inside, live, fields, dst, tail);
        if !tail {
            ends.push(self.emit(Instr::Jump { target: 0 }));
        }
    }

    /// A branch's body, with the slots `fields` bound for it. First the
    /// variables that the branching construct reads (`inside`) but this
    /// branch and what follows (`live`) don't are dropped, or kept as reuse
    /// tokens if they're constructors of a size the branch builds.
    fn branch(
        &mut self,
        body: &Expr,
        inside: &Slots,
        live: &Slots,
        fields: &[Slot],
        dst: Reg,
        tail: bool,
    ) {
        let needed = {
            let mut n = self.uses_of(body);
            n.add(live);
            n
        };
        let tokens = self.tokens.clone();
        let dead: Vec<Slot> = inside
            .iter()
            .filter(|s| self.bound.contains(*s) && !needed.contains(*s))
            .collect();
        for s in dead {
            let size = self
                .known
                .iter()
                .rev()
                .find(|(k, _)| *k == s)
                .map(|(_, n)| *n);
            match size {
                Some(n)
                    if self.tokens.iter().filter(|(m, _)| *m == n).count() < builds(body, n) =>
                {
                    let token = self.temp();
                    self.emit(Instr::DropReuse { src: s, token });
                    self.tokens.push((n, token));
                }
                _ => {
                    self.emit(Instr::Drop { reg: s });
                }
            }
        }
        for s in fields {
            self.bound.insert(*s);
        }
        self.expr(body, dst, tail, live);
        for s in fields {
            self.bound.remove(*s);
        }
        self.tokens = tokens;
    }

    fn patch(&mut self, at: usize, target: u32) {
        match &mut self.code.instrs[at] {
            Instr::JumpIfFalse { target: t, .. }
            | Instr::Test { target: t, .. }
            | Instr::Jump { target: t } => *t = target,
            Instr::NatCase { zero, .. } => *zero = target,
            Instr::IntCase { neg, .. } => *neg = target,
            other => unreachable!("patching {other:?}"),
        }
    }
}
