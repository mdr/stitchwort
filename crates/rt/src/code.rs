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

use num_bigint::BigUint;

use crate::ir::{Expr, Lit, MatchKind, PrimOp, Program};
use crate::value::Value;

/// A register: an index into the current frame.
pub type Reg = u32;

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

struct Compiler<'a> {
    program: &'a Program,
    pool: &'a mut Vec<Value>,
    code: Code,
    /// The next free temporary.
    next: Reg,
}

impl<'a> Compiler<'a> {
    fn body(
        program: &'a Program,
        pool: &'a mut Vec<Value>,
        params: u32,
        frame: u32,
        expr: &Expr,
    ) -> Code {
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
        };
        let dst = cx.temp();
        cx.expr(expr, dst, true);
        cx.code
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

    /// The register holding `e`'s value: a slot that `e` reads, or a new
    /// temporary that it's computed into.
    fn operand(&mut self, e: &Expr) -> Reg {
        if let Expr::Local(s) = e {
            return *s;
        }
        let t = self.temp();
        self.expr(e, t, false);
        t
    }

    fn operands(&mut self, es: &[Expr]) -> Ops {
        let regs: Vec<Reg> = es.iter().map(|e| self.operand(e)).collect();
        let start = u32::try_from(self.code.ops.len()).expect("ops fit");
        self.code.ops.extend(regs);
        Ops {
            start,
            len: u32::try_from(es.len()).expect("ops fit"),
        }
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
    /// through.
    fn expr(&mut self, e: &Expr, dst: Reg, tail: bool) {
        // Temporaries used for this expression's operands are free again
        // once it's computed.
        let mark = self.next;
        match e {
            Expr::Local(s) => {
                if tail {
                    self.emit(Instr::Return { src: *s });
                } else if *s != dst {
                    self.emit(Instr::Move { dst, src: *s });
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
                };
                let k = self.constant(v);
                self.simple(Instr::Const { dst, k }, dst, tail);
            }
            Expr::Call(g, args) => {
                let args = self.operands(args);
                if tail {
                    self.emit(Instr::TailCall { g: g.0, args });
                } else {
                    self.emit(Instr::Call { dst, g: g.0, args });
                }
            }
            Expr::Prim(op, args) => {
                let args = self.operands(args);
                self.simple(Instr::Prim { dst, op: *op, args }, dst, tail);
            }
            Expr::PartialApp(g, args) => {
                let args = self.operands(args);
                self.simple(Instr::Pap { dst, g: g.0, args }, dst, tail);
            }
            Expr::Apply(f, args) => {
                let f = self.operand(f);
                let args = self.operands(args);
                if tail {
                    self.emit(Instr::TailApply { f, args });
                } else {
                    self.emit(Instr::Apply { dst, f, args });
                }
            }
            Expr::Closure(l, captures) => {
                let args = self.operands(captures);
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
                    let args = self.operands(fields);
                    self.simple(Instr::Ctor { dst, tag: *c, args }, dst, tail);
                }
            }
            Expr::Let(slot, value, body) => {
                self.expr(value, *slot, false);
                self.expr(body, dst, tail);
            }
            Expr::If(cond, then, otherwise) => {
                let cond = self.operand(cond);
                let jump = self.emit(Instr::JumpIfFalse { cond, target: 0 });
                self.expr(then, dst, tail);
                let end = (!tail).then(|| self.emit(Instr::Jump { target: 0 }));
                let here = self.here();
                self.patch(jump, here);
                self.expr(otherwise, dst, tail);
                if let Some(end) = end {
                    let here = self.here();
                    self.patch(end, here);
                }
            }
            Expr::Match(scrutinee, kind, arms) => {
                let src = self.operand(scrutinee);
                let mut ends = Vec::new();
                match kind {
                    MatchKind::Data(t) => {
                        let single = self.program.types[t.0 as usize].ctors.len() == 1;
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
                            for (i, slot) in &arm.fields {
                                self.emit(Instr::Field {
                                    dst: *slot,
                                    src,
                                    i: *i,
                                });
                            }
                            self.arm(&arm.body, dst, tail, &mut ends);
                        }
                    }
                    MatchKind::Nat => {
                        let case = self.emit(Instr::NatCase { src, zero: 0 });
                        if let Some((_, slot)) = arms[1].fields.first() {
                            self.emit(Instr::NatPred { dst: *slot, src });
                        }
                        self.arm(&arms[1].body, dst, tail, &mut ends);
                        let here = self.here();
                        self.patch(case, here);
                        self.arm(&arms[0].body, dst, tail, &mut ends);
                    }
                    MatchKind::Int => {
                        let case = self.emit(Instr::IntCase { src, neg: 0 });
                        if let Some((_, slot)) = arms[0].fields.first() {
                            self.emit(Instr::IntOfNat { dst: *slot, src });
                        }
                        self.arm(&arms[0].body, dst, tail, &mut ends);
                        let here = self.here();
                        self.patch(case, here);
                        if let Some((_, slot)) = arms[1].fields.first() {
                            self.emit(Instr::IntNegSucc { dst: *slot, src });
                        }
                        self.arm(&arms[1].body, dst, tail, &mut ends);
                    }
                    MatchKind::Text => {
                        if let Some((_, slot)) = arms[0].fields.first() {
                            self.emit(Instr::TextChars { dst: *slot, src });
                        }
                        self.arm(&arms[0].body, dst, tail, &mut ends);
                    }
                }
                let here = self.here();
                for end in ends {
                    self.patch(end, here);
                }
            }
            Expr::NumSwitch(scrutinee, arms, default) => {
                let src = self.operand(scrutinee);
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
                    self.arm(body, dst, tail, &mut ends);
                }
                let here = self.here();
                self.code.num_tables[table as usize].default = here;
                self.arm(default, dst, tail, &mut ends);
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
    fn arm(&mut self, body: &Expr, dst: Reg, tail: bool, ends: &mut Vec<usize>) {
        self.expr(body, dst, tail);
        if !tail {
            ends.push(self.emit(Instr::Jump { target: 0 }));
        }
    }

    fn patch(&mut self, at: usize, target: u32) {
        match &mut self.code.instrs[at] {
            Instr::JumpIfFalse { target: t, .. } | Instr::Jump { target: t } => *t = target,
            Instr::NatCase { zero, .. } => *zero = target,
            Instr::IntCase { neg, .. } => *neg = target,
            other => unreachable!("patching {other:?}"),
        }
    }
}
