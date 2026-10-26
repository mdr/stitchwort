//! A byte encoding of the lowered program (docs/proposals/
//! standalone-executables.md, stage S1): what `stitchwort build` embeds in
//! an executable and the runtime library reads back. It is the check
//! cache's style (`stitchwort_elab::cache::codec`): LEB128 integers and
//! length-prefixed strings, with a tag byte per variant of every `ir` type.
//! The bytecode image isn't written: the reader rebuilds it with
//! [`crate::code::compile`].
//!
//! **Layout.** `SWRT`, the format version, the crate version and the build
//! hash (a hash of this crate's sources, from `build.rs`), each of which a
//! reader must find equal to its own; then the [`Limits`], the
//! [`MainRow`], the [`Shapes`], the types, the globals, the lambdas and the
//! entry body.
//!
//! **Reading is total.** Any bytes either decode to a program that
//! [`Program::validate`] accepts or give an error: counts are checked against
//! the bytes left before anything is allocated, nesting is limited, and ids
//! are checked against the tables.

use num_bigint::{BigInt, Sign};
use stitchwort_core::{DataId, DefId};

use crate::ir::{
    Arm, Body, CtorInfo, Expr, Global, GlobalId, GlobalKind, Lambda, LambdaId, Lit, MainRow,
    MatchKind, Program, TypeId, TypeInfo,
};
use crate::shared::Limits;
pub use crate::wire::CodecError;
use crate::wire::{BUILD_HASH, Read, Reader, Writer, bad, read_shapes, write_shapes};

const MAGIC: &[u8; 4] = b"SWRT";

/// Bumped when the layout changes.
pub const FORMAT_VERSION: u8 = 1;

/// How deeply an expression may nest when read, so that a corrupt program
/// can't overflow the stack. Lowered code nests far less (`Rogue.main`'s
/// deepest expression is a small fraction of this).
const MAX_DEPTH: usize = 2_000;

/// The largest frame a body may claim when read: the checker allocates one
/// flag per slot.
const MAX_FRAME: u32 = 1 << 20;

// ------------------------------------------------------------------ writing

impl Writer {
    fn lit(&mut self, lit: &Lit) {
        match lit {
            Lit::Nat(n) => {
                self.u8(0);
                self.big(n);
            }
            Lit::Int(n) => {
                self.u8(1);
                let (sign, magnitude) = n.clone().into_parts();
                self.u8(match sign {
                    Sign::Minus => 0,
                    Sign::NoSign => 1,
                    Sign::Plus => 2,
                });
                self.big(&magnitude);
            }
            Lit::Text(s) => {
                self.u8(2);
                self.str(s);
            }
            Lit::Chars(s) => {
                self.u8(3);
                self.str(s);
            }
            Lit::Float(bits) => {
                self.u8(4);
                self.uint(*bits);
            }
        }
    }

    fn exprs(&mut self, exprs: &[Expr]) {
        self.usize(exprs.len());
        for e in exprs {
            self.expr(e);
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Local(slot) => {
                self.u8(0);
                self.uint(u64::from(*slot));
            }
            Expr::Captured(i) => {
                self.u8(1);
                self.uint(u64::from(*i));
            }
            Expr::Global(g) => {
                self.u8(2);
                self.uint(u64::from(g.0));
            }
            Expr::Erased => self.u8(3),
            Expr::Lit(lit) => {
                self.u8(4);
                self.lit(lit);
            }
            Expr::DoneK => self.u8(5),
            Expr::Call(g, args) => {
                self.u8(6);
                self.uint(u64::from(g.0));
                self.exprs(args);
            }
            Expr::Prim(op, args) => {
                self.u8(7);
                self.prim(*op);
                self.exprs(args);
            }
            Expr::PartialApp(g, args) => {
                self.u8(8);
                self.uint(u64::from(g.0));
                self.exprs(args);
            }
            Expr::Apply(f, args) => {
                self.u8(9);
                self.expr(f);
                self.exprs(args);
            }
            Expr::Closure(id, captures) => {
                self.u8(10);
                self.uint(u64::from(id.0));
                self.exprs(captures);
            }
            Expr::Ctor(t, ctor, fields) => {
                self.u8(11);
                self.uint(u64::from(t.0));
                self.uint(u64::from(*ctor));
                self.exprs(fields);
            }
            Expr::Let(slot, value, body) => {
                self.u8(12);
                self.uint(u64::from(*slot));
                self.expr(value);
                self.expr(body);
            }
            Expr::Match(scrutinee, kind, arms) => {
                self.u8(13);
                self.expr(scrutinee);
                match kind {
                    MatchKind::Data(t) => {
                        self.u8(0);
                        self.uint(u64::from(t.0));
                    }
                    MatchKind::Nat => self.u8(1),
                    MatchKind::Int => self.u8(2),
                    MatchKind::Text => self.u8(3),
                }
                self.usize(arms.len());
                for arm in arms {
                    self.uint(u64::from(arm.ctor));
                    self.usize(arm.fields.len());
                    for (field, slot) in &arm.fields {
                        self.uint(u64::from(*field));
                        self.uint(u64::from(*slot));
                    }
                    self.expr(&arm.body);
                }
            }
            Expr::NumSwitch(scrutinee, arms, default) => {
                self.u8(14);
                self.expr(scrutinee);
                self.usize(arms.len());
                for (n, body) in arms {
                    self.big(n);
                    self.expr(body);
                }
                self.expr(default);
            }
            Expr::If(cond, then, otherwise) => {
                self.u8(15);
                self.expr(cond);
                self.expr(then);
                self.expr(otherwise);
            }
            Expr::Unreachable => self.u8(16),
        }
    }

    fn body(&mut self, body: &Body) {
        self.uint(u64::from(body.frame));
        self.expr(&body.expr);
    }
}

/// The program and the limits it runs under, as bytes.
pub fn encode(program: &Program, limits: &Limits) -> Vec<u8> {
    let mut w = Writer::default();
    w.bytes.extend_from_slice(MAGIC);
    w.u8(FORMAT_VERSION);
    w.str(env!("CARGO_PKG_VERSION"));
    w.uint(BUILD_HASH);
    w.uint(limits.steps);
    w.usize(limits.frames);
    w.u8(match program.main_row {
        MainRow::Io => 0,
        MainRow::FailIo => 1,
    });
    write_shapes(&mut w, &program.shapes);
    w.usize(program.types.len());
    for info in &program.types {
        w.usize(info.data.0);
        w.str(&info.name);
        w.u8(u8::from(info.record));
        w.usize(info.ctors.len());
        for ctor in &info.ctors {
            w.str(&ctor.name);
            w.usize(ctor.fields.len());
            for field in &ctor.fields {
                w.str(field);
            }
        }
    }
    w.usize(program.globals.len());
    for global in &program.globals {
        w.str(&global.name);
        w.usize(global.def.0);
        match &global.kind {
            GlobalKind::Function { params, body } => {
                w.u8(0);
                w.uint(u64::from(*params));
                w.body(body);
            }
            GlobalKind::Constant { body } => {
                w.u8(1);
                w.body(body);
            }
            GlobalKind::Native(op) => {
                w.u8(2);
                w.prim(*op);
            }
        }
    }
    w.usize(program.lambdas.len());
    for lambda in &program.lambdas {
        w.uint(u64::from(lambda.params));
        w.uint(u64::from(lambda.captures));
        w.body(&lambda.body);
    }
    w.body(&program.entry);
    w.bytes
}

// ------------------------------------------------------------------ reading

impl<'a> Reader<'a> {
    fn lit(&mut self) -> Read<Lit> {
        Ok(match self.u8()? {
            0 => Lit::Nat(self.big()?),
            1 => {
                let sign = match self.u8()? {
                    0 => Sign::Minus,
                    1 => Sign::NoSign,
                    2 => Sign::Plus,
                    t => return bad(format!("no sign tagged {t}")),
                };
                let magnitude = self.big()?;
                // `from_biguint` makes a zero of any sign `NoSign`; refuse
                // the spellings that aren't what `encode` writes.
                let n = BigInt::from_biguint(sign, magnitude);
                if n.sign() != sign {
                    return bad("an integer whose sign doesn't match its size");
                }
                Lit::Int(n)
            }
            2 => Lit::Text(self.str()?),
            3 => Lit::Chars(self.str()?),
            4 => Lit::Float(self.uint()?),
            t => return bad(format!("no literal tagged {t}")),
        })
    }

    fn exprs(&mut self) -> Read<Vec<Expr>> {
        let n = self.count()?;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(self.expr()?);
        }
        Ok(out)
    }

    fn expr(&mut self) -> Read<Expr> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            return bad("expressions nested too deeply");
        }
        let expr = self.expr_inner();
        self.depth -= 1;
        expr
    }

    fn expr_inner(&mut self) -> Read<Expr> {
        Ok(match self.u8()? {
            0 => Expr::Local(self.u32()?),
            1 => Expr::Captured(self.u32()?),
            2 => Expr::Global(GlobalId(self.u32()?)),
            3 => Expr::Erased,
            4 => Expr::Lit(self.lit()?),
            5 => Expr::DoneK,
            6 => {
                let g = GlobalId(self.u32()?);
                Expr::Call(g, self.exprs()?)
            }
            7 => {
                let op = self.prim()?;
                Expr::Prim(op, self.exprs()?)
            }
            8 => {
                let g = GlobalId(self.u32()?);
                Expr::PartialApp(g, self.exprs()?)
            }
            9 => {
                let f = Box::new(self.expr()?);
                Expr::Apply(f, self.exprs()?)
            }
            10 => {
                let id = LambdaId(self.u32()?);
                Expr::Closure(id, self.exprs()?)
            }
            11 => {
                let t = TypeId(self.u32()?);
                let ctor = self.u32()?;
                Expr::Ctor(t, ctor, self.exprs()?)
            }
            12 => {
                let slot = self.u32()?;
                let value = Box::new(self.expr()?);
                Expr::Let(slot, value, Box::new(self.expr()?))
            }
            13 => {
                let scrutinee = Box::new(self.expr()?);
                let kind = match self.u8()? {
                    0 => MatchKind::Data(TypeId(self.u32()?)),
                    1 => MatchKind::Nat,
                    2 => MatchKind::Int,
                    3 => MatchKind::Text,
                    t => return bad(format!("no match kind tagged {t}")),
                };
                let n = self.count()?;
                let mut arms = Vec::with_capacity(n);
                for _ in 0..n {
                    let ctor = self.u32()?;
                    let m = self.count()?;
                    let mut fields = Vec::with_capacity(m);
                    for _ in 0..m {
                        fields.push((self.u32()?, self.u32()?));
                    }
                    arms.push(Arm {
                        ctor,
                        fields,
                        body: self.expr()?,
                    });
                }
                Expr::Match(scrutinee, kind, arms)
            }
            14 => {
                let scrutinee = Box::new(self.expr()?);
                let n = self.count()?;
                let mut arms = Vec::with_capacity(n);
                for _ in 0..n {
                    let number = self.big()?;
                    arms.push((number, self.expr()?));
                }
                Expr::NumSwitch(scrutinee, arms, Box::new(self.expr()?))
            }
            15 => {
                let cond = Box::new(self.expr()?);
                let then = Box::new(self.expr()?);
                Expr::If(cond, then, Box::new(self.expr()?))
            }
            16 => Expr::Unreachable,
            t => return bad(format!("no expression tagged {t}")),
        })
    }

    fn body(&mut self) -> Read<Body> {
        let frame = self.u32()?;
        if frame > MAX_FRAME {
            return bad("a frame too large");
        }
        Ok(Body {
            frame,
            expr: self.expr()?,
        })
    }
}

/// Reads what [`encode`] wrote. An error if the bytes aren't a program of
/// this format, version and build, or aren't well formed.
pub fn decode(bytes: &[u8]) -> Result<(Program, Limits), CodecError> {
    let mut r = Reader {
        bytes,
        at: 0,
        depth: 0,
    };
    if r.raw(MAGIC.len())? != MAGIC {
        return bad("not a Stitchwort program");
    }
    let format = r.u8()?;
    if format != FORMAT_VERSION {
        return bad(format!("format version {format}, not {FORMAT_VERSION}"));
    }
    let version = r.str()?;
    if *version != *env!("CARGO_PKG_VERSION") {
        return bad(format!(
            "written by version {version}, not {}",
            env!("CARGO_PKG_VERSION")
        ));
    }
    if r.uint()? != BUILD_HASH {
        return bad("written by a different build of the runtime");
    }
    let limits = Limits {
        steps: r.uint()?,
        frames: r.usize()?,
    };
    let main_row = match r.u8()? {
        0 => MainRow::Io,
        1 => MainRow::FailIo,
        t => return bad(format!("no main row tagged {t}")),
    };
    let shapes = read_shapes(&mut r)?;
    let n = r.count()?;
    let mut types = Vec::with_capacity(n);
    for _ in 0..n {
        let data = DataId(r.usize()?);
        let name = r.str()?;
        let record = r.flag()?;
        let m = r.count()?;
        let mut ctors = Vec::with_capacity(m);
        for _ in 0..m {
            let name = r.str()?;
            let k = r.count()?;
            let mut fields = Vec::with_capacity(k);
            for _ in 0..k {
                fields.push(r.str()?);
            }
            ctors.push(CtorInfo { name, fields });
        }
        types.push(TypeInfo {
            data,
            name,
            record,
            ctors,
        });
    }
    let n = r.count()?;
    let mut globals = Vec::with_capacity(n);
    for _ in 0..n {
        let name = r.str()?;
        let def = DefId(r.usize()?);
        let kind = match r.u8()? {
            0 => {
                let params = r.u32()?;
                GlobalKind::Function {
                    params,
                    body: r.body()?,
                }
            }
            1 => GlobalKind::Constant { body: r.body()? },
            2 => GlobalKind::Native(r.prim()?),
            t => return bad(format!("no global tagged {t}")),
        };
        globals.push(Global { name, def, kind });
    }
    let n = r.count()?;
    let mut lambdas = Vec::with_capacity(n);
    for _ in 0..n {
        let params = r.u32()?;
        let captures = r.u32()?;
        lambdas.push(Lambda {
            params,
            captures,
            body: r.body()?,
        });
    }
    let entry = r.body()?;
    if r.at != bytes.len() {
        return bad("bytes after the program");
    }
    let program = Program {
        globals,
        lambdas,
        types,
        entry,
        main_row,
        shapes,
    };
    check_types(&program)?;
    program
        .validate()
        .map_err(|e| CodecError(format!("the program isn't well formed: {e}")))?;
    Ok((program, limits))
}

/// Every type id in the program names a type, which [`Program::validate`]
/// takes for granted.
fn check_types(program: &Program) -> Read<()> {
    fn walk(expr: &Expr, types: usize) -> Read<()> {
        let check = |t: &TypeId| {
            if (t.0 as usize) < types {
                Ok(())
            } else {
                bad(format!("no type {}", t.0))
            }
        };
        match expr {
            Expr::Ctor(t, _, args) => {
                check(t)?;
                args.iter().try_for_each(|e| walk(e, types))
            }
            Expr::Match(scrutinee, kind, arms) => {
                if let MatchKind::Data(t) = kind {
                    check(t)?;
                }
                walk(scrutinee, types)?;
                arms.iter().try_for_each(|a| walk(&a.body, types))
            }
            Expr::Call(_, args)
            | Expr::Prim(_, args)
            | Expr::PartialApp(_, args)
            | Expr::Closure(_, args) => args.iter().try_for_each(|e| walk(e, types)),
            Expr::Apply(f, args) => {
                walk(f, types)?;
                args.iter().try_for_each(|e| walk(e, types))
            }
            Expr::Let(_, value, body) => {
                walk(value, types)?;
                walk(body, types)
            }
            Expr::NumSwitch(scrutinee, arms, default) => {
                walk(scrutinee, types)?;
                arms.iter().try_for_each(|(_, e)| walk(e, types))?;
                walk(default, types)
            }
            Expr::If(c, t, e) => {
                walk(c, types)?;
                walk(t, types)?;
                walk(e, types)
            }
            Expr::Local(_)
            | Expr::Captured(_)
            | Expr::Global(_)
            | Expr::Erased
            | Expr::Lit(_)
            | Expr::DoneK
            | Expr::Unreachable => Ok(()),
        }
    }
    let types = program.types.len();
    for global in &program.globals {
        match &global.kind {
            GlobalKind::Function { body, .. } | GlobalKind::Constant { body } => {
                walk(&body.expr, types)?;
            }
            GlobalKind::Native(_) => {}
        }
    }
    for lambda in &program.lambdas {
        walk(&lambda.body.expr, types)?;
    }
    walk(&program.entry.expr, types)
}
