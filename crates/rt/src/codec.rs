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

use std::fmt;
use std::rc::Rc;

use num_bigint::{BigInt, BigUint, Sign};
use stitchwort_core::partial::Primitive;
use stitchwort_core::{DataId, DefId, native::Native};

use crate::effect::EffectOp;
use crate::ir::{
    Arm, Body, CtorInfo, Expr, Global, GlobalId, GlobalKind, Lambda, LambdaId, Lit, MainRow,
    MatchKind, PrimOp, Program, Shapes, TypeId, TypeInfo,
};
use crate::machine::Limits;
use crate::natives::{FloatPrim, IntNative, TextNative};

const MAGIC: &[u8; 4] = b"SWRT";

/// Bumped when the layout changes.
pub const FORMAT_VERSION: u8 = 1;

const BUILD_HASH: u64 = parse_hash(env!("SW_RT_BUILD_HASH"));

const fn parse_hash(text: &str) -> u64 {
    let bytes = text.as_bytes();
    let mut n: u64 = 0;
    let mut i = 0;
    while i < bytes.len() {
        n = n.wrapping_mul(10).wrapping_add((bytes[i] - b'0') as u64);
        i += 1;
    }
    n
}

/// How deeply an expression may nest when read, so that a corrupt program
/// can't overflow the stack. Lowered code nests far less (`Rogue.main`'s
/// deepest expression is a small fraction of this).
const MAX_DEPTH: usize = 2_000;

/// The largest frame a body may claim when read: the checker allocates one
/// flag per slot.
const MAX_FRAME: u32 = 1 << 20;

/// Why bytes aren't a program this runtime can run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodecError(pub String);

impl fmt::Display for CodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "can't read the program: {}", self.0)
    }
}

impl std::error::Error for CodecError {}

type Read<T> = Result<T, CodecError>;

fn bad<T>(why: impl Into<String>) -> Read<T> {
    Err(CodecError(why.into()))
}

// ---------------------------------------------------------------- enum tags

/// Gives an enum a tag per variant, in the order listed, and checks that the
/// list is every variant (a new variant is a compile error here).
macro_rules! tags {
    ($name:ident, $ty:ty, [$($variant:path),* $(,)?]) => {
        mod $name {
            use super::*;
            pub const ALL: &[$ty] = &[$($variant),*];
            const _: fn($ty) = |v| match v {
                $($variant => {}),*
            };
            pub fn tag(v: $ty) -> u64 {
                ALL.iter().position(|x| *x == v).expect("listed") as u64
            }
        }
    };
}

tags!(
    nat_tags,
    Native,
    [
        Native::Add,
        Native::Sub,
        Native::Mul,
        Native::Leq,
        Native::EqNat,
        Native::DivFuel,
        Native::DecEqNat,
        Native::EqNatRefl,
        Native::EqNatSound
    ]
);

tags!(
    int_tags,
    IntNative,
    [
        IntNative::NatToInt,
        IntNative::IntNeg,
        IntNative::IntAdd,
        IntNative::IntSub,
        IntNative::IntMul,
        IntNative::IntDiv,
        IntNative::IntMod,
        IntNative::IntTDiv,
        IntNative::IntTMod,
        IntNative::IntFDiv,
        IntNative::IntFMod,
        IntNative::IntModNat,
        IntNative::DecEqInt,
        IntNative::IntLeq,
        IntNative::IntLess,
        IntNative::IntCompare,
        IntNative::IntNatAbs,
        IntNative::IntAbs,
        IntNative::IntToNat,
        IntNative::IntToNatChecked,
        IntNative::IntSign,
        IntNative::IntToText,
        IntNative::TextToInt
    ]
);

tags!(
    text_tags,
    TextNative,
    [
        TextNative::TextToList,
        TextNative::TextFromList,
        TextNative::TextAppend,
        TextNative::TextLength,
        TextNative::TextIsEmpty,
        TextNative::DecEqText,
        TextNative::TextCompare,
        TextNative::TextUncons,
        TextNative::TextFold,
        TextNative::TextTrim,
        TextNative::TextTake,
        TextNative::TextDrop,
        TextNative::TextContains,
        TextNative::TextSplit,
        TextNative::TextJoin,
        TextNative::NatToText,
        TextNative::TextToNat
    ]
);

tags!(
    delay_tags,
    Primitive,
    [
        Primitive::Delay,
        Primitive::Now,
        Primitive::Lift,
        Primitive::BindD,
        Primitive::MapSig,
        Primitive::Pfix,
        Primitive::FoldD
    ]
);

tags!(
    float_tags,
    FloatPrim,
    [
        FloatPrim::Add,
        FloatPrim::Sub,
        FloatPrim::Mul,
        FloatPrim::Div,
        FloatPrim::Rem,
        FloatPrim::Floor,
        FloatPrim::Ceil,
        FloatPrim::Trunc,
        FloatPrim::Round,
        FloatPrim::OfInt,
        FloatPrim::OfNat,
        FloatPrim::ToText,
        FloatPrim::Neg,
        FloatPrim::Abs,
        FloatPrim::IsNaN,
        FloatPrim::IsFinite,
        FloatPrim::DecEq,
        FloatPrim::IeeeEq,
        FloatPrim::IeeeLt,
        FloatPrim::IeeeLe,
        FloatPrim::ToInt,
        FloatPrim::Compare,
        FloatPrim::FromBits,
        FloatPrim::Bits
    ]
);

tags!(
    effect_tags,
    EffectOp,
    [
        EffectOp::Bind,
        EffectOp::Fold,
        EffectOp::FoldLazy,
        EffectOp::FoldIn,
        EffectOp::FoldState,
        EffectOp::FoldStateComp,
        EffectOp::Translate,
        EffectOp::RunPure
    ]
);

/// The shapes' fields, in the order they are written.
macro_rules! shapes {
    ($($field:ident),* $(,)?) => {
        fn write_shapes(w: &mut Writer, s: &Shapes) {
            $(w.uint(u64::from(s.$field));)*
        }
        fn read_shapes(r: &mut Reader) -> Read<Shapes> {
            Ok(Shapes { $($field: r.u32()?),* })
        }
    };
}

shapes!(
    false_,
    true_,
    none,
    some,
    yes,
    no,
    nil,
    cons,
    pair,
    char_,
    unit,
    done,
    call,
    bind_node,
    row_empty,
    left,
    right,
    recur,
    sig_map,
    print,
    read_line,
    read_all,
    console,
    keys_mode,
    read_bytes,
    write,
    random_seed,
    console_record,
    stop,
);

// ------------------------------------------------------------------ writing

#[derive(Default)]
struct Writer {
    bytes: Vec<u8>,
}

impl Writer {
    fn u8(&mut self, b: u8) {
        self.bytes.push(b);
    }

    /// LEB128.
    fn uint(&mut self, mut n: u64) {
        loop {
            let low = (n & 0x7f) as u8;
            n >>= 7;
            if n == 0 {
                self.u8(low);
                return;
            }
            self.u8(low | 0x80);
        }
    }

    fn usize(&mut self, n: usize) {
        self.uint(n as u64);
    }

    fn blob(&mut self, bytes: &[u8]) {
        self.usize(bytes.len());
        self.bytes.extend_from_slice(bytes);
    }

    fn str(&mut self, s: &str) {
        self.blob(s.as_bytes());
    }

    fn big(&mut self, n: &BigUint) {
        self.blob(&n.to_bytes_le());
    }

    fn prim(&mut self, op: PrimOp) {
        match op {
            PrimOp::Nat(op) => {
                self.u8(0);
                self.uint(nat_tags::tag(op));
            }
            PrimOp::Int(op) => {
                self.u8(1);
                self.uint(int_tags::tag(op));
            }
            PrimOp::NegSucc => self.u8(2),
            PrimOp::IntEqual => self.u8(3),
            PrimOp::TextEqual => self.u8(4),
            PrimOp::Text(op) => {
                self.u8(5);
                self.uint(text_tags::tag(op));
            }
            PrimOp::Delay(op) => {
                self.u8(6);
                self.uint(delay_tags::tag(op));
            }
            PrimOp::Float(op) => {
                self.u8(7);
                self.uint(float_tags::tag(op));
            }
            PrimOp::Effect(op) => {
                self.u8(8);
                self.uint(effect_tags::tag(op));
            }
        }
    }

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

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
    depth: usize,
}

impl<'a> Reader<'a> {
    fn u8(&mut self) -> Read<u8> {
        let Some(&b) = self.bytes.get(self.at) else {
            return bad("the bytes end early");
        };
        self.at += 1;
        Ok(b)
    }

    fn uint(&mut self) -> Read<u64> {
        let mut n: u64 = 0;
        let mut shift = 0;
        loop {
            let b = self.u8()?;
            if shift >= 64 || (shift == 63 && b > 1) {
                return bad("a number too large");
            }
            n |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(n);
            }
            shift += 7;
        }
    }

    fn usize(&mut self) -> Read<usize> {
        usize::try_from(self.uint()?).or_else(|_| bad("a number too large"))
    }

    fn u32(&mut self) -> Read<u32> {
        u32::try_from(self.uint()?).or_else(|_| bad("a number too large"))
    }

    /// A count of items that each take at least a byte: refused if more
    /// than the bytes left, so that a corrupt count can't ask for memory.
    fn count(&mut self) -> Read<usize> {
        let n = self.usize()?;
        if n > self.bytes.len() - self.at {
            return bad("a count larger than the bytes left");
        }
        Ok(n)
    }

    fn raw(&mut self, n: usize) -> Read<&'a [u8]> {
        let end = self.at.checked_add(n).filter(|e| *e <= self.bytes.len());
        let Some(end) = end else {
            return bad("the bytes end early");
        };
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }

    fn blob(&mut self) -> Read<&'a [u8]> {
        let n = self.usize()?;
        self.raw(n)
    }

    fn str(&mut self) -> Read<Rc<str>> {
        match std::str::from_utf8(self.blob()?) {
            Ok(s) => Ok(Rc::from(s)),
            Err(_) => bad("text that isn't UTF-8"),
        }
    }

    fn big(&mut self) -> Read<BigUint> {
        Ok(BigUint::from_bytes_le(self.blob()?))
    }

    fn flag(&mut self) -> Read<bool> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => bad("a flag that isn't 0 or 1"),
        }
    }

    /// The variant of `all` a tag number names.
    fn variant<T: Copy>(&mut self, all: &[T], what: &str) -> Read<T> {
        let n = self.usize()?;
        match all.get(n) {
            Some(v) => Ok(*v),
            None => bad(format!("no {what} numbered {n}")),
        }
    }

    fn prim(&mut self) -> Read<PrimOp> {
        Ok(match self.u8()? {
            0 => PrimOp::Nat(self.variant(nat_tags::ALL, "Nat native")?),
            1 => PrimOp::Int(self.variant(int_tags::ALL, "Int native")?),
            2 => PrimOp::NegSucc,
            3 => PrimOp::IntEqual,
            4 => PrimOp::TextEqual,
            5 => PrimOp::Text(self.variant(text_tags::ALL, "Text native")?),
            6 => PrimOp::Delay(self.variant(delay_tags::ALL, "Delay primitive")?),
            7 => PrimOp::Float(self.variant(float_tags::ALL, "Float native")?),
            8 => PrimOp::Effect(self.variant(effect_tags::ALL, "effect native")?),
            t => return bad(format!("no native operation tagged {t}")),
        })
    }

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
