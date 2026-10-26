//! The byte format's pieces shared by the program codec ([`crate::codec`])
//! and the tables an executable built with `--native` carries
//! ([`crate::linked`], stage NO6 of docs/proposals/native-only.md): LEB128
//! integers, length-prefixed strings, a tag per variant of the native
//! operations, and the shapes. They are here, not in the codec, so that
//! such an executable links none of the codec.

use std::fmt;
use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::native::Native;
use stitchwort_core::partial::Primitive;

use crate::effect::EffectOp;
use crate::ir::{PrimOp, Shapes};
use crate::natives::{FloatPrim, IntNative, TextNative};

/// A hash of this crate's sources (`build.rs`): bytes are read only by a
/// runtime built from the same code as the writer.
pub(crate) const BUILD_HASH: u64 = parse_hash(env!("SW_RT_BUILD_HASH"));

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

/// Why bytes aren't a program this runtime can run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodecError(pub String);

impl fmt::Display for CodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "can't read the program: {}", self.0)
    }
}

impl std::error::Error for CodecError {}

pub(crate) type Read<T> = Result<T, CodecError>;

pub(crate) fn bad<T>(why: impl Into<String>) -> Read<T> {
    Err(CodecError(why.into()))
}

// ---------------------------------------------------------------- enum tags

/// Gives an enum a tag per variant, in the order listed, and checks that the
/// list is every variant (a new variant is a compile error here).
macro_rules! tags {
    ($name:ident, $ty:ty, [$($variant:path),* $(,)?]) => {
        pub(crate) mod $name {
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
        FloatPrim::Bits,
        FloatPrim::Leq,
        FloatPrim::Less
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
        pub(crate) fn write_shapes(w: &mut Writer, s: &Shapes) {
            $(w.uint(u64::from(s.$field));)*
        }
        pub(crate) fn read_shapes(r: &mut Reader) -> Read<Shapes> {
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
pub(crate) struct Writer {
    pub(crate) bytes: Vec<u8>,
}

impl Writer {
    pub(crate) fn u8(&mut self, b: u8) {
        self.bytes.push(b);
    }

    /// LEB128.
    pub(crate) fn uint(&mut self, mut n: u64) {
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

    pub(crate) fn usize(&mut self, n: usize) {
        self.uint(n as u64);
    }

    pub(crate) fn blob(&mut self, bytes: &[u8]) {
        self.usize(bytes.len());
        self.bytes.extend_from_slice(bytes);
    }

    pub(crate) fn str(&mut self, s: &str) {
        self.blob(s.as_bytes());
    }

    pub(crate) fn big(&mut self, n: &BigUint) {
        self.blob(&n.to_bytes_le());
    }

    pub(crate) fn prim(&mut self, op: PrimOp) {
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
}

// ------------------------------------------------------------------ reading

pub(crate) struct Reader<'a> {
    pub(crate) bytes: &'a [u8],
    pub(crate) at: usize,
    pub(crate) depth: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn u8(&mut self) -> Read<u8> {
        let Some(&b) = self.bytes.get(self.at) else {
            return bad("the bytes end early");
        };
        self.at += 1;
        Ok(b)
    }

    pub(crate) fn uint(&mut self) -> Read<u64> {
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

    pub(crate) fn usize(&mut self) -> Read<usize> {
        usize::try_from(self.uint()?).or_else(|_| bad("a number too large"))
    }

    pub(crate) fn u32(&mut self) -> Read<u32> {
        u32::try_from(self.uint()?).or_else(|_| bad("a number too large"))
    }

    /// A count of items that each take at least a byte: refused if more
    /// than the bytes left, so that a corrupt count can't ask for memory.
    pub(crate) fn count(&mut self) -> Read<usize> {
        let n = self.usize()?;
        if n > self.bytes.len() - self.at {
            return bad("a count larger than the bytes left");
        }
        Ok(n)
    }

    pub(crate) fn raw(&mut self, n: usize) -> Read<&'a [u8]> {
        let end = self.at.checked_add(n).filter(|e| *e <= self.bytes.len());
        let Some(end) = end else {
            return bad("the bytes end early");
        };
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }

    pub(crate) fn blob(&mut self) -> Read<&'a [u8]> {
        let n = self.usize()?;
        self.raw(n)
    }

    pub(crate) fn str(&mut self) -> Read<Rc<str>> {
        match std::str::from_utf8(self.blob()?) {
            Ok(s) => Ok(Rc::from(s)),
            Err(_) => bad("text that isn't UTF-8"),
        }
    }

    pub(crate) fn big(&mut self) -> Read<BigUint> {
        Ok(BigUint::from_bytes_le(self.blob()?))
    }

    pub(crate) fn flag(&mut self) -> Read<bool> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => bad("a flag that isn't 0 or 1"),
        }
    }

    /// The variant of `all` a tag number names.
    pub(crate) fn variant<T: Copy>(&mut self, all: &[T], what: &str) -> Read<T> {
        let n = self.usize()?;
        match all.get(n) {
            Some(v) => Ok(*v),
            None => bad(format!("no {what} numbered {n}")),
        }
    }

    pub(crate) fn prim(&mut self) -> Read<PrimOp> {
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
}
