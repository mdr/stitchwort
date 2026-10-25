//! `Float`, a 64-bit IEEE 754 double (docs/proposals/float.md).
//!
//! In the logic a `Float` is the record of its bits, `{ bits: Nat, valid:
//! Float.isValid bits = True }` (std/Float/Float.sw), with every NaN as the
//! one NaN `0x7FF8000000000000`. A value in the evaluator is just that
//! record, with a number for its bits and `Eq.refl True` for its witness:
//! no new kind of value.
//!
//! Two kinds of definitions compute here:
//!
//! - **Primitives** ([`FloatOp`]): the rounding operations, `Float.add`,
//!   `sub`, `mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt`
//!   and `ofNat`, which have no body. They're admitted here once their types
//!   are checked to be exactly the ones [`Signature`] gives, as `Delay`'s
//!   constants are (`partial.rs`). Applied to records whose bits are known
//!   (to a known number, for the conversions), the evaluator computes the
//!   result with Rust's `f64` (JS's rules for `round`, [`js_round`]; the
//!   nearest double for the conversions, [`nat_to_f64`]) and returns `{ bits
//!   = k, valid = Eq.refl True }`, the NaN made canonical; otherwise the
//!   application is stuck, and conversion compares it structurally. This
//!   reduction rule is part of evaluation, always on: it isn't a native, so
//!   switching the natives off doesn't change it (a primitive has no
//!   definition to fall back to). `Float.toText` is a primitive too, with
//!   no reduction rule at all: each runtime supplies it (§2.6, D688).
//! - **Natives** ([`FloatNative`]): `neg`, `abs`, `isNaN`, `isFinite`,
//!   `ieeeLt`, `ieeeLe`, `toInt` and `Float.decEq`, ordinary definitions
//!   over the bits with an implementation here. As for
//!   the number natives (`native.rs`), each must compute exactly the whole
//!   term its definition does, proofs included, so that switching natives
//!   off never changes which `rfl` proofs check (§3.4, D731). They fire only
//!   on records whose bits are known and valid, and return what the
//!   definition computes there: a record built by `Float.make`, whose witness
//!   is `Eq.refl True` on known bits whatever proof it was given; for
//!   `decEq`, `Yes (Float.bitsExt x y rfl)` or `No (Float.bitsNe x y
//!   (Nat.equalFalse m n rfl))`, with the arguments as given.
//!
//! Both are trusted (DESIGN.md §13). They rely on `Float` being exactly the
//! library's declaration (its `isValid` above all: the reducer's result is
//! well typed only if `isValid k` computes to `True` for the bit patterns it
//! makes), and on each native's definition being the one it was checked
//! against. So `Float` and each definition with a native are bound by
//! content hash ([`FLOAT_DATA_HASH`], [`NATIVE_HASHES`]), as `List` and
//! `Char` are for compact text; a library that doesn't match is refused.
//!
//! The contract the reduction rules follow (§3.3) is versioned:
//! [`FLOAT_CONTRACT`] is hashed into every primitive's hash, so changing what
//! a primitive means changes every hash that depends on it.

use std::rc::Rc;

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{ToPrimitive, Zero};
use stitchwort_syntax::Diagnostic;

use crate::budget::{self, Limits};
use crate::globals::{Globals, State};
use crate::hash::{data_hash, def_hash};
use crate::native::{Force, as_nat_with, nat_value};
use crate::registry::Builtin;
use crate::term::{DataId, DefId, Icit, Sort, Term};
use crate::value::{Elim, Head, Value, conv, eval};

/// The version of the semantic contract of the float primitives: their
/// table, types and reduction rules (docs/proposals/float.md §3.3, §2.5,
/// §3.6). Bump it for any deliberate change of meaning.
pub const FLOAT_CONTRACT: u32 = 1;

/// The content hash (DESIGN.md §11) of the library's `Float`, which covers
/// `Float.isValid` and everything it uses.
pub const FLOAT_DATA_HASH: &str =
    "e4ff60202ca96f2ac20c3db9d79474c8def3839c88836496a736df95675bceb7";

/// The content hashes of the definitions with natives here, and of the
/// theorems `decEq`'s native puts in its result.
pub const NATIVE_HASHES: &[(Builtin, &str)] = &[
    (
        Builtin::FloatNeg,
        "e55c26fe3d2a070f671809f27df0b0e108498d063150f61b87986d9c2e5c59d5",
    ),
    (
        Builtin::FloatAbs,
        "e1068690eedded90c018450d2a65988f81d3f538352b1f26aeba856ae7e5b997",
    ),
    (
        Builtin::FloatIsNaN,
        "79ba98ccc2ff711113b447f8f494d8f60a52ad7d3073ffecb925ee4f07225fe8",
    ),
    (
        Builtin::FloatDecEq,
        "d2bafb2f9f556f54aee0c70bfc03387a3e1dfa78203ba103f75567e9e2cd979b",
    ),
    (
        Builtin::FloatIsFinite,
        "16540775350f744d0f0ed958df5191b2bf9accc0e0db79731ff8c5656f910787",
    ),
    (
        Builtin::FloatIeeeLt,
        "6a9574474272226699bc08034b905e8e3416cdbe65491f8778d113dcd2036b0b",
    ),
    (
        Builtin::FloatIeeeLe,
        "06c93fa67525bdff3f19579c82798b569db55bba61604b8d6f017edcf10fc7f3",
    ),
    (
        Builtin::FloatToInt,
        "26ec25a82920530a6b24bdb014dc38736381e6c4a3d5659167ca3bf154f7a383",
    ),
    (
        Builtin::FloatBitsExt,
        "89edffd7b5e9fb3ae8e3157f90cbe96893843a760424acb64cc9fcf26e499c25",
    ),
    (
        Builtin::FloatBitsNe,
        "561015c695f767e73dd71a5ea634eb2bbfe4135074d987499f3b2823d4704b81",
    ),
];

/// The sign bit.
pub const SIGN: u64 = 1 << 63;
/// The one NaN.
pub const NAN: u64 = 0x7FF8_0000_0000_0000;
/// +infinity.
pub const INFINITY: u64 = 0x7FF0_0000_0000_0000;
/// -infinity.
pub const NEG_INFINITY: u64 = 0xFFF0_0000_0000_0000;

/// `Float.isValid`: a double's bits with the NaN canonical.
pub fn is_valid(bits: u64) -> bool {
    bits <= INFINITY || bits == NAN || (SIGN..=NEG_INFINITY).contains(&bits)
}

/// The bits of `x`, any NaN as the one NaN (D701).
pub fn canonical_bits(x: f64) -> u64 {
    if x.is_nan() { NAN } else { x.to_bits() }
}

/// Stitchwort source for the double with valid `bits`, which reads back as
/// the same double: the shortest decimal that rounds to it (with `.0` when
/// it's whole), `-0.0`, `Float.nan`, `Float.infinity` or `-Float.infinity`.
/// For showing values, as the pretty-printer does.
pub fn source(bits: u64) -> String {
    match bits {
        NAN => "Float.nan".into(),
        INFINITY => "Float.infinity".into(),
        NEG_INFINITY => "-Float.infinity".into(),
        // Rust's `{:?}` is the shortest round-trip spelling: `0.1`, `3.0`,
        // `1e21`, `5e-324`, `-0.0`.
        _ => format!("{:?}", f64::from_bits(bits)),
    }
}

/// A primitive: a rounding operation without a definition, or `toText`,
/// which has none and doesn't reduce.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Floor,
    Ceil,
    Trunc,
    Round,
    OfInt,
    OfNat,
    /// `Float.toText : Float -> Text`: opaque in the kernel, supplied by
    /// each runtime (docs/proposals/float.md §2.6, D688).
    ToText,
}

/// The type a primitive must have.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Signature {
    /// `Float -> Float -> Float`
    Binary,
    /// `Float -> Float`
    Unary,
    /// `Int -> Float`
    OfInt,
    /// `Nat -> Float`
    OfNat,
    /// `Float -> Text`
    ToText,
}

impl Signature {
    pub fn text(self) -> &'static str {
        match self {
            Signature::Binary => "Float -> Float -> Float",
            Signature::Unary => "Float -> Float",
            Signature::OfInt => "Int -> Float",
            Signature::OfNat => "Nat -> Float",
            Signature::ToText => "Float -> Text",
        }
    }
}

impl FloatOp {
    pub const ALL: [FloatOp; 12] = [
        FloatOp::Add,
        FloatOp::Sub,
        FloatOp::Mul,
        FloatOp::Div,
        FloatOp::Rem,
        FloatOp::Floor,
        FloatOp::Ceil,
        FloatOp::Trunc,
        FloatOp::Round,
        FloatOp::OfInt,
        FloatOp::OfNat,
        FloatOp::ToText,
    ];

    /// Its name in the library.
    pub fn name(self) -> &'static str {
        self.builtin().name()
    }

    pub fn builtin(self) -> Builtin {
        match self {
            FloatOp::Add => Builtin::FloatAdd,
            FloatOp::Sub => Builtin::FloatSub,
            FloatOp::Mul => Builtin::FloatMul,
            FloatOp::Div => Builtin::FloatDiv,
            FloatOp::Rem => Builtin::FloatRem,
            FloatOp::Floor => Builtin::FloatFloor,
            FloatOp::Ceil => Builtin::FloatCeil,
            FloatOp::Trunc => Builtin::FloatTrunc,
            FloatOp::Round => Builtin::FloatRound,
            FloatOp::OfInt => Builtin::FloatOfInt,
            FloatOp::OfNat => Builtin::FloatOfNat,
            FloatOp::ToText => Builtin::FloatToText,
        }
    }

    pub fn named(name: &str) -> Option<FloatOp> {
        FloatOp::ALL.into_iter().find(|op| op.name() == name)
    }

    pub fn signature(self) -> Signature {
        match self {
            FloatOp::Add | FloatOp::Sub | FloatOp::Mul | FloatOp::Div | FloatOp::Rem => {
                Signature::Binary
            }
            FloatOp::Floor | FloatOp::Ceil | FloatOp::Trunc | FloatOp::Round => Signature::Unary,
            FloatOp::OfInt => Signature::OfInt,
            FloatOp::OfNat => Signature::OfNat,
            FloatOp::ToText => Signature::ToText,
        }
    }

    pub fn arity(self) -> usize {
        match self.signature() {
            Signature::Binary => 2,
            _ => 1,
        }
    }

    /// A binary operation on doubles: IEEE 754 binary64, rounding to
    /// nearest, ties to even (the contract's conditions C1-C6). `%` is the
    /// truncated remainder, as JS's (and Rust's) `%`, which is exact. The
    /// caller makes a NaN result canonical.
    pub fn apply(self, a: f64, b: f64) -> f64 {
        match self {
            FloatOp::Add => a + b,
            FloatOp::Sub => a - b,
            FloatOp::Mul => a * b,
            FloatOp::Div => a / b,
            FloatOp::Rem => a % b,
            _ => unreachable!("`{}` isn't a binary operation", self.name()),
        }
    }

    /// A unary operation on doubles, as JS's `Math.floor`, `Math.ceil`,
    /// `Math.trunc` and `Math.round`.
    pub fn apply_unary(self, a: f64) -> f64 {
        match self {
            FloatOp::Floor => a.floor(),
            FloatOp::Ceil => a.ceil(),
            FloatOp::Trunc => a.trunc(),
            FloatOp::Round => js_round(a),
            _ => unreachable!("`{}` isn't a unary operation", self.name()),
        }
    }
}

/// JS's `Math.round` (ECMAScript's rule, docs/proposals/float.md §2.5):
/// NaN, the infinities and the zeros as they are; `0 < x < 0.5` gives
/// `+0`; `-0.5 <= x < 0` gives `-0`; otherwise the nearest integer, a tie
/// going towards +infinity. Not `floor(x + 0.5)`, whose sum can round
/// (`0.49999999999999994`, `2^52 + 1`), and not Rust's `round`, which takes
/// a tie away from zero (`-2.5`).
pub fn js_round(x: f64) -> f64 {
    if !x.is_finite() || x == 0.0 {
        return x;
    }
    // Every double this large is whole.
    if x.abs() >= 4_503_599_627_370_496.0 {
        return x;
    }
    if x > 0.0 && x < 0.5 {
        return 0.0;
    }
    if (-0.5..0.0).contains(&x) {
        return -0.0;
    }
    // Below 2^52, `x - floor(x)` and `floor(x) + 1` are exact.
    let r = x.floor();
    if x - r >= 0.5 { r + 1.0 } else { r }
}

/// The double nearest `n` (rounding to nearest, ties to even), or
/// +infinity beyond the largest: JS's `Number(n)` of a non-negative
/// `bigint`.
pub fn nat_to_f64(n: &BigUint) -> f64 {
    let bits = n.bits();
    if bits <= 53 {
        return n.to_u64().expect("53 bits") as f64;
    }
    if bits > 1024 {
        return f64::INFINITY;
    }
    // The top 54 bits: the significand, then the rounding bit; below them,
    // whether anything is left (the sticky bit).
    let shift = bits - 54;
    let top = (n >> shift).to_u64().expect("54 bits");
    let sticky = n.trailing_zeros().is_some_and(|z| z < shift);
    let mut significand = top >> 1;
    if top & 1 == 1 && (sticky || significand & 1 == 1) {
        significand += 1;
    }
    // At most 2^53 times 2^971: the scale is a normal double, and the
    // product is exact, or exactly 2^1024, which is +infinity.
    let scale = f64::from_bits((1023 + shift + 1) << 52);
    significand as f64 * scale
}

/// [`nat_to_f64`] for an integer of either sign: JS's `Number(n)`.
pub fn int_to_f64(n: &BigInt) -> f64 {
    let x = nat_to_f64(n.magnitude());
    if n.sign() == Sign::Minus { -x } else { x }
}

/// The integer the double with valid `bits` is, if it is a whole number
/// (`Float.toInt`): `None` for a fraction, the infinities and the NaN; both
/// zeros are `0`.
pub fn to_int(bits: u64) -> Option<BigInt> {
    let magnitude = bits & !SIGN;
    let exponent = magnitude >> 52;
    let fraction = magnitude & ((1 << 52) - 1);
    let n = match exponent {
        2047 => return None,
        0 if fraction == 0 => BigUint::zero(),
        // Subnormals are below 1.
        0 => return None,
        _ => {
            let significand = (1u64 << 52) | fraction;
            if exponent >= 1075 {
                BigUint::from(significand) << (exponent - 1075)
            } else {
                let shift = 1075 - exponent;
                if shift >= 53 || significand & ((1 << shift) - 1) != 0 {
                    return None;
                }
                BigUint::from(significand >> shift)
            }
        }
    };
    let n = BigInt::from(n);
    Some(if bits >= SIGN { -n } else { n })
}

/// Of the decimals `s × 10^q` with as many digits as `digits` (which reads
/// back as positive finite `x`), the one closest to `x` that reads back as
/// it, and of two equally close, the one with an even last digit: what
/// `Number::toString` recommends and engines do. Rust's shortest formatting
/// gives the shortest digits, but on an exact tie it can take the odd one
/// (`-1149636667324797.25` is `…797.3` in Rust, `…797.2` in JS).
fn closest_digits(x: f64, digits: String, q: i64) -> String {
    let bits = x.to_bits();
    let field = ((bits >> 52) & 0x7FF) as i64;
    let fraction = bits & ((1 << 52) - 1);
    let (m, e) = if field == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1 << 52), field - 1075)
    };
    // Everything times 2^a × 10^b, to be whole.
    let (a, b) = ((-e).max(0) as u32, (-q).max(0) as u32);
    let pow = |base: u32, k: u32| num_traits::pow(BigInt::from(base), k as usize);
    let v = BigInt::from(m) * pow(2, (e + i64::from(a)) as u32) * pow(10, b);
    let scale = pow(10, (q + i64::from(b)) as u32) * pow(2, a);
    let distance = |s: &BigInt| (s * &scale - &v).magnitude().clone();
    let s: BigInt = digits.parse().expect("digits");
    let mut best = (distance(&s), s.clone());
    for alt in [&s - BigInt::from(1), &s + BigInt::from(1)] {
        let text = alt.to_string();
        if text.len() != digits.len() || format!("{text}e{q}").parse::<f64>() != Ok(x) {
            continue;
        }
        let d = distance(&alt);
        let even = |n: &BigInt| (n % 2u32).is_zero();
        if d < best.0 || (d == best.0 && even(&alt) && !even(&best.1)) {
            best = (d, alt);
        }
    }
    best.1.to_string()
}

/// JS's `String(x)` (ECMAScript's `Number::toString` in base 10): the
/// shortest decimal that reads back as `x`, laid out as JS does:
/// `0.30000000000000004`, `100`, `1e+21`, `1e-7`, `NaN`, `-Infinity`, and
/// `0` for both zeros. This is the Rust runtime's `Float.toText`; the
/// generated JS calls `String` itself. Rust's shortest formatting (`{:e}`)
/// gives the number of digits, [`closest_digits`] the closest such decimal
/// (ties to even), as the specification recommends, and the layout follows
/// the specification's cases.
pub fn js_to_string(x: f64) -> String {
    if x.is_nan() {
        return "NaN".into();
    }
    if x == 0.0 {
        return "0".into();
    }
    if x < 0.0 {
        return format!("-{}", js_to_string(-x));
    }
    if x.is_infinite() {
        return "Infinity".into();
    }
    // `d.ddde±k`: the digits `s` (k of them) and the exponent `n` such that
    // the value is 0.s × 10^n.
    let shortest = format!("{x:e}");
    let (mantissa, exponent) = shortest.split_once('e').expect("an exponent");
    let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
    let k = digits.len() as i64;
    let n = exponent.parse::<i64>().expect("a decimal exponent") + 1;
    let digits = closest_digits(x, digits, n - k);
    debug_assert_eq!(digits.len() as i64, k);
    if k <= n && n <= 21 {
        format!("{digits}{}", "0".repeat((n - k) as usize))
    } else if 0 < n && n <= 21 {
        format!("{}.{}", &digits[..n as usize], &digits[n as usize..])
    } else if -6 < n && n <= 0 {
        format!("0.{}{digits}", "0".repeat((-n) as usize))
    } else {
        let e = n - 1;
        let sign = if e < 0 { '-' } else { '+' };
        if k == 1 {
            format!("{digits}e{sign}{}", e.abs())
        } else {
            format!("{}.{}e{sign}{}", &digits[..1], &digits[1..], e.abs())
        }
    }
}

/// A definition over the bits with a native implementation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatNative {
    /// `Float.neg x`: the sign flipped, the NaN for the NaN.
    Neg,
    /// `Float.abs x`: the sign cleared.
    Abs,
    /// `Float.isNaN x : Bool`.
    IsNaN,
    /// `Float.decEq x y : Decidable (x = y)`.
    DecEq,
    /// `Float.isFinite x : Bool`.
    IsFinite,
    /// `Float.ieeeLt x y : Bool`, JS's `<`.
    IeeeLt,
    /// `Float.ieeeLe x y : Bool`, JS's `<=`.
    IeeeLe,
    /// `Float.toInt x : Option Int`.
    ToInt,
}

impl FloatNative {
    pub const ALL: [FloatNative; 8] = [
        FloatNative::Neg,
        FloatNative::Abs,
        FloatNative::IsNaN,
        FloatNative::DecEq,
        FloatNative::IsFinite,
        FloatNative::IeeeLt,
        FloatNative::IeeeLe,
        FloatNative::ToInt,
    ];

    pub fn builtin(self) -> Builtin {
        match self {
            FloatNative::Neg => Builtin::FloatNeg,
            FloatNative::Abs => Builtin::FloatAbs,
            FloatNative::IsNaN => Builtin::FloatIsNaN,
            FloatNative::DecEq => Builtin::FloatDecEq,
            FloatNative::IsFinite => Builtin::FloatIsFinite,
            FloatNative::IeeeLt => Builtin::FloatIeeeLt,
            FloatNative::IeeeLe => Builtin::FloatIeeeLe,
            FloatNative::ToInt => Builtin::FloatToInt,
        }
    }

    pub fn name(self) -> &'static str {
        self.builtin().name()
    }

    pub fn arity(self) -> usize {
        match self {
            FloatNative::DecEq | FloatNative::IeeeLt | FloatNative::IeeeLe => 2,
            _ => 1,
        }
    }

    /// The native on bits: the result's bits, for those returning a `Float`.
    pub fn on_bits(self, bits: u64) -> u64 {
        match self {
            FloatNative::Neg if bits == NAN => NAN,
            FloatNative::Neg => bits ^ SIGN,
            FloatNative::Abs => bits & !SIGN,
            _ => unreachable!("`{}` doesn't return a `Float`", self.name()),
        }
    }
}

/// `Float.isFinite` on valid bits.
pub fn is_finite(bits: u64) -> bool {
    bits & !SIGN < INFINITY
}

/// `Float.ieeeLt` and `Float.ieeeLe` on valid bits: IEEE 754's (and JS's)
/// `<` and `<=`, false when either is the NaN, the zeros equal.
pub fn ieee_less(a: u64, b: u64, or_equal: bool) -> bool {
    let (x, y) = (f64::from_bits(a), f64::from_bits(b));
    if or_equal { x <= y } else { x < y }
}

/// IEEE 754's `totalOrder` on valid bits, the NaN greatest (`Float.compare`).
pub fn total_order(a: u64, b: u64) -> std::cmp::Ordering {
    let key = |bits: u64| -> i128 {
        if bits >= SIGN {
            -i128::from(bits - SIGN) - 1
        } else {
            i128::from(bits)
        }
    };
    key(a).cmp(&key(b))
}

/// What the evaluator does with a definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatDef {
    Primitive(FloatOp),
    Native(FloatNative),
}

/// The library's `Float` and the theorems a native refers to, once bound.
#[derive(Clone, Debug, Default)]
pub struct FloatBinding {
    pub data: Option<DataId>,
    pub bits_ext: Option<DefId>,
    pub bits_ne: Option<DefId>,
}

type Result<T> = std::result::Result<T, Diagnostic>;

fn refused(span: stitchwort_syntax::Span, name: &str, why: &str) -> Diagnostic {
    Diagnostic::error(
        "E-BUILTIN",
        format!("the library's `{name}` isn't the declaration the compiler's `Float` support was written for"),
    )
    .with_label(span, why.to_string())
    .with_note("its content hash is pinned in crates/core/src/float.rs; a test prints the new hashes")
}

/// Hashes, with an operation running for the hasher's depth guard.
fn hex_of(
    g: &Globals,
    f: impl FnOnce() -> budget::Result<Option<crate::hash::ContentHash>>,
) -> Option<String> {
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    f().ok().flatten().map(|h| h.hex())
}

/// The content hash of `Float` and of each definition bound here, against
/// the pinned one: for the test that fails when the library changes them,
/// which prints the new ones.
pub fn bindings(g: &Globals) -> Vec<(String, Option<String>, &'static str)> {
    let mut out = Vec::new();
    if let Some(d) = g.registry.loaded_data(Builtin::Float) {
        out.push((
            "Float".to_string(),
            hex_of(g, || data_hash(g, d)),
            FLOAT_DATA_HASH,
        ));
    }
    for &(b, pinned) in NATIVE_HASHES {
        if let Some(id) = g.registry.loaded_def(b) {
            out.push((b.name().to_string(), hex_of(g, || def_hash(g, id)), pinned));
        }
    }
    out
}

/// Binds the library's `Float`, which must be a record of a `Nat` and a
/// proof, with the pinned content hash.
pub fn register_data(g: &mut Globals, d: DataId) -> Result<()> {
    let data = g.data(d);
    let span = data.span;
    let shaped = data.state == State::Final
        && data.record
        && data.params.is_empty()
        && data.indices.is_empty()
        && data.sort == Sort::Type(0)
        && data.ctors.len() == 1
        && data.ctors[0].fields.len() == 2
        && matches!(data.ctors[0].fields[0].1.strip_loc(), Term::Data(n, args) if Some(*n) == g.builtins.nat && args.is_empty());
    if !shaped {
        return Err(refused(span, "Float", "not the record of a double's bits"));
    }
    if hex_of(g, || data_hash(g, d)).as_deref() != Some(FLOAT_DATA_HASH) {
        return Err(refused(
            span,
            "Float",
            "its content hash isn't the pinned one",
        ));
    }
    g.builtins.float.data = Some(d);
    Ok(())
}

/// The bound `Float` type, as a term.
fn float_ty(g: &Globals) -> Option<Term> {
    Some(Term::Data(g.builtins.float.data?, Vec::new()))
}

/// The type primitive `op` must have, for the bound `Float` and the core's
/// `Int`, `Nat` and `Text`.
fn primitive_type(g: &Globals, op: FloatOp) -> Option<Term> {
    let arrow =
        |dom: Term, cod: Term| Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
    let f = float_ty(g)?;
    let data = |d: DataId| Term::Data(d, Vec::new());
    Some(match op.signature() {
        Signature::Binary => arrow(f.clone(), arrow(f.clone(), f)),
        Signature::Unary => arrow(f.clone(), f),
        Signature::OfInt => arrow(data(g.registry.loaded_data(Builtin::Int)?), f),
        Signature::OfNat => arrow(data(g.builtins.nat?), f),
        Signature::ToText => arrow(f, data(g.registry.loaded_data(Builtin::Text)?)),
    })
}

/// Admits pending definition `id`, declared with only a signature, as
/// primitive `op`: final, with no body. Its type must be exactly the one
/// [`Signature`] gives it (`Float -> Float -> Float` for `add`), for the
/// bound `Float`.
pub fn define_primitive(g: &mut Globals, id: DefId, op: FloatOp) -> Result<()> {
    let Some(def) = g.defs.get(id.0) else {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown definition",
        ));
    };
    if def.state != State::Pending {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            format!(
                "malformed core term: `{}` has already been defined",
                def.name
            ),
        ));
    }
    let taken = g
        .builtins
        .float_defs
        .values()
        .any(|d| *d == FloatDef::Primitive(op));
    let fits = !taken
        && match primitive_type(g, op) {
            Some(expected) => conv(g, 0, &eval(g, &[], &expected)?, &def.ty_value)?,
            None => false,
        };
    if !fits {
        let e = Diagnostic::error(
            "E-BUILTIN",
            format!(
                "the library's `{}` doesn't have the type the compiler expects, `{}`",
                op.name(),
                op.signature().text()
            ),
        )
        .with_label(g.def(id).span, "here");
        g.defs[id.0].state = State::Failed;
        return Err(e);
    }
    let def = &mut g.defs[id.0];
    def.state = State::Final;
    def.arity = 0;
    g.builtins.float_defs.insert(id, FloatDef::Primitive(op));
    Ok(())
}

/// Binds a definition with a native here, or a theorem a native refers to,
/// after checking its content hash against the pinned one (which fixes its
/// type and its definition). `Float` must be bound first.
pub fn register_def(g: &mut Globals, id: DefId, b: Builtin) -> Result<()> {
    let Some(&(_, pinned)) = NATIVE_HASHES.iter().find(|(nb, _)| *nb == b) else {
        return Ok(());
    };
    let span = g.def(id).span;
    if g.builtins.float.data.is_none() {
        return Err(refused(span, b.name(), "`Float` isn't bound"));
    }
    if hex_of(g, || def_hash(g, id)).as_deref() != Some(pinned) {
        return Err(refused(
            span,
            b.name(),
            "its content hash isn't the pinned one",
        ));
    }
    match b {
        Builtin::FloatBitsExt => g.builtins.float.bits_ext = Some(id),
        Builtin::FloatBitsNe => g.builtins.float.bits_ne = Some(id),
        _ => {
            let native = FloatNative::ALL
                .into_iter()
                .find(|n| n.builtin() == b)
                .expect("every pinned definition is a native or a theorem");
            let arity = g.def(id).arity;
            if arity != native.arity() {
                return Err(refused(span, b.name(), "its arity isn't the native's"));
            }
            g.builtins.float_defs.insert(id, FloatDef::Native(native));
        }
    }
    Ok(())
}

/// The record `{ bits = k, valid = Eq.refl True }`.
pub fn float_value(data: DataId, bits: u64) -> Value {
    debug_assert!(is_valid(bits), "a float result with invalid bits {bits:#x}");
    Value::Ctor(data, 0, [nat_value(bits.into()), Value::Refl].into())
}

/// The bits of `value`, if it's a `Float` record whose bits are known and
/// valid.
fn known_bits(
    g: &Globals,
    data: DataId,
    value: &Value,
    force: Force,
) -> budget::Result<Option<u64>> {
    let Value::Ctor(d, 0, fields) = force(g, value.clone())? else {
        return Ok(None);
    };
    if d != data || fields.len() != 2 {
        return Ok(None);
    }
    Ok(as_nat_with(g, &fields[0], force)?
        .and_then(|n| n.to_u64())
        .filter(|b| is_valid(*b)))
}

/// Runs float primitive or native `id` on `spine`, if it is one, it has
/// all its arguments, and their bits are known: `None` otherwise (it's
/// stuck, or its definition unfolds).
pub fn run(g: &Globals, id: DefId, spine: &[Elim], force: Force) -> budget::Result<Option<Value>> {
    let Some(def) = g.builtins.float_def(id) else {
        return Ok(None);
    };
    let Some(data) = g.builtins.float.data else {
        return Ok(None);
    };
    let arity = match def {
        FloatDef::Primitive(op) => op.arity(),
        FloatDef::Native(n) => n.arity(),
    };
    if spine.len() != arity {
        return Ok(None);
    }
    // The conversions take a number, and `toText` never computes.
    if let FloatDef::Primitive(op @ (FloatOp::OfInt | FloatOp::OfNat | FloatOp::ToText)) = def {
        let Elim::App(v, Icit::Explicit) = &spine[0] else {
            return Ok(None);
        };
        let x = match op {
            FloatOp::OfNat => match as_nat_with(g, v, force)? {
                Some(n) => nat_to_f64(&n),
                None => return Ok(None),
            },
            FloatOp::OfInt => match known_int(g, v, force)? {
                Some(n) => int_to_f64(&n),
                None => return Ok(None),
            },
            _ => return Ok(None),
        };
        return Ok(Some(float_value(data, canonical_bits(x))));
    }
    let mut args = Vec::with_capacity(arity);
    let mut bits = Vec::with_capacity(arity);
    for e in spine {
        let Elim::App(v, Icit::Explicit) = e else {
            return Ok(None);
        };
        let Some(b) = known_bits(g, data, v, force)? else {
            return Ok(None);
        };
        args.push(v.clone());
        bits.push(b);
    }
    let boolean = |b: bool| {
        g.builtins
            .bool
            .map(|d| Value::Ctor(d, usize::from(b), [].into()))
    };
    Ok(match def {
        FloatDef::Primitive(op) if op.arity() == 2 => {
            let r = op.apply(f64::from_bits(bits[0]), f64::from_bits(bits[1]));
            Some(float_value(data, canonical_bits(r)))
        }
        FloatDef::Primitive(op) => {
            let r = op.apply_unary(f64::from_bits(bits[0]));
            Some(float_value(data, canonical_bits(r)))
        }
        FloatDef::Native(FloatNative::IsNaN) => boolean(bits[0] == NAN),
        FloatDef::Native(FloatNative::IsFinite) => boolean(is_finite(bits[0])),
        FloatDef::Native(FloatNative::IeeeLt) => boolean(ieee_less(bits[0], bits[1], false)),
        FloatDef::Native(FloatNative::IeeeLe) => boolean(ieee_less(bits[0], bits[1], true)),
        FloatDef::Native(FloatNative::DecEq) => dec_eq(g, &args, bits[0], bits[1]),
        FloatDef::Native(FloatNative::ToInt) => to_int_value(g, bits[0]),
        FloatDef::Native(n) => Some(float_value(data, n.on_bits(bits[0]))),
    })
}

/// The integer `value` is, if it's an `Int` constructor around a known
/// number.
fn known_int(g: &Globals, value: &Value, force: Force) -> budget::Result<Option<BigInt>> {
    let (Some((int, of_nat)), Some((_, neg_succ))) = (
        g.registry.ctor(Builtin::OfNat),
        g.registry.ctor(Builtin::NegSucc),
    ) else {
        return Ok(None);
    };
    let Value::Ctor(d, c, fields) = force(g, value.clone())? else {
        return Ok(None);
    };
    if d != int || fields.len() != 1 {
        return Ok(None);
    }
    let Some(n) = as_nat_with(g, &fields[0], force)? else {
        return Ok(None);
    };
    Ok(if c == of_nat {
        Some(BigInt::from(n))
    } else if c == neg_succ {
        Some(-BigInt::from(n) - 1)
    } else {
        None
    })
}

/// What `Float.toInt` computes for known bits: `None`, `Some (OfNat n)` or
/// `Some (NegSucc n)` (what `Int.neg (OfNat (n + 1))` reduces to).
fn to_int_value(g: &Globals, bits: u64) -> Option<Value> {
    let (option, none) = g.registry.ctor(Builtin::None)?;
    let (_, some) = g.registry.ctor(Builtin::Some)?;
    let (int, of_nat) = g.registry.ctor(Builtin::OfNat)?;
    let (_, neg_succ) = g.registry.ctor(Builtin::NegSucc)?;
    Some(match to_int(bits) {
        None => Value::Ctor(option, none, [].into()),
        Some(n) => {
            let i = match n.to_biguint() {
                Some(m) => Value::Ctor(int, of_nat, [nat_value(m)].into()),
                None => {
                    let m = (-n - BigInt::from(1)).to_biguint().expect("negative");
                    Value::Ctor(int, neg_succ, [nat_value(m)].into())
                }
            };
            Value::Ctor(option, some, [i].into())
        }
    })
}

/// What `Float.decEq x y` computes for known bits `m` and `n`: `Yes
/// (Float.bitsExt x y rfl)`, or `No (Float.bitsNe x y (Nat.equalFalse m n
/// rfl))` (what `Nat.decEq m n` gives, passed on by `Float.decEqFrom`). The
/// theorems stay folded, as they do when the definition runs.
fn dec_eq(g: &Globals, args: &[Value], m: u64, n: u64) -> Option<Value> {
    let dec = g.builtins.decidable?;
    let arg = |v: Value| Elim::App(v, Icit::Explicit);
    let (x, y) = (args[0].clone(), args[1].clone());
    if m == n {
        let proof = Value::Neutral(
            Head::Def(g.builtins.float.bits_ext?),
            vec![arg(x), arg(y), arg(Value::Refl)].into(),
        );
        Some(Value::Ctor(dec, 0, [proof].into()))
    } else {
        let differ = Value::Neutral(
            Head::Def(g.builtins.nat_neq?),
            vec![
                arg(nat_value(m.into())),
                arg(nat_value(n.into())),
                arg(Value::Refl),
            ]
            .into(),
        );
        let proof = Value::Neutral(
            Head::Def(g.builtins.float.bits_ne?),
            vec![arg(x), arg(y), arg(differ)].into(),
        );
        Some(Value::Ctor(dec, 1, [proof].into()))
    }
}

/// A double's bits as the `Nat` the literal elaborator writes.
pub fn literal_term(data: DataId, bits: u64) -> Term {
    Term::ctor(data, 0, vec![Term::Nat(Rc::new(bits.into())), Term::Refl])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn same(a: f64, b: f64) -> bool {
        canonical_bits(a) == canonical_bits(b)
    }

    /// `Math.round`'s cases (docs/proposals/float.md §2.5), which neither
    /// `floor(x + 0.5)` nor Rust's `round` gets all of.
    #[test]
    fn round_is_javascripts() {
        for (x, expected) in [
            (0.49999999999999994, 0.0),
            (-0.5, -0.0),
            (-0.0, -0.0),
            (4503599627370497.0, 4503599627370497.0),
            (-2.5, -2.0),
            (2.5, 3.0),
            (-0.4, -0.0),
            (0.5, 1.0),
            (-1.5, -1.0),
            (f64::INFINITY, f64::INFINITY),
            (f64::NAN, f64::NAN),
        ] {
            assert!(same(js_round(x), expected), "{x}: {}", js_round(x));
        }
    }

    /// Integers to doubles round to nearest, ties to even, and overflow to
    /// infinity exactly at the halfway point past the largest double.
    #[test]
    fn integers_round_ties_to_even() {
        let two = |k: u32| BigUint::from(1u8) << k;
        assert!(same(nat_to_f64(&(two(53) + 1u8)), 9007199254740992.0));
        assert!(same(nat_to_f64(&(two(53) + 3u8)), 9007199254740996.0));
        assert!(same(nat_to_f64(&(two(1024) - two(970))), f64::INFINITY));
        assert!(same(nat_to_f64(&(two(1024) - two(970) - 1u8)), f64::MAX));
        assert!(same(
            int_to_f64(&-BigInt::from(two(64) + 1u8)),
            -18446744073709551616.0
        ));
        assert!(same(nat_to_f64(&BigUint::zero()), 0.0));
    }

    #[test]
    fn to_int_covers_every_whole_double() {
        assert_eq!(to_int(SIGN), Some(BigInt::zero()));
        assert_eq!(to_int((-3.0f64).to_bits()), Some(BigInt::from(-3)));
        assert_eq!(to_int(0.5f64.to_bits()), None);
        assert_eq!(to_int(1), None);
        assert_eq!(to_int(INFINITY), None);
        assert_eq!(to_int(NAN), None);
        assert_eq!(
            to_int(f64::MAX.to_bits()).map(|n| n.bits()),
            Some(1024),
            "the largest double is a 1024-bit integer"
        );
        assert_eq!(
            to_int(4503599627370497.0f64.to_bits()),
            Some(BigInt::from(4503599627370497u64))
        );
    }

    #[test]
    fn to_string_is_javascripts() {
        for (x, expected) in [
            (1e21, "1e+21"),
            (1e20, "100000000000000000000"),
            (1e-7, "1e-7"),
            (1e-6, "0.000001"),
            (0.30000000000000004, "0.30000000000000004"),
            (-0.0, "0"),
            (f64::NAN, "NaN"),
            (f64::NEG_INFINITY, "-Infinity"),
            (5e-324, "5e-324"),
            (1.7976931348623157e308, "1.7976931348623157e+308"),
            (123.0, "123"),
            (-1234.5678, "-1234.5678"),
            // An exact tie between two 17-digit decimals: the even one.
            (f64::from_bits(0xC310_565A_94B4_E5F5), "-1149636667324797.2"),
        ] {
            assert_eq!(js_to_string(x), expected, "{x:e}");
        }
    }
}
