//! The native operations on the machine's values: the kernel's `Nat`
//! natives, the `Int` and `Text` natives as the IR binds them
//! ([`crate::natives`]), and `Delay`'s constants, which build data.
//! `Text.fold`, which calls a function, is the machine's own
//! ([`crate::machine`]).
//!
//! Each computes exactly what the definition it replaces computes: `Nat`
//! subtraction stops at zero; `Int.div` and `Int.mod` are Euclidean (the
//! remainder is never negative), `tdiv`/`tmod` truncate and `fdiv`/`fmod`
//! round down. Divisions take a proof that the divisor isn't zero, so none
//! divides by zero; `Nat.divFuel`, which has no such proof, gives its fuel
//! for a zero divisor, as its definition does. Small numbers are computed
//! as machine integers, falling back to big ones only when a result
//! doesn't fit.

use std::cmp::Ordering;
use std::rc::Rc;

use num_bigint::{BigInt, BigUint, Sign};
use stitchwort_core::native::Native;
use stitchwort_core::partial::Primitive;

use crate::ir::{PrimOp, Shapes};
use crate::natives::{FloatPrim, IntNative, TextNative};
use crate::value::{Delay, Value};

fn bad(op: PrimOp, v: &Value) -> ! {
    panic!("internal error: %{} given {v:?}", op.name())
}

pub fn boolean(s: &Shapes, b: bool) -> Value {
    Value::Tag(if b { s.true_ } else { s.false_ })
}

fn decision(s: &Shapes, b: bool) -> Value {
    Value::Tag(if b { s.yes } else { s.no })
}

/// `LT`, `EQ` or `GT`.
fn ordering(o: Ordering) -> Value {
    Value::Tag(match o {
        Ordering::Less => 0,
        Ordering::Equal => 1,
        Ordering::Greater => 2,
    })
}

fn some(s: &Shapes, v: Value) -> Value {
    Value::data(s.some, [v])
}

thread_local! {
    /// The ASCII characters' cells, made once and shared (a cell is never
    /// changed while shared), for `MkChar`'s tag.
    static ASCII: std::cell::RefCell<(u32, Vec<Value>)> =
        const { std::cell::RefCell::new((u32::MAX, Vec::new())) };
}

pub fn char_value(s: &Shapes, c: char) -> Value {
    let code = u32::from(c);
    if code < 128 {
        return ASCII.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.0 != s.char_ {
                *cache = (
                    s.char_,
                    (0..128u64)
                        .map(|n| Value::data(s.char_, [Value::Nat(n)]))
                        .collect(),
                );
            }
            cache.1[code as usize].clone()
        });
    }
    Value::data(s.char_, [Value::Nat(u64::from(code))])
}

/// A text's characters, as a `List Char`.
pub fn chars(s: &Shapes, text: &str) -> Value {
    let mut list = Value::Tag(s.nil);
    for c in text.chars().rev() {
        list = Value::data(s.cons, [char_value(s, c), list]);
    }
    list
}

fn list(s: &Shapes, items: Vec<Value>) -> Value {
    let mut list = Value::Tag(s.nil);
    for item in items.into_iter().rev() {
        list = Value::data(s.cons, [item, list]);
    }
    list
}

/// A `Char`'s character.
pub fn char_of(v: &Value) -> char {
    if let Value::Data(_, fields) = v
        && let Value::Nat(code) = fields[0]
        && let Some(c) = u32::try_from(code).ok().and_then(char::from_u32)
    {
        return c;
    }
    panic!("internal error: expected a `Char`, got {v:?}")
}

/// The items of a `List`, in order.
fn items<'v>(s: &Shapes, mut l: &'v Value) -> impl Iterator<Item = &'v Value> {
    let cons = s.cons;
    std::iter::from_fn(move || match l {
        Value::Data(t, cell) if *t == cons => {
            let item = &cell[0];
            l = &cell[1];
            Some(item)
        }
        _ => None,
    })
}

pub fn text_of(v: &Value) -> &Rc<str> {
    match v {
        Value::Text(t) => t,
        other => panic!("internal error: expected a `Text`, got {other:?}"),
    }
}

// --------------------------------------------------------------- numbers

/// `a == b` on `Nat`s or on `Int`s: each number has one form.
fn num_eq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Nat(a), Value::Nat(b)) => a == b,
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::BigNat(a), Value::BigNat(b)) => a == b,
        (Value::BigInt(a), Value::BigInt(b)) => a == b,
        _ => false,
    }
}

fn nat_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Nat(a), Value::Nat(b)) => a.cmp(b),
        (Value::Nat(_), Value::BigNat(_)) => Ordering::Less,
        (Value::BigNat(_), Value::Nat(_)) => Ordering::Greater,
        (Value::BigNat(a), Value::BigNat(b)) => a.cmp(b),
        _ => panic!("internal error: comparing {a:?} with {b:?} as `Nat`s"),
    }
}

fn int_cmp(a: &Value, b: &Value) -> Ordering {
    match (a, b) {
        (Value::Int(a), Value::Int(b)) => a.cmp(b),
        _ => a.to_bigint().cmp(&b.to_bigint()),
    }
}

fn int_sign(a: &Value) -> Ordering {
    match a {
        Value::Int(a) => a.cmp(&0),
        Value::BigInt(a) => match a.sign() {
            Sign::Minus => Ordering::Less,
            Sign::NoSign => Ordering::Equal,
            Sign::Plus => Ordering::Greater,
        },
        other => panic!("internal error: expected an `Int`, got {other:?}"),
    }
}

fn nat_add(a: &Value, b: &Value) -> Value {
    if let (Value::Nat(x), Value::Nat(y)) = (a, b)
        && let Some(z) = x.checked_add(*y)
    {
        return Value::Nat(z);
    }
    Value::nat(a.to_biguint() + b.to_biguint())
}

fn nat_sub(a: &Value, b: &Value) -> Value {
    if let (Value::Nat(x), Value::Nat(y)) = (a, b) {
        return Value::Nat(x.saturating_sub(*y));
    }
    let (x, y) = (a.to_biguint(), b.to_biguint());
    if x >= y {
        Value::nat(x - y)
    } else {
        Value::Nat(0)
    }
}

fn nat_mul(a: &Value, b: &Value) -> Value {
    if let (Value::Nat(x), Value::Nat(y)) = (a, b)
        && let Some(z) = x.checked_mul(*y)
    {
        return Value::Nat(z);
    }
    Value::nat(a.to_biguint() * b.to_biguint())
}

/// `divFuel fuel n d`: `min fuel (n / d)`, or `fuel` if `d` is zero.
fn div_fuel(fuel: &Value, n: &Value, d: &Value) -> Value {
    if let (Value::Nat(f), Value::Nat(n), Value::Nat(d)) = (fuel, n, d) {
        return Value::Nat(if *d == 0 { *f } else { (*f).min(n / d) });
    }
    let (f, n, d) = (fuel.to_biguint(), n.to_biguint(), d.to_biguint());
    Value::nat(if d == BigUint::ZERO { f } else { f.min(n / d) })
}

fn nat_to_int(n: &Value) -> Value {
    match n {
        Value::Nat(n) => match i64::try_from(*n) {
            Ok(i) => Value::Int(i),
            Err(_) => Value::BigInt(Rc::new(BigInt::from(*n))),
        },
        Value::BigNat(n) => Value::BigInt(Rc::new(BigInt::from((**n).clone()))),
        other => panic!("internal error: expected a `Nat`, got {other:?}"),
    }
}

/// `NegSucc n`: `-n - 1`.
fn neg_succ(n: &Value) -> Value {
    if let Value::Nat(n) = n
        && let Ok(i) = i64::try_from(*n)
    {
        return Value::Int(-i - 1);
    }
    Value::int(-BigInt::from(n.to_biguint()) - 1)
}

/// An `Int` that isn't negative, as a `Nat`.
pub fn int_to_nat(a: &Value) -> Value {
    match a {
        Value::Int(i) => Value::Nat(u64::try_from(*i).expect("not negative")),
        Value::BigInt(i) => Value::nat(i.to_biguint().expect("not negative")),
        other => panic!("internal error: expected an `Int`, got {other:?}"),
    }
}

/// `-a - 1` of a negative `Int`, as a `Nat`.
pub fn int_neg_succ(a: &Value) -> Value {
    match a {
        // `-a - 1` of a negative `i64` always fits.
        Value::Int(i) => Value::Nat(u64::try_from(-(i + 1)).expect("negative")),
        Value::BigInt(i) => {
            let m: BigInt = -&**i - 1;
            Value::nat(m.to_biguint().expect("negative"))
        }
        other => panic!("internal error: expected an `Int`, got {other:?}"),
    }
}

fn int_abs_nat(a: &Value) -> Value {
    match a {
        Value::Int(i) => Value::Nat(i.unsigned_abs()),
        other => Value::nat(other.to_bigint().magnitude().clone()),
    }
}

/// A binary `Int` operation: on `i64`s if `small` gives a result, otherwise
/// on `BigInt`s.
fn int2(
    a: &Value,
    b: &Value,
    small: impl FnOnce(i64, i64) -> Option<i64>,
    big: impl FnOnce(BigInt, BigInt) -> BigInt,
) -> Value {
    if let (Value::Int(x), Value::Int(y)) = (a, b)
        && let Some(z) = small(*x, *y)
    {
        return Value::Int(z);
    }
    Value::int(big(a.to_bigint(), b.to_bigint()))
}

/// Euclidean division of `a` by `d` (not zero): the remainder is never
/// negative.
fn euclid(a: &BigInt, d: &BigInt) -> (BigInt, BigInt) {
    let (q, r) = (a / d, a % d);
    if r.sign() == Sign::Minus {
        if d.sign() == Sign::Plus {
            (q - 1, r + d)
        } else {
            (q + 1, r - d)
        }
    } else {
        (q, r)
    }
}

/// Division of `a` by `d` (not zero) rounding down.
fn floor(a: &BigInt, d: &BigInt) -> (BigInt, BigInt) {
    let (q, r) = (a / d, a % d);
    if r.sign() != Sign::NoSign && (r.sign() == Sign::Minus) != (d.sign() == Sign::Minus) {
        (q - 1, r + d)
    } else {
        (q, r)
    }
}

fn floor_small(a: i64, d: i64) -> Option<(i64, i64)> {
    let (q, r) = (a.checked_div(d)?, a.checked_rem(d)?);
    if r != 0 && (r < 0) != (d < 0) {
        Some((q - 1, r + d))
    } else {
        Some((q, r))
    }
}

/// `Text.toNat`'s digits, and `Text.toInt`'s after an optional `-`.
fn digits(t: &str) -> Option<&str> {
    (!t.is_empty() && t.bytes().all(|b| b.is_ascii_digit())).then_some(t)
}

fn parse_nat(d: &str) -> Value {
    match d.parse::<u64>() {
        Ok(n) => Value::Nat(n),
        Err(_) => Value::nat(d.parse().expect("digits")),
    }
}

/// The byte offset in `t` after its first `n` characters (scalar values),
/// or `None` if `t` has `n` characters or fewer. A `Nat` beyond a machine
/// word is more than any text's length.
fn char_boundary(t: &str, n: &Value) -> Option<usize> {
    let n = match n {
        Value::Nat(n) => usize::try_from(*n).unwrap_or(usize::MAX),
        _ => usize::MAX,
    };
    // A character is at least one byte.
    if n >= t.len() {
        return None;
    }
    t.char_indices().nth(n).map(|(i, _)| i)
}

fn nat_to_text(n: &Value) -> Value {
    Value::Text(match n {
        Value::Nat(n) => n.to_string().into(),
        other => other.to_biguint().to_string().into(),
    })
}

/// Computes native operation `op` (not `Text.fold`) on `args`.
pub fn eval(s: &Shapes, op: PrimOp, args: &[&Value]) -> Value {
    match op {
        PrimOp::Nat(n) => match n {
            Native::Add => nat_add(args[0], args[1]),
            Native::Sub => nat_sub(args[0], args[1]),
            Native::Mul => nat_mul(args[0], args[1]),
            Native::Leq => boolean(s, nat_cmp(args[0], args[1]) != Ordering::Greater),
            Native::EqNat => boolean(s, num_eq(args[0], args[1])),
            Native::DecEqNat => decision(s, num_eq(args[0], args[1])),
            Native::DivFuel => div_fuel(args[0], args[1], args[2]),
            Native::EqNatRefl | Native::EqNatSound => Value::Erased,
        },
        PrimOp::NegSucc => neg_succ(args[0]),
        PrimOp::IntEqual => boolean(s, num_eq(args[0], args[1])),
        PrimOp::TextEqual => boolean(s, text_of(args[0]) == text_of(args[1])),
        PrimOp::Int(i) => int(s, op, i, args),
        PrimOp::Float(f) => float(s, f, args),
        PrimOp::Text(t) => text(s, op, t, args),
        PrimOp::Delay(p) => {
            let a = || args[0].clone();
            let b = || args[1].clone();
            match p {
                Primitive::Now => Value::Delay(Rc::new(Delay::Now(a()))),
                Primitive::Lift => Value::Delay(Rc::new(Delay::Lift(a()))),
                Primitive::BindD => Value::Delay(Rc::new(Delay::Bind(a(), b()))),
                Primitive::MapSig => Value::Delay(Rc::new(Delay::Map(a(), b()))),
                Primitive::Pfix => Value::Delay(Rc::new(Delay::Pfix(a(), b()))),
                // The type: erased.
                Primitive::Delay => Value::Erased,
                Primitive::FoldD => Value::Delay(Rc::new(Delay::Fold(a(), b(), args[2].clone()))),
            }
        }
        PrimOp::Effect(op) => {
            unreachable!("the machine runs the effect runtime's {op:?} on its frames")
        }
    }
}

/// A `Float` operation (docs/proposals/float.md §3.3): IEEE 754 doubles,
/// every result made canonical by [`Value::float`], so that bits, `==` and
/// the NaN agree with the kernel's model.
fn float(s: &Shapes, f: FloatPrim, args: &[&Value]) -> Value {
    use stitchwort_core::float::{
        FloatOp, canonical_bits, int_to_f64, js_to_string, nat_to_f64, to_int, total_order,
    };
    let x = |i: usize| args[i].to_f64();
    match f {
        FloatPrim::Add => Value::float(FloatOp::Add.apply(x(0), x(1))),
        FloatPrim::Sub => Value::float(FloatOp::Sub.apply(x(0), x(1))),
        FloatPrim::Mul => Value::float(FloatOp::Mul.apply(x(0), x(1))),
        FloatPrim::Div => Value::float(FloatOp::Div.apply(x(0), x(1))),
        FloatPrim::Rem => Value::float(FloatOp::Rem.apply(x(0), x(1))),
        FloatPrim::Floor => Value::float(FloatOp::Floor.apply_unary(x(0))),
        FloatPrim::Ceil => Value::float(FloatOp::Ceil.apply_unary(x(0))),
        FloatPrim::Trunc => Value::float(FloatOp::Trunc.apply_unary(x(0))),
        FloatPrim::Round => Value::float(FloatOp::Round.apply_unary(x(0))),
        FloatPrim::OfInt => Value::float(match args[0] {
            Value::Int(n) => int_to_f64(&BigInt::from(*n)),
            Value::BigInt(n) => int_to_f64(n),
            other => bad(PrimOp::Float(f), other),
        }),
        FloatPrim::OfNat => Value::float(nat_to_f64(&args[0].to_biguint())),
        FloatPrim::ToText => Value::Text(js_to_string(x(0)).into()),
        FloatPrim::IsFinite => boolean(s, x(0).is_finite()),
        FloatPrim::IeeeLt => boolean(s, x(0) < x(1)),
        FloatPrim::IeeeLe => boolean(s, x(0) <= x(1)),
        FloatPrim::ToInt => match to_int(canonical_bits(x(0))) {
            None => Value::Tag(s.none),
            Some(n) => some(s, Value::int(n)),
        },
        FloatPrim::Compare => ordering(total_order(canonical_bits(x(0)), canonical_bits(x(1)))),
        // Rust's `-NaN` has the sign bit set: the NaN stays the NaN.
        FloatPrim::Neg => Value::float(-x(0)),
        FloatPrim::Abs => Value::float(x(0).abs()),
        FloatPrim::IsNaN => boolean(s, x(0).is_nan()),
        FloatPrim::DecEq => decision(s, canonical_bits(x(0)) == canonical_bits(x(1))),
        FloatPrim::IeeeEq => boolean(s, x(0) == x(1)),
        FloatPrim::FromBits => {
            let bits = match args[0] {
                Value::Nat(n) => *n,
                other => bad(PrimOp::Float(f), other),
            };
            Value::float(f64::from_bits(bits))
        }
        FloatPrim::Bits => Value::Nat(canonical_bits(x(0))),
    }
}

fn int(s: &Shapes, op: PrimOp, i: IntNative, args: &[&Value]) -> Value {
    use IntNative::*;
    let a = args[0];
    match i {
        NatToInt => nat_to_int(a),
        IntNeg => match a {
            Value::Int(x) if *x != i64::MIN => Value::Int(-x),
            _ => Value::int(-a.to_bigint()),
        },
        IntAdd => int2(a, args[1], i64::checked_add, |x, y| x + y),
        IntSub => int2(a, args[1], i64::checked_sub, |x, y| x - y),
        IntMul => int2(a, args[1], i64::checked_mul, |x, y| x * y),
        IntDiv => int2(a, args[1], i64::checked_div_euclid, |x, y| euclid(&x, &y).0),
        IntMod => int2(a, args[1], i64::checked_rem_euclid, |x, y| euclid(&x, &y).1),
        IntTDiv => int2(a, args[1], i64::checked_div, |x, y| x / y),
        IntTMod => int2(a, args[1], i64::checked_rem, |x, y| x % y),
        IntFDiv => int2(
            a,
            args[1],
            |x, y| Some(floor_small(x, y)?.0),
            |x, y| floor(&x, &y).0,
        ),
        IntFMod => int2(
            a,
            args[1],
            |x, y| Some(floor_small(x, y)?.1),
            |x, y| floor(&x, &y).1,
        ),
        IntModNat => {
            if let (Value::Int(x), Value::Nat(d)) = (a, args[1])
                && let Ok(d) = i64::try_from(*d)
                && let Some(r) = x.checked_rem_euclid(d)
            {
                return Value::Nat(u64::try_from(r).expect("not negative"));
            }
            let d = BigInt::from(args[1].to_biguint());
            Value::nat(
                euclid(&a.to_bigint(), &d)
                    .1
                    .to_biguint()
                    .expect("not negative"),
            )
        }
        DecEqInt => decision(s, num_eq(a, args[1])),
        IntLeq => boolean(s, int_cmp(a, args[1]) != Ordering::Greater),
        IntLess => boolean(s, int_cmp(a, args[1]) == Ordering::Less),
        IntCompare => ordering(int_cmp(a, args[1])),
        IntNatAbs => int_abs_nat(a),
        IntAbs => match a {
            Value::Int(x) if *x != i64::MIN => Value::Int(x.abs()),
            _ => Value::int(BigInt::from(a.to_bigint().magnitude().clone())),
        },
        IntToNat => {
            if int_sign(a) == Ordering::Less {
                Value::Nat(0)
            } else {
                int_to_nat(a)
            }
        }
        IntToNatChecked => {
            if int_sign(a) == Ordering::Less {
                Value::Tag(s.none)
            } else {
                some(s, int_to_nat(a))
            }
        }
        IntSign => Value::Int(match int_sign(a) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }),
        IntToText => Value::Text(match a {
            Value::Int(x) => x.to_string().into(),
            Value::BigInt(x) => x.to_string().into(),
            other => bad(op, other),
        }),
        TextToInt => {
            let t = text_of(a);
            let (negative, rest) = match t.strip_prefix('-') {
                Some(rest) => (true, rest),
                None => (false, &t[..]),
            };
            match digits(rest) {
                None => Value::Tag(s.none),
                Some(d) => {
                    let n = parse_nat(d);
                    let n = nat_to_int(&n);
                    some(
                        s,
                        if negative {
                            int(s, op, IntNeg, &[&n])
                        } else {
                            n
                        },
                    )
                }
            }
        }
    }
}

fn text(s: &Shapes, op: PrimOp, t: TextNative, args: &[&Value]) -> Value {
    use TextNative::*;
    match t {
        TextToList => chars(s, text_of(args[0])),
        TextFromList => {
            let out: String = items(s, args[0]).map(char_of).collect();
            Value::Text(out.into())
        }
        TextAppend => {
            let (a, b) = (text_of(args[0]), text_of(args[1]));
            if a.is_empty() {
                return args[1].clone();
            }
            if b.is_empty() {
                return args[0].clone();
            }
            let mut out = String::with_capacity(a.len() + b.len());
            out.push_str(a);
            out.push_str(b);
            Value::Text(out.into())
        }
        TextLength => Value::Nat(text_of(args[0]).chars().count() as u64),
        TextIsEmpty => boolean(s, text_of(args[0]).is_empty()),
        DecEqText => decision(s, text_of(args[0]) == text_of(args[1])),
        // UTF-8 orders bytes as the characters they encode.
        TextCompare => ordering(text_of(args[0]).as_bytes().cmp(text_of(args[1]).as_bytes())),
        TextUncons => {
            let t = text_of(args[0]);
            let mut it = t.chars();
            match it.next() {
                None => Value::Tag(s.none),
                Some(c) => some(
                    s,
                    Value::data(s.pair, [char_value(s, c), Value::Text(it.as_str().into())]),
                ),
            }
        }
        TextTrim => {
            let space = char::is_whitespace;
            let t = text_of(args[0]);
            let trimmed = t.trim_matches(space);
            if trimmed.len() == t.len() {
                args[0].clone()
            } else {
                Value::Text(trimmed.into())
            }
        }
        // The first `n` characters (scalar values), or the whole text.
        // `Text.take text n`.
        TextTake => {
            let t = text_of(args[0]);
            match char_boundary(t, args[1]) {
                Some(end) => Value::Text(t[..end].into()),
                None => args[0].clone(),
            }
        }
        // The text after its first `n` characters, or the empty text.
        TextDrop => {
            let t = text_of(args[0]);
            match char_boundary(t, args[1]) {
                Some(0) => args[0].clone(),
                Some(start) => Value::Text(t[start..].into()),
                None => Value::Text("".into()),
            }
        }
        // `Text.contains text needle`. UTF-8 is self-synchronising: a match
        // of a needle's bytes starts and ends between characters, so byte
        // search finds exactly the character matches. The empty needle
        // occurs in every text.
        TextContains => boolean(s, text_of(args[0]).contains(&**text_of(args[1]))),
        // `Text.split text separator`.
        TextSplit => {
            let sep = char_of(args[1]);
            let parts = text_of(args[0])
                .split(sep)
                .map(|p| Value::Text(p.into()))
                .collect();
            list(s, parts)
        }
        // `Text.join texts separator`.
        TextJoin => {
            let sep = char_of(args[1]);
            let mut out = String::new();
            for (i, part) in items(s, args[0]).enumerate() {
                if i > 0 {
                    out.push(sep);
                }
                out.push_str(text_of(part));
            }
            Value::Text(out.into())
        }
        NatToText => nat_to_text(args[0]),
        TextToNat => match digits(text_of(args[0])) {
            None => Value::Tag(s.none),
            Some(d) => some(s, parse_nat(d)),
        },
        TextFold => bad(op, args[0]),
    }
}

/// A `Nat` against a number switch's small and big arms: the target.
pub fn num_switch(table: &crate::code::NumTable, v: &Value) -> u32 {
    match v {
        Value::Nat(n) => table
            .small
            .iter()
            .find(|(k, _)| k == n)
            .map_or(table.default, |(_, t)| *t),
        Value::BigNat(n) => table
            .big
            .iter()
            .find(|(k, _)| k == &**n)
            .map_or(table.default, |(_, t)| *t),
        other => panic!("internal error: a number switch on {other:?}"),
    }
}
