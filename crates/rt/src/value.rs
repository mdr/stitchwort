//! The machine's values (docs/proposals/fast-runtime.md §2.3, §2.4).
//!
//! - Numbers are inline when they fit a machine word (`Nat` in a `u64`,
//!   `Int` in an `i64`), and a `BigUint` or `BigInt` otherwise. Each number
//!   has exactly one form (a number that fits is never big), so equality
//!   is structural.
//! - A constructor without runtime fields (`Nil`, `True`, `None`, a `Yes`
//!   whose proof is erased) is just its tag: no allocation. One with fields
//!   is its tag and one reference-counted array of them.
//! - Text is a reference-counted string.
//! - Freeing never recurses: dropping the last reference to a long list (or
//!   a long chain of closures) frees it with a work list (`Drop` for
//!   [`Fields`], [`Fun`] and [`Delay`]).

use std::rc::Rc;

use num_bigint::{BigInt, BigUint};

/// A runtime value.
#[derive(Clone, Debug, Default)]
pub enum Value {
    /// What stands for an erased value (a proof or a type).
    #[default]
    Erased,
    /// A `Nat` that fits in a `u64`.
    Nat(u64),
    /// A `Nat` that doesn't.
    BigNat(Rc<BigUint>),
    /// An `Int` that fits in an `i64`.
    Int(i64),
    /// An `Int` that doesn't.
    BigInt(Rc<BigInt>),
    Text(Rc<str>),
    /// A `Float`: a double, with every NaN the one NaN (D701). Made only by
    /// [`Value::float`].
    Float(f64),
    /// A constructor without runtime fields: its tag.
    Tag(u32),
    /// A constructor with runtime fields (at least one).
    Data(u32, Fields),
    /// A function value.
    Fun(Rc<Fun>),
    /// A partial computation, which only the runner looks inside.
    Delay(Rc<Delay>),
}

/// A constructor's runtime fields.
#[derive(Clone, Debug)]
pub struct Fields(pub Rc<[Value]>);

impl std::ops::Deref for Fields {
    type Target = [Value];
    fn deref(&self) -> &[Value] {
        &self.0
    }
}

/// A function value.
#[derive(Debug)]
pub enum Fun {
    /// A global function, or a native operation, with none of its arguments.
    Global(u32),
    /// A lambda's code with the values it captured.
    Closure { lambda: u32, captures: Box<[Value]> },
    /// `head` (a `Global` or a `Closure`) with some of its arguments, fewer
    /// than it takes.
    Pap { head: Value, args: Box<[Value]> },
    /// `y => Done y`.
    DoneK,
    /// A resumption of the effect runtime ([`crate::effect`]): if the flag
    /// is set, calling it suspends (gives `Bind (Done y) r`, `r` the same
    /// resumption unflagged); otherwise it runs the rest of the computation.
    Resume(Rc<crate::effect::Resume>, bool),
    /// A state-passing handler's function of the state ([`crate::effect`],
    /// stage 4d): given the state, runs the handler's loop.
    StateRun(Rc<crate::effect::StateRun>),
    /// A state-passing handler's `k`, for every use that isn't a tail
    /// resumption: the state's function from where the operation was
    /// (`Done` of it if the handler's carrier is a computation).
    StateK(Rc<crate::effect::Resume>),
    /// `jump v s`, given to a state-passing handler's clauses: records `v`
    /// and `s` as a [`Fun::Jumped`] for the loop.
    JumpK,
    /// What `jump v s` returns: never applied, only recognised by the loop
    /// it returns to.
    Jumped(Value, Value),
}

/// A partial computation: one of `Delay`'s constants with its runtime
/// arguments (docs/proposals/partial.md §7.4). Building one runs nothing.
#[derive(Debug)]
pub enum Delay {
    Now(Value),
    Lift(Value),
    Bind(Value, Value),
    /// `mapSig m d`: `m` is `MkSigMap inject reply`.
    Map(Value, Value),
    Pfix(Value, Value),
}

impl Value {
    /// A constructor with tag `tag` and these runtime fields: one
    /// allocation.
    pub fn data<const N: usize>(tag: u32, fields: [Value; N]) -> Value {
        if N == 0 {
            Value::Tag(tag)
        } else {
            Value::Data(tag, Fields(Rc::from(fields)))
        }
    }

    /// The same, with the fields in a vector.
    pub fn data_vec(tag: u32, fields: Vec<Value>) -> Value {
        if fields.is_empty() {
            Value::Tag(tag)
        } else {
            Value::Data(tag, Fields(fields.into()))
        }
    }

    /// The constructor's tag, for a constructor.
    #[inline]
    pub fn tag(&self) -> Option<u32> {
        match self {
            Value::Tag(t) | Value::Data(t, _) => Some(*t),
            _ => None,
        }
    }

    /// A `Nat`, in its one form.
    pub fn nat(n: BigUint) -> Value {
        match u64::try_from(&n) {
            Ok(small) => Value::Nat(small),
            Err(_) => Value::BigNat(Rc::new(n)),
        }
    }

    /// An `Int`, in its one form.
    pub fn int(n: BigInt) -> Value {
        match i64::try_from(&n) {
            Ok(small) => Value::Int(small),
            Err(_) => Value::BigInt(Rc::new(n)),
        }
    }

    /// A `Float`, with a NaN made the one NaN, `0x7FF8000000000000`
    /// (docs/proposals/float.md §3.5, D701): so the bits of every `Float`
    /// value are canonical, and `.bits`, `==` and hashing can use them.
    #[inline]
    pub fn float(x: f64) -> Value {
        Value::Float(if x.is_nan() {
            f64::from_bits(stitchwort_core::float::NAN)
        } else {
            x
        })
    }

    /// A `Float` value's double.
    pub fn to_f64(&self) -> f64 {
        match self {
            Value::Float(x) => *x,
            other => panic!("internal error: expected a `Float`, got {other:?}"),
        }
    }

    /// A `Nat` value as a `BigUint`.
    pub fn to_biguint(&self) -> BigUint {
        match self {
            Value::Nat(n) => BigUint::from(*n),
            Value::BigNat(n) => (**n).clone(),
            other => panic!("internal error: expected a `Nat`, got {other:?}"),
        }
    }

    /// An `Int` value as a `BigInt`.
    pub fn to_bigint(&self) -> BigInt {
        match self {
            Value::Int(n) => BigInt::from(*n),
            Value::BigInt(n) => (**n).clone(),
            other => panic!("internal error: expected an `Int`, got {other:?}"),
        }
    }

    /// Whether dropping it does anything: it holds a reference.
    #[inline]
    pub fn owns(&self) -> bool {
        !matches!(
            self,
            Value::Erased | Value::Nat(_) | Value::Int(_) | Value::Float(_) | Value::Tag(_)
        )
    }

    /// Whether it may own other values that dropping it could free.
    #[inline]
    fn is_deep(&self) -> bool {
        matches!(self, Value::Data(..) | Value::Fun(_) | Value::Delay(_))
    }
}

// ------------------------------------------------------------- freeing

/// Moves the values `v` owns, if it's their only owner, into `out`, so
/// that dropping `v` frees nothing more than itself.
fn take_children(v: &mut Value, out: &mut Vec<Value>) {
    match v {
        Value::Data(_, fields) => {
            if let Some(slice) = Rc::get_mut(&mut fields.0) {
                take_from(slice, out);
            }
        }
        Value::Fun(f) => {
            if let Some(f) = Rc::get_mut(f) {
                f.take_children(out);
            }
        }
        Value::Delay(d) => {
            if let Some(d) = Rc::get_mut(d) {
                d.take_children(out);
            }
        }
        _ => {}
    }
}

pub(crate) fn take_from(values: &mut [Value], out: &mut Vec<Value>) {
    for v in values {
        if v.is_deep() {
            out.push(std::mem::take(v));
        }
    }
}

/// Frees what `pending` holds without recursing: each value's children are
/// moved out before it's dropped.
fn free(mut pending: Vec<Value>) {
    while let Some(mut v) = pending.pop() {
        take_children(&mut v, &mut pending);
    }
}

impl Fun {
    fn take_children(&mut self, out: &mut Vec<Value>) {
        match self {
            Fun::Global(_) | Fun::DoneK | Fun::JumpK => {}
            Fun::StateRun(run) => {
                if let Some(run) = Rc::get_mut(run) {
                    run.take_children(out);
                }
            }
            Fun::Jumped(v, s) => {
                take_from(std::slice::from_mut(v), out);
                take_from(std::slice::from_mut(s), out);
            }
            Fun::Resume(resume, _) | Fun::StateK(resume) => {
                if let Some(resume) = Rc::get_mut(resume) {
                    resume.take_children(out);
                }
            }
            Fun::Closure { captures, .. } => take_from(captures, out),
            Fun::Pap { head, args } => {
                take_from(std::slice::from_mut(head), out);
                take_from(args, out);
            }
        }
    }
}

impl Delay {
    fn take_children(&mut self, out: &mut Vec<Value>) {
        match self {
            Delay::Now(a) | Delay::Lift(a) => take_from(std::slice::from_mut(a), out),
            Delay::Bind(a, b) | Delay::Map(a, b) | Delay::Pfix(a, b) => {
                take_from(std::slice::from_mut(a), out);
                take_from(std::slice::from_mut(b), out);
            }
        }
    }
}

impl Drop for Fields {
    fn drop(&mut self) {
        if let Some(slice) = Rc::get_mut(&mut self.0) {
            let mut pending = Vec::new();
            take_from(slice, &mut pending);
            free(pending);
        }
    }
}

impl Drop for Fun {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.take_children(&mut pending);
        free(pending);
    }
}

impl Drop for Delay {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.take_children(&mut pending);
        free(pending);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_value_is_three_words() {
        assert_eq!(std::mem::size_of::<Value>(), 24);
    }

    /// D701: every NaN, of any sign and payload, is stored as the one NaN;
    /// every other double is kept bit for bit, `-0.0` included.
    #[test]
    fn a_float_is_canonical() {
        let bits = |v: Value| v.to_f64().to_bits();
        let nan = stitchwort_core::float::NAN;
        for payload in [
            0x7FF8_0000_0000_0000u64,
            0xFFF8_0000_0000_0000,
            0x7FF0_0000_0000_0001,
            0xFFF0_0000_0000_0001,
            0x7FFF_FFFF_FFFF_FFFF,
            0xFFFF_FFFF_FFFF_FFFF,
        ] {
            assert_eq!(
                bits(Value::float(f64::from_bits(payload))),
                nan,
                "{payload:#x}"
            );
        }
        assert_eq!(bits(Value::float(-f64::NAN)), nan);
        assert_eq!(bits(Value::float(f64::INFINITY - f64::INFINITY)), nan);
        for kept in [
            0u64,
            1 << 63,
            1,
            0x3FF0_0000_0000_0000,
            0xFFF0_0000_0000_0000,
        ] {
            assert_eq!(bits(Value::float(f64::from_bits(kept))), kept, "{kept:#x}");
        }
    }

    #[test]
    fn numbers_have_one_form() {
        assert!(matches!(
            Value::nat(BigUint::from(u64::MAX)),
            Value::Nat(u64::MAX)
        ));
        assert!(matches!(
            Value::nat(BigUint::from(u64::MAX) + 1u32),
            Value::BigNat(_)
        ));
        assert!(matches!(
            Value::int(BigInt::from(i64::MIN)),
            Value::Int(i64::MIN)
        ));
        assert!(matches!(
            Value::int(BigInt::from(i64::MIN) - 1),
            Value::BigInt(_)
        ));
    }

    /// Dropping a long list, or a long chain of closures, doesn't recurse.
    #[test]
    fn a_long_list_is_freed_without_recursing() {
        let mut list = Value::Tag(0);
        for i in 0..2_000_000u64 {
            list = Value::data(1, [Value::Nat(i), list]);
        }
        drop(list);
        let mut f = Value::Fun(Rc::new(Fun::DoneK));
        for _ in 0..2_000_000u64 {
            f = Value::Fun(Rc::new(Fun::Closure {
                lambda: 0,
                captures: vec![f].into(),
            }));
        }
        drop(f);
    }
}
