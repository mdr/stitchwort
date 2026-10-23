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
//! - **Primitives** ([`FloatOp`]): `Float.add` and `Float.sub`, the rounding
//!   operations, which have no body. They're admitted here once their types
//!   are checked to be exactly `Float -> Float -> Float`, as `Delay`'s
//!   constants are (`partial.rs`). Applied to two records whose bits are
//!   known, the evaluator computes the result with Rust's `f64` and returns
//!   `{ bits = k, valid = Eq.refl True }`, the NaN made canonical; otherwise
//!   the application is stuck, and conversion compares it structurally. This
//!   reduction rule is part of evaluation, always on: it isn't a native, so
//!   switching the natives off doesn't change it (a primitive has no
//!   definition to fall back to).
//! - **Natives** ([`FloatNative`]): `neg`, `abs`, `isNaN` and `Float.decEq`,
//!   ordinary definitions over the bits with an implementation here. As for
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

use num_traits::ToPrimitive;
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
        "25a1ae74c7488e63592d578fae986c9ff61595e12c736787de0bd93f7ee9b257",
    ),
    (
        Builtin::FloatAbs,
        "ac1b9102c965182365d17c342fae88250579d2f4e9d7fdf281641d05453e8c52",
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

/// A primitive: a rounding operation without a definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FloatOp {
    Add,
    Sub,
}

impl FloatOp {
    pub const ALL: [FloatOp; 2] = [FloatOp::Add, FloatOp::Sub];

    /// Its name in the library.
    pub fn name(self) -> &'static str {
        self.builtin().name()
    }

    pub fn builtin(self) -> Builtin {
        match self {
            FloatOp::Add => Builtin::FloatAdd,
            FloatOp::Sub => Builtin::FloatSub,
        }
    }

    pub fn named(name: &str) -> Option<FloatOp> {
        FloatOp::ALL.into_iter().find(|op| op.name() == name)
    }

    /// The operation on doubles: IEEE 754 binary64, rounding to nearest,
    /// ties to even (the contract's conditions C1-C6). The caller makes a
    /// NaN result canonical.
    pub fn apply(self, a: f64, b: f64) -> f64 {
        match self {
            FloatOp::Add => a + b,
            FloatOp::Sub => a - b,
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
}

impl FloatNative {
    pub const ALL: [FloatNative; 4] = [
        FloatNative::Neg,
        FloatNative::Abs,
        FloatNative::IsNaN,
        FloatNative::DecEq,
    ];

    pub fn builtin(self) -> Builtin {
        match self {
            FloatNative::Neg => Builtin::FloatNeg,
            FloatNative::Abs => Builtin::FloatAbs,
            FloatNative::IsNaN => Builtin::FloatIsNaN,
            FloatNative::DecEq => Builtin::FloatDecEq,
        }
    }

    pub fn name(self) -> &'static str {
        self.builtin().name()
    }

    pub fn arity(self) -> usize {
        match self {
            FloatNative::DecEq => 2,
            _ => 1,
        }
    }

    /// The native on bits: the result's bits, for those returning a `Float`.
    pub fn on_bits(self, bits: u64) -> u64 {
        match self {
            FloatNative::Neg if bits == NAN => NAN,
            FloatNative::Neg => bits ^ SIGN,
            FloatNative::Abs => bits & !SIGN,
            FloatNative::IsNaN | FloatNative::DecEq => {
                unreachable!("`{}` doesn't return a `Float`", self.name())
            }
        }
    }
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

/// Admits pending definition `id`, declared with only a signature, as
/// primitive `op`: final, with no body. Its type must be exactly `Float ->
/// Float -> Float`, for the bound `Float`.
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
    let arrow =
        |dom: Term, cod: Term| Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod));
    let taken = g
        .builtins
        .float_defs
        .values()
        .any(|d| *d == FloatDef::Primitive(op));
    let fits = !taken
        && match float_ty(g) {
            Some(f) => {
                let expected = arrow(f.clone(), arrow(f.clone(), f));
                conv(g, 0, &eval(g, &[], &expected)?, &def.ty_value)?
            }
            None => false,
        };
    if !fits {
        let e = Diagnostic::error(
            "E-BUILTIN",
            format!(
                "the library's `{}` doesn't have the type the compiler expects, `Float -> Float -> Float`",
                op.name()
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
        FloatDef::Primitive(_) => 2,
        FloatDef::Native(n) => n.arity(),
    };
    if spine.len() != arity {
        return Ok(None);
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
    Ok(match def {
        FloatDef::Primitive(op) => {
            let r = op.apply(f64::from_bits(bits[0]), f64::from_bits(bits[1]));
            Some(float_value(data, canonical_bits(r)))
        }
        FloatDef::Native(FloatNative::IsNaN) => g
            .builtins
            .bool
            .map(|b| Value::Ctor(b, usize::from(bits[0] == NAN), [].into())),
        FloatDef::Native(FloatNative::DecEq) => dec_eq(g, &args, bits[0], bits[1]),
        FloatDef::Native(n) => Some(float_value(data, n.on_bits(bits[0]))),
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
