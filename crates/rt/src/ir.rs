//! The erased IR (docs/proposals/fast-runtime.md, stage 1): a checked
//! program with its types and proofs gone, ready to be run.
//!
//! - **Erased.** Types, proofs and the arguments for erased parameters are
//!   gone. Where an erased value must still be passed (to a function value,
//!   whose parameters are all kept), it's [`Expr::Erased`].
//! - **Globals.** Each definition a program uses is a [`Global`]: a function
//!   of its runtime parameters, a constant (no runtime parameters, computed
//!   when first used), or a native operation.
//! - **Saturated calls.** A call to a known global with all its runtime
//!   arguments is [`Expr::Call`] (or [`Expr::Prim`] for a native); with
//!   fewer, [`Expr::PartialApp`]; with more, an [`Expr::Apply`] of the call
//!   to the rest. Only calls of function values are [`Expr::Apply`], which
//!   handles too few or too many arguments at run time (eval/apply).
//! - **Closures.** Each lambda (consecutive lambdas together) is a
//!   [`Lambda`] with its parameters and the variables it captures, made by
//!   [`Expr::Closure`] from the slots of the frame that makes it.
//! - **Slots.** Variables are numbered slots of the current frame
//!   ([`Expr::Local`]): a function's or lambda's parameters first, then its
//!   local variables. A lambda reads what it captured as [`Expr::Captured`].
//! - **Matching.** A `match` is a switch on the constructor
//!   ([`Expr::Match`]), binding the fields a branch uses to slots. `Nat`,
//!   `Int` and `Text` are native values, matched as numbers and strings
//!   ([`MatchKind`]). `if` is [`Expr::If`].

use std::rc::Rc;

use num_bigint::BigInt;
use stitchwort_core::partial::Primitive;
use stitchwort_core::{BigUint, DataId, DefId, native};

use crate::natives::{IntNative, TextNative};

/// A slot of a frame.
pub type Slot = u32;

/// A global's index in [`Program::globals`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GlobalId(pub u32);

/// A lambda's index in [`Program::lambdas`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LambdaId(pub u32);

/// A data type's index in [`Program::types`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

/// A lowered program: the globals and lambdas it uses, and what it runs.
pub struct Program {
    pub globals: Vec<Global>,
    pub lambdas: Vec<Lambda>,
    /// The data types whose values it builds or matches.
    pub types: Vec<TypeInfo>,
    /// What running the program computes: for a `main`, the partial
    /// computation `main ()` (a `Delay`) that the runner steps.
    pub entry: Body,
    /// The constructors the natives and the runner build and take apart.
    pub shapes: Shapes,
}

/// The constructors that natives build and the runner takes apart and
/// builds, as tags (a constructor's index in its type): found in the
/// checked program's prelude when it's lowered, each checked to have the
/// runtime fields the runtime expects. A constructor without runtime fields
/// is nullary at run time (`Yes`, whose proof is erased). `Ordering`'s
/// `LT`, `EQ`, `GT` are tags 0, 1, 2: the natives that build them are bound
/// to their prelude definitions by content hash ([`crate::natives`]).
#[derive(Clone, Copy, Debug)]
pub struct Shapes {
    /// `False`, `True`: no fields.
    pub false_: u32,
    pub true_: u32,
    /// `None`: no fields; `Some x`.
    pub none: u32,
    pub some: u32,
    /// `Yes`, `No`: no runtime fields (the proofs are erased).
    pub yes: u32,
    pub no: u32,
    /// `Nil`: no fields; `Cons x xs`.
    pub nil: u32,
    pub cons: u32,
    /// `MkPair a b`.
    pub pair: u32,
    /// `MkChar code` (its proof erased).
    pub char_: u32,
    /// The unit value: no fields.
    pub unit: u32,
    /// `Done x`, `Call op rest`.
    pub done: u32,
    pub call: u32,
    /// `L op`, `R op` of `Plus`.
    pub left: u32,
    pub right: u32,
    /// `Recur x`, a recursion request.
    pub recur: u32,
    /// `MkSigMap inject reply`.
    pub sig_map: u32,
    /// `IO`'s `%print text`, `%readLine u`, `%readAll u`.
    pub print: u32,
    pub read_line: u32,
    pub read_all: u32,
}

/// A body of code with its own frame.
#[derive(Clone, Debug)]
pub struct Body {
    /// How many slots its frame needs, parameters included.
    pub frame: u32,
    pub expr: Expr,
}

pub struct Global {
    /// The definition's full logical name, `Std.List.map`.
    pub name: Rc<str>,
    pub def: DefId,
    pub kind: GlobalKind,
}

pub enum GlobalKind {
    /// Takes `params` runtime arguments (at least one), in slots
    /// `0..params`.
    Function { params: u32, body: Body },
    /// Has no runtime parameters: computed when it's first used, and kept.
    Constant { body: Body },
    /// A native operation, as a value: what a reference to it, or a call
    /// with too few arguments, makes a function of.
    Native(PrimOp),
}

impl GlobalKind {
    /// How many runtime arguments a call passes.
    pub fn params(&self) -> u32 {
        match self {
            GlobalKind::Function { params, .. } => *params,
            GlobalKind::Constant { .. } => 0,
            GlobalKind::Native(op) => op.arity(),
        }
    }
}

/// The code of a closure. Its frame has its parameters in slots
/// `0..params`; what it captured is read with [`Expr::Captured`].
pub struct Lambda {
    pub params: u32,
    /// How many values it captures.
    pub captures: u32,
    pub body: Body,
}

/// A data type, for constructor names and field names.
pub struct TypeInfo {
    pub data: DataId,
    pub name: Rc<str>,
    /// A record: one constructor, matched without a tag test.
    pub record: bool,
    pub ctors: Vec<CtorInfo>,
}

pub struct CtorInfo {
    pub name: Rc<str>,
    /// The names of its runtime fields, in order: the erased ones are gone.
    pub fields: Vec<Rc<str>>,
}

#[derive(Clone, Debug)]
pub enum Expr {
    /// A slot of the current frame.
    Local(Slot),
    /// Value `i` that the current closure captured.
    Captured(u32),
    /// A global's value: a constant's value, or a function or native as a
    /// function value.
    Global(GlobalId),
    /// What stands for an erased value (a proof or a type) that must still
    /// be passed.
    Erased,
    Lit(Lit),
    /// `y => Done y`, the continuation of an operation or recursion request,
    /// as one value, so that the runner can tell a request in tail position.
    DoneK,
    /// A call of a global function (or constant) with all its runtime
    /// arguments.
    Call(GlobalId, Vec<Expr>),
    /// A native operation with all its arguments.
    Prim(PrimOp, Vec<Expr>),
    /// A global function with fewer than all its runtime arguments (at least
    /// one): a function value.
    PartialApp(GlobalId, Vec<Expr>),
    /// A function value applied to arguments (at least one).
    Apply(Box<Expr>, Vec<Expr>),
    /// A closure of a lambda, capturing these values.
    Closure(LambdaId, Vec<Expr>),
    /// A constructor with its runtime fields.
    Ctor(TypeId, u32, Vec<Expr>),
    /// `let slot = value; body`.
    Let(Slot, Box<Expr>, Box<Expr>),
    /// A switch on the constructor of `scrutinee` (a variable), one arm per
    /// constructor in order.
    Match(Box<Expr>, MatchKind, Vec<Arm>),
    /// `scrutinee` (a `Nat`) against numbers, in increasing order, or else
    /// the default.
    NumSwitch(Box<Expr>, Vec<(BigUint, Expr)>, Box<Expr>),
    /// A test of a `Bool`.
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// A branch no well-typed program reaches (an impossible case of an
    /// indexed family, or a match on a proposition without constructors).
    Unreachable,
}

/// What a [`Expr::Match`] takes apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatchKind {
    /// A data type's constructors.
    Data(TypeId),
    /// A native `Nat`: `Zero`, or `Succ` with the number one less.
    Nat,
    /// A native `Int`: `OfNat n` if it isn't negative (`n` is the number),
    /// `NegSucc n` if it is (`n` is `-x - 1`).
    Int,
    /// A native `Text`: `MkText` with its characters as a `List Char`.
    Text,
}

/// One constructor's arm of a [`Expr::Match`].
#[derive(Clone, Debug)]
pub struct Arm {
    /// The constructor's index.
    pub ctor: u32,
    /// The runtime fields the body uses: the field's index among the
    /// runtime fields, and the slot it's bound to.
    pub fields: Vec<(u32, Slot)>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Lit {
    /// A `Nat`.
    Nat(BigUint),
    /// An `Int`.
    Int(BigInt),
    /// A `Text`.
    Text(Rc<str>),
    /// A `List Char`, stored compactly: a text literal's characters.
    Chars(Rc<str>),
}

/// A native operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimOp {
    /// A kernel-native `Nat` operation (`stitchwort_core::native`); `Add`
    /// also builds `Succ`s around a number.
    Nat(native::Native),
    /// An `Int` operation; `NatToInt` is also `OfNat`.
    Int(IntNative),
    /// `NegSucc n`, which is `-n - 1`, for a native `Int`.
    NegSucc,
    /// `a == b` on native `Int`s, as a `Bool`: `toBool (Int.decEq a b)`.
    IntEqual,
    /// `a == b` on native `Text`s, as a `Bool`: `toBool (Text.decEq a b)`.
    TextEqual,
    /// A `Text` operation; `TextFromList` is also `MkText`, and
    /// `TextToList` takes it apart.
    Text(TextNative),
    /// One of `Delay`'s constants, building a partial computation that the
    /// runner steps (docs/proposals/partial.md §7.4).
    Delay(Primitive),
}

impl PrimOp {
    /// How many arguments it takes.
    pub fn arity(self) -> u32 {
        use native::Native;
        match self {
            PrimOp::Nat(Native::DivFuel | Native::EqNatSound) => 3,
            PrimOp::Nat(Native::EqNatRefl) => 1,
            PrimOp::Nat(_) => 2,
            PrimOp::Int(op) => match op {
                IntNative::NatToInt
                | IntNative::IntNeg
                | IntNative::IntNatAbs
                | IntNative::IntAbs
                | IntNative::IntToNat
                | IntNative::IntToNatChecked
                | IntNative::IntSign
                | IntNative::IntToText
                | IntNative::TextToInt => 1,
                _ => 2,
            },
            PrimOp::NegSucc => 1,
            PrimOp::IntEqual | PrimOp::TextEqual => 2,
            PrimOp::Text(op) => match op {
                TextNative::TextToList
                | TextNative::TextFromList
                | TextNative::TextLength
                | TextNative::TextIsEmpty
                | TextNative::TextUncons
                | TextNative::TextTrim
                | TextNative::NatToText
                | TextNative::TextToNat => 1,
                TextNative::TextFold => 3,
                _ => 2,
            },
            PrimOp::Delay(prim) => match prim {
                Primitive::Now | Primitive::Lift => 1,
                Primitive::BindD | Primitive::MapSig | Primitive::Pfix => 2,
                Primitive::Delay => 0,
            },
        }
    }

    /// Its name, as the pretty-printer shows it.
    pub fn name(self) -> String {
        match self {
            PrimOp::Nat(op) => op.name().to_string(),
            PrimOp::Int(op) => format!("{op:?}"),
            PrimOp::NegSucc => "NegSucc".into(),
            PrimOp::IntEqual => "IntEqual".into(),
            PrimOp::TextEqual => "TextEqual".into(),
            PrimOp::Text(op) => format!("{op:?}"),
            PrimOp::Delay(prim) => prim.name().to_string(),
        }
    }
}
