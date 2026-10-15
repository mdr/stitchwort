//! Untyped runtime values.
//!
//! The engine is untyped, like the kernel's evaluator; [`crate::typed`] puts
//! the proposal's types on top. Operations are values too: a `Plus` signature
//! injects with [`Val::L`] (left: the private recursion signature, whose one
//! operation `Recur y` is `L(y)`) and [`Val::R`] (right: the rest of the row).

use std::fmt;
use std::rc::Rc;

use crate::delay::Delay;

/// A runtime value.
#[derive(Clone)]
pub enum Val {
    Unit,
    Bool(bool),
    Nat(u64),
    Text(Rc<str>),
    Pair(Rc<Val>, Rc<Val>),
    /// Left injection (`L` of `Plus`, or `Left`).
    L(Rc<Val>),
    /// Right injection (`R` of `Plus`, or `Right`).
    R(Rc<Val>),
    /// A constructor with a numeric tag, for operations of a host signature.
    Tag(u32, Rc<Val>),
    /// A function returning a partial computation (`a -> {Partial | e} b`).
    Fun(Rc<dyn Fn(Val) -> Delay>),
}

impl Val {
    pub fn nat(n: u64) -> Val {
        Val::Nat(n)
    }

    pub fn text(s: &str) -> Val {
        Val::Text(Rc::from(s))
    }

    pub fn pair(a: Val, b: Val) -> Val {
        Val::Pair(Rc::new(a), Rc::new(b))
    }

    pub fn left(v: Val) -> Val {
        Val::L(Rc::new(v))
    }

    pub fn right(v: Val) -> Val {
        Val::R(Rc::new(v))
    }

    pub fn tag(t: u32, v: Val) -> Val {
        Val::Tag(t, Rc::new(v))
    }

    /// The `Nat` inside, panicking otherwise (a type error in the model).
    pub fn as_nat(&self) -> u64 {
        match self {
            Val::Nat(n) => *n,
            other => panic!("expected a Nat, got {other:?}"),
        }
    }

    pub fn as_bool(&self) -> bool {
        match self {
            Val::Bool(b) => *b,
            other => panic!("expected a Bool, got {other:?}"),
        }
    }

    pub fn as_text(&self) -> Rc<str> {
        match self {
            Val::Text(t) => t.clone(),
            other => panic!("expected a Text, got {other:?}"),
        }
    }

    pub fn as_pair(&self) -> (Val, Val) {
        match self {
            Val::Pair(a, b) => ((**a).clone(), (**b).clone()),
            other => panic!("expected a Pair, got {other:?}"),
        }
    }
}

impl fmt::Debug for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Unit => write!(f, "()"),
            Val::Bool(b) => write!(f, "{b}"),
            Val::Nat(n) => write!(f, "{n}"),
            Val::Text(t) => write!(f, "{t:?}"),
            Val::Pair(a, b) => write!(f, "({a:?}, {b:?})"),
            Val::L(v) => write!(f, "L({v:?})"),
            Val::R(v) => write!(f, "R({v:?})"),
            Val::Tag(t, v) => write!(f, "#{t}({v:?})"),
            Val::Fun(_) => write!(f, "<fun>"),
        }
    }
}

impl PartialEq for Val {
    fn eq(&self, other: &Val) -> bool {
        match (self, other) {
            (Val::Unit, Val::Unit) => true,
            (Val::Bool(a), Val::Bool(b)) => a == b,
            (Val::Nat(a), Val::Nat(b)) => a == b,
            (Val::Text(a), Val::Text(b)) => a == b,
            (Val::Pair(a1, b1), Val::Pair(a2, b2)) => a1 == a2 && b1 == b2,
            (Val::L(a), Val::L(b)) | (Val::R(a), Val::R(b)) => a == b,
            (Val::Tag(t1, a), Val::Tag(t2, b)) => t1 == t2 && a == b,
            (Val::Fun(a), Val::Fun(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}
