//! The proposal's types, on top of the untyped engine.
//!
//! Rust's type checker stands in for the elaborator's: `D<S, A>` is
//! `Delay op_S res_S A`, signatures are marker types, and a row variable `e`
//! is a generic parameter `S: Sig`. Each partial definition gets its own
//! private recursion signature `Rec<T>`, with `T` a marker type unique to the
//! definition, as the elaborator would generate. So whether a program can be
//! *expressed* under the request translation is checked by `rustc`.
//!
//! The request translation's boundary (proposal §7.3), as `rustc` sees it.
//! A helper polymorphic in the residual signature accepts a recursive
//! callback:
//!
//! ```
//! use stitchwort_partial_model::typed::*;
//! struct Countdown;
//! impl RecSig for Countdown { type Arg = u64; type Res = u64; }
//!
//! // useP : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat
//! fn use_p<S: Sig>(k: &dyn Fn(u64) -> D<S, u64>, n: u64) -> D<S, u64> { k(n) }
//!
//! // countdown n = if n == 0 then 0 else useP countdown (n - 1)
//! let countdown = pfix::<Countdown, Empty>(|n| {
//!     if n == 0 { now(0) } else { use_p(&|y| recur::<Countdown, Empty>(y), n - 1) }
//! });
//! let _ = countdown.call(5);
//! ```
//!
//! A monomorphic helper doesn't: its callback type can't contain the private
//! recursion signature (the reviewer's `useP`/`loop` example).
//!
//! ```compile_fail
//! use stitchwort_partial_model::typed::*;
//! struct Countdown;
//! impl RecSig for Countdown { type Arg = u64; type Res = u64; }
//!
//! // useP : (Nat -> {Partial} Nat) -> Nat -> {Partial} Nat
//! fn use_p_mono(k: &dyn Fn(u64) -> D<Empty, u64>, n: u64) -> D<Empty, u64> { k(n) }
//!
//! let countdown = pfix::<Countdown, Empty>(|n| {
//!     if n == 0 { now(0) } else {
//!         // error[E0308]: expected `D<Empty, u64>`, found `D<Plus<Rec<Countdown>, Empty>, u64>`
//!         lift_right(use_p_mono(&|y| recur::<Countdown, Empty>(y), n - 1))
//!     }
//! });
//! ```
//!
//! A recursive function can't return a closure that calls itself: the
//! closure would make requests that nothing outside the description answers.
//!
//! ```compile_fail
//! use stitchwort_partial_model::typed::*;
//! struct Retry;
//! impl RecSig for Retry { type Arg = u64; type Res = PFn<Empty, u64, u64>; }
//!
//! // retry : Nat -> {Partial} (Nat -> {Partial} Nat)
//! // retry 0 = \x -> x
//! // retry n = \x -> (retry (n - 1)) x      -- the returned closure refers to retry
//! let retry = pfix::<Retry, Empty>(|n| {
//!     if n == 0 { return now(PFn::new(|x: u64| now(x))); }
//!     // error[E0308]: expected `PFn<Empty, u64, u64>`, found `PFn<Plus<Rec<Retry>, Empty>, u64, u64>`
//!     now(PFn::new(move |x: u64| {
//!         bind(recur::<Retry, Empty>(n - 1), move |g: PFn<Empty, u64, u64>| lift_right(g.call(x)))
//!     }))
//! });
//! ```

use std::marker::PhantomData;
use std::rc::Rc;

use crate::delay::{Comp, Delay, Handler, Kont, SigMap};
use crate::runner::{FOREIGN, PRINT, READ_LINE};
use crate::val::Val;

/// A signature (an ability row, translated).
pub trait Sig: 'static {}

/// The empty row: `{Partial}` alone.
pub struct Empty;
impl Sig for Empty {}

/// The host signature: print, readLine and foreign calls.
pub struct Host;
impl Sig for Host {}

/// `Plus A B`.
pub struct Plus<A, B>(PhantomData<(A, B)>);
impl<A: Sig, B: Sig> Sig for Plus<A, B> {}

/// The private recursion signature of the definition marked by `T`.
pub struct Rec<T>(PhantomData<T>);
impl<T: RecSig> Sig for Rec<T> {}

/// What a partial definition recurses on and returns. Fixed parameters stay
/// outside (captured by the description); arguments that change on recursive
/// calls are packed into `Arg`.
pub trait RecSig: 'static {
    type Arg: Repr;
    type Res: Repr;
}

/// Conversion to and from runtime values.
pub trait Repr: Sized + 'static {
    fn into_val(self) -> Val;
    fn from_val(v: Val) -> Self;
}

impl Repr for Val {
    fn into_val(self) -> Val {
        self
    }
    fn from_val(v: Val) -> Val {
        v
    }
}

impl Repr for u64 {
    fn into_val(self) -> Val {
        Val::Nat(self)
    }
    fn from_val(v: Val) -> u64 {
        v.as_nat()
    }
}

impl Repr for bool {
    fn into_val(self) -> Val {
        Val::Bool(self)
    }
    fn from_val(v: Val) -> bool {
        v.as_bool()
    }
}

impl Repr for () {
    fn into_val(self) -> Val {
        Val::Unit
    }
    fn from_val(_: Val) {}
}

impl Repr for String {
    fn into_val(self) -> Val {
        Val::text(&self)
    }
    fn from_val(v: Val) -> String {
        v.as_text().to_string()
    }
}

impl<A: Repr, B: Repr> Repr for (A, B) {
    fn into_val(self) -> Val {
        Val::pair(self.0.into_val(), self.1.into_val())
    }
    fn from_val(v: Val) -> (A, B) {
        let (a, b) = v.as_pair();
        (A::from_val(a), B::from_val(b))
    }
}

/// `Maybe A`: `Nothing` is `L ()`, `Just a` is `R a`.
impl<A: Repr> Repr for Option<A> {
    fn into_val(self) -> Val {
        match self {
            None => Val::left(Val::Unit),
            Some(a) => Val::right(a.into_val()),
        }
    }
    fn from_val(v: Val) -> Option<A> {
        match v {
            Val::L(_) => None,
            Val::R(a) => Some(A::from_val((*a).clone())),
            other => panic!("expected a Maybe, got {other:?}"),
        }
    }
}

/// `Delay op_S res_S A`.
pub struct D<S: Sig, A> {
    pub raw: Delay,
    _t: PhantomData<(S, A)>,
}

impl<S: Sig, A> Clone for D<S, A> {
    fn clone(&self) -> Self {
        D::from_raw(self.raw.clone())
    }
}

impl<S: Sig, A> D<S, A> {
    pub fn from_raw(raw: Delay) -> D<S, A> {
        D {
            raw,
            _t: PhantomData,
        }
    }
}

/// A function `X -> {Partial | S} B`: a value that can be stored in data.
pub struct PFn<S: Sig, X, B>(Rc<dyn Fn(X) -> D<S, B>>);

impl<S: Sig, X, B> Clone for PFn<S, X, B> {
    fn clone(&self) -> Self {
        PFn(self.0.clone())
    }
}

impl<S: Sig, X: Repr, B: Repr> PFn<S, X, B> {
    pub fn new(f: impl Fn(X) -> D<S, B> + 'static) -> PFn<S, X, B> {
        PFn(Rc::new(f))
    }

    pub fn call(&self, x: X) -> D<S, B> {
        (self.0)(x)
    }
}

impl<S: Sig, X: Repr, B: Repr> Repr for PFn<S, X, B> {
    fn into_val(self) -> Val {
        let f = self.0;
        Val::Fun(Rc::new(move |v| f(X::from_val(v)).raw))
    }
    fn from_val(v: Val) -> PFn<S, X, B> {
        match v {
            Val::Fun(f) => PFn(Rc::new(move |x: X| D::from_raw(f(x.into_val())))),
            other => panic!("expected a function, got {other:?}"),
        }
    }
}

pub fn now<S: Sig, A: Repr>(a: A) -> D<S, A> {
    D::from_raw(Delay::now(a.into_val()))
}

/// `bindD`.
pub fn bind<S: Sig, A: Repr, B: Repr>(d: D<S, A>, k: impl Fn(A) -> D<S, B> + 'static) -> D<S, B> {
    D::from_raw(Delay::bind(d.raw, move |v| k(A::from_val(v)).raw))
}

/// `mapSig sigRight`: embed a computation under one more signature.
pub fn lift_right<X: Sig, S: Sig, A: Repr>(d: D<S, A>) -> D<Plus<X, S>, A> {
    D::from_raw(Delay::map_sig(SigMap::right(), d.raw))
}

/// `mapSig m` with a mapping the caller vouches for (the model doesn't type
/// operations individually).
pub fn map_sig<S1: Sig, S2: Sig, A: Repr>(m: SigMap, d: D<S1, A>) -> D<S2, A> {
    D::from_raw(Delay::map_sig(m, d.raw))
}

/// `recur y`: a request in the private recursion signature.
pub fn recur<T: RecSig, S: Sig>(y: T::Arg) -> D<Plus<Rec<T>, S>, T::Res> {
    D::from_raw(Delay::recur(y.into_val()))
}

/// `pfix`: tie a description into the partial function it describes.
pub fn pfix<T: RecSig, S: Sig>(
    desc: impl Fn(T::Arg) -> D<Plus<Rec<T>, S>, T::Res> + 'static,
) -> PFn<S, T::Arg, T::Res> {
    let raw: Rc<dyn Fn(Val) -> Delay> = Rc::new(move |v| desc(T::Arg::from_val(v)).raw);
    PFn::new(move |x: T::Arg| D::from_raw(Delay::pfix(raw.clone(), x.into_val())))
}

/// Rows that contain the host signature (`{Host | e}`), with its injection.
pub trait HasHost: Sig {
    fn inj(op: Val) -> Val;
}

impl HasHost for Host {
    fn inj(op: Val) -> Val {
        op
    }
}

impl<A: Sig, B: HasHost> HasHost for Plus<A, B> {
    fn inj(op: Val) -> Val {
        Val::right(B::inj(op))
    }
}

fn host_op<S: HasHost, A: Repr>(op: Val) -> D<S, A> {
    D::from_raw(Delay::lift(Comp::op(S::inj(op))))
}

pub fn print<S: HasHost>(t: &str) -> D<S, ()> {
    host_op(Val::tag(PRINT, Val::text(t)))
}

pub fn read_line<S: HasHost>() -> D<S, Option<String>> {
    host_op(Val::tag(READ_LINE, Val::Unit))
}

/// A foreign function, declared `{Partial}`: a host request, never run by
/// `step` itself.
pub fn foreign<S: HasHost>(name: &str, arg: u64) -> D<S, u64> {
    host_op(Val::tag(FOREIGN, Val::pair(Val::text(name), Val::Nat(arg))))
}

// --- Handlers around partial code (partial-handlers.md) ---------------------

/// An operation already injected into the row `S` (the caller vouches for
/// the injection, as for [`map_sig`]: the model doesn't type operations).
pub fn perform<S: Sig, A: Repr>(op: Val) -> D<S, A> {
    D::from_raw(Delay::lift(Comp::op(op)))
}

/// A resumption `k`: the rest of the handled program, still under the
/// handler. Its argument is the operation's reply.
pub type Resume<S, B> = Rc<dyn Fn(Val) -> D<S, B>>;

/// `foldD done call d`. The result is a `D` again: a handler around partial
/// code is partial.
pub fn fold_d<S1: Sig, S2: Sig, A: Repr, B: Repr>(
    done: impl Fn(A) -> D<S2, B> + 'static,
    call: impl Fn(Val, Resume<S2, B>) -> D<S2, B> + 'static,
    d: D<S1, A>,
) -> D<S2, B> {
    let done: Kont = Rc::new(move |v| done(A::from_val(v)).raw);
    let call: Handler = Rc::new(move |o, k: Kont| {
        let k: Resume<S2, B> = Rc::new(move |y| D::from_raw(k(y)));
        call(o, k).raw
    });
    D::from_raw(Delay::fold_d(done, call, d.raw))
}

/// Forward an operation the handler doesn't handle: perform it outside, and
/// resume with its reply. `bindD (lift (Call o Done)) k`.
pub fn forward<E: Sig, B: Repr>(o: Val, k: Resume<E, B>) -> D<E, B> {
    D::from_raw(Delay::bind(Delay::lift(Comp::op(o)), move |y| k(y).raw))
}

/// `handle d with …` for an ability `A` in `{A | e}`, as the elaborator builds
/// it: `A`'s operations (left) go to `clause`, and the rest are forwarded
/// (`handlePlus`).
pub fn handle<A: Sig, E: Sig, X: Repr, B: Repr>(
    done: impl Fn(X) -> D<E, B> + 'static,
    clause: impl Fn(Val, Resume<E, B>) -> D<E, B> + 'static,
    d: D<Plus<A, E>, X>,
) -> D<E, B> {
    fold_d(
        done,
        move |o, k| match o {
            Val::L(a) => clause((*a).clone(), k),
            Val::R(o) => forward((*o).clone(), k),
            other => panic!("an operation outside `Plus` reached a handler: {other:?}"),
        },
        d,
    )
}
