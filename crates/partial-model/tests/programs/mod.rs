//! Partial programs written against the typed model, as the elaborator would
//! translate them. Each comment shows the source.

// Closures such as `|x| recur(x)` mirror the source's `\x -> f x` on purpose.
#![allow(dead_code, clippy::redundant_closure)]

pub mod handlers;

use std::cell::Cell;
use std::rc::Rc;

use stitchwort_partial_model::delay::{Comp, Delay, SigMap};
use stitchwort_partial_model::runner::{PRINT, READ_LINE};
use stitchwort_partial_model::typed::*;
use stitchwort_partial_model::val::Val;

pub struct Nat1;
impl RecSig for Nat1 {
    type Arg = u64;
    type Res = u64;
}

/// `immediate n = n` (declared `{Partial}`, never recurses).
pub fn immediate() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(now)
}

/// `countdown 0 = 0; countdown n = countdown (n - 1)`: `n` tail requests.
pub fn countdown() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n == 0 {
            now(0)
        } else {
            recur::<T, Empty>(n - 1)
        }
    })
}

/// ```text
/// collatzSteps : Nat -> {Partial} Nat
/// collatzSteps 1 = 0
/// collatzSteps n = 1 + collatzSteps (if even n then n / 2 else 3 * n + 1)
/// ```
pub fn collatz_steps() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n <= 1 {
            now(0)
        } else {
            let next = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
            bind(recur::<T, Empty>(next), |r| now(1 + r))
        }
    })
}

/// `fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)`: nested,
/// non-tail requests.
pub fn fib() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n < 2 {
            now(n)
        } else {
            bind(recur::<T, Empty>(n - 1), move |a| {
                bind(recur::<T, Empty>(n - 2), move |b| now(a + b))
            })
        }
    })
}

/// `sumTo 0 = 0; sumTo n = n + sumTo (n - 1)`: one deep non-tail chain.
pub fn sum_to() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n == 0 {
            now(0)
        } else {
            bind(recur::<T, Empty>(n - 1), move |r| now(n + r))
        }
    })
}

/// A mutual group `even`/`odd` as one `pfix` over a sum: the request packs
/// the member (`true` = `even`) and its argument.
pub fn even_odd() -> PFn<Empty, (bool, u64), bool> {
    struct T;
    impl RecSig for T {
        type Arg = (bool, u64);
        type Res = bool;
    }
    pfix::<T, Empty>(|(is_even, n)| {
        if n == 0 {
            now(is_even)
        } else {
            recur::<T, Empty>((!is_even, n - 1))
        }
    })
}

/// Hofstadter's female and male sequences, a mutual group whose requests
/// are nested (an argument is the result of an earlier request):
/// `F 0 = 1; F n = n - M (F (n - 1))`, `M 0 = 0; M n = n - F (M (n - 1))`.
pub fn hofstadter() -> PFn<Empty, (bool, u64), u64> {
    struct T;
    impl RecSig for T {
        type Arg = (bool, u64);
        type Res = u64;
    }
    pfix::<T, Empty>(|(female, n)| {
        if n == 0 {
            now(if female { 1 } else { 0 })
        } else {
            bind(recur::<T, Empty>((female, n - 1)), move |inner| {
                bind(recur::<T, Empty>((!female, inner)), move |outer| {
                    now(n - outer)
                })
            })
        }
    })
}

/// The number of calls Hofstadter's F or M makes, counted directly.
pub fn hofstadter_calls(female: bool, n: u64) -> (u64, u64) {
    if n == 0 {
        return (if female { 1 } else { 0 }, 1);
    }
    let (inner, c1) = hofstadter_calls(female, n - 1);
    let (outer, c2) = hofstadter_calls(!female, inner);
    (n - outer, 1 + c1 + c2)
}

/// `useP : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat`, a helper
/// polymorphic in the residual signature.
pub fn use_p<S: Sig>(k: &dyn Fn(u64) -> D<S, u64>, n: u64) -> D<S, u64> {
    k(n)
}

/// `twice k n = k n + k n`: the callback runs twice.
pub fn twice<S: Sig>(k: Rc<dyn Fn(u64) -> D<S, u64>>, n: u64) -> D<S, u64> {
    let k2 = k.clone();
    bind(k(n), move |a| bind(k2(n), move |b| now(a + b)))
}

/// `viaHelper 0 = 1; viaHelper n = useP viaHelper (n - 1)`: the recursive
/// function passed bare to a row-polymorphic helper.
pub fn via_helper() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n == 0 {
            now(1)
        } else {
            use_p(&|y| recur::<T, Empty>(y), n - 1)
        }
    })
}

/// `tree 0 = 1; tree n = twice (\x -> tree x) (n - 1)`: a callback under a
/// lambda, called twice per level.
pub fn tree() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n == 0 {
            now(1)
        } else {
            twice(Rc::new(|x| recur::<T, Empty>(x)), n - 1)
        }
    })
}

/// Callbacks stored in a record and used inside the description.
pub struct Handlers<S: Sig> {
    pub on_step: PFn<S, u64, u64>,
    pub on_done: PFn<S, u64, u64>,
}

/// `drive : Handlers e -> Nat -> {Partial | e} Nat`.
pub fn drive<S: Sig>(h: &Handlers<S>, n: u64) -> D<S, u64> {
    if n == 0 {
        h.on_done.call(0)
    } else {
        h.on_step.call(n - 1)
    }
}

/// `stored n = drive { onStep = \y -> stored y, onDone = \_ -> 42 } n`.
pub fn stored() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        let h = Handlers {
            on_step: PFn::new(|y| recur::<T, Empty>(y)),
            on_done: PFn::new(|_| now(42)),
        };
        drive(&h, n)
    })
}

/// A recursive function returning a closure that calls an *already-defined*
/// partial function (fine), unlike one calling itself (`typed` doctest).
pub fn returns_closure(callee: PFn<Empty, u64, u64>) -> PFn<Empty, u64, PFn<Empty, u64, u64>> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = PFn<Empty, u64, u64>;
    }
    pfix::<T, Empty>(move |n| {
        if n == 0 {
            let c = callee.clone();
            now(PFn::new(move |x| c.call(x)))
        } else {
            recur::<T, Empty>(n - 1)
        }
    })
}

/// A description that counts how often it's entered.
pub fn counted(entries: Rc<Cell<u64>>) -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(move |n| {
        entries.set(entries.get() + 1);
        if n == 0 {
            now(0)
        } else {
            recur::<T, Empty>(n - 1)
        }
    })
}

/// `bindD (now x) fresh`, where the continuation builds a brand-new `pfix`
/// (a description that didn't exist when the outer `Delay` was built).
pub fn fresh_in_continuation(x: u64) -> D<Empty, u64> {
    bind(now::<Empty, u64>(x), |x| {
        struct Fresh;
        impl RecSig for Fresh {
            type Arg = u64;
            type Res = u64;
        }
        pfix::<Fresh, Empty>(move |n| {
            if n == 0 {
                now(x * 10)
            } else {
                recur::<Fresh, Empty>(n - 1)
            }
        })
        .call(x)
    })
}

/// `spin n = spin n`.
pub fn spin() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(recur::<T, Empty>)
}

// --- With host operations -------------------------------------------------

/// ```text
/// echo : Nat -> {Host, Partial} Nat     -- prints each line until end of input
/// echo count = case readLine () of
///   Nothing -> count
///   Just l  -> print l; echo (count + 1)
/// ```
pub fn echo() -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Host>(|count| {
        bind(read_line(), move |l: Option<String>| match l {
            None => now(count),
            Some(l) => bind(print(&l), move |()| recur::<T, Host>(count + 1)),
        })
    })
}

/// `nest n = print "enter n"; if n == 0 then 0 else (let r = nest (n - 1);
/// print "leave n"; r + n)`: operations before and after a non-tail request.
pub fn nest() -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Host>(|n| {
        bind(print(&format!("enter {n}")), move |()| {
            if n == 0 {
                now(0)
            } else {
                bind(recur::<T, Host>(n - 1), move |r| {
                    bind(print(&format!("leave {n}")), move |()| now(r + n))
                })
            }
        })
    })
}

/// `outer n = if n == 0 then 0 else (let x = nest 1; x + outer (n - 1))`: a
/// recursive function calling another one (two `tie`s nested).
pub fn outer(nest: PFn<Host, u64, u64>) -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Host>(move |n| {
        if n == 0 {
            now(0)
        } else {
            bind(lift_right::<Rec<T>, Host, u64>(nest.call(1)), move |x| {
                bind(recur::<T, Host>(n - 1), move |r| now(x + r))
            })
        }
    })
}

/// The `Ask` signature: one operation, `#10(())`, answered with a `Nat`.
pub struct Ask;
impl Sig for Ask {}

/// `ask : () -> {Ask} Nat`, asked twice and summed: a total computation in
/// its own signature (`#10(())`, answered with a `Nat`).
pub fn ask_twice() -> Delay {
    Delay::lift(Comp::call(Val::tag(10, Val::Unit), |a| {
        Comp::call(Val::tag(10, Val::Unit), move |b| {
            Comp::Done(Val::Nat(a.as_nat() + b.as_nat()))
        })
    }))
}

/// `Ask` to `Host`: `ask` becomes `readLine`, and the reply (a `Maybe Text`)
/// is translated back to the line's length.
pub fn ask_via_read_line() -> SigMap {
    SigMap {
        op: Rc::new(|_| Val::tag(READ_LINE, Val::Unit)),
        res: Rc::new(|_, reply| match reply {
            Val::R(t) => Val::Nat(t.as_text().len() as u64),
            _ => Val::Nat(0),
        }),
    }
}

/// `sumAsks n`: `n` rounds of `ask_twice` through the mapping, recursing
/// after each.
pub fn sum_asks() -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Host>(|n| {
        if n == 0 {
            now(0)
        } else {
            let asked: D<Host, u64> =
                map_sig(ask_via_read_line(), D::<Ask, u64>::from_raw(ask_twice()));
            bind(lift_right::<Rec<T>, Host, u64>(asked), move |x| {
                bind(recur::<T, Host>(n - 1), move |r| now(x + r))
            })
        }
    })
}

/// A mapping *into* the recursion signature: `#11(y)` becomes `Recur y`, and
/// the reply comes back plus 100. `again 0 = 1; again n = 2 * (again (n - 1) + 100)`.
pub fn again() -> PFn<Empty, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Empty>(|n| {
        if n == 0 {
            now(1)
        } else {
            let m = SigMap {
                op: Rc::new(|o| match o {
                    Val::Tag(11, y) => Val::left((**y).clone()),
                    other => panic!("unexpected {other:?}"),
                }),
                res: Rc::new(|_, v| Val::Nat(v.as_nat() + 100)),
            };
            let inner = Delay::lift(Comp::call(Val::tag(11, Val::Nat(n - 1)), |v| {
                Comp::Done(Val::Nat(2 * v.as_nat()))
            }));
            D::from_raw(Delay::map_sig(m, inner))
        }
    })
}

/// Prefix every printed line with `>`.
pub fn prefix_prints() -> SigMap {
    SigMap {
        op: Rc::new(|o| match o {
            Val::Tag(PRINT, t) => Val::tag(PRINT, Val::text(&format!(">{}", t.as_text()))),
            other => other.clone(),
        }),
        res: Rc::new(|_, r| r),
    }
}

/// `forever n = print "tick"; forever (n + 1)`.
pub fn forever_print() -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Host>(|n| bind(print("tick"), move |()| recur::<T, Host>(n + 1)))
}

/// `foreignSpin () = spinForever 0`: a foreign function that never returns.
pub fn foreign_spin() -> D<Host, u64> {
    foreign::<Host>("spin", 0)
}
