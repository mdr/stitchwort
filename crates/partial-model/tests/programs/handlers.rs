//! Handlers around partial code (`docs/proposals/partial-handlers.md`, lane A
//! of §8), as the elaborator would translate them: `handle` is `foldD` with
//! `handlePlus`-style forwarding ([`handle`]). Each comment shows the source.
//!
//! Operations are injected by hand, as the elaborator would: inside a
//! description of row `Plus (Rec T) (Plus A e)`, an operation `o` of `A` is
//! `R (L o)`.

use std::rc::Rc;

use stitchwort_partial_model::delay::SigMap;
use stitchwort_partial_model::runner::READ_LINE;
use stitchwort_partial_model::typed::*;
use stitchwort_partial_model::val::Val;

use super::Ask;

// --- Abilities ---------------------------------------------------------------

/// `ability Fail where stop: Text → Empty`.
pub struct Fail;
impl Sig for Fail {}
pub const STOP: u32 = 40;

/// `ability Input where next: () → Option Text` (the roguelike's commands).
pub struct Input;
impl Sig for Input {}
pub const NEXT: u32 = 41;

/// `ability Each where fork: () → Bool`.
pub struct Each;
impl Sig for Each {}
pub const FORK: u32 = 42;

/// `ability Counter where get: () → Nat; incr: () → ()`.
pub struct Counter;
impl Sig for Counter {}
pub const GET: u32 = 43;
pub const INCR: u32 = 44;

/// `ability Bump where bump: Nat → Nat` (generated programs).
pub struct Bump;
impl Sig for Bump {}
pub const BUMP: u32 = 30;

/// `Ok v`.
pub fn ok(v: Val) -> Val {
    Val::tag(100, v)
}

/// `Err msg`.
pub fn err(msg: &str) -> Val {
    Val::tag(101, Val::text(msg))
}

/// `[]`.
pub fn nil() -> Val {
    Val::Unit
}

/// `x :: xs`.
pub fn cons(x: Val, xs: Val) -> Val {
    Val::pair(x, xs)
}

pub fn list(items: &[Val]) -> Val {
    items.iter().rev().fold(nil(), |xs, x| cons(x.clone(), xs))
}

fn append(xs: Val, ys: Val) -> Val {
    let mut items = Vec::new();
    let mut xs = xs;
    while let Val::Pair(x, rest) = xs {
        items.push((*x).clone());
        xs = (*rest).clone();
    }
    items.into_iter().rev().fold(ys, |acc, x| cons(x, acc))
}

/// `R` applied `n` times: an operation injected under `n` signatures.
fn under(n: usize, o: Val) -> Val {
    (0..n).fold(o, |o, _| Val::right(o))
}

// --- Handlers ---------------------------------------------------------------

/// ```text
/// Fail.toResult (prog: () → {Fail | e} a): {e} Result a Text :=
///   handle prog() with
///     | return x => Ok x
///     | stop msg, k => Err msg
/// ```
pub fn to_result<E: Sig, A: Repr>(d: D<Plus<Fail, E>, A>) -> D<E, Val> {
    handle(
        |x: A| now(ok(x.into_val())),
        |o, _k| match o {
            Val::Tag(STOP, msg) => now(Val::tag(101, (*msg).clone())),
            other => panic!("not a Fail operation: {other:?}"),
        },
        d,
    )
}

/// `stop msg` from the top of a row `Plus Fail e`, under `depth` more
/// signatures (enclosing recursion signatures).
pub fn stop<S: Sig>(depth: usize, msg: &str) -> D<S, u64> {
    perform(under(depth, Val::left(Val::tag(STOP, Val::text(msg)))))
}

/// A state handler with a function carrier, as `seeded` and `fromLines` are:
///
/// ```text
/// fromLines (lines: List Text) (prog: () → {Input | e} a): {e} a :=
///   (handle prog() with
///      | return x => \_ => x
///      | next (), k => \rest => match rest with
///          | [] => k None []
///          | l :: rest => k (Some l) rest) lines
/// ```
pub fn from_lines<E: Sig, A: Repr>(lines: &[&str], d: D<Plus<Input, E>, A>) -> D<E, A> {
    let lines = list(&lines.iter().map(|l| Val::text(l)).collect::<Vec<_>>());
    let folded = handle(
        |x: A| {
            let x = x.into_val();
            now(PFn::<E, Val, A>::new(move |_| now(A::from_val(x.clone()))))
        },
        |o, k: Resume<E, PFn<E, Val, A>>| {
            assert!(
                matches!(o, Val::Tag(NEXT, _)),
                "not an Input operation: {o:?}"
            );
            now(PFn::<E, Val, A>::new(move |rest: Val| {
                let (reply, rest) = match rest {
                    Val::Pair(l, rest) => (Some((*l).clone()), (*rest).clone()),
                    _ => (None, nil()),
                };
                let reply = match reply {
                    Some(l) => Val::right(l),
                    None => Val::left(Val::Unit),
                };
                bind(k(reply), move |f: PFn<E, Val, A>| f.call(rest.clone()))
            }))
        },
        d,
    );
    bind(folded, move |f: PFn<E, Val, A>| f.call(lines.clone()))
}

/// ```text
/// runCounter (start: Nat) (prog: () → {Counter | e} a): {e} (a, Nat) :=
///   (handle prog() with
///      | return x => \s => (x, s)
///      | get (), k => \s => k s s
///      | incr (), k => \s => k () (s + 1)) start
/// ```
pub fn run_counter<E: Sig, A: Repr>(start: u64, d: D<Plus<Counter, E>, A>) -> D<E, (A, u64)> {
    type Carrier<E, A> = PFn<E, u64, (A, u64)>;
    let folded = handle(
        |x: A| {
            let x = x.into_val();
            now(Carrier::<E, A>::new(move |s| {
                now((A::from_val(x.clone()), s))
            }))
        },
        |o, k: Resume<E, Carrier<E, A>>| {
            let is_get = match o {
                Val::Tag(GET, _) => true,
                Val::Tag(INCR, _) => false,
                other => panic!("not a Counter operation: {other:?}"),
            };
            now(Carrier::<E, A>::new(move |s| {
                let (reply, next) = if is_get {
                    (Val::Nat(s), s)
                } else {
                    (Val::Unit, s + 1)
                };
                bind(k(reply), move |f: Carrier<E, A>| f.call(next))
            }))
        },
        d,
    );
    bind(folded, move |f: Carrier<E, A>| f.call(start))
}

/// ```text
/// Each.collectIn (prog: () → {Each | e} a): {e} List a :=
///   handle prog() with
///     | return x => [x]
///     | fork (), k => List.append (k True) (k False)
/// ```
pub fn collect_in<E: Sig, A: Repr>(d: D<Plus<Each, E>, A>) -> D<E, Val> {
    handle(
        |x: A| now(cons(x.into_val(), nil())),
        |o, k: Resume<E, Val>| {
            assert!(
                matches!(o, Val::Tag(FORK, _)),
                "not an Each operation: {o:?}"
            );
            let k2 = k.clone();
            bind(k(Val::Bool(true)), move |xs: Val| {
                bind(k2(Val::Bool(false)), move |ys: Val| {
                    now(append(xs.clone(), ys))
                })
            })
        },
        d,
    )
}

// --- Programs ---------------------------------------------------------------

/// ```text
/// countdown (n: Nat): {Fail, Partial} Nat :=
///   if n == 3 then Empty.absurd (Fail.stop "three") else if n == 0 then 0 else countdown (n - 1)
/// ```
pub fn countdown_fail() -> PFn<Plus<Fail, Empty>, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Plus<Fail, Empty>>(|n| {
        if n == 3 {
            stop(1, "three")
        } else if n == 0 {
            now(0)
        } else {
            recur::<T, Plus<Fail, Empty>>(n - 1)
        }
    })
}

/// `spin n = spin n`, in any row.
pub fn spin_in<S: Sig>() -> PFn<S, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, S>(recur::<T, S>)
}

/// ```text
/// play (turn: Nat): {Input, Host, Partial} Nat :=
///   match Input.next () with
///     | None => turn
///     | Some command =>
///       print "turn {turn}: {command}"
///       play (turn + 1)
/// ```
pub fn play() -> PFn<Plus<Input, Host>, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    type Row = Plus<Rec<T>, Plus<Input, Host>>;
    pfix::<T, Plus<Input, Host>>(|turn| {
        let next: D<Row, Option<String>> = perform(under(1, Val::left(Val::tag(NEXT, Val::Unit))));
        bind(next, move |command: Option<String>| match command {
            None => now(turn),
            Some(command) => bind(
                print::<Row>(&format!("turn {turn}: {command}")),
                move |()| recur::<T, Plus<Input, Host>>(turn + 1),
            ),
        })
    })
}

/// `Input` straight to the host: `next` becomes `readLine`. The unhandled
/// counterpart of [`from_lines`], to compare tick counts.
pub fn input_from_host() -> SigMap {
    SigMap {
        op: Rc::new(|o| match o {
            Val::L(_) => Val::tag(READ_LINE, Val::Unit),
            Val::R(o) => (**o).clone(),
            other => panic!("an operation outside `Plus`: {other:?}"),
        }),
        res: Rc::new(|_, r| r),
    }
}

/// ```text
/// search (n: Nat): {Each, Host, Partial} Nat :=
///   if n == 0 then 0 else
///     let b := Each.fork ()
///     print "{n}{if b then "T" else "F"}"
///     let r := search (n - 1)       -- not a tail call: an `Await` frame
///     2 * r + (if b then 1 else 0)
/// ```
pub fn search() -> PFn<Plus<Each, Host>, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    type Row = Plus<Rec<T>, Plus<Each, Host>>;
    pfix::<T, Plus<Each, Host>>(|n| {
        if n == 0 {
            return now(0);
        }
        let fork: D<Row, bool> = perform(under(1, Val::left(Val::tag(FORK, Val::Unit))));
        bind(fork, move |b: bool| {
            let mark = format!("{n}{}", if b { "T" } else { "F" });
            bind(print::<Row>(&mark), move |()| {
                bind(recur::<T, Plus<Each, Host>>(n - 1), move |r| {
                    now(2 * r + u64::from(b))
                })
            })
        })
    })
}

/// ```text
/// fork (); print (if b then "left" else "right"); if b then spin 0 else 1
/// ```
pub fn left_loops() -> D<Plus<Each, Host>, u64> {
    let fork: D<Plus<Each, Host>, bool> = perform(Val::left(Val::tag(FORK, Val::Unit)));
    bind(fork, |b: bool| {
        bind(
            print::<Plus<Each, Host>>(if b { "left" } else { "right" }),
            move |()| {
                if b {
                    spin_in::<Plus<Each, Host>>().call(0)
                } else {
                    now(1)
                }
            },
        )
    })
}

/// `get ()` and `incr ()` under `depth` signatures, in a row `Plus Counter e`.
pub fn counter_op<S: Sig, A: Repr>(depth: usize, tag: u32) -> D<S, A> {
    perform(under(depth, Val::left(Val::tag(tag, Val::Unit))))
}

/// ```text
/// tally (n: Nat): {Counter, Partial | e} Nat :=
///   if n == 0 then Counter.get () else
///     Counter.incr ()
///     let r := tally (n - 1)        -- not a tail call: an `Await` frame
///     print "tally {n}: {r}"
///     r + n
/// ```
pub fn tally<E: HasHost>() -> PFn<Plus<Counter, E>, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Plus<Counter, E>>(|n| {
        if n == 0 {
            return counter_op::<Plus<Rec<T>, Plus<Counter, E>>, u64>(1, GET);
        }
        bind(
            counter_op::<Plus<Rec<T>, Plus<Counter, E>>, ()>(1, INCR),
            move |()| {
                bind(recur::<T, Plus<Counter, E>>(n - 1), move |r| {
                    bind(
                        print::<Plus<Rec<T>, Plus<Counter, E>>>(&format!("tally {n}: {r}")),
                        move |()| now(r + n),
                    )
                })
            },
        )
    })
}

/// A handler inside a partial function's body, whose handled code calls
/// another partial function and the enclosing one:
///
/// ```text
/// walk (n: Nat): {Host, Partial} Nat :=
///   if n == 0 then 0 else
///     let (x, _) := runCounter 0 (() => tally n + walk (n - 1))
///     print "walk {n}: {x}"
///     x
/// ```
pub fn walk() -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    type Outer = Plus<Rec<T>, Host>;
    pfix::<T, Host>(|n| {
        if n == 0 {
            return now(0);
        }
        let handled: D<Plus<Counter, Outer>, u64> = bind(tally::<Outer>().call(n), move |t| {
            bind(
                lift_right::<Counter, Outer, u64>(recur::<T, Host>(n - 1)),
                move |w| now(t + w),
            )
        });
        bind(run_counter(0, handled), move |(x, _): (u64, u64)| {
            bind(print::<Outer>(&format!("walk {n}: {x}")), move |()| now(x))
        })
    })
}

/// ```text
/// climb (n: Nat): {Counter, Fail, Host, Partial} Nat :=
///   Counter.incr ()
///   let c := Counter.get ()
///   print "climb {c}"
///   if c == 3 then Empty.absurd (Fail.stop "three") else climb (n + 1)
/// ```
pub fn climb() -> PFn<Plus<Counter, Plus<Fail, Host>>, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    type S = Plus<Counter, Plus<Fail, Host>>;
    type Row = Plus<Rec<T>, S>;
    pfix::<T, S>(|n| {
        bind(counter_op::<Row, ()>(1, INCR), move |()| {
            bind(counter_op::<Row, u64>(1, GET), move |c| {
                bind(print::<Row>(&format!("climb {c}")), move |()| {
                    if c == 3 {
                        stop(2, "three")
                    } else {
                        recur::<T, S>(n + 1)
                    }
                })
            })
        })
    })
}

/// `{Counter, Fail | e}` to `{Fail, Counter | e}`: swap the first two
/// signatures, so either handler can be the inner one.
pub fn swap_first_two() -> SigMap {
    SigMap {
        op: Rc::new(|o| match o {
            Val::L(a) => Val::right(Val::left((**a).clone())),
            Val::R(rest) => match &**rest {
                Val::L(b) => Val::left((**b).clone()),
                _ => o.clone(),
            },
            other => panic!("an operation outside `Plus`: {other:?}"),
        }),
        res: Rc::new(|_, r| r),
    }
}

/// ```text
/// countDown (n: Nat): {Host, Partial} Nat :=
///   print "cd {n}"
///   if n == 0 then 0 else n + countDown (n - 1)
/// ```
pub fn count_down() -> PFn<Host, u64, u64> {
    struct T;
    impl RecSig for T {
        type Arg = u64;
        type Res = u64;
    }
    pfix::<T, Host>(|n| {
        bind(print::<Plus<Rec<T>, Host>>(&format!("cd {n}")), move |()| {
            if n == 0 {
                now(0)
            } else {
                bind(recur::<T, Host>(n - 1), move |r| now(r + n))
            }
        })
    })
}

/// Clauses that run partial code:
///
/// ```text
/// handle (let a := ask 2; print "got {a}"; a + ask 1) with
///   | return x => 100 * x + countDown 1
///   | ask n, k => k (countDown n)
/// ```
pub fn ask_by_counting_down() -> D<Host, u64> {
    let ask = |n: u64| perform::<Plus<Ask, Host>, u64>(Val::left(Val::tag(10, Val::Nat(n))));
    let prog = bind(ask(2), move |a| {
        bind(print::<Plus<Ask, Host>>(&format!("got {a}")), move |()| {
            bind(ask(1), move |b| now(a + b))
        })
    });
    handle::<Ask, Host, u64, u64>(
        |x| bind(count_down().call(1), move |r| now(100 * x + r)),
        |o, k| match o {
            Val::Tag(10, n) => bind(count_down().call(n.as_nat()), move |r| k(Val::Nat(r))),
            other => panic!("not an Ask operation: {other:?}"),
        },
        prog,
    )
}
