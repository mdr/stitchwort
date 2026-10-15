//! The stepping equations, transcribed literally (proposal §7.4).
//!
//! This is the *specification*: short, recursive, and not stack-safe. The
//! machine ([`crate::machine`]) is the implementation, and the tests check
//! that both produce the same traces. [`Rules::Draft2`] keeps draft 2's
//! `pfix` equation so its double counting can be reproduced.
//!
//! ```text
//! step (now v)       = Done (Now v)
//! step (lift c)      = mapLeaves c
//! step (bindD d k)   = bindSeg k (step d)
//! step (mapSig m d)  = mapSeg m (step d)
//! step (pfix f x)    = tieSeg f (step (f x))        -- draft 3: enter, no tick
//! step (pfix f x)    = Done (Later (tie f (f x)))   -- draft 2
//! step (tie f d)     = tieSeg f (step d)
//! step (resume s)    = s
//!
//! tieSeg f (Done (Now v))          = Done (Now v)
//! tieSeg f (Done (Later d'))       = Done (Later (tie f d'))
//! tieSeg f (Call (R o) r)          = Call o (\x -> tieSeg f (r x))
//! tieSeg f (Call (L (Recur y)) r)  = Done (Later (bindD (pfix f y) (\v -> tie f (resume (r v)))))
//! ```

use std::rc::Rc;

use crate::delay::{Comp, Delay, Kont, Node, SigMap};
use crate::val::Val;

/// A segment: `Comp op res (Next a (Delay op res a))`.
#[derive(Clone)]
pub enum Seg {
    Now(Val),
    Later(Delay),
    Call(Val, Rc<dyn Fn(Val) -> Seg>),
}

/// Which `pfix` equation to use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rules {
    /// `step (pfix f x) = Done (Later (tie f (f x)))`: a tick on entry *and*
    /// one per request, so two per recursive call.
    Draft2,
    /// `step (pfix f x) = tieSeg f (step (f x))`: one tick per request only.
    Draft3,
}

pub fn step(rules: Rules, d: &Delay) -> Seg {
    match &*d.0 {
        Node::Now(v) => Seg::Now(v.clone()),
        Node::Lift(c) => map_leaves(c.clone()),
        Node::Bind(d, k) => bind_seg(rules, k.clone(), step(rules, d)),
        Node::MapSig(m, d) => map_seg(m.clone(), step(rules, d)),
        Node::Pfix(f, x) => match rules {
            Rules::Draft3 => tie_seg(f.clone(), step(rules, &f(x.clone()))),
            // `bindD (now x) f` is `f x`, suspended: the body doesn't run
            // until the `Later`'s rest is stepped.
            Rules::Draft2 => {
                let f2 = f.clone();
                let body = Delay::bind(Delay::now(x.clone()), move |v| f2(v));
                Seg::Later(Delay::tie(f.clone(), body))
            }
        },
        Node::Tie(f, d) => tie_seg(f.clone(), step(rules, d)),
        Node::Resume(s) => s.clone(),
        Node::Suspended(_) => panic!("a machine state given to the reference stepper"),
    }
}

fn map_leaves(c: Comp) -> Seg {
    match c {
        Comp::Done(v) => Seg::Now(v),
        Comp::Call(o, r) => Seg::Call(o, Rc::new(move |x| map_leaves(r.apply(x)))),
    }
}

fn bind_seg(rules: Rules, k: Kont, s: Seg) -> Seg {
    match s {
        Seg::Now(v) => step(rules, &k(v)),
        Seg::Later(d) => Seg::Later(Delay::bind_k(d, k)),
        Seg::Call(o, r) => Seg::Call(o, Rc::new(move |x| bind_seg(rules, k.clone(), r(x)))),
    }
}

fn map_seg(m: SigMap, s: Seg) -> Seg {
    match s {
        Seg::Now(v) => Seg::Now(v),
        Seg::Later(d) => Seg::Later(Delay::map_sig(m, d)),
        Seg::Call(o, r) => {
            let target = (m.op)(&o);
            Seg::Call(
                target,
                Rc::new(move |x| map_seg(m.clone(), r((m.res)(&o, x)))),
            )
        }
    }
}

fn tie_seg(f: Kont, s: Seg) -> Seg {
    match s {
        Seg::Now(v) => Seg::Now(v),
        Seg::Later(d) => Seg::Later(Delay::tie(f, d)),
        Seg::Call(Val::R(o), r) => {
            Seg::Call((*o).clone(), Rc::new(move |x| tie_seg(f.clone(), r(x))))
        }
        Seg::Call(Val::L(y), r) => {
            let f2 = f.clone();
            let rest = move |v| Delay::tie(f2.clone(), Delay::resume(r(v)));
            Seg::Later(Delay::bind(Delay::pfix(f, (*y).clone()), rest))
        }
        Seg::Call(o, _) => panic!("a description made an operation outside `Plus`: {o:?}"),
    }
}
