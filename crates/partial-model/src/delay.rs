//! `Comp` segments and `Delay` values, as the runtime represents them.
//!
//! The kernel constants of the proposal (§7.2) are [`Delay::now`],
//! [`Delay::lift`], [`Delay::bind`], [`Delay::map_sig`] and [`Delay::pfix`].
//! Each just *records* its arguments: building a `Delay` never runs user code.
//! In particular `pfix f x` stores `f` and `x` without applying `f`; the
//! description's body runs only when the value is stepped (proposal §7.4,
//! "suspended runtime states").
//!
//! The other node kinds are internal runtime states that user code can't
//! build: `Tie` and `Resume` belong to the reference stepper
//! ([`crate::reference`]), `Suspended` to the machine ([`crate::machine`]).

use std::rc::Rc;

use crate::machine::Machine;
use crate::reference::Seg;
use crate::val::Val;

/// A continuation of `bindD`, and a description given to `pfix`.
pub type Kont = Rc<dyn Fn(Val) -> Delay>;

/// The continuation of a `Call` node in a `Comp` tree.
#[derive(Clone)]
pub enum Cont {
    /// `\v -> Done v`. Kept distinct so tail requests can be recognised.
    Done,
    Fn(Rc<dyn Fn(Val) -> Comp>),
}

impl Cont {
    pub fn apply(&self, v: Val) -> Comp {
        match self {
            Cont::Done => Comp::Done(v),
            Cont::Fn(f) => f(v),
        }
    }

    pub fn is_done(&self) -> bool {
        matches!(self, Cont::Done)
    }
}

/// The prelude's well-founded `Comp` tree: `Done value | Call op rest`.
#[derive(Clone)]
pub enum Comp {
    Done(Val),
    Call(Val, Cont),
}

impl Comp {
    /// `Call o Done`: perform `o` and return its reply.
    pub fn op(o: Val) -> Comp {
        Comp::Call(o, Cont::Done)
    }

    /// `Call o rest`.
    pub fn call(o: Val, rest: impl Fn(Val) -> Comp + 'static) -> Comp {
        Comp::Call(o, Cont::Fn(Rc::new(rest)))
    }
}

/// `res(source_op, target_reply)`: the reply the source operation expects.
pub type ResMap = Rc<dyn Fn(&Val, Val) -> Val>;

/// A signature mapping (`SigMap`): each source operation becomes a target
/// operation, and the target's reply is translated back to the source's.
#[derive(Clone)]
pub struct SigMap {
    pub op: Rc<dyn Fn(&Val) -> Val>,
    pub res: ResMap,
}

impl SigMap {
    /// `sigRight`: embed a computation into `Plus other sig` on the right.
    pub fn right() -> SigMap {
        SigMap {
            op: Rc::new(|o| Val::right(o.clone())),
            res: Rc::new(|_, r| r),
        }
    }
}

/// A possibly endless computation. Cloning is cheap (shared).
#[derive(Clone)]
pub struct Delay(pub(crate) Rc<Node>);

pub(crate) enum Node {
    Now(Val),
    Lift(Comp),
    Bind(Delay, Kont),
    MapSig(SigMap, Delay),
    /// `pfix f x`: suspended. `f` hasn't been applied to `x`.
    Pfix(Kont, Val),
    /// Reference stepper only: `tie f d` answers `d`'s recursion requests.
    Tie(Kont, Delay),
    /// Reference stepper only: a segment turned back into a `Delay`.
    Resume(Seg),
    /// Machine only: the rest of a computation after a `Later`.
    Suspended(Box<Machine>),
}

impl Delay {
    pub fn now(v: Val) -> Delay {
        Delay(Rc::new(Node::Now(v)))
    }

    pub fn lift(c: Comp) -> Delay {
        Delay(Rc::new(Node::Lift(c)))
    }

    pub fn bind(d: Delay, k: impl Fn(Val) -> Delay + 'static) -> Delay {
        Delay(Rc::new(Node::Bind(d, Rc::new(k))))
    }

    pub fn bind_k(d: Delay, k: Kont) -> Delay {
        Delay(Rc::new(Node::Bind(d, k)))
    }

    pub fn map_sig(m: SigMap, d: Delay) -> Delay {
        Delay(Rc::new(Node::MapSig(m, d)))
    }

    /// `pfix f x`. Doesn't apply `f`.
    pub fn pfix(f: Kont, x: Val) -> Delay {
        Delay(Rc::new(Node::Pfix(f, x)))
    }

    /// A recursion request `Recur y`, as a description would make it:
    /// `lift (Call (L (Recur y)) Done)`.
    pub fn recur(y: Val) -> Delay {
        Delay::lift(Comp::op(Val::left(y)))
    }

    /// A host operation `o` from inside a description, under `n` enclosing
    /// recursion signatures (`R` applied `n` times).
    pub fn op_under(n: usize, o: Val) -> Delay {
        let mut o = o;
        for _ in 0..n {
            o = Val::right(o);
        }
        Delay::lift(Comp::op(o))
    }

    pub(crate) fn tie(f: Kont, d: Delay) -> Delay {
        Delay(Rc::new(Node::Tie(f, d)))
    }

    pub(crate) fn resume(s: Seg) -> Delay {
        Delay(Rc::new(Node::Resume(s)))
    }

    pub(crate) fn suspended(m: Machine) -> Delay {
        Delay(Rc::new(Node::Suspended(Box::new(m))))
    }

    /// Whether this is a still-unentered `pfix` application.
    pub fn is_unentered_pfix(&self) -> bool {
        matches!(&*self.0, Node::Pfix(..))
    }
}

/// Dropping a long chain of `Bind`s (say a million left-nested binds) must not
/// recurse on the host stack, so children are unlinked iteratively.
impl Drop for Node {
    fn drop(&mut self) {
        let mut stack: Vec<Delay> = Vec::new();
        take_children(self, &mut stack);
        while let Some(d) = stack.pop() {
            if let Ok(mut node) = Rc::try_unwrap(d.0) {
                take_children(&mut node, &mut stack);
            }
        }
    }
}

fn take_children(n: &mut Node, out: &mut Vec<Delay>) {
    match n {
        Node::Bind(d, _) | Node::MapSig(_, d) | Node::Tie(_, d) => {
            if Rc::strong_count(&d.0) == 1 {
                let leaf = Delay(Rc::new(Node::Now(Val::Unit)));
                out.push(std::mem::replace(d, leaf));
            }
        }
        Node::Now(_) | Node::Lift(_) | Node::Pfix(..) | Node::Resume(_) | Node::Suspended(_) => {}
    }
}
