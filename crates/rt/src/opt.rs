//! Simplifying the lowered IR before it runs (fast-runtime.md, "As built
//! (stage 4)"). Lowering keeps the program's own structure, so a comparison
//! `a < b` on `Nat` is a call of `Decidable.toBool` on a call of
//! `Nat.decLessThan`, which calls `Bool.decTrue`; `==` on `Char` goes
//! through `Char.decEq`; and an `Ord` method is a projection out of a
//! dictionary, then a closure call. This pass removes that overhead, the
//! way GHC's simplifier or Lean's compiler do, but only the few rules that
//! pay here:
//!
//! - **Inlining** a call of a small, non-recursive global function (its
//!   arguments bound by `let`s, or substituted when they're variables or
//!   constants), and **beta** for a closure applied where it's made.
//! - **Known constructors**: a `match` on a value whose constructor is known
//!   (built by a `let` in scope, matched by an enclosing arm, a constant
//!   whose value is a constructor such as an instance dictionary, or a
//!   literal) takes its arm, with no test.
//! - **Case of case**: a `match` (or `if`) on the result of a branching
//!   expression is pushed into the branches, when it's small, so that each
//!   branch's constructor meets it: `toBool (decTrue b)` is `b`.
//! - A `match` on a `Bool` is an `if`; `if c then True else False` is `c`;
//!   a `match` on a decision from `decEq` on native values is an `if` on
//!   the native equality.
//! - **Calls of known functions**: applying a global, a partial application
//!   or a closure literal is a direct call; a closure capturing constants
//!   (`sortBy Nat.compare`'s comparison) gets its own lambda with them
//!   substituted, which the rules above can then simplify.
//!
//! Everything here is pure and total (a partial computation is a value until
//! the runner runs it), so a binding nothing reads is dropped and work may
//! be duplicated across branches without changing what a program prints.
//! Each body's slots are renamed apart first, so that copies can't clash,
//! and packed again at the end.

use std::collections::HashMap;
use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::native::Native;

use crate::ir::{
    Arm, Body, Expr, Global, GlobalId, GlobalKind, Lambda, LambdaId, Lit, MatchKind, PrimOp,
    Program, Slot, TypeId,
};
use crate::natives::{IntNative, TextNative};

/// The largest body (in [`size`]) that is inlined at a call.
const INLINE_SIZE: usize = 24;
/// The largest lambda body applied where it's made that's inlined.
const BETA_SIZE: usize = 48;
/// How much code case of case may copy at once.
const PUSH_SIZE: usize = 48;
/// Inlining and case of case per body, so that nothing runs away.
const FUEL: u32 = 200;
/// How deeply inlined code may inline in turn.
const DEPTH: u32 = 12;
/// The largest recursive function copied for known function arguments, and
/// how many copies a program may have.
const COPY_SIZE: usize = 200;
const COPIES: usize = 64;
/// The deepest body the passes here take on.
const MAX_NESTING: usize = 1000;

/// The data types the rules need to recognise.
#[derive(Clone, Copy, Debug)]
pub struct Types {
    pub bool_: Option<TypeId>,
    pub decidable: Option<TypeId>,
}

/// Simplifies every body of `p`.
pub fn optimize(p: &mut Program, types: Types) {
    let n = p.globals.len();
    let mut cx = Cx {
        inline: vec![None; n],
        consts: vec![None; n],
        natives: p
            .globals
            .iter()
            .map(|g| match g.kind {
                GlobalKind::Native(op) => Some(op),
                _ => None,
            })
            .collect(),
        params: p.globals.iter().map(|g| g.kind.params()).collect(),
        types,
        true_: p.shapes.true_,
        false_: p.shapes.false_,
        yes: p.shapes.yes,
        no: p.shapes.no,
        lambdas: std::mem::take(&mut p.lambdas),
        specialised: HashMap::new(),
        ctor_arity: p
            .types
            .iter()
            .map(|t| t.ctors.iter().map(|c| c.fields.len()).collect())
            .collect(),
        globals: std::mem::take(&mut p.globals),
        busy: None,
        copies: HashMap::new(),
    };
    // Globals first (in dependency order, so that a callee is simplified
    // before it's inlined), then lambdas, then the entry; each may make
    // copies of globals and lambdas, which are simplified in turn.
    let (mut g, mut l) = (0, 0);
    cx.drain(&mut g, &mut l);
    let entry = std::mem::replace(
        &mut p.entry,
        Body {
            frame: 0,
            expr: Expr::Erased,
        },
    );
    p.entry = cx.body(entry, 0, None);
    cx.drain(&mut g, &mut l);
    p.globals = cx.globals;
    p.lambdas = cx.lambdas;
}

struct Cx {
    /// Each global function small enough to inline: its parameters and its
    /// (simplified) body.
    inline: Vec<Option<Rc<(u32, Expr)>>>,
    /// Each constant whose value is a constructor of closed expressions.
    consts: Vec<Option<Rc<Expr>>>,
    natives: Vec<Option<PrimOp>>,
    params: Vec<u32>,
    types: Types,
    true_: u32,
    false_: u32,
    yes: u32,
    no: u32,
    lambdas: Vec<Lambda>,
    /// Lambdas made by substituting constants for captures, by the lambda
    /// and the constants.
    specialised: HashMap<(u32, String), (LambdaId, Vec<usize>)>,
    ctor_arity: Vec<Vec<usize>>,
    globals: Vec<Global>,
    /// The global being simplified: its body isn't available meanwhile.
    busy: Option<usize>,
    /// Copies of recursive functions with constant function arguments
    /// substituted, by the function and the arguments.
    copies: HashMap<String, GlobalId>,
}

impl Cx {
    /// Simplifies the globals from `g` and the lambdas from `l`, including
    /// those made on the way, until there are none left.
    fn drain(&mut self, g: &mut usize, l: &mut usize) {
        loop {
            if *g < self.globals.len() {
                self.global(*g);
                *g += 1;
            } else if *l < self.lambdas.len() {
                // A lambda's body stays readable while it's simplified:
                // inlining may bring a closure of the same lambda into it.
                let params = self.lambdas[*l].params;
                let body = self.lambdas[*l].body.clone();
                self.lambdas[*l].body = self.body(body, params, None);
                *l += 1;
            } else {
                return;
            }
        }
    }

    /// Simplifies global `i`, and notes whether it's worth inlining or a
    /// known constructor.
    fn global(&mut self, i: usize) {
        let kind = std::mem::replace(
            &mut self.globals[i].kind,
            GlobalKind::Constant {
                body: Body {
                    frame: 0,
                    expr: Expr::Erased,
                },
            },
        );
        self.busy = Some(i);
        let kind = match kind {
            GlobalKind::Function { params, body } => {
                let body = self.body(body, params, Some(i));
                if size(&body.expr) <= INLINE_SIZE && !calls(&body.expr, i) {
                    self.inline[i] = Some(Rc::new((params, body.expr.clone())));
                }
                GlobalKind::Function { params, body }
            }
            GlobalKind::Constant { body } => {
                let body = self.body(body, 0, Some(i));
                if let Expr::Ctor(..) = &body.expr
                    && closed(&body.expr)
                {
                    self.consts[i] = Some(Rc::new(body.expr.clone()));
                }
                GlobalKind::Constant { body }
            }
            native => native,
        };
        self.globals[i].kind = kind;
        self.busy = None;
    }

    /// A body simplified, its slots packed again. `global` is the global it
    /// belongs to, which it doesn't inline into itself.
    fn body(&mut self, body: Body, params: u32, global: Option<usize>) -> Body {
        // The passes here recurse over the body: one nested more deeply
        // than this (a long list literal, say) is left as lowered.
        if nesting(&body.expr) > MAX_NESTING {
            return body;
        }
        let mut next = params;
        let expr = Renamer::new(&mut next, None).expr(&body.expr);
        let mut s = Simp {
            cx: self,
            next,
            env: HashMap::new(),
            fuel: FUEL,
            depth: 0,
            global,
        };
        let expr = s.simp(expr);
        let mut packer = Packer {
            map: HashMap::new(),
            depth: params,
            max: params,
        };
        let expr = packer.expr(expr);
        Body {
            frame: packer.max,
            expr,
        }
    }
}

// ------------------------------------------------------------- measuring

/// How deeply `e` nests, found without recursing.
fn nesting<'a>(e: &'a Expr) -> usize {
    let mut max = 0;
    let mut stack = vec![(e, 1)];
    while let Some((e, d)) = stack.pop() {
        max = max.max(d);
        let mut push = |x: &'a Expr| stack.push((x, d + 1));
        match e {
            Expr::Local(_)
            | Expr::Captured(_)
            | Expr::Global(_)
            | Expr::Erased
            | Expr::Lit(_)
            | Expr::DoneK
            | Expr::Unreachable => {}
            Expr::Call(_, a)
            | Expr::Prim(_, a)
            | Expr::PartialApp(_, a)
            | Expr::Closure(_, a)
            | Expr::Ctor(_, _, a) => a.iter().for_each(&mut push),
            Expr::Apply(f, a) => {
                push(f);
                a.iter().for_each(&mut push);
            }
            Expr::Let(_, v, b) => {
                push(v);
                push(b);
            }
            Expr::Match(x, _, arms) => {
                push(x);
                arms.iter().for_each(|arm| push(&arm.body));
            }
            Expr::NumSwitch(x, arms, d) => {
                push(x);
                arms.iter().for_each(|(_, b)| push(b));
                push(d);
            }
            Expr::If(c, t, f) => {
                push(c);
                push(t);
                push(f);
            }
        }
    }
    max
}

/// How big `e` is: its nodes.
fn size(e: &Expr) -> usize {
    1 + match e {
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => 0,
        Expr::Call(_, a)
        | Expr::Prim(_, a)
        | Expr::PartialApp(_, a)
        | Expr::Closure(_, a)
        | Expr::Ctor(_, _, a) => a.iter().map(size).sum(),
        Expr::Apply(f, a) => size(f) + a.iter().map(size).sum::<usize>(),
        Expr::Let(_, v, b) => size(v) + size(b),
        Expr::Match(s, _, arms) => size(s) + arms.iter().map(|a| size(&a.body)).sum::<usize>(),
        Expr::NumSwitch(s, arms, d) => {
            size(s) + arms.iter().map(|(_, b)| size(b)).sum::<usize>() + size(d)
        }
        Expr::If(c, t, e) => size(c) + size(t) + size(e),
    }
}

/// Whether `e` refers to global `g` (calls it, or makes a function of it).
fn calls(e: &Expr, g: usize) -> bool {
    let any = |a: &[Expr]| a.iter().any(|x| calls(x, g));
    match e {
        Expr::Global(h) => h.0 as usize == g,
        Expr::Call(h, a) | Expr::PartialApp(h, a) => h.0 as usize == g || any(a),
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => false,
        Expr::Prim(_, a) | Expr::Closure(_, a) | Expr::Ctor(_, _, a) => any(a),
        Expr::Apply(f, a) => calls(f, g) || any(a),
        Expr::Let(_, v, b) => calls(v, g) || calls(b, g),
        Expr::Match(s, _, arms) => calls(s, g) || arms.iter().any(|a| calls(&a.body, g)),
        Expr::NumSwitch(s, arms, d) => {
            calls(s, g) || arms.iter().any(|(_, b)| calls(b, g)) || calls(d, g)
        }
        Expr::If(c, t, e) => calls(c, g) || calls(t, g) || calls(e, g),
    }
}

/// How many times `e` reads slot `s`.
fn reads(e: &Expr, s: Slot) -> usize {
    let all = |a: &[Expr]| a.iter().map(|x| reads(x, s)).sum::<usize>();
    match e {
        Expr::Local(t) => usize::from(*t == s),
        Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => 0,
        Expr::Call(_, a)
        | Expr::Prim(_, a)
        | Expr::PartialApp(_, a)
        | Expr::Closure(_, a)
        | Expr::Ctor(_, _, a) => all(a),
        Expr::Apply(f, a) => reads(f, s) + all(a),
        Expr::Let(_, v, b) => reads(v, s) + reads(b, s),
        Expr::Match(x, _, arms) => {
            reads(x, s) + arms.iter().map(|a| reads(&a.body, s)).sum::<usize>()
        }
        Expr::NumSwitch(x, arms, d) => {
            reads(x, s) + arms.iter().map(|(_, b)| reads(b, s)).sum::<usize>() + reads(d, s)
        }
        Expr::If(c, t, e) => reads(c, s) + reads(t, s) + reads(e, s),
    }
}

/// A value that's free to copy: reading it does no work worth sharing.
fn trivial(e: &Expr) -> bool {
    match e {
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK => true,
        Expr::Ctor(_, _, fields) => fields.is_empty(),
        _ => false,
    }
}

/// An expression that reads no variables: it means the same anywhere.
fn closed(e: &Expr) -> bool {
    match e {
        Expr::Global(_) | Expr::Erased | Expr::Lit(_) | Expr::DoneK => true,
        Expr::PartialApp(_, a) | Expr::Closure(_, a) | Expr::Ctor(_, _, a) => a.iter().all(closed),
        _ => false,
    }
}

/// A constant that's cheap to copy into a lambda: no allocation to repeat.
fn constant(e: &Expr) -> bool {
    match e {
        Expr::Global(_) | Expr::Erased | Expr::Lit(_) | Expr::DoneK => true,
        Expr::Ctor(_, _, a) => a.is_empty(),
        _ => false,
    }
}

/// Whether `e` branches: its value is one of several leaves.
fn branching(e: &Expr) -> bool {
    match e {
        Expr::If(..) | Expr::Match(..) | Expr::NumSwitch(..) => true,
        Expr::Let(_, _, b) => branching(b),
        _ => false,
    }
}

/// How many leaves `e` has (unreachable ones don't count).
fn leaves(e: &Expr) -> usize {
    match e {
        Expr::If(_, t, e) => leaves(t) + leaves(e),
        Expr::Match(_, _, arms) => arms.iter().map(|a| leaves(&a.body)).sum(),
        Expr::NumSwitch(_, arms, d) => {
            arms.iter().map(|(_, b)| leaves(b)).sum::<usize>() + leaves(d)
        }
        Expr::Let(_, _, b) => leaves(b),
        Expr::Unreachable => 0,
        _ => 1,
    }
}

/// The native `Bool` equality a `decEq` native decides.
fn equality(op: PrimOp) -> Option<PrimOp> {
    match op {
        PrimOp::Nat(Native::DecEqNat) => Some(PrimOp::Nat(Native::EqNat)),
        PrimOp::Int(IntNative::DecEqInt) => Some(PrimOp::IntEqual),
        PrimOp::Text(TextNative::DecEqText) => Some(PrimOp::TextEqual),
        _ => None,
    }
}

// --------------------------------------------------------------- renaming

/// Copies an expression with each variable it binds given a fresh slot,
/// and the free ones replaced as `map` says (a callee's parameters by its
/// arguments, say), and what a lambda captured by `captures`.
struct Renamer<'a> {
    map: HashMap<Slot, Expr>,
    next: &'a mut Slot,
    captures: Option<&'a [Expr]>,
}

impl<'a> Renamer<'a> {
    fn new(next: &'a mut Slot, captures: Option<&'a [Expr]>) -> Self {
        Renamer {
            map: HashMap::new(),
            next,
            captures,
        }
    }

    fn fresh(&mut self, s: Slot) -> (Slot, Option<Expr>) {
        let n = *self.next;
        *self.next += 1;
        (n, self.map.insert(s, Expr::Local(n)))
    }

    fn restore(&mut self, s: Slot, old: Option<Expr>) {
        match old {
            Some(e) => self.map.insert(s, e),
            None => self.map.remove(&s),
        };
    }

    fn all(&mut self, es: &[Expr]) -> Vec<Expr> {
        es.iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, e: &Expr) -> Expr {
        match e {
            Expr::Local(s) => self.map.get(s).cloned().unwrap_or(Expr::Local(*s)),
            Expr::Captured(i) => match self.captures {
                Some(c) => c[*i as usize].clone(),
                None => Expr::Captured(*i),
            },
            Expr::Global(_) | Expr::Erased | Expr::Lit(_) | Expr::DoneK | Expr::Unreachable => {
                e.clone()
            }
            Expr::Call(g, a) => Expr::Call(*g, self.all(a)),
            Expr::Prim(op, a) => Expr::Prim(*op, self.all(a)),
            Expr::PartialApp(g, a) => Expr::PartialApp(*g, self.all(a)),
            Expr::Apply(f, a) => Expr::Apply(Box::new(self.expr(f)), self.all(a)),
            Expr::Closure(l, a) => Expr::Closure(*l, self.all(a)),
            Expr::Ctor(t, c, a) => Expr::Ctor(*t, *c, self.all(a)),
            Expr::Let(s, v, b) => {
                let v = self.expr(v);
                let (n, old) = self.fresh(*s);
                let b = self.expr(b);
                self.restore(*s, old);
                Expr::Let(n, Box::new(v), Box::new(b))
            }
            Expr::Match(x, k, arms) => {
                let x = self.expr(x);
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let mut saved = Vec::new();
                        let fields = arm
                            .fields
                            .iter()
                            .map(|(i, s)| {
                                let (n, old) = self.fresh(*s);
                                saved.push((*s, old));
                                (*i, n)
                            })
                            .collect();
                        let body = self.expr(&arm.body);
                        for (s, old) in saved.into_iter().rev() {
                            self.restore(s, old);
                        }
                        Arm {
                            ctor: arm.ctor,
                            fields,
                            body,
                        }
                    })
                    .collect();
                Expr::Match(Box::new(x), *k, arms)
            }
            Expr::NumSwitch(x, arms, d) => Expr::NumSwitch(
                Box::new(self.expr(x)),
                arms.iter()
                    .map(|(n, b)| (n.clone(), self.expr(b)))
                    .collect(),
                Box::new(self.expr(d)),
            ),
            Expr::If(c, t, e) => Expr::If(
                Box::new(self.expr(c)),
                Box::new(self.expr(t)),
                Box::new(self.expr(e)),
            ),
        }
    }
}

/// Packs a body's slots again after simplifying: each variable gets the
/// lowest slot free in its scope, and sibling scopes share slots, as
/// lowering gives them out.
struct Packer {
    map: HashMap<Slot, Slot>,
    depth: Slot,
    max: Slot,
}

impl Packer {
    fn bind(&mut self, s: Slot) -> (Slot, Option<Slot>) {
        let n = self.depth;
        self.depth += 1;
        self.max = self.max.max(self.depth);
        (n, self.map.insert(s, n))
    }

    fn unbind(&mut self, s: Slot, old: Option<Slot>) {
        match old {
            Some(o) => self.map.insert(s, o),
            None => self.map.remove(&s),
        };
        self.depth -= 1;
    }

    fn all(&mut self, es: Vec<Expr>) -> Vec<Expr> {
        es.into_iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, e: Expr) -> Expr {
        match e {
            Expr::Local(s) => Expr::Local(self.map.get(&s).copied().unwrap_or(s)),
            Expr::Captured(_)
            | Expr::Global(_)
            | Expr::Erased
            | Expr::Lit(_)
            | Expr::DoneK
            | Expr::Unreachable => e,
            Expr::Call(g, a) => Expr::Call(g, self.all(a)),
            Expr::Prim(op, a) => Expr::Prim(op, self.all(a)),
            Expr::PartialApp(g, a) => Expr::PartialApp(g, self.all(a)),
            Expr::Apply(f, a) => {
                let f = self.expr(*f);
                Expr::Apply(Box::new(f), self.all(a))
            }
            Expr::Closure(l, a) => Expr::Closure(l, self.all(a)),
            Expr::Ctor(t, c, a) => Expr::Ctor(t, c, self.all(a)),
            Expr::Let(s, v, b) => {
                let v = self.expr(*v);
                let (n, old) = self.bind(s);
                let b = self.expr(*b);
                self.unbind(s, old);
                Expr::Let(n, Box::new(v), Box::new(b))
            }
            Expr::Match(x, k, arms) => {
                let x = self.expr(*x);
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let mut saved = Vec::new();
                        let fields = arm
                            .fields
                            .iter()
                            .map(|(i, s)| {
                                let (n, old) = self.bind(*s);
                                saved.push((*s, old));
                                (*i, n)
                            })
                            .collect();
                        let body = self.expr(arm.body);
                        for (s, old) in saved.into_iter().rev() {
                            self.unbind(s, old);
                        }
                        Arm {
                            ctor: arm.ctor,
                            fields,
                            body,
                        }
                    })
                    .collect();
                Expr::Match(Box::new(x), k, arms)
            }
            Expr::NumSwitch(x, arms, d) => {
                let x = self.expr(*x);
                let arms = arms.into_iter().map(|(n, b)| (n, self.expr(b))).collect();
                let d = self.expr(*d);
                Expr::NumSwitch(Box::new(x), arms, Box::new(d))
            }
            Expr::If(c, t, e) => {
                let c = self.expr(*c);
                let t = self.expr(*t);
                let e = self.expr(*e);
                Expr::If(Box::new(c), Box::new(t), Box::new(e))
            }
        }
    }
}

// ------------------------------------------------------------- simplifying

/// What's known about a slot's value.
#[derive(Clone)]
enum Known {
    /// It's this expression, free to copy: read it instead.
    Alias(Expr),
    /// A constructor with these fields (trivial expressions).
    Ctor(u32, Vec<Expr>),
    /// The decision a `decEq` native makes on these arguments: its
    /// `Bool` version is this native.
    Decision(PrimOp, Vec<Expr>),
    /// A closure or partial application of trivial values: applying it
    /// is a call.
    Fun(Expr),
}

struct Simp<'a> {
    cx: &'a mut Cx,
    /// The next fresh slot.
    next: Slot,
    env: HashMap<Slot, Known>,
    fuel: u32,
    depth: u32,
    global: Option<usize>,
}

impl Simp<'_> {
    fn fresh(&mut self) -> Slot {
        let n = self.next;
        self.next += 1;
        n
    }

    /// A copy of `e` with fresh slots for what it binds, and `map` for
    /// what it reads.
    fn copy(&mut self, e: &Expr, map: HashMap<Slot, Expr>, captures: Option<&[Expr]>) -> Expr {
        let mut r = Renamer {
            map,
            next: &mut self.next,
            captures,
        };
        r.expr(e)
    }

    /// The truth value of `e`, if it's known.
    fn truth(&self, e: &Expr) -> Option<bool> {
        let bool_ = self.cx.types.bool_?;
        let tag = match e {
            Expr::Ctor(t, c, f) if *t == bool_ && f.is_empty() => *c,
            Expr::Local(s) => match self.env.get(s) {
                Some(Known::Ctor(c, _)) => *c,
                _ => return None,
            },
            _ => return None,
        };
        Some(tag == self.cx.true_)
    }

    /// Records what's known about `slot`, bound to `value`.
    fn learn(&mut self, slot: Slot, value: &Expr) {
        match value {
            Expr::Ctor(_, c, fields) if fields.iter().all(trivial) => {
                self.env.insert(slot, Known::Ctor(*c, fields.clone()));
            }
            Expr::Closure(_, caps) | Expr::PartialApp(_, caps) if caps.iter().all(trivial) => {
                self.env.insert(slot, Known::Fun(value.clone()));
            }
            Expr::Prim(op, args) => {
                if let Some(eq) = equality(*op) {
                    self.env.insert(slot, Known::Decision(eq, args.clone()));
                }
            }
            _ => {}
        }
    }

    /// Binds every field of `arm` (a constructor of type `t`) to a slot,
    /// fresh ones for those it didn't bind, and returns them in order.
    fn complete_fields(&mut self, t: TypeId, arm: &mut Arm) -> Vec<Expr> {
        let n = self.cx.ctor_arity[t.0 as usize][arm.ctor as usize];
        let mut fields = Vec::with_capacity(n);
        for i in 0..n {
            let i = u32::try_from(i).expect("fields fit");
            let slot = match arm.fields.iter().find(|(j, _)| *j == i) {
                Some((_, slot)) => *slot,
                None => {
                    let slot = self.fresh();
                    arm.fields.push((i, slot));
                    slot
                }
            };
            fields.push(Expr::Local(slot));
        }
        arm.fields.sort_by_key(|(i, _)| *i);
        fields
    }

    /// A `Nat` operation on literals, computed now.
    fn fold(&self, e: Expr) -> Expr {
        let Expr::Prim(PrimOp::Nat(op), args) = &e else {
            return e;
        };
        let [Expr::Lit(Lit::Nat(a)), Expr::Lit(Lit::Nat(b))] = &args[..] else {
            return e;
        };
        let truth = |b: bool| match self.cx.types.bool_ {
            Some(t) => Expr::Ctor(
                t,
                if b { self.cx.true_ } else { self.cx.false_ },
                Vec::new(),
            ),
            None => e.clone(),
        };
        match op {
            Native::Add => Expr::Lit(Lit::Nat(a + b)),
            Native::Mul => Expr::Lit(Lit::Nat(a * b)),
            // `Nat` subtraction stops at zero.
            Native::Sub => Expr::Lit(Lit::Nat(if a >= b { a - b } else { BigUint::ZERO })),
            Native::Leq => truth(a <= b),
            Native::EqNat => truth(a == b),
            _ => e.clone(),
        }
    }

    /// `let slot = value; body`, `value` simplified already, `body` not.
    fn let_(&mut self, slot: Slot, value: Expr, body: Expr) -> Expr {
        self.let_with(slot, value, |s| s.simp(body))
    }

    /// `let slot = value; body`, `value` simplified already, and `body`
    /// what `simp_body` makes in the scope of what's known about it.
    fn let_with(
        &mut self,
        slot: Slot,
        value: Expr,
        simp_body: impl FnOnce(&mut Self) -> Expr,
    ) -> Expr {
        if trivial(&value) {
            self.env.insert(slot, Known::Alias(value));
            let out = simp_body(self);
            self.env.remove(&slot);
            return out;
        }
        // `let a = (match s { C(f…) => e }); body`, with one arm that can
        // happen (a projection out of a record or pair): the body moves into
        // the arm, where `s` is known to be `C(f…)`, so that a later match on
        // `s` (the other projection) needs no test.
        if let Expr::Match(x, MatchKind::Data(t), arms) = &value
            && let Expr::Local(s) = **x
            && arms
                .iter()
                .filter(|a| !matches!(a.body, Expr::Unreachable))
                .count()
                == 1
        {
            let t = *t;
            let Expr::Match(x, k, mut arms) = value else {
                unreachable!("matched above")
            };
            let at = arms
                .iter()
                .position(|a| !matches!(a.body, Expr::Unreachable))
                .expect("one arm");
            let arm_body = std::mem::replace(&mut arms[at].body, Expr::Unreachable);
            let fields = self.complete_fields(t, &mut arms[at]);
            let old = self.env.insert(s, Known::Ctor(arms[at].ctor, fields));
            let body = self.let_with(slot, arm_body, simp_body);
            match old {
                Some(o) => self.env.insert(s, o),
                None => self.env.remove(&s),
            };
            arms[at].fields.retain(|(_, f)| reads(&body, *f) > 0);
            arms[at].body = body;
            return Expr::Match(x, k, arms);
        }
        self.learn(slot, &value);
        let body = simp_body(self);
        self.env.remove(&slot);
        match reads(&body, slot) {
            // Nothing reads it: it needn't be computed.
            0 => return body,
            // Read once, first thing: no need for the variable.
            1 if matches!(body, Expr::Local(s) if s == slot) => return value,
            1 if !branching(&value)
                && matches!(&body, Expr::If(c, ..) if matches!(**c, Expr::Local(s) if s == slot)) =>
            {
                let Expr::If(_, t, e) = body else {
                    unreachable!()
                };
                return Expr::If(Box::new(value), t, e);
            }
            // Case of case: the body only takes it apart.
            1 if self.fuel > 0 && branching(&value) && leaves(&value) >= 2 => {
                let scrutinised = match &body {
                    Expr::Match(x, ..) | Expr::If(x, ..) => {
                        matches!(**x, Expr::Local(s) if s == slot)
                    }
                    _ => false,
                };
                if scrutinised && size(&body) * (leaves(&value) - 1) <= PUSH_SIZE {
                    self.fuel -= 1;
                    return self.map_leaves(value, &mut |s, leaf| {
                        let n = s.fresh();
                        let copy = s.copy(&body, HashMap::from([(slot, Expr::Local(n))]), None);
                        let value = leaf;
                        s.let_(n, value, copy)
                    });
                }
            }
            _ => {}
        }
        Expr::Let(slot, Box::new(value), Box::new(body))
    }

    /// `e` with each of its leaves replaced by `f` of it.
    fn map_leaves(&mut self, e: Expr, f: &mut dyn FnMut(&mut Self, Expr) -> Expr) -> Expr {
        match e {
            Expr::If(c, t, e) => {
                let t = self.map_leaves(*t, f);
                let e = self.map_leaves(*e, f);
                if self.truth(&t) == Some(true) && self.truth(&e) == Some(false) {
                    return *c;
                }
                Expr::If(c, Box::new(t), Box::new(e))
            }
            Expr::Match(x, k, arms) => Expr::Match(
                x,
                k,
                arms.into_iter()
                    .map(|arm| Arm {
                        ctor: arm.ctor,
                        fields: arm.fields,
                        body: self.map_leaves(arm.body, f),
                    })
                    .collect(),
            ),
            Expr::NumSwitch(x, arms, d) => {
                let arms = arms
                    .into_iter()
                    .map(|(n, b)| (n, self.map_leaves(b, f)))
                    .collect();
                let d = self.map_leaves(*d, f);
                Expr::NumSwitch(x, arms, Box::new(d))
            }
            Expr::Let(s, v, b) => Expr::Let(s, v, Box::new(self.map_leaves(*b, f))),
            Expr::Unreachable => Expr::Unreachable,
            leaf => f(self, leaf),
        }
    }

    fn all(&mut self, es: Vec<Expr>) -> Vec<Expr> {
        es.into_iter().map(|e| self.simp(e)).collect()
    }

    fn simp(&mut self, e: Expr) -> Expr {
        match e {
            Expr::Local(s) => match self.env.get(&s) {
                Some(Known::Alias(e)) => e.clone(),
                _ => Expr::Local(s),
            },
            Expr::Captured(_)
            | Expr::Global(_)
            | Expr::Erased
            | Expr::Lit(_)
            | Expr::DoneK
            | Expr::Unreachable => e,
            Expr::Let(s, v, b) => {
                let v = self.simp(*v);
                self.let_(s, v, *b)
            }
            Expr::Call(g, args) => {
                let args = self.all(args);
                self.call(g, args)
            }
            Expr::Prim(op, args) => {
                let args = self.all(args);
                self.fold(prim(op, args))
            }
            Expr::PartialApp(g, args) => Expr::PartialApp(g, self.all(args)),
            Expr::Ctor(t, c, args) => Expr::Ctor(t, c, self.all(args)),
            Expr::Closure(l, caps) => {
                let caps = self.all(caps);
                self.closure(l, caps)
            }
            Expr::Apply(f, args) => {
                let f = self.simp(*f);
                let args = self.all(args);
                self.apply(f, args)
            }
            Expr::If(c, t, e) => {
                let c = self.simp(*c);
                self.if_(c, *t, *e)
            }
            Expr::NumSwitch(x, arms, d) => {
                let x = self.simp(*x);
                if let Expr::Lit(Lit::Nat(n)) = &x {
                    let body = arms
                        .into_iter()
                        .find(|(m, _)| m == n)
                        .map_or(*d, |(_, b)| b);
                    return self.simp(body);
                }
                let arms = arms.into_iter().map(|(n, b)| (n, self.simp(b))).collect();
                let d = self.simp(*d);
                Expr::NumSwitch(Box::new(x), arms, Box::new(d))
            }
            Expr::Match(x, k, arms) => {
                let x = self.simp(*x);
                self.match_(x, k, arms)
            }
        }
    }

    /// `if c then t else e`, `c` simplified already.
    fn if_(&mut self, c: Expr, t: Expr, e: Expr) -> Expr {
        if let Some(b) = self.truth(&c) {
            return self.simp(if b { t } else { e });
        }
        if self.fuel > 0
            && branching(&c)
            && leaves(&c) >= 2
            && (size(&t) + size(&e)) * (leaves(&c) - 1) <= PUSH_SIZE
        {
            self.fuel -= 1;
            return self.map_leaves(c, &mut |s, leaf| {
                let t = s.copy(&t, HashMap::new(), None);
                let e = s.copy(&e, HashMap::new(), None);
                s.if_(leaf, t, e)
            });
        }
        let known = |s: &mut Self, b: bool, body: Expr| {
            if let Expr::Local(slot) = &c
                && s.cx.types.bool_.is_some()
            {
                let tag = if b { s.cx.true_ } else { s.cx.false_ };
                let old = s.env.insert(*slot, Known::Ctor(tag, Vec::new()));
                let out = s.simp(body);
                match old {
                    Some(o) => s.env.insert(*slot, o),
                    None => s.env.remove(slot),
                };
                out
            } else {
                s.simp(body)
            }
        };
        let t = known(self, true, t);
        let e = known(self, false, e);
        if self.truth(&t) == Some(true) && self.truth(&e) == Some(false) {
            return c;
        }
        Expr::If(Box::new(c), Box::new(t), Box::new(e))
    }

    /// A match on `x` (simplified already).
    fn match_(&mut self, x: Expr, k: MatchKind, arms: Vec<Arm>) -> Expr {
        // A known constructor takes its arm.
        let known: Option<(u32, Vec<Expr>)> = match (&x, k) {
            (Expr::Local(s), MatchKind::Data(_)) => match self.env.get(s) {
                Some(Known::Ctor(c, fields)) => Some((*c, fields.clone())),
                _ => None,
            },
            (Expr::Ctor(_, c, fields), MatchKind::Data(_)) => Some((*c, fields.clone())),
            (Expr::Global(g), MatchKind::Data(_)) => self.cx.consts[g.0 as usize]
                .as_deref()
                .and_then(|e| match e {
                    Expr::Ctor(_, c, fields) => Some((*c, fields.clone())),
                    _ => None,
                }),
            (Expr::Lit(Lit::Nat(n)), MatchKind::Nat) => Some(if *n == BigUint::ZERO {
                (0, Vec::new())
            } else {
                (1, vec![Expr::Lit(Lit::Nat(n - 1u32))])
            }),
            _ => None,
        };
        let mut arms = arms;
        if let Some((c, fields)) = known
            && let Some(at) = arms.iter().position(|a| a.ctor == c)
        {
            let arm = arms.swap_remove(at);
            let mut lets = Vec::new();
            for (i, slot) in &arm.fields {
                let v = fields[*i as usize].clone();
                if trivial(&v) {
                    self.env.insert(*slot, Known::Alias(v));
                } else {
                    lets.push((*slot, v));
                }
            }
            let mut out = arm.body;
            for (slot, v) in lets.into_iter().rev() {
                out = Expr::Let(slot, Box::new(v), Box::new(out));
            }
            let out = self.simp(out);
            for (_, slot) in &arm.fields {
                self.env.remove(slot);
            }
            return out;
        }
        if let MatchKind::Data(t) = k {
            // A decision from `decEq` on native values: an `if` on equality.
            if Some(t) == self.cx.types.decidable
                && let Expr::Local(s) = &x
                && let Some(Known::Decision(eq, args)) = self.env.get(s).cloned()
            {
                let (yes, no) = self.two(arms, self.cx.yes, self.cx.no);
                return self.if_(Expr::Prim(eq, args), yes, no);
            }
            // A match on a `Bool` is an `if`.
            if Some(t) == self.cx.types.bool_ {
                let (t, e) = self.two(arms, self.cx.true_, self.cx.false_);
                return self.if_(x, t, e);
            }
        }
        // Otherwise each arm knows the constructor.
        let arms = arms
            .into_iter()
            .map(|mut arm| {
                let mut old = None;
                let mut learned = None;
                if let (Expr::Local(s), MatchKind::Data(t)) = (&x, k) {
                    let n = self.cx.ctor_arity[t.0 as usize][arm.ctor as usize];
                    let mut fields = Vec::with_capacity(n);
                    for i in 0..n {
                        let i = u32::try_from(i).expect("fields fit");
                        let slot = match arm.fields.iter().find(|(j, _)| *j == i) {
                            Some((_, slot)) => *slot,
                            None => {
                                let slot = self.fresh();
                                arm.fields.push((i, slot));
                                slot
                            }
                        };
                        fields.push(Expr::Local(slot));
                    }
                    arm.fields.sort_by_key(|(i, _)| *i);
                    old = self.env.insert(*s, Known::Ctor(arm.ctor, fields));
                    learned = Some(*s);
                }
                let body = self.simp(arm.body);
                if let Some(s) = learned {
                    match old.take() {
                        Some(o) => self.env.insert(s, o),
                        None => self.env.remove(&s),
                    };
                }
                let fields = arm
                    .fields
                    .into_iter()
                    .filter(|(_, slot)| reads(&body, *slot) > 0)
                    .collect();
                Arm {
                    ctor: arm.ctor,
                    fields,
                    body,
                }
            })
            .collect();
        Expr::Match(Box::new(x), k, arms)
    }

    /// The bodies of the arms for constructors `a` and `b` of a type with
    /// two constructors and no fields.
    fn two(&mut self, arms: Vec<Arm>, a: u32, b: u32) -> (Expr, Expr) {
        let mut x = None;
        let mut y = None;
        for arm in arms {
            if arm.ctor == a {
                x = Some(arm.body);
            } else if arm.ctor == b {
                y = Some(arm.body);
            }
        }
        (
            x.unwrap_or(Expr::Unreachable),
            y.unwrap_or(Expr::Unreachable),
        )
    }

    /// A call of global `g` with all its arguments (simplified already).
    fn call(&mut self, g: GlobalId, args: Vec<Expr>) -> Expr {
        let i = g.0 as usize;
        if Some(i) != self.global
            && self.fuel > 0
            && self.depth < DEPTH
            && let Some(inline) = self.cx.inline[i].clone()
        {
            self.fuel -= 1;
            let (params, body) = &*inline;
            debug_assert_eq!(*params as usize, args.len());
            return self.instantiate(body, args, None, &[]);
        }
        match self.specialise(g, &args) {
            Some(call) => call,
            None => Expr::Call(g, args),
        }
    }

    /// A function value that's the same wherever it's read: a global, a
    /// partial application of constants, or a closure that captures
    /// nothing. Through a variable bound to one, too.
    fn known_function(&self, e: &Expr) -> Option<Expr> {
        match e {
            Expr::Global(h) if self.cx.params[h.0 as usize] > 0 => Some(e.clone()),
            Expr::PartialApp(_, a) if a.iter().all(constant) => Some(e.clone()),
            Expr::Closure(_, a) if a.is_empty() => Some(e.clone()),
            Expr::Local(s) => match self.env.get(s) {
                Some(Known::Fun(f)) => self.known_function(&f.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// A call of recursive global `g` with some arguments known functions
    /// (`map scramble xs`, `merge less xs ys`): a call of a copy of `g` with
    /// them substituted, whose own recursive calls that pass them on call
    /// the copy. Then applying them is a direct call, which can be inlined.
    fn specialise(&mut self, g: GlobalId, args: &[Expr]) -> Option<Expr> {
        let i = g.0 as usize;
        if self.cx.busy == Some(i) || self.cx.copies.len() >= COPIES {
            return None;
        }
        let GlobalKind::Function { params, body } = &self.cx.globals[i].kind else {
            return None;
        };
        if !calls(&body.expr, i) || size(&body.expr) > COPY_SIZE {
            return None;
        }
        let known: Vec<(usize, Expr)> = args
            .iter()
            .enumerate()
            .filter_map(|(k, a)| self.known_function(a).map(|f| (k, f)))
            .collect();
        if known.is_empty() || known.len() == args.len() {
            return None;
        }
        let key = format!(
            "{i}:{}",
            known
                .iter()
                .map(|(k, f)| format!("{k}={f:?};"))
                .collect::<String>()
        );
        let id = match self.cx.copies.get(&key) {
            Some(id) => *id,
            None => {
                let params = *params;
                let id = GlobalId(u32::try_from(self.cx.globals.len()).expect("fits"));
                let positions: Vec<usize> = known.iter().map(|(k, _)| *k).collect();
                let redirected = redirect(&body.expr, g, &positions, id);
                let mut map = HashMap::new();
                let mut kept = 0;
                for p in 0..params {
                    match known.iter().find(|(k, _)| *k == p as usize) {
                        Some((_, f)) => map.insert(p, f.clone()),
                        None => {
                            kept += 1;
                            map.insert(p, Expr::Local(kept - 1))
                        }
                    };
                }
                let mut next = kept;
                let expr = Renamer {
                    map,
                    next: &mut next,
                    captures: None,
                }
                .expr(&redirected);
                let original = &self.cx.globals[i];
                self.cx.globals.push(Global {
                    name: format!("{}[{}]", original.name, self.cx.copies.len()).into(),
                    def: original.def,
                    kind: GlobalKind::Function {
                        params: kept,
                        body: Body { frame: next, expr },
                    },
                });
                self.cx.inline.push(None);
                self.cx.consts.push(None);
                self.cx.natives.push(None);
                self.cx.params.push(kept);
                self.cx.copies.insert(key, id);
                id
            }
        };
        let rest = args
            .iter()
            .enumerate()
            .filter(|(k, _)| !known.iter().any(|(j, _)| j == k))
            .map(|(_, a)| a.clone())
            .collect();
        Some(Expr::Call(id, rest))
    }

    /// `body` (of a function or lambda) with its parameters bound to `args`
    /// and what it captured to `captures`, simplified.
    fn instantiate(
        &mut self,
        body: &Expr,
        args: Vec<Expr>,
        _lambda: Option<LambdaId>,
        captures: &[Expr],
    ) -> Expr {
        let mut lets = Vec::new();
        let mut map = HashMap::new();
        for (p, a) in args.into_iter().enumerate() {
            let p = u32::try_from(p).expect("params fit");
            if trivial(&a) {
                map.insert(p, a);
            } else {
                let n = self.fresh();
                map.insert(p, Expr::Local(n));
                lets.push((n, a));
            }
        }
        let mut caps = Vec::new();
        for c in captures {
            if trivial(c) {
                caps.push(c.clone());
            } else {
                let n = self.fresh();
                caps.push(Expr::Local(n));
                lets.push((n, c.clone()));
            }
        }
        let body = self.copy(body, map, (!captures.is_empty()).then_some(&caps[..]));
        lets.reverse();
        self.bind_lets(lets, body)
    }

    /// `lets` (the first last) around `body`, each as [`Simp::let_with`]
    /// does it, so that case of case can take the bound values apart.
    fn bind_lets(&mut self, mut lets: Vec<(Slot, Expr)>, body: Expr) -> Expr {
        match lets.pop() {
            None => {
                self.depth += 1;
                let out = self.simp(body);
                self.depth -= 1;
                out
            }
            Some((n, v)) => self.let_with(n, v, move |s| s.bind_lets(lets, body)),
        }
    }

    /// `f` applied to `args`, both simplified already.
    fn apply(&mut self, f: Expr, mut args: Vec<Expr>) -> Expr {
        match f {
            Expr::Global(g) => self.saturate(g, Vec::new(), args),
            Expr::PartialApp(g, held) => self.saturate(g, held, args),
            Expr::Apply(f, mut first) => {
                first.append(&mut args);
                Expr::Apply(f, first)
            }
            Expr::Closure(l, caps)
                if self.cx.lambdas[l.0 as usize].params as usize == args.len()
                    && size(&self.cx.lambdas[l.0 as usize].body.expr)
                        <= if caps.is_empty() {
                            COPY_SIZE
                        } else {
                            BETA_SIZE
                        }
                    && self.fuel > 0
                    && self.depth < DEPTH =>
            {
                self.fuel -= 1;
                let body = self.cx.lambdas[l.0 as usize].body.expr.clone();
                self.instantiate(&body, args, Some(l), &caps)
            }
            Expr::Local(s) => match self.env.get(&s) {
                Some(Known::Fun(f)) => {
                    let f = f.clone();
                    self.apply(f, args)
                }
                _ => Expr::Apply(Box::new(Expr::Local(s)), args),
            },
            f => Expr::Apply(Box::new(f), args),
        }
    }

    /// Global `g` applied to `held` then `args`.
    fn saturate(&mut self, g: GlobalId, mut held: Vec<Expr>, mut args: Vec<Expr>) -> Expr {
        let i = g.0 as usize;
        let n = self.cx.params[i] as usize;
        held.append(&mut args);
        let mut all = held;
        if n == 0 {
            // A constant's value, a function value.
            return Expr::Apply(Box::new(Expr::Global(g)), all);
        }
        if all.len() < n {
            return Expr::PartialApp(g, all);
        }
        let rest = all.split_off(n);
        let call = match self.cx.natives[i] {
            Some(op) => self.fold(prim(op, all)),
            None => self.call(g, all),
        };
        if rest.is_empty() {
            call
        } else {
            self.apply(call, rest)
        }
    }

    /// A closure of lambda `l`: if it captures constants, a closure of a
    /// lambda with them substituted, which can be simplified with them.
    fn closure(&mut self, l: LambdaId, caps: Vec<Expr>) -> Expr {
        let fixed: Vec<usize> = (0..caps.len()).filter(|i| constant(&caps[*i])).collect();
        if fixed.is_empty() {
            return Expr::Closure(l, caps);
        }
        let key = (
            l.0,
            fixed
                .iter()
                .map(|i| format!("{i}={:?};", caps[*i]))
                .collect::<String>(),
        );
        let (id, kept) = match self.cx.specialised.get(&key) {
            Some(found) => found.clone(),
            None => {
                let lambda = &self.cx.lambdas[l.0 as usize];
                let mut kept = Vec::new();
                let substitute: Vec<Expr> = (0..caps.len())
                    .map(|i| {
                        if fixed.contains(&i) {
                            caps[i].clone()
                        } else {
                            kept.push(i);
                            Expr::Captured(u32::try_from(kept.len() - 1).expect("fits"))
                        }
                    })
                    .collect();
                let mut next = lambda.params;
                let expr = Renamer::new(&mut next, Some(&substitute)).expr(&lambda.body.expr);
                let new = Lambda {
                    params: lambda.params,
                    captures: u32::try_from(kept.len()).expect("fits"),
                    body: Body { frame: next, expr },
                };
                let id = LambdaId(u32::try_from(self.cx.lambdas.len()).expect("fits"));
                self.cx.lambdas.push(new);
                self.cx.specialised.insert(key, (id, kept.clone()));
                (id, kept)
            }
        };
        let mut caps = caps;
        let kept_caps = kept
            .iter()
            .map(|i| std::mem::replace(&mut caps[*i], Expr::Erased))
            .collect();
        Expr::Closure(id, kept_caps)
    }
}

/// `e` with each call of `g` that passes its own parameters `positions` on
/// unchanged made a call of `copy` without them.
fn redirect(e: &Expr, g: GlobalId, positions: &[usize], copy: GlobalId) -> Expr {
    let all =
        |a: &[Expr]| -> Vec<Expr> { a.iter().map(|x| redirect(x, g, positions, copy)).collect() };
    match e {
        Expr::Call(h, a)
            if *h == g
                && positions
                    .iter()
                    .all(|p| matches!(a[*p], Expr::Local(s) if s as usize == *p)) =>
        {
            let rest: Vec<Expr> = a
                .iter()
                .enumerate()
                .filter(|(k, _)| !positions.contains(k))
                .map(|(_, x)| redirect(x, g, positions, copy))
                .collect();
            Expr::Call(copy, rest)
        }
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => e.clone(),
        Expr::Call(h, a) => Expr::Call(*h, all(a)),
        Expr::Prim(op, a) => Expr::Prim(*op, all(a)),
        Expr::PartialApp(h, a) => Expr::PartialApp(*h, all(a)),
        Expr::Closure(l, a) => Expr::Closure(*l, all(a)),
        Expr::Ctor(t, c, a) => Expr::Ctor(*t, *c, all(a)),
        Expr::Apply(f, a) => Expr::Apply(Box::new(redirect(f, g, positions, copy)), all(a)),
        Expr::Let(s, v, b) => Expr::Let(
            *s,
            Box::new(redirect(v, g, positions, copy)),
            Box::new(redirect(b, g, positions, copy)),
        ),
        Expr::Match(x, k, arms) => Expr::Match(
            Box::new(redirect(x, g, positions, copy)),
            *k,
            arms.iter()
                .map(|arm| Arm {
                    ctor: arm.ctor,
                    fields: arm.fields.clone(),
                    body: redirect(&arm.body, g, positions, copy),
                })
                .collect(),
        ),
        Expr::NumSwitch(x, arms, d) => Expr::NumSwitch(
            Box::new(redirect(x, g, positions, copy)),
            arms.iter()
                .map(|(n, b)| (n.clone(), redirect(b, g, positions, copy)))
                .collect(),
            Box::new(redirect(d, g, positions, copy)),
        ),
        Expr::If(c, t, f) => Expr::If(
            Box::new(redirect(c, g, positions, copy)),
            Box::new(redirect(t, g, positions, copy)),
            Box::new(redirect(f, g, positions, copy)),
        ),
    }
}

/// A native operation, with the few rewrites that pay.
fn prim(op: PrimOp, mut args: Vec<Expr>) -> Expr {
    if op == PrimOp::Text(TextNative::TextFromList)
        && let [Expr::Prim(PrimOp::Text(TextNative::TextToList), inner)] = &mut args[..]
    {
        return inner.pop().expect("one argument");
    }
    Expr::Prim(op, args)
}
