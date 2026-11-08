//! Calls plus a number, so that a function like `length` written as
//! `Succ (length rest)` doesn't keep a frame per element. `Nat` is a
//! machine number at run time, so `Succ (f x)` is `%Nat.add(f x, 1)`, not a
//! constructor, and [`crate::trmc`] doesn't make it a loop.
//!
//! A function `g` whose result, in some branch, is a sum with a call to
//! `g` itself as one of its terms (`f x + 1`, `n + f xs`, `Succ (Succ (f
//! x))`) gets a twin `g'` with one more parameter, the sum so far. Where
//! `g` returns `t + g args`, `g'` tail-calls itself with `args` and the sum
//! plus `t`; a branch that returns `v` (no call of `g` to add to) returns
//! the sum plus `v`; a branch that is a plain tail call of `g` is a turn
//! with the sum unchanged. `g` is the twin called with a sum of 0. The
//! twin keeps the invariant `g' args s = s + g args`, which is all the
//! rewrite relies on: addition on `Nat` and on `Int` is exact (both are
//! unbounded), associative and commutative, so
//! `s + (t + g args) = (s + t) + g args`, and the result is the same number.
//!
//! - **Which sums.** A `%Nat.add` or `%Int.add`, nested any way, of which
//!   exactly one term is a call of `g` with all its arguments (or a
//!   variable bound to one and read nowhere else), and no other term calls
//!   `g` or makes a closure that might. A function's sums all use the same
//!   one of the two operations. Subtraction (truncated on `Nat`) isn't
//!   associative; multiplication would need a second accumulator to mix
//!   with addition, and isn't done.
//! - **Other calls of `g`.** A call of `g` that isn't a term of such a sum,
//!   or a plain tail call, stays a call of `g`, which is the twin's
//!   wrapper: by the invariant it computes the same value.
//! - **Tail calls kept.** A branch that ends in a tail call of another
//!   function becomes `s + h args`, no longer a tail call; so `g` is only
//!   changed if no such `h` can come back to `g`, and if no branch ends in
//!   a closure call or an effect native, which might. Otherwise a loop
//!   through `h` that ran in constant space would take a frame a turn.
//! - **Not mutual recursion.** Only calls of `g` itself are turns.
//! - **Effects.** A function that performs operations returns a
//!   computation, not a number, so its sums are inside continuations and it
//!   isn't changed; its empty-row variant ([`crate::specialise`]) can be.
//!   Everything here is pure and total, so a term computed before the call
//!   rather than after it gives the same value.

use stitchwort_core::collections::HashMap;
use stitchwort_core::native::Native;

use crate::ir::{Body, Expr, Global, GlobalId, GlobalKind, Lit, PrimOp, Program, Reuse, Slot};
use crate::natives::IntNative;
use crate::opt::{MAX_NESTING, nesting, reads};
use crate::trmc::{Graph, shift, uses};

/// Turns the functions of `program` that add a number to a call of
/// themselves into loops.
pub fn apply(program: &mut Program) {
    let count = program.globals.len();
    let graph = Graph::new(program);
    let mut twins: Vec<Global> = Vec::new();
    let mut wrappers = Vec::new();
    for i in 0..count {
        let twin = GlobalId(u32::try_from(count + twins.len()).expect("globals fit"));
        let Some((params, add, body)) = build(program, &graph, i, twin) else {
            continue;
        };
        let global = &program.globals[i];
        twins.push(Global {
            name: format!("{}[sum]", global.name).into(),
            def: global.def,
            kind: GlobalKind::Function {
                params: params + 1,
                body,
            },
            reuse: Reuse::None,
        });
        // The function: its twin, with a sum of 0.
        let mut args: Vec<Expr> = (0..params).map(Expr::Local).collect();
        args.push(Expr::Lit(add.zero()));
        wrappers.push((i, params, Expr::Call(twin, args)));
    }
    for (i, params, wrapper) in wrappers {
        program.globals[i].kind = GlobalKind::Function {
            params,
            body: Body {
                frame: params,
                expr: wrapper,
            },
        };
    }
    program.globals.append(&mut twins);
}

/// The addition a function's sums use.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Add {
    Nat,
    Int,
}

impl Add {
    fn of(op: PrimOp) -> Option<Add> {
        match op {
            PrimOp::Nat(Native::Add) => Some(Add::Nat),
            PrimOp::Int(IntNative::IntAdd) => Some(Add::Int),
            _ => None,
        }
    }

    fn op(self) -> PrimOp {
        match self {
            Add::Nat => PrimOp::Nat(Native::Add),
            Add::Int => PrimOp::Int(IntNative::IntAdd),
        }
    }

    fn zero(self) -> Lit {
        match self {
            Add::Nat => Lit::Nat(0u32.into()),
            Add::Int => Lit::Int(0.into()),
        }
    }

    fn is_zero(self, e: &Expr) -> bool {
        match (self, e) {
            (Add::Nat, Expr::Lit(Lit::Nat(n))) => *n == 0u32.into(),
            (Add::Int, Expr::Lit(Lit::Int(n))) => *n == 0.into(),
            _ => false,
        }
    }
}

/// Global `i`'s parameter count, addition and twin's body (whose id is
/// `twin`), or `None` if it isn't to be changed.
fn build(program: &Program, graph: &Graph, i: usize, twin: GlobalId) -> Option<(u32, Add, Body)> {
    let GlobalKind::Function { params, body } = &program.globals[i].kind else {
        return None;
    };
    // The passes here recurse over the body.
    if nesting(&body.expr) > MAX_NESTING {
        return None;
    }
    let me = GlobalId(u32::try_from(i).expect("globals fit"));
    let mut cx = Cx {
        program,
        me,
        twin,
        params: *params,
        add: None,
        built: false,
        bad: false,
        leaf_calls: Vec::new(),
        holes: HashMap::default(),
    };
    // The sum so far is the slot after the parameters; the locals move up.
    let expr = shift(&body.expr, *params, 1);
    let sum = Expr::Local(*params);
    // The first time finds which addition the sums use, which the branches
    // that aren't sums need; the second builds the twin's body with it.
    cx.tail(&expr, &sum);
    let add = cx.add?;
    cx.built = false;
    cx.leaf_calls.clear();
    let expr = cx.tail(&expr, &sum);
    if !cx.built || cx.bad || cx.leaf_calls.iter().any(|h| graph.reaches(*h, me)) {
        return None;
    }
    Some((
        *params,
        add,
        Body {
            frame: body.frame + 1,
            expr,
        },
    ))
}

struct Cx<'p> {
    program: &'p Program,
    me: GlobalId,
    twin: GlobalId,
    params: u32,
    /// The addition the sums found so far use.
    add: Option<Add>,
    /// Whether any branch adds to a call of the function.
    built: bool,
    /// Whether the function can't be changed: a branch ends in something
    /// that may go on to call it, or two kinds of sum are mixed.
    bad: bool,
    /// The functions that branches end by calling.
    leaf_calls: Vec<GlobalId>,
    /// The variables that stand for a call of the function, with its
    /// arguments.
    holes: HashMap<Slot, Vec<Expr>>,
}

impl Cx<'_> {
    /// The arguments of the call of the function that `e` is, or stands
    /// for.
    fn call(&self, e: &Expr) -> Option<Vec<Expr>> {
        match e {
            Expr::Call(g, args) if *g == self.me && args.len() == self.params as usize => {
                Some(args.clone())
            }
            Expr::Local(s) => self.holes.get(s).cloned(),
            _ => None,
        }
    }

    /// Whether `e` may call the function, directly or through a closure it
    /// makes, or reads a variable that stands for a call of it.
    fn mentions(&self, e: &Expr) -> bool {
        uses(self.program, e).contains(&self.me) || self.holes.keys().any(|s| reads(e, *s) > 0)
    }

    /// For a sum `e` with exactly one term a call of the function: the
    /// call's arguments and the other terms.
    fn sum(&self, e: &Expr) -> Option<(Add, Vec<Expr>, Vec<Expr>)> {
        let Expr::Prim(op, _) = e else {
            return None;
        };
        let add = Add::of(*op)?;
        let mut terms = Vec::new();
        flatten(add, e, &mut terms);
        let at = terms.iter().position(|t| self.call(t).is_some())?;
        let args = self.call(terms[at]).expect("a call");
        let rest: Vec<Expr> = terms
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != at)
            .map(|(_, t)| (*t).clone())
            .collect();
        if rest.iter().any(|t| self.mentions(t)) {
            return None;
        }
        Some((add, args, rest))
    }

    fn use_add(&mut self, add: Add) {
        match self.add {
            None => self.add = Some(add),
            Some(a) if a == add => {}
            Some(_) => self.bad = true,
        }
    }

    fn turn(&self, mut args: Vec<Expr>, sum: Expr) -> Expr {
        args.push(sum);
        Expr::Call(self.twin, args)
    }

    /// `e`, in tail position, for the twin, where `sum` is the sum so far:
    /// each branch returns the sum plus its value, or is a turn.
    fn tail(&mut self, e: &Expr, sum: &Expr) -> Expr {
        match e {
            Expr::Let(s, value, body) => {
                if let Some(args) = self.call(value)
                    && !matches!(**value, Expr::Local(_))
                {
                    // The variable is the call where a sum in tail position
                    // uses it as one; read any other way, the `let` stays,
                    // and the body is done again without it standing for
                    // the call.
                    let saved = (self.add, self.built, self.bad, self.leaf_calls.len());
                    self.holes.insert(*s, args);
                    let rest = self.tail(body, sum);
                    self.holes.remove(s);
                    if reads(&rest, *s) == 0 {
                        return rest;
                    }
                    (self.add, self.built, self.bad) = (saved.0, saved.1, saved.2);
                    self.leaf_calls.truncate(saved.3);
                }
                Expr::Let(*s, value.clone(), Box::new(self.tail(body, sum)))
            }
            Expr::Match(x, kind, arms) => Expr::Match(
                x.clone(),
                *kind,
                arms.iter()
                    .map(|arm| crate::ir::Arm {
                        ctor: arm.ctor,
                        fields: arm.fields.clone(),
                        body: self.tail(&arm.body, sum),
                    })
                    .collect(),
            ),
            Expr::NumSwitch(x, arms, default) => Expr::NumSwitch(
                x.clone(),
                arms.iter()
                    .map(|(n, b)| (n.clone(), self.tail(b, sum)))
                    .collect(),
                Box::new(self.tail(default, sum)),
            ),
            Expr::If(c, a, b) => Expr::If(
                c.clone(),
                Box::new(self.tail(a, sum)),
                Box::new(self.tail(b, sum)),
            ),
            Expr::Unreachable => Expr::Unreachable,
            other => {
                if let Some(args) = self.call(other) {
                    return self.turn(args, sum.clone());
                }
                if let Some((add, args, terms)) = self.sum(other) {
                    self.use_add(add);
                    self.built = true;
                    let total = terms
                        .into_iter()
                        .fold(sum.clone(), |acc, t| Expr::Prim(add.op(), vec![acc, t]));
                    return self.turn(args, total);
                }
                match other {
                    Expr::Call(g, _) => self.leaf_calls.push(*g),
                    Expr::Apply(..) | Expr::Prim(PrimOp::Effect(_), _) => self.bad = true,
                    _ => {}
                }
                let add = self.add.unwrap_or(Add::Nat);
                if add.is_zero(other) {
                    return sum.clone();
                }
                Expr::Prim(add.op(), vec![sum.clone(), other.clone()])
            }
        }
    }
}

/// The terms of the sum `e`, in order: its operands, and theirs where they
/// are sums by the same addition.
fn flatten<'e>(add: Add, e: &'e Expr, terms: &mut Vec<&'e Expr>) {
    match e {
        Expr::Prim(op, args) if Add::of(*op) == Some(add) && args.len() == 2 => {
            flatten(add, &args[0], terms);
            flatten(add, &args[1], terms);
        }
        other => terms.push(other),
    }
}
