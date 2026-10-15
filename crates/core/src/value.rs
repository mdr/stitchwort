//! Values, evaluation, quotation and conversion (normalisation by evaluation).
//!
//! Variables in values are de Bruijn *levels*: `Var(0)` is the outermost binder.
//!
//! Reduction policy: a definition stays folded (a neutral `Def` head) until it
//! has all its parameters *and* its case tree can take a step. This keeps
//! comparison from unfolding recursive definitions forever. See `docs/core.md`.

use std::rc::Rc;

use num_bigint::BigUint;

use crate::globals::Globals;
use crate::native;
use crate::term::{Branch, DataId, DefId, Icit, Name, Sort, Term};

#[derive(Clone, Debug)]
pub enum Value {
    Sort(Sort),
    Pi(Name, Icit, Rc<Value>, Closure),
    Lam(Name, Icit, Closure),
    Data(DataId, Vec<Value>),
    Ctor(DataId, usize, Vec<Value>),
    /// A number, standing for `Succ (Succ … Zero)`. See [`native`].
    Nat(Rc<BigUint>),
    /// `k + x` for a number `k ≥ 1` and an `x` not built from numbers:
    /// `Succ` applied `k` times to `x`. See [`native::view`].
    NatAdd(Rc<BigUint>, Rc<Value>),
    Eq(Rc<Value>, Rc<Value>, Rc<Value>),
    Refl,
    /// A computation stuck on a variable or an unsolved metavariable, or a
    /// folded definition.
    Neutral(Head, Vec<Elim>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Head {
    Var(usize),
    Def(DefId),
    Meta(usize),
}

#[derive(Clone, Debug)]
pub enum Elim {
    App(Value, Icit),
    J { motive: Value, base: Value },
}

#[derive(Clone, Debug)]
pub struct Closure {
    /// Shared, not copied: values captured by nested closures would
    /// otherwise be copied again at every level.
    pub env: Rc<[Value]>,
    pub body: Rc<Term>,
}

impl Closure {
    pub fn apply(&self, g: &Globals, arg: Value) -> Value {
        let mut env = self.env.to_vec();
        env.push(arg);
        eval(g, &env, &self.body)
    }
}

impl Value {
    pub fn var(level: usize) -> Value {
        Value::Neutral(Head::Var(level), Vec::new())
    }
}

pub fn eval(g: &Globals, env: &[Value], term: &Term) -> Value {
    match term {
        Term::Var(ix) => env[env.len() - 1 - ix].clone(),
        Term::Def(id) => {
            let def = g.def(*id);
            match &def.body {
                Some(body) if def.arity == 0 => eval(g, &[], body),
                _ => Value::Neutral(Head::Def(*id), Vec::new()),
            }
        }
        Term::Meta(m) => match g.meta_solution(*m) {
            Some(value) => value,
            None => Value::Neutral(Head::Meta(*m), Vec::new()),
        },
        Term::Data(d, args) => Value::Data(*d, args.iter().map(|a| eval(g, env, a)).collect()),
        Term::Ctor(d, c, args) => {
            native::ctor(g, *d, *c, args.iter().map(|a| eval(g, env, a)).collect())
        }
        Term::Nat(n) => Value::Nat(n.clone()),
        Term::Sort(s) => Value::Sort(*s),
        Term::Pi(x, i, a, b) => Value::Pi(
            x.clone(),
            *i,
            Rc::new(eval(g, env, a)),
            Closure {
                env: env.into(),
                body: b.clone(),
            },
        ),
        Term::Lam(x, i, b) => Value::Lam(
            x.clone(),
            *i,
            Closure {
                env: env.into(),
                body: b.clone(),
            },
        ),
        Term::App(f, a, i) => apply_icit(g, eval(g, env, f), eval(g, env, a), *i),
        Term::Ann(e, _) => eval(g, env, e),
        Term::Case(..) => eval_tree(g, env.to_vec(), term)
            .expect("internal error: a case outside a definition's case tree got stuck"),
        Term::Eq(ty, a, b) => Value::Eq(
            Rc::new(eval(
                g,
                env,
                ty.as_ref()
                    .expect("internal error: evaluating an unchecked equation"),
            )),
            Rc::new(eval(g, env, a)),
            Rc::new(eval(g, env, b)),
        ),
        Term::Refl => Value::Refl,
        Term::J(motive, base, proof) => match force(g, eval(g, env, proof)) {
            Value::Refl => eval(g, env, base),
            Value::Neutral(head, mut spine) => {
                spine.push(Elim::J {
                    motive: eval(g, env, motive),
                    base: eval(g, env, base),
                });
                Value::Neutral(head, spine)
            }
            other => panic!("internal error: J applied to {other:?}"),
        },
        Term::Loc(_, t) => eval(g, env, t),
    }
}

pub fn apply(g: &Globals, f: Value, arg: Value) -> Value {
    apply_icit(g, f, arg, Icit::Explicit)
}

pub fn apply_icit(g: &Globals, f: Value, arg: Value, icit: Icit) -> Value {
    match f {
        Value::Lam(_, _, closure) => closure.apply(g, arg),
        Value::Neutral(Head::Def(id), mut spine) => {
            spine.push(Elim::App(arg, icit));
            unfold(g, id, spine)
        }
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::App(arg, icit));
            Value::Neutral(head, spine)
        }
        other => panic!("internal error: applying {other:?}"),
    }
}

fn apply_spine(g: &Globals, mut value: Value, spine: &[Elim]) -> Value {
    for elim in spine {
        value = match elim {
            Elim::App(arg, icit) => apply_icit(g, value, arg.clone(), *icit),
            Elim::J { base, .. } => match force(g, value) {
                Value::Refl => base.clone(),
                Value::Neutral(head, mut spine) => {
                    spine.push(elim.clone());
                    Value::Neutral(head, spine)
                }
                other => panic!("internal error: J applied to {other:?}"),
            },
        };
    }
    value
}

/// Replaces a solved metavariable at the head of `value` by its solution.
pub fn force(g: &Globals, value: Value) -> Value {
    match &value {
        Value::Neutral(Head::Meta(m), spine) => match g.meta_solution(*m) {
            Some(solution) => force(g, apply_spine(g, solution, spine)),
            None => value,
        },
        _ => value,
    }
}

/// Unfolds a definition applied to `spine` if it has all its arguments and its
/// case tree can make progress. Otherwise it stays folded.
fn unfold(g: &Globals, id: DefId, spine: Vec<Elim>) -> Value {
    if let Some(op) = g.builtins.native(id)
        && op.arity() == spine.len()
        && let Some(value) = native::run(g, id, op, &spine)
    {
        return value;
    }
    let def = g.def(id);
    if let Some(body) = &def.body
        && def.arity == spine.len()
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(value) = eval_tree(g, args, body.peel_lams(def.arity))
        {
            return value;
        }
    }
    Value::Neutral(Head::Def(id), spine)
}

/// Evaluates a case tree. Returns `None` if a case is stuck on a non-constructor.
fn eval_tree(g: &Globals, env: Vec<Value>, term: &Term) -> Option<Value> {
    match term.strip_loc() {
        Term::Case(ix, d, branches) => {
            let (c, fields) = match force(g, env[env.len() - 1 - ix].clone()) {
                Value::Ctor(_, c, fields) => (c, fields),
                other @ (Value::Nat(_) | Value::NatAdd(..)) if Some(*d) == g.builtins.nat => {
                    native::split_value(&other)?
                }
                _ => return None,
            };
            let Branch { body, .. } = &branches[c];
            let mut env = env.clone();
            env.extend(fields);
            eval_tree(g, env, body)
        }
        other => Some(eval(g, &env, other)),
    }
}

/// Converts a value back into a term, with `level` variables in scope.
/// Solved metavariables are replaced by their solutions.
pub fn quote(g: &Globals, level: usize, value: &Value) -> Term {
    let q = |v: &Value| quote(g, level, v);
    match force(g, value.clone()) {
        Value::Sort(s) => Term::Sort(s),
        Value::Pi(x, i, a, b) => Term::Pi(
            x.clone(),
            i,
            Rc::new(q(&a)),
            Rc::new(quote(g, level + 1, &b.apply(g, Value::var(level)))),
        ),
        Value::Lam(x, i, b) => Term::Lam(
            x.clone(),
            i,
            Rc::new(quote(g, level + 1, &b.apply(g, Value::var(level)))),
        ),
        Value::Data(d, args) => Term::Data(d, args.iter().map(q).collect()),
        Value::Ctor(d, c, args) => Term::Ctor(d, c, args.iter().map(q).collect()),
        Value::Nat(n) => Term::Nat(n),
        Value::NatAdd(k, base) => native::nat_add_term(g, &k, q(&base)),
        Value::Eq(ty, a, b) => Term::Eq(Some(Rc::new(q(&ty))), Rc::new(q(&a)), Rc::new(q(&b))),
        Value::Refl => Term::Refl,
        Value::Neutral(head, spine) => {
            let mut term = match head {
                Head::Var(l) => Term::Var(level - 1 - l),
                Head::Def(id) => Term::Def(id),
                Head::Meta(m) => Term::Meta(m),
            };
            for elim in &spine {
                term = match elim {
                    Elim::App(v, i) => Term::app_icit(term, q(v), *i),
                    Elim::J { motive, base } => {
                        Term::J(Rc::new(q(motive)), Rc::new(q(base)), Rc::new(term))
                    }
                };
            }
            term
        }
    }
}

/// Definitional equality, with `level` variables in scope. Used by the kernel,
/// which never sees metavariables (the elaborator unifies instead).
pub fn conv(g: &Globals, level: usize, a: &Value, b: &Value) -> bool {
    // Numbers, `k + x`, `Zero` and `Succ` all compare by their `k + x` forms:
    // `3` and `Succ x` are equal when `x` is `2`.
    if native::nat_like(g, a) || native::nat_like(g, b) {
        return native::compare(g, a, b, |x, y| conv(g, level, x, y), |_, _| false);
    }
    let fresh = Value::var(level);
    match (a, b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            i1 == i2
                && conv(g, level, a1, a2)
                && conv(
                    g,
                    level + 1,
                    &b1.apply(g, fresh.clone()),
                    &b2.apply(g, fresh),
                )
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => conv(
            g,
            level + 1,
            &b1.apply(g, fresh.clone()),
            &b2.apply(g, fresh),
        ),
        // Eta: `f` and `\x -> f x` are equal.
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => conv(
            g,
            level + 1,
            &b.apply(g, fresh.clone()),
            &apply_icit(g, other.clone(), fresh, *i),
        ),
        (Value::Data(d1, a1), Value::Data(d2, a2)) => d1 == d2 && all_conv(g, level, a1, a2),
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            d1 == d2 && c1 == c2 && all_conv(g, level, a1, a2)
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            conv(g, level, t1, t2) && conv(g, level, x1, x2) && conv(g, level, y1, y2)
        }
        (Value::Refl, Value::Refl) => true,
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => {
            (h1 == h2
                && s1.len() == s2.len()
                && s1.iter().zip(s2).all(|pair| match pair {
                    (Elim::App(x, _), Elim::App(y, _)) => conv(g, level, x, y),
                    (
                        Elim::J {
                            motive: m1,
                            base: b1,
                        },
                        Elim::J {
                            motive: m2,
                            base: b2,
                        },
                    ) => conv(g, level, m1, m2) && conv(g, level, b1, b2),
                    _ => false,
                }))
                || eta_definition(g, level, a, b, conv)
        }
        _ => eta_definition(g, level, a, b, conv),
    }
}

/// If `value` is a definition applied to fewer arguments than it takes (so
/// it's a function that doesn't unfold yet), the implicitness of its next
/// parameter.
pub fn underapplied(g: &Globals, value: &Value) -> Option<Icit> {
    let Value::Neutral(Head::Def(id), spine) = value else {
        return None;
    };
    let def = g.def(*id);
    let body = def.body.as_ref()?;
    if spine.len() >= def.arity {
        return None;
    }
    match body.peel_lams(spine.len()) {
        Term::Lam(_, icit, _) => Some(*icit),
        _ => None,
    }
}

/// Eta for definitions: an under-applied definition is a function, so it's
/// compared with `other` by applying both to a fresh variable (as for
/// lambdas). `SCRes` defined as `SCRes o = PlusRes … o` then equals
/// `PlusRes …`.
pub fn eta_definition(
    g: &Globals,
    level: usize,
    a: &Value,
    b: &Value,
    compare: impl Fn(&Globals, usize, &Value, &Value) -> bool,
) -> bool {
    let Some(icit) = underapplied(g, a).or_else(|| underapplied(g, b)) else {
        return false;
    };
    let fresh = Value::var(level);
    compare(
        g,
        level + 1,
        &apply_icit(g, a.clone(), fresh.clone(), icit),
        &apply_icit(g, b.clone(), fresh, icit),
    )
}

fn all_conv(g: &Globals, level: usize, xs: &[Value], ys: &[Value]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| conv(g, level, x, y))
}
