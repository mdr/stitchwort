//! A reference evaluator, for testing the real one
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! This is the straightforward recursive evaluator the abstract machine in
//! `value.rs` was derived from. It's kept so the two can be compared on the
//! same programs: they have different control flow, so a mistake in one
//! (frames applied in the wrong order, a lost argument, a wrong environment)
//! shows up as a disagreement.
//!
//! It must stay independent: it shares the data types (`Term`, `Value`,
//! `Globals`) and the native number functions, which it calls with its own
//! `force`, but never calls anything in `value.rs` that evaluates. It isn't
//! optimised, and only changes when the language's evaluation rules do. It
//! recurses on the Rust stack, so it's only for small inputs, and it doesn't
//! count resources.
//!
//! Only compiled for tests (the `reference` feature).

use std::rc::Rc;

use crate::budget::Result;
use crate::globals::Globals;
use crate::native;
use crate::term::{Branch, DefId, Icit, Term};
use crate::value::{Closure, Elim, Head, Spine, Value};

pub fn eval(g: &Globals, env: &[Value], term: &Term) -> Result<Value> {
    let eval_all = |args: &[Rc<Term>]| -> Result<Vec<Value>> {
        args.iter().map(|a| eval(g, env, a)).collect()
    };
    Ok(match term {
        Term::Var(ix) => env[env.len() - 1 - ix].clone(),
        Term::Def(id) => {
            let def = g.def(*id);
            match &def.body {
                Some(body) if def.arity == 0 && !folds(g, *id) => eval(g, &[], body)?,
                _ => Value::Neutral(Head::Def(*id), Spine::new()),
            }
        }
        Term::Meta(m) => match g.meta_solution(*m) {
            Some(value) => value,
            None => Value::Neutral(Head::Meta(*m), Spine::new()),
        },
        Term::Data(d, args) => Value::Data(*d, eval_all(args)?),
        Term::Ctor(d, c, args) => native::ctor(g, *d, *c, eval_all(args)?),
        Term::Nat(n) => Value::Nat(n.clone()),
        // A compact list is its expansion, built here in full: this evaluator
        // doesn't share the machine's rules for ranges.
        Term::Chars(chars) => expand(g, chars.as_slice()),
        Term::Sort(s) => Value::Sort(*s),
        Term::Pi(x, i, a, b) => Value::Pi(
            x.clone(),
            *i,
            Rc::new(eval(g, env, a)?),
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
        Term::App(f, a, i) => {
            let f = eval(g, env, f)?;
            apply_icit(g, f, eval(g, env, a)?, *i)?
        }
        Term::Ann(e, _) => eval(g, env, e)?,
        Term::Let(_, _, value, body, _) => {
            let mut env = env.to_vec();
            env.push(eval(g, &env, value)?);
            eval(g, &env, body)?
        }
        Term::Case(..) | Term::NumCase(..) => eval_tree(g, env.to_vec(), term)?
            .expect("internal error: a case outside a definition's case tree got stuck"),
        Term::Eq(ty, a, b) => Value::Eq(
            Rc::new(eval(
                g,
                env,
                ty.as_ref()
                    .expect("internal error: evaluating an unchecked equation"),
            )?),
            Rc::new(eval(g, env, a)?),
            Rc::new(eval(g, env, b)?),
        ),
        Term::Refl => Value::Refl,
        Term::J(motive, base, proof) => match force(g, eval(g, env, proof)?)? {
            Value::Refl => eval(g, env, base)?,
            Value::Neutral(head, mut spine) => {
                spine.push(Elim::J {
                    motive: Box::new(eval(g, env, motive)?),
                    base: Box::new(eval(g, env, base)?),
                });
                Value::Neutral(head, spine)
            }
            _ => panic!("internal error: J applied to a non-proof"),
        },
        Term::Loc(_, t) => eval(g, env, t)?,
    })
}

pub fn apply_closure(g: &Globals, closure: &Closure, arg: Value) -> Result<Value> {
    let mut env = closure.env.to_vec();
    env.push(arg);
    eval(g, &env, &closure.body)
}

pub fn apply_icit(g: &Globals, f: Value, arg: Value, icit: Icit) -> Result<Value> {
    match f {
        Value::Lam(_, _, closure) => apply_closure(g, &closure, arg),
        Value::Neutral(Head::Def(id), mut spine) => {
            spine.push(Elim::App(arg, icit));
            unfold(g, id, spine.into_vec())
        }
        Value::Neutral(head, mut spine) => {
            spine.push(Elim::App(arg, icit));
            Ok(Value::Neutral(head, spine))
        }
        _ => panic!("internal error: applying a non-function"),
    }
}

fn apply_spine(g: &Globals, mut value: Value, spine: &[Elim]) -> Result<Value> {
    for elim in spine {
        value = match elim {
            Elim::App(arg, icit) => apply_icit(g, value, arg.clone(), *icit)?,
            Elim::J { base, .. } => match force(g, value)? {
                Value::Refl => (**base).clone(),
                Value::Neutral(head, mut spine) => {
                    spine.push(elim.clone());
                    Value::Neutral(head, spine)
                }
                _ => panic!("internal error: J applied to a non-proof"),
            },
        };
    }
    Ok(value)
}

/// `Cons (MkChar c rfl) … Nil`, for the characters `chars`: what a compact
/// list means (docs/proposals/compact-text.md, "Expansion"), written out
/// from the prelude's constructors, independently of [`crate::chars`].
fn expand(g: &Globals, chars: &[char]) -> Value {
    let list = g
        .registry
        .data(crate::registry::Builtin::List)
        .expect("a compact list needs `List`");
    let char = g
        .registry
        .data(crate::registry::Builtin::Char)
        .expect("a compact list needs `Char`");
    let mut value = Value::Ctor(list, 0, Vec::new().into());
    for c in chars.iter().rev() {
        let code = Value::Nat(Rc::new(u32::from(*c).into()));
        let head = Value::Ctor(char, 0, vec![code, Value::Refl].into());
        value = Value::Ctor(list, 1, vec![head, value].into());
    }
    value
}

/// `term` with every compact list replaced by its expansion, as constructor
/// terms: for comparing the machine's quotation, which keeps compact lists,
/// with this evaluator's, which never makes them.
pub fn expand_term(g: &Globals, term: &Term) -> Term {
    let go = |t: &Rc<Term>| Rc::new(expand_term(g, t));
    match term {
        Term::Chars(chars) => {
            let list = g
                .registry
                .data(crate::registry::Builtin::List)
                .expect("a compact list needs `List`");
            let char = g
                .registry
                .data(crate::registry::Builtin::Char)
                .expect("a compact list needs `Char`");
            let mut out = Term::Ctor(list, 0, Vec::new());
            for c in chars.as_slice().iter().rev() {
                let code = Term::Nat(Rc::new(u32::from(*c).into()));
                let head = Term::ctor(char, 0, vec![code, Term::Refl]);
                out = Term::ctor(list, 1, vec![head, out]);
            }
            out
        }
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
            term.clone()
        }
        Term::Data(d, args) => Term::Data(*d, args.iter().map(go).collect()),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, args.iter().map(go).collect()),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a), go(b)),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b)),
        Term::App(f, a, i) => Term::App(go(f), go(a), *i),
        Term::Ann(e, t) => Term::Ann(go(e), go(t)),
        Term::Let(x, a, v, b, e) => Term::Let(x.clone(), go(a), go(v), go(b), *e),
        Term::Case(ix, d, branches) => Term::Case(
            *ix,
            *d,
            branches
                .iter()
                .map(|b| Branch {
                    names: b.names.clone(),
                    body: b.body.as_ref().map(go),
                })
                .collect(),
        ),
        Term::NumCase(ix, arms, default) => Term::NumCase(
            *ix,
            arms.iter()
                .map(|a| crate::term::NumArm {
                    value: a.value.clone(),
                    body: go(&a.body),
                })
                .collect(),
            go(default),
        ),
        Term::Eq(ty, a, b) => Term::Eq(ty.as_ref().map(go), go(a), go(b)),
        Term::J(m, b, p) => Term::J(go(m), go(b), go(p)),
        Term::Loc(span, t) => Term::Loc(*span, go(t)),
    }
}

/// Replaces a solved metavariable at the head of `value` by its solution, and
/// expands a compact list (which only a metavariable's solution, made by the
/// machine, can hold).
pub fn force(g: &Globals, value: Value) -> Result<Value> {
    if let Value::Chars(chars) = &value {
        return Ok(expand(g, chars.as_slice()));
    }
    match &value {
        Value::Neutral(Head::Meta(m), spine) => match g.meta_solution(*m) {
            Some(solution) => {
                let applied = apply_spine(g, solution, spine)?;
                force(g, applied)
            }
            None => Ok(value),
        },
        _ => Ok(value),
    }
}

fn unfold(g: &Globals, id: DefId, spine: Vec<Elim>) -> Result<Value> {
    if let Some(op) = g.builtins.native(id)
        && op.arity() == spine.len()
    {
        match native::run(g, id, op, &spine, force)? {
            Some(native::Outcome::Done(value)) => return Ok(value),
            Some(native::Outcome::Again(spine)) => return unfold(g, id, spine),
            None => {}
        }
    }
    let def = g.def(id);
    if let Some(body) = &def.body
        && def.arity == spine.len()
        && !folds(g, id)
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(value) = eval_tree(g, args, body.peel_lams(def.arity))?
        {
            return Ok(value);
        }
    }
    Ok(Value::Neutral(Head::Def(id), spine.into()))
}

/// Whether a dictionary stays folded when it has all its arguments
/// (`Def::fold`), except while a program runs.
fn folds(g: &Globals, id: DefId) -> bool {
    g.def(id).fold && !g.erasure.active()
}

/// A dictionary left folded, unfolded (repeatedly) for a `case` to take it
/// apart; anything else as it is.
fn unfold_folded(g: &Globals, value: Value) -> Result<Value> {
    if let Value::Neutral(Head::Def(id), spine) = &value
        && folds(g, *id)
        && spine.len() == g.def(*id).arity
        && let Some(body) = g.def(*id).body.clone()
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(next) = eval_tree(g, args, body.peel_lams(g.def(*id).arity))?
        {
            return unfold_folded(g, force(g, next)?);
        }
    }
    Ok(value)
}

fn eval_tree(g: &Globals, mut env: Vec<Value>, term: &Term) -> Result<Option<Value>> {
    match term.strip_loc() {
        Term::Case(ix, d, branches) => {
            let (c, fields) = match unfold_folded(g, force(g, env[env.len() - 1 - ix].clone())?)? {
                Value::Ctor(_, c, fields) => (c, fields.to_vec()),
                other @ (Value::Nat(_) | Value::NatAdd(..)) if Some(*d) == g.builtins.nat => {
                    match native::split_value(&other) {
                        Some(split) => split,
                        None => return Ok(None),
                    }
                }
                _ => return Ok(None),
            };
            let Branch { body, .. } = &branches[c];
            let Some(body) = body else {
                return Ok(None);
            };
            env.extend(fields);
            eval_tree(g, env, body)
        }
        Term::NumCase(ix, arms, default) => {
            // A folded definition is taken apart here too, as `value.rs` does.
            let scrutinee = unfold_folded(g, force(g, env[env.len() - 1 - ix].clone())?)?;
            let (k, base) = native::view_with(g, &scrutinee, force)?;
            let body = if base.is_none() {
                match arms.iter().find(|a| *a.value == k) {
                    Some(arm) => &arm.body,
                    None => default,
                }
            } else if arms.iter().all(|a| *a.value < k) {
                // `k + x` is at least `k`.
                default
            } else {
                return Ok(None);
            };
            eval_tree(g, env, body)
        }
        other => eval(g, &env, other).map(Some),
    }
}

/// Converts a value back into a term, with `level` variables in scope.
pub fn quote(g: &Globals, level: usize, value: &Value) -> Result<Term> {
    let q = |v: &Value| quote(g, level, v);
    Ok(match force(g, value.clone())? {
        Value::Sort(s) => Term::Sort(s),
        Value::Pi(x, i, a, b) => Term::Pi(
            x.clone(),
            i,
            Rc::new(q(&a)?),
            Rc::new(quote(
                g,
                level + 1,
                &apply_closure(g, &b, Value::var(level))?,
            )?),
        ),
        Value::Lam(x, i, b) => Term::Lam(
            x.clone(),
            i,
            Rc::new(quote(
                g,
                level + 1,
                &apply_closure(g, &b, Value::var(level))?,
            )?),
        ),
        Value::Data(d, args) => Term::Data(
            d,
            args.iter()
                .map(|a| q(a).map(Rc::new))
                .collect::<Result<_>>()?,
        ),
        Value::Ctor(d, c, args) => Term::Ctor(
            d,
            c,
            args.iter()
                .map(|a| q(a).map(Rc::new))
                .collect::<Result<_>>()?,
        ),
        Value::Nat(n) => Term::Nat(n),
        Value::Chars(_) => unreachable!("forcing expands compact lists"),
        Value::NatAdd(k, base) => native::nat_add_term(g, &k, q(&base)?),
        Value::Eq(ty, a, b) => Term::Eq(Some(Rc::new(q(&ty)?)), Rc::new(q(&a)?), Rc::new(q(&b)?)),
        Value::Refl => Term::Refl,
        Value::Neutral(head, spine) => {
            let mut term = match head {
                Head::Var(l) => Term::Var(level - 1 - l),
                Head::Def(id) => Term::Def(id),
                Head::Meta(m) => Term::Meta(m),
            };
            for elim in &spine {
                term = match elim {
                    Elim::App(v, i) => Term::app_icit(term, q(v)?, *i),
                    Elim::J { motive, base } => {
                        Term::J(Rc::new(q(motive)?), Rc::new(q(base)?), Rc::new(term))
                    }
                };
            }
            term
        }
    })
}

/// Definitional equality (the recursive version `value::conv` was derived
/// from).
pub fn conv(g: &Globals, level: usize, a: &Value, b: &Value) -> Result<bool> {
    if matches!(a, Value::Chars(_)) || matches!(b, Value::Chars(_)) {
        return conv(g, level, &force(g, a.clone())?, &force(g, b.clone())?);
    }
    if native::nat_like(g, a) || native::nat_like(g, b) {
        return native::compare_with(
            g,
            a,
            b,
            |x, y| conv(g, level, x, y),
            |_, _| Ok(false),
            force,
        );
    }
    let fresh = Value::var(level);
    let apply = |c: &Closure, v: Value| apply_closure(g, c, v);
    Ok(match (a, b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            i1 == i2
                && conv(g, level, a1, a2)?
                && conv(g, level + 1, &apply(b1, fresh.clone())?, &apply(b2, fresh)?)?
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => {
            conv(g, level + 1, &apply(b1, fresh.clone())?, &apply(b2, fresh)?)?
        }
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => conv(
            g,
            level + 1,
            &apply(b, fresh.clone())?,
            &apply_icit(g, other.clone(), fresh, *i)?,
        )?,
        (Value::Data(d1, a1), Value::Data(d2, a2)) => d1 == d2 && all_conv(g, level, a1, a2)?,
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            d1 == d2 && c1 == c2 && all_conv(g, level, a1, a2)?
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            conv(g, level, t1, t2)? && conv(g, level, x1, x2)? && conv(g, level, y1, y2)?
        }
        (Value::Refl, Value::Refl) => true,
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => {
            (h1 == h2 && s1.len() == s2.len() && conv_spines(g, level, s1, s2)?)
                || eta(g, level, a, b)?
        }
        _ => eta(g, level, a, b)?,
    })
}

fn all_conv(g: &Globals, level: usize, xs: &[Value], ys: &[Value]) -> Result<bool> {
    if xs.len() != ys.len() {
        return Ok(false);
    }
    for (x, y) in xs.iter().zip(ys) {
        if !conv(g, level, x, y)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn conv_spines(g: &Globals, level: usize, s1: &[Elim], s2: &[Elim]) -> Result<bool> {
    for pair in s1.iter().zip(s2) {
        let same = match pair {
            (Elim::App(x, _), Elim::App(y, _)) => conv(g, level, x, y)?,
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                },
            ) => conv(g, level, m1, m2)? && conv(g, level, b1, b2)?,
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Eta for partially applied definitions: both sides applied to a fresh
/// variable.
fn eta(g: &Globals, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let underapplied = |v| crate::value::underapplied(g, v);
    let Some(icit) = underapplied(a).or_else(|| underapplied(b)) else {
        return Ok(false);
    };
    let fresh = Value::var(level);
    conv(
        g,
        level + 1,
        &apply_icit(g, a.clone(), fresh.clone(), icit)?,
        &apply_icit(g, b.clone(), fresh, icit)?,
    )
}
