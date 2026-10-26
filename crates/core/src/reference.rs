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
use crate::term::{Branch, DefId, Icit, QuotForm, Term};
use crate::value::{Closure, Elim, Head, Spine, Value, quot_mk_rep, quot_value};

pub fn eval(g: &Globals, env: &[Value], term: &Term) -> Result<Value> {
    let eval_all = |args: &[Rc<Term>]| -> Result<Vec<Value>> {
        args.iter().map(|a| eval(g, env, a)).collect()
    };
    Ok(match term {
        Term::Var(ix) => env[env.len() - 1 - ix].clone(),
        Term::Def(id) => {
            let def = g.def(*id);
            match seen(g, *id) {
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
        Term::Case(..) | Term::NumCase(..) => eval_tree(g, env.to_vec(), term, false)?
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
        Term::J(motive, base, proof) => match unfold_folded(g, force(g, eval(g, env, proof)?)?)? {
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
        // The one computation rule: `Quot.lift f h (Quot.mk a)` is `f a`.
        Term::Quot(form, args, _) => eval_quot(g, env, *form, args)?,
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
            Elim::J { base, .. } => match unfold_folded(g, force(g, value)?)? {
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
        Term::Quot(form, args, e) => Term::Quot(*form, args.iter().map(go).collect(), *e),
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
    if crate::value::hidden(g, id) {
        return Ok(Value::Neutral(Head::Def(id), spine.into()));
    }
    if let Some(value) = crate::float::run(g, id, &spine, force)? {
        return Ok(value);
    }
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
        && !native::folds_mul(g, id, &spine)
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(value) =
                eval_tree(g, args, body.peel_lams(def.arity), folds_on_lift(g, id))?
        {
            return Ok(value);
        }
    }
    Ok(Value::Neutral(Head::Def(id), spine.into()))
}

/// Definition `id`'s body, unless it's opaque and hidden now
/// ([`crate::value::hidden`]).
fn seen(g: &Globals, id: DefId) -> Option<&Rc<Term>> {
    g.def(id)
        .body
        .as_ref()
        .filter(|_| !crate::value::hidden(g, id))
}

/// Whether a dictionary (`Def::fold`) or a theorem stays folded when it has
/// all its arguments, except while a program runs.
fn folds(g: &Globals, id: DefId) -> bool {
    let def = g.def(id);
    (def.fold || def.theorem) && !g.erasure.program_running()
}

/// Whether a definition with all its arguments stays folded when its case
/// tree reaches a `Quot.lift` on a quotient that isn't a `Quot.mk`, except
/// while a program runs.
fn folds_on_lift(g: &Globals, id: DefId) -> bool {
    g.def(id).lift_leaf && !g.erasure.program_running()
}

/// Whether `value` is a folded definition with all its arguments (or may
/// be, folded on a `Quot.lift`), or `k * x` left folded
/// (`native::folds_mul`).
fn is_folded(g: &Globals, value: &Value) -> bool {
    matches!(value, Value::Neutral(Head::Def(id), spine)
        if (folds(g, *id) || folds_on_lift(g, *id) || native::folds_mul(g, *id, spine))
            && spine.len() == g.def(*id).arity
            && seen(g, *id).is_some())
}

/// A dictionary or theorem left folded (or a definition folded on a
/// `Quot.lift`), unfolded (repeatedly) for a `case` or `J` to take it apart,
/// or a comparison; anything else as it is.
fn unfold_folded(g: &Globals, value: Value) -> Result<Value> {
    if let Value::Neutral(Head::Def(id), spine) = &value
        && (folds(g, *id) || folds_on_lift(g, *id) || native::folds_mul(g, *id, spine))
        && spine.len() == g.def(*id).arity
        && let Some(body) = seen(g, *id).cloned()
    {
        let args: Option<Vec<Value>> = spine
            .iter()
            .map(|e| match e {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            })
            .collect();
        if let Some(args) = args
            && let Some(next) = eval_tree(g, args, body.peel_lams(g.def(*id).arity), false)?
        {
            return unfold_folded(g, force(g, next)?);
        }
    }
    Ok(value)
}

/// The number `value` is, as `k` plus what's unknown, a folded definition
/// taken apart first as `value.rs` does. Its own frame, so `eval_tree`'s
/// recursion keeps a small one.
#[inline(never)]
fn number_view(g: &Globals, value: &Value) -> Result<(num_bigint::BigUint, Option<Value>)> {
    let value = unfold_folded(g, force(g, value.clone())?)?;
    native::view_with(g, &value, force)
}

fn eval_tree(
    g: &Globals,
    mut env: Vec<Value>,
    term: &Term,
    fold_lifts: bool,
) -> Result<Option<Value>> {
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
            eval_tree(g, env, body, fold_lifts)
        }
        Term::NumCase(ix, arms, default) => {
            let (k, base) = number_view(g, &env[env.len() - 1 - ix])?;
            let body = if base.is_none() {
                match arms.iter().find(|a| *a.value == k) {
                    Some(arm) => &arm.body,
                    None => default,
                }
            } else if arms.iter().all(|a| *a.value < k) {
                // `k + x` is at least `k`.
                default
            } else if let Some(Value::Neutral(Head::Var(_, apart), spine)) = &base
                && spine.is_empty()
                && arms.iter().all(|a| {
                    *a.value < k || apart.numbers(g).binary_search(&(&*a.value - &k)).is_ok()
                })
            {
                // `x` is a variable known not to be any arm's number less `k`.
                default
            } else {
                return Ok(None);
            };
            eval_tree(g, env, body, fold_lifts)
        }
        // A `Quot.lift` leaf counts as a case on its quotient: stuck, the
        // definition stays folded (`fold_lifts`: only one marked for it,
        // `folds_on_lift`).
        Term::Quot(QuotForm::Lift, args, _)
            if fold_lifts && args.len() == QuotForm::Lift.arity() =>
        {
            lift_leaf(g, &env, args)
        }
        other => eval(g, &env, other).map(Some),
    }
}

/// A `Quot.lift` leaf of a case tree: `f a` on `Quot.mk a`, else stuck.
#[inline(never)]
fn lift_leaf(g: &Globals, env: &[Value], args: &[std::rc::Rc<Term>]) -> Result<Option<Value>> {
    Ok(lift(g, env, args)?.ok())
}

/// A quotient form applied to `args`. The one computation rule:
/// `Quot.lift f h (Quot.mk a)` is `f a`.
#[inline(never)]
fn eval_quot(
    g: &Globals,
    env: &[Value],
    form: QuotForm,
    args: &[std::rc::Rc<Term>],
) -> Result<Value> {
    let eval_all = |args: &[std::rc::Rc<Term>]| -> Result<Vec<Value>> {
        args.iter().map(|a| eval(g, env, a)).collect()
    };
    if form == QuotForm::Lift && args.len() == QuotForm::Lift.arity() {
        return match lift(g, env, args)? {
            Ok(value) => Ok(value),
            Err(q) => {
                let mut values = eval_all(&args[..5])?;
                values.push(q);
                Ok(quot_value(QuotForm::Lift, values))
            }
        };
    }
    Ok(quot_value(form, eval_all(args)?))
}

/// `Quot.lift` applied to `args`: `f a` if the quotient is `Quot.mk a`, else
/// the quotient's value. Its own frame, so `eval`'s and `eval_tree`'s
/// recursion keep small ones (io.sw's long chain of prints recurses deeply).
#[inline(never)]
fn lift(
    g: &Globals,
    env: &[Value],
    args: &[std::rc::Rc<Term>],
) -> Result<std::result::Result<Value, Value>> {
    let q = unfold_folded(g, force(g, eval(g, env, &args[5])?)?)?;
    Ok(match quot_mk_rep(&q) {
        Some(a) => Ok(apply_icit(
            g,
            eval(g, env, &args[3])?,
            a.clone(),
            Icit::Explicit,
        )?),
        None => Err(q),
    })
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
            let (mut term, rest) = match head {
                Head::Var(l, _) => (Term::Var(level - 1 - l), &spine[..]),
                Head::Def(id) => (Term::Def(id), &spine[..]),
                Head::Meta(m) => (Term::Meta(m), &spine[..]),
                Head::Quot(form) => quote_quot(g, level, form, &spine)?,
            };
            for elim in rest {
                term = match elim {
                    Elim::App(v, i) => Term::app_icit(term, q(v)?, *i),
                    Elim::J { motive, base } => {
                        Term::J(Rc::new(q(motive)?), Rc::new(q(base)?), Rc::new(term))
                    }
                };
            }
            term
        }
        Value::Call(..) => unreachable!("the reference evaluator never glues"),
        Value::Resumption(_) => {
            panic!("internal error: a handler's resumption reached the checker")
        }
    })
}

/// A quotient form's own arguments, the first eliminations of `spine`,
/// quoted, as the form applied to them; and the eliminations after them,
/// which apply its result. Its own frame, as `lift` is.
#[inline(never)]
fn quote_quot<'s>(
    g: &Globals,
    level: usize,
    form: QuotForm,
    spine: &'s [Elim],
) -> Result<(Term, &'s [Elim])> {
    let n = spine
        .iter()
        .take(form.arity())
        .take_while(|e| matches!(e, Elim::App(..)))
        .count();
    let args = spine[..n]
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => quote(g, level, v).map(Rc::new),
            Elim::J { .. } => unreachable!("counted applications"),
        })
        .collect::<Result<_>>()?;
    Ok((Term::Quot(form, args, false), &spine[n..]))
}

/// Definitional equality (the recursive version `value::conv` was derived
/// from).
pub fn conv(g: &Globals, level: usize, a: &Value, b: &Value) -> Result<bool> {
    // Folded calls: the same one applied to equal arguments is equal;
    // otherwise they're compared unfolded.
    if is_folded(g, a) || is_folded(g, b) {
        if let (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) = (a, b)
            && i1 == i2
            && s1.len() == s2.len()
            && conv_spines(g, level, s1, s2)?
        {
            return Ok(true);
        }
        let a2 = unfold_folded(g, a.clone())?;
        let b2 = unfold_folded(g, b.clone())?;
        let moved = |x: &Value, y: &Value| match (x, y) {
            (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) => {
                !(i1 == i2 && s1.ptr_eq(s2))
            }
            _ => true,
        };
        if (is_folded(g, a) && moved(a, &a2)) || (is_folded(g, b) && moved(b, &b2)) {
            return conv(g, level, &a2, &b2);
        }
    }
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
        // Two different definitions stuck on a `case`: by their case trees.
        (Value::Neutral(Head::Def(i1), _), Value::Neutral(Head::Def(i2), _))
            if i1 != i2
                && crate::value::opens_by_tree(g, a)
                && crate::value::opens_by_tree(g, b) =>
        {
            // Pairs already found equal in the outermost tree comparison are
            // equal again (SW-395): without this, a chain of helpers each
            // calling the next in two branches takes 2^n comparisons here
            // too. Looked up by the quoted pair, printed: its own key, not
            // the machine's `identical`.
            let open = OpenTrees::enter();
            let key = (
                level,
                format!("{:?}", quote(g, level, a)?),
                format!("{:?}", quote(g, level, b)?),
            );
            if open.known(&key) {
                true
            } else {
                let (t1, e1) = tree_of(g, a);
                let (t2, e2) = tree_of(g, b);
                let same = same_trees(g, level, &t1, e1, &t2, e2)?;
                if same {
                    open.record(key);
                }
                same
            }
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) => {
            (h1 == h2 && s1.len() == s2.len() && conv_spines(g, level, s1, s2)?)
                || eta(g, level, a, b)?
        }
        _ => eta(g, level, a, b)?,
    })
}

/// A pair of calls compared by their trees: the level and the two, quoted.
type CallPair = (usize, String, String);

thread_local! {
    /// How many tree comparisons are open, and the pairs of calls found
    /// equal since the outermost one started.
    static EQUAL_CALLS: std::cell::RefCell<(usize, crate::collections::HashSet<CallPair>)> =
        std::cell::RefCell::new((0, crate::collections::HashSet::default()));
}

/// One open tree comparison; the record is dropped with the outermost.
struct OpenTrees;

impl OpenTrees {
    fn enter() -> OpenTrees {
        EQUAL_CALLS.with(|m| m.borrow_mut().0 += 1);
        OpenTrees
    }

    fn known(&self, pair: &CallPair) -> bool {
        EQUAL_CALLS.with(|m| m.borrow().1.contains(pair))
    }

    fn record(&self, pair: CallPair) {
        EQUAL_CALLS.with(|m| m.borrow_mut().1.insert(pair));
    }
}

impl Drop for OpenTrees {
    fn drop(&mut self) {
        EQUAL_CALLS.with(|m| {
            let mut m = m.borrow_mut();
            m.0 -= 1;
            if m.0 == 0 {
                m.1.clear();
            }
        });
    }
}

/// A stuck call's case tree and arguments.
fn tree_of(g: &Globals, value: &Value) -> (Rc<Term>, Vec<Value>) {
    let Value::Neutral(Head::Def(id), spine) = value else {
        unreachable!()
    };
    let def = g.def(*id);
    let args = spine
        .iter()
        .map(|e| match e {
            Elim::App(v, _) => v.clone(),
            Elim::J { .. } => unreachable!(),
        })
        .collect();
    (
        Term::peel_lams_rc(def.body().expect("a body"), def.arity),
        args,
    )
}

/// Two case trees in their environments: both stuck on equal scrutinees with
/// equal branches (fields as fresh variables), or both leaves with equal
/// values. A constructor scrutinee takes its branch first.
fn same_trees(
    g: &Globals,
    level: usize,
    t1: &Rc<Term>,
    mut e1: Vec<Value>,
    t2: &Rc<Term>,
    mut e2: Vec<Value>,
) -> Result<bool> {
    // Steps a tree along constructor scrutinees; `None` if it reaches
    // anything but a stuck `Case` or a leaf.
    let settle = |t: &Rc<Term>, e: &mut Vec<Value>| -> Result<Option<(Rc<Term>, Option<Value>)>> {
        let mut t = t.clone();
        loop {
            match t.strip_loc() {
                Term::Case(ix, _, branches) => {
                    let s = force(g, e[e.len() - 1 - ix].clone())?;
                    match &s {
                        Value::Ctor(_, c, fields) => match &branches[*c].body {
                            Some(body) => {
                                e.extend(fields.iter().cloned());
                                t = body.clone();
                            }
                            None => return Ok(None),
                        },
                        Value::Neutral(..) if !is_folded(g, &s) => return Ok(Some((t, Some(s)))),
                        _ => return Ok(None),
                    }
                }
                Term::NumCase(..) => return Ok(None),
                _ => return Ok(Some((t, None))),
            }
        }
    };
    let (Some((t1, s1)), Some((t2, s2))) = (settle(t1, &mut e1)?, settle(t2, &mut e2)?) else {
        return Ok(false);
    };
    match (s1, s2) {
        (None, None) => conv(g, level, &eval(g, &e1, &t1)?, &eval(g, &e2, &t2)?),
        (Some(s1), Some(s2)) => {
            let (Term::Case(_, d1, b1), Term::Case(_, d2, b2)) = (t1.strip_loc(), t2.strip_loc())
            else {
                unreachable!()
            };
            if d1 != d2 || b1.len() != b2.len() || !conv(g, level, &s1, &s2)? {
                return Ok(false);
            }
            for (c, (x, y)) in b1.iter().zip(b2.iter()).enumerate() {
                match (&x.body, &y.body) {
                    (None, None) => {}
                    (Some(x), Some(y)) => {
                        let k = g.data(*d1).ctors[c].fields.len();
                        let fresh: Vec<Value> = (level..level + k).map(Value::var).collect();
                        let mut f1 = e1.clone();
                        let mut f2 = e2.clone();
                        f1.extend(fresh.iter().cloned());
                        f2.extend(fresh);
                        if !same_trees(g, level + k, x, f1, y, f2)? {
                            return Ok(false);
                        }
                    }
                    _ => return Ok(false),
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
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
