//! Pattern unification for metavariables, and zonking (substituting solutions
//! back into terms). Follows András Kovács' elaboration-zoo.

use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::budget::{ResourceError, Result};
use stitchwort_core::native;
use stitchwort_core::value::{
    Closure, Elim, Head, apply_icit, eval, expand_step, force, is_folded, quote, same_closure,
    underapplied, unfold_folded,
};
use stitchwort_core::{Globals, Term, Value};

/// Makes `a` and `b` equal by solving metavariables, with `level` variables in
/// scope. `Ok(false)` if they can't be made equal; an error if it ran out of
/// resources before finding out. A `false` may be followed by trying another
/// way; an error never is.
///
/// The pairs still to unify are kept on a work list, depth first and left to
/// right as a recursive version would take them, so metavariables are solved
/// in the same order; a function type's codomain is only evaluated once its
/// domain has been unified, so it sees the solutions.
pub fn unify(g: &Globals, level: usize, a: &Value, b: &Value) -> Result<bool> {
    let mut work = vec![Task::Values(level, a.clone(), b.clone())];
    while let Some(task) = work.pop() {
        g.budget.step()?;
        let same = match task {
            Task::Values(level, a, b) => unify_step(g, level, &a, &b, &mut work)?,
            // Identical functions unify without solving anything (`same_closure`).
            Task::Codomains(_, b1, b2) if same_closure(&b1, &b2) => true,
            Task::Codomains(level, b1, b2) => {
                let fresh = Value::var(level);
                work.push(Task::Values(
                    level + 1,
                    b1.apply(g, fresh.clone())?,
                    b2.apply(g, fresh)?,
                ));
                true
            }
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Unification still to do.
enum Task {
    Values(usize, Value, Value),
    Codomains(usize, Closure, Closure),
}

/// Unifies the outermost layer of `a` and `b`: `false` if they can't be made
/// equal there; otherwise pushes the pairs of parts still to unify.
fn unify_step(
    g: &Globals,
    level: usize,
    a: &Value,
    b: &Value,
    work: &mut Vec<Task>,
) -> Result<bool> {
    let a = force(g, a.clone())?;
    let b = force(g, b.clone())?;
    let is_meta = |v: &Value| matches!(v, Value::Neutral(Head::Meta(_), _));
    // Numbers compare by their `k + x` forms (see `conv`): `3` and `Succ ?x`
    // unify by solving `?x` with `2`.
    if !is_meta(&a) && !is_meta(&b) && (native::nat_like(g, &a) || native::nat_like(g, &b)) {
        return native::compare(
            g,
            &a,
            &b,
            |x, y| {
                work.push(Task::Values(level, x.clone(), y.clone()));
                Ok(true)
            },
            |x, v| Ok(is_meta(x) && unify(g, level, x, v)?),
        );
    }
    // Dictionaries left folded by name (`Def::fold`), as in `conv`: the same
    // one's arguments first (what that solves is kept only if they all
    // unify), otherwise unfolded. A metavariable against one is solved with
    // it, by name, below.
    if !is_meta(&a) && !is_meta(&b) && (is_folded(g, &a) || is_folded(g, &b)) {
        if let (Value::Neutral(Head::Def(i1), s1), Value::Neutral(Head::Def(i2), s2)) = (&a, &b)
            && i1 == i2
            && let Some(pairs) = spine_pairs(level, s1, s2)
        {
            let trail = g.meta_trail.borrow().len();
            let mut same = true;
            for pair in pairs {
                let Task::Values(l, x, y) = pair else {
                    unreachable!()
                };
                if !unify(g, l, &x, &y)? {
                    same = false;
                    break;
                }
            }
            if same {
                return Ok(true);
            }
            undo_since(g, trail);
        }
        let a2 = unfold_folded(g, &a)?;
        let b2 = unfold_folded(g, &b)?;
        if a2.is_some() || b2.is_some() {
            work.push(Task::Values(level, a2.unwrap_or(a), b2.unwrap_or(b)));
            return Ok(true);
        }
    }
    let fresh = Value::var(level);
    // Parts are pushed last-first, so they're unified first-first.
    let push_all = |work: &mut Vec<Task>, xs: &[Value], ys: &[Value]| {
        for (x, y) in xs.iter().zip(ys).rev() {
            work.push(Task::Values(level, x.clone(), y.clone()));
        }
    };
    Ok(match (&a, &b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            if i1 != i2 {
                return Ok(false);
            }
            work.push(Task::Codomains(level, b1.clone(), b2.clone()));
            work.push(Task::Values(level, (**a1).clone(), (**a2).clone()));
            true
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) if same_closure(b1, b2) => true,
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => {
            work.push(Task::Values(
                level + 1,
                b1.apply(g, fresh.clone())?,
                b2.apply(g, fresh)?,
            ));
            true
        }
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => {
            work.push(Task::Values(
                level + 1,
                b.apply(g, fresh.clone())?,
                apply_icit(g, other.clone(), fresh, *i)?,
            ));
            true
        }
        (Value::Data(d1, a1), Value::Data(d2, a2)) => {
            if d1 != d2 || a1.len() != a2.len() {
                return Ok(false);
            }
            push_all(work, a1, a2);
            true
        }
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            if d1 != d2 || c1 != c2 || a1.len() != a2.len() {
                return Ok(false);
            }
            push_all(work, a1, a2);
            true
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            push_all(
                work,
                &[(**t1).clone(), (**x1).clone(), (**y1).clone()],
                &[(**t2).clone(), (**x2).clone(), (**y2).clone()],
            );
            true
        }
        (Value::Refl, Value::Refl) => true,
        // Compact lists, as in `conv`: two ranges by their characters.
        (Value::Chars(x), Value::Chars(y)) => x.as_slice() == y.as_slice(),
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2)) if m1 == m2 => {
            match spine_pairs(level, s1, s2) {
                Some(pairs) => {
                    work.extend(pairs.into_iter().rev());
                    true
                }
                None => false,
            }
        }
        // Solving a metavariable is a leaf: it builds a solution from the
        // other side, or tries matching last arguments.
        // A frozen metavariable is rigid: against a metavariable that isn't,
        // that one is solved; against anything else, they differ.
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2))
            if g.meta_frozen(*m1) != g.meta_frozen(*m2) =>
        {
            let (m, spine, other) = if g.meta_frozen(*m1) {
                (*m2, s2, &a)
            } else {
                (*m1, s1, &b)
            };
            solve(g, level, m, spine, other)? || first_order(g, level, m, spine, other)?
        }
        (Value::Neutral(Head::Meta(m), _), _) | (_, Value::Neutral(Head::Meta(m), _))
            if g.meta_frozen(*m) =>
        {
            false
        }
        (Value::Neutral(Head::Meta(m), spine), other)
        | (other, Value::Neutral(Head::Meta(m), spine)) => {
            solve(g, level, *m, spine, other)? || first_order(g, level, *m, spine, other)?
        }
        // A range against anything else but a metavariable (which is solved
        // with the range itself, above): its first cell, as a constructor.
        // So `Cons ?c ?tail ~ "ab"` solves `?c` with `MkChar 97 rfl` and
        // `?tail` with the range `"b"`.
        (Value::Chars(_), _) => {
            work.push(Task::Values(level, expand_step(g, a.clone()), b.clone()));
            true
        }
        (_, Value::Chars(_)) => {
            work.push(Task::Values(level, a.clone(), expand_step(g, b.clone())));
            true
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) if h1 == h2 => {
            if underapplied(g, &a).is_none() && underapplied(g, &b).is_none() {
                // Eta for definitions doesn't apply, so the spines must match.
                match spine_pairs(level, s1, s2) {
                    Some(pairs) => {
                        work.extend(pairs.into_iter().rev());
                        true
                    }
                    None => false,
                }
            } else {
                // A function: the spines, or else eta. The one place this
                // recurses, once per level of nested partially applied
                // definitions.
                let spines = match spine_pairs(level, s1, s2) {
                    Some(pairs) => {
                        let mut same = true;
                        for pair in pairs {
                            let Task::Values(l, x, y) = pair else {
                                unreachable!()
                            };
                            if !unify(g, l, &x, &y)? {
                                same = false;
                                break;
                            }
                        }
                        same
                    }
                    None => false,
                };
                spines || push_eta(g, level, &a, &b, work)?
            }
        }
        _ => push_eta(g, level, &a, &b, work)?,
    })
}

/// Undoes the metavariable solutions made since the trail was `len` long.
fn undo_since(g: &Globals, len: usize) {
    let mut metas = g.metas.borrow_mut();
    let mut trail = g.meta_trail.borrow_mut();
    while trail.len() > len {
        let (m, old) = trail.pop().expect("longer");
        if let Some(meta) = metas.get_mut(m) {
            meta.solution = old;
        }
    }
}

/// The pairs of values in two spines, or `None` if they differ in length or
/// their eliminations don't match.
fn spine_pairs(level: usize, s1: &[Elim], s2: &[Elim]) -> Option<Vec<Task>> {
    if s1.len() != s2.len() {
        return None;
    }
    let mut pairs = Vec::new();
    for pair in s1.iter().zip(s2) {
        match pair {
            (Elim::App(x, _), Elim::App(y, _)) => {
                pairs.push(Task::Values(level, x.clone(), y.clone()));
            }
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                },
            ) => {
                pairs.push(Task::Values(level, (**m1).clone(), (**m2).clone()));
                pairs.push(Task::Values(level, (**b1).clone(), (**b2).clone()));
            }
            _ => return None,
        }
    }
    Some(pairs)
}

/// Eta for definitions: pushes both sides applied to a fresh variable, or
/// returns `false` if neither is a partially applied definition.
fn push_eta(g: &Globals, level: usize, a: &Value, b: &Value, work: &mut Vec<Task>) -> Result<bool> {
    let Some(icit) = underapplied(g, a).or_else(|| underapplied(g, b)) else {
        return Ok(false);
    };
    let fresh = Value::var(level);
    work.push(Task::Values(
        level + 1,
        apply_icit(g, a.clone(), fresh.clone(), icit)?,
        apply_icit(g, b.clone(), fresh, icit)?,
    ));
    Ok(true)
}

/// When `?m … x = f … y` isn't a pattern (`x` isn't a variable), tries
/// matching the last arguments and then the rest: `?m … = f …` and `x = y`.
/// This finds *a* solution, not necessarily the most general one, which is
/// fine because the kernel re-checks the result.
fn first_order(g: &Globals, level: usize, m: usize, spine: &[Elim], other: &Value) -> Result<bool> {
    let Value::Neutral(head, other_spine) = other else {
        return Ok(false);
    };
    let (Some((Elim::App(x, i1), rest1)), Some((Elim::App(y, i2), rest2))) =
        (spine.split_last(), other_spine.split_last())
    else {
        return Ok(false);
    };
    Ok(i1 == i2
        && unify(g, level, x, y)?
        && unify(
            g,
            level,
            &Value::Neutral(Head::Meta(m), rest1.to_vec().into()),
            &Value::Neutral(*head, rest2.to_vec().into()),
        )?)
}

/// Why a solution couldn't be built: there isn't one of the right shape, or
/// it ran out of resources finding out.
enum Fail {
    No,
    Out(ResourceError),
}

impl From<ResourceError> for Fail {
    fn from(e: ResourceError) -> Fail {
        Fail::Out(e)
    }
}

/// `Ok(Some(x))`, `Ok(None)` for no, or the resource error.
fn settle<T>(r: std::result::Result<T, Fail>) -> Result<Option<T>> {
    match r {
        Ok(x) => Ok(Some(x)),
        Err(Fail::No) => Ok(None),
        Err(Fail::Out(e)) => Err(e),
    }
}

/// Solves `?m spine = rhs`, where the spine must be distinct variables (a
/// "pattern"). The solution is `x1 … xn => rhs`, with the spine's variables
/// renamed to the lambda's parameters.
fn solve(g: &Globals, level: usize, m: usize, spine: &[Elim], rhs: &Value) -> Result<bool> {
    let mut renaming = HashMap::new();
    let mut repeated = Vec::new();
    let mut icits = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(arg, icit) => match force(g, arg.clone())? {
                Value::Neutral(Head::Var(l), s) if s.is_empty() => {
                    if renaming.insert(l, icits.len()).is_some() {
                        repeated.push(l);
                    }
                    icits.push(*icit);
                }
                _ => return Ok(false),
            },
            Elim::J { .. } => return Ok(false),
        }
    }
    // A variable given twice (`?m x t x`: a proof's unknown, applied to every
    // variable in scope, inside a lambda applied to a variable already in
    // scope) is a solution only if the other side doesn't mention it: with
    // `?m x x = x` there are two solutions (`a b => a` and `a b => b`), so
    // neither is chosen, but with `?m x x = p`, `a b => p` is the one.
    for l in repeated {
        renaming.remove(&l);
    }
    let Some(mut solution) = settle(rename(g, m, &renaming, icits.len(), level, rhs))? else {
        return Ok(false);
    };
    for icit in icits.into_iter().rev() {
        solution = Term::Lam("x".into(), icit, Rc::new(solution));
    }
    let value = eval(g, &[], &solution)?;
    g.solve_meta(m, value);
    Ok(true)
}

type Renamed<T> = std::result::Result<T, Fail>;

/// Quotes `value` (in a context of `cod` variables) into a term in a context of
/// `dom` variables, following `renaming`. Fails if `value` mentions `m` itself
/// (no circular solutions) or a variable the renaming doesn't cover.
fn rename(
    g: &Globals,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    value: &Value,
) -> Renamed<Term> {
    g.budget.step()?;
    let go = |v: &Value| rename(g, m, renaming, dom, cod, v);
    let under = |closure: &Closure| -> Renamed<Term> {
        let mut renaming = renaming.clone();
        renaming.insert(cod, dom);
        let body = closure.apply(g, Value::var(cod))?;
        rename(g, m, &renaming, dom + 1, cod + 1, &body)
    };
    Ok(match force(g, value.clone())? {
        Value::Sort(s) => Term::Sort(s),
        Value::Refl => Term::Refl,
        Value::Pi(x, i, a, b) => Term::Pi(x, i, Rc::new(go(&a)?), Rc::new(under(&b)?)),
        Value::Lam(x, i, b) => Term::Lam(x, i, Rc::new(under(&b)?)),
        Value::Data(d, args) => Term::data(d, args.iter().map(go).collect::<Renamed<_>>()?),
        Value::Ctor(d, c, args) => Term::ctor(d, c, args.iter().map(go).collect::<Renamed<_>>()?),
        Value::Nat(n) => Term::Nat(n),
        // Closed: nothing to rename, and no metavariable to occur.
        Value::Chars(_) => quote(g, cod, value)?,
        Value::NatAdd(k, base) => native::nat_add_term(g, &k, go(&base)?),
        Value::Eq(t, a, b) => Term::Eq(Some(Rc::new(go(&t)?)), Rc::new(go(&a)?), Rc::new(go(&b)?)),
        Value::Neutral(Head::Meta(m2), spine) if m2 != m => {
            if let Some((m3, kept)) = prune(g, m2, &spine, renaming)? {
                let mut term = Term::Meta(m3);
                for elim in kept {
                    let Elim::App(v, i) = elim else {
                        unreachable!("pruned spines only contain applications")
                    };
                    term = Term::app_icit(term, go(&v)?, i);
                }
                return Ok(term);
            }
            rename_spine(g, m, renaming, dom, cod, Term::Meta(m2), &spine)?
        }
        Value::Neutral(head, spine) => {
            let head = match head {
                Head::Meta(_) => return Err(Fail::No),
                Head::Def(id) => Term::Def(id),
                Head::Var(l) => {
                    let new = *renaming.get(&l).ok_or(Fail::No)?;
                    Term::Var(dom - 1 - new)
                }
            };
            rename_spine(g, m, renaming, dom, cod, head, &spine)?
        }
    })
}

fn rename_spine(
    g: &Globals,
    m: usize,
    renaming: &HashMap<usize, usize>,
    dom: usize,
    cod: usize,
    head: Term,
    spine: &[Elim],
) -> Renamed<Term> {
    let go = |v: &Value| rename(g, m, renaming, dom, cod, v);
    let mut term = head;
    for elim in spine {
        term = match elim {
            Elim::App(v, i) => Term::app_icit(term, go(v)?, *i),
            Elim::J { motive, base } => {
                Term::J(Rc::new(go(motive)?), Rc::new(go(base)?), Rc::new(term))
            }
        };
    }
    Ok(term)
}

/// Pruning: `?m2 spine` appears in a solution, but some of its arguments are
/// variables the solution can't mention. If the spine is distinct variables,
/// `?m2` can't depend on those positions in any solution, so solve it as a new
/// metavariable applied to only the remaining arguments. Returns the new
/// metavariable and the arguments it keeps.
fn prune(
    g: &Globals,
    m2: usize,
    spine: &[Elim],
    renaming: &HashMap<usize, usize>,
) -> Result<Option<(usize, Vec<Elim>)>> {
    if g.meta_frozen(m2) {
        return Ok(None); // pruning would solve it
    }
    let mut levels = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(v, _) => match force(g, v.clone())? {
                Value::Neutral(Head::Var(l), s) if s.is_empty() && !levels.contains(&l) => {
                    levels.push(l);
                }
                _ => return Ok(None),
            },
            Elim::J { .. } => return Ok(None),
        }
    }
    if levels.iter().all(|l| renaming.contains_key(l)) {
        return Ok(None);
    }
    let span = g.metas.borrow()[m2].span;
    let m3 = g.new_meta(span);
    let n = spine.len();
    let mut body = Term::Meta(m3);
    let mut kept = Vec::new();
    for (i, (elim, level)) in spine.iter().zip(&levels).enumerate() {
        if renaming.contains_key(level) {
            let Elim::App(_, icit) = elim else {
                unreachable!()
            };
            body = Term::app_icit(body, Term::Var(n - 1 - i), *icit);
            kept.push(elim.clone());
        }
    }
    for elim in spine.iter().rev() {
        let Elim::App(_, icit) = elim else {
            unreachable!()
        };
        body = Term::Lam("x".into(), *icit, Rc::new(body));
    }
    g.solve_meta(m2, eval(g, &[], &body)?);
    Ok(Some((m3, kept)))
}

/// Why zonking failed.
#[derive(Debug, PartialEq, Eq)]
pub enum ZonkError {
    /// This metavariable is unsolved.
    Unsolved(usize),
    Resource(ResourceError),
}

impl From<ResourceError> for ZonkError {
    fn from(e: ResourceError) -> ZonkError {
        ZonkError::Resource(e)
    }
}

/// [`zonk_in`], keeping none, outside any `let`.
#[cfg(test)]
pub fn zonk(g: &Globals, level: usize, term: &Term) -> std::result::Result<Term, ZonkError> {
    zonk_in(g, level, term, &|_| false, &[])
}

/// `term` (with `level` variables in scope, inside `lets`) with each
/// occurrence of a `let`'s value folded back to its variable.
pub(crate) fn refold(
    g: &Globals,
    term: Term,
    level: usize,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    let mut term = term;
    for (slot, normal) in lets {
        // The value, moved under `under` more binders, is compared without
        // making the moved copy.
        let hook = |t: &Term, under: usize| {
            crate::matching::same_shifted(normal, t, level - slot + under, 0)
                .then(|| Term::Var(level + under - 1 - slot))
        };
        match fold_back(g, &term, 0, &hook) {
            Ok(Some(t)) => term = t,
            Ok(None) => {}
            Err(_) => {
                return Err(ZonkError::Resource(ResourceError::Nesting(
                    crate::check::PASS,
                )));
            }
        }
    }
    Ok(term)
}

/// [`refold`]'s pass: `term` (under `under` binders of the pass) with each
/// sub-term `hook` replaces replaced, outermost first, or `None` if it
/// replaces none. What's unchanged is shared, not rebuilt: most passes
/// find nothing to fold, and rebuilding (and then dropping) a large normal
/// form once per `let` in scope was most of the cost of lifting.
fn fold_back(
    g: &Globals,
    term: &Term,
    under: usize,
    hook: &dyn Fn(&Term, usize) -> Option<Term>,
) -> Result<Option<Term>> {
    g.budget.nesting(crate::check::PASS)?;
    if let Some(t) = hook(term, under) {
        return Ok(Some(t));
    }
    // A child, folded; `None` if unchanged.
    let go = |t: &Rc<Term>, under| fold_back(g, t, under, hook).map(|t| t.map(Rc::new));
    // The children, if any changed.
    let all = |ts: &[Rc<Term>], under| -> Result<Option<Vec<Rc<Term>>>> {
        let mut out: Option<Vec<Rc<Term>>> = None;
        for (i, t) in ts.iter().enumerate() {
            if let Some(new) = go(t, under)? {
                out.get_or_insert_with(|| ts[..i].to_vec()).push(new);
            } else if let Some(out) = &mut out {
                out.push(t.clone());
            }
        }
        Ok(out)
    };
    let or = |new: Option<Rc<Term>>, old: &Rc<Term>| new.unwrap_or_else(|| old.clone());
    Ok(match term {
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => None,
        Term::Data(d, args) => all(args, under)?.map(|args| Term::Data(*d, args)),
        Term::Ctor(d, c, args) => all(args, under)?.map(|args| Term::Ctor(*d, *c, args)),
        Term::Pi(x, i, a, b) => match (go(a, under)?, go(b, under + 1)?) {
            (None, None) => None,
            (a2, b2) => Some(Term::Pi(x.clone(), *i, or(a2, a), or(b2, b))),
        },
        Term::Lam(x, i, b) => go(b, under + 1)?.map(|b| Term::Lam(x.clone(), *i, b)),
        Term::App(h, a, i) => match (go(h, under)?, go(a, under)?) {
            (None, None) => None,
            (h2, a2) => Some(Term::App(or(h2, h), or(a2, a), *i)),
        },
        Term::Ann(e, t) => match (go(e, under)?, go(t, under)?) {
            (None, None) => None,
            (e2, t2) => Some(Term::Ann(or(e2, e), or(t2, t))),
        },
        Term::Let(x, a, v, b, e) => match (go(a, under)?, go(v, under)?, go(b, under + 1)?) {
            (None, None, None) => None,
            (a2, v2, b2) => Some(Term::Let(x.clone(), or(a2, a), or(v2, v), or(b2, b), *e)),
        },
        Term::Case(ix, d, branches) => {
            let mut new: Vec<Option<Rc<Term>>> = Vec::with_capacity(branches.len());
            for b in branches.iter() {
                new.push(match &b.body {
                    Some(body) => go(body, under + b.names.len())?,
                    None => None,
                });
            }
            if new.iter().all(Option::is_none) {
                None
            } else {
                Some(Term::Case(
                    *ix,
                    *d,
                    branches
                        .iter()
                        .zip(new)
                        .map(|(b, n)| stitchwort_core::term::Branch {
                            names: b.names.clone(),
                            body: b.body.as_ref().map(|old| or(n, old)),
                        })
                        .collect(),
                ))
            }
        }
        Term::NumCase(ix, arms, default) => {
            let mut new: Vec<Option<Rc<Term>>> = Vec::with_capacity(arms.len());
            for a in arms.iter() {
                new.push(go(&a.body, under)?);
            }
            let default2 = go(default, under)?;
            if new.iter().all(Option::is_none) && default2.is_none() {
                None
            } else {
                Some(Term::NumCase(
                    *ix,
                    arms.iter()
                        .zip(new)
                        .map(|(a, n)| stitchwort_core::term::NumArm {
                            value: a.value.clone(),
                            body: or(n, &a.body),
                        })
                        .collect(),
                    or(default2, default),
                ))
            }
        }
        Term::Eq(t, a, b) => {
            let t2 = match t {
                Some(t) => go(t, under)?,
                None => None,
            };
            match (t2, go(a, under)?, go(b, under)?) {
                (None, None, None) => None,
                (t2, a2, b2) => Some(Term::Eq(
                    t.as_ref().map(|t| or(t2, t)),
                    or(a2, a),
                    or(b2, b),
                )),
            }
        }
        Term::J(m, b, p) => match (go(m, under)?, go(b, under)?, go(p, under)?) {
            (None, None, None) => None,
            (m2, b2, p2) => Some(Term::J(or(m2, m), or(b2, b), or(p2, p))),
        },
        Term::Loc(span, t) => go(t, under)?.map(|t| Term::Loc(*span, t)),
    })
}

/// `f`'s result, if it's cheap to compute: a `let`'s value's normal form,
/// for [`refold`], which is only an optimisation. A value too large to
/// compute and compare quickly (a long list, say) isn't folded back; that's
/// also where folding would cost more than it saves.
pub(crate) fn cheaply<T>(g: &Globals, f: impl FnOnce() -> Result<T>) -> Option<T> {
    let _op = g.budget.operation(stitchwort_core::Limits {
        work: 100_000,
        stack: 128 * 1024,
        size: 10_000,
        frames: 10_000,
    });
    f().ok()
}

/// Whether a `let`'s value, as a normal form, is worth folding back: an
/// alias of a variable, or a constant, costs nothing to compute again.
pub(crate) fn worth_folding(normal: &Term) -> bool {
    !matches!(normal.strip_loc(), Term::Var(_) | Term::Nat(_))
}

/// A `let` that `term` is inside, in [`zonk_in`]: its level, and its value
/// as a normal form in the context before it.
pub(crate) type Around = (usize, Rc<Term>);

/// Replaces solved metavariables in `term` (with `level` variables in scope,
/// inside the `let`s `lets`) by their solutions. Fails on an unsolved
/// metavariable, except those `keep` allows, which are left in place.
///
/// A metavariable's solution never mentions a `let`'s variable: it was
/// solved where the variable's value is its value (docs/proposals/let.md
/// §6.1 rule 2). So a solution that a program runs, such as a decision
/// procedure found for `if m < 3` after `let m := n + 1`, would compute the
/// value again (`n + 1 < 3`). Where the solution is put back inside the
/// `let`, occurrences of the value's normal form are folded back to the
/// variable, outermost `let` first (so a later one's value, which mentions
/// an earlier one, is recognised). That's the same term to the checker, and
/// the program shares the value.
pub(crate) fn zonk_in(
    g: &Globals,
    level: usize,
    term: &Term,
    keep: &dyn Fn(usize) -> bool,
    lets: &[Around],
) -> std::result::Result<Term, ZonkError> {
    g.budget.step()?;
    let zonk_keeping = |g: &Globals, level: usize, t: &Term, keep: &dyn Fn(usize) -> bool| {
        zonk_in(g, level, t, keep, lets)
    };
    let go = |t: &Term, level| zonk_keeping(g, level, t, keep).map(Rc::new);
    Ok(match term {
        Term::Meta(_) | Term::App(..) if matches!(term.spine().0, Term::Meta(_)) => {
            let env: Vec<Value> = (0..level).map(Value::var).collect();
            let solved = quote(g, level, &eval(g, &env, term)?)?;
            if let Some(m) = solved.subterms().find_map(|(t, _)| match t {
                Term::Meta(m) if !keep(*m) => Some(*m),
                _ => None,
            }) {
                return Err(ZonkError::Unsolved(m));
            }
            refold(g, solved, level, lets)?
        }
        Term::Let(x, a, v, b, e) => {
            let a = go(a, level)?;
            let v = go(v, level)?;
            let env: Vec<Value> = (0..level).map(Value::var).collect();
            let normal = cheaply(g, || quote(g, level, &eval(g, &env, &v)?));
            let b = match normal {
                Some(normal) if worth_folding(&normal) => {
                    let mut inner = lets.to_vec();
                    inner.push((level, Rc::new(normal)));
                    Rc::new(zonk_in(g, level + 1, b, keep, &inner)?)
                }
                _ => go(b, level + 1)?,
            };
            Term::Let(x.clone(), a, v, b, *e)
        }
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => term.clone(),
        Term::Data(d, args) => Term::Data(
            *d,
            args.iter()
                .map(|a| zonk_keeping(g, level, a, keep).map(Rc::new))
                .collect::<std::result::Result<_, _>>()?,
        ),
        Term::Ctor(d, c, args) => Term::Ctor(
            *d,
            *c,
            args.iter()
                .map(|a| zonk_keeping(g, level, a, keep).map(Rc::new))
                .collect::<std::result::Result<_, _>>()?,
        ),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a, level)?, go(b, level + 1)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b, level + 1)?),
        Term::App(f, a, i) => Term::App(go(f, level)?, go(a, level)?, *i),
        Term::Ann(e, t) => Term::Ann(go(e, level)?, go(t, level)?),
        Term::Case(ix, d, branches) => Term::Case(
            *ix,
            *d,
            branches
                .iter()
                .map(|b| {
                    Ok(stitchwort_core::term::Branch {
                        names: b.names.clone(),
                        body: b
                            .body
                            .as_ref()
                            .map(|body| {
                                zonk_keeping(g, level + b.names.len(), body, keep).map(Rc::new)
                            })
                            .transpose()?,
                    })
                })
                .collect::<std::result::Result<_, ZonkError>>()?,
        ),
        Term::NumCase(ix, arms, default) => Term::NumCase(
            *ix,
            arms.iter()
                .map(|a| {
                    Ok(stitchwort_core::term::NumArm {
                        value: a.value.clone(),
                        body: go(&a.body, level)?,
                    })
                })
                .collect::<std::result::Result<_, ZonkError>>()?,
            go(default, level)?,
        ),
        Term::Eq(t, a, b) => Term::Eq(
            t.as_ref().map(|t| go(t, level)).transpose()?,
            go(a, level)?,
            go(b, level)?,
        ),
        Term::J(m, b, p) => Term::J(go(m, level)?, go(b, level)?, go(p, level)?),
        Term::Loc(span, t) => Term::Loc(*span, go(t, level)?),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_core::{Icit, Sort};
    use stitchwort_syntax::{SourceMap, Span};

    fn globals() -> Globals {
        Globals::default()
    }

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    /// A fresh metavariable applied to the variables at `levels`.
    fn meta(g: &Globals, levels: &[usize]) -> (usize, Value) {
        let m = g.new_meta(span());
        let spine = levels
            .iter()
            .map(|l| Elim::App(Value::var(*l), Icit::Explicit))
            .collect();
        (m, Value::Neutral(Head::Meta(m), spine))
    }

    fn ty() -> Value {
        Value::Sort(Sort::Type(0))
    }

    fn eq(a: Value, b: Value) -> Value {
        Value::Eq(Rc::new(ty()), Rc::new(a), Rc::new(b))
    }

    fn is_var(g: &Globals, v: &Value, level: usize) -> bool {
        matches!(force(g, v.clone()).unwrap(), Value::Neutral(Head::Var(l), s) if l == level && s.is_empty())
    }

    #[test]
    fn solves_a_pattern() {
        let g = globals();
        // ?m x0 x1 = x1, so ?m = a b => b
        let (m, lhs) = meta(&g, &[0, 1]);
        assert!(unify(&g, 2, &lhs, &Value::var(1)).unwrap());
        let solution = g.meta_solution(m).expect("solved");
        let applied = apply_icit(
            &g,
            apply_icit(&g, solution, Value::var(5), Icit::Explicit).unwrap(),
            Value::var(7),
            Icit::Explicit,
        )
        .unwrap();
        assert!(is_var(&g, &applied, 7));
    }

    #[test]
    fn solves_from_either_side() {
        let g = globals();
        let (m, rhs) = meta(&g, &[]);
        assert!(unify(&g, 0, &ty(), &rhs).unwrap());
        assert!(matches!(
            g.meta_solution(m),
            Some(Value::Sort(Sort::Type(0)))
        ));
    }

    #[test]
    fn refuses_a_circular_solution() {
        let g = globals();
        // ?m x0 = (?m x0 = x0) has no finite solution.
        let (m, lhs) = meta(&g, &[0]);
        assert!(!unify(&g, 1, &lhs, &eq(lhs.clone(), Value::var(0))).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn refuses_a_solution_mentioning_a_variable_out_of_scope() {
        let g = globals();
        // ?m only receives x0, so it can't be x1.
        let (m, lhs) = meta(&g, &[0]);
        assert!(!unify(&g, 2, &lhs, &Value::var(1)).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn refuses_a_spine_that_repeats_a_variable() {
        let g = globals();
        // ?m x0 x0 = x0 has two solutions (a b => a and a b => b), so neither is chosen.
        let (m, lhs) = meta(&g, &[0, 0]);
        assert!(!unify(&g, 1, &lhs, &Value::var(0)).unwrap());
        assert!(g.meta_solution(m).is_none());
    }

    #[test]
    fn solves_a_spine_that_repeats_a_variable_when_the_other_side_ignores_it() {
        let g = globals();
        // ?m x0 x0 = Type has one solution, `a b => Type`.
        let (m, lhs) = meta(&g, &[0, 0]);
        assert!(unify(&g, 1, &lhs, &ty()).unwrap());
        assert!(g.meta_solution(m).is_some());
    }

    #[test]
    fn the_same_metavariable_needs_matching_arguments() {
        let g = globals();
        let (_, a) = meta(&g, &[0, 1]);
        let b = match &a {
            Value::Neutral(head, _) => Value::Neutral(
                *head,
                vec![
                    Elim::App(Value::var(1), Icit::Explicit),
                    Elim::App(Value::var(0), Icit::Explicit),
                ]
                .into(),
            ),
            _ => unreachable!(),
        };
        assert!(unify(&g, 2, &a, &a.clone()).unwrap());
        assert!(!unify(&g, 2, &a, &b).unwrap());
    }

    #[test]
    fn prunes_dependencies_that_a_solution_cannot_have() {
        let g = globals();
        // ?a = (?b x0 = Type), where ?a can't depend on x0. Pruning solves
        // ?b := _ => ?c, so the equation has the solution ?a := (?c = Type).
        let (a, lhs) = meta(&g, &[]);
        let (b, b_applied) = meta(&g, &[0]);
        assert!(unify(&g, 1, &lhs, &eq(b_applied.clone(), ty())).unwrap());
        assert!(g.meta_solution(a).is_some());
        assert!(g.meta_solution(b).is_some());
        match force(&g, b_applied).unwrap() {
            Value::Neutral(Head::Meta(c), spine) => {
                assert_ne!(c, b);
                assert!(spine.is_empty(), "?c doesn't depend on x0");
            }
            other => panic!("expected ?b x0 to reduce to a new metavariable, got {other:?}"),
        }
    }

    #[test]
    fn zonk_reports_an_unsolved_metavariable() {
        let g = globals();
        let (m, _) = meta(&g, &[]);
        assert_eq!(
            zonk(&g, 0, &Term::Meta(m)).err(),
            Some(ZonkError::Unsolved(m))
        );
    }

    #[test]
    fn zonk_substitutes_and_normalises_a_solution() {
        let g = globals();
        let (m, lhs) = meta(&g, &[0]);
        assert!(unify(&g, 1, &lhs, &Value::var(0)).unwrap());
        // ?m x0 with ?m = a => a zonks to x0.
        let term = Term::app(Term::Meta(m), Term::Var(0));
        let zonked = zonk(&g, 1, &term).expect("solved");
        assert!(matches!(zonked, Term::Var(0)), "{zonked:?}");
    }

    fn closed(g: &Globals, t: &Term) -> Value {
        eval(g, &[], t).unwrap()
    }

    fn pi(i: Icit, a: Term, b: Term) -> Term {
        Term::Pi("x".into(), i, Rc::new(a), Rc::new(b))
    }

    fn lam(b: Term) -> Term {
        Term::Lam("x".into(), Icit::Explicit, Rc::new(b))
    }

    fn sort(i: u32) -> Term {
        Term::Sort(Sort::Type(i))
    }

    #[test]
    fn refuses_to_unify_things_that_differ_anywhere() {
        let g = globals();
        let refl_eq = |a: Term, b: Term| Term::Eq(Some(Rc::new(sort(1))), Rc::new(a), Rc::new(b));
        let differ = [
            (
                pi(Icit::Explicit, sort(0), sort(0)),
                pi(Icit::Explicit, sort(1), sort(0)),
            ),
            (
                pi(Icit::Explicit, sort(0), sort(0)),
                pi(Icit::Explicit, sort(0), sort(1)),
            ),
            (
                pi(Icit::Explicit, sort(0), sort(0)),
                pi(Icit::Implicit, sort(0), sort(0)),
            ),
            (lam(Term::Var(0)), lam(sort(0))),
            (lam(lam(Term::Var(1))), lam(lam(Term::Var(0)))),
            (refl_eq(sort(0), sort(0)), refl_eq(sort(1), sort(0))),
            (refl_eq(sort(0), sort(0)), refl_eq(sort(0), sort(1))),
            (Term::Refl, sort(0)),
        ];
        for (a, b) in &differ {
            assert!(
                !unify(&g, 0, &closed(&g, a), &closed(&g, b)).unwrap(),
                "{a:?} vs {b:?}"
            );
            assert!(
                !unify(&g, 0, &closed(&g, b), &closed(&g, a)).unwrap(),
                "{b:?} vs {a:?}"
            );
            assert!(
                unify(&g, 0, &closed(&g, a), &closed(&g, a)).unwrap(),
                "{a:?} vs itself"
            );
        }
        // Eta: `x => f x` unifies with `f`, but `x y => f y x` doesn't.
        let f = Value::var(0);
        let eta = eval(
            &g,
            std::slice::from_ref(&f),
            &lam(Term::app(Term::Var(1), Term::Var(0))),
        )
        .unwrap();
        assert!(unify(&g, 1, &eta, &f).unwrap());
        assert!(unify(&g, 1, &f, &eta).unwrap());
        let flipped = eval(
            &g,
            std::slice::from_ref(&f),
            &lam(lam(Term::app(
                Term::app(Term::Var(2), Term::Var(0)),
                Term::Var(1),
            ))),
        )
        .unwrap();
        assert!(!unify(&g, 1, &flipped, &f).unwrap());
    }

    #[test]
    fn spines_must_match_in_length_and_elements() {
        let g = globals();
        let x = Value::var(0);
        let applied = |args: Vec<usize>| {
            Value::Neutral(
                Head::Var(0),
                args.into_iter()
                    .map(|l| Elim::App(Value::var(l), Icit::Explicit))
                    .collect(),
            )
        };
        assert!(unify(&g, 3, &applied(vec![1, 2]), &applied(vec![1, 2])).unwrap());
        assert!(!unify(&g, 3, &applied(vec![1, 2]), &applied(vec![2, 1])).unwrap());
        assert!(!unify(&g, 3, &applied(vec![1]), &applied(vec![1, 2])).unwrap());
        assert!(!unify(&g, 3, &x, &Value::var(1)).unwrap());
        let stuck = |motive: Value| {
            Value::Neutral(
                Head::Var(0),
                vec![Elim::J {
                    motive: Box::new(motive),
                    base: Box::new(ty()),
                }]
                .into(),
            )
        };
        assert!(unify(&g, 1, &stuck(ty()), &stuck(ty())).unwrap());
        assert!(!unify(&g, 1, &stuck(ty()), &stuck(Value::Sort(Sort::Prop))).unwrap());
    }

    #[test]
    fn solutions_can_contain_binders() {
        let g = globals();
        // ?m x0 = (y => x0), so ?m = a => y => a.
        let (m, lhs) = meta(&g, &[0]);
        let rhs = eval(&g, &[Value::var(0)], &lam(Term::Var(1))).unwrap();
        assert!(unify(&g, 1, &lhs, &rhs).unwrap());
        let solution = g.meta_solution(m).expect("solved");
        let applied = apply_icit(
            &g,
            apply_icit(&g, solution, Value::var(5), Icit::Explicit).unwrap(),
            Value::var(9),
            Icit::Explicit,
        )
        .unwrap();
        assert!(is_var(&g, &applied, 5));
        // ?n x0 = ((y : Type) -> x0), a function type mentioning the argument.
        let (n, lhs) = meta(&g, &[0]);
        let rhs = eval(
            &g,
            &[Value::var(0)],
            &pi(Icit::Explicit, sort(0), Term::Var(1)),
        )
        .unwrap();
        assert!(unify(&g, 1, &lhs, &rhs).unwrap());
        assert!(g.meta_solution(n).is_some());
    }

    #[test]
    fn pruning_keeps_the_arguments_a_solution_may_mention() {
        let g = globals();
        // With x0, x1, x2 in scope: ?a x0 x2 = (?b x0 x1 x2 = Type). ?b can't
        // depend on x1, but it may depend on x0 and x2, in that order.
        let (_, lhs) = meta(&g, &[0, 2]);
        let (b, b_applied) = meta(&g, &[0, 1, 2]);
        assert!(unify(&g, 3, &lhs, &eq(b_applied.clone(), ty())).unwrap());
        assert!(g.meta_solution(b).is_some());
        match force(&g, b_applied).unwrap() {
            Value::Neutral(Head::Meta(_), spine) => {
                let kept: Vec<bool> = spine
                    .iter()
                    .map(|e| matches!(e, Elim::App(v, _) if is_var(&g, v, 0)))
                    .collect();
                assert_eq!(spine.len(), 2, "x1 was pruned");
                assert_eq!(kept, vec![true, false], "x0 first, then x2");
                assert!(matches!(&spine[1], Elim::App(v, _) if is_var(&g, v, 2)));
            }
            other => panic!("expected a new metavariable, got {other:?}"),
        }
    }

    #[test]
    fn zonk_works_under_binders() {
        let g = globals();
        let (m, lhs) = meta(&g, &[]);
        assert!(unify(&g, 0, &lhs, &ty()).unwrap());
        // x => ?m, inside a case branch with two fields.
        let term = lam(Term::Meta(m));
        assert!(
            matches!(zonk(&g, 0, &term), Ok(Term::Lam(_, _, ref body)) if matches!(**body, Term::Sort(_)))
        );
        // ?id x0 = x0, used inside a case branch with two fields.
        let (id, id_applied) = meta(&g, &[0]);
        assert!(unify(&g, 1, &id_applied, &Value::var(0)).unwrap());
        let branch = Term::Case(
            0,
            stitchwort_core::DataId(0),
            vec![stitchwort_core::term::Branch {
                names: vec!["a".into(), "b".into()],
                body: Some(Rc::new(Term::app(Term::Meta(id), Term::Var(0)))),
            }]
            .into(),
        );
        match zonk(&g, 1, &branch) {
            Ok(Term::Case(_, _, ref branches)) => {
                assert!(
                    matches!(branches[0].body.as_deref(), Some(Term::Var(0))),
                    "{:?}",
                    branches[0].body
                );
            }
            other => panic!("expected a case, got {other:?}"),
        }
    }

    // Compact lists (docs/proposals/compact-text.md): unifying against one
    // solves metavariables exactly as unifying against its expansion does.

    use stitchwort_core::chars::{self, Chars, CompactText};

    /// Globals with `List` and `Char` registered as data types 0 and 1. (No
    /// declarations: unification only compares constructors.)
    fn text_globals() -> (Globals, CompactText) {
        let mut g = globals();
        let text = CompactText::new(stitchwort_core::DataId(0), stitchwort_core::DataId(1));
        g.builtins.text = Some(text.clone());
        (g, text)
    }

    fn compact(text: &str) -> Value {
        Value::Chars(Chars::whole(text.chars().collect()))
    }

    /// The expansion, built from constructors.
    fn expanded(t: &CompactText, text: &str) -> Value {
        let mut list = Value::Ctor(t.list, 0, Vec::new().into());
        for c in text.chars().rev() {
            list = Value::Ctor(t.list, 1, [chars::char_value(t, c), list].into());
        }
        list
    }

    fn cons(t: &CompactText, head: Value, tail: Value) -> Value {
        Value::Ctor(t.list, 1, [head, tail].into())
    }

    fn mk_char(t: &CompactText, code: Value, proof: Value) -> Value {
        Value::Ctor(t.char, 0, [code, proof].into())
    }

    fn quoted(g: &Globals, v: Value) -> String {
        format!("{:?}", quote(g, 0, &v).unwrap())
    }

    #[test]
    fn cons_of_metavariables_against_a_compact_list() {
        for compact_side in [true, false] {
            let (g, t) = text_globals();
            let t = &t;
            let (c, c_value) = meta(&g, &[]);
            let (tail, tail_value) = meta(&g, &[]);
            let lhs = cons(t, c_value, tail_value);
            let rhs = if compact_side {
                compact("ab")
            } else {
                expanded(t, "ab")
            };
            assert!(unify(&g, 0, &lhs, &rhs).unwrap());
            let c = g.meta_solution(c).unwrap();
            let tail = g.meta_solution(tail).unwrap();
            assert_eq!(quoted(&g, c), quoted(&g, chars::char_value(t, 'a')));
            if compact_side {
                // The rest of the same range.
                assert!(matches!(&tail, Value::Chars(r) if r.as_slice() == ['b']));
            }
            assert!(stitchwort_core::value::conv(&g, 0, &tail, &expanded(t, "b")).unwrap());
            // Consistent: the solved left side is the right side.
            assert!(unify(&g, 0, &lhs, &compact("ab")).unwrap());
            assert!(!unify(&g, 0, &lhs, &compact("ac")).unwrap());
        }
    }

    #[test]
    fn a_metavariable_is_solved_with_the_compact_list_itself() {
        let (g, _) = text_globals();
        let (m, lhs) = meta(&g, &[]);
        assert!(unify(&g, 0, &lhs, &compact("abc")).unwrap());
        assert_eq!(
            format!("{:?}", zonk(&g, 0, &Term::Meta(m)).unwrap()),
            r#"Chars(Chars("abc"))"#
        );
    }

    /// `Cons (MkChar ?n ?p) Nil ~ "a"`, with `?n` solved before, after, or
    /// differently.
    #[test]
    fn character_and_proof_metavariables_before_and_after_solving() {
        for (first, expect) in [(None, true), (Some(97u32), true), (Some(98), false)] {
            for compact_side in [true, false] {
                let (g, t) = text_globals();
                let t = &t;
                let (n, n_value) = meta(&g, &[]);
                let (p, p_value) = meta(&g, &[]);
                if let Some(code) = first {
                    let code = stitchwort_core::native::nat_value(code.into());
                    assert!(unify(&g, 0, &n_value, &code).unwrap());
                }
                let nil = Value::Ctor(t.list, 0, Vec::new().into());
                let lhs = cons(t, mk_char(t, n_value.clone(), p_value), nil);
                let rhs = if compact_side {
                    compact("a")
                } else {
                    expanded(t, "a")
                };
                assert_eq!(unify(&g, 0, &lhs, &rhs).unwrap(), expect, "{first:?}");
                if expect {
                    assert_eq!(quoted(&g, g.meta_solution(n).unwrap()), "Nat(97)");
                    assert_eq!(quoted(&g, g.meta_solution(p).unwrap()), "Refl");
                    // Afterwards, `?n` can't be anything else.
                    let other = stitchwort_core::native::nat_value(98u32.into());
                    assert!(!unify(&g, 0, &n_value, &other).unwrap());
                }
            }
        }
    }

    /// A rigid proof variable stays distinct from `rfl`, against the compact
    /// list as against its expansion.
    #[test]
    fn a_rigid_proof_is_not_rfl() {
        let (g, t) = text_globals();
        let t = &t;
        let code = stitchwort_core::native::nat_value(97u32.into());
        let nil = Value::Ctor(t.list, 0, Vec::new().into());
        let lhs = cons(t, mk_char(t, code, Value::var(0)), nil);
        assert!(!unify(&g, 1, &lhs, &compact("a")).unwrap());
        assert!(!unify(&g, 1, &lhs, &expanded(t, "a")).unwrap());
        assert!(!unify(&g, 1, &compact("a"), &lhs).unwrap());
    }

    #[test]
    fn compact_lists_unify_by_their_characters() {
        let (g, t) = text_globals();
        let t = &t;
        let ab: Rc<[char]> = "xaby".chars().collect();
        let middle = Value::Chars(Chars::new(ab, 1, 3).unwrap());
        assert!(unify(&g, 0, &middle, &compact("ab")).unwrap());
        assert!(unify(&g, 0, &middle, &expanded(t, "ab")).unwrap());
        assert!(!unify(&g, 0, &middle, &compact("abc")).unwrap());
        assert!(!unify(&g, 0, &middle, &expanded(t, "a")).unwrap());
        // A cons cell in front of a compact tail.
        let mixed = cons(t, chars::char_value(t, 'a'), compact("b"));
        assert!(unify(&g, 0, &mixed, &compact("ab")).unwrap());
        assert!(unify(&g, 0, &compact("ab"), &mixed).unwrap());
        assert!(!unify(&g, 0, &mixed, &compact("ba")).unwrap());
    }

    #[test]
    fn identical_functions_unify_without_solving_anything() {
        let g = globals();
        // `x => ?m y x`, twice, with different values for the variable
        // the body doesn't use.
        let (m, _) = meta(&g, &[]);
        let body = || {
            Rc::new(Term::App(
                Rc::new(Term::App(
                    Rc::new(Term::Meta(m)),
                    Rc::new(Term::Var(1)),
                    Icit::Explicit,
                )),
                Rc::new(Term::Var(0)),
                Icit::Explicit,
            ))
        };
        let lam = |unused: usize| {
            Value::Lam(
                "x".into(),
                Icit::Explicit,
                Closure {
                    env: vec![Value::var(unused), Value::var(3)].into(),
                    body: body(),
                },
            )
        };
        let before = g.budget.total_work();
        assert!(unify(&g, 4, &lam(0), &lam(1)).unwrap());
        assert_eq!(g.budget.total_work() - before, 1, "one step: the shortcut");
        assert!(g.meta_solution(m).is_none());
    }
}
