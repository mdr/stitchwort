//! Pattern unification for metavariables, and zonking (substituting solutions
//! back into terms). Follows András Kovács' elaboration-zoo.

use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::value::{Closure, Elim, Head, apply_icit, eval, force, quote};
use stitchwort_core::{Globals, Term, Value};

/// Makes `a` and `b` equal by solving metavariables, with `level` variables in
/// scope. Returns `false` if they can't be made equal.
pub fn unify(g: &Globals, level: usize, a: &Value, b: &Value) -> bool {
    let a = force(g, a.clone());
    let b = force(g, b.clone());
    let fresh = Value::var(level);
    match (&a, &b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            i1 == i2
                && unify(g, level, a1, a2)
                && unify(
                    g,
                    level + 1,
                    &b1.apply(g, fresh.clone()),
                    &b2.apply(g, fresh),
                )
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => unify(
            g,
            level + 1,
            &b1.apply(g, fresh.clone()),
            &b2.apply(g, fresh),
        ),
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => unify(
            g,
            level + 1,
            &b.apply(g, fresh.clone()),
            &apply_icit(g, other.clone(), fresh, *i),
        ),
        (Value::Data(d1, a1), Value::Data(d2, a2)) => d1 == d2 && unify_all(g, level, a1, a2),
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            d1 == d2 && c1 == c2 && unify_all(g, level, a1, a2)
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            unify(g, level, t1, t2) && unify(g, level, x1, x2) && unify(g, level, y1, y2)
        }
        (Value::Refl, Value::Refl) => true,
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2)) if m1 == m2 => {
            unify_spines(g, level, s1, s2)
        }
        (Value::Neutral(Head::Meta(m), spine), other)
        | (other, Value::Neutral(Head::Meta(m), spine)) => solve(g, level, *m, spine, other),
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) if h1 == h2 => {
            unify_spines(g, level, s1, s2)
        }
        _ => false,
    }
}

fn unify_all(g: &Globals, level: usize, xs: &[Value], ys: &[Value]) -> bool {
    xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| unify(g, level, x, y))
}

fn unify_spines(g: &Globals, level: usize, s1: &[Elim], s2: &[Elim]) -> bool {
    s1.len() == s2.len()
        && s1.iter().zip(s2).all(|pair| match pair {
            (Elim::App(x, _), Elim::App(y, _)) => unify(g, level, x, y),
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                },
            ) => unify(g, level, m1, m2) && unify(g, level, b1, b2),
            _ => false,
        })
}

/// Solves `?m spine = rhs`, where the spine must be distinct variables (a
/// "pattern"). The solution is `\x1 … xn -> rhs`, with the spine's variables
/// renamed to the lambda's parameters.
fn solve(g: &Globals, level: usize, m: usize, spine: &[Elim], rhs: &Value) -> bool {
    let mut renaming = HashMap::new();
    let mut icits = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(arg, icit) => match force(g, arg.clone()) {
                Value::Neutral(Head::Var(l), s) if s.is_empty() && !renaming.contains_key(&l) => {
                    renaming.insert(l, renaming.len());
                    icits.push(*icit);
                }
                _ => return false,
            },
            Elim::J { .. } => return false,
        }
    }
    let Some(mut solution) = rename(g, m, &renaming, renaming.len(), level, rhs) else {
        return false;
    };
    for icit in icits.into_iter().rev() {
        solution = Term::Lam("x".into(), icit, Rc::new(solution));
    }
    let value = eval(g, &[], &solution);
    g.solve_meta(m, value);
    true
}

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
) -> Option<Term> {
    let go = |v: &Value| rename(g, m, renaming, dom, cod, v);
    let under = |closure: &Closure| {
        let mut renaming = renaming.clone();
        renaming.insert(cod, dom);
        rename(
            g,
            m,
            &renaming,
            dom + 1,
            cod + 1,
            &closure.apply(g, Value::var(cod)),
        )
    };
    Some(match force(g, value.clone()) {
        Value::Sort(s) => Term::Sort(s),
        Value::Refl => Term::Refl,
        Value::Pi(x, i, a, b) => Term::Pi(x, i, Rc::new(go(&a)?), Rc::new(under(&b)?)),
        Value::Lam(x, i, b) => Term::Lam(x, i, Rc::new(under(&b)?)),
        Value::Data(d, args) => Term::Data(d, args.iter().map(go).collect::<Option<_>>()?),
        Value::Ctor(d, c, args) => Term::Ctor(d, c, args.iter().map(go).collect::<Option<_>>()?),
        Value::Eq(t, a, b) => Term::Eq(Some(Rc::new(go(&t)?)), Rc::new(go(&a)?), Rc::new(go(&b)?)),
        Value::Neutral(Head::Meta(m2), spine) if m2 != m => {
            if let Some((m3, kept)) = prune(g, m2, &spine, renaming) {
                let mut term = Term::Meta(m3);
                for elim in kept {
                    let Elim::App(v, i) = elim else {
                        unreachable!("pruned spines only contain applications")
                    };
                    term = Term::app_icit(term, go(&v)?, i);
                }
                return Some(term);
            }
            rename_spine(g, m, renaming, dom, cod, Term::Meta(m2), &spine)?
        }
        Value::Neutral(head, spine) => {
            let head = match head {
                Head::Meta(_) => return None,
                Head::Def(id) => Term::Def(id),
                Head::Var(l) => {
                    let new = *renaming.get(&l)?;
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
) -> Option<Term> {
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
    Some(term)
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
) -> Option<(usize, Vec<Elim>)> {
    let mut levels = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(v, _) => match force(g, v.clone()) {
                Value::Neutral(Head::Var(l), s) if s.is_empty() && !levels.contains(&l) => {
                    levels.push(l);
                }
                _ => return None,
            },
            Elim::J { .. } => return None,
        }
    }
    if levels.iter().all(|l| renaming.contains_key(l)) {
        return None;
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
    g.solve_meta(m2, eval(g, &[], &body));
    Some((m3, kept))
}

/// Replaces solved metavariables in `term` (with `level` variables in scope)
/// by their solutions. Returns an unsolved metavariable if there is one.
pub fn zonk(g: &Globals, level: usize, term: &Term) -> Result<Term, usize> {
    let go = |t: &Term, level| zonk(g, level, t).map(Rc::new);
    Ok(match term {
        Term::Meta(_) | Term::App(..) if matches!(term.spine().0, Term::Meta(_)) => {
            let env: Vec<Value> = (0..level).map(Value::var).collect();
            let solved = quote(g, level, &eval(g, &env, term));
            if let Some(m) = first_meta(&solved) {
                return Err(m);
            }
            solved
        }
        Term::Var(_) | Term::Def(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => term.clone(),
        Term::Data(d, args) => Term::Data(
            *d,
            args.iter()
                .map(|a| zonk(g, level, a))
                .collect::<Result<_, _>>()?,
        ),
        Term::Ctor(d, c, args) => Term::Ctor(
            *d,
            *c,
            args.iter()
                .map(|a| zonk(g, level, a))
                .collect::<Result<_, _>>()?,
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
                        body: zonk(g, level + b.names.len(), &b.body)?,
                    })
                })
                .collect::<Result<_, usize>>()?,
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

fn first_meta(term: &Term) -> Option<usize> {
    match term {
        Term::Meta(m) => Some(*m),
        Term::Var(_) | Term::Def(_) | Term::Sort(_) | Term::Refl => None,
        Term::Data(_, args) | Term::Ctor(_, _, args) => args.iter().find_map(first_meta),
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => {
            first_meta(a).or_else(|| first_meta(b))
        }
        Term::Lam(_, _, b) | Term::Loc(_, b) => first_meta(b),
        Term::Case(_, _, branches) => branches.iter().find_map(|b| first_meta(&b.body)),
        Term::Eq(t, a, b) => t
            .as_deref()
            .and_then(first_meta)
            .or_else(|| first_meta(a))
            .or_else(|| first_meta(b)),
        Term::J(m, b, p) => first_meta(m)
            .or_else(|| first_meta(b))
            .or_else(|| first_meta(p)),
    }
}
