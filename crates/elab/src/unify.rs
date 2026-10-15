//! Pattern unification for metavariables, and zonking (substituting solutions
//! back into terms). Follows András Kovács' elaboration-zoo.

use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::budget::{ResourceError, Result};
use stitchwort_core::native;
use stitchwort_core::value::{Closure, Elim, Head, apply_icit, eta_definition, eval, force, quote};
use stitchwort_core::{Globals, Term, Value};

/// Makes `a` and `b` equal by solving metavariables, with `level` variables in
/// scope. `Ok(false)` if they can't be made equal; an error if it ran out of
/// resources before finding out. A `false` may be followed by trying another
/// way; an error never is.
pub fn unify(g: &Globals, level: usize, a: &Value, b: &Value) -> Result<bool> {
    g.budget.step()?;
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
            |x, y| unify(g, level, x, y),
            |x, v| Ok(is_meta(x) && unify(g, level, x, v)?),
        );
    }
    let fresh = Value::var(level);
    Ok(match (&a, &b) {
        (Value::Sort(s), Value::Sort(t)) => s == t,
        (Value::Pi(_, i1, a1, b1), Value::Pi(_, i2, a2, b2)) => {
            i1 == i2
                && unify(g, level, a1, a2)?
                && unify(
                    g,
                    level + 1,
                    &b1.apply(g, fresh.clone())?,
                    &b2.apply(g, fresh)?,
                )?
        }
        (Value::Lam(_, _, b1), Value::Lam(_, _, b2)) => unify(
            g,
            level + 1,
            &b1.apply(g, fresh.clone())?,
            &b2.apply(g, fresh)?,
        )?,
        (Value::Lam(_, i, b), other) | (other, Value::Lam(_, i, b)) => unify(
            g,
            level + 1,
            &b.apply(g, fresh.clone())?,
            &apply_icit(g, other.clone(), fresh, *i)?,
        )?,
        (Value::Data(d1, a1), Value::Data(d2, a2)) => d1 == d2 && unify_all(g, level, a1, a2)?,
        (Value::Ctor(d1, c1, a1), Value::Ctor(d2, c2, a2)) => {
            d1 == d2 && c1 == c2 && unify_all(g, level, a1, a2)?
        }
        (Value::Eq(t1, x1, y1), Value::Eq(t2, x2, y2)) => {
            unify(g, level, t1, t2)? && unify(g, level, x1, x2)? && unify(g, level, y1, y2)?
        }
        (Value::Refl, Value::Refl) => true,
        (Value::Neutral(Head::Meta(m1), s1), Value::Neutral(Head::Meta(m2), s2)) if m1 == m2 => {
            unify_spines(g, level, s1, s2)?
        }
        (Value::Neutral(Head::Meta(m), spine), other)
        | (other, Value::Neutral(Head::Meta(m), spine)) => {
            solve(g, level, *m, spine, other)? || first_order(g, level, *m, spine, other)?
        }
        (Value::Neutral(h1, s1), Value::Neutral(h2, s2)) if h1 == h2 => {
            unify_spines(g, level, s1, s2)? || eta_definition(g, level, &a, &b, unify)?
        }
        _ => eta_definition(g, level, &a, &b, unify)?,
    })
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
            &Value::Neutral(Head::Meta(m), rest1.to_vec()),
            &Value::Neutral(*head, rest2.to_vec()),
        )?)
}

fn unify_all(g: &Globals, level: usize, xs: &[Value], ys: &[Value]) -> Result<bool> {
    if xs.len() != ys.len() {
        return Ok(false);
    }
    for (x, y) in xs.iter().zip(ys) {
        if !unify(g, level, x, y)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn unify_spines(g: &Globals, level: usize, s1: &[Elim], s2: &[Elim]) -> Result<bool> {
    if s1.len() != s2.len() {
        return Ok(false);
    }
    for pair in s1.iter().zip(s2) {
        let same = match pair {
            (Elim::App(x, _), Elim::App(y, _)) => unify(g, level, x, y)?,
            (
                Elim::J {
                    motive: m1,
                    base: b1,
                },
                Elim::J {
                    motive: m2,
                    base: b2,
                },
            ) => unify(g, level, m1, m2)? && unify(g, level, b1, b2)?,
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
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
/// "pattern"). The solution is `\x1 … xn -> rhs`, with the spine's variables
/// renamed to the lambda's parameters.
fn solve(g: &Globals, level: usize, m: usize, spine: &[Elim], rhs: &Value) -> Result<bool> {
    let mut renaming = HashMap::new();
    let mut icits = Vec::new();
    for elim in spine {
        match elim {
            Elim::App(arg, icit) => match force(g, arg.clone())? {
                Value::Neutral(Head::Var(l), s) if s.is_empty() && !renaming.contains_key(&l) => {
                    renaming.insert(l, renaming.len());
                    icits.push(*icit);
                }
                _ => return Ok(false),
            },
            Elim::J { .. } => return Ok(false),
        }
    }
    let Some(mut solution) = settle(rename(g, m, &renaming, renaming.len(), level, rhs))? else {
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

/// Replaces solved metavariables in `term` (with `level` variables in scope)
/// by their solutions. Fails on an unsolved metavariable.
pub fn zonk(g: &Globals, level: usize, term: &Term) -> std::result::Result<Term, ZonkError> {
    g.budget.step()?;
    let go = |t: &Term, level| zonk(g, level, t).map(Rc::new);
    Ok(match term {
        Term::Meta(_) | Term::App(..) if matches!(term.spine().0, Term::Meta(_)) => {
            let env: Vec<Value> = (0..level).map(Value::var).collect();
            let solved = quote(g, level, &eval(g, &env, term)?)?;
            if let Some(m) = first_meta(&solved) {
                return Err(ZonkError::Unsolved(m));
            }
            solved
        }
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
            term.clone()
        }
        Term::Data(d, args) => Term::Data(
            *d,
            args.iter()
                .map(|a| zonk(g, level, a).map(Rc::new))
                .collect::<std::result::Result<_, _>>()?,
        ),
        Term::Ctor(d, c, args) => Term::Ctor(
            *d,
            *c,
            args.iter()
                .map(|a| zonk(g, level, a).map(Rc::new))
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
                        body: Rc::new(zonk(g, level + b.names.len(), &b.body)?),
                    })
                })
                .collect::<std::result::Result<_, ZonkError>>()?,
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
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl => None,
        Term::Data(_, args) | Term::Ctor(_, _, args) => args.iter().find_map(|a| first_meta(a)),
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
        // ?m x0 x1 = x1, so ?m = \a b -> b
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
        // ?m x0 x0 = x0 has two solutions (\a b -> a and \a b -> b), so neither is chosen.
        let (m, lhs) = meta(&g, &[0, 0]);
        assert!(!unify(&g, 1, &lhs, &Value::var(0)).unwrap());
        assert!(g.meta_solution(m).is_none());
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
                ],
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
        // ?b := \_ -> ?c, so the equation has the solution ?a := (?c = Type).
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
        // ?m x0 with ?m = \a -> a zonks to x0.
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
        // Eta: `\x -> f x` unifies with `f`, but `\x y -> f y x` doesn't.
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
        let stuck =
            |motive: Value| Value::Neutral(Head::Var(0), vec![Elim::J { motive, base: ty() }]);
        assert!(unify(&g, 1, &stuck(ty()), &stuck(ty())).unwrap());
        assert!(!unify(&g, 1, &stuck(ty()), &stuck(Value::Sort(Sort::Prop))).unwrap());
    }

    #[test]
    fn solutions_can_contain_binders() {
        let g = globals();
        // ?m x0 = (\y -> x0), so ?m = \a -> \y -> a.
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
        // \x -> ?m, inside a case branch with two fields.
        let term = lam(Term::Meta(m));
        assert!(
            matches!(zonk(&g, 0, &term), Ok(Term::Lam(_, _, body)) if matches!(*body, Term::Sort(_)))
        );
        // ?id x0 = x0, used inside a case branch with two fields.
        let (id, id_applied) = meta(&g, &[0]);
        assert!(unify(&g, 1, &id_applied, &Value::var(0)).unwrap());
        let branch = Term::Case(
            0,
            stitchwort_core::DataId(0),
            vec![stitchwort_core::term::Branch {
                names: vec!["a".into(), "b".into()],
                body: Rc::new(Term::app(Term::Meta(id), Term::Var(0))),
            }]
            .into(),
        );
        match zonk(&g, 1, &branch) {
            Ok(Term::Case(_, _, branches)) => {
                assert!(
                    matches!(*branches[0].body, Term::Var(0)),
                    "{:?}",
                    branches[0].body
                );
            }
            other => panic!("expected a case, got {other:?}"),
        }
    }
}
