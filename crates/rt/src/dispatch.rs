//! Compiled handler dispatch, stage 1a spike (SW-2507,
//! docs/proposals/compiled-handler-dispatch.md §2): a handler's step
//! `handlePlus [5 implicit] (A.%elim [implicit…] c₁ … cₙ) forward` lowered as
//! one closure `o k [jump s] => case o of L o′ => case o′ of opᵢ x => cᵢ x k
//! [jump s] | R o′ => forward o′ k [jump s]`, the two case trees being
//! `handlePlus`'s and `A.%elim`'s own run bodies with their parameters
//! replaced by the arguments. Each clause and the forward occurs once, in
//! its arm, so a literal lambda there is β-reduced by the lowering; a clause
//! that isn't a lambda or a variable is bound by a `let` outside the closure,
//! so it is still computed once, at handler start.
//!
//! A prototype for measurement, not finished work: it has no unit tests, and
//! `SW_NO_DISPATCH=1` at build time turns it off.

use std::rc::Rc;

use stitchwort_core::budget::Result;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, Icit, NumArm};
use stitchwort_core::{DefId, Ev, Term};

use crate::erasure::def_shape;
use crate::fusion::{spine_icit, strip};

pub struct Dispatch {
    pub handle_plus: DefId,
    mask: Vec<bool>,
    arity: usize,
}

impl Dispatch {
    pub fn new(g: &Ev) -> Option<Dispatch> {
        if std::env::var_os("SW_NO_DISPATCH").is_some() {
            return None;
        }
        let handle_plus = g.env.registry().loaded_def(Builtin::HandlePlus)?;
        let mask = def_shape(g, handle_plus, false).ok()?.mask().to_vec();
        let arity = g.def(handle_plus).arity();
        g.def(handle_plus).run_body()?;
        Some(Dispatch {
            handle_plus,
            mask,
            arity,
        })
    }

    /// `handlePlus` applied to `args` (everything but `o` and `k`) as one
    /// lambda of `o`, `k` and, where `state` (a fused state handler's step,
    /// which the loop always gives four arguments), `jump` and `s`.
    pub fn rewrite(&self, g: &Ev, args: &[&Term], state: bool) -> Result<Option<Term>> {
        if args.len() + 2 != self.arity || self.mask.len() < self.arity {
            return Ok(None);
        }
        let runtime: Vec<usize> = (0..args.len()).filter(|i| !self.mask[*i]).collect();
        let [elim_at, forward_at] = runtime[..] else {
            return Ok(None);
        };
        let Some((Term::Def(elim), elim_args)) = spine_icit(args[elim_at]) else {
            return Ok(None);
        };
        let elim = *elim;
        let elim_def = g.def(elim);
        if elim_def.run_body().is_none() || elim_args.len() + 2 != elim_def.arity() {
            return Ok(None);
        }
        let Ok(elim_shape) = def_shape(g, elim, false) else {
            return Ok(None);
        };
        let elim_mask = elim_shape.mask().to_vec();
        if elim_mask.len() < elim_def.arity() {
            return Ok(None);
        }
        let new = if state { 4 } else { 2 };
        // The runtime arguments that aren't lambdas or variables, bound
        // outside the closure: (where among `elim`'s arguments, or `None`
        // for the forward) in binding order.
        let needs_let = |t: &Term| !matches!(strip(t), Term::Lam(..) | Term::Var(_));
        let mut bound: Vec<(Option<usize>, &Term)> = Vec::new();
        for (i, (arg, _)) in elim_args.iter().enumerate() {
            if !elim_mask[i] && needs_let(arg) {
                bound.push((Some(i), arg));
            }
        }
        if needs_let(args[forward_at]) {
            bound.push((None, args[forward_at]));
        }
        let b = bound.len();
        // An outer term, or a bound one's variable, inside the lets and the
        // closure's binders.
        let inside = |at: Option<usize>, t: &Term| -> Result<Term> {
            match bound.iter().position(|(w, _)| *w == at) {
                Some(j) => Ok(Term::Var(new + (b - 1 - j))),
                None => t.shift(g, b + new, 0),
            }
        };
        let mut elim_app = Term::Def(elim);
        for (i, (arg, icit)) in elim_args.iter().enumerate() {
            let arg = if elim_mask[i] {
                arg.shift(g, b + new, 0)?
            } else {
                inside(Some(i), arg)?
            };
            elim_app = Term::app_icit(elim_app, arg, *icit);
        }
        let mut plus_args = Vec::with_capacity(self.arity + 2);
        for (i, arg) in args.iter().enumerate() {
            plus_args.push(if i == elim_at {
                elim_app.clone()
            } else if i == forward_at {
                inside(None, arg)?
            } else {
                arg.shift(g, b + new, 0)?
            });
        }
        plus_args.push(Term::Var(new - 1));
        plus_args.push(Term::Var(new - 2));
        if state {
            plus_args.push(Term::Var(1));
            plus_args.push(Term::Var(0));
        }
        let Some(body) = inline_call(g, self.handle_plus, &plus_args, Some(elim))? else {
            return Ok(None);
        };
        let mut out = body;
        for name in ["s", "jump", "k", "o"].into_iter().skip(4 - new) {
            out = Term::Lam(name.into(), Icit::Explicit, Rc::new(out));
        }
        for (j, (_, value)) in bound.iter().enumerate().rev() {
            out = Term::Let(
                "c".into(),
                Rc::new(Term::Refl),
                Rc::new(value.shift(g, j, 0)?),
                Rc::new(out),
                false,
            );
        }
        Ok(Some(out))
    }
}

/// `id`'s case tree with its parameters replaced by `args` (terms in the
/// current scope, at least its arity of them; a scrutinee's must be a
/// variable) and the rest applied in each arm; an arm that is then a
/// saturated call of `also` is inlined in turn.
fn inline_call(g: &Ev, id: DefId, args: &[Term], also: Option<DefId>) -> Result<Option<Term>> {
    let def = g.def(id);
    let arity = def.arity();
    let Some(body) = def.run_body() else {
        return Ok(None);
    };
    if args.len() < arity {
        return Ok(None);
    }
    let mut lams = Term::peel_lams_rc(body, arity).as_ref().clone();
    for _ in 0..arity {
        lams = Term::Lam("x".into(), Icit::Explicit, Rc::new(lams));
    }
    for arg in &args[..arity] {
        let Term::Lam(_, _, inner) = &lams else {
            unreachable!("a lambda per parameter")
        };
        let next = inner.instantiate(g, arg)?;
        lams = next;
    }
    let rest = &args[arity..];
    let leaf = |t: &Term, depth: usize| -> Result<Term> {
        let mut t = t.clone();
        for r in rest {
            t = Term::app(t, r.shift(g, depth, 0)?);
        }
        if let Some(inner) = also
            && let Some((Term::Def(h), spine)) = spine_icit(&t)
            && *h == inner
        {
            let spine: Vec<Term> = spine.iter().map(|(a, _)| (*a).clone()).collect();
            if let Some(inlined) = inline_call(g, inner, &spine, None)? {
                return Ok(inlined);
            }
        }
        Ok(t)
    };
    Ok(Some(map_leaves(&lams, 0, &leaf)?))
}

/// `term` with each leaf of its case tree (`depth` binders below the top)
/// replaced by `leaf`.
fn map_leaves(
    term: &Term,
    depth: usize,
    leaf: &dyn Fn(&Term, usize) -> Result<Term>,
) -> Result<Term> {
    match term {
        Term::Loc(_, inner) => map_leaves(inner, depth, leaf),
        Term::Case(ix, d, branches) => {
            let mut out = Vec::with_capacity(branches.len());
            for branch in branches.iter() {
                let body = match &branch.body {
                    Some(body) => {
                        Some(Rc::new(map_leaves(body, depth + branch.names.len(), leaf)?))
                    }
                    None => None,
                };
                out.push(Branch {
                    names: branch.names.clone(),
                    body,
                });
            }
            Ok(Term::Case(*ix, *d, out.into()))
        }
        Term::NumCase(ix, arms, default) => {
            let mut out = Vec::with_capacity(arms.len());
            for arm in arms.iter() {
                out.push(NumArm {
                    value: arm.value.clone(),
                    body: Rc::new(map_leaves(&arm.body, depth, leaf)?),
                });
            }
            Ok(Term::NumCase(
                *ix,
                out.into(),
                Rc::new(map_leaves(default, depth, leaf)?),
            ))
        }
        other => leaf(other, depth),
    }
}
