//! State-passing handlers run as a loop (docs/proposals/effect-runtime.md
//! §4 A′ and §9.1.5, D1162; stage 4d), shared by the runtime's lowering and
//! the JS backend.
//!
//! A handler whose result is a function of a state, at the empty row,
//!
//! ```text
//! handle prog() with
//!   | return x => s => x
//!   | next u, k => s => k s (s + 1)
//! ```
//!
//! is a fold whose clauses each return a function of the state, and a
//! clause that resumes calls `k`'s function with the next state. In JS that
//! is a chain of calls, one per operation, each a tail call that JS doesn't
//! optimise, so it overflows the stack. This pass recognises the shape in
//! the elaborated term, after elaboration (no elaborator change, so no hash
//! changes), and rewrites the fold's clauses so that the backends can run
//! it as a loop with the state in a variable:
//!
//! - each operation clause `x, k => s => body` (under `Done` at the closed
//!   empty row) becomes `x, k => jump => s => body′`, where `body′` is
//!   `body` with every `k v s′` in tail position (through `let`s, applied
//!   lambdas, `if` and `Decidable.elim`) replaced by `jump v s′`;
//! - at the closed empty row the return clause `x => Done e` becomes
//!   `x => e`, so it gives the state's function directly.
//!
//! The backends' fold (`effFoldState` in JS, [`crate::effect::EffectOp`]'s
//! `FoldState…` natively) applies a clause to the operation, a real `k`, a
//! `jump` that only records its two arguments, and the state; if the clause
//! returns a recorded jump, it goes on with the rest of the computation from
//! `v` and the state `s′`, in the same loop; anything else is the result.
//! Every other use of `k` (not in tail position, twice, stored, under a
//! lambda) gets the real `k`, which runs the same loop from where the
//! operation was, so the meaning is the tree's whatever the clause does.
//!
//! Recognised, for a `foldComp` whose carrier is
//!
//! - `Comp NoOp NoRes (S -> R)` (the closed empty row: `handle` with
//!   `runPure` around it): the return clause must be `Done e` and every
//!   operation clause `Done e`;
//! - `CompIn Empty (S -> R)`, or `S -> R` once empty-row specialisation has
//!   reduced that (an empty-row variant of a handler written for `{e}`):
//!   any clauses, since `doneIn Empty` is the identity.
//!
//! A clause whose `e` isn't a lambda is eta-expanded (`s => e s`), which
//! is sound since generated code is pure and total. A fold none of whose
//! clauses has a tail `k v s′` is left alone.

use std::rc::Rc;

use stitchwort_core::budget::Result;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Icit;
use stitchwort_core::{DataId, DefId, Globals, Term};

use crate::erasure::def_shape;

/// How deeply the tail positions of a clause are followed.
const MAX_DEPTH: usize = 200;

/// What the rewrite needs to know about the core.
pub struct StateFusion {
    comp: DataId,
    no_op: DataId,
    comp_in: Option<DefId>,
    /// `Effects` and the index of its `Empty`.
    row: Option<(DataId, usize)>,
    run_pure: DefId,
    /// `runPure`'s parameters, implicit ones included.
    run_pure_params: usize,
    handle_plus: DefId,
    /// Which of `handlePlus`'s parameters are erased.
    handle_plus_mask: Vec<bool>,
    if_then_else: Option<DefId>,
    elim_dec: Option<DefId>,
}

/// A fold to run as a loop: its rewritten return clause and operation
/// function (`foldComp`'s `done` and `call`).
pub struct Fused {
    /// The carrier is a computation (`Comp NoOp NoRes`): the fold's result,
    /// and `k`'s, are `Done` of the state's function.
    pub comp: bool,
    pub done: Term,
    pub call: Term,
    /// How many tail resumptions were made jumps, over all clauses.
    pub jumps: usize,
}

impl StateFusion {
    pub fn new(g: &Globals) -> Option<StateFusion> {
        let r = &g.registry;
        let run_pure = r.loaded_def(Builtin::RunPure)?;
        let run_pure_params = def_shape(g, run_pure, false).ok()?.mask().len();
        let handle_plus = r.loaded_def(Builtin::HandlePlus)?;
        let handle_plus_mask = def_shape(g, handle_plus, false).ok()?.mask().to_vec();
        let row = r.loaded_data(Builtin::Row).and_then(|d| {
            let empty = g.data(d).ctors.iter().position(|c| &*c.name == "Empty")?;
            Some((d, empty))
        });
        Some(StateFusion {
            comp: r.loaded_data(Builtin::Comp)?,
            no_op: r.loaded_data(Builtin::NoOp)?,
            comp_in: r.loaded_def(Builtin::CompIn),
            row,
            run_pure,
            run_pure_params,
            handle_plus,
            handle_plus_mask,
            if_then_else: r.loaded_def(Builtin::IfThenElse),
            elim_dec: r.loaded_def(Builtin::ElimDec),
        })
    }

    /// `foldComp`'s arguments (`ops`, `res`, `t`, the carrier, `done`,
    /// `call`, `c`, and any it's applied to after), rewritten if the fold is
    /// a state-passing handler at the empty row.
    pub fn fuse(&self, g: &Globals, args: &[&Term]) -> Result<Option<Fused>> {
        if args.len() < 7 {
            return Ok(None);
        }
        let Some(comp) = self.carrier(args[3]) else {
            return Ok(None);
        };
        let done = if comp {
            let Term::Lam(x, i, body) = args[4].strip_loc() else {
                return Ok(None);
            };
            let Some(e) = self.done_field(body) else {
                return Ok(None);
            };
            Term::Lam(x.clone(), *i, Rc::new(e.clone()))
        } else {
            args[4].clone()
        };
        // `handlePlus [5 implicit] (elim [implicit…] clause…) forward`. The
        // runtime arguments are told by erasure, not by how they're applied
        // (a term may have every application marked explicit).
        let Some((head, plus_args)) = spine_icit(args[5]) else {
            return Ok(None);
        };
        if !matches!(head, Term::Def(id) if *id == self.handle_plus)
            || plus_args.len() > self.handle_plus_mask.len()
        {
            return Ok(None);
        }
        let runtime: Vec<usize> = (0..plus_args.len())
            .filter(|i| !self.handle_plus_mask[*i])
            .collect();
        let [elim_at, forward_at] = runtime[..] else {
            return Ok(None);
        };
        if forward_at != plus_args.len() - 1 {
            return Ok(None);
        }
        let Some((elim_head, elim_args)) = spine_icit(plus_args[elim_at].0) else {
            return Ok(None);
        };
        let Term::Def(elim_id) = elim_head else {
            return Ok(None);
        };
        let Ok(elim_shape) = def_shape(g, *elim_id, false) else {
            return Ok(None);
        };
        let elim_mask = elim_shape.mask();
        if elim_args.len() > elim_mask.len() {
            return Ok(None);
        }
        let mut jumps = 0;
        let mut elim = elim_head.clone();
        for (i, (arg, icit)) in elim_args.iter().enumerate() {
            let arg = if elim_mask[i] {
                (*arg).clone()
            } else {
                let Some(clause) = self.clause(g, arg, comp, &mut jumps)? else {
                    return Ok(None);
                };
                clause
            };
            elim = Term::app_icit(elim, arg, *icit);
        }
        if jumps == 0 {
            return Ok(None);
        }
        let mut call = head.clone();
        for (i, (arg, icit)) in plus_args.iter().enumerate() {
            let arg = if i == elim_at {
                elim.clone()
            } else {
                (*arg).clone()
            };
            call = Term::app_icit(call, arg, *icit);
        }
        Ok(Some(Fused {
            comp,
            done,
            call,
            jumps,
        }))
    }

    /// Whether the carrier is a state's function at the empty row: `Some
    /// (true)` for `Comp NoOp NoRes (S -> R)`, `Some(false)` for `CompIn
    /// Empty (S -> R)` or, once specialisation has reduced that, `S -> R`.
    fn carrier(&self, carrier: &Term) -> Option<bool> {
        let (head, args) = carrier.spine();
        let (comp, t) = match head.strip_loc() {
            Term::Data(d, params) if *d == self.comp && args.is_empty() && params.len() == 3 => {
                if !matches!(params[0].strip_loc(), Term::Data(n, a) if *n == self.no_op && a.is_empty())
                {
                    return None;
                }
                (true, &*params[2])
            }
            Term::Def(id) if Some(*id) == self.comp_in && args.len() == 2 => {
                let (row, empty) = self.row?;
                if !matches!(args[0].strip_loc(), Term::Ctor(d, c, _) if *d == row && *c == empty) {
                    return None;
                }
                (false, args[1])
            }
            // `CompIn Empty (S -> R)` with the `CompIn` already reduced away,
            // as the empty-row specialisation does: a plain type can be a
            // fold's carrier only that way.
            Term::Pi(..) if args.is_empty() => (false, carrier),
            _ => return None,
        };
        matches!(strip(t), Term::Pi(..)).then_some(comp)
    }

    /// `e`, if `term` is `Done e`.
    fn done_field<'t>(&self, term: &'t Term) -> Option<&'t Term> {
        match strip(term) {
            Term::Ctor(d, 0, fields) if *d == self.comp && fields.len() == 1 => Some(&fields[0]),
            _ => None,
        }
    }

    /// Operation clause `x => k => body` as `x => k => jump => s => body′`.
    fn clause(
        &self,
        g: &Globals,
        clause: &Term,
        comp: bool,
        jumps: &mut usize,
    ) -> Result<Option<Term>> {
        let Term::Lam(x, xi, inner) = strip(clause) else {
            return Ok(None);
        };
        let Term::Lam(k, ki, body) = strip(inner) else {
            return Ok(None);
        };
        // The state's function, under `x` and `k`.
        let f = if comp {
            match self.done_field(body) {
                Some(f) => f,
                None => return Ok(None),
            }
        } else {
            &**body
        };
        // Its body under `x`, `k`, `jump` and `s`: `jump` is a new binder
        // between `k` and `s`.
        let (s, body) = match strip(f) {
            Term::Lam(s, _, b) => (s.clone(), b.shift(g, 1, 1)?),
            other => ("s".into(), Term::app(other.shift(g, 2, 0)?, Term::Var(0))),
        };
        let body = self.tail(g, &body, 0, jumps)?;
        let lam = |name, icit, body| Term::Lam(name, icit, Rc::new(body));
        Ok(Some(lam(
            x.clone(),
            *xi,
            lam(
                k.clone(),
                *ki,
                lam("jump".into(), Icit::Explicit, lam(s, Icit::Explicit, body)),
            ),
        )))
    }

    /// `term`, under `depth` more binders than the clause's body (where `s`
    /// is 0, `jump` 1 and `k` 2), with its tail resumptions made jumps.
    fn tail(&self, g: &Globals, term: &Term, depth: usize, jumps: &mut usize) -> Result<Term> {
        if depth > MAX_DEPTH {
            return Ok(term.clone());
        }
        let jump =
            |v: &Term, s: &Term| Term::app(Term::app(Term::Var(1 + depth), v.clone()), s.clone());
        match term {
            Term::Loc(span, inner) => {
                return Ok(Term::Loc(
                    *span,
                    Rc::new(self.tail(g, inner, depth, jumps)?),
                ));
            }
            Term::Ann(inner, _) => return self.tail(g, inner, depth, jumps),
            // `k v s′`.
            Term::App(f, s, _) => {
                if let Some(v) = self.resume(f, depth) {
                    *jumps += 1;
                    return Ok(jump(v, s));
                }
            }
            _ => {}
        }
        // `let r := k v; r s′`, or the same as an applied lambda.
        let bound = match term {
            Term::Let(_, _, value, body, false) => Some((&**value, &**body)),
            Term::App(f, value, _) => match strip(f) {
                Term::Lam(_, _, body) => Some((&**value, &**body)),
                _ => None,
            },
            _ => None,
        };
        if let Some((value, body)) = bound {
            if let Some(v) = self.resume(value, depth)
                && let Term::App(r, s, _) = strip(body)
                && matches!(strip(r), Term::Var(0))
                && !s.mentions(0)
            {
                *jumps += 1;
                // `s` is under the `let`'s binder, which it doesn't use.
                return Ok(jump(v, &s.instantiate_var(g, 0)?));
            }
            let body = self.tail(g, body, depth + 1, jumps)?;
            return Ok(match term {
                Term::Let(x, ty, value, _, skip) => {
                    Term::Let(x.clone(), ty.clone(), value.clone(), Rc::new(body), *skip)
                }
                Term::App(f, value, icit) => {
                    let Term::Lam(x, li, _) = strip(f) else {
                        unreachable!("matched above")
                    };
                    Term::App(
                        Rc::new(Term::Lam(x.clone(), *li, Rc::new(body))),
                        value.clone(),
                        *icit,
                    )
                }
                _ => unreachable!("matched above"),
            });
        }
        if let Term::Let(x, ty, value, body, true) = term {
            let body = self.tail(g, body, depth + 1, jumps)?;
            return Ok(Term::Let(
                x.clone(),
                ty.clone(),
                value.clone(),
                Rc::new(body),
                true,
            ));
        }
        // `Bool.ifThenElse [a] c (_ => t) (_ => e)` and `Decidable.elim [p]
        // [a] d (h => t) (r => e)`: both branches. Each gives its branch's
        // result as its own, in tail position (`Bool.ifThenElse` is lowered
        // to a test; `Decidable.elim`'s cases are `yes h` and `no r`).
        if let Some((Term::Def(id), args)) = spine_icit(term)
            && let Some(at) = self.branches(*id, args.len())
            && let (Term::Lam(xt, it, t), Term::Lam(xe, ie, e)) =
                (strip(args[at].0), strip(args[at + 1].0))
        {
            let t = self.tail(g, t, depth + 1, jumps)?;
            let e = self.tail(g, e, depth + 1, jumps)?;
            let mut out = Term::Def(*id);
            for (i, (arg, icit)) in args.iter().enumerate() {
                let arg = if i == at {
                    Term::Lam(xt.clone(), *it, Rc::new(t.clone()))
                } else if i == at + 1 {
                    Term::Lam(xe.clone(), *ie, Rc::new(e.clone()))
                } else {
                    (*arg).clone()
                };
                out = Term::app_icit(out, arg, *icit);
            }
            return Ok(out);
        }
        Ok(term.clone())
    }

    /// Where the two branches are among the arguments of `id` applied to
    /// `n` arguments, if it's a conditional whose result is a branch's.
    fn branches(&self, id: DefId, n: usize) -> Option<usize> {
        if Some(id) == self.if_then_else && n == 4 {
            Some(2)
        } else if Some(id) == self.elim_dec && n == 5 {
            Some(3)
        } else {
            None
        }
    }

    /// `v`, if `term` is `k`'s state function for `v`: `k v` (an empty-row
    /// variant, where `k` gives the function), or `runPure (k v)` (the
    /// closed empty row, where `k` gives `Done` of it).
    fn resume<'t>(&self, term: &'t Term, depth: usize) -> Option<&'t Term> {
        let k = 2 + depth;
        let call = |t: &'t Term| match strip(t) {
            Term::App(f, v, _) if matches!(strip(f), Term::Var(i) if *i == k) => Some(&**v),
            _ => None,
        };
        if let Some(v) = call(term) {
            return Some(v);
        }
        let (head, args) = term.spine();
        match head {
            Term::Def(id) if *id == self.run_pure && args.len() == self.run_pure_params => {
                call(args[args.len() - 1])
            }
            _ => None,
        }
    }
}

/// Locations and annotations taken off.
fn strip(term: &Term) -> &Term {
    let mut term = term;
    while let Term::Loc(_, t) | Term::Ann(t, _) = term {
        term = t;
    }
    term
}

/// `f a b c` as `f` and its arguments with how each is applied, looking
/// through locations; `None` if it isn't an application.
fn spine_icit(term: &Term) -> Option<(&Term, Vec<(&Term, Icit)>)> {
    let mut args = Vec::new();
    let mut head = strip(term);
    while let Term::App(f, a, icit) = head {
        args.push((a.as_ref(), *icit));
        head = strip(f);
    }
    if args.is_empty() {
        return None;
    }
    args.reverse();
    Some((head, args))
}
