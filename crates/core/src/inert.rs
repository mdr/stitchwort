//! Inert proof parameters (D2349; docs/proposals/proof-irrelevance.md §7.1,
//! §7.3).
//!
//! A definition's parameter below its arity is *inert* if its declared type
//! is a proposition and the checked body never computes with it: every
//! occurrence is
//!
//! 1. inside an argument at an inert position of an enclosing call of a
//!    definition (however deeply: nothing inside such an argument is looked
//!    at), or
//! 2. inside a part of the term that values don't keep (a `let`'s type, an
//!    annotation's type), or
//! 3. the scrutinee of a `case` with no possible branch (`Void.absurd`),
//!    which never computes whatever its scrutinee is (D2353).
//!
//! Anything else clears the mark: taking it apart, `J` on it, a quotient
//! form, applying it, returning it, storing it in a constructor field
//! (D2354), passing it to a local function or to a definition's position
//! that isn't inert, binding it with `let`, or mentioning it in a type that
//! values keep. Comparison skips inert arguments, in calls and in the
//! glued-call shortcut alike; that is safe because changing an inert
//! argument changes a call's unfolding only inside other inert arguments
//! (§7.10).
//!
//! Over a recursion group the marks are a greatest fixed point: every
//! candidate starts marked, and a round clears each one with an occurrence
//! the clauses don't allow, reading the group's marks as they stand, until
//! a round clears nothing. So a proof passed only to itself, or around a
//! cycle of members, stays inert.
//!
//! The reference evaluator checks every mark independently
//! (`reference::validate_inert`).

use std::rc::Rc;

use stitchwort_syntax::Diagnostic;

use crate::check::{Ctx, sort_of};
use crate::ev::Ev;
use crate::term::{DefId, Sort, Term};
use crate::value::{Value, force};

type Result<T> = std::result::Result<T, Diagnostic>;

/// Why a candidate isn't inert: the first offending occurrence's place.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Why {
    /// The scrutinee of a `case` with a possible branch.
    TakenApart,
    /// The proof of a `J`.
    JProof,
    /// An argument of a quotient form.
    Quotient,
    /// The head of an application.
    Applied,
    /// The definition's result, or part of it.
    Returned,
    /// A constructor's field.
    Field,
    /// An argument of something other than a definition: a local function,
    /// a lambda.
    LocalFunction,
    /// The argument at position `1` of definition `0`, which isn't inert.
    NotInert(DefId, usize),
    /// A `let`'s value.
    LetValue,
    /// A type that values keep: a function type, a data type's argument, an
    /// equation, `J`'s motive.
    Type,
}

/// A candidate the analysis cleared, and why.
#[derive(Clone, Debug)]
pub struct Cleared {
    pub def: DefId,
    pub param: usize,
    pub why: Why,
}

/// The candidates of definition `id`, with its body installed: whether each
/// parameter below its arity has a type in `Prop`. Not `erase::of_def`,
/// which also marks types.
pub fn candidates(g: &Ev, id: DefId) -> Result<Vec<bool>> {
    let def = g.def(id);
    let _set = g.machine.transparent.set(def.transparent.clone());
    // Glued, as when the body is checked, so that a parameter's type
    // mentioning an expensive closed value (`h: cost = cost`) doesn't
    // compute it; and the codomain after the last parameter, which no
    // candidate needs, isn't evaluated at all.
    let was = g.machine.glue.replace(true);
    let result = (|| {
        let mut cx = Ctx::new(g, def.span);
        let mut ty = force(g, crate::check::def_type(g, def)?)?;
        let mut out = Vec::with_capacity(def.arity);
        for k in 0..def.arity {
            let Value::Pi(x, _, dom, cod) = &ty else {
                // The body has more parameters than the type shows without
                // unfolding: a mark there could only be wrong, so none.
                out.resize(def.arity, false);
                break;
            };
            out.push(sort_of(&mut cx, dom)? == Sort::Prop);
            if k + 1 < def.arity {
                let next = cod.apply(g, Value::var(cx.level()))?;
                cx.bind(x.clone(), (**dom).clone());
                ty = force(g, next)?;
            }
        }
        Ok(out)
    })();
    g.machine.glue.set(was);
    result
}

/// The inert marks of the members of a group, whose bodies are installed,
/// and every candidate cleared, with why. An error (the candidates ran out
/// of budget) means the group gets no marks.
pub fn analyse(g: &Ev, ids: &[DefId]) -> Result<(Vec<Vec<bool>>, Vec<Cleared>)> {
    let mut marks: Vec<Vec<bool>> = Vec::with_capacity(ids.len());
    for id in ids {
        marks.push(match g.def(*id).body {
            Some(_) => candidates(g, *id)?,
            None => Vec::new(),
        });
    }
    let mut cleared = Vec::new();
    loop {
        let mut changed = false;
        for (k, id) in ids.iter().enumerate() {
            if !marks[k].iter().any(|m| *m) {
                continue;
            }
            let def = g.def(*id);
            let Some(body) = &def.body else { continue };
            let inert = |f: DefId, i: usize| -> bool {
                match ids.iter().position(|m| *m == f) {
                    Some(j) => marks[j].get(i).copied().unwrap_or(false),
                    None => g.def(f).is_inert(i),
                }
            };
            let found = offences(g, body.peel_lams(def.arity), def.arity, &marks[k], &inert);
            for (param, why) in found {
                if marks[k][param] {
                    marks[k][param] = false;
                    changed = true;
                    cleared.push(Cleared {
                        def: *id,
                        param,
                        why,
                    });
                }
            }
        }
        if !changed {
            return Ok((marks, cleared));
        }
    }
}

/// The marked parameters of a body with an occurrence the clauses don't
/// allow, each with the first such occurrence's place. `tree` is the body
/// under its `arity` lambdas; `inert` says whether a definition's parameter
/// is inert.
fn offences(
    g: &Ev,
    tree: &Term,
    arity: usize,
    marked: &[bool],
    inert: &dyn Fn(DefId, usize) -> bool,
) -> Vec<(usize, Why)> {
    // The parameter a variable at `depth` binders below the tree's top is.
    let param = |ix: usize, depth: usize| -> Option<usize> {
        let k = ix.checked_sub(depth)?;
        (k < arity).then(|| arity - 1 - k)
    };
    let mut found: Vec<(usize, Why)> = Vec::new();
    let offend = |found: &mut Vec<(usize, Why)>, ix: usize, depth: usize, why: &Why| {
        if let Some(i) = param(ix, depth)
            && marked[i]
            && !found.iter().any(|(j, _)| *j == i)
        {
            found.push((i, why.clone()));
        }
    };
    // Terms still to walk, with their depth and the place they're in. A
    // work list, not recursion: bodies can nest deeply (long literals).
    let mut work: Vec<(&Term, usize, Why)> = vec![(tree, 0, Why::Returned)];
    while let Some((term, depth, why)) = work.pop() {
        match term {
            Term::Loc(_, t) => work.push((t, depth, why)),
            Term::Var(ix) => offend(&mut found, *ix, depth, &why),
            Term::App(..) => {
                let mut args = Vec::new();
                let mut head = term;
                while let Term::App(f, a, _) = head.strip_loc() {
                    args.push(&**a);
                    head = f;
                }
                args.reverse();
                match head.strip_loc() {
                    Term::Def(f) => {
                        for (k, arg) in args.into_iter().enumerate() {
                            if !inert(*f, k) {
                                work.push((arg, depth, Why::NotInert(*f, k)));
                            }
                        }
                    }
                    head => {
                        work.push((head, depth, Why::Applied));
                        for arg in args {
                            work.push((arg, depth, Why::LocalFunction));
                        }
                    }
                }
            }
            Term::Lam(_, _, b) => work.push((b, depth + 1, why)),
            Term::Pi(_, _, a, b) => {
                work.push((a, depth, Why::Type));
                work.push((b, depth + 1, Why::Type));
            }
            Term::Ann(t, _) => work.push((t, depth, why)),
            Term::Let(_, _, v, b, _) => {
                work.push((v, depth, Why::LetValue));
                work.push((b, depth + 1, why));
            }
            Term::Data(_, args) => work.extend(args.iter().map(|a| (&**a, depth, Why::Type))),
            Term::Ctor(_, _, args) => work.extend(args.iter().map(|a| (&**a, depth, Why::Field))),
            Term::Eq(ty, a, b) => {
                work.extend(ty.iter().map(|t| (&**t, depth, Why::Type)));
                work.push((a, depth, Why::Type));
                work.push((b, depth, Why::Type));
            }
            Term::J(m, b, p) => {
                work.push((m, depth, Why::Type));
                work.push((b, depth, why));
                work.push((p, depth, Why::JProof));
            }
            Term::Quot(_, args, _) => {
                work.extend(args.iter().map(|a| (&**a, depth, Why::Quotient)))
            }
            Term::Case(ix, d, branches) => {
                if branches.iter().any(|b| b.body.is_some()) {
                    offend(&mut found, *ix, depth, &Why::TakenApart);
                }
                let ctors = &g.data(*d).ctors;
                for (c, branch) in branches.iter().enumerate() {
                    if let Some(body) = &branch.body {
                        work.push((body, depth + ctors[c].fields.len(), why.clone()));
                    }
                }
            }
            Term::NumCase(ix, arms, default) => {
                offend(&mut found, *ix, depth, &Why::TakenApart);
                work.extend(arms.iter().map(|a| (&*a.body, depth, why.clone())));
                work.push((default, depth, why));
            }
            Term::Def(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => {}
        }
    }
    found
}

/// The marks [`analyse`] gives a group, ready to install: none at all if
/// it failed.
pub fn group_marks(g: &Ev, ids: &[DefId]) -> Vec<Rc<[bool]>> {
    match analyse(g, ids) {
        Ok((marks, _)) => marks.into_iter().map(Rc::from).collect(),
        Err(_) => ids.iter().map(|_| Rc::from([])).collect(),
    }
}
