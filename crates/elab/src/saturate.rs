//! Partial recursive calls, made whole for the termination checker.
//!
//! The kernel's termination checker needs every occurrence of a member of
//! the group being defined applied to all its parameters (its entry arity),
//! so each call says what every parameter is given. A member applied to some
//! but not all of them, `f a b` where `f` takes four, is rewritten to the
//! lambda `x y => f a b x y` before the group goes to the kernel. Each call
//! made through that lambda passes the same `a` and `b`, and the parameters
//! it takes stand for arguments the checker knows nothing about. So the
//! group is accepted only if the arguments given include one that gets
//! smaller; otherwise the kernel refuses it, and [`explain`] says why.
//!
//! A member given no arguments at all is left alone: nothing about its
//! arguments is known there, and the kernel's own error for it says so.

use std::rc::Rc;

use stitchwort_core::{DefId, Globals, Icit, Name, Term};
use stitchwort_syntax::{Diagnostic, Span};

type Result<T> = std::result::Result<T, Diagnostic>;

/// A group's members, each with its body.
type Members = Vec<(DefId, Term)>;

/// A partial occurrence that was made whole.
pub struct Expanded {
    /// The innermost location around it: where the kernel reports its call.
    span: Option<Span>,
    name: String,
    /// The explicit arguments it was given, and the explicit ones it takes.
    given: usize,
    wanted: usize,
}

/// `members` with every partial occurrence of a member applied to all its
/// parameters, and what was rewritten. Unchanged bodies are returned as
/// they were.
pub fn saturate(g: &Globals, members: &[(DefId, Term)]) -> Result<(Members, Vec<Expanded>)> {
    let params: Vec<(DefId, Vec<(Name, Icit)>)> = members
        .iter()
        .map(|(id, body)| (*id, entry_params(body)))
        .collect();
    let mut saturator = Saturator {
        g,
        params: &params,
        span: None,
        expanded: Vec::new(),
    };
    let mut out = Vec::with_capacity(members.len());
    for (id, body) in members {
        let body = Rc::new(body.clone());
        let new = saturator.expand(&body)?.unwrap_or(body);
        out.push((*id, Rc::unwrap_or_clone(new)));
    }
    Ok((out, saturator.expanded))
}

/// Adds to a termination error a note for each call it points at that was
/// a partial occurrence made whole.
pub fn explain(mut diagnostic: Diagnostic, expanded: &[Expanded]) -> Diagnostic {
    if diagnostic.code != "E-TERMINATION" {
        return diagnostic;
    }
    for occurrence in expanded {
        let Some(span) = occurrence.span else {
            continue;
        };
        if !diagnostic.labels.iter().any(|l| l.span == span) {
            continue;
        }
        let Expanded {
            name,
            given,
            wanted,
            ..
        } = occurrence;
        let note = format!(
            "`{name}` is given {given} of its {wanted} arguments here; the rest are whatever \
             it's applied to later, which isn't known to be smaller, so an argument that gets \
             smaller must be among the ones given"
        );
        if !diagnostic.notes.contains(&note) {
            diagnostic.notes.insert(0, note);
        }
    }
    diagnostic
}

/// The leading lambdas of a definition's body: its parameters, as the
/// kernel counts them (`Term::count_lams`).
fn entry_params(body: &Term) -> Vec<(Name, Icit)> {
    let mut params = Vec::new();
    let mut term = body.strip_loc();
    while let Term::Lam(x, icit, inner) = term {
        params.push((x.clone(), *icit));
        term = inner.strip_loc();
    }
    params
}

struct Saturator<'a> {
    g: &'a Globals,
    /// Each member's parameters.
    params: &'a [(DefId, Vec<(Name, Icit)>)],
    /// The innermost location around the term being rewritten.
    span: Option<Span>,
    expanded: Vec<Expanded>,
}

impl Saturator<'_> {
    fn member(&self, id: DefId) -> Option<&[(Name, Icit)]> {
        self.params
            .iter()
            .find(|(member, _)| *member == id)
            .map(|(_, params)| &params[..])
    }

    /// `term` rewritten, or `None` if nothing in it changes.
    fn expand(&mut self, term: &Rc<Term>) -> Result<Option<Rc<Term>>> {
        self.g.budget.nesting("elaborator")?;
        Ok(match &**term {
            Term::Loc(span, inner) => {
                let saved = self.span.replace(*span);
                let result = self.expand(inner);
                self.span = saved;
                result?.map(|inner| Rc::new(Term::Loc(*span, inner)))
            }
            Term::App(..) => {
                let (head, args) = spine(term);
                if let Term::Def(id) = head
                    && let Some(params) = self.member(*id)
                    && args.len() < params.len()
                {
                    let params = params.to_vec();
                    Some(Rc::new(self.whole(*id, &params, &args)?))
                } else {
                    self.spine_args(term)?
                }
            }
            Term::Var(_)
            | Term::Def(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => None,
            Term::Data(d, args) => self.all(args)?.map(|args| Rc::new(Term::Data(*d, args))),
            Term::Ctor(d, c, args) => self
                .all(args)?
                .map(|args| Rc::new(Term::Ctor(*d, *c, args))),
            Term::Quot(form, args, erased) => self
                .all(args)?
                .map(|args| Rc::new(Term::Quot(*form, args, *erased))),
            Term::Pi(x, icit, dom, cod) => self
                .pair(dom, cod)?
                .map(|(dom, cod)| Rc::new(Term::Pi(x.clone(), *icit, dom, cod))),
            Term::Lam(x, icit, body) => self
                .expand(body)?
                .map(|body| Rc::new(Term::Lam(x.clone(), *icit, body))),
            Term::Ann(e, t) => self.pair(e, t)?.map(|(e, t)| Rc::new(Term::Ann(e, t))),
            Term::Let(x, ty, value, body, erased) => {
                let parts = [ty.clone(), value.clone(), body.clone()];
                self.all(&parts)?.map(|parts| {
                    let [ty, value, body]: [Rc<Term>; 3] = parts.try_into().expect("three parts");
                    Rc::new(Term::Let(x.clone(), ty, value, body, *erased))
                })
            }
            Term::Case(ix, d, branches) => {
                let mut changed = false;
                let mut new = Vec::with_capacity(branches.len());
                for branch in branches.iter() {
                    let body = match &branch.body {
                        Some(body) => match self.expand(body)? {
                            Some(body) => {
                                changed = true;
                                Some(body)
                            }
                            None => Some(body.clone()),
                        },
                        None => None,
                    };
                    new.push(stitchwort_core::term::Branch {
                        names: branch.names.clone(),
                        body,
                    });
                }
                changed.then(|| Rc::new(Term::Case(*ix, *d, new.into())))
            }
            Term::NumCase(ix, arms, default) => {
                let mut changed = false;
                let mut new = Vec::with_capacity(arms.len());
                for arm in arms.iter() {
                    let body = match self.expand(&arm.body)? {
                        Some(body) => {
                            changed = true;
                            body
                        }
                        None => arm.body.clone(),
                    };
                    new.push(stitchwort_core::term::NumArm {
                        value: arm.value.clone(),
                        body,
                    });
                }
                let default = match self.expand(default)? {
                    Some(default) => {
                        changed = true;
                        default
                    }
                    None => default.clone(),
                };
                changed.then(|| Rc::new(Term::NumCase(*ix, new.into(), default)))
            }
            Term::Eq(ty, a, b) => {
                let ty_new = match ty {
                    Some(ty) => self.expand(ty)?,
                    None => None,
                };
                let pair = self.pair(a, b)?;
                if ty_new.is_none() && pair.is_none() {
                    None
                } else {
                    let ty = ty_new.or_else(|| ty.clone());
                    let (a, b) = pair.unwrap_or_else(|| (a.clone(), b.clone()));
                    Some(Rc::new(Term::Eq(ty, a, b)))
                }
            }
            Term::J(m, b, p) => {
                let parts = [m.clone(), b.clone(), p.clone()];
                self.all(&parts)?.map(|parts| {
                    let [m, b, p]: [Rc<Term>; 3] = parts.try_into().expect("three parts");
                    Rc::new(Term::J(m, b, p))
                })
            }
        })
    }

    /// The spine `term` with its arguments rewritten, keeping its
    /// applications and locations. Its head is rewritten too, unless it's a
    /// member, whose occurrence the whole spine is.
    fn spine_args(&mut self, term: &Rc<Term>) -> Result<Option<Rc<Term>>> {
        match &**term {
            Term::Loc(span, inner) => Ok(self
                .spine_args(inner)?
                .map(|inner| Rc::new(Term::Loc(*span, inner)))),
            Term::App(f, a, icit) => {
                let f_new = self.spine_args(f)?;
                let a_new = self.expand(a)?;
                if f_new.is_none() && a_new.is_none() {
                    return Ok(None);
                }
                Ok(Some(Rc::new(Term::App(
                    f_new.unwrap_or_else(|| f.clone()),
                    a_new.unwrap_or_else(|| a.clone()),
                    *icit,
                ))))
            }
            Term::Def(id) if self.member(*id).is_some() => Ok(None),
            _ => self.expand(term),
        }
    }

    /// Member `id`, given the first `args` of its `params`, applied to all
    /// of them: `x y => id args x y`.
    fn whole(
        &mut self,
        id: DefId,
        params: &[(Name, Icit)],
        args: &[(&Rc<Term>, Icit)],
    ) -> Result<Term> {
        let missing = &params[args.len()..];
        let shift = missing.len();
        let mut call = Term::Def(id);
        for (arg, icit) in args {
            let arg = self.expand(arg)?.unwrap_or_else(|| (*arg).clone());
            call = Term::app_icit(call, arg.shift(self.g, shift, 0)?, *icit);
        }
        for (k, (_, icit)) in missing.iter().enumerate() {
            call = Term::app_icit(call, Term::Var(shift - 1 - k), *icit);
        }
        for (x, icit) in missing.iter().rev() {
            call = Term::Lam(x.clone(), *icit, Rc::new(call));
        }
        let explicit = |params: &[(Name, Icit)]| {
            params
                .iter()
                .filter(|(_, icit)| *icit == Icit::Explicit)
                .count()
        };
        self.expanded.push(Expanded {
            span: self.span,
            name: self.g.def(id).name.to_string(),
            given: explicit(&params[..args.len()]),
            wanted: explicit(params),
        });
        Ok(call)
    }

    /// `terms` rewritten, if any of them changes.
    fn all(&mut self, terms: &[Rc<Term>]) -> Result<Option<Vec<Rc<Term>>>> {
        let mut changed = false;
        let mut new = Vec::with_capacity(terms.len());
        for term in terms {
            match self.expand(term)? {
                Some(term) => {
                    changed = true;
                    new.push(term);
                }
                None => new.push(term.clone()),
            }
        }
        Ok(changed.then_some(new))
    }

    fn pair(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Result<Option<(Rc<Term>, Rc<Term>)>> {
        let a_new = self.expand(a)?;
        let b_new = self.expand(b)?;
        if a_new.is_none() && b_new.is_none() {
            return Ok(None);
        }
        Ok(Some((
            a_new.unwrap_or_else(|| a.clone()),
            b_new.unwrap_or_else(|| b.clone()),
        )))
    }
}

/// Splits `f a b` into `f` and its arguments with their implicitness,
/// looking through locations.
fn spine(term: &Rc<Term>) -> (&Term, Vec<(&Rc<Term>, Icit)>) {
    let mut args = Vec::new();
    let mut head: &Term = term.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push((a, *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}
