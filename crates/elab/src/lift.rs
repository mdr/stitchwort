//! Lifting: turning a piece of a definition into a generated top-level
//! definition, a *helper* (docs/proposals/syntax-conveniences.md §2).
//!
//! A helper is elaborated where it's written, in the owner's context, and
//! recorded as a [`Draft`]. Where it's used, the owner's term has a frozen
//! metavariable (`Globals::meta_frozen`) applied to the variables in scope:
//! unification treats it as rigid, so nothing is learnt from it before the
//! helper exists. Once the owner's body (or signature) is elaborated, the
//! drafts are *resolved* in the order they were made, which puts a nested
//! helper before the one containing it ([`Elaborator::lift`]):
//!
//! 1. solved metavariables are substituted in, and variables a case split
//!    has replaced by a constructor are replaced by it;
//! 2. the captures are computed: the variables the helper uses, closed
//!    under "the variables their types mention" (§2.1, rules 1 and 2; a
//!    nested helper's captures are seen through its call, rule 3);
//! 3. the captures are ordered by their types' dependencies, keeping
//!    context order where possible, and the helper's type is the telescope
//!    of them followed by the result type;
//! 4. the helper is declared, and the frozen metavariable is solved with the
//!    call `owner.%matchN c₁ … cₖ`, every capture passed explicitly;
//! 5. the helper is admitted on its own at once if it refers to nothing
//!    pending, or else joins the owner's group, admitted with it (§2.2).

use std::collections::{BTreeSet, HashSet};
use std::rc::Rc;

use stitchwort_core::check as kernel;
use stitchwort_core::globals::State;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{Head, eval, quote};
use stitchwort_core::{DefId, Globals, Icit, Name, Term, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, Result};

/// A helper elaborated in its owner's context, not yet a definition.
pub(crate) struct Draft {
    /// The frozen metavariable standing for the call.
    pub meta: usize,
    /// The `match`, for error messages.
    pub span: Span,
    /// The context the helper's body was elaborated in. Its first `base`
    /// variables are the context the `match` is in; any after them were
    /// added by the `match` itself (a generalised scrutinee and the like).
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    pub names: Vec<Name>,
    pub base: usize,
    /// For each variable at level `base + i`, what the call passes for it: a
    /// term in the first `base` variables.
    pub extra: Vec<Term>,
    /// The body (a case tree) and its type, in the whole context.
    pub body: Term,
    pub goal: Term,
}

/// Records a helper whose body `body` of type `goal` was elaborated in `cx`,
/// and gives the term standing for its call, in the context's first `base`
/// variables. `extra` says what's passed for the variables after those.
pub(crate) fn draft(
    cx: &Ctx,
    base: usize,
    extra: Vec<Term>,
    body: Term,
    goal: &Value,
    span: Span,
) -> Result<Term> {
    let g = cx.g();
    let goal = cx.quote(goal)?;
    let meta = g.new_meta(span);
    g.freeze_meta(meta);
    let mut call = Term::Meta(meta);
    for level in spine(&cx.env[..base]) {
        call = Term::app(call, Term::Var(base - 1 - level));
    }
    cx.e.drafts.borrow_mut().push(Draft {
        meta,
        span,
        env: cx.env.clone(),
        types: cx.types.clone(),
        names: cx.names.clone(),
        base,
        extra,
        body,
        goal,
    });
    Ok(call)
}

/// The variables a metavariable created in `env` is applied to: those a
/// case split hasn't replaced (as `Ctx::fresh_meta`).
fn spine(env: &[Value]) -> Vec<usize> {
    (0..env.len()).filter(|&l| is_var(&env[l], l)).collect()
}

fn is_var(value: &Value, level: usize) -> bool {
    matches!(value, Value::Neutral(Head::Var(l), s) if *l == level && s.is_empty())
}

/// Rebuilds `term` (in a context of `depth` variables) with each free
/// variable, by level, replaced by `f(level)`: a term in the target context.
/// A case split's variable must be replaced by a variable.
fn replace(
    g: &Globals,
    term: &Term,
    depth: usize,
    f: &dyn Fn(usize) -> Result<Term>,
) -> Result<Term> {
    go_replace(g, term, depth, 0, f, &|_, _| None)
}

/// [`replace`], where `hook(t, binders)` may replace a whole sub-term `t` first.
pub(crate) fn replace_with(
    g: &Globals,
    term: &Term,
    depth: usize,
    f: &dyn Fn(usize) -> Result<Term>,
    hook: &dyn Fn(&Term, usize) -> Option<Term>,
) -> Result<Term> {
    go_replace(g, term, depth, 0, f, hook)
}

fn go_replace(
    g: &Globals,
    term: &Term,
    depth: usize,
    under: usize,
    f: &dyn Fn(usize) -> Result<Term>,
    hook: &dyn Fn(&Term, usize) -> Option<Term>,
) -> Result<Term> {
    g.budget.nesting(crate::check::PASS)?;
    if let Some(t) = hook(term, under) {
        return Ok(t);
    }
    let go = |t: &Rc<Term>, under| go_replace(g, t, depth, under, f, hook).map(Rc::new);
    let var = |ix: usize| -> Result<Term> {
        if ix < under {
            return Ok(Term::Var(ix));
        }
        Ok(f(depth - 1 - (ix - under))?.shift(g, under, 0)?)
    };
    let split = |ix: usize| -> Result<usize> {
        match var(ix)? {
            Term::Var(new) => Ok(new),
            _ => Err(Diagnostic::error(
                "E-MALFORMED",
                "internal error: lifting replaced a case split's variable",
            )),
        }
    };
    Ok(match term {
        Term::Var(ix) => var(*ix)?,
        Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => term.clone(),
        Term::Data(d, args) => Term::Data(
            *d,
            args.iter().map(|a| go(a, under)).collect::<Result<_>>()?,
        ),
        Term::Ctor(d, c, args) => Term::Ctor(
            *d,
            *c,
            args.iter().map(|a| go(a, under)).collect::<Result<_>>()?,
        ),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a, under)?, go(b, under + 1)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b, under + 1)?),
        Term::App(h, a, i) => Term::App(go(h, under)?, go(a, under)?, *i),
        Term::Ann(e, t) => Term::Ann(go(e, under)?, go(t, under)?),
        Term::Case(ix, d, branches) => Term::Case(
            split(*ix)?,
            *d,
            branches
                .iter()
                .map(|b| {
                    Ok(Branch {
                        names: b.names.clone(),
                        body: go(&b.body, under + b.names.len())?,
                    })
                })
                .collect::<Result<_>>()?,
        ),
        Term::NumCase(ix, arms, default) => Term::NumCase(
            split(*ix)?,
            arms.iter()
                .map(|a| {
                    Ok(NumArm {
                        value: a.value.clone(),
                        body: go(&a.body, under)?,
                    })
                })
                .collect::<Result<_>>()?,
            go(default, under)?,
        ),
        Term::Eq(t, a, b) => Term::Eq(
            t.as_ref().map(|t| go(t, under)).transpose()?,
            go(a, under)?,
            go(b, under)?,
        ),
        Term::J(m, b, p) => Term::J(go(m, under)?, go(b, under)?, go(p, under)?),
        Term::Loc(span, t) => Term::Loc(*span, go(t, under)?),
    })
}

/// The levels of the free variables of `term`, in a context of `depth`
/// variables (a case split's variable counts).
fn free_levels(term: &Term, depth: usize, out: &mut BTreeSet<usize>) {
    for (t, under) in term.subterms() {
        let ix = match t {
            Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) => *ix,
            _ => continue,
        };
        if ix >= under {
            out.insert(depth - 1 - (ix - under));
        }
    }
}

/// The definitions `term` refers to.
fn defs(term: &Term) -> impl Iterator<Item = DefId> + '_ {
    term.subterms().filter_map(|(t, _)| match t {
        Term::Def(id) => Some(*id),
        _ => None,
    })
}

impl Elaborator {
    /// Resolves the drafts made while elaborating `owner` (a declaration
    /// key), in the order they were made. Each is declared, and admitted at
    /// once unless it refers to something pending and `join` allows it to
    /// join the owner's group: those are returned, with their bodies, for the
    /// caller to admit with the owner.
    pub(crate) fn lift(&mut self, owner: &str, join: bool) -> Result<Vec<(DefId, Term)>> {
        if self.drafts.borrow().is_empty() {
            return Ok(Vec::new());
        }
        self.solve_obligations()?;
        let drafts = std::mem::take(&mut *self.drafts.borrow_mut());
        // Numbered in source order within the owner (§2.4).
        let mut order: Vec<usize> = (0..drafts.len()).collect();
        order.sort_by_key(|&i| (drafts[i].span.start, std::cmp::Reverse(drafts[i].span.end)));
        let mut number = vec![0; drafts.len()];
        for (n, &i) in order.iter().enumerate() {
            number[i] = n + 1;
        }
        let mut joined: Vec<(DefId, Term)> = Vec::new();
        let mut joined_ids = HashSet::new();
        for (draft, n) in drafts.into_iter().zip(number) {
            let key = format!("{owner}.%match{n}");
            let (id, body) = self.resolve_draft(&draft, &key)?;
            let pending = defs(&body)
                .any(|d| joined_ids.contains(&d) || self.globals.def(d).state == State::Pending);
            if let Some(item) = self.module.item {
                self.module.def_items.insert(id, item);
            }
            self.lifted.push((id, draft.span));
            if join && pending {
                joined_ids.insert(id);
                joined.push((id, body));
            } else {
                kernel::define_group(&mut self.globals, &[(id, body)])
                    .map_err(|d| self.explain_lifted(d))?;
            }
        }
        Ok(joined)
    }

    /// Declares the helper for `draft`, solves its frozen metavariable with
    /// the call, and gives its id and body.
    fn resolve_draft(&mut self, draft: &Draft, key: &str) -> Result<(DefId, Term)> {
        let (ty, lam, args) = self.lifted_parts(draft)?;
        let name = crate::scope::display(key).to_string();
        // Everything in the type was elaborated and checked where it was
        // written, except what generalising a scrutinee changed: if the
        // kernel refuses it, that's why (§4.4).
        let id = kernel::declare_def(
            &mut self.globals,
            &name.into(),
            &ty,
            false,
            false,
            draft.span,
        )
        .map_err(|d| {
            if crate::undo::fatal(&d) {
                return d;
            }
            if d.message.contains("which isn't finished") {
                // Like a signature mentioning a member of its own group.
                return Diagnostic::error(
                    "E-MUTUAL-SIGNATURE",
                    "this `match`'s type refers to a definition that isn't finished",
                )
                .with_label(draft.span, "this `match`")
                .with_note(format!("the kernel's reason: {}", d.message))
                .with_note(
                    "the `match` is made into a definition whose type must only mention \
                         finished definitions; annotate it with a type that doesn't, or use a \
                         top-level helper",
                );
            }
            Diagnostic::error(
                "E-MATCH-MOTIVE",
                "this `match` can't be given a type: generalising its scrutinee makes the \
                     types it depends on ill-formed",
            )
            .with_label(draft.span, "this `match`")
            .with_note(format!("the kernel's reason: {}", d.message))
            .with_note(
                "a top-level helper with a written signature can always do what this \
                     `match` would: define one and call it",
            )
        })?;
        // The call, as a function of the metavariable's spine.
        let g = &self.globals;
        let mut call = Term::Def(id);
        for arg in args {
            call = Term::app(call, arg);
        }
        for _ in spine(&draft.env[..draft.base]) {
            call = Term::Lam("x".into(), Icit::Explicit, Rc::new(call));
        }
        g.solve_meta(draft.meta, eval(g, &[], &call)?);
        Ok((id, lam))
    }

    /// The helper's type and body, and the arguments of its call, as terms
    /// in the frozen metavariable's spine.
    pub(crate) fn lifted_parts(&self, draft: &Draft) -> Result<(Term, Term, Vec<Term>)> {
        let g = &self.globals;
        let n = draft.env.len();
        // Variables a case split replaced by a constructor are replaced by
        // it: the helper takes the constructor's fields instead.
        let unrefine = |t: &Term, depth: usize| -> Result<Term> {
            let t = self.zonk(t, depth)?;
            replace(g, &t, depth, &|l| {
                if is_var(&draft.env[l], l) {
                    Ok(Term::Var(depth - 1 - l))
                } else {
                    Ok(quote(g, depth, &draft.env[l])?)
                }
            })
        };
        let body = unrefine(&draft.body, n)?;
        let goal = unrefine(&draft.goal, n)?;
        // The captures: what the body and type use, and what their types
        // mention (§2.1).
        let mut captures = BTreeSet::new();
        free_levels(&body, n, &mut captures);
        free_levels(&goal, n, &mut captures);
        let mut types = vec![None; n];
        let mut deps: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); n];
        let mut work: Vec<usize> = captures.iter().copied().collect();
        while let Some(l) = work.pop() {
            if types[l].is_some() {
                continue;
            }
            let ty = unrefine(&quote(g, n, &draft.types[l])?, n)?;
            free_levels(&ty, n, &mut deps[l]);
            for &d in &deps[l] {
                if captures.insert(d) {
                    work.push(d);
                }
            }
            types[l] = Some(ty);
        }
        // Ordered by their types' dependencies, keeping context order where
        // the dependencies allow (§4.4).
        let mut ordered: Vec<usize> = Vec::new();
        let mut left: Vec<usize> = captures.iter().copied().collect();
        while !left.is_empty() {
            let Some(i) = left
                .iter()
                .position(|l| deps[*l].iter().all(|d| ordered.contains(d)))
            else {
                return Err(Diagnostic::error(
                    "E-MATCH-MOTIVE",
                    "this `match`'s type can't be built: the types of the variables it uses \
                     depend on each other in a cycle",
                )
                .with_label(draft.span, "this `match`")
                .with_note(
                    "write the helper as a top-level definition with its own signature instead",
                ));
            };
            ordered.push(left.remove(i));
        }
        let position = |l: usize| ordered.iter().position(|c| *c == l);
        let into = |t: &Term, depth: usize, scope: usize| {
            replace(g, t, depth, &|l| match position(l) {
                Some(p) if p < scope => Ok(Term::Var(scope - 1 - p)),
                _ => Err(Diagnostic::error(
                    "E-MALFORMED",
                    "internal error: a lifted term uses a variable it doesn't capture",
                )),
            })
        };
        let k = ordered.len();
        let mut ty = into(&goal, n, k)?;
        let mut lam = into(&body, n, k)?;
        for (p, &l) in ordered.iter().enumerate().rev() {
            let dom = into(types[l].as_ref().expect("computed above"), n, p)?;
            let x = draft.names[l].clone();
            ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(dom), Rc::new(ty));
            lam = Term::Lam(x, Icit::Explicit, Rc::new(lam));
        }
        // The call's arguments, as functions of the metavariable's spine.
        let base = draft.base;
        let spine = spine(&draft.env[..base]);
        let s = spine.len();
        let in_spine = |t: &Term| {
            let t = unrefine(t, base)?;
            replace(g, &t, base, &|l| match spine.iter().position(|v| *v == l) {
                Some(p) => Ok(Term::Var(s - 1 - p)),
                None => Err(Diagnostic::error(
                    "E-MALFORMED",
                    "internal error: a lifted call uses a variable outside its context",
                )),
            })
        };
        let args = ordered
            .iter()
            .map(|&l| {
                if l < base {
                    in_spine(&Term::Var(base - 1 - l))
                } else {
                    in_spine(&draft.extra[l - base])
                }
            })
            .collect::<Result<_>>()?;
        Ok((ty, lam, args))
    }

    /// Mentions of lifted helpers in a diagnostic name the `match` instead
    /// (§2.5): `f.%match1` is never shown.
    pub(crate) fn explain_lifted(&self, mut d: Diagnostic) -> Diagnostic {
        // Longest first, so `f.%match1` isn't found inside `f.%match10`.
        let mut lifted: Vec<(String, Span)> = self
            .lifted
            .iter()
            .map(|&(id, span)| (self.globals.def(id).name.to_string(), span))
            .collect();
        lifted.sort_by_key(|(name, _)| std::cmp::Reverse(name.len()));
        for (bare, span) in lifted {
            let mentioned = d.message.contains(&bare)
                || d.labels.iter().any(|l| l.message.contains(&bare))
                || d.notes.iter().any(|n| n.contains(&bare));
            if !mentioned {
                continue;
            }
            // Named on its own (`f.%match1` in "can't show that … terminate"),
            // it's "this `match`"; inside a printed term, `(match …)`.
            let quoted = format!("`{bare}`");
            let reword = |s: &str| {
                s.replace(&quoted, "this `match`")
                    .replace(&bare, "(match …)")
            };
            d.message = reword(&d.message);
            for l in &mut d.labels {
                l.message = reword(&l.message);
            }
            for note in &mut d.notes {
                *note = reword(note);
            }
            d = d.with_label(span, "this `match`");
        }
        d
    }
}
