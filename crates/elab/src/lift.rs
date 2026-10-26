//! Lifting: turning a piece of a definition into a generated top-level
//! definition, a *helper* (docs/proposals/syntax-conveniences.md §2).
//!
//! A helper (a lifted `match`, or a local definition) is elaborated where
//! it's written, in the owner's context, and recorded as a [`Draft`].
//! Where it's used, the owner's term has a frozen metavariable
//! (`Globals::meta_frozen`) applied to the variables in scope: unification
//! treats it as rigid, so nothing is learnt from it before the helper
//! exists. Once the owner's body (or signature) is elaborated, the drafts
//! are *resolved* together ([`Elaborator::lift`]):
//!
//! 1. solved metavariables are substituted in, and variables a case split
//!    has replaced by a constructor are replaced by it;
//! 2. the captures are computed, for all the drafts at once: the variables
//!    each helper uses, closed under "the variables their types mention"
//!    and "the captures of the helpers it calls" (§2.1, rules 1 to 3). A
//!    call of another draft is its frozen metavariable applied to the
//!    variables in scope, of which only those that helper captures count:
//!    a fixed point, since helpers may call each other;
//! 3. the captures are ordered by their types' dependencies, keeping
//!    context order where possible, and the helper's type is the telescope
//!    of them followed by the result type;
//! 4. the drafts are split into strongly connected components by which
//!    others they call, and each component, after those it calls, is
//!    declared (its frozen metavariables solved with the calls
//!    `owner.go c₁ … cₖ`, every capture passed explicitly), then admitted
//!    on its own if it refers to nothing pending, or else joins the owner's
//!    group, admitted with it (§2.2).

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::State;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{Head, eval, quote_folded};
use stitchwort_core::{DefId, Globals, Icit, Name, Term, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, LetDef, Result};

/// Where a variable comes in the order captures are taken: its place in
/// `order`, and variables not listed come after, by level.
pub(crate) fn rank(order: &[usize], level: usize) -> usize {
    order
        .iter()
        .position(|&l| l == level)
        .unwrap_or(order.len() + level)
}

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
    /// The body (a case tree, or for a local definition, its lambdas around
    /// one) and its type, in the whole context.
    pub body: Term,
    pub goal: Term,
    /// How each variable of the context was bound (`Ctx::kinds`): a local
    /// definition's captures keep their kind (§2.1).
    pub kinds: Vec<Icit>,
    /// Which variables of the context are `let`s, with their types and
    /// values (`Ctx::lets`): the helper re-creates those it uses.
    pub lets: Vec<Option<Rc<LetDef>>>,
    /// The order the captures are taken in, from where it was written
    /// (`Ctx::order`).
    pub order: Vec<usize>,
    /// For a local definition, what it is; `None` for a `match`.
    pub local: Option<LocalDraft>,
}

/// A local definition being lifted (`local.rs`).
pub(crate) struct LocalDraft {
    /// `owner.go`.
    pub key: String,
    /// `go`, as written.
    pub name: String,
    pub theorem: bool,
    /// The whole definition, from `def` to its last arm: a `match` inside is
    /// numbered within it (`owner.go.%match1`).
    pub whole: Span,
}

/// What resolving a batch gives: the helpers to admit with the owner, and
/// what each draft became.
pub(crate) type Batch = (Vec<(DefId, Term)>, Vec<Resolved>);

/// What [`Elaborator::captures`] unrefined, keeping metavariables of the
/// batch, for finding which drafts each calls: each draft's body and type,
/// and the types of the variables of its context it captures.
pub(crate) struct Unrefined {
    parts: Vec<(Term, Term)>,
    types: Vec<Vec<Option<Term>>>,
}

/// The `let`s each draft's terms are folded back to when unrefined (see
/// [`Elaborator::around`]), by the draft's frozen metavariable: how long the
/// record of solutions was when they were computed (a solution since may
/// change them), how many of the draft's context's levels they cover, and
/// the foldable `let`s among those. Kept only within one lifting (each
/// starts afresh), since a metavariable's number is reused afterwards.
pub(crate) type Arounds = HashMap<usize, (usize, usize, Vec<crate::unify::Around>)>;

/// A helper's type, body, and its call's arguments with their kinds.
type Parts = (Term, Term, Vec<(Term, Icit)>);

/// A helper once resolved: its definition and captures (levels in the
/// draft's context, in order, with their kinds).
pub(crate) struct Resolved {
    pub id: DefId,
    pub captures: Vec<(usize, Icit, Name)>,
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
    let goal = cx.quote_folded(goal)?;
    let meta = g.new_meta(span);
    g.freeze_meta(meta);
    let mut call = Term::Meta(meta);
    for level in spine(&cx.env[..base], &cx.lets) {
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
        kinds: cx.kinds.clone(),
        lets: cx.lets.clone(),
        order: cx.order.clone(),
        local: None,
    });
    Ok(call)
}

/// The variables a helper's frozen metavariable, created in `env`, is
/// applied to: those a case split hasn't replaced (as `Ctx::fresh_meta`),
/// and, unlike `fresh_meta`, the `let`s in scope (`lets`), so the call can
/// pass a `let`'s variable, sharing its value, where it passes something
/// that uses it (a generalised scrutinee). The frozen metavariable is never
/// solved by unification, which needs a spine of plain variables; its
/// solution is the call, made in [`Elaborator::resolve_batch`].
pub(crate) fn spine(env: &[Value], lets: &[Option<Rc<LetDef>>]) -> Vec<usize> {
    (0..env.len())
        .filter(|&l| is_var(&env[l], l) || lets.get(l).is_some_and(Option::is_some))
        .collect()
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
        Term::Let(x, a, v, b, e) => Term::Let(
            x.clone(),
            go(a, under)?,
            go(v, under)?,
            go(b, under + 1)?,
            *e,
        ),
        Term::Case(ix, d, branches) => Term::Case(
            split(*ix)?,
            *d,
            branches
                .iter()
                .map(|b| {
                    Ok(Branch {
                        names: b.names.clone(),
                        body: b
                            .body
                            .as_ref()
                            .map(|body| go(body, under + b.names.len()))
                            .transpose()?,
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
        Term::Quot(form, args, e) => Term::Quot(
            *form,
            args.iter().map(|a| go(a, under)).collect::<Result<_>>()?,
            *e,
        ),
        Term::Loc(span, t) => Term::Loc(*span, go(t, under)?),
    })
}

/// The levels of the free variables of `term`, in a context of `depth`
/// variables (a case split's variable counts), except that a call of a
/// draft (its frozen metavariable applied to the variables in scope, then
/// its own arguments) only uses the variables at the positions `calls`
/// gives for that metavariable: `(s, used)`, where `s` is how many
/// arguments stand for variables in scope and `used` those the draft
/// captures (§2.1 rule 3).
pub(crate) fn uses(
    term: &Term,
    depth: usize,
    calls: &dyn Fn(usize) -> Option<(usize, BTreeSet<usize>)>,
    out: &mut BTreeSet<usize>,
) {
    let mut stack = vec![(term, 0usize)];
    while let Some((t, under)) = stack.pop() {
        if let Term::App(..) = t.strip_loc() {
            let (head, args) = t.spine();
            if let Term::Meta(m) = head
                && let Some((s, used)) = calls(*m)
            {
                for (p, a) in args.into_iter().enumerate() {
                    if p >= s || used.contains(&p) {
                        stack.push((a, under));
                    }
                }
                continue;
            }
        }
        if let Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) = t
            && *ix >= under
        {
            out.insert(depth - 1 - (ix - under));
        }
        t.for_each_child(|c, u| stack.push((c, under + u)));
    }
}

/// The metavariables `term` mentions.
fn metas(term: &Term, out: &mut BTreeSet<usize>) {
    for (t, _) in term.subterms() {
        if let Term::Meta(m) = t {
            out.insert(*m);
        }
    }
}

/// The definitions `term` refers to.
pub(crate) fn defs(term: &Term) -> impl Iterator<Item = DefId> + '_ {
    term.subterms().filter_map(|(t, _)| match t {
        Term::Def(id) => Some(*id),
        _ => None,
    })
}

/// How a draft is named in a message: "this `match`", or "`go`".
fn described(draft: &Draft) -> String {
    match &draft.local {
        Some(local) => format!("`{}`", local.name),
        None => "this `match`".into(),
    }
}

/// Whether `inner` is inside `outer`.
pub(crate) fn within(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.start <= inner.start && inner.end <= outer.end
}

/// The keys of a batch of drafts: a local definition's own; a `match`'s
/// numbered in source order within the innermost local definition it's in,
/// or else within the owner (§2.4).
fn keys(owner: &str, drafts: &[Draft]) -> Vec<String> {
    let prefix = |d: &Draft| -> String {
        drafts
            .iter()
            .filter_map(|o| o.local.as_ref())
            .filter(|l| within(l.whole, d.span))
            .min_by_key(|l| l.whole.end - l.whole.start)
            .map_or_else(|| owner.to_string(), |l| l.key.clone())
    };
    let mut out = vec![String::new(); drafts.len()];
    let mut matches: HashMap<String, Vec<usize>> = HashMap::default();
    for (i, d) in drafts.iter().enumerate() {
        match &d.local {
            Some(l) => out[i] = l.key.clone(),
            None => matches.entry(prefix(d)).or_default().push(i),
        }
    }
    for (prefix, mut members) in matches {
        members.sort_by_key(|&i| (drafts[i].span.start, std::cmp::Reverse(drafts[i].span.end)));
        for (n, i) in members.into_iter().enumerate() {
            out[i] = format!("{prefix}.%match{}", n + 1);
        }
    }
    out
}

impl Elaborator {
    /// Resolves the drafts made while elaborating `owner` (a declaration
    /// key). Each is declared, and admitted at once unless it refers to
    /// something pending and `join` allows it to join the owner's group:
    /// those are returned, with their bodies, for the caller to admit with
    /// the owner.
    pub(crate) fn lift(&mut self, owner: &str, join: bool) -> Result<Vec<(DefId, Term)>> {
        if self.drafts.borrow().is_empty() {
            return Ok(Vec::new());
        }
        self.solve_obligations()?;
        let drafts = std::mem::take(&mut *self.drafts.borrow_mut());
        Ok(self.resolve_batch(owner, drafts, join)?.0)
    }

    /// Resolves `drafts` together (see the module's documentation): the
    /// helpers to admit with the owner, and what each draft became.
    pub(crate) fn resolve_batch(
        &mut self,
        owner: &str,
        drafts: Vec<Draft>,
        join: bool,
    ) -> Result<Batch> {
        self.arounds.borrow_mut().clear();
        let keys = keys(owner, &drafts);
        let index: HashMap<usize, usize> = drafts
            .iter()
            .enumerate()
            .map(|(i, d)| (d.meta, i))
            .collect();
        let in_batch = |m: usize| index.contains_key(&m);
        let (ordered, unrefined) = self.captures(&drafts, &index)?;
        // Which drafts each one calls (in its body, type or captures' types).
        let mut calls: Vec<Vec<usize>> = Vec::new();
        for ((caps, (body, goal)), types) in
            ordered.iter().zip(&unrefined.parts).zip(&unrefined.types)
        {
            let mut found = BTreeSet::new();
            metas(body, &mut found);
            metas(goal, &mut found);
            for &l in caps {
                metas(types[l].as_ref().expect("a capture's type"), &mut found);
            }
            calls.push(found.iter().filter_map(|m| index.get(m).copied()).collect());
        }
        drop(unrefined);
        let mut joined: Vec<(DefId, Term)> = Vec::new();
        let mut joined_ids = HashSet::default();
        let mut resolved: Vec<Option<Resolved>> = (0..drafts.len()).map(|_| None).collect();
        // Tarjan's components come after the components they call.
        for mut component in crate::module::tarjan(&calls) {
            component.sort_unstable();
            let mut members = Vec::new();
            for &i in &component {
                let d = &drafts[i];
                // A frozen metavariable left in its type is a member of its
                // own component, not declared yet.
                let mut unfinished = BTreeSet::new();
                let kept = self.parts(d, &ordered[i], &in_batch, false)?;
                metas(&kept.0, &mut unfinished);
                if !unfinished.is_empty() {
                    return Err(Diagnostic::error(
                        "E-MUTUAL-SIGNATURE",
                        format!(
                            "{}'s type refers to a local definition defined together with it",
                            described(d)
                        ),
                    )
                    .with_label(d.span, "here")
                    .with_note(
                        "a definition's type can only mention finished definitions, and the \
                         ones it calls and that call it aren't finished until it is",
                    ));
                }
                // With no metavariable left in the type or the call's
                // arguments, keeping the batch's unsolved ones kept none:
                // the parts are what keeping none gives, so they aren't
                // worked out again (the type can be large).
                for (arg, _) in &kept.2 {
                    metas(arg, &mut unfinished);
                }
                let (ty, _, args) = if unfinished.is_empty() {
                    kept
                } else {
                    self.parts(d, &ordered[i], &|_| false, false)?
                };
                let id = self.declare_helper(d, &keys[i], &ty)?;
                // Opaque with its owner's `unfolding` clause, if it has one
                // (`opaque.rs`).
                self.opaque_helper(id);
                let g = &self.globals;
                let mut call = Term::Def(id);
                for (arg, icit) in args {
                    call = Term::app_icit(call, arg, icit);
                }
                let s = spine(&d.env[..d.base], &d.lets).len();
                g.lifted_calls
                    .borrow_mut()
                    .insert(d.meta, (s, Rc::new(call.clone())));
                for _ in 0..s {
                    call = Term::Lam("x".into(), Icit::Explicit, Rc::new(call));
                }
                g.solve_meta(d.meta, eval(g, &[], &call)?);
                if let Some(item) = self.module.item {
                    self.module.def_items.insert(id, item);
                }
                match &d.local {
                    Some(local) => {
                        self.local_helpers
                            .push((local.key.clone(), id, local.whole));
                        self.globals.print_labels.borrow_mut().push(
                            stitchwort_core::globals::PrintLabel {
                                head: Term::Def(id),
                                name: local.name.as_str().into(),
                                levels: ordered[i].clone(),
                            },
                        );
                    }
                    None => self.lifted.push((id, d.span)),
                }
                members.push((i, id));
            }
            let mut bodies = Vec::new();
            for &(i, id) in &members {
                let (_, lam, _) = self.parts(&drafts[i], &ordered[i], &|_| false, true)?;
                bodies.push((id, lam));
            }
            let ids: HashSet<DefId> = members.iter().map(|(_, id)| *id).collect();
            let pending = bodies.iter().any(|(_, body)| {
                defs(body).any(|d| {
                    !ids.contains(&d)
                        && (joined_ids.contains(&d)
                            || self.globals.def(d).state() == State::Pending)
                })
            });
            for &(i, id) in &members {
                let d = &drafts[i];
                resolved[i] = Some(Resolved {
                    id,
                    captures: ordered[i]
                        .iter()
                        .map(|&l| (l, d.kinds[l], d.names[l].clone()))
                        .collect(),
                });
            }
            if join && pending {
                joined_ids.extend(ids);
                joined.extend(bodies);
            } else {
                kernel::define_group(&mut self.globals, &bodies)
                    .map_err(|d| self.explain_lifted(d))?;
                for (_, id) in &members {
                    self.opaque_helper_admitted(*id);
                }
            }
        }
        let resolved = resolved
            .into_iter()
            .map(|r| r.expect("every component is resolved"))
            .collect();
        self.arounds.borrow_mut().clear();
        Ok((joined, resolved))
    }

    /// Declares the helper for `draft`, of type `ty`, as `key`.
    fn declare_helper(&mut self, draft: &Draft, key: &str, ty: &Term) -> Result<DefId> {
        let name = crate::scope::display(key).to_string();
        let theorem = draft.local.as_ref().is_some_and(|l| l.theorem);
        let what = described(draft);
        // Everything in the type was elaborated and checked where it was
        // written, except what generalising a scrutinee changed: if the
        // kernel refuses it, that's why (§4.4).
        kernel::declare_def(
            &mut self.globals,
            &name.into(),
            ty,
            theorem,
            false,
            draft.span,
        )
        .map_err(|d| {
            if crate::undo::fatal(&d) {
                return d;
            }
            if let Some(reason) = std::iter::once(&d.message)
                .chain(d.labels.iter().map(|l| &l.message))
                .find(|m| m.contains("which isn't finished"))
            {
                // Like a signature mentioning a member of its own group.
                return Diagnostic::error(
                    "E-MUTUAL-SIGNATURE",
                    format!("{what}'s type refers to a definition that isn't finished"),
                )
                .with_label(draft.span, "here")
                .with_note(format!("the kernel's reason: {reason}"))
                .with_note(if draft.local.is_some() {
                    "a local definition is made into a top-level one, whose type can only \
                     mention finished definitions: not the definition it's in, nor a local \
                     definition that calls that"
                } else {
                    "the `match` is made into a definition whose type must only mention \
                     finished definitions; annotate it with a type that doesn't, or use a \
                     top-level helper"
                });
            }
            if draft.local.is_some() {
                return d;
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
        })
    }

    /// `term` (in `draft`'s context, of `depth` variables) with solved
    /// metavariables substituted in, and the variables a case split replaced
    /// by a constructor replaced by it: the helper takes the constructor's
    /// fields instead. Unsolved metavariables are an error, except those
    /// `keep` allows.
    ///
    /// For a type: a `let`'s variable, whose slot holds its value, is
    /// replaced by that value too (types are erased, so this costs nothing
    /// when running; a type quoted from a value never mentions one anyway).
    fn unrefine(
        &self,
        draft: &Draft,
        term: &Term,
        depth: usize,
        keep: &dyn Fn(usize) -> bool,
    ) -> Result<Term> {
        self.unrefine_as(draft, term, depth, keep, false)
    }

    /// [`Elaborator::unrefine`] for what the call passes: a `let`'s variable
    /// stays a variable, since the frozen metavariable's spine includes the
    /// `let`s in scope ([`spine`]), so the call shares the value the owner
    /// computed instead of computing it again.
    fn unrefine_call(
        &self,
        draft: &Draft,
        term: &Term,
        depth: usize,
        keep: &dyn Fn(usize) -> bool,
    ) -> Result<Term> {
        self.unrefine_as(draft, term, depth, keep, true)
    }

    fn unrefine_as(
        &self,
        draft: &Draft,
        term: &Term,
        depth: usize,
        keep: &dyn Fn(usize) -> bool,
        lets: bool,
    ) -> Result<Term> {
        let g = &self.globals;
        let t = if lets {
            let around = self.around(draft, depth);
            self.zonk_around(term, depth, keep, &around)?
        } else {
            self.zonk_keeping(term, depth, keep)?
        };
        replace(g, &t, depth, &|l| {
            if is_var(&draft.env[l], l) || (lets && draft.lets[l].is_some()) {
                Ok(Term::Var(depth - 1 - l))
            } else {
                Ok(quote_folded(g, depth, &draft.env[l])?)
            }
        })
    }

    /// The `let`s of `draft`'s context, in its first `depth` variables, that
    /// solutions are folded back to ([`crate::unify::refold`]): each with
    /// its value's normal form, itself folded back to the ones before it.
    /// They're the same for every term of the draft until a metavariable is
    /// solved, so they're computed once ([`Arounds`]).
    fn around(&self, draft: &Draft, depth: usize) -> Vec<crate::unify::Around> {
        let g = &self.globals;
        let trail = g.meta_trail.borrow().len();
        let upto = depth.min(draft.lets.len());
        let mut cache = self.arounds.borrow_mut();
        let (made, done, around) = cache.entry(draft.meta).or_default();
        if *made != trail {
            (*made, *done) = (trail, 0);
            around.clear();
        }
        for l in *done..upto {
            if draft.lets[l].is_some()
                && let Some(normals) = crate::unify::cheaply(g, || {
                    let mut out = Vec::new();
                    for normal in crate::unify::both_forms(g, l, &draft.env[l])? {
                        out.push(crate::unify::refold(g, normal, l, around).map_err(
                            |e| match e {
                                crate::unify::ZonkError::Resource(e) => e,
                                crate::unify::ZonkError::Unsolved(_) => {
                                    unreachable!("refolding solves nothing")
                                }
                            },
                        )?);
                    }
                    Ok(out)
                })
            {
                for normal in normals {
                    if crate::unify::worth_folding(&normal) {
                        around.push((l, Rc::new(normal)));
                    }
                }
            }
        }
        *done = (*done).max(upto);
        around.iter().filter(|(l, _)| *l < depth).cloned().collect()
    }

    /// The helper's body, unrefined, with the `let`s of the owner's context
    /// it uses re-created inside it (docs/proposals/let.md §6.1 rule 4,
    /// §A.4): the helper takes the variables their values use, and knows
    /// `x := v` as the owner did, instead of taking `x` as an opaque
    /// argument or having `v`'s normal form pasted in. A `let` is never a
    /// case-tree node, so each is re-created at the top of each leaf of the
    /// case tree that uses it (with the `let`s its type and value use, in
    /// order); only one leaf runs, so a value is computed at most once per
    /// call.
    fn unrefine_body(
        &self,
        draft: &Draft,
        term: &Term,
        keep: &dyn Fn(usize) -> bool,
    ) -> Result<Term> {
        let n = draft.env.len();
        let t = self.unrefine_as(draft, term, n, keep, true)?;
        if draft.lets.iter().all(Option::is_none) {
            return Ok(t);
        }
        // A local definition's parameters are its leading lambdas; a
        // `match`'s helper takes none of its own.
        self.recreate(draft, &t, 0, draft.local.is_some(), keep)
    }

    /// [`Elaborator::unrefine_body`]'s walk down the case tree of `term`
    /// (under `under` binders of its own), through leading lambdas if
    /// `params`.
    fn recreate(
        &self,
        draft: &Draft,
        term: &Term,
        under: usize,
        params: bool,
        keep: &dyn Fn(usize) -> bool,
    ) -> Result<Term> {
        self.globals.budget.nesting(crate::check::PASS)?;
        let go =
            |t: &Term, under, params| self.recreate(draft, t, under, params, keep).map(Rc::new);
        Ok(match term {
            Term::Loc(span, t) => Term::Loc(*span, go(t, under, params)?),
            Term::Lam(x, i, b) if params => Term::Lam(x.clone(), *i, go(b, under + 1, true)?),
            Term::Case(ix, d, branches) => Term::Case(
                *ix,
                *d,
                branches
                    .iter()
                    .map(|b| {
                        Ok(Branch {
                            names: b.names.clone(),
                            body: b
                                .body
                                .as_ref()
                                .map(|body| go(body, under + b.names.len(), false))
                                .transpose()?,
                        })
                    })
                    .collect::<Result<_>>()?,
            ),
            Term::NumCase(ix, arms, default) => Term::NumCase(
                *ix,
                arms.iter()
                    .map(|a| {
                        Ok(NumArm {
                            value: a.value.clone(),
                            body: go(&a.body, under, false)?,
                        })
                    })
                    .collect::<Result<_>>()?,
                go(default, under, false)?,
            ),
            leaf => self.with_lets(draft, leaf, under, keep)?,
        })
    }

    /// `leaf` (in the draft's context and `under` binders of the helper's
    /// own) inside the `let`s of the draft's context it uses.
    fn with_lets(
        &self,
        draft: &Draft,
        leaf: &Term,
        under: usize,
        keep: &dyn Fn(usize) -> bool,
    ) -> Result<Term> {
        let g = &self.globals;
        let n = draft.env.len();
        let c = n + under;
        let lets_in = |t: &Term, depth: usize, out: &mut Vec<usize>| {
            for (t, binders) in t.subterms() {
                if let Term::Var(ix) = t
                    && let Some(ix) = ix.checked_sub(binders)
                    && let Some(level) = depth.checked_sub(ix + 1)
                    && draft.lets.get(level).is_some_and(Option::is_some)
                {
                    out.push(level);
                }
            }
        };
        // The `let`s it uses, and those their types and values use.
        let mut defs: std::collections::BTreeMap<usize, (Term, Term)> = Default::default();
        let mut work = Vec::new();
        lets_in(leaf, c, &mut work);
        while let Some(l) = work.pop() {
            if defs.contains_key(&l) {
                continue;
            }
            let def = draft.lets[l].as_ref().expect("a `let`'s slot");
            let ty = self.unrefine_as(draft, &def.ty, l, keep, true)?;
            let value = self.unrefine_as(draft, &def.value, l, keep, true)?;
            lets_in(&ty, l, &mut work);
            lets_in(&value, l, &mut work);
            defs.insert(l, (ty, value));
        }
        if defs.is_empty() {
            return Ok(leaf.clone());
        }
        let levels: Vec<usize> = defs.keys().copied().collect();
        // A term in the first `from` variables of the context, moved under
        // the first `i` re-created `let`s, which stand for their slots.
        let moved = |t: &Term, from: usize, i: usize| {
            replace(g, t, from, &|l| {
                Ok(match levels[..i].iter().position(|m| *m == l) {
                    Some(j) => Term::Var(i - 1 - j),
                    None => Term::Var(c + i - 1 - l),
                })
            })
        };
        let k = levels.len();
        let mut body = moved(leaf, c, k)?;
        for (i, l) in levels.iter().enumerate().rev() {
            let (ty, value) = &defs[l];
            body = Term::let_(
                draft.names[*l].clone(),
                moved(ty, *l, i)?,
                moved(value, *l, i)?,
                body,
            );
        }
        Ok(body)
    }

    /// The captures of each draft, ordered (§2.1): the least sets closed
    /// under the variables each uses, their types' variables, and the
    /// captures of the drafts each calls. `index` gives each draft's
    /// frozen metavariable's draft.
    fn captures(
        &self,
        drafts: &[Draft],
        index: &HashMap<usize, usize>,
    ) -> Result<(Vec<Vec<usize>>, Unrefined)> {
        let g = &self.globals;
        let in_batch = |m: usize| index.contains_key(&m);
        // Bodies and types, and the types of the variables, as the fixed
        // point reads them (each variable's computed once, when needed).
        let mut parts: Vec<(Term, Term)> = Vec::new();
        let mut types: Vec<Vec<Option<Term>>> = Vec::new();
        for d in drafts {
            let n = d.env.len();
            parts.push((
                self.unrefine_body(d, &d.body, &in_batch)?,
                self.unrefine(d, &d.goal, n, &in_batch)?,
            ));
            types.push(vec![None; n]);
        }
        let spines: Vec<Vec<usize>> = drafts
            .iter()
            .map(|d| spine(&d.env[..d.base], &d.lets))
            .collect();
        let mut caps: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); drafts.len()];
        let mut used: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); drafts.len()];
        loop {
            let mut changed = false;
            for (i, d) in drafts.iter().enumerate() {
                let n = d.env.len();
                let calls = |m: usize| index.get(&m).map(|&j| (spines[j].len(), used[j].clone()));
                let mut found = BTreeSet::new();
                uses(&parts[i].0, n, &calls, &mut found);
                uses(&parts[i].1, n, &calls, &mut found);
                let mut work: Vec<usize> = found.iter().copied().collect();
                let mut done = BTreeSet::new();
                while let Some(l) = work.pop() {
                    if !done.insert(l) {
                        continue;
                    }
                    if types[i][l].is_none() {
                        let ty = quote_folded(g, n, &d.types[l])?;
                        types[i][l] = Some(self.unrefine(d, &ty, n, &in_batch)?);
                    }
                    let mut deps = BTreeSet::new();
                    uses(
                        types[i][l].as_ref().expect("just computed"),
                        n,
                        &calls,
                        &mut deps,
                    );
                    for dep in deps {
                        if found.insert(dep) {
                            work.push(dep);
                        }
                    }
                }
                if found != caps[i] {
                    caps[i] = found;
                    changed = true;
                }
            }
            for (i, d) in drafts.iter().enumerate() {
                used[i] = self.positions(d, &spines[i], &caps[i])?;
            }
            if !changed {
                break;
            }
        }
        // Each one's captures, ordered by their types' dependencies, keeping
        // context order where the dependencies allow (§4.4).
        let mut out = Vec::new();
        for (i, d) in drafts.iter().enumerate() {
            let n = d.env.len();
            let calls = |m: usize| index.get(&m).map(|&j| (spines[j].len(), used[j].clone()));
            let mut deps: HashMap<usize, BTreeSet<usize>> = HashMap::default();
            for &l in &caps[i] {
                let mut found = BTreeSet::new();
                uses(
                    types[i][l].as_ref().expect("computed above"),
                    n,
                    &calls,
                    &mut found,
                );
                deps.insert(l, found);
            }
            let mut ordered: Vec<usize> = Vec::new();
            let mut left: Vec<usize> = caps[i].iter().copied().collect();
            left.sort_by_key(|&l| rank(&d.order, l));
            while !left.is_empty() {
                let Some(p) = left
                    .iter()
                    .position(|l| deps[l].iter().all(|d| ordered.contains(d)))
                else {
                    return Err(Diagnostic::error(
                        "E-MATCH-MOTIVE",
                        format!(
                            "{}'s type can't be built: the types of the variables it uses \
                             depend on each other in a cycle",
                            described(d)
                        ),
                    )
                    .with_label(d.span, "here")
                    .with_note(
                        "write the helper as a top-level definition with its own signature \
                         instead",
                    ));
                };
                ordered.push(left.remove(p));
            }
            out.push(ordered);
        }
        Ok((out, Unrefined { parts, types }))
    }

    /// The positions in `spine` (the frozen metavariable's arguments) of
    /// the variables a draft with captures `caps` needs passed.
    fn positions(
        &self,
        d: &Draft,
        spine: &[usize],
        caps: &BTreeSet<usize>,
    ) -> Result<BTreeSet<usize>> {
        let mut levels = BTreeSet::new();
        for &c in caps {
            if c < d.base {
                levels.insert(c);
            } else {
                let extra = self.unrefine_call(d, &d.extra[c - d.base], d.base, &|_| true)?;
                uses(&extra, d.base, &|_| None, &mut levels);
            }
        }
        levels
            .into_iter()
            .map(|l| {
                spine.iter().position(|v| *v == l).ok_or_else(|| {
                    Diagnostic::error(
                        "E-MALFORMED",
                        "internal error: a lifted call uses a variable outside its context",
                    )
                })
            })
            .collect()
    }

    /// The helper's type and body (with `body`; otherwise `Refl` stands for
    /// it), and the arguments of its call (as terms in the frozen
    /// metavariable's spine, with their kinds), given its captures in
    /// order. Unsolved metavariables are an error unless `keep` allows them.
    fn parts(
        &self,
        draft: &Draft,
        ordered: &[usize],
        keep: &dyn Fn(usize) -> bool,
        body: bool,
    ) -> Result<Parts> {
        let g = &self.globals;
        let n = draft.env.len();
        let body = if body {
            self.unrefine_body(draft, &draft.body, keep)?
        } else {
            Term::Refl
        };
        let goal = self.unrefine(draft, &draft.goal, n, keep)?;
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
        // A local definition's captures keep their kinds; a `match` can't be
        // named in source, so its are all explicit.
        let kind = |l: usize| match &draft.local {
            Some(_) => draft.kinds[l],
            None => Icit::Explicit,
        };
        let k = ordered.len();
        let mut ty = into(&goal, n, k)?;
        let mut lam = into(&body, n, k)?;
        for (p, &l) in ordered.iter().enumerate().rev() {
            let dom = quote_folded(g, n, &draft.types[l])?;
            let dom = into(&self.unrefine(draft, &dom, n, keep)?, n, p)?;
            let x = draft.names[l].clone();
            ty = Term::Pi(x.clone(), kind(l), Rc::new(dom), Rc::new(ty));
            lam = Term::Lam(x, kind(l), Rc::new(lam));
        }
        // The call's arguments, as functions of the metavariable's spine.
        let base = draft.base;
        let spine = spine(&draft.env[..base], &draft.lets);
        let s = spine.len();
        let in_spine = |t: &Term| {
            let t = self.unrefine_call(draft, t, base, keep)?;
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
                let arg = if l < base {
                    in_spine(&Term::Var(base - 1 - l))?
                } else {
                    in_spine(&draft.extra[l - base])?
                };
                Ok((arg, kind(l)))
            })
            .collect::<Result<_>>()?;
        Ok((ty, lam, args))
    }

    /// The type a `match`'s helper would have (for the motive check before
    /// its alternatives are elaborated).
    pub(crate) fn lifted_type(&self, draft: &Draft) -> Result<Term> {
        self.arounds.borrow_mut().clear();
        let (ordered, _) = self.captures(std::slice::from_ref(draft), &HashMap::default())?;
        let ty = self.parts(draft, &ordered[0], &|_| false, false);
        self.arounds.borrow_mut().clear();
        Ok(ty?.0)
    }

    /// Mentions of lifted helpers in a diagnostic name the `match` instead
    /// (§2.5): `f.%match1` is never shown.
    /// In a termination message, a local definition of the declaration
    /// being checked is named as written: `go`, not `sumTo.go`.
    pub(crate) fn explain_lifted(&self, mut d: Diagnostic) -> Diagnostic {
        // Only the kernel's termination messages name one by its key; the
        // elaborator's own say what they mean.
        let helpers = match d.code {
            "E-TERMINATION" => &self.local_helpers[..],
            _ => &[],
        };
        for (_, id, _) in helpers {
            let def = self.globals.def(*id);
            let full = format!("`{}`", def.name);
            let Some((_, short)) = def.name.rsplit_once('.') else {
                continue;
            };
            let short = format!("`{short}`");
            d.message = d.message.replace(&full, &short);
            for l in &mut d.labels {
                l.message = l.message.replace(&full, &short);
            }
            for note in &mut d.notes {
                *note = note.replace(&full, &short);
            }
        }
        // Longest first, so `f.%match1` isn't found inside `f.%match10`.
        let mut lifted: Vec<(String, Span)> = self
            .lifted
            .iter()
            .map(|&(id, span)| (self.globals.def(id).name.to_string(), span))
            .collect();
        lifted.sort_by_key(|(name, _)| std::cmp::Reverse(name.len()));
        let mut owners: Vec<String> = Vec::new();
        // How many different generated helpers the message mentions inline:
        // each prints as `(match …)`, so two of them look like one.
        let mut inline_helpers = 0;
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
            let inline = std::iter::once(&d.message)
                .chain(d.labels.iter().map(|l| &l.message))
                .chain(d.notes.iter())
                .any(|s| s.replace(&quoted, "").contains(&bare));
            if inline {
                inline_helpers += 1;
            }
            if inline
                && let Some((owner, _)) = bare.rsplit_once(".%match")
                && !owners.iter().any(|o| o == owner)
            {
                owners.push(owner.to_string());
            }
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
        // D229: say where the `match` is and how to name it. The source
        // position is the label, which the renderer shows with its file and
        // line.
        if !owners.is_empty() {
            let inside = owners
                .iter()
                .map(|o| format!("`{o}`"))
                .collect::<Vec<_>>()
                .join(" and ");
            d = d.with_note(format!(
                "`(match …)` is a `match` written inside {inside}, marked \"this `match`\" \
                 above; the compiler turned it into a function that source can't name. The \
                 same `match` written again is another such function, equal to it only if \
                 neither calls the definition it's written in. To state a lemma \
                 about it, make it a local `def` in its arm and refer to it as \
                 `owner.name`, where `owner` is the definition it is written in \
                 (docs/syntax.md, \"Proving things about a definition with an inner \
                 `match`\")"
            ));
        }
        if inline_helpers >= 2 {
            d = d.with_note(
                "two different `(match …)` appear here, which print alike but are different \
                 hidden functions; two such functions are equal only when they split the same \
                 value and every branch gives the same result, and neither calls the \
                 definition it's written in; to prove something about both, name the step as \
                 a `def` and use it in both places",
            );
        }
        d
    }
}
