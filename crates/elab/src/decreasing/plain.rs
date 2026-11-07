//! `f.unfold` over the body as written, when a plain `if` gave a recursive
//! call under it its condition, or a `match` its equation
//! (docs/proposals/decreasing-with-hypothesis.md, stages 1 and 2).
//!
//! In a `decreasing` body a plain `if` is elaborated as `if _: …` would be,
//! `Decidable.elim d (h => a) (h => b)`, its decision tagged with the `Bool`
//! the plain `if` is on (`logic::tag_plain`). Where only recursive calls'
//! proofs use `h`, `f.%step` keeps the `Decidable.elim` (the calls need it)
//! and two more definitions are made:
//!
//! 1. `f.%plain (x…) (%rec: (y…) -> B) (c…): B`, the body with each such `if`
//!    as `Bool.ifThenElse b (_ => a) (_ => b)` and each recursive call
//!    without its proof. A `match` lifted from the body is passed `y… p =>
//!    %rec y…`.
//! 2. `f.%plain.%same (x…) (r: (y…) -> B) (c…): f.%step x… (y… p => r y…)
//!    c… = f.%plain x… r c…`, by `f.%step`'s case tree, and at each leaf by
//!    `Decidable.elimIf` or `Bool.elimDecTrueIf` at each such `if`, through
//!    the `if`s around it by `Decidable.elimCong` and `Bool.ifThenElseCong`,
//!    through a `let` by the same `let`, and in an argument by rewriting one
//!    `if` at a time (`J`).
//!
//! `f.unfold` is then `f x… = f.%plain x… (y… => f y…)`. An `if` whose `h`
//! something else uses, or that sits where the proof doesn't go (inside a
//! function passed to another, a condition), stays a `Decidable.elim` in
//! `f.%plain` too.
//!
//! Stage 2: a `match` in the body, lifted to `H` (`f.%step.%match1`), is
//! passed its equation `e = s` (`rfl`), named or not, when an arm calls the
//! definition (`matching.rs`, [`super::FOUND`]). Such an `H` gets a twin `H'`
//! (`H.%plain`), made the same way as `f.%plain` from its own case tree
//! (its plain `if`s are kept tagged for this, `lifted_helper_body`), and
//! without the parameters its plain body doesn't need: the equation, and
//! any fact only a call's proof used. `H.%plain.%same` says `H x… (y… p =>
//! r y…) … = H' …`, and `f.%plain` calls `H'` wherever the proof reaches,
//! the call proved by that lemma. So `f.unfold` shows the `match` with no
//! equation, which a proof can generalise. `let`s only the dropped proofs
//! used go too.

use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::same_term;
use stitchwort_core::{DefId, Ev, Icit, Name, Term};
use stitchwort_syntax::Span;

use super::{Binder, Plan, apps, instantiate, internal_error, lams, pis, split_pis, var};
use crate::logic::PLAIN;
use crate::{Elaborator, Result, kernel};

/// What `f.unfold` is stated with when the body has plain `if`s to show.
pub(super) struct PlainView {
    /// `f.%plain`.
    pub(super) view: DefId,
    /// `f.%plain.%same`.
    pub(super) same: DefId,
}

/// The core definitions this refers to.
struct Lemmas {
    elim: DefId,
    ite: DefId,
    to_bool: DefId,
    dec_true: DefId,
    /// The standard decisions of comparisons, each `Bool.decTrue` of the
    /// comparison's `Bool` (`bind::comparison`).
    comparisons: Vec<DefId>,
    elim_if: DefId,
    true_if: DefId,
    elim_cong: DefId,
    if_cong: DefId,
    /// The twins made so far, by the lifted `match` they're of.
    twins: HashMap<DefId, Twin>,
}

/// Which lemma turns a tagged `if` into the plain one.
#[derive(Clone, Copy)]
enum Kind {
    /// `b` is `Decidable.toBool d`: `Decidable.elimIf`.
    ToBool,
    /// `d` is `Bool.decTrue b`, or a comparison's decision, which is that
    /// by definition: `Bool.elimDecTrueIf`.
    DecTrue,
}

/// A term with the parts the proof rewrites marked, as `decreasing.rs`'s
/// `Tpl` for recursive calls.
enum Part {
    Same(Term),
    Hole(usize),
    App(Box<Part>, Box<Part>, Icit),
    Ctor(stitchwort_core::DataId, usize, Vec<Part>),
    Ann(Box<Part>, Term),
    Loc(Span, Box<Part>),
}

/// A part to rewrite: as `f.%step` has it, as `f.%plain` has it, and a
/// proof that they're equal.
struct Hole {
    pre: Term,
    post: Term,
    proof: Term,
}

fn spine_owned(t: &Term) -> (Term, Vec<(Term, Icit)>) {
    let mut args = Vec::new();
    let mut head = t.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push(((**a).clone(), *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head.clone(), args)
}

/// `t` with each immediate child `c` replaced by `f(c, depth of c)`.
fn children(
    t: &Term,
    depth: usize,
    f: &mut dyn FnMut(&Term, usize) -> Result<Term>,
) -> Result<Term> {
    let mut go = |t: &Rc<Term>, d: usize| -> Result<Rc<Term>> { Ok(Rc::new(f(t, d)?)) };
    Ok(match t {
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => t.clone(),
        Term::Data(d, args) => Term::Data(
            *d,
            args.iter().map(|a| go(a, depth)).collect::<Result<_>>()?,
        ),
        Term::Ctor(d, c, args) => Term::Ctor(
            *d,
            *c,
            args.iter().map(|a| go(a, depth)).collect::<Result<_>>()?,
        ),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a, depth)?, go(b, depth + 1)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b, depth + 1)?),
        Term::App(a, b, i) => Term::App(go(a, depth)?, go(b, depth)?, *i),
        Term::Ann(a, b) => Term::Ann(go(a, depth)?, go(b, depth)?),
        Term::Let(x, a, v, b, e) => Term::Let(
            x.clone(),
            go(a, depth)?,
            go(v, depth)?,
            go(b, depth + 1)?,
            *e,
        ),
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
                            .map(|body| go(body, depth + b.names.len()))
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
                        body: go(&a.body, depth)?,
                    })
                })
                .collect::<Result<_>>()?,
            go(default, depth)?,
        ),
        Term::Eq(ty, a, b) => Term::Eq(
            ty.as_ref().map(|t| go(t, depth)).transpose()?,
            go(a, depth)?,
            go(b, depth)?,
        ),
        Term::J(m, b, p) => Term::J(go(m, depth)?, go(b, depth)?, go(p, depth)?),
        Term::Proj(d, i, t) => Term::Proj(*d, *i, go(t, depth)?),
        Term::Quot(form, args, e) => Term::Quot(
            *form,
            args.iter().map(|a| go(a, depth)).collect::<Result<_>>()?,
            *e,
        ),
        Term::Loc(span, t) => Term::Loc(*span, go(t, depth)?),
    })
}

/// The name of the `let` [`Lemmas::mark`] wraps around a call of a lifted
/// `match` that has a twin, `let %twin := Refl in call`, for `pre`, `post`
/// and the proof to find. It never reaches the kernel.
const TWIN: &str = "%twin";

/// Whether `t` holds a tagged `if` or a marked call of a twin.
fn tagged(t: &Term) -> bool {
    t.subterms()
        .any(|(t, _)| matches!(t, Term::Let(name, ..) if &**name == PLAIN || &**name == TWIN))
}

/// The call `let %twin := Refl in call` marks.
fn twin_call(
    g: &Ev,
    t: &Term,
) -> std::result::Result<Option<Term>, stitchwort_core::budget::ResourceError> {
    match t.strip_loc() {
        Term::Let(name, _, v, body, _) if &**name == TWIN => Ok(Some(body.instantiate(g, v)?)),
        _ => Ok(None),
    }
}

/// `t` without the `let`s nothing uses, such as a fact only recursive calls'
/// proofs used, once they're dropped: the same by computation, and the
/// plain form doesn't show them.
fn dead_lets(g: &Ev, t: &Term) -> Result<Term> {
    Ok(t.rewrite_up(g, &mut |node| match node {
        Term::Let(name, _, _, body, _) if !name.starts_with('%') && !body.mentions(0) => {
            Ok(Some(body.instantiate(g, &Term::Refl)?))
        }
        _ => Ok(None),
    })?)
}

/// `r`, for `y… p => r y…` with `k` binders (`Rec::adapter`).
fn unadapt(t: &Term, k: usize) -> Option<Term> {
    let mut body = t.strip_loc();
    for _ in 0..k {
        body = match body {
            Term::Lam(_, _, b) => b.strip_loc(),
            _ => return None,
        };
    }
    let (head, args) = spine_owned(body);
    let Term::Var(ix) = head else {
        return None;
    };
    let plain = args.len() + 1 == k
        && (args.iter().enumerate())
            .all(|(j, (a, _))| matches!(a.strip_loc(), Term::Var(v) if *v == k - 1 - j));
    (plain && ix >= k).then(|| Term::Var(ix - k))
}

/// A lifted `match` whose arms call `%rec`, and its twin for `f.%plain`:
/// the same with `%rec` taking no proof, and without the parameters only
/// proofs used (the `match`'s equation `e = s`, passed `rfl`, and any fact
/// only a recursive call's proof used).
struct Twin {
    twin: DefId,
    /// `H x… (y… p => r y…) … = H' …`, for all of `H`'s parameters.
    same: DefId,
    /// `H`'s arity, and which of its parameters is `%rec`.
    arity: usize,
    rec: usize,
    /// `rec`'s parameters, the proof included.
    rec_arity: usize,
    /// `H`'s parameters that `H'` takes, in order.
    kept: Vec<usize>,
}

/// The tag of decision `d`, `let %plain := b in d'`: `b` and `d'`.
fn untag(
    g: &Ev,
    d: &Term,
) -> std::result::Result<Option<(Term, Term)>, stitchwort_core::budget::ResourceError> {
    let Term::Let(name, _, b, inner, _) = d.strip_loc() else {
        return Ok(None);
    };
    if &**name != PLAIN {
        return Ok(None);
    }
    Ok(Some(((**b).clone(), inner.instantiate(g, b)?)))
}

/// What `%rec` is passed and called as in `f.%plain`, where it takes no
/// proof: `adapt` makes the step's body into that.
struct Rec {
    /// `%rec`'s level.
    level: usize,
    /// Its parameters, the proof last.
    tel: Vec<Binder>,
}

impl Rec {
    fn arity(&self) -> usize {
        self.tel.len()
    }

    /// `y… p => %rec y…`, in a context of `depth` variables.
    fn adapter(&self, depth: usize) -> Term {
        let k = self.arity();
        let inner = depth + k;
        let call = apps(
            var(inner, self.level),
            (0..k - 1).map(|j| (var(inner, depth + j), self.tel[j].icit)),
        );
        let names: Vec<(Name, Icit)> = self.tel.iter().map(|b| (b.name.clone(), b.icit)).collect();
        lams(&names, call)
    }

    /// `t` (`depth` variables deep) with each recursive call's proof dropped
    /// and `%rec` anywhere else as [`Rec::adapter`].
    fn adapt(&self, g: &Ev, t: &Term, depth: usize) -> Result<Term> {
        g.machine.budget.nesting(super::PASS)?;
        let rec = depth - 1 - self.level;
        if let Term::App(..) = t {
            let (head, args) = spine_owned(t);
            if matches!(head, Term::Var(ix) if ix == rec) && args.len() >= self.arity() {
                let mut out = head;
                for (j, (a, icit)) in args.iter().enumerate() {
                    if j + 1 != self.arity() {
                        out = Term::app_icit(out, self.adapt(g, a, depth)?, *icit);
                    }
                }
                return Ok(out);
            }
        }
        match t {
            Term::Var(ix) if *ix == rec => Ok(self.adapter(depth)),
            _ => children(t, depth, &mut |c, d| self.adapt(g, c, d)),
        }
    }
}

impl Lemmas {
    fn new(g: &Ev) -> Result<Lemmas> {
        let r = &g.env.registry();
        let def = |b: Builtin| {
            r.def(b)
                .ok_or_else(|| internal_error(&format!("`{}` isn't loaded", b.name())))
        };
        Ok(Lemmas {
            elim: def(Builtin::ElimDec)?,
            ite: def(Builtin::IfThenElse)?,
            to_bool: def(Builtin::ToBool)?,
            dec_true: def(Builtin::DecTrue)?,
            comparisons: [
                Builtin::DecLessEqNat,
                Builtin::DecLessThanNat,
                Builtin::DecLessEqInt,
                Builtin::DecLessThanInt,
                Builtin::FloatDecLessEq,
                Builtin::FloatDecLessThan,
            ]
            .into_iter()
            .filter_map(|b| r.loaded_def(b))
            .collect(),
            elim_if: def(Builtin::ElimDecIf)?,
            true_if: def(Builtin::ElimDecTrueIf)?,
            elim_cong: def(Builtin::ElimDecCong)?,
            if_cong: def(Builtin::IfCong)?,
            twins: HashMap::default(),
        })
    }

    fn is(&self, head: &Term, id: DefId) -> bool {
        matches!(head, Term::Def(d) if *d == id)
    }

    /// Which lemma shows that deciding with `d` is the plain `if` on `b`.
    fn kind(&self, b: &Term, d: &Term) -> Option<Kind> {
        let (bh, bargs) = spine_owned(b);
        if self.is(&bh, self.to_bool)
            && let Some((d2, _)) = bargs.last()
            && same_term(d2, d)
        {
            return Some(Kind::ToBool);
        }
        let (dh, dargs) = spine_owned(d);
        if self.is(&dh, self.dec_true)
            && let [(c, _)] = &dargs[..]
            && same_term(c, b)
        {
            return Some(Kind::DecTrue);
        }
        // A comparison's decision is `Bool.decTrue` of the `Bool` its plain
        // `if` is on (`bind::comparison`), by definition.
        if let Term::Def(id) = dh
            && self.comparisons.contains(&id)
            && dargs.len() == 2
        {
            return Some(Kind::DecTrue);
        }
        // Both found with the operands bound, `(x… => b') ops…` and `(x… =>
        // d') ops…` (`bind::Bound`): as `b'` and `d'` are.
        if !bargs.is_empty()
            && bargs.len() == dargs.len()
            && bargs
                .iter()
                .zip(&dargs)
                .all(|((x, _), (y, _))| same_term(x, y))
        {
            let body = |head: &Term| -> Option<Term> {
                let mut t = match head.strip_loc() {
                    Term::Ann(e, _) => e.strip_loc().clone(),
                    t => t.clone(),
                };
                for _ in 0..bargs.len() {
                    t = match &t {
                        Term::Lam(_, _, body) => body.strip_loc().clone(),
                        _ => return None,
                    };
                }
                Some(t)
            };
            return self.kind(&body(&bh)?, &body(&dh)?);
        }
        None
    }

    /// `t` with the tags kept only on `if`s `f.%plain` can show plainly and
    /// `f.%plain.%same` can prove so; `count` counts those. `allowed`: the
    /// proof reaches `t`'s position.
    /// `root`: `t` is a whole leaf, a branch of an `if` or the body of a
    /// `let` that is, where a `let` can be gone through.
    #[allow(clippy::too_many_arguments)]
    fn mark(
        &self,
        g: &Ev,
        t: &Term,
        depth: usize,
        allowed: bool,
        root: bool,
        count: &mut usize,
    ) -> Result<Term> {
        g.machine.budget.nesting(super::PASS)?;
        let work = |t: &Term| {
            t.subterms().any(|(t, _)| match t {
                Term::Let(name, ..) => &**name == PLAIN,
                Term::Def(d) => self.twins.contains_key(d),
                _ => false,
            })
        };
        if !work(t) {
            return Ok(t.clone());
        }
        let (head, args) = spine_owned(t);
        if allowed
            && let Term::Def(h) = head
            && let Some(twin) = self.twins.get(&h)
            && args.len() == twin.arity
            && unadapt(&args[twin.rec].0, twin.rec_arity).is_some()
        {
            // Its arguments are left as `f.%step` has them, so the twin's
            // lemma is all the proof needs here.
            let args = (args.iter())
                .map(|(a, icit)| Ok((self.mark(g, a, depth, false, false, count)?, *icit)))
                .collect::<Result<Vec<_>>>()?;
            *count += 1;
            let call = apps(head, args).shift(g, 1, 0)?;
            return Ok(Term::let_(TWIN.into(), Term::Refl, Term::Refl, call));
        }
        let branch = |this: &Lemmas, a: &Term, count: &mut usize| -> Result<Term> {
            match a.strip_loc() {
                Term::Lam(x, i, body) => Ok(Term::Lam(
                    x.clone(),
                    *i,
                    Rc::new(this.mark(g, body, depth + 1, allowed, true, count)?),
                )),
                other => this.mark(g, other, depth, false, false, count),
            }
        };
        if self.is(&head, self.elim) && args.len() == 5 {
            let (decision, tag) = match untag(g, &args[2].0)? {
                Some((b, d)) => (d, Some(b)),
                None => (args[2].0.clone(), None),
            };
            let decision = self.mark(g, &decision, depth, false, false, count)?;
            let y = branch(self, &args[3].0, count)?;
            let n = branch(self, &args[4].0, count)?;
            // As `f.%plain` has them: a twin's call there may leave out a
            // fact the branch's `match` was passed.
            let unused = |b: &Term| -> Result<bool> {
                Ok(matches!(&self.post(g, b)?, Term::Lam(_, _, body) if !body.mentions(0)))
            };
            let decision = match tag {
                Some(b)
                    if allowed
                        && unused(&y)?
                        && unused(&n)?
                        && self.kind(&b, &decision).is_some() =>
                {
                    *count += 1;
                    let bool_ty = Term::Data(
                        g.env
                            .registry()
                            .data(Builtin::Bool)
                            .ok_or_else(|| internal_error("`Bool` isn't loaded"))?,
                        Vec::new(),
                    );
                    Term::let_(PLAIN.into(), bool_ty, b, decision.shift(g, 1, 0)?)
                }
                _ => decision,
            };
            return Ok(apps(
                head,
                [
                    args[0].clone(),
                    args[1].clone(),
                    (decision, args[2].1),
                    (y, args[3].1),
                    (n, args[4].1),
                ],
            ));
        }
        if self.is(&head, self.ite) && args.len() == 4 {
            let cond = self.mark(g, &args[1].0, depth, false, false, count)?;
            let t = branch(self, &args[2].0, count)?;
            let e = branch(self, &args[3].0, count)?;
            return Ok(apps(
                head,
                [
                    args[0].clone(),
                    (cond, args[1].1),
                    (t, args[2].1),
                    (e, args[3].1),
                ],
            ));
        }
        match t {
            Term::Loc(s, inner) => Ok(Term::Loc(
                *s,
                Rc::new(self.mark(g, inner, depth, allowed, root, count)?),
            )),
            Term::App(f, a, icit) => {
                let arg_allowed = allowed && !matches!(a.strip_loc(), Term::Lam(..));
                let head_allowed = allowed && !matches!(f.strip_loc(), Term::Lam(..));
                Ok(Term::App(
                    Rc::new(self.mark(g, f, depth, head_allowed, false, count)?),
                    Rc::new(self.mark(g, a, depth, arg_allowed, false, count)?),
                    *icit,
                ))
            }
            Term::Ctor(d, c, fields) => Ok(Term::Ctor(
                *d,
                *c,
                fields
                    .iter()
                    .map(|f| {
                        let ok = allowed && !matches!(f.strip_loc(), Term::Lam(..));
                        Ok(Rc::new(self.mark(g, f, depth, ok, false, count)?))
                    })
                    .collect::<Result<_>>()?,
            )),
            Term::Ann(e, ty) => Ok(Term::Ann(
                Rc::new(self.mark(g, e, depth, allowed, false, count)?),
                Rc::new(self.mark(g, ty, depth, false, false, count)?),
            )),
            Term::Let(x, ty, v, b, e) => Ok(Term::Let(
                x.clone(),
                Rc::new(self.mark(g, ty, depth, false, false, count)?),
                Rc::new(self.mark(g, v, depth, false, false, count)?),
                Rc::new(self.mark(g, b, depth + 1, allowed && root, root, count)?),
                *e,
            )),
            _ => children(t, depth, &mut |c, d| {
                self.mark(g, c, d, false, false, count)
            }),
        }
    }

    /// [`Lemmas::mark`] for the step's own case tree, whose leaves the
    /// proof reaches.
    fn mark_tree(&self, g: &Ev, t: &Term, depth: usize, count: &mut usize) -> Result<Term> {
        match t {
            Term::Loc(s, inner) => Ok(Term::Loc(
                *s,
                Rc::new(self.mark_tree(g, inner, depth, count)?),
            )),
            Term::Case(..) | Term::NumCase(..) => {
                children(t, depth, &mut |c, d| self.mark_tree(g, c, d, count))
            }
            _ => self.mark(g, t, depth, true, true, count),
        }
    }

    /// `t` as `f.%step` has it: every tag dropped.
    fn pre(&self, g: &Ev, t: &Term) -> Result<Term> {
        Ok(t.rewrite_up(g, &mut |node| {
            if let Some(call) = twin_call(g, node)? {
                return Ok(Some(call));
            }
            let (head, args) = spine_owned(node);
            if !self.is(&head, self.elim) || args.len() != 5 {
                return Ok(None);
            }
            let Some((_, decision)) = untag(g, &args[2].0)? else {
                return Ok(None);
            };
            let mut args = args;
            args[2].0 = decision;
            Ok(Some(apps(head, args)))
        })?)
    }

    /// `t` as `f.%plain` has it: every tagged `if` the plain `if`.
    fn post(&self, g: &Ev, t: &Term) -> Result<Term> {
        Ok(t.rewrite_up(g, &mut |node| {
            if let Some(call) = twin_call(g, node)? {
                // `mark` made sure the call has `%rec` as `y… p => r y…`.
                let Some((args, twin)) = self.twin_of(&call) else {
                    return Ok(Some(call));
                };
                let Some(r) = unadapt(&args[twin.rec].0, twin.rec_arity) else {
                    return Ok(Some(call));
                };
                let args = (twin.kept.iter()).map(|&i| {
                    if i == twin.rec {
                        (r.clone(), args[i].1)
                    } else {
                        args[i].clone()
                    }
                });
                return Ok(Some(apps(Term::Def(twin.twin), args)));
            }
            let (head, args) = spine_owned(node);
            if !self.is(&head, self.elim) || args.len() != 5 {
                return Ok(None);
            }
            let Some((b, _)) = untag(g, &args[2].0)? else {
                return Ok(None);
            };
            let head = Term::app_icit(Term::Def(self.ite), args[1].0.clone(), Icit::Implicit);
            Ok(Some(Term::app(
                Term::app(Term::app(head, b), args[3].0.clone()),
                args[4].0.clone(),
            )))
        })?)
    }

    /// A proof that `t` (marked, of type `ty`, `depth` variables deep) as
    /// `f.%step` has it equals `t` as `f.%plain` has it; `None` if they're
    /// the same.
    fn proof(&self, g: &Ev, t: &Term, ty: &Term, depth: usize) -> Result<Option<Term>> {
        g.machine.budget.nesting(super::PASS)?;
        if !tagged(t) {
            return Ok(None);
        }
        if let Some(p) = self.hole_proof(g, t, Some(ty), depth)? {
            return Ok(Some(p));
        }
        let mut holes = Vec::new();
        let part = self.part(g, t, depth, &mut holes)?;
        let ty2 = ty.shift(g, 2, 0)?;
        let pre2 = self.pre(g, t)?.shift(g, 2, 0)?;
        let mut proof = Term::Refl;
        for i in 0..holes.len() {
            let rhs = rebuild(g, &part, &holes, i, 2, &Term::Var(1))?;
            let motive = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Lam(
                    "p".into(),
                    Icit::Explicit,
                    Rc::new(Term::Eq(
                        Some(Rc::new(ty2.clone())),
                        Rc::new(pre2.clone()),
                        Rc::new(rhs),
                    )),
                )),
            );
            proof = Term::J(
                Rc::new(motive),
                Rc::new(proof),
                Rc::new(holes[i].proof.clone()),
            );
        }
        Ok(Some(proof))
    }

    /// `t` with its holes marked, each one's proof in `holes`.
    fn part(&self, g: &Ev, t: &Term, depth: usize, holes: &mut Vec<Hole>) -> Result<Part> {
        g.machine.budget.nesting(super::PASS)?;
        if !tagged(t) {
            return Ok(Part::Same(t.clone()));
        }
        if let Some(proof) = self.hole_proof(g, t, None, depth)? {
            holes.push(Hole {
                pre: self.pre(g, t)?,
                post: self.post(g, t)?,
                proof,
            });
            return Ok(Part::Hole(holes.len() - 1));
        }
        Ok(match t {
            Term::Loc(s, inner) => Part::Loc(*s, Box::new(self.part(g, inner, depth, holes)?)),
            Term::Ann(e, ty) => {
                Part::Ann(Box::new(self.part(g, e, depth, holes)?), self.pre(g, ty)?)
            }
            Term::App(f, a, icit) => Part::App(
                Box::new(self.part(g, f, depth, holes)?),
                Box::new(self.part(g, a, depth, holes)?),
                *icit,
            ),
            Term::Ctor(d, c, fields) => Part::Ctor(
                *d,
                *c,
                fields
                    .iter()
                    .map(|f| self.part(g, f, depth, holes))
                    .collect::<Result<_>>()?,
            ),
            _ => return Err(internal_error("a plain `if` where its proof can't reach")),
        })
    }

    /// The head, arguments and twin of `call`, a call [`Lemmas::mark`]
    /// marked.
    fn twin_of(&self, call: &Term) -> Option<(Vec<(Term, Icit)>, &Twin)> {
        let (head, args) = spine_owned(call);
        let Term::Def(h) = head else {
            return None;
        };
        let twin = self.twins.get(&h)?;
        (args.len() == twin.arity).then_some((args, twin))
    }

    /// A proof for `t` when it is one step of its own: a tagged `if`, an
    /// `if` around one, a marked call of a twin, or, where its type `ty` is
    /// known, a `let` around one.
    fn hole_proof(
        &self,
        g: &Ev,
        t: &Term,
        ty: Option<&Term>,
        depth: usize,
    ) -> Result<Option<Term>> {
        let t = t.strip_loc();
        if let Some(call) = twin_call(g, t)? {
            // H x… (y… p => r y…) … = H' …, H's lemma at the same arguments
            // but `r` for `%rec`.
            let (mut args, twin) = (self.twin_of(&call))
                .ok_or_else(|| internal_error("a marked call that isn't of a twin"))?;
            args[twin.rec].0 = unadapt(&args[twin.rec].0, twin.rec_arity)
                .ok_or_else(|| internal_error("a twin's call without its `%rec`"))?;
            return Ok(Some(apps(Term::Def(twin.same), args)));
        }
        if let (Term::Let(x, vty, v, b, e), Some(ty)) = (t, ty) {
            let inner = self.proof(g, b, &ty.shift(g, 1, 0)?, depth + 1)?;
            return Ok(inner.map(|p| Term::Let(x.clone(), vty.clone(), v.clone(), Rc::new(p), *e)));
        }
        let (head, args) = spine_owned(t);
        let branch_proof = |a: &Term, ty: &Term| -> Result<Term> {
            match a.strip_loc() {
                Term::Lam(x, _, body) => {
                    let p = self
                        .proof(g, body, &ty.shift(g, 1, 0)?, depth + 1)?
                        .unwrap_or(Term::Refl);
                    Ok(Term::Lam(x.clone(), Icit::Explicit, Rc::new(p)))
                }
                _ => Ok(Term::Lam("_".into(), Icit::Explicit, Rc::new(Term::Refl))),
            }
        };
        if self.is(&head, self.elim) && args.len() == 5 {
            let a = &args[1].0;
            let (sy, sn) = (branch_proof(&args[3].0, a)?, branch_proof(&args[4].0, a)?);
            let (y1, n1) = (self.pre(g, &args[3].0)?, self.pre(g, &args[4].0)?);
            let (y2, n2) = (self.post(g, &args[3].0)?, self.post(g, &args[4].0)?);
            if let Some((b, d)) = untag(g, &args[2].0)? {
                let kind = self
                    .kind(&b, &d)
                    .ok_or_else(|| internal_error("a plain `if` with no lemma"))?;
                let mut lemma_args = match kind {
                    Kind::ToBool => vec![
                        args[0].clone(),
                        (a.clone(), Icit::Implicit),
                        (self.pre(g, &d)?, Icit::Explicit),
                    ],
                    Kind::DecTrue => vec![(a.clone(), Icit::Implicit), (b, Icit::Explicit)],
                };
                lemma_args.extend(
                    [y1, n1, y2, n2, sy, sn]
                        .into_iter()
                        .map(|t| (t, Icit::Explicit)),
                );
                let lemma = match kind {
                    Kind::ToBool => self.elim_if,
                    Kind::DecTrue => self.true_if,
                };
                return Ok(Some(apps(Term::Def(lemma), lemma_args)));
            }
            if !tagged(&args[3].0) && !tagged(&args[4].0) {
                return Ok(None);
            }
            let mut lemma_args = vec![
                args[0].clone(),
                (a.clone(), Icit::Implicit),
                (args[2].0.clone(), Icit::Explicit),
            ];
            lemma_args.extend(
                [y1, y2, n1, n2, sy, sn]
                    .into_iter()
                    .map(|t| (t, Icit::Explicit)),
            );
            return Ok(Some(apps(Term::Def(self.elim_cong), lemma_args)));
        }
        if self.is(&head, self.ite) && args.len() == 4 {
            if !tagged(&args[2].0) && !tagged(&args[3].0) {
                return Ok(None);
            }
            let a = &args[0].0;
            let (st, se) = (branch_proof(&args[2].0, a)?, branch_proof(&args[3].0, a)?);
            let mut lemma_args = vec![
                (a.clone(), Icit::Implicit),
                (args[1].0.clone(), Icit::Explicit),
            ];
            lemma_args.extend(
                [
                    self.pre(g, &args[2].0)?,
                    self.post(g, &args[2].0)?,
                    self.pre(g, &args[3].0)?,
                    self.post(g, &args[3].0)?,
                    st,
                    se,
                ]
                .into_iter()
                .map(|t| (t, Icit::Explicit)),
            );
            return Ok(Some(apps(Term::Def(self.if_cong), lemma_args)));
        }
        Ok(None)
    }
}

/// The term `part` stands for, holes before `at` as `f.%plain` has them,
/// `at` itself `hole`, and the rest as `f.%step` has them, moved under
/// `shift` binders.
fn rebuild(
    g: &Ev,
    part: &Part,
    holes: &[Hole],
    at: usize,
    shift: usize,
    hole: &Term,
) -> Result<Term> {
    let go = |p: &Part| rebuild(g, p, holes, at, shift, hole);
    Ok(match part {
        Part::Same(t) => t.shift(g, shift, 0)?,
        Part::Hole(i) => match i.cmp(&at) {
            std::cmp::Ordering::Less => holes[*i].post.shift(g, shift, 0)?,
            std::cmp::Ordering::Equal => hole.clone(),
            std::cmp::Ordering::Greater => holes[*i].pre.shift(g, shift, 0)?,
        },
        Part::App(f, a, icit) => Term::App(Rc::new(go(f)?), Rc::new(go(a)?), *icit),
        Part::Ctor(d, c, fields) => Term::Ctor(
            *d,
            *c,
            fields
                .iter()
                .map(|f| Ok(Rc::new(go(f)?)))
                .collect::<Result<_>>()?,
        ),
        Part::Ann(inner, ty) => Term::Ann(Rc::new(go(inner)?), Rc::new(ty.shift(g, shift, 0)?)),
        Part::Loc(span, inner) => Term::Loc(*span, Rc::new(go(inner)?)),
    })
}

impl Elaborator {
    /// `f.%plain` and `f.%plain.%same` for `f.%step` (`step`), whose body
    /// with its plain `if`s still tagged is `tagged` (`None`: it has none),
    /// and the twins of the `match`es lifted from it (`helpers`), which are
    /// pushed to `made`; `None` when nothing can be shown plainly.
    pub(super) fn plain_view(
        &mut self,
        plan: &Plan,
        step: DefId,
        tagged: Option<&Term>,
        helpers: &[DefId],
        made: &mut Vec<DefId>,
    ) -> Result<Option<PlainView>> {
        let g = &self.ev();
        let mut l = Lemmas::new(g)?;
        for &h in helpers {
            if let Some(twin) = self.twin(&l, h, helpers)? {
                made.extend([twin.twin, twin.same]);
                l.twins.insert(h, twin);
            }
        }
        let g = &self.ev();
        let body = match tagged {
            Some(t) => t.clone(),
            None if l.twins.is_empty() => return Ok(None),
            None => (g.def(step).body())
                .ok_or_else(|| internal_error("a step without a body"))?
                .as_ref()
                .clone(),
        };
        let a = plan.n() + 1;
        let (tel, result) = split_pis(g.def(step).ty(), Some(a));
        if tel.len() != a {
            return Err(internal_error(
                "a step whose type doesn't show its parameters",
            ));
        }
        let name = |suffix: &str| -> Name { format!("{}.{suffix}", plan.name).into() };
        let Some(made_view) = self.plain_def(
            &l,
            &tel,
            &result,
            plan.header,
            step,
            &body,
            false,
            &name("%plain"),
            plan.span,
        )?
        else {
            return Ok(None);
        };
        Ok(Some(PlainView {
            view: made_view.twin,
            same: made_view.same,
        }))
    }

    /// The twin of `h`, a `match` lifted from the step, if its arms call
    /// `%rec` and the twin differs from it: it drops a parameter, or calls
    /// a twin itself. `helpers`: all those lifted from the step (one that
    /// calls itself or one after it, in a group, gets none).
    fn twin(&mut self, l: &Lemmas, h: DefId, helpers: &[DefId]) -> Result<Option<Twin>> {
        let g = &self.ev();
        let def = g.def(h);
        let Some(body) = def.body().cloned() else {
            return Ok(None);
        };
        // With its plain `if`s still tagged, if it has any (and the record
        // is of this helper, not of one an abandoned attempt made).
        let recorded = (self.decl.decreasing.borrow().as_ref())
            .and_then(|a| a.tagged_helpers.borrow().get(&h).cloned());
        let body = match recorded {
            Some(tagged) if same_term(&self.settle_tagged(&tagged)?, &body) => Rc::new(tagged),
            _ => body,
        };
        let g = &self.ev();
        let def = g.def(h);
        if body
            .subterms()
            .any(|(t, _)| matches!(t, Term::Def(d) if *d >= h && helpers.contains(d)))
        {
            return Ok(None);
        }
        let arity = body.count_lams();
        let (tel, result) = split_pis(def.ty(), Some(arity));
        if tel.len() != arity {
            return Ok(None);
        }
        let Some(rec) = tel.iter().position(|b| &*b.name == super::REC) else {
            return Ok(None);
        };
        let name: Name = format!("{}.%plain", def.name()).into();
        let lifted = (self.tables.lifted.iter())
            .find(|(id, _)| *id == h)
            .map(|(_, span)| *span);
        let span = lifted.unwrap_or(def.span());
        let Some(made) = self.plain_def(l, &tel, &result, rec, h, &body, true, &name, span)? else {
            return Ok(None);
        };
        if let Some(span) = lifted {
            self.tables.lifted.push((made.twin, span));
        }
        Ok(Some(made))
    }

    /// The plain form of a definition with parameters `tel`, result type
    /// `result` and body `body` (its lambdas around a case tree), whose
    /// parameter `rec` is `%rec`: `name`, the same with `%rec` taking no
    /// proof and its plain `if`s and twins' calls plain, and `name.%same`,
    /// that the definition with `y… p => r y…` for `%rec` is it with `r`.
    /// With `drop`, parameters the plain body doesn't need are left out
    /// (a lifted `match`'s); `None` if it would be the definition itself.
    #[allow(clippy::too_many_arguments)]
    fn plain_def(
        &mut self,
        l: &Lemmas,
        tel: &[Binder],
        result: &Term,
        rec_at: usize,
        orig: DefId,
        body: &Term,
        drop: bool,
        name: &Name,
        span: Span,
    ) -> Result<Option<Twin>> {
        let g = &self.ev();
        let a = tel.len();
        let (rec_tel, rec_result) = split_pis(&tel[rec_at].ty, None);
        if rec_tel.last().is_none_or(|b| b.icit != Icit::Auto) {
            return Err(internal_error("a recursive call's type without its proof"));
        }
        let rec = Rec {
            level: rec_at,
            tel: rec_tel,
        };
        let tree = Term::peel_lams_rc(&Rc::new(body.clone()), a);
        let adapted = dead_lets(g, &rec.adapt(g, &tree, a)?)?;
        let mut count = 0;
        let marked = l.mark_tree(g, &adapted, a, &mut count)?;
        let post = l.post(g, &marked)?;
        // `%rec` without its proof: `(y…) -> B`.
        let k = rec.arity();
        let plain_rec = pis(&rec.tel[..k - 1], instantiate(g, &rec_result, &Term::Refl)?);
        let mut view_tel = tel.to_vec();
        view_tel[rec_at].ty = plain_rec;
        // What the plain body needs: `%rec`, what it mentions, and what the
        // types of those and of the result mention.
        let mut needed = vec![!drop; a];
        needed[rec_at] = true;
        for (i, need) in needed.iter_mut().enumerate() {
            *need |= post.mentions(a - 1 - i) || result.mentions(a - 1 - i);
        }
        for j in (0..a).rev() {
            if needed[j] {
                let ty = &view_tel[j].ty;
                for (i, need) in needed[..j].iter_mut().enumerate() {
                    *need |= ty.mentions(j - 1 - i);
                }
            }
        }
        let kept: Vec<usize> = (0..a).filter(|&i| needed[i]).collect();
        if count == 0 && kept.len() == a {
            return Ok(None);
        }
        let new_level = |l: usize| kept.iter().position(|&k| k == l).unwrap_or(0);
        let twin_tel = (kept.iter().enumerate())
            .map(|(j, &i)| {
                Ok(Binder {
                    name: view_tel[i].name.clone(),
                    icit: view_tel[i].icit,
                    ty: super::reindex(g, &view_tel[i].ty, i, j, &new_level)?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let twin_result = super::reindex(g, result, a, kept.len(), &new_level)?;
        let twin = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            name,
            &pis(&twin_tel, twin_result),
            false,
            false,
            span,
        )?;
        let g = &self.ev();
        let names = |tel: &[Binder]| -> Vec<(Name, Icit)> {
            tel.iter().map(|b| (b.name.clone(), b.icit)).collect()
        };
        let twin_body = super::reindex(g, &post, a, kept.len(), &new_level)?;
        kernel::define_group(
            &mut self.kernel,
            &self.tables,
            &[(twin, lams(&names(&twin_tel), twin_body))],
        )?;
        // H x… (y… p => r y…) … = H' (those of x… r … it takes)
        let lhs = apps(
            Term::Def(orig),
            (0..a).map(|i| {
                let t = if i == rec_at {
                    rec.adapter(a)
                } else {
                    var(a, i)
                };
                (t, tel[i].icit)
            }),
        );
        let rhs = apps(
            Term::Def(twin),
            kept.iter().map(|&i| (var(a, i), tel[i].icit)),
        );
        let same_ty = pis(&view_tel, Term::Eq(None, Rc::new(lhs), Rc::new(rhs)));
        let same_name: Name = format!("{name}.%same").into();
        let same = kernel::declare_def(
            &mut self.kernel,
            &self.tables,
            &self.unit,
            &same_name,
            &same_ty,
            true,
            false,
            span,
        )?;
        let g = &self.ev();
        let proof = l.tree_proof(g, &marked, result, a, a)?;
        kernel::define_group(
            &mut self.kernel,
            &self.tables,
            &[(same, lams(&names(&view_tel), proof))],
        )?;
        Ok(Some(Twin {
            twin,
            same,
            arity: a,
            rec: rec_at,
            rec_arity: k,
            kept,
        }))
    }
}

impl Lemmas {
    /// The proof of `f.%plain.%same` for the step's case tree `t`, `depth`
    /// variables deep, the result type `result` in the context of the `a`
    /// parameters: the same tree, each leaf by [`Lemmas::proof`].
    fn tree_proof(&self, g: &Ev, t: &Term, result: &Term, a: usize, depth: usize) -> Result<Term> {
        g.machine.budget.nesting(super::PASS)?;
        Ok(match t {
            Term::Loc(s, inner) => {
                Term::Loc(*s, Rc::new(self.tree_proof(g, inner, result, a, depth)?))
            }
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
                                .map(|body| {
                                    Ok::<_, stitchwort_syntax::Diagnostic>(Rc::new(
                                        self.tree_proof(g, body, result, a, depth + b.names.len())?,
                                    ))
                                })
                                .transpose()?,
                        })
                    })
                    .collect::<Result<_>>()?,
            ),
            Term::NumCase(ix, arms, default) => Term::NumCase(
                *ix,
                arms.iter()
                    .map(|arm| {
                        Ok(NumArm {
                            value: arm.value.clone(),
                            body: Rc::new(self.tree_proof(g, &arm.body, result, a, depth)?),
                        })
                    })
                    .collect::<Result<_>>()?,
                Rc::new(self.tree_proof(g, default, result, a, depth)?),
            ),
            leaf => {
                let ty = result.shift(g, depth - a, 0)?;
                self.proof(g, leaf, &ty, depth)?.unwrap_or(Term::Refl)
            }
        })
    }
}
