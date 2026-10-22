//! `decreasing`: recursion justified by a measure, compiled to fuel that
//! carries its own proof of being enough (docs/proposals/well-founded-recursion.md,
//! option B, stage 1). The kernel sees only structural recursion.
//!
//! For `def f (x: A) (c: C): B decreasing m x := body` (the header's
//! parameters `x`, the measure's; `c`, any after the colon), the compiler
//! makes:
//!
//! 1. `f.%step (x: A) (%rec: (y: A) -> (c: C) -> [auto decreasing: m y < m x] -> B) (c: C): B`,
//!    the body as written, elaborated with each recursive call `f y c'`
//!    standing for `%rec y c'`, whose `decreasing` argument is found by
//!    `auto` or given as `[decreasing := p]`. It isn't recursive.
//! 2. `f.%go (k: Nat) (x: A) (c: C) (h: m x < k): B`, structural on `k`:
//!    `Zero` is impossible (`m x < 0`), and `Succ k` is `f.%step` with
//!    `%rec` = `y c' p => f.%go k y c' (Nat.leTrans … p h)`.
//! 3. `f (x: A) (c: C): B := f.%go (Succ (m x)) x c (Nat.leRefl (m x))`,
//!    marked to stay folded until something takes it apart, so a goal
//!    shows `f x c`, not the fuel.
//! 4. `f.%step.%respects`: `f.%step` gives equal results for two `%rec`s
//!    that agree everywhere (and the same for each `match` lifted from it
//!    that uses `%rec`), by the same case tree, each leaf by rewriting one
//!    recursive call at a time (`J`), through an `if` by
//!    `Decidable.elimCong`/`Bool.ifThenElseCong`.
//! 5. `f.%irrel`: the amount of fuel doesn't matter, by induction on it.
//! 6. `f.unfold (x: A) (c: C): f x c = f.%step x (y c' => f y c') c`, the
//!    definition's own equation (Lean's `f.eq_def`).
//!
//! The runtimes run `f.%step x (y c' => f y c') c` instead of the fuelled
//! body ([`stitchwort_core::globals::Def::run_body`]). A `theorem` gets 1 to
//! 3 only: its proof recurses on the measure, and nothing unfolds it.

use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{eval, force};
use stitchwort_core::{DataId, DefId, Globals, Icit, Name, Term, Value};
use stitchwort_syntax::ast::{self, Decl, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, check};
use crate::{Elaborator, Global, Result, kernel, scope};

/// The parameter of `f.%step` that recursive calls stand for.
pub(crate) const REC: &str = "%rec";

/// The name of the auto parameter a recursive call's proof is passed as:
/// `[decreasing := p]`.
const PROOF: &str = "decreasing";

const PASS: &str = "decreasing";

/// While the body of a definition with `decreasing` is elaborated: which
/// definition a recursive call names, and what its measure is, for the
/// message when a call's obligation can't be proved.
pub(crate) struct Active {
    pub target: DefId,
    /// Whether the body calls the definition at all.
    pub used: Cell<bool>,
    /// The measure of the definition's own parameters (the first `header`
    /// variables of the body's context).
    pub measure: Term,
    pub header: usize,
}

/// A parameter in a telescope: its name, how it's passed, and its type (in
/// the context of the ones before it).
#[derive(Clone)]
struct Binder {
    name: Name,
    icit: Icit,
    ty: Term,
}

/// The first `count` parameters of type `ty` (all of them if `None`), and
/// what's left.
fn split_pis(ty: &Term, count: Option<usize>) -> (Vec<Binder>, Term) {
    let mut binders = Vec::new();
    let mut ty = ty.strip_loc();
    while count.is_none_or(|c| binders.len() < c) {
        let Term::Pi(name, icit, dom, cod) = ty else {
            break;
        };
        binders.push(Binder {
            name: name.clone(),
            icit: *icit,
            ty: (**dom).clone(),
        });
        ty = cod.strip_loc();
    }
    (binders, ty.clone())
}

fn pis(binders: &[Binder], body: Term) -> Term {
    binders.iter().rev().fold(body, |body, b| {
        Term::Pi(b.name.clone(), b.icit, Rc::new(b.ty.clone()), Rc::new(body))
    })
}

fn lams(binders: &[(Name, Icit)], body: Term) -> Term {
    binders.iter().rev().fold(body, |body, (x, icit)| {
        Term::Lam(x.clone(), *icit, Rc::new(body))
    })
}

fn apps(head: Term, args: impl IntoIterator<Item = (Term, Icit)>) -> Term {
    args.into_iter()
        .fold(head, |f, (a, icit)| Term::app_icit(f, a, icit))
}

fn explicit(args: impl IntoIterator<Item = Term>) -> Vec<(Term, Icit)> {
    args.into_iter().map(|a| (a, Icit::Explicit)).collect()
}

/// The variable at `level` in a context of `depth` variables.
fn var(depth: usize, level: usize) -> Term {
    Term::Var(depth - 1 - level)
}

/// Rebuilds `t`, a term `depth` binders deep, with `f(index, binders)`
/// for each variable, where `binders` is how many binders inside `t` it's
/// under. A `case` must stay on a variable.
fn map_vars(
    g: &Globals,
    t: &Term,
    depth: usize,
    f: &dyn Fn(usize, usize) -> Result<Term>,
) -> Result<Term> {
    g.budget.nesting(PASS)?;
    let go = |t: &Rc<Term>, d: usize| -> Result<Rc<Term>> { Ok(Rc::new(map_vars(g, t, d, f)?)) };
    let scrutinee = |ix: usize| -> Result<usize> {
        match f(ix, depth)? {
            Term::Var(new) => Ok(new),
            _ => Err(internal_error(
                "a `case` on a variable that isn't one any more",
            )),
        }
    };
    Ok(match t {
        Term::Var(ix) => f(*ix, depth)?,
        Term::Def(_)
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
            scrutinee(*ix)?,
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
            scrutinee(*ix)?,
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
        Term::Loc(span, t) => Term::Loc(*span, go(t, depth)?),
    })
}

/// `t`, a term in a context of `src` variables, moved to a context of `tgt`
/// variables where the variable at level `l` is at level `map(l)`.
fn reindex(
    g: &Globals,
    t: &Term,
    src: usize,
    tgt: usize,
    map: &dyn Fn(usize) -> usize,
) -> Result<Term> {
    map_vars(g, t, 0, &|ix, d| {
        Ok(if ix < d {
            Term::Var(ix)
        } else {
            let level = src - 1 - (ix - d);
            Term::Var(tgt - 1 - map(level) + d)
        })
    })
}

/// `t` with the variable at level `from` replaced by the one at `to`, in a
/// context of `depth` variables.
fn rename(g: &Globals, t: &Term, depth: usize, from: usize, to: usize) -> Result<Term> {
    reindex(g, t, depth, depth, &|l| if l == from { to } else { l })
}

/// `body`, under one binder, with `value` (outside it) for that binder.
fn instantiate(g: &Globals, body: &Term, value: &Term) -> Result<Term> {
    map_vars(g, body, 0, &|ix, d| {
        Ok(if ix < d {
            Term::Var(ix)
        } else if ix == d {
            value.shift(g, d, 0)?
        } else {
            Term::Var(ix - 1)
        })
    })
}

/// `t` with every `let` replaced by its value (they're transparent, so this
/// changes no meaning): the proofs rewrite under them.
fn zeta(g: &Globals, t: &Term) -> Result<Term> {
    g.budget.nesting(PASS)?;
    let go = |t: &Rc<Term>| -> Result<Rc<Term>> { Ok(Rc::new(zeta(g, t)?)) };
    Ok(match t {
        Term::Let(_, _, v, b, _) => {
            let v = zeta(g, v)?;
            let b = zeta(g, b)?;
            instantiate(g, &b, &v)?
        }
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => t.clone(),
        Term::Data(d, args) => Term::Data(*d, args.iter().map(go).collect::<Result<_>>()?),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, args.iter().map(go).collect::<Result<_>>()?),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a)?, go(b)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b)?),
        Term::App(a, b, i) => Term::App(go(a)?, go(b)?, *i),
        Term::Ann(a, b) => Term::Ann(go(a)?, go(b)?),
        Term::Eq(ty, a, b) => Term::Eq(ty.as_ref().map(go).transpose()?, go(a)?, go(b)?),
        Term::J(m, b, p) => Term::J(go(m)?, go(b)?, go(p)?),
        Term::Loc(span, inner) => Term::Loc(*span, go(inner)?),
        Term::Case(..) | Term::NumCase(..) => t.clone(),
    })
}

/// `f a b c` as `f` and its arguments with how each is passed, looking
/// through locations.
fn spine(t: &Term) -> (&Term, Vec<(&Term, Icit)>) {
    let mut args = Vec::new();
    let mut head = t.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push((a.as_ref(), *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}

fn internal_error(message: &str) -> Diagnostic {
    Diagnostic::error("E-DECREASING", format!("internal error: {message}"))
}

/// The definitions `decreasing` refers to, from the core.
struct Prelude {
    nat: DataId,
    succ: usize,
    less_than: DefId,
    le_trans: DefId,
    le_refl: DefId,
    absurd: DefId,
    exfalso: DefId,
    false_not_true: DefId,
    elim: DefId,
    elim_cong: DefId,
    if_then_else: DefId,
    if_cong: DefId,
}

impl Prelude {
    fn new(g: &Globals) -> Result<Prelude> {
        let r = &g.registry;
        let missing = || {
            Diagnostic::error(
                "E-DECREASING",
                "`decreasing` needs the prelude, which isn't loaded",
            )
        };
        let def = |b: Builtin| r.def(b).ok_or_else(missing);
        let (nat_succ, succ) = r.ctor(Builtin::Succ).ok_or_else(missing)?;
        Ok(Prelude {
            nat: nat_succ,
            succ,
            less_than: def(Builtin::LessThan)?,
            le_trans: def(Builtin::LeTrans)?,
            le_refl: def(Builtin::LeRefl)?,
            absurd: def(Builtin::VoidAbsurd)?,
            exfalso: def(Builtin::VoidExfalso)?,
            false_not_true: def(Builtin::FalseNotTrue)?,
            elim: def(Builtin::ElimDec)?,
            elim_cong: def(Builtin::ElimDecCong)?,
            if_then_else: def(Builtin::IfThenElse)?,
            if_cong: def(Builtin::IfCong)?,
        })
    }

    fn succ(&self, n: Term) -> Term {
        Term::ctor(self.nat, self.succ, vec![n])
    }

    fn less(&self, a: Term, b: Term) -> Term {
        apps(Term::Def(self.less_than), explicit([a, b]))
    }
}

/// Everything about the definition being generated that doesn't change.
struct Plan {
    f: DefId,
    name: String,
    /// `f`'s parameters, all of them.
    tel: Vec<Binder>,
    /// Its result type, after them.
    result: Term,
    /// How many of `tel` are the header's: the measure's context.
    header: usize,
    /// The measure, in the context of `tel[..header]`.
    measure: Term,
    theorem: bool,
    span: Span,
    p: Prelude,
}

impl Plan {
    fn n(&self) -> usize {
        self.tel.len()
    }

    /// The measure of parameters at levels `level(0) … level(header - 1)`,
    /// in a context of `depth` variables.
    fn measure_at(
        &self,
        g: &Globals,
        depth: usize,
        level: &dyn Fn(usize) -> usize,
    ) -> Result<Term> {
        reindex(g, &self.measure, self.header, depth, level)
    }

    /// Parameter `i`'s type, with parameter `l` at level `level(l)`, in a
    /// context of `depth` variables.
    fn param_ty(
        &self,
        g: &Globals,
        i: usize,
        depth: usize,
        level: &dyn Fn(usize) -> usize,
    ) -> Result<Term> {
        reindex(g, &self.tel[i].ty, i, depth, level)
    }

    fn result_at(&self, g: &Globals, depth: usize, level: &dyn Fn(usize) -> usize) -> Result<Term> {
        reindex(g, &self.result, self.n(), depth, level)
    }

    /// The parameters as arguments: parameter `i` at level `level(i)`.
    fn args(
        &self,
        depth: usize,
        level: &dyn Fn(usize) -> usize,
        range: std::ops::Range<usize>,
    ) -> Vec<(Term, Icit)> {
        range
            .map(|i| (var(depth, level(i)), self.tel[i].icit))
            .collect()
    }

    /// The parameters again, as binders, starting at level `base`.
    fn binders(&self, g: &Globals, base: usize) -> Result<Vec<Binder>> {
        (0..self.n())
            .map(|i| {
                Ok(Binder {
                    name: self.tel[i].name.clone(),
                    icit: self.tel[i].icit,
                    ty: self.param_ty(g, i, base + i, &|l| base + l)?,
                })
            })
            .collect()
    }

    fn lam_names(&self) -> Vec<(Name, Icit)> {
        self.tel.iter().map(|b| (b.name.clone(), b.icit)).collect()
    }

    /// The type of `%rec` in a context of `depth` variables where the
    /// header's parameter `l` is at level `level(l)`.
    fn rec_ty(&self, g: &Globals, depth: usize, level: &dyn Fn(usize) -> usize) -> Result<Term> {
        let n = self.n();
        let ys = self.binders(g, depth)?;
        let inner = depth + n;
        let proof = Binder {
            name: PROOF.into(),
            icit: Icit::Auto,
            ty: self.p.less(
                self.measure_at(g, inner, &|l| depth + l)?,
                self.measure_at(g, inner, level)?,
            ),
        };
        let result = self.result_at(g, inner + 1, &|l| depth + l)?;
        Ok(pis(&ys, pis(&[proof], result)))
    }

    /// `y… p => go fuel y… (Nat.leTrans (Succ (m y)) (m x) fuel p hyp)`: what
    /// `%rec` is in `f.%go`, given `fuel` and `hyp: m x <= fuel` (terms in a
    /// context of `depth` variables, where `x`'s are at `level`).
    fn rec_lam(
        &self,
        g: &Globals,
        go: DefId,
        depth: usize,
        fuel: &Term,
        hyp: &Term,
        level: &dyn Fn(usize) -> usize,
    ) -> Result<Term> {
        let n = self.n();
        let inner = depth + n + 1;
        let fuel = fuel.shift(g, n + 1, 0)?;
        let hyp = hyp.shift(g, n + 1, 0)?;
        let glue = self.glue(g, inner, depth, Term::Var(0), &fuel, hyp, level)?;
        let call = apps(
            Term::Def(go),
            [(fuel, Icit::Explicit)]
                .into_iter()
                .chain(self.args(inner, &|l| depth + l, 0..n))
                .chain([(glue, Icit::Explicit)]),
        );
        let mut names = self.lam_names();
        names.push((PROOF.into(), Icit::Auto));
        Ok(lams(&names, call))
    }

    /// `Nat.leTrans (Succ (m y)) (m x) fuel p hyp: m y < fuel`, in a context
    /// of `depth` variables, the `y`s from level `ys`, the `x`s at `level`.
    #[allow(clippy::too_many_arguments)]
    fn glue(
        &self,
        g: &Globals,
        depth: usize,
        ys: usize,
        p: Term,
        fuel: &Term,
        hyp: Term,
        level: &dyn Fn(usize) -> usize,
    ) -> Result<Term> {
        Ok(apps(
            Term::Def(self.p.le_trans),
            explicit([
                self.p.succ(self.measure_at(g, depth, &|l| ys + l)?),
                self.measure_at(g, depth, level)?,
                fuel.clone(),
                p,
                hyp,
            ]),
        ))
    }

    /// From a proof of `False = True`, anything of type `goal`.
    fn absurd(&self, goal: Term, proof: Term) -> Term {
        let via = if self.theorem {
            self.p.exfalso
        } else {
            self.p.absurd
        };
        apps(
            Term::Def(via),
            [
                (goal, Icit::Implicit),
                (
                    Term::app(Term::Def(self.p.false_not_true), proof),
                    Icit::Explicit,
                ),
            ],
        )
    }
}

/// How a definition elaborated with `%rec` in it is told apart: the levels of
/// `r1`, `r2` and `e` in the context of a `respects` lemma's leaf.
#[derive(Clone, Copy)]
struct Leaf {
    depth: usize,
    r1: usize,
    r2: usize,
    e: usize,
    /// How many arguments a recursive call takes (with its proof).
    arity: usize,
}

impl Leaf {
    fn under(self, n: usize) -> Leaf {
        Leaf {
            depth: self.depth + n,
            ..self
        }
    }

    fn mentions(&self, t: &Term) -> bool {
        t.mentions(self.depth - 1 - self.r1)
    }
}

/// A part of a leaf, with the recursive calls in it marked (`Site`): what
/// the proof rewrites, one at a time.
enum Tpl {
    Plain(Term),
    Site(usize),
    /// A call of a helper lifted from the body that passes `%rec` on, as
    /// argument `rec`.
    Helper {
        site: usize,
        head: DefId,
        args: Vec<(Tpl, Icit)>,
        rec: usize,
    },
    App(Box<Tpl>, Box<Tpl>, Icit),
    Ctor(DataId, usize, Vec<Tpl>),
    Ann(Box<Tpl>, Term),
    Loc(Span, Box<Tpl>),
}

/// A recursive call to rewrite: the call as it is in the leaf (for a
/// helper's, unused), and a proof that it gives the same with `r2`.
struct Site {
    pre: Term,
    proof: Term,
}

#[derive(Clone, Copy, PartialEq)]
enum Choice {
    Pre,
    Post,
    Hole,
}

/// The state of generating the `respects` lemmas.
struct Gen {
    /// The definition's name, for messages.
    name: String,
    /// The helpers lifted from `f.%step`, which may pass `%rec` on.
    helpers: Vec<DefId>,
    /// Each helper's lemma, once declared.
    respects: HashMap<DefId, DefId>,
    /// The definitions generated, in order, for the module's records.
    made: Vec<DefId>,
}

impl Elaborator {
    /// A definition with `decreasing`, on its own (a group of one): its
    /// signature, then everything [the module's documentation](self) lists.
    pub(crate) fn decreasing_group(
        &mut self,
        members: &[(usize, &Decl, &[Decl])],
    ) -> Vec<(usize, Diagnostic)> {
        let (item, signature, equations) = members[0];
        let Decl::Signature {
            name,
            decreasing: Some(measure),
            theorem,
            span,
            ..
        } = signature
        else {
            unreachable!("only called for a signature with `decreasing`")
        };
        let mut out = Vec::new();
        self.module.item = Some(item);
        if members.len() > 1 {
            let names: Vec<String> = members
                .iter()
                .filter_map(|(_, s, _)| match s {
                    Decl::Signature { name, .. } => Some(format!("`{}`", name.text)),
                    _ => None,
                })
                .collect();
            out.push((
                item,
                Diagnostic::error(
                    "E-DECREASING",
                    "`decreasing` isn't supported for definitions that call each other yet",
                )
                .with_label(measure.span(), "this measure")
                .with_note(format!(
                    "{} call each other; give them a fuel argument for now",
                    names.join(", ")
                )),
            ));
            return out;
        }
        let result = self.signature(signature);
        out.extend(self.warnings.drain(..).map(|w| (item, w)));
        out.extend(self.lambda_warnings.take().into_iter().map(|w| (item, w)));
        let f = match result {
            Ok(id) => id,
            Err(d) => {
                out.push((item, d));
                return out;
            }
        };
        if let Ok(key) = self.declaration_key(name) {
            self.scope.insert(&key, Global::Def(f), name.span, false);
        }
        self.module.phase = crate::module::Phase::Body;
        self.local_helpers.clear();
        self.preadmitted.borrow_mut().clear();
        let result = self.decreasing_definition(f, name, measure, *theorem, *span, equations);
        *self.decreasing.borrow_mut() = None;
        out.extend(self.lambda_warnings.take().into_iter().map(|w| (item, w)));
        out.extend(self.warnings.drain(..).map(|w| (item, w)));
        match result {
            Ok(()) => {
                if let Err(d) = self.bind_local_helpers() {
                    out.push((item, d));
                }
                if let Err(d) = self.after_definition(signature, f) {
                    out.push((item, d));
                }
            }
            Err(d) => out.push((item, d)),
        }
        out
    }

    fn decreasing_definition(
        &mut self,
        f: DefId,
        def_name: &ast::Name,
        measure: &Expr,
        theorem: bool,
        span: Span,
        equations: &[Decl],
    ) -> Result<()> {
        let key = self.declaration_key(def_name)?;
        let display = scope::display(&key).to_string();
        let (tel, result) = split_pis(&self.globals.def(f).ty.clone(), None);
        // The header's parameters: those up to the last one the equations
        // name before their own patterns.
        let named = match equations.first() {
            Some(Decl::Equation { arm, patterns, .. }) => arm.unwrap_or(patterns.len()),
            _ => 0,
        };
        let mut header = 0;
        let mut explicit_seen = 0;
        while explicit_seen < named && header < tel.len() {
            if tel[header].icit == Icit::Explicit {
                explicit_seen += 1;
            }
            header += 1;
        }
        if named == 0 || explicit_seen < named {
            return Err(Diagnostic::error(
                "E-DECREASING",
                format!(
                    "`{}`'s measure needs the parameters it uses named in its header",
                    def_name.text
                ),
            )
            .with_label(measure.span(), "this measure")
            .with_note(format!(
                "write them before the colon: `def {} (n: Nat): … decreasing n`",
                def_name.text
            )));
        }
        // A recursive call inside a lambda has no proof that the lambda's
        // argument is smaller (§6.3): refused before anything is elaborated.
        for eq in equations {
            let Decl::Equation { rhs: Some(rhs), .. } = eq else {
                continue;
            };
            for n in crate::module::names_in_lambdas(rhs) {
                if matches!(self.named(&n.text), Some((Global::Def(id), _)) if *id == f) {
                    return Err(lambda_call(Some(n.span), &def_name.text));
                }
            }
        }
        let measure_term = self.measure_term(&key, &tel[..header], measure)?;
        let p = Prelude::new(&self.globals)?;
        let plan = Plan {
            f,
            name: display.clone(),
            tel,
            result,
            header,
            measure: measure_term,
            theorem,
            span,
            p,
        };
        // 1. The step.
        let step = self.decreasing_step(&plan, &key, def_name, equations)?;
        let first_helper = step.1;
        let step = step.0;
        let g = &self.globals;
        let n = plan.n();
        if g.def(step).arity != n + 1 {
            return Err(Diagnostic::error(
                "E-DECREASING",
                format!(
                    "`decreasing` needs `{}`'s body to take all its arguments",
                    def_name.text
                ),
            )
            .with_label(def_name.span, "its body returns a function")
            .with_note(
                "match every argument after the colon in its arms, or name them in the header",
            ));
        }
        let helpers: Vec<DefId> = (first_helper..self.globals.defs.len()).map(DefId).collect();
        let mut made = vec![step];
        // 2. The fuelled function.
        let go = self.generated(&plan, |e| e.decreasing_go(&plan, step))?;
        made.push(go);
        // 3. The function itself.
        {
            let g = &self.globals;
            let start = plan.p.succ(plan.measure_at(g, n, &|l| l)?);
            let refl = Term::app(Term::Def(plan.p.le_refl), plan.measure_at(g, n, &|l| l)?);
            let body = lams(
                &plan.lam_names(),
                apps(
                    Term::Def(go),
                    [(start, Icit::Explicit)]
                        .into_iter()
                        .chain(plan.args(n, &|l| l, 0..n))
                        .chain([(refl, Icit::Explicit)]),
                ),
            );
            kernel::mark_folded(&mut self.globals, f);
            self.generated_admit(&plan, &[(f, body)])?;
        }
        if !theorem {
            let mut st = Gen {
                name: def_name.text.clone(),
                helpers,
                respects: HashMap::new(),
                made: Vec::new(),
            };
            let respects = self.generated(&plan, |e| e.respects(&mut st, step, plan.header))?;
            made.extend(st.made.iter().copied());
            let irrel = self.generated(&plan, |e| e.decreasing_irrel(&plan, step, go, respects))?;
            made.push(irrel);
            let unfold = self.generated(&plan, |e| {
                e.decreasing_unfold(&plan, step, go, irrel, respects)
            })?;
            made.push(unfold);
            // What the runtimes run: the recursion as written.
            let g = &self.globals;
            let r_f = plan_rec_f(&plan, g, n)?;
            let run = lams(
                &plan.lam_names(),
                apps(
                    Term::Def(step),
                    plan.args(n, &|l| l, 0..plan.header)
                        .into_iter()
                        .chain([(r_f, Icit::Explicit)])
                        .chain(plan.args(n, &|l| l, plan.header..n)),
                ),
            );
            self.generated(&plan, |e| {
                kernel::set_run_body(&mut e.globals, f, &run)?;
                Ok(f)
            })?;
            // Named from outside as `f.unfold`, as a local definition is
            // (`dot::helper`).
            let unfold_key = format!("{key}.unfold");
            self.scope
                .insert(&unfold_key, Global::Def(unfold), def_name.span, false);
            self.helper_keys.insert(unfold_key);
        }
        if let Some(item) = self.module.item {
            for id in made {
                self.module.def_items.insert(id, item);
            }
        }
        let used = self
            .decreasing
            .borrow()
            .as_ref()
            .is_some_and(|a| a.used.get());
        if !used {
            self.warnings.push(
                Diagnostic::warning(
                    "W-DECREASING-UNUSED",
                    format!(
                        "`{}` never calls itself, so it doesn't need `decreasing`",
                        def_name.text
                    ),
                )
                .with_label(measure.span(), "this measure isn't needed"),
            );
        }
        Ok(())
    }

    /// The measure, elaborated in the context of the header's parameters: a
    /// `Nat`.
    fn measure_term(&mut self, key: &str, header: &[Binder], measure: &Expr) -> Result<Term> {
        self.clear_metas();
        *self.owner.borrow_mut() = vec![key.to_string()];
        let nat = self
            .globals
            .registry
            .data(Builtin::Nat)
            .ok_or_else(|| internal_error("no `Nat`"))?;
        let term = (|| {
            let mut cx = Ctx::new(self, measure.span());
            for b in header {
                let ty = cx.eval(&b.ty)?;
                cx.bind(&b.name, ty);
            }
            let nat_ty = cx.eval(&Term::data(nat, Vec::new()))?;
            check(&mut cx, measure, &nat_ty).map_err(|d| {
                if d.code == "E-TYPE-MISMATCH" {
                    d.with_note("the measure after `decreasing` is a `Nat` that gets smaller at every recursive call")
                } else {
                    d
                }
            })
        })();
        self.owner.borrow_mut().clear();
        let term = term?;
        if !self.drafts.borrow().is_empty() {
            self.drafts.borrow_mut().clear();
            return Err(Diagnostic::error(
                "E-DECREASING",
                "a measure can't contain a `match` or a local definition",
            )
            .with_label(measure.span(), "this measure")
            .with_note("define the measure as a function and call it here"));
        }
        let term = self.finish(&term, header.len())?;
        self.clear_metas();
        Ok(term)
    }

    /// `f.%step`: declared, its body elaborated with recursive calls going
    /// to `%rec`, and admitted. Also the first id after it, where the
    /// helpers lifted from it start.
    fn decreasing_step(
        &mut self,
        plan: &Plan,
        key: &str,
        def_name: &ast::Name,
        equations: &[Decl],
    ) -> Result<(DefId, usize)> {
        let g = &self.globals;
        let (n, s) = (plan.n(), plan.header);
        // Parameter `l` of `f` is at level `l` before `%rec` and `l + 1` after.
        let after = |l: usize| if l < s { l } else { l + 1 };
        let mut binders = Vec::new();
        for i in 0..n {
            if i == s {
                binders.push(Binder {
                    name: REC.into(),
                    icit: Icit::Explicit,
                    ty: plan.rec_ty(g, s, &|l| l)?,
                });
            }
            binders.push(Binder {
                name: plan.tel[i].name.clone(),
                icit: plan.tel[i].icit,
                ty: plan.param_ty(g, i, after(i), &after)?,
            });
        }
        if s == n {
            binders.push(Binder {
                name: REC.into(),
                icit: Icit::Explicit,
                ty: plan.rec_ty(g, s, &|l| l)?,
            });
        }
        let ty = pis(&binders, plan.result_at(g, n + 1, &after)?);
        let step_key = format!("{key}.%step");
        let step = kernel::declare_def(
            &mut self.globals,
            &scope::display(&step_key).into(),
            &ty,
            plan.theorem,
            false,
            plan.span,
        )
        .map_err(|d| self.generator_failed(plan, d))?;
        let first_helper = self.globals.defs.len();
        // The equations, with a pattern for `%rec` after the header's.
        let equations: Vec<Decl> = equations
            .iter()
            .map(|eq| match eq {
                Decl::Equation {
                    name,
                    patterns,
                    rhs,
                    arm,
                    span,
                } => {
                    let at = arm.unwrap_or(patterns.len());
                    let mut patterns = patterns.clone();
                    patterns.insert(
                        at,
                        Pattern::Var(ast::Name {
                            text: REC.to_string(),
                            span: name.span,
                        }),
                    );
                    Decl::Equation {
                        name: name.clone(),
                        patterns,
                        rhs: rhs.clone(),
                        arm: arm.map(|a| a + 1),
                        span: *span,
                    }
                }
                other => other.clone(),
            })
            .collect();
        *self.decreasing.borrow_mut() = Some(Active {
            target: plan.f,
            used: Cell::new(false),
            measure: plan.measure.clone(),
            header: s,
        });
        let ty_value = self.globals.def(step).ty_value.clone();
        let written = Rc::new(self.globals.def(step).ty.clone());
        let (body, joined) = self.with_local_retries(&step_key, def_name, |e| {
            let mut cx = Ctx::new(e, def_name.span);
            let term = e.body_in(
                &mut cx,
                ty_value.clone(),
                Some(written.clone()),
                def_name,
                &equations,
            )?;
            let joined = e.lift(&step_key, true)?;
            Ok((e.finish(&term, 0)?, joined))
        })?;
        if !joined.is_empty() {
            return Err(internal_error(
                "a `match` in a definition with `decreasing` refers to it directly",
            ));
        }
        kernel::define_group(&mut self.globals, &[(step, body)])
            .map_err(|d| self.explain_lifted(d))?;
        Ok((step, first_helper))
    }

    /// Runs one step of generating, turning a refusal into a message that
    /// says what failed.
    fn generated(
        &mut self,
        plan: &Plan,
        step: impl FnOnce(&mut Self) -> Result<DefId>,
    ) -> Result<DefId> {
        step(self).map_err(|d| self.generator_failed(plan, d))
    }

    fn generated_admit(&mut self, plan: &Plan, members: &[(DefId, Term)]) -> Result<()> {
        kernel::define_group(&mut self.globals, members).map_err(|d| self.generator_failed(plan, d))
    }

    fn generator_failed(&self, plan: &Plan, d: Diagnostic) -> Diagnostic {
        if d.code == "E-RESOURCE" || d.code == "E-DECREASING" {
            return d;
        }
        Diagnostic::error(
            "E-DECREASING",
            format!(
                "internal error: the definitions `decreasing` generates for `{}` were refused",
                plan.name
            ),
        )
        .with_label(plan.span, "while generating these")
        .with_note(format!("the kernel's reason: {}: {}", d.code, d.message))
        .with_note("this is a bug in the compiler, not in the program")
    }

    /// `f.%go`.
    fn decreasing_go(&mut self, plan: &Plan, step: DefId) -> Result<DefId> {
        let g = &self.globals;
        let (n, s) = (plan.n(), plan.header);
        // k at level 0, x… at 1…n, h at n + 1.
        let x = |l: usize| 1 + l;
        let mut binders = vec![Binder {
            name: "k".into(),
            icit: Icit::Explicit,
            ty: Term::data(plan.p.nat, Vec::new()),
        }];
        binders.extend(plan.binders(g, 1)?);
        binders.push(Binder {
            name: "h".into(),
            icit: Icit::Explicit,
            ty: plan.p.less(plan.measure_at(g, n + 1, &x)?, var(n + 1, 0)),
        });
        let ty = pis(&binders, plan.result_at(g, n + 2, &x)?);
        let name: Name = format!("{}.%go", plan.name).into();
        let go = kernel::declare_def(
            &mut self.globals,
            &name,
            &ty,
            plan.theorem,
            false,
            plan.span,
        )?;
        let g = &self.globals;
        // `Zero`: `h: m x < 0` is `False = True`.
        let zero = plan.absurd(plan.result_at(g, n + 2, &x)?, var(n + 2, n + 1));
        // `Succ k'`, with `k'` at level n + 2.
        let depth = n + 3;
        let rec = plan.rec_lam(g, go, depth, &var(depth, n + 2), &var(depth, n + 1), &x)?;
        let succ = apps(
            Term::Def(step),
            plan.args(depth, &x, 0..s)
                .into_iter()
                .chain([(rec, Icit::Explicit)])
                .chain(plan.args(depth, &x, s..n)),
        );
        // The case is on `k`, at level 0 of n + 2.
        let tree = Term::Case(
            n + 1,
            plan.p.nat,
            vec![
                Branch {
                    names: Vec::new(),
                    body: Some(Rc::new(zero)),
                },
                Branch {
                    names: vec!["k".into()],
                    body: Some(Rc::new(succ)),
                },
            ]
            .into(),
        );
        let mut names = vec![("k".into(), Icit::Explicit)];
        names.extend(plan.lam_names());
        names.push(("h".into(), Icit::Explicit));
        kernel::define_group(&mut self.globals, &[(go, lams(&names, tree))])?;
        Ok(go)
    }

    /// `f.%irrel`: `go k x h = go j x g`.
    fn decreasing_irrel(
        &mut self,
        plan: &Plan,
        step: DefId,
        go: DefId,
        respects: DefId,
    ) -> Result<DefId> {
        let g = &self.globals;
        let (n, s) = (plan.n(), plan.header);
        // k at 0, j at 1, x… at 2…n+1, h at n+2, g at n+3.
        let x = |l: usize| 2 + l;
        let (hl, gl) = (n + 2, n + 3);
        let nat = Term::data(plan.p.nat, Vec::new());
        let mut binders = vec![
            Binder {
                name: "k".into(),
                icit: Icit::Explicit,
                ty: nat.clone(),
            },
            Binder {
                name: "j".into(),
                icit: Icit::Explicit,
                ty: nat,
            },
        ];
        binders.extend(plan.binders(g, 2)?);
        binders.push(Binder {
            name: "h".into(),
            icit: Icit::Explicit,
            ty: plan.p.less(plan.measure_at(g, hl, &x)?, var(hl, 0)),
        });
        binders.push(Binder {
            name: "g".into(),
            icit: Icit::Explicit,
            ty: plan.p.less(plan.measure_at(g, gl, &x)?, var(gl, 1)),
        });
        let goal = |depth: usize| -> Term {
            let call = |fuel: usize, hyp: usize| {
                apps(
                    Term::Def(go),
                    [(var(depth, fuel), Icit::Explicit)]
                        .into_iter()
                        .chain(plan.args(depth, &x, 0..n))
                        .chain([(var(depth, hyp), Icit::Explicit)]),
                )
            };
            Term::Eq(None, Rc::new(call(0, hl)), Rc::new(call(1, gl)))
        };
        let ty = pis(&binders, goal(n + 4));
        let name: Name = format!("{}.%irrel", plan.name).into();
        let irrel = kernel::declare_def(&mut self.globals, &name, &ty, true, false, plan.span)?;
        let g = &self.globals;
        // Case on k (level 0); in its `Succ` branch k' is at n + 4, then a
        // case on j (level 1), whose `Succ` branch has j' at n + 5.
        let depth = n + 6;
        let (k1, j1) = (n + 4, n + 5);
        let r_k = plan.rec_lam(g, go, depth, &var(depth, k1), &var(depth, hl), &x)?;
        let r_j = plan.rec_lam(g, go, depth, &var(depth, j1), &var(depth, gl), &x)?;
        // e: y… p => irrel k' j' y… (glue p h) (glue p g)
        let inner = depth + n + 1;
        let e = {
            let call = apps(
                Term::Def(irrel),
                explicit([var(inner, k1), var(inner, j1)])
                    .into_iter()
                    .chain(plan.args(inner, &|l| depth + l, 0..n))
                    .chain(explicit([
                        plan.glue(
                            g,
                            inner,
                            depth,
                            Term::Var(0),
                            &var(inner, k1),
                            var(inner, hl),
                            &x,
                        )?,
                        plan.glue(
                            g,
                            inner,
                            depth,
                            Term::Var(0),
                            &var(inner, j1),
                            var(inner, gl),
                            &x,
                        )?,
                    ])),
            );
            let mut names = plan.lam_names();
            names.push(("p".into(), Icit::Explicit));
            lams(&names, call)
        };
        let succ_succ = apps(
            Term::Def(respects),
            plan.args(depth, &x, 0..s)
                .into_iter()
                .chain(explicit([r_k, r_j, e]))
                .chain(plan.args(depth, &x, s..n)),
        );
        let _ = step;
        let zero_k = plan_exfalso(plan, goal(n + 4), var(n + 4, hl));
        let zero_j = plan_exfalso(plan, goal(n + 5), var(n + 5, gl));
        let inner_case = Term::Case(
            (n + 5) - 1 - 1,
            plan.p.nat,
            vec![
                Branch {
                    names: Vec::new(),
                    body: Some(Rc::new(zero_j)),
                },
                Branch {
                    names: vec!["j".into()],
                    body: Some(Rc::new(succ_succ)),
                },
            ]
            .into(),
        );
        let tree = Term::Case(
            n + 3,
            plan.p.nat,
            vec![
                Branch {
                    names: Vec::new(),
                    body: Some(Rc::new(zero_k)),
                },
                Branch {
                    names: vec!["k".into()],
                    body: Some(Rc::new(inner_case)),
                },
            ]
            .into(),
        );
        let mut names = vec![("k".into(), Icit::Explicit), ("j".into(), Icit::Explicit)];
        names.extend(plan.lam_names());
        names.push(("h".into(), Icit::Explicit));
        names.push(("g".into(), Icit::Explicit));
        kernel::define_group(&mut self.globals, &[(irrel, lams(&names, tree))])?;
        Ok(irrel)
    }

    /// `f.unfold: f x = f.%step x (y… => f y…)`.
    fn decreasing_unfold(
        &mut self,
        plan: &Plan,
        step: DefId,
        go: DefId,
        irrel: DefId,
        respects: DefId,
    ) -> Result<DefId> {
        let g = &self.globals;
        let (n, s) = (plan.n(), plan.header);
        let id = |l: usize| l;
        let r_f = plan_rec_f(plan, g, n)?;
        let step_call = |r: Term| {
            apps(
                Term::Def(step),
                plan.args(n, &id, 0..s)
                    .into_iter()
                    .chain([(r, Icit::Explicit)])
                    .chain(plan.args(n, &id, s..n)),
            )
        };
        let lhs = apps(Term::Def(plan.f), plan.args(n, &id, 0..n));
        let ty = pis(
            &plan.binders(g, 0)?,
            Term::Eq(None, Rc::new(lhs), Rc::new(step_call(r_f.clone()))),
        );
        let name: Name = format!("{}.unfold", plan.name).into();
        let unfold = kernel::declare_def(&mut self.globals, &name, &ty, true, false, plan.span)?;
        let g = &self.globals;
        let m_x = plan.measure_at(g, n, &id)?;
        let refl_x = Term::app(Term::Def(plan.p.le_refl), m_x.clone());
        let r_go = plan.rec_lam(g, go, n, &m_x, &refl_x, &id)?;
        // e: y… p => irrel (m x) (Succ (m y)) y… (glue p (leRefl (m x))) (leRefl (m y))
        let inner = n + n + 1;
        let m_x_in = m_x.shift(g, n + 1, 0)?;
        let m_y_in = plan.measure_at(g, inner, &|l| n + l)?;
        let e = {
            let call = apps(
                Term::Def(irrel),
                explicit([m_x_in.clone(), plan.p.succ(m_y_in.clone())])
                    .into_iter()
                    .chain(plan.args(inner, &|l| n + l, 0..n))
                    .chain(explicit([
                        plan.glue(
                            g,
                            inner,
                            n,
                            Term::Var(0),
                            &m_x_in,
                            refl_x.shift(g, n + 1, 0)?,
                            &id,
                        )?,
                        Term::app(Term::Def(plan.p.le_refl), m_y_in),
                    ])),
            );
            let mut names = plan.lam_names();
            names.push(("p".into(), Icit::Explicit));
            lams(&names, call)
        };
        let proof = apps(
            Term::Def(respects),
            plan.args(n, &id, 0..s)
                .into_iter()
                .chain(explicit([r_go, r_f, e]))
                .chain(plan.args(n, &id, s..n)),
        );
        kernel::define_group(
            &mut self.globals,
            &[(unfold, lams(&plan.lam_names(), proof))],
        )?;
        Ok(unfold)
    }

    /// The lemma that definition `d` (`f.%step`, or a helper lifted from it)
    /// gives equal results for two values of its parameter `c` (`%rec`) that
    /// agree on every argument: declared and admitted once.
    fn respects(&mut self, st: &mut Gen, d: DefId, c: usize) -> Result<DefId> {
        if let Some(id) = st.respects.get(&d) {
            return Ok(*id);
        }
        let g = &self.globals;
        let def = g.def(d);
        let a = def.arity;
        let body = def
            .body()
            .cloned()
            .ok_or_else(|| internal_error("a helper without a body"))?;
        let (tel, result) = split_pis(&def.ty, Some(a));
        if tel.len() < a || c >= a {
            return Err(internal_error(
                "a helper whose type doesn't show its parameters",
            ));
        }
        let rec_ty = tel[c].ty.clone();
        let (rec_tel, _) = split_pis(&rec_ty, None);
        let arity = rec_tel.len();
        if rec_tel.last().is_none_or(|b| b.icit != Icit::Auto) {
            return Err(internal_error("a recursive call's type without its proof"));
        }
        // Parameter l at level l up to `c` (`r1`), then r2, e, and the rest
        // two further on.
        let map = move |l: usize| if l <= c { l } else { l + 2 };
        let mut binders = Vec::new();
        for (i, b) in tel.iter().enumerate() {
            if i == c {
                binders.push(Binder {
                    name: "r1".into(),
                    icit: b.icit,
                    ty: b.ty.clone(),
                });
                binders.push(Binder {
                    name: "r2".into(),
                    icit: b.icit,
                    ty: b.ty.shift(g, 1, 0)?,
                });
                // e: y… (p: P) -> r1 y… p = r2 y… p
                let ys = arity - 1;
                let mut e_binders = Vec::new();
                for (j, yb) in rec_tel.iter().enumerate() {
                    e_binders.push(Binder {
                        name: yb.name.clone(),
                        icit: if j == ys { Icit::Explicit } else { yb.icit },
                        ty: reindex(g, &yb.ty, c + j, c + 2 + j, &|l| {
                            if l < c { l } else { l + 2 }
                        })?,
                    });
                }
                let inner = c + 2 + arity;
                let call = |r: usize| {
                    apps(
                        var(inner, r),
                        rec_tel
                            .iter()
                            .enumerate()
                            .map(|(j, yb)| (var(inner, c + 2 + j), yb.icit)),
                    )
                };
                binders.push(Binder {
                    name: "e".into(),
                    icit: Icit::Explicit,
                    ty: pis(
                        &e_binders,
                        Term::Eq(None, Rc::new(call(c)), Rc::new(call(c + 1))),
                    ),
                });
                continue;
            }
            binders.push(Binder {
                name: b.name.clone(),
                icit: b.icit,
                ty: reindex(g, &b.ty, i, map(i), &map)?,
            });
        }
        let depth = a + 2;
        let call = |r: usize| {
            apps(
                Term::Def(d),
                (0..a).map(|i| {
                    let level = if i == c { r } else { map(i) };
                    (var(depth, level), tel[i].icit)
                }),
            )
        };
        let ty = pis(
            &binders,
            Term::Eq(None, Rc::new(call(c)), Rc::new(call(c + 1))),
        );
        let name: Name = format!("{}.%respects", def.name).into();
        let span = def.span;
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        st.respects.insert(d, id);
        st.made.push(id);
        let g = &self.globals;
        let tree = reindex(g, &Term::peel_lams_rc(&body, a), a, depth, &map)?;
        let leaf = Leaf {
            depth,
            r1: c,
            r2: c + 1,
            e: c + 2,
            arity,
        };
        let proof = self.tree_proofs(st, &tree, &result, a, &map, leaf)?;
        let names: Vec<(Name, Icit)> = binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
        kernel::define_group(&mut self.globals, &[(id, lams(&names, proof))])?;
        Ok(id)
    }

    /// A proof for each leaf of case tree `tree` (a respects lemma's), of
    /// type `result` (in the context of the `a` parameters, moved by `map`).
    fn tree_proofs(
        &mut self,
        st: &mut Gen,
        tree: &Term,
        result: &Term,
        a: usize,
        map: &dyn Fn(usize) -> usize,
        leaf: Leaf,
    ) -> Result<Term> {
        self.globals.budget.nesting(PASS)?;
        Ok(match tree {
            Term::Loc(span, inner) => Term::Loc(
                *span,
                Rc::new(self.tree_proofs(st, inner, result, a, map, leaf)?),
            ),
            Term::Case(ix, d, branches) => {
                let mut out = Vec::new();
                for b in branches.iter() {
                    out.push(Branch {
                        names: b.names.clone(),
                        body: match &b.body {
                            Some(body) => Some(Rc::new(self.tree_proofs(
                                st,
                                body,
                                result,
                                a,
                                map,
                                leaf.under(b.names.len()),
                            )?)),
                            None => None,
                        },
                    });
                }
                Term::Case(*ix, *d, out.into())
            }
            Term::NumCase(ix, arms, default) => {
                let mut out = Vec::new();
                for arm in arms.iter() {
                    out.push(NumArm {
                        value: arm.value.clone(),
                        body: Rc::new(self.tree_proofs(st, &arm.body, result, a, map, leaf)?),
                    });
                }
                let default = self.tree_proofs(st, default, result, a, map, leaf)?;
                Term::NumCase(*ix, out.into(), Rc::new(default))
            }
            t => {
                let ty = reindex(&self.globals, result, a, leaf.depth, map)?;
                self.cong(st, t, &ty, leaf, None)?.unwrap_or(Term::Refl)
            }
        })
    }

    /// A proof that `t` (at `leaf`, mentioning `r1`) equals itself with
    /// `r2` for `r1`, given `e`; `None` if it doesn't mention `r1`. `ty` is
    /// `t`'s type.
    fn cong(
        &mut self,
        st: &mut Gen,
        t: &Term,
        ty: &Term,
        leaf: Leaf,
        span: Option<Span>,
    ) -> Result<Option<Term>> {
        let g = &self.globals;
        let t = zeta(g, t)?;
        if !leaf.mentions(&t) {
            return Ok(None);
        }
        let mut sites = Vec::new();
        let tpl = self.template(st, &t, leaf, &mut sites, span)?;
        let g = &self.globals;
        let ty2 = ty.shift(g, 2, 0)?;
        let orig2 = t.shift(g, 2, 0)?;
        let mut proof = Term::Refl;
        for i in 0..sites.len() {
            let choose = |j: usize| match j.cmp(&i) {
                std::cmp::Ordering::Less => Choice::Post,
                std::cmp::Ordering::Equal => Choice::Hole,
                std::cmp::Ordering::Greater => Choice::Pre,
            };
            let rhs = rebuild(g, &tpl, &sites, leaf, &choose, 2, &Term::Var(1))?;
            let motive = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Lam(
                    "p".into(),
                    Icit::Explicit,
                    Rc::new(Term::Eq(
                        Some(Rc::new(ty2.clone())),
                        Rc::new(orig2.clone()),
                        Rc::new(rhs),
                    )),
                )),
            );
            proof = Term::J(
                Rc::new(motive),
                Rc::new(proof),
                Rc::new(sites[i].proof.clone()),
            );
        }
        Ok(Some(proof))
    }

    /// `t` with its recursive calls marked, each one's proof recorded in
    /// `sites` in the order they're rewritten.
    fn template(
        &mut self,
        st: &mut Gen,
        t: &Term,
        leaf: Leaf,
        sites: &mut Vec<Site>,
        span: Option<Span>,
    ) -> Result<Tpl> {
        self.globals.budget.nesting(PASS)?;
        if !leaf.mentions(t) {
            return Ok(Tpl::Plain(t.clone()));
        }
        let g = &self.globals;
        let depth = leaf.depth;
        let r1 = var(depth, leaf.r1);
        Ok(match t {
            Term::Loc(s, inner) => Tpl::Loc(
                *s,
                Box::new(self.template(st, inner, leaf, sites, Some(*s))?),
            ),
            Term::Ann(inner, ty) if !leaf.mentions(ty) => Tpl::Ann(
                Box::new(self.template(st, inner, leaf, sites, span)?),
                (**ty).clone(),
            ),
            Term::Ctor(d, c, fields) => {
                let mut out = Vec::new();
                for f in fields.iter() {
                    out.push(self.template(st, f, leaf, sites, span)?);
                }
                Tpl::Ctor(*d, *c, out)
            }
            Term::App(..) => {
                let (head, args) = spine(t);
                let head = head.clone();
                let args: Vec<(Term, Icit)> =
                    args.into_iter().map(|(a, i)| (a.clone(), i)).collect();
                let p = Prelude::new(g)?;
                let (core, used) = if matches!(&head, Term::Var(ix) if *ix == depth - 1 - leaf.r1) {
                    // A recursive call.
                    if args.len() < leaf.arity {
                        return Err(unsupported(
                            span,
                            "a recursive call that isn't given all its arguments",
                        ));
                    }
                    if args[..leaf.arity].iter().any(|(a, _)| leaf.mentions(a)) {
                        return Err(unsupported(
                            span,
                            "a recursive call whose arguments contain another recursive call",
                        ));
                    }
                    let pre = apps(r1.clone(), args[..leaf.arity].iter().cloned());
                    let proof = apps(
                        var(depth, leaf.e),
                        args[..leaf.arity].iter().enumerate().map(|(j, (a, icit))| {
                            (
                                a.clone(),
                                if j + 1 == leaf.arity {
                                    Icit::Explicit
                                } else {
                                    *icit
                                },
                            )
                        }),
                    );
                    sites.push(Site { pre, proof });
                    (Tpl::Site(sites.len() - 1), leaf.arity)
                } else if let Some((tpl, used)) = self.eliminator(st, &p, &head, &args, leaf, sites, span)? {
                    (tpl, used)
                } else if let Term::Def(k) = head
                    && st.helpers.contains(&k)
                    && let Some(c) = args.iter().position(|(a, _)| {
                        matches!(a.strip_loc(), Term::Var(ix) if *ix == depth - 1 - leaf.r1)
                    })
                    && c < self.globals.def(k).arity
                {
                    let ka = self.globals.def(k).arity;
                    if args.len() < ka {
                        return Err(unsupported(span, "a `match` that returns a function"));
                    }
                    let respects = self.respects(st, k, c)?;
                    let mut targs = Vec::new();
                    for (i, (a, icit)) in args[..ka].iter().enumerate() {
                        if i == c {
                            targs.push((Tpl::Plain(Term::Var(usize::MAX)), *icit));
                        } else {
                            targs.push((self.template(st, a, leaf, sites, span)?, *icit));
                        }
                    }
                    let g = &self.globals;
                    // Its arguments as they are once everything before it is
                    // rewritten: every site so far, with `r2`.
                    let mut proof_args = Vec::new();
                    for (i, (a, icit)) in targs.iter().enumerate() {
                        if i == c {
                            proof_args.push((var(depth, leaf.r1), *icit));
                            proof_args.push((var(depth, leaf.r2), *icit));
                            proof_args.push((var(depth, leaf.e), Icit::Explicit));
                        } else {
                            proof_args.push((
                                rebuild(g, a, sites, leaf, &|_| Choice::Post, 0, &Term::Refl)?,
                                *icit,
                            ));
                        }
                    }
                    let proof = apps(Term::Def(respects), proof_args);
                    sites.push(Site {
                        pre: Term::Refl,
                        proof,
                    });
                    (
                        Tpl::Helper {
                            site: sites.len() - 1,
                            head: k,
                            args: targs,
                            rec: c,
                        },
                        ka,
                    )
                } else {
                    if leaf.mentions(&head) {
                        return Err(match head.strip_loc() {
                            Term::Lam(..) => lambda_call(span, &st.name),
                            _ => unsupported(span, "a recursive call in this position"),
                        });
                    }
                    (Tpl::Plain(head.clone()), 0)
                };
                let mut tpl = core;
                for (a, icit) in &args[used..] {
                    let a = self.template(st, a, leaf, sites, span)?;
                    tpl = Tpl::App(Box::new(tpl), Box::new(a), *icit);
                }
                tpl
            }
            Term::Lam(..) => return Err(lambda_call(span, &st.name)),
            _ => {
                return Err(unsupported(span, "a recursive call in this position"));
            }
        })
    }

    /// An `if` with a recursive call in a branch: the call of
    /// `Decidable.elim` or `Bool.ifThenElse`, its proof by their `…Cong`
    /// lemma, and how many arguments it takes.
    #[allow(clippy::too_many_arguments)]
    fn eliminator(
        &mut self,
        st: &mut Gen,
        p: &Prelude,
        head: &Term,
        args: &[(Term, Icit)],
        leaf: Leaf,
        sites: &mut Vec<Site>,
        span: Option<Span>,
    ) -> Result<Option<(Tpl, usize)>> {
        let Term::Def(id) = head.strip_loc() else {
            return Ok(None);
        };
        // (the lemma, how many arguments, which are the branches, which is
        // the result type)
        let (cong, count, branches, result) = if *id == p.elim {
            (p.elim_cong, 5, [3, 4], 1)
        } else if *id == p.if_then_else {
            (p.if_cong, 4, [2, 3], 0)
        } else {
            return Ok(None);
        };
        if args.len() < count || !args[..count].iter().any(|(a, _)| leaf.mentions(a)) {
            return Ok(None);
        }
        if args[..branches[0]].iter().any(|(a, _)| leaf.mentions(a)) {
            return Err(unsupported(span, "a recursive call in an `if`'s condition"));
        }
        let depth = leaf.depth;
        let ty = args[result].0.clone();
        let mut lemma_args: Vec<(Term, Icit)> = args[..branches[0]].to_vec();
        let mut proofs = Vec::new();
        for &b in &branches {
            let (branch, _) = &args[b];
            lemma_args.push((branch.clone(), Icit::Explicit));
            lemma_args.push((
                rename(&self.globals, branch, depth, leaf.r1, leaf.r2)?,
                Icit::Explicit,
            ));
            let proof = match branch.strip_loc() {
                _ if !leaf.mentions(branch) => {
                    Term::Lam("h".into(), Icit::Explicit, Rc::new(Term::Refl))
                }
                Term::Lam(x, Icit::Explicit, body) => {
                    let g = &self.globals;
                    let inner_ty = ty.shift(g, 1, 0)?;
                    let proof = self
                        .cong(st, body, &inner_ty, leaf.under(1), span)?
                        .unwrap_or(Term::Refl);
                    Term::Lam(x.clone(), Icit::Explicit, Rc::new(proof))
                }
                _ => return Err(unsupported(span, "an `if` branch that isn't written out")),
            };
            proofs.push(proof);
        }
        lemma_args.extend(proofs.into_iter().map(|p| (p, Icit::Explicit)));
        let proof = apps(Term::Def(cong), lemma_args);
        sites.push(Site {
            pre: apps(head.clone(), args[..count].iter().cloned()),
            proof,
        });
        Ok(Some((Tpl::Site(sites.len() - 1), count)))
    }
}

/// `y… => [p] => f y…`, in a context of `depth` variables.
fn plan_rec_f(plan: &Plan, g: &Globals, depth: usize) -> Result<Term> {
    let _ = g;
    let n = plan.n();
    let inner = depth + n + 1;
    let call = apps(Term::Def(plan.f), plan.args(inner, &|l| depth + l, 0..n));
    let mut names = plan.lam_names();
    names.push((PROOF.into(), Icit::Auto));
    Ok(lams(&names, call))
}

fn plan_exfalso(plan: &Plan, goal: Term, proof: Term) -> Term {
    apps(
        Term::Def(plan.p.exfalso),
        [
            (goal, Icit::Implicit),
            (
                Term::app(Term::Def(plan.p.false_not_true), proof),
                Icit::Explicit,
            ),
        ],
    )
}

/// The term `tpl` stands for, with each site as `choose` says, moved under
/// `shift` more binders, a hole being `hole`.
fn rebuild(
    g: &Globals,
    tpl: &Tpl,
    sites: &[Site],
    leaf: Leaf,
    choose: &dyn Fn(usize) -> Choice,
    shift: usize,
    hole: &Term,
) -> Result<Term> {
    g.budget.nesting(PASS)?;
    let go = |t: &Tpl| rebuild(g, t, sites, leaf, choose, shift, hole);
    Ok(match tpl {
        Tpl::Plain(t) => t.shift(g, shift, 0)?,
        Tpl::Site(i) => match choose(*i) {
            Choice::Pre => sites[*i].pre.shift(g, shift, 0)?,
            Choice::Post => {
                rename(g, &sites[*i].pre, leaf.depth, leaf.r1, leaf.r2)?.shift(g, shift, 0)?
            }
            Choice::Hole => hole.clone(),
        },
        Tpl::Helper {
            site,
            head,
            args,
            rec,
        } => {
            let r = match choose(*site) {
                Choice::Hole => return Ok(hole.clone()),
                Choice::Pre => leaf.r1,
                Choice::Post => leaf.r2,
            };
            let mut term = Term::Def(*head);
            for (i, (a, icit)) in args.iter().enumerate() {
                let a = if i == *rec {
                    var(leaf.depth + shift, r)
                } else {
                    go(a)?
                };
                term = Term::app_icit(term, a, *icit);
            }
            term
        }
        Tpl::App(f, a, icit) => Term::App(Rc::new(go(f)?), Rc::new(go(a)?), *icit),
        Tpl::Ctor(d, c, fields) => Term::Ctor(
            *d,
            *c,
            fields
                .iter()
                .map(|f| Ok(Rc::new(go(f)?)))
                .collect::<Result<_>>()?,
        ),
        Tpl::Ann(inner, ty) => Term::Ann(Rc::new(go(inner)?), Rc::new(ty.shift(g, shift, 0)?)),
        Tpl::Loc(span, inner) => Term::Loc(*span, Rc::new(go(inner)?)),
    })
}

fn lambda_call(span: Option<Span>, name: &str) -> Diagnostic {
    let d = Diagnostic::error(
        "E-DECREASING",
        format!("`{name}` is called inside a function (`x => …`), which `decreasing` doesn't support yet"),
    )
    .with_note(
        "the function is called by whatever it's passed to, and nothing says that's only on \
         arguments with a smaller measure",
    )
    .with_note(format!("give `{name}` a fuel argument for now"));
    match span {
        Some(span) => d.with_label(span, "this call has no proof that its measure is smaller"),
        None => d,
    }
}

fn unsupported(span: Option<Span>, what: &str) -> Diagnostic {
    let d = Diagnostic::error(
        "E-DECREASING",
        format!("{what} can't be used with `decreasing` yet"),
    )
    .with_note("give this definition a fuel argument for now");
    match span {
        Some(span) => d.with_label(span, "here"),
        None => d,
    }
}

impl Ctx<'_> {
    /// While a definition with `decreasing` is elaborated, a name that
    /// refers to it, in its body: the recursive call's stand-in, `%rec`.
    pub(crate) fn decreasing_call(&self, name: &str) -> Option<(Term, Value)> {
        let target = self.e.decreasing.borrow().as_ref()?.target;
        if self.lookup(name).is_some() {
            return None;
        }
        match self.e.named(name) {
            Some((Global::Def(id), _)) if *id == target => {}
            _ => return None,
        }
        self.decreasing_rec(None)
    }

    /// `%rec`, if definition `id` (or with `None`, the one whose body is
    /// being elaborated) is the definition with `decreasing` it stands for.
    pub(crate) fn decreasing_rec(&self, id: Option<DefId>) -> Option<(Term, Value)> {
        let active = self.e.decreasing.borrow();
        let active = active.as_ref()?;
        if id.is_some_and(|id| id != active.target) {
            return None;
        }
        let level = self.lookup(REC)?;
        active.used.set(true);
        Some((
            Term::Var(self.level() - 1 - level),
            self.types[level].clone(),
        ))
    }
}

/// If `goal`, an obligation that couldn't be proved, is a recursive call's
/// `decreasing` one: the message for it, else `error` as it was.
pub(crate) fn explain_obligation(cx: &mut Ctx, goal: &Value, error: Diagnostic) -> Diagnostic {
    if crate::undo::fatal(&error) {
        return error;
    }
    let (measure, header) = match cx.e.decreasing.borrow().as_ref() {
        Some(active) => (active.measure.clone(), active.header),
        None => return error,
    };
    if cx.level() < header {
        return error;
    }
    let g = cx.g();
    let Some(less) = g.registry.def(Builtin::LessThan) else {
        return error;
    };
    // In the obligation's context, where a case may have refined the parameters.
    let env: Vec<Value> = cx.env[..header].to_vec();
    let Ok(old) = eval(g, &env, &measure) else {
        return error;
    };
    // Is the goal `_ < m x`?
    let matches = crate::undo::attempt(cx, |cx| {
        let meta = cx.fresh_meta();
        let new = cx.eval(&meta)?;
        let shape = stitchwort_core::value::apply(
            cx.g(),
            stitchwort_core::value::apply(cx.g(), eval(cx.g(), &[], &Term::Def(less))?, new)?,
            old.clone(),
        )?;
        if cx.unify(goal, &shape)? {
            Ok(meta)
        } else {
            Err(cx.error("E-DECREASING", "not a decreasing obligation", "here"))
        }
    });
    let Ok(Some(meta)) = matches else {
        return error;
    };
    let old_shown = cx.show(&old);
    let shown = match cx.eval(&meta) {
        Ok(new) => format!("{} < {old_shown}", cx.show(&new)),
        Err(_) => cx.show(goal),
    };
    let mut hypotheses = Vec::new();
    for level in 0..cx.level() {
        let name = cx.names[level].to_string();
        if name.starts_with('%') || name.is_empty() {
            continue;
        }
        if let Ok(Value::Eq(..)) = force(cx.g(), cx.types[level].clone()) {
            hypotheses.push(format!("`{name}: {}`", cx.show(&cx.types[level].clone())));
        }
    }
    let mut d = Diagnostic::error(
        "E-DECREASING",
        format!("can't show `{shown}` here, which `decreasing {old_shown}` needs for this call"),
    )
    .with_label(cx.span, "this recursive call");
    if !hypotheses.is_empty() {
        d = d.with_note(format!("in scope: {}", hypotheses.join(", ")));
    }
    d.with_note(format!(
        "give a proof with `[decreasing := …]`, or test it with `if h: {shown} then … else …`"
    ))
}
