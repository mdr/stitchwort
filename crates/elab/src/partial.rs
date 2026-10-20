//! Partial recursive definitions (docs/proposals/partial.md §7.3, §9.3).
//!
//! A group of definitions that call each other (or one that calls itself)
//! and whose types all say `{Partial}` doesn't recurse in the core. Each
//! reference to a member inside the group becomes a *request*, and the
//! runtime ties the knot with the kernel's `pfix`. For a group `f`, `g`, …
//! with fixed parameters `ps` (its leading type parameters) and a row `ρ`,
//! these ordinary, non-recursive declarations are submitted, in order:
//!
//! - `f.Request ps`: a data type with one constructor per member, holding
//!   the member's other arguments (its changing ones), packed.
//! - `f.Response ps : f.Request ps -> Type`: by cases, each member's result
//!   type at those arguments.
//! - `g.recur ps xs`, for each member `g`: the request `Recur (g.request xs)`,
//!   as a computation in the row `{Rec (f.Request ps), ρ}`. It has `g`'s
//!   parameters, and a `Delay` over that row.
//! - `g.description ps xs`, for each member: `g`'s equations, elaborated
//!   with every member's name standing for its `.recur`. So every reference
//!   to a member (a call, a partial application, the name on its own, under
//!   a lambda) is a request, and nothing in it refers to a member.
//! - `f.body ps r`: by cases on the request `r`, the member's description.
//! - `g ps xs = pfix (f.body ps) (g.request xs)`, for each member, together
//!   (one `define_group`, so they're admitted all or none).
//!
//! The kernel checks every one of them as usual: none refers to itself, so
//! termination checking has nothing to do, and a reference to a member left
//! in a description by mistake would be one to a pending declaration, which
//! admission refuses.
//!
//! Untrusted: a mistake here makes a program rejected or wrong, not the
//! logic inconsistent.

use std::rc::Rc;

use stitchwort_core::check as kernel;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, Spine, Value, eval, force, quote};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term};
use stitchwort_syntax::ast::Decl;
use stitchwort_syntax::{Diagnostic, Span};

use crate::module::Phase;
use crate::{Elaborator, Global, Result, effects};

/// A parameter of a member, as its signature has it.
#[derive(Clone)]
struct Param {
    name: Name,
    icit: Icit,
    /// Its type, in the context of the parameters before it.
    ty: Term,
}

/// A member's signature, split up.
struct Member {
    id: DefId,
    name: String,
    span: Span,
    params: Vec<Param>,
    /// The operations and results of its row, and its result type: the
    /// arguments of the `Delay` it returns, in the context of `params`.
    ops: Term,
    res: Term,
    result: Term,
}

/// The prelude declarations the translation builds with.
struct Names {
    delay: DefId,
    lift: DefId,
    pfix: DefId,
    comp: DataId,
    plus: DataId,
    rec: DataId,
    plus_res: DefId,
    rec_res: DefId,
}

/// The variable for binder `i` of `depth` binders.
fn var(depth: usize, i: usize) -> Term {
    Term::Var(depth - 1 - i)
}

fn apps(head: Term, args: impl IntoIterator<Item = (Term, Icit)>) -> Term {
    args.into_iter()
        .fold(head, |f, (a, icit)| Term::app_icit(f, a, icit))
}

fn pis(params: &[Param], body: Term) -> Term {
    params.iter().rev().fold(body, |b, p| {
        Term::Pi(p.name.clone(), p.icit, Rc::new(p.ty.clone()), Rc::new(b))
    })
}

fn lams(params: &[Param], body: Term) -> Term {
    params
        .iter()
        .rev()
        .fold(body, |b, p| Term::Lam(p.name.clone(), p.icit, Rc::new(b)))
}

impl Elaborator {
    /// Whether definition `id`'s type ends in `Delay`: `… -> {Partial} a`.
    pub fn is_partial(&self, id: DefId) -> Result<bool> {
        self.partial_after(id, usize::MAX)
    }

    /// Whether definition `id`'s result is a `Delay` once it has its first
    /// `n` parameters (or all of them): whether a definition with entry
    /// arity `n` is partial, as opposed to returning partial functions.
    fn partial_after(&self, id: DefId, n: usize) -> Result<bool> {
        let g = &self.globals;
        let Some(delay) = g.builtins.primitive_id(Primitive::Delay) else {
            return Ok(false);
        };
        let mut ty = g.def(id).ty_value.clone();
        let mut level = 0;
        loop {
            match force(g, ty)? {
                Value::Pi(_, _, _, cod) if level < n => {
                    ty = cod.apply(g, Value::var(level))?;
                    level += 1;
                }
                Value::Neutral(Head::Def(d), spine) => return Ok(d == delay && spine.len() == 3),
                _ => return Ok(false),
            }
        }
    }

    /// Whether the definition `id`, defined by `equations`, is partial: its
    /// result is a `Delay` once it has the parameters its equations bind
    /// (every implicit one up to the last explicit one the equations match,
    /// and any implicit ones right after; as `Elaborator::body` binds them).
    pub(crate) fn partial_member(&self, id: DefId, equations: &[Decl]) -> Result<bool> {
        let n = self.entry_params(id, equations)?;
        self.partial_after(id, n)
    }

    /// How many parameters the equations of definition `id` bind.
    fn entry_params(&self, id: DefId, equations: &[Decl]) -> Result<usize> {
        let g = &self.globals;
        let explicit = match equations.first() {
            Some(Decl::Equation { patterns, .. }) => patterns.len(),
            _ => 0,
        };
        let (mut ty, mut level, mut seen) = (g.def(id).ty_value.clone(), 0, 0);
        loop {
            match force(g, ty)? {
                Value::Pi(_, icit, _, cod) if icit.is_implicit() || seen < explicit => {
                    if !icit.is_implicit() {
                        seen += 1;
                    }
                    ty = cod.apply(g, Value::var(level))?;
                    level += 1;
                }
                _ => return Ok(level),
            }
        }
    }

    /// A recursive group whose members are partial and total, which stage 1
    /// refuses (docs/proposals/partial.md §9.3).
    pub(crate) fn mixed_partial(
        &self,
        members: &[(usize, &Decl, &[Decl])],
        ids: &[DefId],
        partial: &[bool],
    ) -> Diagnostic {
        let named = |want: bool| -> Vec<String> {
            members
                .iter()
                .zip(partial)
                .filter(|(_, p)| **p == want)
                .filter_map(|((_, decl, _), _)| match decl {
                    Decl::Signature { name, .. } => Some(format!("`{}`", name.text)),
                    _ => None,
                })
                .collect()
        };
        let (partial_names, total_names) = (named(true), named(false));
        let mut d = Diagnostic::error(
            "E-PARTIAL-MIXED",
            format!(
                "{} and {} call each other, but only {} {} `Partial`",
                total_names.join(", "),
                partial_names.join(", "),
                partial_names.join(", "),
                if partial_names.len() == 1 {
                    "is"
                } else {
                    "are"
                },
            ),
        );
        for (((_, decl, _), p), id) in members.iter().zip(partial).zip(ids) {
            if let Decl::Signature { name, .. } = decl {
                let returns_partial = !*p && self.is_partial(*id).unwrap_or(false);
                d = d.with_label(
                    name.span,
                    if *p {
                        format!("`{}` is `Partial`", name.text)
                    } else if returns_partial {
                        format!(
                            "`{}` isn't `Partial`: it returns a partial function, but finishes itself",
                            name.text
                        )
                    } else {
                        format!("`{}` isn't `Partial`", name.text)
                    },
                );
            }
        }
        d.with_note(
            "a recursive group must be all `Partial` or all total: split the cycle, so that the \
             total definitions don't refer back to the partial ones, or make them all `Partial`",
        )
    }

    /// Elaborates a recursive group of partial definitions, already
    /// declared as `ids` (pending), into the declarations listed at the top
    /// of this file. The diagnostics, each with the item it's about.
    pub(crate) fn partial_group(
        &mut self,
        members: &[(usize, &Decl, &[Decl])],
        ids: &[DefId],
    ) -> Vec<(usize, Diagnostic)> {
        let first_item = members[0].0;
        match self.describe_group(members, ids) {
            Ok(errors) => errors,
            Err(d) => vec![(first_item, d)],
        }
    }

    fn describe_group(
        &mut self,
        members: &[(usize, &Decl, &[Decl])],
        ids: &[DefId],
    ) -> Result<Vec<(usize, Diagnostic)>> {
        let g = &self.globals;
        // A prelude whose partial primitives were refused (E-BUILTIN) has
        // already reported that; there is nothing to describe against.
        if [Primitive::Delay, Primitive::Lift, Primitive::Pfix]
            .into_iter()
            .any(|p| g.builtins.primitive_id(p).is_none())
        {
            return Ok(Vec::new());
        }
        let names = {
            let prim = |p: Primitive| g.builtins.primitive_id(p).expect("partial types exist");
            let data = |b: Builtin| g.registry.data(b).expect("the prelude declares it");
            let def = |b: Builtin| g.registry.def(b).expect("the prelude declares it");
            Names {
                delay: prim(Primitive::Delay),
                lift: prim(Primitive::Lift),
                pfix: prim(Primitive::Pfix),
                comp: data(Builtin::Comp),
                plus: data(Builtin::Plus),
                rec: data(Builtin::Rec),
                plus_res: def(Builtin::PlusRes),
                rec_res: def(Builtin::RecRes),
            }
        };
        let infos: Vec<Member> = members
            .iter()
            .zip(ids)
            .map(|(&(_, decl, equations), id)| self.split_signature(decl, equations, *id))
            .collect::<Result<_>>()?;
        let fixed = self.fixed_params(&infos)?;
        let ops_fixed = self.shared_row(&infos, fixed)?;
        let f = fixed;
        let first = &infos[0];
        let fixed_params: Vec<Param> = first.params[..f].to_vec();
        let span = first.span;

        // The request type, and what each request is answered with.
        self.module.phase = Phase::Body;
        let req_name: Name = format!("{}.Request", first.name).into();
        let req = kernel::declare_data_group(
            &mut self.globals,
            fixed_params
                .iter()
                .map(|p| (p.name.clone(), p.ty.clone()))
                .collect(),
            Sort::Type(0),
            vec![(req_name, span)],
        )?[0];
        let ctors = infos
            .iter()
            .map(|m| kernel::CtorDecl {
                name: format!("{}.request", m.name).into(),
                fields: m.params[f..]
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone(), m.span))
                    .collect(),
                result: Vec::new(),
            })
            .collect();
        kernel::define_data_group(&mut self.globals, vec![(req, ctors)])
            .map_err(|e| self.unpackable(&infos, f, e))?;
        let req_at = |depth: usize| Term::data(req, (0..f).map(|i| var(depth, i)).collect());

        let response = {
            let ty = pis(
                &fixed_params,
                Term::Pi(
                    "r".into(),
                    Icit::Explicit,
                    Rc::new(req_at(f)),
                    Rc::new(Term::Sort(Sort::Type(0))),
                ),
            );
            let branches: Vec<stitchwort_core::term::Branch> = infos
                .iter()
                .map(|m| {
                    let c = m.params.len() - f;
                    Ok(stitchwort_core::term::Branch {
                        names: m.params[f..].iter().map(|p| p.name.clone()).collect(),
                        // From (fixed, changing) to (fixed, r, changing).
                        body: Some(Rc::new(m.result.shift(&self.globals, 1, c)?)),
                    })
                })
                .collect::<Result<_>>()?;
            let body = lams(
                &fixed_params,
                Term::Lam(
                    "r".into(),
                    Icit::Explicit,
                    Rc::new(Term::Case(0, req, branches.into())),
                ),
            );
            let id = kernel::declare_def(
                &mut self.globals,
                &format!("{}.Response", first.name).into(),
                &ty,
                false,
                false,
                span,
            )?;
            kernel::define_def(&mut self.globals, id, &body)?;
            id
        };
        let response_at = |depth: usize| {
            apps(
                Term::Def(response),
                fixed_params
                    .iter()
                    .enumerate()
                    .map(|(i, p)| (var(depth, i), p.icit)),
            )
        };
        // `Delay (Plus (Rec A) ops) (PlusRes (RecRes B) res) result`, at
        // `depth`, for the row `ops`/`res` at that depth.
        let described = |depth: usize, ops: Term, res: Term, result: Term| {
            let rec_a = Term::data(names.rec, vec![req_at(depth)]);
            let ops2 = Term::data(names.plus, vec![rec_a.clone(), ops.clone()]);
            let rec_res = apps(
                Term::Def(names.rec_res),
                [
                    (req_at(depth), Icit::Implicit),
                    (response_at(depth), Icit::Explicit),
                ],
            );
            let res2 = apps(
                Term::Def(names.plus_res),
                [
                    (rec_a, Icit::Implicit),
                    (ops, Icit::Implicit),
                    (rec_res, Icit::Explicit),
                    (res, Icit::Explicit),
                ],
            );
            (
                apps(
                    Term::Def(names.delay),
                    [
                        (ops2.clone(), Icit::Explicit),
                        (res2.clone(), Icit::Explicit),
                        (result, Icit::Explicit),
                    ],
                ),
                ops2,
                res2,
            )
        };

        // Each member's request function, and its description's signature.
        let mut recurs = Vec::new();
        let mut descriptions = Vec::new();
        for (k, m) in infos.iter().enumerate() {
            let d = m.params.len();
            let (ty, ops2, res2) = described(d, m.ops.clone(), m.res.clone(), m.result.clone());
            let ty = pis(&m.params, ty);
            let request = Term::ctor(req, k, (f..d).map(|j| var(d, j)).collect());
            let op = Term::ctor(names.plus, 0, vec![Term::ctor(names.rec, 0, vec![request])]);
            let done = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::ctor(names.comp, 0, vec![Term::Var(0)])),
            );
            let body = lams(
                &m.params,
                Term::app(
                    apps(
                        Term::Def(names.lift),
                        [
                            (ops2, Icit::Implicit),
                            (res2, Icit::Implicit),
                            (m.result.clone(), Icit::Implicit),
                        ],
                    ),
                    Term::ctor(names.comp, 1, vec![op, done]),
                ),
            );
            let recur = kernel::declare_def(
                &mut self.globals,
                &format!("{}.recur", m.name).into(),
                &ty,
                false,
                false,
                m.span,
            )?;
            kernel::define_def(&mut self.globals, recur, &body)?;
            recurs.push(recur);
            descriptions.push(kernel::declare_def(
                &mut self.globals,
                &format!("{}.description", m.name).into(),
                &ty,
                false,
                false,
                m.span,
            )?);
        }

        // The descriptions: each member's equations, with every member's
        // name standing for its request function.
        let keys = infos
            .iter()
            .map(|m| {
                self.declaration_key(&stitchwort_syntax::ast::Name {
                    text: m.name.clone(),
                    span: m.span,
                })
            })
            .collect::<Result<Vec<String>>>()?;
        let saved: Vec<_> = keys
            .iter()
            .map(|key| (key.clone(), self.scope.get(key)))
            .collect();
        for ((m, recur), key) in infos.iter().zip(&recurs).zip(&keys) {
            self.scope.insert(key, Global::Def(*recur), m.span, false);
        }
        self.recursion = Some(effects::Recursion {
            ans: {
                let mut ans = Value::Neutral(Head::Def(response), Spine::new());
                for (i, p) in fixed_params.iter().enumerate() {
                    ans = stitchwort_core::value::apply_icit(
                        &self.globals,
                        ans,
                        Value::var(i),
                        p.icit,
                    )?;
                }
                ans
            },
            req_data: req,
            names: infos.iter().map(|m| m.name.clone()).collect(),
        });
        let mut out = Vec::new();
        let mut bodies = Vec::new();
        for (&(item, decl, equations), desc) in members.iter().zip(&descriptions) {
            let Decl::Signature { name: def_name, .. } = decl else {
                unreachable!()
            };
            self.module.item = Some(item);
            self.module.phase = Phase::Body;
            self.clear_metas();
            match self.body(*desc, def_name, equations) {
                Ok(body) => bodies.push(body),
                Err(d) => out.push((item, d)),
            }
        }
        self.recursion = None;
        for (((name, global), id), m) in saved.into_iter().zip(ids).zip(&infos) {
            let span = global.map_or(m.span, |(_, s)| s);
            self.scope.insert(&name, Global::Def(*id), span, false);
        }
        if !out.is_empty() {
            return Ok(out);
        }
        // Every reference to a member passes the fixed parameters on
        // unchanged.
        for ((&(item, _, _), body), m) in members.iter().zip(&bodies).zip(&infos) {
            if let Some(d) = self.nonuniform(body, &recurs, &infos, f, m) {
                out.push((item, d));
            }
        }
        if !out.is_empty() {
            return Ok(out);
        }
        for ((&(item, _, _), body), desc) in members.iter().zip(bodies).zip(&descriptions) {
            self.module.item = Some(item);
            if let Err(d) = kernel::define_def(&mut self.globals, *desc, &body) {
                out.push((item, d));
            }
        }
        if !out.is_empty() {
            return Ok(out);
        }

        // The group's description: by cases on the request.
        self.module.item = Some(members[0].0);
        let body_id = {
            let depth = f + 1;
            let ops = ops_fixed.0.shift(&self.globals, 1, 0)?;
            let res = ops_fixed.1.shift(&self.globals, 1, 0)?;
            let result = Term::app(response_at(depth), Term::Var(0));
            let (ty, _, _) = described(depth, ops, res, result);
            let ty = pis(
                &fixed_params,
                Term::Pi("r".into(), Icit::Explicit, Rc::new(req_at(f)), Rc::new(ty)),
            );
            let branches: Vec<stitchwort_core::term::Branch> = infos
                .iter()
                .zip(&descriptions)
                .map(|(m, desc)| {
                    let depth = f + 1 + m.params.len() - f;
                    let args = (0..f).map(|i| (var(depth, i), m.params[i].icit)).chain(
                        (f..m.params.len())
                            .map(|j| (Term::Var(m.params.len() - 1 - j), m.params[j].icit)),
                    );
                    stitchwort_core::term::Branch {
                        names: m.params[f..].iter().map(|p| p.name.clone()).collect(),
                        body: Some(Rc::new(apps(Term::Def(*desc), args))),
                    }
                })
                .collect();
            let body = lams(
                &fixed_params,
                Term::Lam(
                    "r".into(),
                    Icit::Explicit,
                    Rc::new(Term::Case(0, req, branches.into())),
                ),
            );
            let id = kernel::declare_def(
                &mut self.globals,
                &format!("{}.body", first.name).into(),
                &ty,
                false,
                false,
                span,
            )?;
            kernel::define_def(&mut self.globals, id, &body)?;
            id
        };

        // The members themselves: `pfix (f.body ps) (g.request xs)`.
        let mut wrappers = Vec::new();
        for (k, m) in infos.iter().enumerate() {
            let d = m.params.len();
            let fixed_args = || (0..f).map(|i| (var(d, i), m.params[i].icit));
            let description = apps(Term::Def(body_id), fixed_args());
            let request = Term::ctor(req, k, (f..d).map(|j| var(d, j)).collect());
            let body = lams(
                &m.params,
                Term::app(
                    Term::app(
                        apps(
                            Term::Def(names.pfix),
                            [
                                (m.ops.clone(), Icit::Implicit),
                                (m.res.clone(), Icit::Implicit),
                                (req_at(d), Icit::Implicit),
                                (response_at(d), Icit::Implicit),
                            ],
                        ),
                        description,
                    ),
                    request,
                ),
            );
            wrappers.push((m.id, body));
        }
        kernel::define_group(&mut self.globals, &wrappers)?;
        for (&(item, signature, _), id) in members.iter().zip(ids) {
            self.module.item = Some(item);
            if let Err(d) = self.after_definition(signature, *id) {
                out.push((item, d));
            }
        }
        Ok(out)
    }

    /// A member's parameters (those its equations bind), and the arguments
    /// of the `Delay` it then returns.
    fn split_signature(&self, decl: &Decl, equations: &[Decl], id: DefId) -> Result<Member> {
        let Decl::Signature { name, .. } = decl else {
            unreachable!()
        };
        let g = &self.globals;
        let n = self.entry_params(id, equations)?;
        let mut params = Vec::new();
        let mut ty = g.def(id).ty_value.clone();
        for level in 0..n {
            let Value::Pi(x, icit, dom, cod) = force(g, ty)? else {
                unreachable!("`entry_params` counted these")
            };
            params.push(Param {
                name: x,
                icit,
                ty: quote(g, level, &dom)?,
            });
            ty = cod.apply(g, Value::var(level))?;
        }
        let Value::Neutral(_, spine) = force(g, ty)? else {
            unreachable!("a partial member's result is a `Delay`")
        };
        let arg = |i: usize| -> Result<Term> {
            match &spine[i] {
                Elim::App(v, _) => Ok(quote(g, n, v)?),
                Elim::J { .. } => unreachable!("a `Delay` is applied to its arguments"),
            }
        };
        Ok(Member {
            id,
            name: name.text.clone(),
            span: name.span,
            params,
            ops: arg(0)?,
            res: arg(1)?,
            result: arg(2)?,
        })
    }

    /// Whether a parameter of type `ty` (with `level` variables in scope) is
    /// large: a type, a type family, or in a universe above `Type`. Those
    /// can't be packed into a request, so they must be fixed.
    fn is_large(&self, level: usize, ty: &Value) -> Result<bool> {
        let g = &self.globals;
        let (mut level, mut ty) = (level, ty.clone());
        loop {
            match force(g, ty)? {
                Value::Sort(_) => return Ok(true),
                Value::Pi(_, _, _, cod) => {
                    ty = cod.apply(g, Value::var(level))?;
                    level += 1;
                }
                Value::Data(d, _) => return Ok(matches!(g.data(d).sort, Sort::Type(i) if i > 0)),
                _ => return Ok(false),
            }
        }
    }

    /// How many leading parameters are fixed: the members' leading large
    /// parameters, which must be the same for every member. Large
    /// parameters after the first ordinary one are refused.
    fn fixed_params(&self, infos: &[Member]) -> Result<usize> {
        let g = &self.globals;
        let mut counts = Vec::new();
        for m in infos {
            let mut env = Vec::new();
            let mut count = None;
            for (i, p) in m.params.iter().enumerate() {
                let ty = eval(g, &env, &p.ty)?;
                let large = self.is_large(i, &ty)?;
                match (large, count) {
                    (true, None) => {}
                    (false, None) => count = Some(i),
                    (true, Some(_)) => {
                        return Err(nonuniform_error(
                            m,
                            format!(
                                "`{}`'s parameter `{}` is a type (or a family of types), but it \
                                 comes after an ordinary parameter",
                                m.name, p.name
                            ),
                        )
                        .with_note(
                            "a partial recursive function's type parameters must come first: \
                             each recursive call passes them on unchanged",
                        ));
                    }
                    (false, Some(_)) => {}
                }
                env.push(Value::var(i));
            }
            counts.push(count.unwrap_or(m.params.len()));
        }
        let f = counts[0];
        for (m, &c) in infos.iter().zip(&counts).skip(1) {
            let mut same = c == f;
            let mut env = Vec::new();
            for i in 0..f.min(c) {
                if !same {
                    break;
                }
                let a = eval(g, &env, &infos[0].params[i].ty)?;
                let b = eval(g, &env, &m.params[i].ty)?;
                same = infos[0].params[i].icit == m.params[i].icit
                    && stitchwort_core::value::conv(g, i, &a, &b)?;
                env.push(Value::var(i));
            }
            if !same {
                return Err(nonuniform_error(
                    m,
                    format!(
                        "`{}` and `{}` call each other, so they must have the same type parameters",
                        infos[0].name, m.name
                    ),
                )
                .with_label(
                    infos[0].span,
                    format!("`{}` is declared here", infos[0].name),
                )
                .with_note(
                    "the members of a partial recursive group share their leading type \
                     parameters: write the same ones, in the same order, for each",
                ));
            }
        }
        Ok(f)
    }

    /// The members' row, which mustn't depend on their ordinary parameters
    /// and must be the same for each: its operations and results, in the
    /// context of the fixed parameters.
    fn shared_row(&self, infos: &[Member], f: usize) -> Result<(Term, Term)> {
        let g = &self.globals;
        let mut shared: Option<(Term, Term, Value, Value)> = None;
        for m in infos {
            let c = m.params.len() - f;
            if (0..c).any(|ix| m.ops.mentions(ix) || m.res.mentions(ix)) {
                return Err(nonuniform_error(
                    m,
                    format!("`{}`'s abilities depend on its arguments", m.name),
                )
                .with_note(
                    "a partial recursive function's abilities can depend only on its type \
                     parameters, since each recursive call runs with the same ones",
                ));
            }
            let env: Vec<Value> = (0..m.params.len()).map(Value::var).collect();
            let ops = eval(g, &env, &m.ops)?;
            let res = eval(g, &env, &m.res)?;
            match &shared {
                None => {
                    shared = Some((quote(g, f, &ops)?, quote(g, f, &res)?, ops, res));
                }
                Some((_, _, ops0, res0)) => {
                    let same = stitchwort_core::value::conv(g, f, ops0, &ops)?
                        && stitchwort_core::value::conv(g, f, res0, &res)?;
                    if !same {
                        return Err(Diagnostic::error(
                            "E-PARTIAL-NONUNIFORM",
                            format!(
                                "`{}` and `{}` call each other, so they must have the same \
                                 abilities",
                                infos[0].name, m.name
                            ),
                        )
                        .with_label(m.span, format!("`{}` is declared here", m.name))
                        .with_label(
                            infos[0].span,
                            format!("`{}` is declared here", infos[0].name),
                        )
                        .with_note(
                            "the members of a partial recursive group run as one loop, so their \
                             rows must list the same abilities",
                        ));
                    }
                }
            }
        }
        let (ops, res, _, _) = shared.expect("a group has members");
        Ok((ops, res))
    }

    /// The request type couldn't be defined: an argument can't be packed.
    fn unpackable(&self, infos: &[Member], f: usize, e: Diagnostic) -> Diagnostic {
        if e.code == "E-RESOURCE" {
            return e;
        }
        let m = &infos[0];
        let names: Vec<String> = infos
            .iter()
            .flat_map(|m| m.params[f..].iter().map(|p| format!("`{}`", p.name)))
            .collect();
        nonuniform_error(
            m,
            format!(
                "the arguments of `{}`'s recursive calls can't be packed into a request",
                m.name
            ),
        )
        .with_note(format!(
            "each recursive call's arguments ({}) are packed into one value, which must be data \
             of type `Type`; the kernel said: {}",
            names.join(", "),
            e.message
        ))
    }

    /// A reference to a member in `body` (a description) that doesn't pass
    /// the fixed parameters on unchanged: non-uniform recursion.
    fn nonuniform(
        &self,
        body: &Term,
        recurs: &[DefId],
        infos: &[Member],
        f: usize,
        m: &Member,
    ) -> Option<Diagnostic> {
        if f == 0 {
            return None;
        }
        // A work list: the term, its binder depth, and whether it's the
        // function of an application (so its spine was checked already).
        let mut pending = vec![(body, 0usize, false)];
        while let Some((term, depth, in_head)) = pending.pop() {
            match term {
                Term::App(fun, arg, _) => {
                    if !in_head && let Some(d) = self.check_spine(term, depth, recurs, infos, f, m)
                    {
                        return Some(d);
                    }
                    pending.push((fun, depth, true));
                    pending.push((arg, depth, false));
                }
                Term::Loc(_, t) => pending.push((t, depth, in_head)),
                Term::Def(id) if !in_head && recurs.contains(id) => {
                    return self.check_spine(term, depth, recurs, infos, f, m);
                }
                _ => term.for_each_child(|t, under| pending.push((t, depth + under, false))),
            }
        }
        None
    }

    fn check_spine(
        &self,
        term: &Term,
        depth: usize,
        recurs: &[DefId],
        infos: &[Member],
        f: usize,
        m: &Member,
    ) -> Option<Diagnostic> {
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return None;
        };
        let k = recurs.iter().position(|r| r == id)?;
        let uniform = args.len() >= f
            && args[..f]
                .iter()
                .enumerate()
                .all(|(i, a)| matches!(a.strip_loc(), Term::Var(ix) if *ix + i + 1 == depth));
        if uniform {
            return None;
        }
        Some(
            nonuniform_error(
                m,
                format!(
                    "`{}` calls `{}` with different type parameters",
                    m.name, infos[k].name
                ),
            )
            .with_note(
                "a partial recursive function's recursive calls must pass its type parameters on \
                 unchanged (non-uniform recursion, which changes them, isn't supported)",
            ),
        )
    }
}

fn nonuniform_error(m: &Member, message: String) -> Diagnostic {
    Diagnostic::error("E-PARTIAL-NONUNIFORM", message)
        .with_label(m.span, format!("`{}` is declared here", m.name))
}
