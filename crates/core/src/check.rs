//! The type checker for core terms. See `docs/core.md` for the rules.
//!
//! Checking also completes terms: it fills in the type of each `a = b`, which
//! evaluation needs.

use std::rc::Rc;

use stitchwort_syntax::{Diagnostic, Span};

use crate::budget;
use crate::globals::{Ctor, Data, Def, Globals, Validator};
use crate::pretty;
use crate::term::{Branch, DataId, DefId, Icit, Name, Sort, Term};
use crate::termination;
use crate::value::{Value, apply, conv, eval, quote};

type Result<T> = std::result::Result<T, Diagnostic>;

/// The typing context: a value and a type for each variable in scope.
pub struct Ctx<'g> {
    g: &'g Globals,
    /// What each variable evaluates to. Normally the variable itself, but
    /// inside a case branch the matched variable is the constructor value.
    env: Vec<Value>,
    types: Vec<Value>,
    names: Vec<Name>,
    span: Span,
}

impl<'g> Ctx<'g> {
    pub fn new(g: &'g Globals, span: Span) -> Self {
        Ctx {
            g,
            env: Vec::new(),
            types: Vec::new(),
            names: Vec::new(),
            span,
        }
    }

    fn level(&self) -> usize {
        self.env.len()
    }

    fn bind(&mut self, name: Name, ty: Value) {
        self.env.push(Value::var(self.level()));
        self.types.push(ty);
        self.names.push(name);
    }

    fn unbind(&mut self, n: usize) {
        let keep = self.level() - n;
        self.env.truncate(keep);
        self.types.truncate(keep);
        self.names.truncate(keep);
    }

    fn eval(&self, term: &Term) -> Result<Value> {
        Ok(eval(self.g, &self.env, term)?)
    }

    fn quote(&self, value: &Value) -> Result<Term> {
        Ok(quote(self.g, self.level(), value)?)
    }

    fn conv(&self, a: &Value, b: &Value) -> Result<bool> {
        Ok(conv(self.g, self.level(), a, b)?)
    }

    fn show(&self, value: &Value) -> String {
        pretty::value(self.g, &self.names, value)
    }

    fn error(
        &self,
        code: &'static str,
        message: impl Into<String>,
        label: impl Into<String>,
    ) -> Diagnostic {
        Diagnostic::error(code, message).with_label(self.span, label)
    }

    fn mismatch(&self, expected: &Value, found: &Value) -> Diagnostic {
        if let (Value::Sort(_), Value::Sort(_)) = (expected, found) {
            return self
                .error(
                    "E-UNIVERSE",
                    "universe mismatch",
                    format!(
                        "expected something of type `{}`, but this has type `{}`",
                        self.show(expected),
                        self.show(found)
                    ),
                )
                .with_note("`Type n` lives in `Type (n+1)`; allowing `Type : Type` would make the logic inconsistent");
        }
        self.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "expected `{}`, but this has type `{}`",
                self.show(expected),
                self.show(found)
            ),
        )
    }
}

pub fn infer(cx: &mut Ctx, term: &Term) -> Result<(Term, Value)> {
    let g = cx.g;
    match term {
        Term::Loc(span, inner) => {
            let saved = std::mem::replace(&mut cx.span, *span);
            let result = infer(cx, inner);
            cx.span = saved;
            let (inner, ty) = result?;
            Ok((Term::Loc(*span, Rc::new(inner)), ty))
        }
        Term::Var(ix) if *ix < cx.level() => {
            Ok((term.clone(), cx.types[cx.level() - 1 - ix].clone()))
        }
        Term::Var(ix) => Err(malformed(cx, format!("variable {ix} is out of scope"))),
        Term::Def(id) => match g.defs.get(id.0) {
            Some(def) => Ok((term.clone(), def.ty_value.clone())),
            None => Err(malformed(cx, "reference to an unknown definition")),
        },
        Term::Data(d, args) => {
            let Some(data) = g.datas.get(d.0) else {
                return Err(malformed(cx, "reference to an unknown data type"));
            };
            if args.len() != data.params.len() {
                return Err(malformed(
                    cx,
                    format!("`{}` needs {} parameter(s)", data.name, data.params.len()),
                ));
            }
            let mut params = Vec::new();
            let mut out = Vec::new();
            for ((_, param_ty), arg) in data.params.iter().zip(args) {
                let ty = eval(g, &params, param_ty)?;
                let arg = check(cx, arg, &ty)?;
                params.push(cx.eval(&arg)?);
                out.push(arg);
            }
            Ok((Term::Data(*d, out), Value::Sort(data.sort)))
        }
        Term::Sort(s) => Ok((term.clone(), Value::Sort(s.succ()))),
        Term::Nat(_) => match g.builtins.nat {
            Some(nat) => Ok((term.clone(), Value::Data(nat, Vec::new()))),
            None => Err(malformed(cx, "a number, but `Nat` isn't defined")),
        },
        Term::Pi(x, icit, dom, cod) => {
            let (dom, s1) = check_type(cx, dom)?;
            let dom_value = cx.eval(&dom)?;
            cx.bind(x.clone(), dom_value);
            let result = check_type(cx, cod);
            cx.unbind(1);
            let (cod, s2) = result?;
            Ok((
                Term::Pi(x.clone(), *icit, Rc::new(dom), Rc::new(cod)),
                Value::Sort(Sort::pi(s1, s2)),
            ))
        }
        Term::App(f, a, icit) => {
            let (f, f_ty) = infer(cx, f)?;
            match f_ty {
                Value::Pi(_, pi_icit, dom, cod) if pi_icit == *icit => {
                    let a = check(cx, a, &dom)?;
                    let a_value = cx.eval(&a)?;
                    Ok((Term::app_icit(f, a, *icit), cod.apply(g, a_value)?))
                }
                other => Err(cx.error(
                    "E-NOT-A-FUNCTION",
                    "this isn't a function",
                    format!(
                        "it's applied to an argument, but its type is `{}`",
                        cx.show(&other)
                    ),
                )),
            }
        }
        Term::Ann(e, ty) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty)?;
            let e = check(cx, e, &ty_value)?;
            Ok((Term::Ann(Rc::new(e), Rc::new(ty)), ty_value))
        }
        Term::Eq(Some(ty), a, b) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty)?;
            let a = check(cx, a, &ty_value)?;
            let b = check(cx, b, &ty_value)?;
            Ok((
                Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::Prop),
            ))
        }
        Term::Eq(None, a, b) => {
            let (a, b, ty) = match infer(cx, a) {
                Ok((a, ty)) => (a, check(cx, b, &ty)?, ty),
                Err(e) if e.code == "E-CANNOT-INFER" => {
                    let (b, ty) = infer(cx, b)?;
                    (check(cx, a, &ty)?, b, ty)
                }
                Err(e) => return Err(e),
            };
            let ty = cx.quote(&ty)?;
            Ok((
                Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::Prop),
            ))
        }
        Term::J(motive, base, proof) => infer_j(cx, motive, base, proof),
        // A constructor of a data type without parameters has only one possible type.
        Term::Ctor(d, _, _) if g.datas.get(d.0).is_some_and(|d| d.params.is_empty()) => {
            let ty = Value::Data(*d, Vec::new());
            Ok((check(cx, term, &ty)?, ty))
        }
        Term::Meta(_) => Err(malformed(cx, "unsolved metavariable")),
        Term::Lam(..) | Term::Ctor(..) | Term::Refl | Term::Case(..) => Err(cx.error(
            "E-CANNOT-INFER",
            "can't work out the type of this",
            "add a type annotation: `(… : T)`",
        )),
    }
}

pub fn check(cx: &mut Ctx, term: &Term, expected: &Value) -> Result<Term> {
    let g = cx.g;
    match (term, expected) {
        (Term::Loc(span, inner), _) => {
            let saved = std::mem::replace(&mut cx.span, *span);
            let result = check(cx, inner, expected);
            cx.span = saved;
            Ok(Term::Loc(*span, Rc::new(result?)))
        }
        (Term::Lam(x, icit, body), Value::Pi(_, pi_icit, dom, cod)) if icit == pi_icit => {
            let var = Value::var(cx.level());
            cx.bind(x.clone(), (**dom).clone());
            let result = check(cx, body, &cod.apply(g, var)?);
            cx.unbind(1);
            Ok(Term::Lam(x.clone(), *icit, Rc::new(result?)))
        }
        (Term::Lam(..), _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "this is a function, but the expected type is `{}`",
                cx.show(expected)
            ),
        )),
        (Term::Ctor(d, c, _), _) if g.datas.get(d.0).and_then(|d| d.ctors.get(*c)).is_none() => {
            Err(malformed(cx, "reference to an unknown constructor"))
        }
        (Term::Ctor(d, c, args), Value::Data(d2, params)) if d == d2 => {
            let ctor = &g.data(*d).ctors[*c];
            if args.len() != ctor.fields.len() {
                return Err(malformed(
                    cx,
                    format!("`{}` needs {} field(s)", ctor.name, ctor.fields.len()),
                ));
            }
            let mut env = params.clone();
            let mut out = Vec::new();
            for ((_, field_ty), arg) in ctor.fields.iter().zip(args) {
                let ty = eval(g, &env, field_ty)?;
                let arg = check(cx, arg, &ty)?;
                env.push(cx.eval(&arg)?);
                out.push(arg);
            }
            Ok(Term::Ctor(*d, *c, out))
        }
        (Term::Ctor(d, c, _), _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "`{}` builds a `{}`, but the expected type is `{}`",
                g.data(*d).ctors[*c].name,
                g.data(*d).name,
                cx.show(expected)
            ),
        )),
        (Term::Refl, Value::Eq(_, a, b)) => {
            if cx.conv(a, b)? {
                Ok(Term::Refl)
            } else {
                Err(cx
                    .error(
                        "E-REFL",
                        "`rfl` can't prove this",
                        format!("`{}` and `{}` aren't equal", cx.show(a), cx.show(b)),
                    )
                    .with_note(
                        "`rfl` proves `a = b` only when both sides compute to the same value",
                    ))
            }
        }
        (Term::Refl, _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "`rfl` proves an equation, but the expected type is `{}`",
                cx.show(expected)
            ),
        )),
        (Term::Case(ix, d, branches), _) => check_case(cx, *ix, *d, branches, expected),
        _ => {
            let (term, found) = infer(cx, term)?;
            if cx.conv(&found, expected)? {
                Ok(term)
            } else {
                Err(cx.mismatch(expected, &found))
            }
        }
    }
}

pub fn check_type(cx: &mut Ctx, term: &Term) -> Result<(Term, Sort)> {
    let (term, ty) = infer(cx, term)?;
    match ty {
        Value::Sort(s) => Ok((term, s)),
        other => Err(cx.error(
            "E-NOT-A-TYPE",
            "expected a type",
            format!("this has type `{}`, so it isn't a type", cx.show(&other)),
        )),
    }
}

/// The universe that `ty` lives in.
fn sort_of(cx: &mut Ctx, ty: &Value) -> Result<Sort> {
    if let Value::Sort(s) = ty {
        return Ok(s.succ());
    }
    let term = cx.quote(ty)?;
    Ok(check_type(cx, &term)?.1)
}

fn infer_j(cx: &mut Ctx, motive: &Term, base: &Term, proof: &Term) -> Result<(Term, Value)> {
    let g = cx.g;
    let (proof, proof_ty) = infer(cx, proof)?;
    let Value::Eq(ty, x, y) = proof_ty else {
        return Err(cx.error(
            "E-TYPE-MISMATCH",
            "`J` needs a proof of an equation",
            format!("its last argument has type `{}`", cx.show(&proof_ty)),
        ));
    };
    let Term::Lam(y_name, Icit::Explicit, inner) = motive.strip_loc() else {
        return Err(motive_error(cx));
    };
    let Term::Lam(p_name, Icit::Explicit, body) = inner.strip_loc() else {
        return Err(motive_error(cx));
    };
    let level = cx.level();
    cx.bind(y_name.clone(), (*ty).clone());
    cx.bind(
        p_name.clone(),
        Value::Eq(ty.clone(), x.clone(), Rc::new(Value::var(level))),
    );
    let result = check_type(cx, body);
    cx.unbind(2);
    let (body, _) = result?;
    let motive = Term::Lam(
        y_name.clone(),
        Icit::Explicit,
        Rc::new(Term::Lam(p_name.clone(), Icit::Explicit, Rc::new(body))),
    );
    let motive_value = cx.eval(&motive)?;
    let base_ty = apply(
        g,
        apply(g, motive_value.clone(), (*x).clone())?,
        Value::Refl,
    )?;
    let base = check(cx, base, &base_ty)?;
    let proof_value = cx.eval(&proof)?;
    let result = apply(g, apply(g, motive_value, (*y).clone())?, proof_value)?;
    Ok((
        Term::J(Rc::new(motive), Rc::new(base), Rc::new(proof)),
        result,
    ))
}

fn motive_error(cx: &Ctx) -> Diagnostic {
    cx.error(
        "E-CANNOT-INFER",
        "the first argument of `J` must be a function of two arguments",
        "write it as `\\y p -> …`",
    )
}

fn check_case(
    cx: &mut Ctx,
    ix: usize,
    d: DataId,
    branches: &[Branch],
    goal: &Value,
) -> Result<Term> {
    let g = cx.g;
    if ix >= cx.level() {
        return Err(malformed(cx, format!("variable {ix} is out of scope")));
    }
    let x = cx.level() - 1 - ix;
    let Some(data) = g.datas.get(d.0) else {
        return Err(malformed(cx, "reference to an unknown data type"));
    };
    let params = match &cx.types[x] {
        Value::Data(d2, params) if *d2 == d => params.clone(),
        other => {
            return Err(cx.error(
                "E-TYPE-MISMATCH",
                "type mismatch",
                format!(
                    "this matches on a `{}`, but `{}` has type `{}`",
                    data.name,
                    cx.names[x],
                    cx.show(other)
                ),
            ));
        }
    };
    if branches.len() != data.ctors.len() {
        return Err(cx.error(
            "E-NONEXHAUSTIVE",
            "missing cases",
            format!("`{}` has {} constructors", data.name, data.ctors.len()),
        ));
    }
    if data.sort == Sort::Prop && sort_of(cx, goal)? != Sort::Prop {
        let subsingleton = data.ctors.len() <= 1
            && data
                .ctors
                .iter()
                .all(|c| c.field_sorts.iter().all(|s| *s == Sort::Prop));
        if !subsingleton {
            return Err(cx
                .error(
                    "E-PROP-ELIM",
                    format!("can't match on a proof of `{}` to produce data", data.name),
                    format!("the result type `{}` isn't a proposition", cx.show(goal)),
                )
                .with_note(format!(
                    "`{}` is a proposition, so its proofs are erased at runtime. Matching on one \
                     can only produce data when the proposition has at most one constructor and \
                     every field is itself a proof.",
                    data.name
                )));
        }
    }

    if let Some((ctor, branch)) = data
        .ctors
        .iter()
        .zip(branches)
        .find(|(ctor, branch)| ctor.fields.len() != branch.names.len())
    {
        return Err(malformed(
            cx,
            format!(
                "the `{}` branch binds {} field(s), but it has {}",
                ctor.name,
                branch.names.len(),
                ctor.fields.len()
            ),
        ));
    }

    let goal_term = cx.quote(goal)?;
    let mut out = Vec::new();
    for (c, (ctor, branch)) in data.ctors.iter().zip(branches).enumerate() {
        let base = cx.level();
        let fields: Vec<Value> = (0..ctor.fields.len())
            .map(|i| Value::var(base + i))
            .collect();
        // Inside the branch, the matched variable *is* the constructor value,
        // so it's substituted into the goal and the whole context.
        let value = Value::Ctor(d, c, fields.clone().into());
        let level = cx.level();
        let mut env = substitute(g, level, x, &value, &cx.env)?;
        env[x] = value.clone();
        let refined_types = substitute(g, level, x, &value, &cx.types)?;
        let branch_goal = substitute(g, level, x, &value, &[eval(g, &cx.env, &goal_term)?])?
            .pop()
            .expect("one value in, one out");
        let saved_env = std::mem::replace(&mut cx.env, env);
        let saved_types = std::mem::replace(&mut cx.types, refined_types);

        let mut field_env = params.clone();
        for ((_, field_ty), (name, field)) in
            ctor.fields.iter().zip(branch.names.iter().zip(&fields))
        {
            let ty = eval(g, &field_env, field_ty)?;
            field_env.push(field.clone());
            cx.bind(name.clone(), ty);
        }
        let result = check(cx, &branch.body, &branch_goal);
        cx.unbind(ctor.fields.len());
        cx.env = saved_env;
        cx.types = saved_types;
        out.push(Branch {
            names: branch.names.clone(),
            body: result?,
        });
    }
    Ok(Term::Case(ix, d, out.into()))
}

/// Substitutes `value` for variable `x` in each of `values`, with `level`
/// variables in scope. Case branches use this to refine the whole context:
/// with nested patterns, a variable matched later can appear in the type of
/// one bound earlier (`rest : res o` after `o` is matched as `L o'`).
pub fn substitute(
    g: &Globals,
    level: usize,
    x: usize,
    value: &Value,
    values: &[Value],
) -> budget::Result<Vec<Value>> {
    let mut env: Vec<Value> = (0..level).map(Value::var).collect();
    env[x] = value.clone();
    values
        .iter()
        .map(|v| eval(g, &env, &quote(g, level, v)?))
        .collect()
}

/// Infers the type of a closed term.
pub fn infer_closed(g: &Globals, term: &Term, span: Span) -> Result<(Term, Value)> {
    infer(&mut Ctx::new(g, span), term)
}

// Declarations

/// Checks the body of a definition added by [`declare_def`]. Until this
/// succeeds the definition has no body, so it never unfolds: recursive
/// references inside its own body stay opaque while it's being checked.
pub fn define_def(g: &mut Globals, id: DefId, body: &Term) -> Result<()> {
    let def = g.def(id);
    let (name, span, ty_value) = (def.name.clone(), def.span, def.ty_value.clone());
    let mut cx = Ctx::new(g, span);
    if !case_only_in_tree(body.peel_lams(body.count_lams()), true) {
        return Err(malformed(
            &cx,
            "`case` may only appear at the top of a definition",
        ));
    }
    let body = check(&mut cx, body, &ty_value)?;
    termination::check(g, &body, id, &name, span)?;
    let def = &mut g.defs[id.0];
    def.arity = body.count_lams();
    def.body = Some(body);
    Ok(())
}

/// Checks a definition's type and adds it without a body.
pub fn declare_def(
    g: &mut Globals,
    name: &Name,
    ty: &Term,
    theorem: bool,
    export: bool,
    span: Span,
) -> Result<DefId> {
    let mut cx = Ctx::new(g, span);
    if !case_only_in_tree(ty, false) {
        return Err(malformed(
            &cx,
            "`case` may only appear at the top of a definition",
        ));
    }
    let (ty, sort) = check_type(&mut cx, ty)?;
    if theorem && sort != Sort::Prop {
        let ty_value = cx.eval(&ty)?;
        return Err(Diagnostic::error(
            "E-NOT-A-PROP",
            format!("`{name}` is declared as a theorem, but its type isn't a proposition"),
        )
        .with_label(
            span,
            format!(
                "`{}` is a type of data, not a proposition",
                cx.show(&ty_value)
            ),
        )
        .with_note("remove `theorem` to make it an ordinary definition"));
    }
    let ty_value = eval(g, &[], &ty)?;
    g.defs.push(Def {
        name: name.clone(),
        ty,
        ty_value,
        body: None,
        arity: 0,
        theorem,
        export,
        validators: Vec::new(),
        span,
    });
    Ok(DefId(g.defs.len() - 1))
}

/// Checks a data type's parameters and adds it with no constructors yet, so
/// its constructors can refer to it.
pub fn declare_data(
    g: &mut Globals,
    name: Name,
    params: Vec<(Name, Term)>,
    sort: Sort,
    span: Span,
) -> Result<DataId> {
    let mut cx = Ctx::new(g, span);
    let mut checked = Vec::new();
    for (x, ty) in params {
        let (ty, _) = check_type(&mut cx, &ty)?;
        let value = cx.eval(&ty)?;
        cx.bind(x.clone(), value);
        checked.push((x, ty));
    }
    let defs_before = g.defs.len();
    g.datas.push(Data {
        name,
        params: checked,
        sort,
        ctors: Vec::new(),
        defs_before,
        ctors_defined: false,
        span,
    });
    Ok(DataId(g.datas.len() - 1))
}

pub struct CtorDecl {
    pub name: Name,
    pub fields: Vec<(Name, Term, Span)>,
}

pub fn define_ctors(g: &mut Globals, d: DataId, ctors: Vec<CtorDecl>) -> Result<()> {
    let Some(data) = g.datas.get(d.0) else {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown data type",
        ));
    };
    let mut cx = Ctx::new(g, data.span);
    if data.ctors_defined {
        return Err(malformed(
            &cx,
            format!("`{}`'s constructors are already defined", data.name),
        ));
    }
    for (x, ty) in &data.params {
        let value = cx.eval(ty)?;
        cx.bind(x.clone(), value);
    }
    let mut out = Vec::new();
    for ctor in ctors {
        let mut fields = Vec::new();
        let mut field_sorts = Vec::new();
        let mut field_erased = Vec::new();
        for (x, ty, span) in ctor.fields {
            cx.span = span;
            if !case_only_in_tree(&ty, false) {
                return Err(malformed(
                    &cx,
                    "`case` may only appear at the top of a definition",
                ));
            }
            if let Some(later) = declared_later(g, &ty, d) {
                return Err(cx
                    .error(
                        "E-POSITIVITY",
                        format!(
                            "field `{x}` uses {later}, which was declared after `{}`",
                            data.name
                        ),
                        "declared later",
                    )
                    .with_note(
                        "something declared after a data type could mention it, hiding a \
                         negative occurrence from the positivity check",
                    ));
            }
            let (ty, sort) = check_type(&mut cx, &ty)?;
            if !sort.fits_in(data.sort) {
                return Err(cx.error(
                    "E-UNIVERSE",
                    format!("field `{x}` is too large for `{}`", data.name),
                    format!(
                        "its type is in `{}`, but `{}` is in `{}`",
                        pretty::term(g, &[], &Term::Sort(sort)),
                        data.name,
                        pretty::term(g, &[], &Term::Sort(data.sort))
                    ),
                ));
            }
            if !positive(&ty, d, cx.level()) {
                return Err(cx
                    .error(
                        "E-POSITIVITY",
                        format!("`{}` is used in a negative position", data.name),
                        format!("field `{x}` takes a `{}` as input", data.name),
                    )
                    .with_note(
                        "a data type can't contain functions that take that same type as input; \
                         that would make it possible to prove anything",
                    ));
            }
            let value = cx.eval(&ty)?;
            field_erased.push(sort == Sort::Prop || is_type_former(g, cx.level(), &value)?);
            cx.bind(x.clone(), value);
            fields.push((x, ty));
            field_sorts.push(sort);
        }
        cx.unbind(fields.len());
        out.push(Ctor {
            name: ctor.name,
            fields,
            field_sorts,
            field_erased,
        });
    }
    g.datas[d.0].ctors = out;
    g.datas[d.0].ctors_defined = true;
    Ok(())
}

/// A definition or data type in `term` declared after data type `d`, if any.
fn declared_later(g: &Globals, term: &Term, d: DataId) -> Option<String> {
    let later_data = |d2: &DataId| {
        (d2.0 > d.0).then(|| {
            let name = g.datas.get(d2.0).map_or("?".into(), |x| x.name.to_string());
            format!("the data type `{name}`")
        })
    };
    let go = |t: &Term| declared_later(g, t, d);
    match term {
        Term::Def(id) => (id.0 >= g.data(d).defs_before).then(|| {
            let name = g.defs.get(id.0).map_or("?".into(), |x| x.name.to_string());
            format!("`{name}`")
        }),
        Term::Var(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => None,
        Term::Data(d2, args) | Term::Ctor(d2, _, args) => {
            later_data(d2).or_else(|| args.iter().find_map(go))
        }
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => go(a).or_else(|| go(b)),
        Term::Lam(_, _, b) | Term::Loc(_, b) => go(b),
        Term::Case(_, d2, branches) => {
            later_data(d2).or_else(|| branches.iter().find_map(|b| go(&b.body)))
        }
        Term::Eq(t, a, b) => t
            .as_deref()
            .and_then(go)
            .or_else(|| go(a))
            .or_else(|| go(b)),
        Term::J(m, b, p) => go(m).or_else(|| go(b)).or_else(|| go(p)),
    }
}

/// An error for a term no correct elaborator would produce.
fn malformed(cx: &Ctx, message: impl Into<String>) -> Diagnostic {
    cx.error("E-MALFORMED", "malformed core term", message)
        .with_note("this is a bug in the compiler, not in your program")
}

/// Whether `case` appears only in case-tree positions: at the top of a
/// definition's body (`in_tree`), and at the top of each branch. Evaluation
/// relies on this.
fn case_only_in_tree(term: &Term, in_tree: bool) -> bool {
    let no_case = |t: &Term| case_only_in_tree(t, false);
    match term {
        Term::Case(_, _, branches) => {
            in_tree && branches.iter().all(|b| case_only_in_tree(&b.body, true))
        }
        Term::Loc(_, t) => case_only_in_tree(t, in_tree),
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
            true
        }
        Term::Data(_, args) | Term::Ctor(_, _, args) => args.iter().all(no_case),
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => no_case(a) && no_case(b),
        Term::Lam(_, _, b) => no_case(b),
        Term::Eq(t, a, b) => t.as_deref().is_none_or(no_case) && no_case(a) && no_case(b),
        Term::J(m, b, p) => no_case(m) && no_case(b) && no_case(p),
    }
}

/// Strict positivity: the data type `d` may appear in a field's type only as
/// itself applied to its own parameters, possibly as the result of a function
/// whose inputs don't mention it.
fn positive(ty: &Term, d: DataId, depth: usize) -> bool {
    if !occurs(ty, d) {
        return true;
    }
    match ty.strip_loc() {
        Term::Data(d2, args) if *d2 == d => args
            .iter()
            .enumerate()
            .all(|(j, arg)| matches!(arg.strip_loc(), Term::Var(ix) if depth - 1 - ix == j)),
        Term::Pi(_, _, dom, cod) => !occurs(dom, d) && positive(cod, d, depth + 1),
        _ => false,
    }
}

fn occurs(term: &Term, d: DataId) -> bool {
    match term {
        Term::Data(d2, args) => *d2 == d || args.iter().any(|a| occurs(a, d)),
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {
            false
        }
        Term::Ctor(_, _, args) => args.iter().any(|a| occurs(a, d)),
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => occurs(a, d) || occurs(b, d),
        Term::Lam(_, _, b) | Term::Loc(_, b) => occurs(b, d),
        Term::Case(_, d2, branches) => *d2 == d || branches.iter().any(|b| occurs(&b.body, d)),
        Term::Eq(ty, a, b) => {
            ty.as_ref().is_some_and(|t| occurs(t, d)) || occurs(a, d) || occurs(b, d)
        }
        Term::J(m, b, p) => occurs(m, d) || occurs(b, d) || occurs(p, d),
    }
}

/// Checks and adds a validator for proof parameter `param` of an exported
/// definition: `decision` must have type `decidable P`, where `P` is the
/// parameter's type, in the context of the parameters before it.
///
/// `decidable` must be shaped like the prelude's `Decidable`: one `Prop`
/// parameter `p`, and a first constructor whose only field is a proof of `p`.
/// That's what lets extracted code treat the first constructor as "the
/// precondition holds".
pub fn add_validator(
    g: &mut Globals,
    id: DefId,
    param: usize,
    decidable: DataId,
    decision: &Term,
) -> Result<()> {
    let def = g.def(id);
    let span = def.span;
    let tel = telescope(g, &def.ty_value, span)?;
    let mut cx = Ctx::new(g, span);
    let Some((_, prop, true)) = tel.params.get(param) else {
        return Err(malformed(
            &cx,
            "a validator for a parameter that isn't erased",
        ));
    };
    let shaped_like_decidable = g.datas.get(decidable.0).is_some_and(|d| {
        d.params.len() == 1
            && matches!(d.params[0].1.strip_loc(), Term::Sort(Sort::Prop))
            && d.ctors.len() == 2
            && d.ctors[0].fields.len() == 1
            && matches!(d.ctors[0].fields[0].1.strip_loc(), Term::Var(0))
    });
    if !shaped_like_decidable || !case_only_in_tree(decision, false) {
        return Err(malformed(&cx, "a validator that isn't a decision"));
    }
    for (x, ty, _) in &tel.params[..param] {
        cx.bind(x.clone(), ty.clone());
    }
    let expected = Value::Data(decidable, vec![prop.clone()]);
    let decision = check(&mut cx, decision, &expected)?;
    g.defs[id.0].validators.push(Validator { param, decision });
    Ok(())
}

/// Whether `ty` is `Type`, `Prop`, or a function type ending in one: values of
/// such types are types, which are erased at runtime.
pub fn is_type_former(g: &Globals, level: usize, ty: &Value) -> budget::Result<bool> {
    match ty {
        Value::Sort(_) => Ok(true),
        Value::Pi(_, _, _, cod) => is_type_former(g, level + 1, &cod.apply(g, Value::var(level))?),
        _ => Ok(false),
    }
}

/// A definition's parameters, as seen through its type.
pub struct Telescope {
    /// Name, type, and whether the parameter is erased at runtime.
    pub params: Vec<(Name, Value, bool)>,
    /// The result type, with the parameters as variables.
    pub result: Value,
    /// Whether values of the result type are erased (proofs or types).
    pub result_erased: bool,
}

/// Splits an already-checked type into its parameters and result.
pub fn telescope(g: &Globals, ty: &Value, span: Span) -> Result<Telescope> {
    let mut cx = Ctx::new(g, span);
    let mut params = Vec::new();
    let mut ty = ty.clone();
    while let Value::Pi(x, _, dom, cod) = &ty {
        let erased = is_erased(&mut cx, dom)?;
        let next = cod.apply(g, Value::var(cx.level()))?;
        cx.bind(x.clone(), (**dom).clone());
        params.push((x.clone(), (**dom).clone(), erased));
        ty = next;
    }
    let result_erased = is_erased(&mut cx, &ty)?;
    Ok(Telescope {
        params,
        result: ty,
        result_erased,
    })
}

fn is_erased(cx: &mut Ctx, ty: &Value) -> Result<bool> {
    Ok(is_type_former(cx.g, cx.level(), ty)? || sort_of(cx, ty)? == Sort::Prop)
}
