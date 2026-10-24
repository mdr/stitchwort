//! Default values of record and constructor fields
//! (docs/proposals/named-arguments.md §5.1 and §5.2): `step: Nat := 1` in a
//! record, `(id: Text := "anonymous")` in a constructor. A literal
//! `{ stop = 10 }`, or a named construction `Circle { radius = 1 }`, may
//! leave out a field that has one.
//!
//! Each default becomes a generated definition, a *helper*, elaborated once
//! the type is admitted: `RangeOptions.step.default`, or
//! `Shape.Circle.id.default` for a constructor's field. Its parameters are
//! the type's parameters and earlier fields the default needs: the
//! variables its elaborated value and its type mention, closed under the
//! variables their types mention (§5.1 rule 5), in context order, which
//! respects their dependencies. So it is checked for every value of the
//! earlier fields (rule 2), and it is an ordinary definition, which unfolds
//! when applied (rule 4). It is elaborated in the empty row, so it performs
//! nothing and isn't `Partial` (rule 9).
//!
//! A literal that leaves a field out calls the helper with the values the
//! literal gives (rule 1): a written field a default needs that isn't a
//! variable or a literal is bound by a transparent `let` first, so it isn't
//! computed twice (in a computation, effectful fields already run first,
//! into variables). Leaving a field out commits to its default (rule 3): a
//! later field is checked against the type the default gives.
//!
//! The helpers' names contain two dots, which source can't write, so they
//! are kept out of the name table; [`FieldDefault`]s, kept per declaration
//! (`Data::defaults`, and in the check cache), are how a
//! literal finds them. Defaults aren't part of the type's hash (D1099): a
//! literal that uses one refers to its helper, so changing a default changes
//! exactly the hashes of the literals that leave that field out.

use std::collections::BTreeSet;
use std::rc::Rc;

use stitchwort_core::collections::HashSet;
use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, Icit, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Decl, Expr};

use crate::check::{Ctx, check, implicit_arg};
use crate::module::Phase;
use crate::{Elaborator, Result, error, kernel};

pub(crate) use stitchwort_core::globals::FieldDefault;

impl Elaborator {
    /// After data type `d` (declared by `decl`) is admitted: a helper for
    /// each field's default, recorded in its `Data::defaults`.
    pub(crate) fn field_defaults(&mut self, decl: &Decl, d: DataId) -> Result<()> {
        let Decl::Data {
            ctors, interface, ..
        } = decl
        else {
            return Ok(());
        };
        let written: Vec<(usize, &ast::Name, &Expr)> = ctors
            .iter()
            .enumerate()
            .flat_map(|(c, ctor)| {
                ctor.fields
                    .iter()
                    .zip(&ctor.defaults)
                    .filter_map(move |(binder, default)| {
                        default
                            .as_ref()
                            .map(|v| binder.names.iter().map(move |n| (c, n, v)))
                    })
                    .flatten()
            })
            .collect();
        let Some(&(_, first, _)) = written.first() else {
            return Ok(());
        };
        if *interface {
            return Err(error(
                "E-FIELD-DEFAULT",
                first.span,
                "an interface's methods can't have default values",
            )
            .with_note("give every method in each instance"));
        }
        let mut table: Vec<Vec<Option<FieldDefault>>> = self
            .globals
            .data(d)
            .ctors
            .iter()
            .map(|c| vec![None; c.fields.len()])
            .collect();
        for (c, field, value) in written {
            let i = self.globals.data(d).ctors[c]
                .fields
                .iter()
                .position(|(x, _)| **x == *field.text)
                .expect("the constructor has the field it declares");
            table[c][i] = Some(self.default_helper(d, c, i, value)?);
        }
        self.globals.datas[d.0].defaults = Some(Rc::new(table));
        Ok(())
    }

    /// The helper for the default `value` of field `i` of constructor `c`
    /// of `d`.
    fn default_helper(
        &mut self,
        d: DataId,
        c: usize,
        i: usize,
        value: &Expr,
    ) -> Result<FieldDefault> {
        let g = &self.globals;
        let data = g.data(d);
        let ctor = &data.ctors[c];
        let np = data.params.len();
        let field = ctor.fields[i].0.clone();
        let label: Name = if data.record {
            format!("{}.{field}.default", data.name)
        } else {
            format!("{}.{}.{field}.default", data.name, ctor.name)
        }
        .into();
        // Each variable of the context: its name and type, in the context of
        // the variables before it.
        let context: Vec<(Name, Term)> = data
            .params
            .iter()
            .chain(&ctor.fields[..i])
            .cloned()
            .collect();
        let field_ty = ctor.fields[i].1.clone();
        let earlier: Vec<String> = ctor.fields[..i]
            .iter()
            .map(|(x, _)| format!("`{x}`"))
            .collect();
        let later: Vec<String> = ctor.fields[i + 1..]
            .iter()
            .map(|(x, _)| x.to_string())
            .collect();
        let span = value.span();
        self.module.phase = Phase::Body;
        self.local_helpers.clear();
        self.preadmitted.borrow_mut().clear();
        let shown = ast::Name {
            text: label.to_string(),
            span,
        };
        let body = self.with_local_retries(&label, &shown, |e| {
            let term = {
                let mut cx = Ctx::new(e, span);
                for (x, ty) in &context {
                    let ty = cx.eval(ty)?;
                    cx.bind(x, ty);
                }
                let expected = cx.eval(&field_ty)?;
                check(&mut cx, value, &expected)?
            };
            e.lift(&label, false)?;
            e.finish(&term, context.len())
        });
        self.local_helpers.clear();
        let body = body.map_err(|e| match e.code {
            // The usual note, to add the ability (or `Partial`) to the function's type,
            // doesn't apply: a default has no type to add it to.
            "E-ABILITY" | "E-PARTIAL" => Diagnostic {
                notes: Vec::new(),
                ..e
            }
            .with_note(
                "a field's default can't perform operations: it is computed wherever a value \
                 leaves the field out",
            ),
            "E-UNKNOWN-NAME" => {
                match later.iter().find(|x| e.message.contains(&format!("`{x}`"))) {
                    Some(x) => e.with_note(format!(
                        "`{x}` is a later field: a default may use only the fields before it"
                    )),
                    None => e,
                }
            }
            "E-REFL" | "E-TYPE-MISMATCH" if !earlier.is_empty() => e.with_note(format!(
                "a field's default must work for any values of the earlier fields ({}), \
                 since a value may give them and leave this one out",
                earlier.join(", ")
            )),
            _ => e,
        })?;
        let g = &self.globals;
        let n = context.len();
        // What it needs: the variables the value and its type mention, and
        // those their types mention.
        let mut captures = BTreeSet::new();
        crate::lift::uses(&body, n, &|_| None, &mut captures);
        crate::lift::uses(&field_ty, n, &|_| None, &mut captures);
        let mut work: Vec<usize> = captures.iter().copied().collect();
        while let Some(l) = work.pop() {
            let mut deps = BTreeSet::new();
            crate::lift::uses(&context[l].1, l, &|_| None, &mut deps);
            for dep in deps {
                if captures.insert(dep) {
                    work.push(dep);
                }
            }
        }
        let captures: Vec<usize> = captures.into_iter().collect();
        let position = |l: usize| captures.iter().position(|c| *c == l);
        let into = |t: &Term, depth: usize, scope: usize| {
            crate::lift::replace_with(
                g,
                t,
                depth,
                &|l| match position(l) {
                    Some(p) if p < scope => Ok(Term::Var(scope - 1 - p)),
                    _ => Err(Diagnostic::error(
                        "E-MALFORMED",
                        "internal error: a field's default uses a variable it doesn't take",
                    )),
                },
                &|_, _| None,
            )
        };
        let k = captures.len();
        let mut ty = into(&field_ty, n, k)?;
        let mut lam = into(&body, n, k)?;
        for (p, &l) in captures.iter().enumerate().rev() {
            let (x, dom) = &context[l];
            let dom = into(dom, l, p)?;
            let icit = helper_icit(l, np);
            ty = Term::Pi(x.clone(), icit, Rc::new(dom), Rc::new(ty));
            lam = Term::Lam(x.clone(), icit, Rc::new(lam));
        }
        let helper = kernel::declare_def(&mut self.globals, &label, &ty, false, false, span)?;
        kernel::define_def(&mut self.globals, helper, &lam)?;
        Ok(FieldDefault { helper, captures })
    }

    /// The default of field `i` of constructor `c` of `d`, if it has one.
    pub(crate) fn field_default(&self, d: DataId, c: usize, i: usize) -> Option<&FieldDefault> {
        self.globals
            .data(d)
            .defaults
            .as_ref()?
            .get(c)?
            .get(i)?
            .as_ref()
    }

    /// The names of the fields of constructor `c` of `d` that have defaults.
    pub(crate) fn defaulted_fields(&self, d: DataId, c: usize) -> Vec<&str> {
        let ctor = &self.globals.data(d).ctors[c];
        (0..ctor.fields.len())
            .filter(|&i| self.field_default(d, c, i).is_some())
            .map(|i| &*ctor.fields[i].0)
            .collect()
    }
}

/// How a helper takes the variable at `level`: the type's parameters
/// implicitly, its fields explicitly.
fn helper_icit(level: usize, params: usize) -> Icit {
    if level < params {
        Icit::Implicit
    } else {
        Icit::Explicit
    }
}

/// A note for a missing field's error: which fields may be left out.
pub(crate) fn defaulted_note(defaulted: &[&str]) -> Option<String> {
    let quoted: Vec<String> = defaulted.iter().map(|f| format!("`{f}`")).collect();
    match quoted.as_slice() {
        [] => None,
        [one] => Some(format!("{one} has a default value, so it may be left out")),
        [rest @ .., last] => Some(format!(
            "{} and {last} have default values, so they may be left out",
            rest.join(", ")
        )),
    }
}

/// How a field the literal doesn't give is filled in, when it has no
/// default.
pub(crate) type Missing<'a> = dyn FnMut(&mut Ctx, usize, &Value) -> Result<Term> + 'a;

/// Constructor `c` of `d` at the parameters `params`, from the fields
/// `written` (each checked against its type, in declaration order) and the
/// defaults of those left out; any other field left out is filled by
/// `missing`. The term (the constructor, inside the `let`s of rule 1), and
/// the values of the parameters and fields, in `cx`'s context, for the
/// result type's indices.
pub(crate) fn construct(
    cx: &mut Ctx,
    d: DataId,
    c: usize,
    params: &[Value],
    written: &[(ast::Name, Expr)],
    missing: &mut Missing,
) -> Result<(Term, Vec<Value>)> {
    let g = cx.g();
    let ctor = &g.data(d).ctors[c];
    let np = params.len();
    let given = |i: usize| written.iter().find(|(n, _)| *n.text == *ctor.fields[i].0);
    // The written fields a default left out needs.
    let mut needed: HashSet<usize> = HashSet::default();
    for i in 0..ctor.fields.len() {
        if given(i).is_none()
            && let Some(default) = cx.e.field_default(d, c, i)
        {
            needed.extend(
                default
                    .captures
                    .iter()
                    .filter(|&&l| l >= np)
                    .map(|l| l - np),
            );
        }
    }
    let mark = cx.mark();
    let mut env = params.to_vec();
    // Each field's term, with the level it was made at.
    let mut terms: Vec<(Term, usize)> = Vec::new();
    // Each `let`: name, type and value, made at the level before it.
    let mut lets: Vec<(Name, Term, Term)> = Vec::new();
    let mut defaulted: Vec<usize> = Vec::new();
    let result = (|| -> Result<()> {
        for (i, (field, field_ty)) in ctor.fields.iter().enumerate() {
            let ty = eval(g, &env, field_ty)?;
            let mut term = match given(i) {
                Some((_, expr)) => match check(cx, expr, &ty) {
                    Ok(term) => term,
                    Err(e) => return Err(left_out_note(cx, e, d, c, i, np, &env, &defaulted)),
                },
                None => match cx.e.field_default(d, c, i) {
                    Some(default) => {
                        defaulted.push(i);
                        call(cx, default, np, &env, &terms)?
                    }
                    None => missing(cx, i, &ty)?,
                },
            };
            if given(i).is_some() && needed.contains(&i) && !simple(&term) {
                let ty_term = cx.quote(&ty)?;
                let level = cx.level();
                cx.define(
                    None,
                    field.clone(),
                    ty.clone(),
                    ty_term.clone(),
                    term.clone(),
                )?;
                lets.push((field.clone(), ty_term, term));
                term = Term::Var(0);
                terms.push((term, level + 1));
            } else {
                terms.push((term, cx.level()));
            }
            let (last, at) = terms.last().expect("just pushed");
            env.push(
                if kernel::later_types_mention(&ctor.fields, i) || needed.contains(&i) {
                    cx.eval(&last.shift(g, cx.level() - at, 0)?)?
                } else {
                    unused()
                },
            );
        }
        Ok(())
    })();
    let level = cx.level();
    cx.reset(mark);
    result?;
    let fields = terms
        .iter()
        .map(|(t, at)| Ok(t.shift(g, level - at, 0)?))
        .collect::<Result<Vec<_>>>()?;
    let mut term = Term::ctor(d, c, fields);
    for (x, ty, value) in lets.into_iter().rev() {
        term = Term::let_(x, ty, value, term);
    }
    Ok((term, env))
}

/// A variable, a number, text or a constant: what a default may use
/// without a `let` (§5.1 rule 1).
fn simple(term: &Term) -> bool {
    match term.strip_loc() {
        Term::Var(_) | Term::Def(_) | Term::Nat(_) | Term::Chars(_) | Term::Sort(_) => true,
        Term::Ctor(_, _, fields) => fields.is_empty(),
        _ => false,
    }
}

/// The call of `default`'s helper, at `cx`'s level, given the parameters
/// and the terms of the earlier fields (each with the level it was made
/// at).
fn call(
    cx: &Ctx,
    default: &FieldDefault,
    np: usize,
    env: &[Value],
    terms: &[(Term, usize)],
) -> Result<Term> {
    let g = cx.g();
    let mut term = Term::Def(default.helper);
    for &l in &default.captures {
        let arg = if l < np {
            cx.quote(&env[l])?
        } else {
            let (t, at) = &terms[l - np];
            t.shift(g, cx.level() - at, 0)?
        };
        term = Term::app_icit(term, arg, helper_icit(l, np));
    }
    Ok(term)
}

/// A written field's type error, with a note when its type mentions a
/// field left out: that field is its default (§5.1 rule 3).
#[allow(clippy::too_many_arguments)]
fn left_out_note(
    cx: &Ctx,
    e: Diagnostic,
    d: DataId,
    c: usize,
    i: usize,
    np: usize,
    env: &[Value],
    defaulted: &[usize],
) -> Diagnostic {
    if e.code != "E-TYPE-MISMATCH" {
        return e;
    }
    let g = cx.g();
    let ctor = &g.data(d).ctors[c];
    let mut e = e;
    for &j in defaulted {
        if ctor.fields[i].1.mentions(i - 1 - j) {
            let value = force(g, env[np + j].clone())
                .map(|v| cx.show(&v))
                .unwrap_or_else(|_| "its default".into());
            e = e.with_note(format!(
                "`{}` is left out, so it is its default value, `{value}`; give `{}` to use \
                 another",
                ctor.fields[j].0, ctor.fields[j].0
            ));
        }
    }
    e
}

/// `C { f = e, … }` leaving out fields with defaults, checked against
/// `expected` if known: the constructor's parameters are `expected`'s, or
/// else unknowns, and its implicit fields are unknowns, as in a positional
/// application. The term and its type.
pub(crate) fn ctor_with_defaults(
    cx: &mut Ctx,
    d: DataId,
    c: usize,
    written: &[(ast::Name, Expr)],
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let g = cx.g();
    let data = g.data(d);
    let np = data.params.len();
    let known = match expected {
        Some(t) => match force(g, t.clone())? {
            Value::Data(e, args) if e == d => Some(args[..np].to_vec()),
            _ => None,
        },
        None => None,
    };
    let params = match known {
        Some(params) => params,
        None => {
            let mut params: Vec<Value> = Vec::new();
            for (k, (_, ty)) in data.params.iter().enumerate() {
                let ty = eval(g, &params, ty)?;
                let icit = if data.auto_params.get(k).copied().unwrap_or(false) {
                    Icit::Auto
                } else {
                    Icit::Implicit
                };
                let meta = implicit_arg(cx, icit, &ty);
                params.push(cx.eval(&meta)?);
            }
            params
        }
    };
    let mut missing = |cx: &mut Ctx, _: usize, ty: &Value| Ok(implicit_arg(cx, Icit::Implicit, ty));
    let (term, env) = construct(cx, d, c, &params, written, &mut missing)?;
    let mut args = params;
    for index in &data.ctors[c].result {
        args.push(eval(g, &env, index)?);
    }
    let ty = Value::Data(d, args);
    if let Some(t) = expected
        && !cx.unify(&ty, t)?
    {
        return Err(cx.mismatch(t, &ty));
    }
    Ok((term, ty))
}
