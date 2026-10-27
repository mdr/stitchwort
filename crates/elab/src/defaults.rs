//! Default values of record and constructor fields
//! (docs/proposals/named-arguments.md §5.1 and §5.2): `step: Nat := 1` in a
//! record, `(id: Text := "anonymous")` in a constructor. A literal
//! `{ stop = 10 }`, or a named construction `Circle { radius = 1 }`, may
//! leave out a field that has one.
//!
//! Each default becomes a generated definition, a *helper*, elaborated once
//! the type is admitted: `RangeOptions.step%default`, or
//! `Shape.Circle.id%default` for a constructor's field. Its parameters are
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
//! The helpers' names contain a `%`, which source can't write, so they
//! are kept out of the name table; [`FieldDefault`]s, kept per declaration
//! (`Data::defaults`, and in the check cache), are how a
//! literal finds them. Defaults aren't part of the type's hash (D1099): a
//! literal that uses one refers to its helper, so changing a default changes
//! exactly the hashes of the literals that leave that field out.

use std::collections::BTreeSet;
use std::rc::Rc;

use stitchwort_core::collections::HashSet;
use stitchwort_core::globals::ParamDefaults;
use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Term, Value};
use stitchwort_syntax::ast::{self, Decl, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Arg, Ctx, check, implicit_arg};
use crate::module::Phase;
use crate::named::Slot;
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
            format!("{}.{field}%default", data.name)
        } else {
            format!("{}.{}.{field}%default", data.name, ctor.name)
        }
        .into();
        // Each variable of the context: its name and type, in the context of
        // the variables before it, and how the helper takes it.
        let context: Vec<(Name, Term, Icit)> = data
            .params
            .iter()
            .chain(&ctor.fields[..i])
            .enumerate()
            .map(|(l, (x, ty))| (x.clone(), ty.clone(), helper_icit(l, np)))
            .collect();
        let field_ty = ctor.fields[i].1.clone();
        let earlier: Vec<String> = ctor.fields[..i]
            .iter()
            .map(|(x, _)| x.to_string())
            .collect();
        let later: Vec<String> = ctor.fields[i + 1..]
            .iter()
            .map(|(x, _)| x.to_string())
            .collect();
        self.make_helper(
            Of::Field,
            label,
            &context,
            &field_ty,
            value,
            &earlier,
            &later,
        )
    }

    /// After definition `id` (declared by `signature`) is declared, before
    /// its body: a helper for each of its header's default values
    /// (docs/proposals/signature-defaults.md §7.1), recorded in its
    /// `Def::param_defaults`.
    pub(crate) fn param_defaults(&mut self, signature: &Decl, id: DefId) -> Result<()> {
        let Decl::Signature { ty, defaults, .. } = signature else {
            return Ok(());
        };
        if defaults.iter().all(Option::is_none) {
            return Ok(());
        }
        let front = self.front_binders(ty)?;
        let def = self.globals.def(id);
        let owner = def.name.clone();
        let telescope = telescope(&def.ty);
        let table = self.header_helpers(&owner, &telescope, front, defaults)?;
        self.globals.set_param_defaults(id, table);
        Ok(())
    }

    /// A helper for each of `defaults`, the default values of the header's
    /// parameters, which are `telescope`'s from `front` on.
    pub(crate) fn header_helpers(
        &mut self,
        owner: &str,
        telescope: &[(Name, Term, Icit)],
        front: usize,
        defaults: &[Option<Expr>],
    ) -> Result<ParamDefaults> {
        let header = front + defaults.len();
        if telescope.len() < header {
            return Err(Diagnostic::error(
                "E-MALFORMED",
                "internal error: a definition's type has fewer parameters than its header",
            ));
        }
        let explicit = |range: std::ops::Range<usize>| -> Vec<String> {
            telescope[range]
                .iter()
                .filter(|(_, _, icit)| *icit == Icit::Explicit)
                .map(|(x, _, _)| x.to_string())
                .collect()
        };
        let mut params = vec![None; header];
        for (k, default) in defaults.iter().enumerate() {
            let Some(value) = default else { continue };
            let i = front + k;
            let (x, ty, _) = &telescope[i];
            let label: Name = format!("{owner}.{x}%default").into();
            let context: Vec<(Name, Term, Icit)> = telescope[..i]
                .iter()
                .map(|(x, ty, icit)| {
                    let icit = if *icit == Icit::Explicit {
                        Icit::Explicit
                    } else {
                        Icit::Implicit
                    };
                    (x.clone(), ty.clone(), icit)
                })
                .collect();
            let earlier = explicit(front..i);
            let later = explicit(i + 1..header);
            params[i] =
                Some(self.make_helper(Of::Param, label, &context, ty, value, &earlier, &later)?);
        }
        Ok(ParamDefaults { header, params })
    }

    /// How many implicit parameters a signature `ty` gets in front of its
    /// written ones: the names bound automatically, each with its
    /// divergence index if it has one (`signature_type`).
    fn front_binders(&self, ty: &Expr) -> Result<usize> {
        let auto = crate::autobind::auto_bound(self, ty)?;
        let indexed = match self
            .globals
            .registry
            .data(stitchwort_core::registry::Builtin::Divergence)
        {
            Some(_) if !self.total_rows_only.get() => auto.indexed_rows.len(),
            _ => 0,
        };
        Ok(auto.names.len() + indexed)
    }

    /// A default's helper, named `label`: `value` checked against `ty` in
    /// `context` (each variable's name, type in the context of those before
    /// it, and how the helper takes it), in the empty row, and closed over
    /// the variables it needs. `earlier` and `later` are the names of the
    /// fields or explicit parameters around it, for messages.
    #[allow(clippy::too_many_arguments)]
    fn make_helper(
        &mut self,
        of: Of,
        label: Name,
        context: &[(Name, Term, Icit)],
        ty: &Term,
        value: &Expr,
        earlier: &[String],
        later: &[String],
    ) -> Result<FieldDefault> {
        let field_ty = ty.clone();
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
                for (x, ty, _) in context {
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
        let body = body.map_err(|e| helper_error(of, e, earlier, later))?;
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
            let (x, dom, icit) = &context[l];
            let dom = into(dom, l, p)?;
            let icit = *icit;
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

/// A default's error, with what to know about defaults.
fn helper_error(of: Of, e: Diagnostic, earlier: &[String], later: &[String]) -> Diagnostic {
    match e.code {
        // The usual note, to add the ability (or `Partial`) to the function's type,
        // doesn't apply: a default has no type to add it to.
        "E-ABILITY" | "E-PARTIAL" => Diagnostic {
            notes: Vec::new(),
            ..e
        }
        .with_note(match of {
            Of::Field => {
                "a field's default can't perform operations: it is computed wherever a \
                 value leaves the field out"
            }
            Of::Param => {
                "a parameter's default can't perform operations: it is computed at each \
                 call that leaves the parameter out"
            }
        }),
        "E-UNKNOWN-NAME" => match later.iter().find(|x| e.message.contains(&format!("`{x}`"))) {
            Some(x) => e.with_note(format!(
                "`{x}` is a later {0}: a default may use only the {0}s before it",
                of.noun()
            )),
            None => e,
        },
        "E-REFL" | "E-TYPE-MISMATCH" if !earlier.is_empty() => {
            let quoted: Vec<String> = earlier.iter().map(|x| format!("`{x}`")).collect();
            e.with_note(match of {
                Of::Field => format!(
                    "a field's default must work for any values of the earlier fields ({}), \
                     since a value may give them and leave this one out",
                    quoted.join(", ")
                ),
                Of::Param => format!(
                    "a default must work for any values of the earlier parameters ({}), \
                     since a call may give them and leave this one out",
                    quoted.join(", ")
                ),
            })
        }
        _ => e,
    }
}

/// What a default belongs to, for its messages.
#[derive(Clone, Copy)]
enum Of {
    Field,
    Param,
}

impl Of {
    fn noun(self) -> &'static str {
        match self {
            Of::Field => "field",
            Of::Param => "parameter",
        }
    }
}

/// The parameters of a function type `ty` as written: each one's name,
/// type (in the context of those before it) and kind.
pub(crate) fn telescope(ty: &Term) -> Vec<(Name, Term, Icit)> {
    let mut out = Vec::new();
    let mut ty = ty;
    while let Term::Pi(x, icit, dom, cod) = ty.strip_loc() {
        out.push((x.clone(), (**dom).clone(), *icit));
        ty = cod;
    }
    out
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

// Calls of a definition whose parameters have defaults
// (docs/proposals/signature-defaults.md §6, §7.2).

/// What a local definition's name stands for, by which its defaults are
/// found: the frozen metavariable while its owner is elaborated, or the
/// definition once admitted early (`Elaborator::preadmit`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum LocalHead {
    Meta(usize),
    Def(DefId),
}

impl LocalHead {
    /// Whether it outlives undoing to a state with `metas` metavariables.
    pub(crate) fn before(self, metas: usize) -> bool {
        match self {
            LocalHead::Meta(m) => m < metas,
            LocalHead::Def(_) => true,
        }
    }
}

/// A local definition's defaults. Each helper is a term in the context the
/// local definition was elaborated in, of `base` variables.
pub(crate) struct LocalDefaults {
    pub base: usize,
    /// How many arguments the local definition's name is applied to before
    /// its own parameters' (the variables it captures).
    pub prefix: usize,
    pub header: usize,
    pub params: Vec<Option<LocalDefault>>,
    /// The definition's name, for messages.
    pub name: String,
}

/// One parameter's default in a local definition: its helper and the
/// earlier parameters it takes, by level, each taken as `Icit` says.
pub(crate) struct LocalDefault {
    pub helper: Term,
    pub captures: Vec<(usize, Icit)>,
}

/// Where a call's head finds its defaults.
#[derive(Clone, Copy, Debug)]
pub(crate) enum DefaultsOf {
    Def(DefId),
    Local(LocalHead),
}

/// The defaults of a call's head, as a call sees them.
#[derive(Clone, Debug)]
pub(crate) struct HeadDefaults {
    pub of: DefaultsOf,
    /// How many arguments the head is applied to already, before its first
    /// parameter's.
    pub prefix: usize,
    /// How many of its parameters are its header's: a positional argument
    /// past them in a call that leaves a default out is an error (§6.3).
    pub header: usize,
    /// Which parameters have a default.
    pub defaulted: Vec<bool>,
    /// The function's name, for messages.
    pub name: String,
}

impl HeadDefaults {
    /// The default of parameter `param`, as an argument.
    pub(crate) fn arg(&self, param: usize) -> DefaultRef {
        DefaultRef {
            of: self.of,
            prefix: self.prefix,
            param,
        }
    }
}

/// One parameter's default, as an argument of a call.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DefaultRef {
    pub of: DefaultsOf,
    pub prefix: usize,
    pub param: usize,
}

/// The defaults of `head`, a function about to be applied, if it has any:
/// a definition, or a local definition's name.
pub(crate) fn of_head(cx: &Ctx, head: &Term) -> Option<HeadDefaults> {
    let (h, args) = head.spine();
    match h {
        Term::Def(id) if args.is_empty() && cx.g().def(*id).param_defaults.is_some() => {
            let def = cx.g().def(*id);
            let table = def.param_defaults.as_ref()?;
            Some(HeadDefaults {
                of: DefaultsOf::Def(*id),
                prefix: 0,
                header: table.header,
                defaulted: table.params.iter().map(Option::is_some).collect(),
                name: crate::scope::display(&def.name).to_string(),
            })
        }
        Term::Meta(m) => local_of(cx, LocalHead::Meta(*m), args.len()),
        Term::Def(id) => local_of(cx, LocalHead::Def(*id), args.len()),
        _ => None,
    }
}

fn local_of(cx: &Ctx, head: LocalHead, prefix: usize) -> Option<HeadDefaults> {
    let table = cx.e.local_defaults.borrow().get(&head).cloned()?;
    (table.prefix == prefix).then(|| HeadDefaults {
        of: DefaultsOf::Local(head),
        prefix,
        header: table.header,
        defaulted: table.params.iter().map(Option::is_some).collect(),
        name: table.name.clone(),
    })
}

/// Whether the definition or local definition `name` refers to has
/// parameter defaults, without elaborating anything.
pub(crate) fn of_name(cx: &Ctx, name: &str) -> Option<HeadDefaults> {
    if cx.lookup(name).is_some() {
        return None;
    }
    if let Ok(Some((term, _))) = cx.local(name) {
        return of_head(cx, &term);
    }
    match cx.e.named(name) {
        Some((crate::Global::Def(id), _)) => of_head(cx, &Term::Def(*id)),
        _ => None,
    }
}

fn internal() -> Diagnostic {
    Diagnostic::error(
        "E-MALFORMED",
        "internal error: a call's default doesn't match its function",
    )
}

/// The helper of default `r`, as a term at `cx`'s level, and the
/// parameters it takes.
fn resolve(cx: &Ctx, r: DefaultRef) -> Result<(Term, Vec<(usize, Icit)>)> {
    match r.of {
        DefaultsOf::Def(id) => {
            let g = cx.g();
            let found = g
                .def(id)
                .param_defaults
                .as_ref()
                .and_then(|t| t.params.get(r.param)?.as_ref())
                .ok_or_else(internal)?;
            let icits = telescope(&g.def(found.helper).ty)
                .into_iter()
                .map(|(_, _, icit)| icit);
            Ok((
                Term::Def(found.helper),
                found.captures.iter().copied().zip(icits).collect(),
            ))
        }
        DefaultsOf::Local(head) => {
            let table =
                cx.e.local_defaults
                    .borrow()
                    .get(&head)
                    .cloned()
                    .ok_or_else(internal)?;
            let found = table
                .params
                .get(r.param)
                .and_then(Option::as_ref)
                .ok_or_else(internal)?;
            let by = cx.level().checked_sub(table.base).ok_or_else(internal)?;
            Ok((found.helper.shift(cx.g(), by, 0)?, found.captures.clone()))
        }
    }
}

/// The call of default `r`'s helper, given `params`, the terms of the
/// function's parameters before it at `cx`'s level plus `extra`.
fn helper_call_with(cx: &Ctx, r: DefaultRef, params: &[Term], extra: usize) -> Result<Term> {
    let (helper, captures) = resolve(cx, r)?;
    let mut call = helper.shift(cx.g(), extra, 0)?;
    for (l, icit) in captures {
        let arg = params.get(l).ok_or_else(internal)?;
        call = Term::app_icit(call, arg.clone(), icit);
    }
    Ok(call)
}

/// The call of default `r`'s helper for the application `term` of the
/// function to the arguments before it (`check::apply_args`, which puts
/// it in its place before any later argument is elaborated).
pub(crate) fn helper_call(cx: &Ctx, r: DefaultRef, term: &Term) -> Result<Term> {
    let (_, args) = app_spine(term);
    let params: Vec<Term> = args.into_iter().skip(r.prefix).map(|(t, _)| t).collect();
    helper_call_with(cx, r, &params, 0)
}

/// `f a b`'s function and arguments, each with how it's applied.
fn app_spine(term: &Term) -> (Term, Vec<(Term, Icit)>) {
    let mut args = Vec::new();
    let mut t = term.strip_loc();
    while let Term::App(f, a, icit) = t {
        args.push(((**a).clone(), *icit));
        t = f.strip_loc();
    }
    args.reverse();
    (t.clone(), args)
}

/// `head args`, where `head` has parameter defaults (§6.1): the arguments
/// in their parameters' places, each defaulted parameter the call doesn't
/// name given its default, and a required one left out before the last
/// given or defaulted made a parameter of the function the call is. A
/// written argument a default needs is bound by a `let` first, unless it
/// is simple (§6.5).
pub(crate) fn apply(
    cx: &mut Ctx,
    head: (Term, Value),
    defaults: HeadDefaults,
    args: &[Arg],
) -> Result<(Term, Value)> {
    let sig = crate::named::signature(cx, &head.1)?.with_defaults(defaults.clone());
    let planned = crate::named::plan_indexed(cx, &sig, args, None)?;
    let slots: Vec<Slot> = planned.iter().map(|(_, s)| s.clone()).collect();
    let snapshot = crate::undo::Snapshot::take(cx);
    let result = match crate::named::positional(&slots) {
        Some(positional) => crate::check::apply_args(cx, head.clone(), &positional)
            .and_then(|(term, ty)| Ok((bind_needed(cx, &head, term, &defaults, &planned)?, ty))),
        None => crate::named::apply_slots(cx, head.clone(), &slots),
    };
    match result {
        Err(e) if e.code == "E-TYPE-MISMATCH" && !crate::undo::fatal(&e) => {
            Err(default_note(cx, &head, &planned, snapshot, e))
        }
        other => other,
    }
}

/// The parameters of a call `planned` gives by a written argument, and
/// those it gives their defaults, with the defaults.
fn by_kind(planned: &[(Option<usize>, Slot)]) -> (Vec<usize>, Vec<(usize, DefaultRef)>) {
    let mut written = Vec::new();
    let mut defaulted = Vec::new();
    for (p, slot) in planned {
        match (p, slot) {
            (Some(p), Slot::Given(Arg::Default(r))) => defaulted.push((*p, *r)),
            (Some(p), Slot::Given(Arg::Explicit(_) | Arg::Piped(_))) => written.push(*p),
            _ => {}
        }
    }
    (written, defaulted)
}

/// `term`, the call `head` applied as `planned` says, with each written
/// argument a default takes bound by a `let` around it, unless it is
/// simple, so it isn't computed twice (§6.5).
fn bind_needed(
    cx: &mut Ctx,
    head: &(Term, Value),
    term: Term,
    defaults: &HeadDefaults,
    planned: &[(Option<usize>, Slot)],
) -> Result<Term> {
    let (written, defaulted) = by_kind(planned);
    let mut needed = BTreeSet::new();
    for (_, r) in &defaulted {
        let (_, captures) = resolve(cx, *r)?;
        needed.extend(
            captures
                .iter()
                .map(|(l, _)| *l)
                .filter(|l| written.contains(l)),
        );
    }
    if needed.is_empty() {
        return Ok(term);
    }
    let (f, spine) = app_spine(&term);
    let Some(params) = spine.get(defaults.prefix..) else {
        return Ok(term);
    };
    let lets: Vec<usize> = needed
        .into_iter()
        .filter(|&l| params.get(l).is_some_and(|(t, _)| !simple(t)))
        .collect();
    let Some(&last) = lets.last() else {
        return Ok(term);
    };
    let g = cx.g();
    // Each parameter's name and type, up to the last one bound.
    let mut ty = head.1.clone();
    let mut parts: Vec<(Name, Term)> = Vec::new();
    for (arg, _) in &params[..=last] {
        let Value::Pi(x, _, dom, cod) = force(g, ty)? else {
            return Ok(term);
        };
        parts.push((x.clone(), cx.quote(&dom)?));
        ty = cod.apply(g, cx.eval(arg)?)?;
    }
    let k = lets.len();
    let mut terms: Vec<Term> = Vec::with_capacity(params.len());
    for (t, _) in params {
        terms.push(t.shift(g, k, 0)?);
    }
    for (rank, &l) in lets.iter().enumerate() {
        terms[l] = Term::Var(k - 1 - rank);
    }
    for (p, r) in &defaulted {
        terms[*p] = helper_call_with(cx, *r, &terms[..*p], k)?;
    }
    let mut out = f.shift(g, k, 0)?;
    for (t, icit) in &spine[..defaults.prefix] {
        out = Term::app_icit(out, t.shift(g, k, 0)?, *icit);
    }
    for (t, (_, icit)) in terms.into_iter().zip(params) {
        out = Term::app_icit(out, t, *icit);
    }
    for (rank, &l) in lets.iter().enumerate().rev() {
        let (x, ty) = &parts[l];
        out = Term::let_(
            x.clone(),
            ty.shift(g, rank, 0)?,
            params[l].0.shift(g, rank, 0)?,
            out,
        );
    }
    Ok(out)
}

/// A type error in a call that left out a defaulted parameter whose value
/// a later parameter's type mentions: that parameter is its default
/// (§5.2, §8.3). Says so, with its value where it doesn't depend on the
/// call's arguments, and with what to write to give another where an
/// unknown in its place would have fitted.
fn default_note(
    cx: &mut Ctx,
    head: &(Term, Value),
    planned: &[(Option<usize>, Slot)],
    snapshot: crate::undo::Snapshot,
    e: Diagnostic,
) -> Diagnostic {
    snapshot.restore(cx);
    let (_, defaulted) = by_kind(planned);
    let Ok(deps) = crate::named::dependencies(cx, &head.1) else {
        return e;
    };
    let names = match crate::named::signature(cx, &head.1) {
        Ok(sig) => sig.params,
        Err(_) => return e,
    };
    let mentioned: Vec<(usize, DefaultRef)> = defaulted
        .into_iter()
        .filter(|(p, _)| {
            deps.iter()
                .enumerate()
                .any(|(i, d)| i > *p && d.contains(p))
        })
        .collect();
    if mentioned.is_empty() {
        return e;
    }
    // What an unknown in each one's place would be.
    let hole = Expr::Hole(cx.span);
    let slots: Vec<Slot> = planned
        .iter()
        .map(|(p, s)| match (p, s) {
            (Some(p), Slot::Given(Arg::Default(_))) if mentioned.iter().any(|(m, _)| m == p) => {
                Slot::Given(Arg::Explicit(&hole))
            }
            _ => s.clone(),
        })
        .collect();
    let mut solved: Vec<Option<String>> = vec![None; mentioned.len()];
    let again = crate::undo::Snapshot::take(cx);
    if let Some(positional) = crate::named::positional(&slots)
        && let Ok((term, _)) = crate::check::apply_args(cx, head.clone(), &positional)
    {
        let (_, args) = app_spine(&term);
        let prefix = mentioned.first().map_or(0, |(_, r)| r.prefix);
        for (k, (p, _)) in mentioned.iter().enumerate() {
            if let Some((arg, _)) = args.get(prefix + p)
                && let Ok(value) = cx.eval(arg)
                && let Ok(value) = force(cx.g(), value)
                && !matches!(
                    value,
                    Value::Neutral(stitchwort_core::value::Head::Meta(_), _)
                )
            {
                solved[k] = Some(cx.show(&value));
            }
        }
    }
    again.restore(cx);
    let mut e = e;
    for ((p, r), solved) in mentioned.iter().zip(solved) {
        let x = names
            .get(*p)
            .map_or_else(String::new, |n| n.name.to_string());
        let value = default_value(cx, *r).map_or_else(String::new, |v| format!(", `{v}`"));
        let fix = match solved {
            Some(v) => format!("give `({x} := {v})` to use another"),
            None => format!("give `({x} := …)` to use another"),
        };
        e = e.with_note(format!(
            "`{x}` is left out, so it is its default value{value}; {fix}"
        ));
    }
    e
}

/// The value of default `r`, shown, if its helper takes nothing.
pub(crate) fn default_value(cx: &Ctx, r: DefaultRef) -> Option<String> {
    let (helper, captures) = resolve(cx, r).ok()?;
    if !captures.is_empty() {
        return None;
    }
    let value = force(cx.g(), cx.eval(&helper).ok()?).ok()?;
    Some(cx.show(&value))
}

/// For a call `f args` of a function with defaults, each default the call
/// fills because it doesn't name the parameter: "`step` is its default, `1`".
pub(crate) fn filled_by_call(cx: &Ctx, expr: &Expr) -> Vec<String> {
    let (Expr::Var(name), args) = crate::check::spine(expr) else {
        return Vec::new();
    };
    let head = match cx.local(&name.text) {
        Ok(Some(head)) => head,
        _ if cx.lookup(&name.text).is_some() => return Vec::new(),
        _ => match cx.e.named(&name.text) {
            Some((crate::Global::Def(id), _)) => match kernel::def_ty(cx.g(), *id) {
                Ok(ty) => (Term::Def(*id), ty),
                Err(_) => return Vec::new(),
            },
            _ => return Vec::new(),
        },
    };
    left_out(cx, &head, &args)
        .into_iter()
        .map(|(x, r)| match default_value(cx, r) {
            Some(value) => format!("`{x}` is its default, `{value}`"),
            None => format!("`{x}` is its default"),
        })
        .collect()
}

/// The defaulted parameters of `head` that a call with `args` doesn't
/// name, each with its default.
fn left_out(cx: &Ctx, head: &(Term, Value), args: &[Arg]) -> Vec<(Name, DefaultRef)> {
    let Some(defaults) = of_head(cx, &head.0) else {
        return Vec::new();
    };
    let Ok(sig) = crate::named::signature(cx, &head.1) else {
        return Vec::new();
    };
    let given: Vec<&str> = args
        .iter()
        .filter_map(|a| match a {
            Arg::NamedExplicit(n, _) => Some(n.text.as_str()),
            _ => None,
        })
        .collect();
    (0..defaults.defaulted.len())
        .filter(|&i| defaults.defaulted[i])
        .filter_map(|i| {
            let x = &sig.params.get(i)?.name;
            (!given.contains(&&**x)).then(|| (x.clone(), defaults.arg(i)))
        })
        .collect()
}

/// For hover on the head of a call written at `at`, `head` applied to
/// `args`: each default the call used, "`step` left out: its default `1`".
pub(crate) fn note_left_out(cx: &Ctx, at: Span, head: &(Term, Value), args: &[Arg]) {
    if cx.e.nav.is_none() {
        return;
    }
    let lines: Vec<String> = left_out(cx, head, args)
        .into_iter()
        .map(|(x, r)| {
            let value = match r.of {
                DefaultsOf::Def(id) => cx.e.param_default_shown(id, r.param),
                DefaultsOf::Local(_) => default_value(cx, r),
            };
            match value {
                Some(value) => format!("`{x}` left out: its default `{value}`"),
                None => format!("`{x}` left out: its default"),
            }
        })
        .collect();
    if !lines.is_empty() {
        cx.e.note_call_defaults(at, lines.join("\n\n"));
    }
}

/// The defaults of local definition `signature`, whose key is `key`, once
/// its name, and those of the others in its group (`group`), are bound in
/// `cx` to `head` of type `head_ty` (`local.rs`): each default is
/// elaborated in `cx` with the parameters before it bound, and becomes a
/// helper lifted with the owner's other local definitions, named
/// `key.x%default`. They are recorded for the calls of the name. `front`
/// is how many implicit parameters its type has before the written ones.
pub(crate) fn local_defaults(
    cx: &mut Ctx,
    signature: &Decl,
    key: &str,
    (head, head_ty): (&Term, &Value),
    front: usize,
    group: &[&str],
) -> Result<()> {
    let Decl::Signature {
        name,
        ty: written,
        defaults,
        ..
    } = signature
    else {
        return Ok(());
    };
    if defaults.iter().all(Option::is_none) {
        return Ok(());
    }
    let (h, args) = app_spine(head);
    let local_head = match h {
        Term::Meta(m) => LocalHead::Meta(m),
        Term::Def(id) => LocalHead::Def(id),
        _ => return Err(internal()),
    };
    let prefix = args.len();
    let base = cx.level();
    let ty = cx.quote(head_ty)?;
    let telescope = telescope(&ty);
    let header = front + defaults.len();
    if telescope.len() < header {
        return Err(internal());
    }
    // A default can't use the definition, nor one defined together with it.
    for r in crate::module::default_refs(written, defaults) {
        if let crate::module::Ref::Name(n) = r
            && group.contains(&n.text.as_str())
        {
            return Err(crate::module::default_uses(&name.text, &n.text, n.span));
        }
    }
    let explicit = |range: std::ops::Range<usize>| -> Vec<String> {
        telescope[range]
            .iter()
            .filter(|(_, _, icit)| *icit == Icit::Explicit)
            .map(|(x, _, _)| x.to_string())
            .collect()
    };
    let mut params = Vec::with_capacity(header);
    params.resize_with(header, || None);
    for (k, default) in defaults.iter().enumerate() {
        let Some(value) = default else { continue };
        let i = front + k;
        let (x, dom, _) = &telescope[i];
        let helper_key = format!("{key}.{x}%default");
        let earlier = explicit(front..i);
        let later = explicit(i + 1..header);
        params[i] = Some(local_helper(
            cx,
            &telescope,
            i,
            dom,
            value,
            &helper_key,
            &format!("{}.{x}%default", name.text),
            (&earlier, &later),
        )?);
    }
    label_defaults(cx, h.clone(), &telescope[..header], &params);
    cx.e.local_defaults.borrow_mut().insert(
        local_head,
        Rc::new(LocalDefaults {
            base,
            prefix,
            header,
            params,
            name: name.text.clone(),
        }),
    );
    Ok(())
}

/// Gives the printer's label of a local definition's calls, `head`, its
/// defaults `params`, so a call shows without the arguments they fill.
/// `header` is its header's parameters.
fn label_defaults(
    cx: &Ctx,
    head: Term,
    header: &[(Name, Term, Icit)],
    params: &[Option<LocalDefault>],
) {
    let level = cx.level();
    let call = |default: &LocalDefault| -> Option<stitchwort_core::globals::DefaultCall> {
        let (helper, outer) = app_spine(&default.helper);
        let levels = outer
            .iter()
            .map(|(arg, _)| match arg.strip_loc() {
                Term::Var(ix) => level.checked_sub(ix + 1),
                _ => None,
            })
            .collect::<Option<Vec<usize>>>()?;
        Some(stitchwort_core::globals::DefaultCall {
            head: helper,
            levels,
            captures: default.captures.iter().map(|(p, _)| *p).collect(),
        })
    };
    let shown = stitchwort_core::globals::CallDefaults {
        header: header.len(),
        params: header
            .iter()
            .zip(params)
            .map(|((x, _, _), default)| (x.clone(), default.as_ref().and_then(call)))
            .collect(),
    };
    let shown = Rc::new(shown);
    let g = cx.g();
    let mut labels = g.print_labels.borrow_mut();
    if let Some(label) = labels.iter_mut().rev().find(|l| match (&l.head, &head) {
        (Term::Meta(a), Term::Meta(b)) => a == b,
        (Term::Def(a), Term::Def(b)) => a == b,
        _ => false,
    }) {
        label.defaults = Some(shown);
    }
}

/// The helper of the default `value` of parameter `i` of a local
/// definition with parameters `telescope` (in `cx`'s context), of type
/// `dom`: an admitted definition if an earlier attempt admitted it,
/// otherwise a draft lifted with the owner's.
#[allow(clippy::too_many_arguments)]
fn local_helper(
    cx: &mut Ctx,
    telescope: &[(Name, Term, Icit)],
    i: usize,
    dom: &Term,
    value: &Expr,
    key: &str,
    shown: &str,
    (earlier, later): (&[String], &[String]),
) -> Result<LocalDefault> {
    let g = cx.g();
    let base = cx.level();
    let span = value.span();
    let mark = cx.mark();
    let saved = cx.span;
    let checked = (|| -> Result<Term> {
        for (x, ty, icit) in &telescope[..i] {
            let ty = cx.eval(ty)?;
            cx.bind(x, ty);
            cx.set_kind(*icit);
        }
        cx.span = span;
        let expected = cx.eval(dom)?;
        let term = check(cx, value, &expected)?;
        cx.e.zonk_keeping(&term, cx.level(), &|_| true)
    })();
    cx.reset(mark);
    cx.span = saved;
    let term = checked.map_err(|e| helper_error(Of::Param, e, earlier, later))?;
    // What it needs: the parameters the value and its type mention, and
    // those their types mention.
    let depth = base + i;
    let mut used = BTreeSet::new();
    crate::lift::uses(&term, depth, &|_| None, &mut used);
    crate::lift::uses(dom, depth, &|_| None, &mut used);
    let mut captures: BTreeSet<usize> = used
        .into_iter()
        .filter_map(|l| l.checked_sub(base))
        .collect();
    let mut work: Vec<usize> = captures.iter().copied().collect();
    while let Some(c) = work.pop() {
        let mut deps = BTreeSet::new();
        crate::lift::uses(&telescope[c].1, base + c, &|_| None, &mut deps);
        for dep in deps.into_iter().filter_map(|l| l.checked_sub(base)) {
            if captures.insert(dep) {
                work.push(dep);
            }
        }
    }
    let captures: Vec<usize> = captures.into_iter().collect();
    let position = |c: usize| captures.iter().position(|p| *p == c);
    // `t`, in `base + depth` variables, in `base` variables and the first
    // `scope` captures.
    let into = |t: &Term, depth: usize, scope: usize| {
        crate::lift::replace_with(
            g,
            t,
            base + depth,
            &|l| {
                if l < base {
                    return Ok(Term::Var(base + scope - 1 - l));
                }
                match position(l - base) {
                    Some(p) if p < scope => Ok(Term::Var(scope - 1 - p)),
                    _ => Err(Diagnostic::error(
                        "E-MALFORMED",
                        "internal error: a parameter's default uses a variable it doesn't take",
                    )),
                }
            },
            &|_, _| None,
        )
    };
    let k = captures.len();
    let mut goal = into(dom, i, k)?;
    let mut body = into(&term, i, k)?;
    let mut taken = Vec::with_capacity(k);
    for (p, &c) in captures.iter().enumerate().rev() {
        let (x, ty, icit) = &telescope[c];
        let ty = into(ty, c, p)?;
        let icit = if *icit == Icit::Explicit {
            Icit::Explicit
        } else {
            Icit::Implicit
        };
        goal = Term::Pi(x.clone(), icit, Rc::new(ty), Rc::new(goal));
        body = Term::Lam(x.clone(), icit, Rc::new(body));
        taken.push((c, icit));
    }
    taken.reverse();
    let found =
        cx.e.preadmitted
            .borrow()
            .get(key)
            .map(|r| (r.id, r.captures.clone()));
    let helper = match found {
        Some((id, admitted)) => crate::local::admitted_call(cx, shown, id, &admitted)?.0,
        None => crate::local::draft(cx, key, shown, span, body, goal)?,
    };
    Ok(LocalDefault {
        helper,
        captures: taken,
    })
}
