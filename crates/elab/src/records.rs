//! Declared records (docs/proposals/records.md, stage 1). A record
//! `type Person = { name : Text, age : Nat }` is a data type with one
//! constructor, `Person.%mk` (which source can't write), and a field for each of the record's, so the
//! kernel needs nothing new. The elaborator adds:
//!
//! - a projection per field, `Person.name : Person -> Text`, generated as an
//!   ordinary case-tree definition, which `p.name` calls;
//! - literals `{ name = …, age = … }`, checked against an expected record
//!   type, and updates `{ p | age = … }`;
//! - record patterns `{ name, age = a, .. }`, resolved by the type of what
//!   they match;
//! - a derived `DecEq` instance, for `==`, when one can be built for the
//!   whole record (`derive.rs`);
//! - decision procedures for proof fields, which extracted JS runs to
//!   establish them for decoded input (§11.3).
//!
//! Names generated here contain a `.`, which source can't write (`Person.name`
//! in source is field access on `Person`), so they never clash with the
//! user's.

use std::borrow::Cow;
use std::collections::HashSet;
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{eval, force, quote, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, check, infer, insert};
use crate::{CtorPattern, Elaborator, Global, Result, auto, error};

/// What the elaborator knows about a record type, beyond its data type.
pub(crate) struct RecordInfo {
    /// The generated projection for each field, in declaration order, or
    /// `None` where there can't be one: a data field of a `Prop` record
    /// (taking data out of a proof isn't allowed), or a field whose type
    /// mentions such a field.
    pub projections: Vec<Option<DefId>>,
}

impl Elaborator {
    /// After record `d` is admitted: its projections, and `==` if it can be
    /// derived.
    pub(crate) fn after_record(&mut self, d: DataId, interface: bool) -> Result<()> {
        let projections = self.projections(d, interface)?;
        self.records.insert(d, RecordInfo { projections });
        if interface {
            let projections = self.records[&d]
                .projections
                .iter()
                .map(|p| p.expect("an interface is in `Type`"))
                .collect();
            self.after_interface(d, projections)?;
        }
        self.unnoted(|e| {
            e.derive_data_eq(d)?;
            e.derive_data_show(d)?;
            e.derive_data_ord(d)?;
            if !interface {
                e.derive_record_ext(d)?;
            }
            Ok(())
        })
    }

    /// Defines `R.field : [params] -> (r : R params) -> T` for each field,
    /// by matching `r`. In `T`, earlier fields are their projections of `r`.
    /// For an interface, they're `R.%field`, out of the way of its methods
    /// (`interfaces.rs`).
    fn projections(&mut self, d: DataId, interface: bool) -> Result<Vec<Option<DefId>>> {
        let mut out: Vec<Option<DefId>> = Vec::new();
        let count = self.globals.data(d).ctors[0].fields.len();
        for i in 0..count {
            let g = &self.globals;
            let data = g.data(d);
            let (ctor, np) = (&data.ctors[0], data.params.len());
            let (field, field_ty) = ctor.fields[i].clone();
            let missing = |j: usize| out[j].is_none() && field_ty.mentions(i - 1 - j);
            if (data.sort == Sort::Prop && ctor.field_sorts[i] != Sort::Prop) || (0..i).any(missing)
            {
                out.push(None);
                continue;
            }
            // The earlier fields, as projections of `r` (at level `np`).
            let with_r: Vec<Value> = (0..=np).map(Value::var).collect();
            let mut env: Vec<Value> = with_r[..np].to_vec();
            for proj in &out {
                env.push(match proj {
                    Some(p) => eval(g, &with_r, &applied(*p, np))?,
                    None => unused(),
                });
            }
            let result = quote(g, np + 1, &eval(g, &env, &field_ty)?)?;
            let params: Vec<Term> = (0..np).map(|k| Term::Var(np - 1 - k)).collect();
            let mut ty = Term::Pi(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::data(d, params)),
                Rc::new(result),
            );
            let names: Vec<Name> = ctor.fields.iter().map(|(x, _)| x.clone()).collect();
            let mut body = Term::Lam(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::Case(
                    0,
                    d,
                    vec![Branch {
                        body: Some(Rc::new(Term::Var(count - 1 - i))),
                        names,
                    }]
                    .into(),
                )),
            );
            for (x, t) in data.params.iter().rev() {
                ty = Term::Pi(x.clone(), Icit::Implicit, Rc::new(t.clone()), Rc::new(ty));
                body = Term::Lam(x.clone(), Icit::Implicit, Rc::new(body));
            }
            let hidden = if interface { "%" } else { "" };
            let name: Name = format!("{}.{hidden}{field}", data.name).into();
            let span = data.span;
            let id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
            kernel::define_def(&mut self.globals, id, &body)?;
            // In the record's namespace, but not visible by its short name:
            // fields are reached through a record (`p.name`), or written in
            // full (`Person.name`).
            let key = Self::member_key(&self.data_key(d), &format!("{hidden}{field}"));
            self.scope.insert(&key, Global::Def(id), span, false);
            self.scope.mark_member(&key);
            out.push(Some(id));
        }
        Ok(out)
    }

    /// Finds a decision procedure for each proof field of each record that
    /// values of `ty` contain, for extracted JS to run on decoded input
    /// (docs/proposals/records.md §11.3), unless it already has one. `what`
    /// names the export, for the error when a proof field has none.
    pub(crate) fn record_validators(
        &mut self,
        ty: &Value,
        what: &str,
        span: Span,
        seen: &mut HashSet<DataId>,
    ) -> Result<()> {
        let mut pending = vec![ty.clone()];
        while let Some(ty) = pending.pop() {
            let Value::Data(d, args) = force(&self.globals, ty)? else {
                continue;
            };
            pending.extend(args);
            if !seen.insert(d) {
                continue;
            }
            let data = self.globals.data(d);
            let (np, ctors) = (data.params.len(), data.ctors.len());
            for c in 0..ctors {
                // The parameters and fields, as variables, and their types.
                let mut env: Vec<Value> = Vec::new();
                let mut types: Vec<Value> = Vec::new();
                for k in 0..np {
                    let param_ty = &self.globals.data(d).params[k].1;
                    types.push(eval(&self.globals, &env, param_ty)?);
                    env.push(Value::var(k));
                }
                let fields = self.globals.data(d).ctors[c].fields.len();
                for i in 0..fields {
                    let data = self.globals.data(d);
                    let ctor = &data.ctors[c];
                    let ty = eval(&self.globals, &env, &ctor.fields[i].1)?;
                    let erased = ctor.field_erased[i];
                    let missing = data.record
                        && ctor.field_sorts[i] == Sort::Prop
                        && !data.validators.iter().any(|v| v.ctor == c && v.field == i);
                    if missing {
                        self.field_validator(d, c, i, &env, &types, what, span)?;
                    } else if !erased {
                        pending.push(ty.clone());
                    }
                    types.push(ty);
                    env.push(Value::var(env.len()));
                }
            }
        }
        Ok(())
    }

    /// Finds and adds the decision procedure for proof field `i` of
    /// constructor `c` of record `d`, whose context (parameters and earlier
    /// fields) is `env` with types `types`.
    #[allow(clippy::too_many_arguments)]
    fn field_validator(
        &mut self,
        d: DataId,
        c: usize,
        i: usize,
        env: &[Value],
        types: &[Value],
        what: &str,
        span: Span,
    ) -> Result<()> {
        let Some(decidable) = self.globals.registry.data(Builtin::Decidable) else {
            return Ok(());
        };
        let data = self.globals.data(d);
        let (record, field) = (data.name.clone(), data.ctors[c].fields[i].0.clone());
        let mut names: Vec<Name> = data.params.iter().map(|(x, _)| x.clone()).collect();
        names.extend(data.ctors[c].fields[..i].iter().map(|(x, _)| x.clone()));
        let field_ty = data.ctors[c].fields[i].1.clone();
        self.clear_metas();
        let shown = stitchwort_core::pretty::term(&self.globals, &names, &field_ty);
        let mut cx = Ctx::from_parts(self, env.to_vec(), types.to_vec(), names, span);
        let prop = cx.eval(&field_ty)?;
        let decision = auto::decide(&mut cx, &prop, 0).map_err(|e| {
            if e.code == "E-RESOURCE" {
                return e;
            }
            Diagnostic::error("E-EXPORT", format!("`{what}` can't be exported"))
                .with_label(
                    span,
                    format!(
                        "`{record}`'s proof field `{field}` (`{shown}`) can't be checked at runtime"
                    ),
                )
                .with_note(
                    "a record passed in from JavaScript has no proofs: each proof field needs a \
                     decision procedure (an `instance` returning `Decidable …`), defined before the \
                     export, to establish it",
                )
        })?;
        let decision = self.finish(&decision, env.len())?;
        self.clear_metas();
        kernel::add_field_validator(&mut self.globals, d, c, i, decidable, &decision)
    }

    /// The constructor pattern a record pattern stands for, matching a value
    /// of type `ty` (if known): each field's pattern in declaration order,
    /// with `_` for those left out by `..`.
    pub(crate) fn record_pattern<'a>(
        &self,
        fields: &'a [(ast::Name, Pattern)],
        rest: bool,
        span: Span,
        ty: Option<&Value>,
    ) -> Result<CtorPattern<'a>> {
        let g = &self.globals;
        let d = match ty.map(|t| force(g, t.clone())).transpose()? {
            Some(Value::Data(d, _)) if g.data(d).record => d,
            Some(Value::Data(d, _)) => {
                return Err(error(
                    "E-NOT-A-RECORD",
                    span,
                    format!(
                        "this is a record pattern, but it matches a `{}`, which isn't a record",
                        g.data(d).name
                    ),
                ));
            }
            _ => {
                return Err(error(
                    "E-CANNOT-INFER",
                    span,
                    "can't tell which record type this pattern matches",
                )
                .with_note(
                    "a record pattern needs the type of what it matches to be known: a \
                     parameter's type from the signature, or a field's from the constructor \
                     around it",
                ));
            }
        };
        let ctor = &g.data(d).ctors[0];
        check_field_names(g, d, fields.iter().map(|(n, _)| n))?;
        fields.iter().for_each(|(n, _)| self.note_field(d, n));
        let mut args = Vec::new();
        for (field, _) in &ctor.fields {
            match fields.iter().find(|(n, _)| *n.text == **field) {
                Some((_, p)) => args.push(Cow::Borrowed(p)),
                None if rest => args.push(Cow::Owned(Pattern::Wildcard(span))),
                None => {
                    return Err(error(
                        "E-RECORD-FIELD",
                        span,
                        format!("this pattern doesn't match field `{field}`"),
                    )
                    .with_note("add it, or end the pattern with `..` to ignore the other fields"));
                }
            }
        }
        Ok(CtorPattern {
            data: d,
            ctor: 0,
            args,
            span,
        })
    }

    /// `C { f = p, g, .. }` (docs/proposals/variant-fields.md §4): the
    /// positional pattern for constructor `c` of `d`, with the pattern given
    /// for each explicit field named, `_` for those left out (with `..`).
    /// Implicit fields are left to `ctor_pattern_args`, which fills them
    /// with `_` as for a positional pattern. `ty` is the type of what the
    /// pattern matches, if known: only for the notes about a record
    /// argument.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn ctor_fields_pattern<'a>(
        &self,
        d: DataId,
        c: usize,
        written: &ast::Name,
        fields: &'a [(ast::Name, Pattern)],
        rest: bool,
        span: Span,
        ty: Option<&Value>,
    ) -> Result<CtorPattern<'a>> {
        let g = &self.globals;
        let ctor = &g.data(d).ctors[c];
        let explicit: Vec<usize> = (0..ctor.fields.len())
            .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
            .collect();
        let argument = self.record_argument(d, c, &explicit, ty)?;
        let mut seen: Vec<&ast::Name> = Vec::new();
        for (name, _) in fields {
            if !explicit.iter().any(|&i| *ctor.fields[i].0 == *name.text) {
                return Err(self.unknown_ctor_field(d, c, &explicit, name, fields, argument));
            }
            if let Some(first) = seen.iter().find(|s| s.text == name.text) {
                return Err(error(
                    "E-RECORD-FIELD",
                    name.span,
                    format!("field `{}` is given twice", name.text),
                )
                .with_label(first.span, "first given here"));
            }
            seen.push(name);
        }
        fields
            .iter()
            .for_each(|(n, _)| self.note_ctor_field(written.span, n));
        let mut args = Vec::new();
        for &i in &explicit {
            let field = &ctor.fields[i].0;
            match fields.iter().find(|(n, _)| *n.text == **field) {
                Some((_, p)) => args.push(Cow::Borrowed(p)),
                None if rest => args.push(Cow::Owned(Pattern::Wildcard(span))),
                None => {
                    return Err(error(
                        "E-RECORD-FIELD",
                        span,
                        format!(
                            "this pattern doesn't match `{}`'s field `{field}`",
                            ctor.name
                        ),
                    )
                    .with_note("add it, or end the pattern with `..` to ignore the other fields"));
                }
            }
        }
        // `Some { value = n, .. }` where `Some` holds a record that has a
        // field `value` too: legal, and names `Some`'s own field, but easily
        // meant as the record's (variant-fields.md §12.3).
        if let Some(r) = argument
            && !fields.is_empty()
            && fields.iter().all(|(n, _)| record_has(g, r, &n.text))
        {
            let field = &ctor.fields[explicit[0]].0;
            let mut warnings = self.lambda_warnings.borrow_mut();
            if !warnings
                .iter()
                .any(|w| w.labels.first().is_some_and(|l| l.span == span))
            {
                warnings.push(
                    Diagnostic::warning(
                        "W-RECORD-ARGUMENT",
                        format!(
                            "this names `{}`'s own field `{field}`, not a field of the record it holds",
                            ctor.name
                        ),
                    )
                    .with_label(span, format!("matches `{}`'s field `{field}`", ctor.name))
                    .with_note(format!(
                        "`{}`'s field holds the record type `{}`, which has fields of these names; to match \
                         those, write `{} ({{ … }})`; to keep this meaning, write `{} p`",
                        ctor.name,
                        g.data(r).name,
                        written.text,
                        written.text
                    )),
                );
            }
        }
        Ok(CtorPattern {
            data: d,
            ctor: c,
            args,
            span,
        })
    }

    /// The record type of constructor `c`'s one explicit field, if it has
    /// exactly one and its type (where the pattern's type `ty` is known) is
    /// a record.
    fn record_argument(
        &self,
        d: DataId,
        c: usize,
        explicit: &[usize],
        ty: Option<&Value>,
    ) -> Result<Option<DataId>> {
        let g = &self.globals;
        let [only] = explicit else {
            return Ok(None);
        };
        let types = self.field_types(ty, d, c, 0)?;
        let Some(Some(field_ty)) = types.get(*only) else {
            return Ok(None);
        };
        Ok(match force(g, field_ty.clone())? {
            Value::Data(r, _) if g.data(r).record => Some(r),
            _ => None,
        })
    }

    /// `C { f = … }` where `C` has no explicit field `f`.
    fn unknown_ctor_field(
        &self,
        d: DataId,
        c: usize,
        explicit: &[usize],
        name: &ast::Name,
        fields: &[(ast::Name, Pattern)],
        argument: Option<DataId>,
    ) -> Diagnostic {
        let g = &self.globals;
        let ctor = &g.data(d).ctors[c];
        if ctor.fields.iter().any(|(f, _)| **f == *name.text) {
            return error(
                "E-UNKNOWN-FIELD",
                name.span,
                format!("`{}` is an implicit field of `{}`", name.text, ctor.name),
            )
            .with_note(format!(
                "braces name explicit fields only; match an implicit one positionally, \
                 `{} [{} := p] …`",
                ctor.name, name.text
            ));
        }
        let listed: Vec<String> = explicit
            .iter()
            .map(|&i| format!("`{}`", ctor.fields[i].0))
            .collect();
        let mut e = error(
            "E-UNKNOWN-FIELD",
            name.span,
            format!("`{}` has no field `{}`", ctor.name, name.text),
        )
        .with_note(if listed.is_empty() {
            format!("`{}` has no fields", ctor.name)
        } else {
            format!("`{}`'s fields are {}", ctor.name, listed.join(", "))
        });
        if let Some(r) = argument
            && fields.iter().all(|(n, _)| record_has(g, r, &n.text))
        {
            e = e.with_note(format!(
                "braces right after a constructor name its own fields; to match the `{}` \
                 it holds, write `{} ({{ … }})`",
                g.data(r).name,
                ctor.name
            ));
        }
        e
    }
}

/// Whether record type `r` has a field `name`.
fn record_has(g: &stitchwort_core::Globals, r: DataId, name: &str) -> bool {
    g.data(r).ctors[0].fields.iter().any(|(f, _)| **f == *name)
}

/// `R.field` applied to the parameters (implicitly) and the record, in the
/// context of the parameters and then the record.
fn applied(proj: DefId, np: usize) -> Term {
    let mut term = Term::Def(proj);
    for k in 0..np {
        term = Term::app_icit(term, Term::Var(np - k), Icit::Implicit);
    }
    Term::app(term, Term::Var(0))
}

/// Refuses a field name that `d` doesn't have, or one given twice.
fn check_field_names<'n>(
    g: &stitchwort_core::Globals,
    d: DataId,
    names: impl Iterator<Item = &'n ast::Name>,
) -> Result<()> {
    let data = g.data(d);
    let mut seen: Vec<&ast::Name> = Vec::new();
    for name in names {
        if !data.ctors[0].fields.iter().any(|(f, _)| **f == *name.text) {
            return Err(unknown_field(g, d, name));
        }
        if let Some(first) = seen.iter().find(|s| s.text == name.text) {
            return Err(error(
                "E-RECORD-FIELD",
                name.span,
                format!("field `{}` is given twice", name.text),
            )
            .with_label(first.span, "first given here"));
        }
        seen.push(name);
    }
    Ok(())
}

fn unknown_field(g: &stitchwort_core::Globals, d: DataId, name: &ast::Name) -> Diagnostic {
    let data = g.data(d);
    let fields: Vec<String> = data.ctors[0]
        .fields
        .iter()
        .map(|(f, _)| format!("`{f}`"))
        .collect();
    let listed = if fields.is_empty() {
        "it has no fields".to_string()
    } else {
        format!("its fields are {}", fields.join(", "))
    };
    error(
        "E-UNKNOWN-FIELD",
        name.span,
        format!("`{}` has no field `{}`", data.name, name.text),
    )
    .with_note(listed)
}

/// The record type `ty` is, if it is one; otherwise the error for using
/// `what` (a literal, an update, or `.field`) on it.
fn record_type(cx: &Ctx, ty: &Value, what: &str) -> Result<(DataId, Vec<Value>)> {
    let g = cx.g();
    match force(g, ty.clone())? {
        Value::Data(d, params) if g.data(d).record => Ok((d, params)),
        Value::Neutral(stitchwort_core::value::Head::Meta(_), _) => Err(cx
            .error(
                "E-CANNOT-INFER",
                format!("can't tell which record type {what} is"),
                "its type isn't known here",
            )
            .with_note("add a type annotation, as in `(p: Person)`")),
        other => Err(cx.error(
            "E-NOT-A-RECORD",
            format!("{what} needs a record"),
            format!("this has type `{}`, which isn't a record", cx.show(&other)),
        )),
    }
}

/// A record literal or update, checked against `expected`.
pub(crate) fn check_record(
    cx: &mut Ctx,
    base: Option<&Expr>,
    fields: &[(ast::Name, Expr)],
    expected: &Value,
) -> Result<Term> {
    match base {
        None => {
            let (d, params) = record_type(cx, expected, "this record literal")?;
            literal(cx, d, &params, fields)
        }
        Some(base) => {
            let base = check(cx, base, expected)?;
            update(cx, base, expected, fields)
        }
    }
}

/// A record update, inferring its type from its base.
pub(crate) fn infer_update(
    cx: &mut Ctx,
    base: &Expr,
    fields: &[(ast::Name, Expr)],
) -> Result<(Term, Value)> {
    let (base, ty) = infer(cx, base)?;
    let (base, ty) = insert(cx, base, ty)?;
    let term = update(cx, base, &ty, fields)?;
    Ok((term, ty))
}

/// `{ f = e, … }` at record `d` with parameters `params`: every field given
/// once, in any order. Fields are checked in declaration order, since a
/// field's type can mention earlier fields; that doesn't change the order
/// they run in (docs/proposals/records.md §6.1).
fn literal(
    cx: &mut Ctx,
    d: DataId,
    params: &[Value],
    fields: &[(ast::Name, Expr)],
) -> Result<Term> {
    let g = cx.g();
    check_field_names(g, d, fields.iter().map(|(n, _)| n))?;
    fields.iter().for_each(|(n, _)| cx.e.note_field(d, n));
    let ctor = &g.data(d).ctors[0];
    // An interface's superclass fields may be left out: they're filled in
    // (docs/proposals/interfaces.md §5.8 (a)).
    let supers: Vec<usize> = match cx.e.interfaces.get(&d) {
        Some(info) => info.supers.iter().map(|(i, _)| *i).collect(),
        None => Vec::new(),
    };
    let missing: Vec<String> = ctor
        .fields
        .iter()
        .enumerate()
        .filter(|(i, (f, _))| !supers.contains(i) && !fields.iter().any(|(n, _)| *n.text == **f))
        .map(|(_, (f, _))| format!("`{f}`"))
        .collect();
    if !missing.is_empty() {
        return Err(cx.error(
            "E-RECORD-FIELD",
            format!(
                "this `{}` is missing {}",
                g.data(d).name,
                missing.join(", ")
            ),
            "every field must be given",
        ));
    }
    let mut env = params.to_vec();
    let mut terms = Vec::new();
    for (i, (field, field_ty)) in ctor.fields.iter().enumerate() {
        let ty = eval(g, &env, field_ty)?;
        let term = match fields.iter().find(|(n, _)| *n.text == **field) {
            Some((_, expr)) => check(cx, expr, &ty)?,
            None => {
                // An omitted superclass: a typed unknown, with an obligation
                // to find it, before the later fields are checked; solved now
                // if it can be, otherwise with the declaration's others.
                let meta = crate::check::implicit_arg(cx, Icit::Auto, &ty);
                cx.e.solve_now(&meta)?;
                meta
            }
        };
        env.push(if kernel::later_types_mention(&ctor.fields, i) {
            cx.eval(&term)?
        } else {
            unused()
        });
        terms.push(term);
    }
    Ok(Term::ctor(d, 0, terms))
}

/// `{ base | f = e, … }`, where `base : ty`: a new record with the given
/// fields replaced and the others projected from `base`, which is evaluated
/// once. A later field whose type mentions a replaced one must be replaced
/// too (DESIGN.md §9).
fn update(cx: &mut Ctx, base: Term, ty: &Value, fields: &[(ast::Name, Expr)]) -> Result<Term> {
    let g = cx.g();
    let (d, params) = record_type(cx, ty, "this update")?;
    check_field_names(g, d, fields.iter().map(|(n, _)| n))?;
    fields.iter().for_each(|(n, _)| cx.e.note_field(d, n));
    let data = g.data(d);
    let ctor = &data.ctors[0];
    let replaced = |f: &str| fields.iter().any(|(n, _)| n.text == f);
    for (j, (field, field_ty)) in ctor.fields.iter().enumerate() {
        if replaced(field) {
            continue;
        }
        if let Some((dep, _)) = ctor.fields[..j]
            .iter()
            .enumerate()
            .find(|(i, (f, _))| replaced(f) && field_ty.mentions(j - 1 - i))
            .map(|(_, f)| f)
        {
            return Err(cx
                .error(
                    "E-RECORD-UPDATE",
                    format!("updating `{dep}` needs `{field}` updated too"),
                    format!("the type of `{field}` mentions `{dep}`"),
                )
                .with_note(format!(
                    "give a new `{field}` for the new `{dep}`: `{{ … | {dep} = …, {field} = … }}`"
                )));
        }
    }
    // A base that isn't a variable is bound to one first, so it's evaluated
    // once, rather than once per field taken from it.
    let bound = !matches!(base.strip_loc(), Term::Var(_));
    let mark = cx.mark();
    let base_var = if bound {
        cx.bind_hidden("%record".into(), ty.clone());
        Term::Var(0)
    } else {
        base.clone()
    };
    let result = update_fields(cx, d, &params, &base_var, fields);
    cx.reset(mark);
    let body = result?;
    if !bound {
        return Ok(body);
    }
    let pi = Term::Pi(
        "%record".into(),
        Icit::Explicit,
        Rc::new(cx.quote(ty)?),
        Rc::new(quote(g, cx.level() + 1, ty)?),
    );
    let lam = Term::Lam("%record".into(), Icit::Explicit, Rc::new(body));
    Ok(Term::app(Term::Ann(Rc::new(lam), Rc::new(pi)), base))
}

/// The fields of an update, in the context where `base` is a variable.
fn update_fields(
    cx: &mut Ctx,
    d: DataId,
    params: &[Value],
    base: &Term,
    fields: &[(ast::Name, Expr)],
) -> Result<Term> {
    let g = cx.g();
    let data = g.data(d);
    let ctor = &data.ctors[0];
    let mut env = params.to_vec();
    let mut terms = Vec::new();
    for (i, (field, field_ty)) in ctor.fields.iter().enumerate() {
        let ty = eval(g, &env, field_ty)?;
        let term = match fields.iter().find(|(n, _)| *n.text == **field) {
            Some((_, expr)) => check(cx, expr, &ty)?,
            None => {
                let Some(proj) = cx.e.records.get(&d).and_then(|r| r.projections[i]) else {
                    return Err(cx.error(
                        "E-PROP-ELIM",
                        format!("can't take field `{field}` out of a proof"),
                        format!("`{}` is a proposition, so give `{field}` here", data.name),
                    ));
                };
                let mut term = Term::Def(proj);
                for p in params {
                    term = Term::app_icit(term, cx.quote(p)?, Icit::Implicit);
                }
                Term::app(term, base.clone())
            }
        };
        env.push(if kernel::later_types_mention(&ctor.fields, i) {
            cx.eval(&term)?
        } else {
            unused()
        });
        terms.push(term);
    }
    Ok(Term::ctor(d, 0, terms))
}
