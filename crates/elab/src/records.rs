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
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::collections::HashSet;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, check, infer, insert};
use crate::{CtorPattern, Elaborator, Result, auto, error};

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
            e.derive_data_finite(d)?;
            e.derive_nested(d)?;
            if !interface {
                e.derive_record_ext(d)?;
            }
            Ok(())
        })
    }

    /// The generated projection of each field of record `d`, in
    /// declaration order, or `None` where there can't be one: its
    /// shared-field accessors (`shared.rs`), of which a record is the
    /// one-constructor case. For an interface, they're `R.%field`, out of
    /// the way of its methods (`interfaces.rs`).
    fn projections(&mut self, d: DataId, interface: bool) -> Result<Vec<Option<DefId>>> {
        let made = self.accessors(d, if interface { "%" } else { "" })?;
        Ok(self.globals.data(d).ctors[0]
            .fields
            .iter()
            .map(|(f, _)| made.get(f).copied())
            .collect())
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
            // The library's `Map` is no record to decode field by field: a
            // `Map Text V` crosses as an object, built by `Map.fromList`, and
            // any other map is refused by the extractor, saying so.
            if self.globals.registry.loaded_data(Builtin::Map) == Some(d) {
                continue;
            }
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
        let held = self.held_data(d, c, &explicit, ty)?;
        let mut seen: Vec<&ast::Name> = Vec::new();
        for (name, _) in fields {
            if !explicit.iter().any(|&i| *ctor.fields[i].0 == *name.text) {
                let names: Vec<&ast::Name> = fields.iter().map(|(n, _)| n).collect();
                return Err(self.unknown_ctor_field(d, c, &explicit, name, &names, held, "match"));
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
        Ok(self
            .held_data(d, c, explicit, ty)?
            .filter(|&r| self.globals.data(r).record))
    }

    /// The data type of constructor `c`'s one explicit field, if it has
    /// exactly one, its type (where the pattern's type `ty` is known) is a
    /// data type, and that has one constructor.
    fn held_data(
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
            Value::Data(r, _) if g.data(r).ctors.len() == 1 => Some(r),
            _ => None,
        })
    }

    /// `C { f = … }` where `C` has no explicit field `f`. `names` are all
    /// the names given; `verb` says what the braces do (`match`, `build`).
    #[allow(clippy::too_many_arguments)]
    fn unknown_ctor_field(
        &self,
        d: DataId,
        c: usize,
        explicit: &[usize],
        name: &ast::Name,
        names: &[&ast::Name],
        argument: Option<DataId>,
        verb: &str,
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
                "braces name explicit fields only; {verb} an implicit one positionally, \
                 `{} [{} := {}] …`",
                ctor.name,
                name.text,
                if verb == "match" { "p" } else { "e" }
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
            && names.iter().all(|n| record_has(g, r, &n.text))
        {
            let braces = if g.data(r).record {
                "({ … })".to_string()
            } else {
                format!("({} {{ … }})", g.data(r).ctors[0].name)
            };
            e = e.with_note(format!(
                "braces right after a constructor name its own fields; to {verb} the `{}` \
                 it holds, write `{} {braces}`",
                g.data(r).name,
                ctor.name
            ));
        }
        e
    }
}

/// `C { f = e, … }` in an expression (docs/proposals/variant-fields.md
/// §4.5): the positional application `C e₁ … eₙ`, the explicit fields'
/// values in declaration order, which is then elaborated as if written so
/// (the same term, so the same hash). As for a record literal, every
/// explicit field is given once; implicit fields are left to unification,
/// as in a positional application. `expected`, where known, only adds a
/// note when the names are those of the record a one-field constructor
/// holds. Fields with defaults may be left out
/// (docs/proposals/named-arguments.md §5.1).
pub(crate) fn ctor_fields(
    cx: &mut Ctx,
    written: &ast::Name,
    fields: &[(ast::Name, Expr)],
    span: Span,
    expected: Option<&Value>,
) -> Result<Construction> {
    let (d, c) = match cx.e.ctor_named(&written.text, written.span) {
        Ok(found) => found,
        Err(e) if e.code == "E-NOT-A-CONSTRUCTOR" => {
            return not_a_ctor(cx, written, fields, span, e).map(Construction::Positional);
        }
        Err(e) => return Err(e),
    };
    let g = cx.g();
    let ctor = &g.data(d).ctors[c];
    let explicit: Vec<usize> = (0..ctor.fields.len())
        .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
        .collect();
    let mut seen: Vec<&ast::Name> = Vec::new();
    for (name, _) in fields {
        if !explicit.iter().any(|&i| *ctor.fields[i].0 == *name.text) {
            let held = cx.e.held_data(d, c, &explicit, expected)?;
            let names: Vec<&ast::Name> = fields.iter().map(|(n, _)| n).collect();
            return Err(cx
                .e
                .unknown_ctor_field(d, c, &explicit, name, &names, held, "build"));
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
    let left_out = |i: &usize| !fields.iter().any(|(n, _)| *n.text == *ctor.fields[*i].0);
    let missing: Vec<String> = explicit
        .iter()
        .filter(|i| left_out(i) && cx.e.field_default(d, c, **i).is_none())
        .map(|&i| format!("`{}`", ctor.fields[i].0))
        .collect();
    if !missing.is_empty() {
        let defaulted = cx.e.defaulted_fields(d, c);
        let mut error = Diagnostic::error(
            "E-RECORD-FIELD",
            format!("this `{}` is missing {}", ctor.name, missing.join(", ")),
        )
        .with_label(
            span,
            if defaulted.is_empty() {
                "every explicit field must be given"
            } else {
                "every explicit field without a default value must be given"
            },
        );
        if let Some(note) = crate::defaults::defaulted_note(&defaulted) {
            error = error.with_note(note);
        }
        return Err(error);
    }
    if explicit.iter().any(left_out) {
        fields
            .iter()
            .for_each(|(n, _)| cx.e.note_ctor_field(written.span, n));
        return Ok(Construction::Defaults(d, c));
    }
    let mut positional = Expr::Var(written.clone());
    for &i in &explicit {
        let field = &ctor.fields[i].0;
        let (_, value) = fields
            .iter()
            .find(|(n, _)| *n.text == **field)
            .expect("every field is given");
        positional = Expr::App(Box::new(positional), Box::new(value.clone()));
    }
    // After `ctor_named` noted the constructor, so the field names find it.
    fields
        .iter()
        .for_each(|(n, _)| cx.e.note_ctor_field(written.span, n));
    Ok(Construction::Positional(positional))
}

/// What a named construction `C { f = e, … }` is elaborated as.
pub(crate) enum Construction {
    /// The positional application, every explicit field given.
    Positional(Expr),
    /// Constructor `c` of `d`, leaving out fields that have defaults
    /// (`defaults::ctor_with_defaults`).
    Defaults(DataId, usize),
}

/// `T { … }` where `T` isn't a constructor. A type or a function keeps the
/// braces' old meaning, a record literal as its argument: `AtR { q = … }`
/// in a type indexed by a record. A record type's own name is refused,
/// `e`, with a note: its literal is written without the name.
fn not_a_ctor(
    cx: &Ctx,
    written: &ast::Name,
    fields: &[(ast::Name, Expr)],
    span: Span,
    e: Diagnostic,
) -> Result<Expr> {
    if matches!(
        cx.e.resolve_exact(written),
        Ok((crate::Global::Data(d), ..)) if cx.g().data(d).record
    ) {
        return Err(e.with_note(format!(
            "`{0}` is a record type: a literal is written without its name, \
             `({{ … }}: {0})` where the type isn't known",
            written.text
        )));
    }
    let record = Expr::Record {
        base: None,
        fields: fields.to_vec(),
        span: Span {
            start: written.span.end + 1,
            ..span
        },
    };
    Ok(Expr::App(
        Box::new(Expr::Var(written.clone())),
        Box::new(record),
    ))
}

/// Whether record type `r` has a field `name`.
fn record_has(g: &stitchwort_core::Globals, r: DataId, name: &str) -> bool {
    g.data(r).ctors[0].fields.iter().any(|(f, _)| **f == *name)
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

/// Whether `ty` is a data type that isn't a record, whose values an update
/// rebuilds by their constructor (docs/proposals/variant-fields.md §6).
fn variant(cx: &Ctx, ty: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(matches!(force(g, ty.clone())?, Value::Data(d, _) if !g.data(d).record))
}

/// When the field-name rule ([`infer_literal`]) is held back. A construct
/// that infers one part and, if that can't be done, takes the type from
/// another part (the sides of `==` and of other comparisons, `a ++ b`, a
/// `calc`'s first term) infers that first part with the rule held back
/// ([`held`]), so a literal there is `E-CANNOT-INFER` as before the rule
/// existed and the other part says its type. Only if the whole construct
/// then fails is it elaborated again with the rule in force
/// ([`last_resort`]). So the rule applies only where nothing else says the
/// type, and a program that elaborated without it elaborates as before.
/// Holding it back changes when the rule is used, never what it looks at:
/// that is still only the literal's field names and the names in scope
/// (D1991, assumption R1).
///
/// Since K1 (postponement.md, stage 2) nothing is held back: a literal of
/// unknown type waits in the queue instead of failing, and the rule runs as
/// its default at the end, so the other part always gets to say the type
/// first and [`last_resort`] never runs again. Stage 5 removes this.
#[derive(Default)]
pub(crate) struct FieldNames {
    /// Above zero inside [`held`].
    held: std::cell::Cell<usize>,
    /// Above zero while [`last_resort`] tries again: nothing is held then.
    released: std::cell::Cell<usize>,
    /// How many literals have been held back.
    hits: std::cell::Cell<usize>,
}

impl FieldNames {
    /// Whether the rule is held back here, counting it if so.
    #[expect(dead_code, reason = "a literal waits instead (K1); stage 5 removes it")]
    fn hold(&self) -> bool {
        let held = self.held.get() > 0 && self.released.get() == 0;
        if held {
            self.hits.set(self.hits.get() + 1);
        }
        held
    }

    pub(crate) fn reset(&self) {
        self.held.set(0);
        self.released.set(0);
        self.hits.set(0);
    }
}

/// Runs `f` with the field-name rule held back ([`FieldNames`]).
pub(crate) fn held<T>(cx: &mut Ctx, f: impl FnOnce(&mut Ctx) -> T) -> T {
    let names = &cx.e.field_names;
    names.held.set(names.held.get() + 1);
    let result = f(cx);
    let names = &cx.e.field_names;
    names.held.set(names.held.get() - 1);
    result
}

/// Runs `f`, which holds the field-name rule back somewhere ([`held`]); if
/// it fails after holding back a literal, undoes it and runs it again with
/// the rule in force, giving that result.
pub(crate) fn last_resort<T>(cx: &mut Ctx, f: impl Fn(&mut Ctx) -> Result<T>) -> Result<T> {
    if cx.e.field_names.released.get() > 0 {
        return f(cx);
    }
    let hits = cx.e.field_names.hits.get();
    let snapshot = crate::undo::Snapshot::take(cx);
    let result = f(cx);
    match &result {
        Err(e) if !crate::undo::fatal(e) && cx.e.field_names.hits.get() > hits => {}
        _ => return result,
    }
    snapshot.restore(cx);
    let names = &cx.e.field_names;
    names.released.set(names.released.get() + 1);
    let again = f(cx);
    let names = &cx.e.field_names;
    names.released.set(names.released.get() - 1);
    again
}

/// The record types a literal with these fields may be, when nothing says
/// which: those visible by their short name whose fields are exactly the
/// literal's (interfaces left out). Their keys, in declaration order.
fn with_field_names(cx: &Ctx, fields: &[(ast::Name, Expr)]) -> Vec<(DataId, String)> {
    let g = cx.g();
    let written: std::collections::BTreeSet<&str> = fields.iter().map(|(n, _)| &*n.text).collect();
    if written.len() != fields.len() {
        return Vec::new();
    }
    (0..g.datas.len())
        .map(DataId)
        .filter(|&d| {
            let data = g.data(d);
            // A record still being declared has no constructor yet.
            let Some(ctor) = data.ctors.first() else {
                return false;
            };
            data.record
                && data.indices.is_empty()
                && !cx.e.interfaces.contains_key(&d)
                && ctor.fields.len() == written.len()
                && ctor.fields.iter().all(|(f, _)| written.contains(&**f))
        })
        .filter_map(|d| {
            let key = cx.e.data_key(d);
            let visible = matches!(
                cx.e.resolve(crate::scope::short(&key)),
                crate::scope::Resolved::Found { global: crate::Global::Data(found), rest, .. }
                    if found == d && rest.is_empty()
            );
            visible.then(|| (d, crate::scope::display(&key).to_string()))
        })
        .collect()
}

/// A record literal with no type known: queued (K1, postponement.md §5.4)
/// at a fresh unknown type, which the rest of the declaration may fix;
/// where nothing does, the field-name rule ([`Literal::apply_default`])
/// picks the one record type in scope with exactly its fields, with its
/// parameters to be inferred.
pub(crate) fn infer_literal(cx: &mut Ctx, fields: &[(ast::Name, Expr)]) -> Result<(Term, Value)> {
    let meta = cx.fresh_meta();
    let ty = cx.eval(&meta)?;
    let term = queue_literal(cx, fields, &ty)?;
    Ok((term, ty))
}

/// K1: a record literal whose type `expected` has an unknown at its head.
/// It waits before checking any field, so it keeps nothing elaborated
/// (invariant 6 holds trivially). Resumed, it is [`check_record`] at the
/// type now known; its default is SW-805's field-name rule, applied at the
/// end of the declaration only if nothing else has said the type (D2013).
/// The rule still looks only at the literal's field names and the names in
/// scope at the literal (D1991, assumption R1): only when it runs changes.
struct Literal {
    fields: Vec<(ast::Name, Expr)>,
    expected: Value,
}

impl crate::queue::Check for Literal {
    fn resume(&self, cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        let term = check_record(cx, None, &self.fields, &self.expected)?;
        Ok(crate::queue::Resumed::Done(term))
    }

    fn default_priority(&self) -> Option<crate::queue::Priority> {
        Some(crate::queue::Priority::FieldNames)
    }

    fn apply_default(&self, cx: &mut Ctx) -> Result<bool> {
        debug_assert!(
            cx.e.queue.settling(),
            "the field-name rule chose a type before the end (invariant 8)"
        );
        let [(d, _)] = with_field_names(cx, &self.fields)[..] else {
            return Ok(false);
        };
        let params = (0..cx.g().data(d).params.len())
            .map(|_| {
                let meta = cx.fresh_meta();
                cx.eval(&meta)
            })
            .collect::<Result<Vec<_>>>()?;
        cx.unify(&Value::Data(d, params), &self.expected)
    }
}

/// Queues a record literal at `expected`, whose head is an unknown: the
/// placeholder standing for it. If it is still waiting at the end, with no
/// record type its field names pick, it is reported with the error the
/// field-name rule gives.
fn queue_literal(cx: &mut Ctx, fields: &[(ast::Name, Expr)], expected: &Value) -> Result<Term> {
    let candidates = with_field_names(cx, fields);
    let mut error = cx
        .error(
            "E-CANNOT-INFER",
            "can't tell which record type this literal is",
            "nothing here says what type it should have",
        )
        .with_note("add a type annotation, as in `({ x = 0, y = 0 }: Point)`");
    if candidates.is_empty() {
        error = error.with_note("no record type in scope has exactly these fields");
    } else if candidates.len() > 1 {
        let names: Vec<String> = candidates.iter().map(|(_, k)| format!("`{k}`")).collect();
        error = error.with_note(format!(
            "more than one record type has exactly these fields: {}",
            names.join(", ")
        ));
    }
    let literal = Literal {
        fields: fields.to_vec(),
        expected: expected.clone(),
    };
    crate::queue::queue(
        cx,
        Rc::new(literal),
        expected.clone(),
        expected.clone(),
        error,
    )
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
            if let Value::Neutral(stitchwort_core::value::Head::Meta(_), _) =
                force(cx.g(), expected.clone())?
            {
                return queue_literal(cx, fields, expected);
            }
            let (d, params) = record_type(cx, expected, "this record literal")?;
            literal(cx, d, &params, fields)
        }
        Some(base) => {
            if variant(cx, expected)? {
                let base = check(cx, base, expected)?;
                return crate::shared::variant_update(cx, base, expected, fields);
            }
            if let Some(term) = changing_update(cx, base, fields, expected)? {
                return Ok(term);
            }
            let base = check(cx, base, expected)?;
            // The base may have told what `expected` is.
            if variant(cx, expected)? {
                return crate::shared::variant_update(cx, base, expected, fields);
            }
            update(cx, base, expected, None, fields)
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
    if variant(cx, &ty)? {
        return Ok((crate::shared::variant_update(cx, base, &ty, fields)?, ty));
    }
    let Ok((d, params)) = record_type(cx, &ty, "this update") else {
        return Ok((update(cx, base, &ty, None, fields)?, ty));
    };
    check_field_names(cx.g(), d, fields.iter().map(|(n, _)| n))?;
    let uses = param_uses(cx.g(), d, fields);
    if !uses.iter().any(|u| matches!(u, ParamUse::Free)) {
        return Ok((update(cx, base, &ty, None, fields)?, ty));
    }
    // The update as written first, so a literal in it is checked against the
    // parameters the base has (`{ w | at = 5 }` stays a `W Int`); only if that
    // fails may the parameters its new fields mention change.
    let kept = crate::undo::attempt(cx, |cx| update(cx, base.clone(), &ty, None, fields))?;
    if let Some(term) = kept {
        return Ok((term, ty));
    }
    let mut result = params;
    for (param, u) in result.iter_mut().zip(&uses) {
        if matches!(u, ParamUse::Free) {
            let meta = cx.fresh_meta();
            *param = cx.eval(&meta)?;
        }
    }
    let term = update(cx, base, &ty, Some(result.clone()), fields)?;
    Ok((term, Value::Data(d, result)))
}

/// What an update does with one of the record's type parameters.
enum ParamUse {
    /// Only replaced fields mention it: the update may change it.
    Free,
    /// A kept field has a type that mentions it (named), so it stays.
    KeptField(String),
    /// Another parameter's type mentions it (named), so it stays.
    Parameter(String),
    /// No replaced field mentions it, or no field does at all.
    Unused,
}

/// For each parameter of record `d`, what an update of `fields` does with it
/// (as in Haskell's type-changing update: a parameter can change only if
/// every field whose type mentions it is replaced).
fn param_uses(
    g: &stitchwort_core::Globals,
    d: DataId,
    fields: &[(ast::Name, Expr)],
) -> Vec<ParamUse> {
    let data = g.data(d);
    let np = data.params.len();
    let ctor = &data.ctors[0];
    let replaced = |f: &str| fields.iter().any(|(n, _)| n.text == f);
    (0..np)
        .map(|k| {
            // Parameter `k` as a variable in field `j`'s type, which is in
            // the context of the parameters and then the earlier fields.
            let in_field = |j: usize| ctor.fields[j].1.mentions(j + np - 1 - k);
            let kept =
                (0..ctor.fields.len()).find(|&j| !replaced(&ctor.fields[j].0) && in_field(j));
            if let Some(j) = kept {
                return ParamUse::KeptField(ctor.fields[j].0.to_string());
            }
            if let Some(p) = (k + 1..np).find(|&p| data.params[p].1.mentions(p - 1 - k)) {
                return ParamUse::Parameter(data.params[p].0.to_string());
            }
            if (0..ctor.fields.len()).any(|j| replaced(&ctor.fields[j].0) && in_field(j)) {
                ParamUse::Free
            } else {
                ParamUse::Unused
            }
        })
        .collect()
}

/// `{ base | f = e, … }` checked against `expected` when the base's type
/// differs from it in parameters (`{ t | start = f t.start }`: a `Timed Int`
/// made a `Timed Nat`); `None` if the base's type is `expected`, or can't be
/// told without it, which the caller elaborates as it always has. A
/// parameter that would have to change but can't is an error naming the kept
/// field that fixes it.
fn changing_update(
    cx: &mut Ctx,
    base: &Expr,
    fields: &[(ast::Name, Expr)],
    expected: &Value,
) -> Result<Option<Term>> {
    let g = cx.g();
    let Value::Data(d, wanted) = force(g, expected.clone())? else {
        return Ok(None);
    };
    let data = g.data(d);
    if !data.record
        || data.params.is_empty()
        || fields
            .iter()
            .any(|(n, _)| !data.ctors[0].fields.iter().any(|(f, _)| **f == *n.text))
    {
        return Ok(None);
    }
    let uses = param_uses(g, d, fields);
    if uses.iter().all(|u| matches!(u, ParamUse::Unused)) {
        return Ok(None);
    }
    // The base's type, learnt without committing to anything.
    let snapshot = crate::undo::Snapshot::take(cx);
    let found = infer(cx, base).and_then(|(term, ty)| insert(cx, term, ty));
    let learnt = match found {
        Ok((_, ty)) => match force(cx.g(), ty.clone())? {
            Value::Data(d2, have) if d2 == d => Some((ty, have)),
            _ => None,
        },
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(_) => None,
    };
    let same = match &learnt {
        Some((ty, _)) => cx.unify(ty, expected).unwrap_or(false),
        None => true,
    };
    snapshot.restore(cx);
    let Some((_, have)) = learnt.filter(|_| !same) else {
        return Ok(None);
    };
    for k in 0..data.params.len() {
        if matches!(uses[k], ParamUse::Free) || crate::undo::unify(cx, &have[k], &wanted[k])? {
            continue;
        }
        let name = &data.params[k].0;
        let (old, new) = (cx.show(&have[k]), cx.show(&wanted[k]));
        let why = match &uses[k] {
            ParamUse::KeptField(kept) => format!(
                "the kept field `{kept}` has a type that mentions `{name}`, so `{name}` stays `{old}`"
            ),
            ParamUse::Parameter(other) => format!(
                "the type of the parameter `{other}` depends on `{name}`, so `{name}` stays `{old}`"
            ),
            _ => format!("no replaced field mentions `{name}`, so it stays `{old}`"),
        };
        let mut error = cx.error(
            "E-RECORD-UPDATE",
            format!("this update can't change `{name}` from `{old}` to `{new}`"),
            why,
        );
        if let ParamUse::KeptField(kept) = &uses[k] {
            error = error.with_note(format!(
                "a type parameter can change only if every field whose type mentions it is \
                 replaced: give a new `{kept}` too"
            ));
        }
        return Err(error);
    }
    let (base, ty) = infer(cx, base)?;
    let (base, ty) = insert(cx, base, ty)?;
    Ok(Some(update(cx, base, &ty, Some(wanted), fields)?))
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
        .filter(|(i, (f, _))| {
            !supers.contains(i)
                && cx.e.field_default(d, 0, *i).is_none()
                && !fields.iter().any(|(n, _)| *n.text == **f)
        })
        .map(|(_, (f, _))| format!("`{f}`"))
        .collect();
    if !missing.is_empty() {
        let defaulted = cx.e.defaulted_fields(d, 0);
        let mut error = cx.error(
            "E-RECORD-FIELD",
            format!(
                "this `{}` is missing {}",
                g.data(d).name,
                missing.join(", ")
            ),
            if defaulted.is_empty() {
                "every field must be given"
            } else {
                "every field without a default value must be given"
            },
        );
        if let Some(note) = crate::defaults::defaulted_note(&defaulted) {
            error = error.with_note(note);
        }
        return Err(error);
    }
    if cx.g().data(d).defaults.is_some() {
        // Fields left out are their defaults (docs/proposals/named-arguments.md
        // §5.1); a record with defaults isn't an interface, so none is a
        // superclass.
        let mut none = |_: &mut Ctx, _: usize, _: &Value| -> Result<Term> {
            unreachable!("every field without a default is given")
        };
        return Ok(crate::defaults::construct(cx, d, 0, params, fields, &mut none)?.0);
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
/// too (DESIGN.md §9). The new record has `ty`'s parameters, or `result`
/// (those only replaced fields mention may differ from the base's).
fn update(
    cx: &mut Ctx,
    base: Term,
    ty: &Value,
    result: Option<Vec<Value>>,
    fields: &[(ast::Name, Expr)],
) -> Result<Term> {
    let g = cx.g();
    let (d, params) = record_type(cx, ty, "this update")?;
    let uses = param_uses(g, d, fields);
    let new_ty = match &result {
        Some(new) => Value::Data(d, new.clone()),
        None => ty.clone(),
    };
    let new_params = result.unwrap_or_else(|| params.clone());
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
    // once, rather than once per field taken from it. The binding is a
    // transparent `let` (SW-386, D1091): the variable stands for the base
    // itself, so a new value whose type mentions the base's fields
    // (`ys: Vec Nat (pick b r).n` for `xs: Vec Nat n`) fits the type the
    // kept fields give it (`Vec Nat %record.n`).
    let mark = cx.mark();
    // The `let`'s type, if the base is bound.
    let bound = match base.strip_loc() {
        Term::Var(_) => None,
        _ => {
            let ty_term = cx.quote(ty)?;
            cx.define(
                None,
                "%record".into(),
                ty.clone(),
                ty_term.clone(),
                base.clone(),
            )?;
            Some(ty_term)
        }
    };
    let base_term = match bound {
        Some(_) => Term::Var(0),
        None => base.clone(),
    };
    let result = update_fields(cx, d, &params, &new_params, &uses, &base_term, fields);
    cx.reset(mark);
    let body = result?;
    match bound {
        // Annotated, as the constructor alone may not be inferable.
        Some(ty_term) => Ok(Term::Ann(
            Rc::new(Term::let_("%record".into(), ty_term, base, body)),
            Rc::new(cx.quote(&new_ty)?),
        )),
        None => Ok(body),
    }
}

/// The fields of an update, in the context where `base` is a variable.
fn update_fields(
    cx: &mut Ctx,
    d: DataId,
    params: &[Value],
    new_params: &[Value],
    uses: &[ParamUse],
    base: &Term,
    fields: &[(ast::Name, Expr)],
) -> Result<Term> {
    let g = cx.g();
    let data = g.data(d);
    let ctor = &data.ctors[0];
    let np = params.len();
    // The replaced fields are checked against the new parameters, the others
    // taken from `base` at its own.
    let mut env = new_params.to_vec();
    let mut terms = Vec::new();
    for (i, (field, field_ty)) in ctor.fields.iter().enumerate() {
        let ty = eval(g, &env, field_ty)?;
        let term = match fields.iter().find(|(n, _)| *n.text == **field) {
            Some((_, expr)) => check(cx, expr, &ty).map_err(|e| {
                // A type parameter a kept field fixes, which this field's
                // type mentions: say so, if the field's value didn't fit.
                let pinned = (0..np).find_map(|k| match &uses[k] {
                    ParamUse::KeptField(kept) if field_ty.mentions(i + np - 1 - k) => {
                        Some((&data.params[k].0, kept))
                    }
                    _ => None,
                });
                match pinned {
                    Some((param, kept)) if e.code == "E-TYPE-MISMATCH" => e.with_note(format!(
                        "`{param}` can't change here: the kept field `{kept}` has a type that mentions it; \
                         replace `{kept}` too, or keep `{param}`"
                    )),
                    _ => e,
                }
            })?,
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
