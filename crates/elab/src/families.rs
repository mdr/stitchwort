//! Indexed families in the elaborator (docs/proposals/indexed-families.md
//! §7): constructors with result types and implicit fields, written
//! (`[n: Nat]`) or automatic (an unknown lowercase name in a constructor of
//! an indexed family, D144).

use stitchwort_core::check as kernel;
use stitchwort_core::value::force;
use stitchwort_core::{DataId, Name, Term, Value, pretty};
use stitchwort_syntax::ast::{self, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, check_type};
use crate::{Elaborator, Result, autobind, error, name};

impl Elaborator {
    /// Elaborates constructor `ctor` of data type `d`, which has indices, a
    /// written result type or implicit fields. Automatic implicit fields go
    /// at the front, ordered by their dependencies on each other (the order
    /// of first use when that works, else the first other order that does);
    /// one whose type would mention a written field is `E-IMPLICIT-FIELD`.
    pub(crate) fn family_ctor(
        &self,
        d: DataId,
        ctor: &ast::CtorDecl,
        span: Span,
    ) -> Result<kernel::CtorDecl> {
        for (k, binder) in ctor.fields.iter().enumerate() {
            if let Some(earlier) = ctor.fields[..k]
                .iter()
                .flat_map(|b| &b.names)
                .find(|e| binder.names.iter().any(|n| n.text == e.text))
            {
                return Err(error(
                    "E-DUPLICATE",
                    binder.names[0].span,
                    format!("there's already a field `{}`", earlier.text),
                )
                .with_label(earlier.span, "first declared here"));
            }
        }
        let autos = if self.globals.data(d).indices.is_empty() {
            Vec::new()
        } else {
            self.ctor_autos(d, ctor)?
        };
        let mut first_error = None;
        for order in orders(autos.len()) {
            let ordered: Vec<&ast::Name> = order.iter().map(|&i| &autos[i]).collect();
            match self.ctor_attempt(d, ctor, span, &ordered, true) {
                Ok(decl) => return Ok(decl),
                Err(e) if e.code == "E-RESOURCE" => return Err(e),
                Err(e) => {
                    first_error.get_or_insert(e);
                }
            }
        }
        let first_error = first_error.expect("at least one order");
        if !autos.is_empty()
            && let Some(e) = self.implicit_field_error(d, ctor, span, &autos)?
        {
            return Err(e);
        }
        Err(first_error)
    }

    /// The names a constructor of an indexed family binds automatically:
    /// as for a signature, but over its fields and result type, with the
    /// type's parameters in scope.
    fn ctor_autos(&self, d: DataId, ctor: &ast::CtorDecl) -> Result<Vec<ast::Name>> {
        let params: Vec<String> = (self.globals.data(d).params.iter())
            .map(|(x, _)| x.to_string())
            .collect();
        let span = ctor.name.span;
        let mut ty = ctor.result.clone().unwrap_or(Expr::Hole(span));
        for (binder, implicit) in ctor.fields.iter().zip(implicits(ctor)).rev() {
            ty = Expr::Pi {
                names: binder.names.clone(),
                implicit,
                auto: false,
                dom: Box::new(binder.ty.clone()),
                cod: Box::new(ty),
                span,
            };
        }
        Ok(autobind::auto_bound_in(self, &ty, params)?.names)
    }

    /// One attempt at constructor `ctor`, with the automatic fields `autos`
    /// at the front (`front`) or after the written ones.
    fn ctor_attempt(
        &self,
        d: DataId,
        ctor: &ast::CtorDecl,
        span: Span,
        autos: &[&ast::Name],
        front: bool,
    ) -> Result<kernel::CtorDecl> {
        self.clear_metas();
        let g = &self.globals;
        let data = g.data(d);
        let np = data.params.len();
        let mut cx = Ctx::new(self, span);
        for (x, ty) in &data.params {
            let value = cx.eval(ty)?;
            cx.bind(x, value);
        }
        // Each field: its name, unfinished type, span and implicitness.
        let mut fields: Vec<(Name, Term, Span, bool)> = Vec::new();
        let bind_autos = |cx: &mut Ctx, fields: &mut Vec<(Name, Term, Span, bool)>| {
            for n in autos {
                cx.span = n.span;
                let dom = cx.fresh_meta();
                let value = cx.eval(&dom)?;
                fields.push((name(n), dom, n.span, true));
                cx.bind(&n.text, value);
            }
            cx.span = span;
            Ok::<_, Diagnostic>(())
        };
        if front {
            bind_autos(&mut cx, &mut fields)?;
        }
        for (binder, implicit) in ctor.fields.iter().zip(implicits(ctor)) {
            let (ty, _) = check_type(&mut cx, &binder.ty)?;
            for (k, n) in binder.names.iter().enumerate() {
                let ty = ty.shift(g, k, 0)?;
                let value = cx.eval(&ty)?;
                fields.push((name(n), ty, binder.ty.span(), implicit));
                cx.bind(&n.text, value);
            }
        }
        if !front {
            bind_autos(&mut cx, &mut fields)?;
        }
        let result = self.ctor_result(&mut cx, d, ctor)?;
        let mut out = Vec::new();
        for (i, (x, ty, span, _)) in fields.iter().enumerate() {
            out.push((x.clone(), self.finish(ty, np + i)?, *span));
        }
        let result = (result.iter())
            .map(|r| self.finish(r, np + fields.len()))
            .collect::<Result<Vec<_>>>()?;
        Ok(kernel::CtorDecl {
            name: name(&ctor.name),
            fields: out,
            result,
            implicit: fields.iter().map(|f| f.3).collect(),
        })
    }

    /// The result indices of constructor `ctor` of `d`, in `cx` (the
    /// parameters and the fields), from its result type: `d` applied to
    /// exactly its own parameters, then indices.
    fn ctor_result(&self, cx: &mut Ctx, d: DataId, ctor: &ast::CtorDecl) -> Result<Vec<Term>> {
        let g = &self.globals;
        let data = g.data(d);
        let (np, ni) = (data.params.len(), data.indices.len());
        let own = || {
            let params: Vec<&str> = data.params.iter().map(|(x, _)| &**x).collect();
            std::iter::once(&*data.name)
                .chain(params)
                .collect::<Vec<_>>()
                .join(" ")
        };
        let Some(written) = &ctor.result else {
            if ni == 0 {
                return Ok(Vec::new());
            }
            return Err(error(
                "E-TYPE-MISMATCH",
                ctor.name.span,
                format!(
                    "`{}` needs a result type, since `{}` has indices",
                    ctor.name.text, data.name
                ),
            )
            .with_note(format!(
                "write it after the fields: `| {} …: {} …`",
                ctor.name.text,
                own()
            )));
        };
        cx.span = written.span();
        let (ty, _) = check_type(cx, written)?;
        let value = force(g, cx.eval(&ty)?)?;
        let wrong = |cx: &Ctx, value: &Value| {
            error(
                "E-TYPE-MISMATCH",
                written.span(),
                format!(
                    "`{}`'s result must be `{}` applied to its indices, but this is `{}`",
                    ctor.name.text,
                    own(),
                    cx.show(value)
                ),
            )
            .with_note(
                "a constructor's result has the type's own parameters, as they're declared; \
                 only the indices may differ",
            )
        };
        let Value::Data(d2, args) = &value else {
            return Err(wrong(cx, &value));
        };
        if *d2 != d || args.len() != np + ni {
            return Err(wrong(cx, &value));
        }
        for (i, arg) in args[..np].iter().enumerate() {
            if !cx.unify(arg, &Value::var(i))? {
                return Err(wrong(cx, &value));
            }
        }
        args[np..].iter().map(|a| cx.quote(a)).collect()
    }

    /// For a constructor that failed with its automatic fields at the front:
    /// `E-IMPLICIT-FIELD` if, put after the written fields instead, it
    /// checks and one of them has a type mentioning a written field.
    fn implicit_field_error(
        &self,
        d: DataId,
        ctor: &ast::CtorDecl,
        span: Span,
        autos: &[ast::Name],
    ) -> Result<Option<Diagnostic>> {
        let ordered: Vec<&ast::Name> = autos.iter().collect();
        let Ok(decl) = self.ctor_attempt(d, ctor, span, &ordered, false) else {
            return Ok(None);
        };
        let g = &self.globals;
        let written = decl.fields.len() - autos.len();
        for (j, auto) in autos.iter().enumerate() {
            let ty = &decl.fields[written + j].1;
            let Some(k) = (0..written).find(|&k| ty.mentions(written + j - 1 - k)) else {
                continue;
            };
            let mut names: Vec<Name> = g.data(d).params.iter().map(|(x, _)| x.clone()).collect();
            names.extend(decl.fields[..written + j].iter().map(|(x, _, _)| x.clone()));
            let shown = pretty::term(g, &names, ty);
            let field = &decl.fields[k].0;
            return Ok(Some(
                error(
                    "E-IMPLICIT-FIELD",
                    auto.span,
                    format!("`{}` needs to be written as a field", auto.text),
                )
                .with_note(format!(
                    "`{}` isn't declared, so it's an automatic implicit field, of type `{shown}`, \
                     which mentions the field `{field}`. Automatic fields go before the written \
                     ones",
                    auto.text
                ))
                .with_note(format!("write `[{}: {shown}]` after `{field}`", auto.text)),
            ));
        }
        Ok(None)
    }
}

/// Whether each binder of `ctor` is implicit.
fn implicits(ctor: &ast::CtorDecl) -> Vec<bool> {
    (0..ctor.fields.len())
        .map(|i| ctor.implicit.get(i).copied().unwrap_or(false))
        .collect()
}

/// The orders to try `n` automatic fields in: the order of first use, then
/// (for up to four) every other, in lexicographic order.
fn orders(n: usize) -> Vec<Vec<usize>> {
    let first: Vec<usize> = (0..n).collect();
    if n > 4 {
        return vec![first];
    }
    let mut out = Vec::new();
    let mut current = first;
    loop {
        out.push(current.clone());
        // The next permutation, lexicographically.
        let Some(i) = (1..current.len())
            .rev()
            .find(|&i| current[i - 1] < current[i])
        else {
            break;
        };
        let j = (i..current.len())
            .rev()
            .find(|&j| current[j] > current[i - 1])
            .expect("a larger element");
        current.swap(i - 1, j);
        current[i..].reverse();
    }
    out
}
