//! The hidden `let` a chain of comparisons binds its middle operand with
//! (`lo <= f x <= hi`, SW-1339; the parser builds it,
//! [`stitchwort_syntax::ast::Expr::as_chain_let`]).
//!
//! As a `Bool`, or where it performs, the chain is that `let`, so the
//! operand runs once. As a proposition, a statement or the fact an `if`
//! learns, the operand is put back in place of the variable: a proposition
//! never runs, and so reads (and hashes) as `lo ≤ f x ∧ f x ≤ hi`, as if
//! written out. The decision procedure an `if` on the chain runs keeps the
//! `let`.

use stitchwort_core::Term;
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Expr, Name as AstName};

use crate::Ctx;
use crate::check::{Result, infer, insert};

/// The hidden variable, standing for `value` in the context.
pub(crate) struct Binding {
    name: stitchwort_core::Name,
    ty: Term,
    value: Term,
}

impl Binding {
    /// `body`, a term under the variable, with the value in its place.
    pub(crate) fn inline(&self, cx: &Ctx, body: &Term) -> Result<Term> {
        body.instantiate(&cx.g(), &self.value)
            .map_err(Diagnostic::from)
    }

    /// `body`, a term under the variable, run with the variable bound to the
    /// value once.
    pub(crate) fn wrap(&self, body: Term) -> Term {
        Term::let_(self.name.clone(), self.ty.clone(), self.value.clone(), body)
    }
}

/// Runs `f` with `name` bound to `value`.
pub(crate) fn around<T>(
    cx: &mut Ctx,
    name: &AstName,
    value: &Expr,
    f: impl FnOnce(&mut Ctx) -> Result<T>,
) -> Result<(T, Binding)> {
    let (term, ty) = infer(cx, value)?;
    let (term, ty) = insert(cx, term, ty)?;
    let ty_term = cx.quote_folded(&ty)?;
    let x: stitchwort_core::Name = name.text.as_str().into();
    let mark = cx.mark();
    let result = cx
        .define(
            Some(&name.text),
            x.clone(),
            ty,
            ty_term.clone(),
            term.clone(),
        )
        .and_then(|()| f(cx));
    cx.reset(mark);
    Ok((
        result?,
        Binding {
            name: x,
            ty: ty_term,
            value: term,
        },
    ))
}

/// A chain of comparisons where a type is wanted: the proposition with the
/// operand in place.
pub(crate) fn check_type(
    cx: &mut Ctx,
    name: &AstName,
    value: &Expr,
    body: &Expr,
) -> Result<(Term, stitchwort_core::Sort)> {
    let ((term, sort), binding) = around(cx, name, value, |cx| crate::check::check_type(cx, body))?;
    Ok((binding.inline(cx, &term)?, sort))
}

/// The first chain with a computed middle along the logical spine of
/// `expr` (through brackets and the operands of `&&`, `||` and `not`, not
/// under a binder), as `(name, value, rest)`: `rest` is `expr` with that
/// chain replaced by its body, which mentions the hidden variable. A
/// proposition such as `b != 0 && 1 <= f b <= 9` is decided with the
/// middle bound once around the decision ([`around`]), not put back in
/// place in the decision as in the proposition.
pub(crate) fn on_spine<'a>(cx: &Ctx, expr: &'a Expr) -> Option<(&'a AstName, &'a Expr, Expr)> {
    use crate::logic::{Logic, classify};
    if let Some((name, value, body)) = expr.as_chain_let() {
        return Some((name, value, body.clone()));
    }
    if let Expr::Bracketed(inner, span) = expr {
        let (name, value, rest) = on_spine(cx, inner)?;
        return Some((name, value, Expr::Bracketed(Box::new(rest), *span)));
    }
    match classify(cx, expr)? {
        Logic::And(a, b) | Logic::Or(a, b) => {
            let Expr::Binary(op, ..) = expr else {
                return None;
            };
            if let Some((name, value, rest)) = on_spine(cx, a) {
                return Some((
                    name,
                    value,
                    Expr::Binary(*op, Box::new(rest), Box::new(b.clone())),
                ));
            }
            let (name, value, rest) = on_spine(cx, b)?;
            Some((
                name,
                value,
                Expr::Binary(*op, Box::new(a.clone()), Box::new(rest)),
            ))
        }
        Logic::Not(a, _) => {
            let Expr::App(f, _) = expr else {
                return None;
            };
            let (name, value, rest) = on_spine(cx, a)?;
            Some((name, value, Expr::App(f.clone(), Box::new(rest))))
        }
    }
}
