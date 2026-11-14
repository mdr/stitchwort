//! A definition's header, `def f (x: A) [b: B] (): R`, as the compiler's
//! tree has it: a signature whose type is a `Pi` per parameter in front of
//! the result type, and the patterns every equation starts with
//! (docs/proposals/declaration-syntax.md §2.3). The parser builds these too,
//! until the lowering replaces it (docs/proposals/syntax-tree-lowering.md).

use crate::Span;
use crate::ast::{Expr, MatchKind, Name, Pattern};

/// A parameter written in a header, before the colon.
pub(crate) enum Param {
    /// `(x y : A)`; with `implicit`, `[x y : A]`; with `auto` too,
    /// `[auto h : P]`.
    Named {
        names: Vec<Name>,
        ty: Expr,
        implicit: bool,
        auto: bool,
        /// `(x: A := v)`: a default value, on an explicit parameter.
        default: Option<Box<Expr>>,
        span: Span,
    },
    /// `()`: a parameter of type `()` that isn't used. It's matched by `_`
    /// (§2.3), not by the pattern `()`, which would make an arm absurd.
    Unit(Span),
}

/// The signature's type, the header's parameters as arrows in front of the
/// result type, in the order written; and the patterns each equation starts
/// with, a variable for each explicit parameter and `_` for `()` (§2.3).
/// The elaborator auto-binds type variables once over this complete type,
/// as it does for an old-style signature: no parameter is elaborated on its
/// own.
pub(crate) fn lower_header(params: Vec<Param>, result: Expr) -> (Expr, Vec<Pattern>) {
    let mut patterns = Vec::new();
    debug_assert!(header_defaults(&params).is_empty(), "defaults taken first");
    for param in &params {
        match param {
            Param::Named {
                names,
                implicit: false,
                ..
            } => patterns.extend(names.iter().cloned().map(Pattern::Var)),
            Param::Named { .. } => {}
            Param::Unit(span) => patterns.push(Pattern::Wildcard(*span)),
        }
    }
    let ty = params
        .into_iter()
        .rev()
        .fold(result, |cod, param| match param {
            Param::Unit(span) => Expr::Arrow(Box::new(Expr::Unit(span)), Box::new(cod)),
            Param::Named {
                names,
                ty,
                implicit,
                auto,
                span,
                default: _,
            } => {
                let span = span.to(cod.span());
                Expr::Pi {
                    names,
                    implicit,
                    auto,
                    dom: Box::new(ty),
                    cod: Box::new(cod),
                    span,
                }
            }
        });
    (ty, patterns)
}

/// The header's default values, as `Decl::Signature::defaults` holds them,
/// taken out of `params`: empty if none has one.
pub(crate) fn take_defaults(params: &mut [Param]) -> Vec<Option<Expr>> {
    if header_defaults(params).is_empty() {
        return Vec::new();
    }
    let mut out = Vec::new();
    for param in params {
        match param {
            Param::Named { names, default, .. } => {
                let default = default.take().map(|d| *d);
                out.extend(names.iter().map(|_| default.clone()));
            }
            Param::Unit(_) => out.push(None),
        }
    }
    out
}

/// The header's parameters that have default values.
fn header_defaults(params: &[Param]) -> Vec<&Expr> {
    params
        .iter()
        .filter_map(|p| match p {
            Param::Named { default, .. } => default.as_deref(),
            Param::Unit(_) => None,
        })
        .collect()
}


/// Whether `body` is the `match` of a clause lambda written as it is
/// (`match | …`, `match some | …`, `matches | …`).
pub(crate) fn clause_match(body: &Expr) -> bool {
    matches!(
        body,
        Expr::Match {
            kind: MatchKind::Clause | MatchKind::ClauseSome | MatchKind::ClauseMatches,
            ..
        }
    )
}

