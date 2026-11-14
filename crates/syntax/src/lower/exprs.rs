//! Expressions: dispatch on the kind, and the ones of a single token.

use crate::ast::Expr;
use crate::lexer::Tok;
use crate::tree::{Element, Leaf};

use super::decls::name;
use super::{Lower, Lowering, Unsupported};

impl<'f> Lower<'f> {
    /// The expression an element of the tree is.
    pub(crate) fn expr(&self, element: Element<'f>) -> Lowering<Expr> {
        match element {
            Element::Leaf(leaf) => leaf_expr(leaf),
            Element::Node(node) => Err(Unsupported::Kind(node.kind())),
        }
    }
}

/// An expression of one token: a name, a literal, `_`, `?`, `Type`, `Prop`,
/// and `omega`, `ring` and `cases` without their parts.
fn leaf_expr(leaf: Leaf<'_>) -> Lowering<Expr> {
    let span = leaf.span();
    Ok(match leaf.tok() {
        Tok::Lower(_) | Tok::Upper(_) => Expr::Var(name(leaf).expect("a name")),
        Tok::Num(n) => Expr::Num(n.clone(), span),
        Tok::Float(text) => Expr::Float(text.clone(), span),
        Tok::Str(text) => Expr::Str(text.clone(), span),
        Tok::Char(c) => Expr::Char(*c, span),
        Tok::Underscore => Expr::Hole(span),
        Tok::Question => Expr::Goal(span),
        Tok::TypeU => Expr::Type(0, span),
        Tok::Prop => Expr::Prop(span),
        Tok::KwOmega => Expr::Omega {
            facts: Vec::new(),
            span,
        },
        Tok::KwRing => Expr::Ring {
            facts: Vec::new(),
            span,
        },
        Tok::KwCases => Expr::Cases { body: None, span },
        _ => return Err(Unsupported::Token),
    })
}
