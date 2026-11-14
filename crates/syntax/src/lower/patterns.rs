//! Patterns: dispatch on the kind, and the ones of a single token.

use crate::ast::Pattern;
use crate::lexer::Tok;
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::{Lower, Lowering, Unsupported};

impl<'f> Lower<'f> {
    /// The pattern an element of the tree is.
    pub(crate) fn pattern(&self, element: Element<'f>) -> Lowering<Pattern> {
        match element {
            Element::Leaf(leaf) => leaf_pattern(leaf),
            Element::Node(node) if node.kind() == NodeKind::PatternAbsurd => absurd(node),
            Element::Node(node) => Err(Unsupported::Kind(node.kind())),
        }
    }
}

/// A pattern of one token: a variable, `_`, a number, a character, or a
/// constructor without arguments (`Quot.mk` among them: it isn't one, but
/// is read as one so that the elaborator can say why).
fn leaf_pattern(leaf: Leaf<'_>) -> Lowering<Pattern> {
    let span = leaf.span();
    Ok(match leaf.tok() {
        Tok::Lower(text) if text != "Quot.mk" => Pattern::Var(name(leaf).expect("a name")),
        Tok::Lower(_) | Tok::Upper(_) => Pattern::Ctor(name(leaf).expect("a name"), Vec::new(), span),
        Tok::Underscore => Pattern::Wildcard(span),
        Tok::Num(n) => Pattern::Num(n.clone(), span),
        Tok::Char(c) => Pattern::Char(*c, span),
        _ => return Err(Unsupported::Token),
    })
}

/// `()`: the pattern of an empty type.
fn absurd(node: Node<'_>) -> Lowering<Pattern> {
    let span = required(node.span(), NodeKind::PatternAbsurd, "its tokens")?;
    Ok(Pattern::Absurd(span))
}
