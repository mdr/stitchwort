//! Reading a node's parts: its child nodes, its own tokens, and the part
//! that follows a given token (a slot, found by the token that introduces
//! it, never by position).

use crate::Span;
use crate::lexer::Tok;
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::{Lowering, Unsupported};

impl<'f> Node<'f> {
    /// Its child nodes, without its own tokens.
    pub fn child_nodes(&self) -> impl Iterator<Item = Node<'f>> + 'f {
        self.children().filter_map(|child| match child {
            Element::Node(node) => Some(node),
            Element::Leaf(_) => None,
        })
    }

    /// Its own tokens: those not inside a child node.
    pub fn own_leaves(&self) -> impl Iterator<Item = Leaf<'f>> + 'f {
        self.children().filter_map(|child| match child {
            Element::Leaf(leaf) => Some(leaf),
            Element::Node(_) => None,
        })
    }

    /// Its first own token, if it is `tok`.
    pub fn first_leaf_is(&self, tok: &Tok) -> Option<Leaf<'f>> {
        match self.children().next()? {
            Element::Leaf(leaf) if leaf.tok() == tok => Some(leaf),
            _ => None,
        }
    }

    /// Its own token `tok`, the first of them.
    pub fn leaf(&self, tok: &Tok) -> Option<Leaf<'f>> {
        self.own_leaves().find(|leaf| leaf.tok() == tok)
    }

    /// The part right after its own token `tok`: the slot that token
    /// introduces (`:=` a body, `then` a branch). `None` if the token isn't
    /// there or nothing follows it.
    pub fn after(&self, tok: &Tok) -> Option<Element<'f>> {
        let mut children = self.children();
        children.find(|child| matches!(child, Element::Leaf(leaf) if leaf.tok() == tok))?;
        children.next()
    }

    /// Its first child node of kind `kind`.
    pub fn child(&self, kind: NodeKind) -> Option<Node<'f>> {
        self.child_nodes().find(|node| node.kind() == kind)
    }

    /// From its first token's start to its last token's end; `None` for a
    /// declaration that didn't lex, which has no tokens.
    pub fn span(&self) -> Option<Span> {
        let range = self.token_range();
        let tokens = self.file().tokens();
        let first = tokens.get(range.start)?;
        let last = tokens.get(range.end.checked_sub(1)?)?;
        Some(first.span.to(last.span))
    }
}

impl<'f> Leaf<'f> {
    pub fn tok(&self) -> &'f Tok {
        &self.token().tok
    }

    pub fn span(&self) -> Span {
        self.token().span
    }
}

/// A part the parser always gives a node of kind `kind`: `Missing` if it
/// isn't there.
pub(super) fn required<T>(part: Option<T>, kind: NodeKind, what: &'static str) -> Lowering<T> {
    part.ok_or(Unsupported::Missing(kind, what))
}
