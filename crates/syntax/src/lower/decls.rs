//! Declarations: what each root kind lowers to.

use crate::ast::{Decl, FailedName, Import, ImportItem, Name, NamespaceDecl};
use crate::lexer::Tok;
use crate::parser::{failed_names_in, failed_names_of};
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::{Lower, Lowering, Unsupported};

/// The name a token holds, if it is a name.
pub(super) fn name(leaf: Leaf<'_>) -> Option<Name> {
    match leaf.tok() {
        Tok::Lower(text) | Tok::Upper(text) => Some(Name {
            text: text.clone(),
            span: leaf.span(),
        }),
        _ => None,
    }
}

/// The token an element is, if it is one.
fn as_leaf(element: Option<Element<'_>>) -> Option<Leaf<'_>> {
    match element? {
        Element::Leaf(leaf) => Some(leaf),
        Element::Node(_) => None,
    }
}

impl<'f> Lower<'f> {
    /// `namespace Day05`
    pub(super) fn namespace(&self, root: Node<'f>) -> Lowering<NamespaceDecl> {
        let kind = NodeKind::Namespace;
        let keyword = required(root.first_leaf_is(&Tok::KwNamespace), kind, "`namespace`")?;
        let path = as_leaf(root.after(&Tok::KwNamespace)).and_then(name);
        let path = required(path, kind, "its name")?;
        Ok(NamespaceDecl {
            span: keyword.span().to(path.span),
            path,
        })
    }

    /// `import List (map, filter as f)`, `import List (..)`
    pub(super) fn import(&self, root: Node<'f>) -> Lowering<Import> {
        let kind = NodeKind::Import;
        let keyword = required(root.first_leaf_is(&Tok::KwImport), kind, "`import`")?;
        let path = as_leaf(root.after(&Tok::KwImport)).and_then(name);
        let path = required(path, kind, "its namespace")?;
        let close = required(root.leaf(&Tok::RParen), kind, "`)`")?;
        let everything = root.leaf(&Tok::DotDot).map(|dots| dots.span());
        let items = root
            .child_nodes()
            .filter(|node| node.kind() == NodeKind::ImportItem)
            .map(|item| {
                let mut leaves = item.own_leaves();
                let name = leaves.next().and_then(name);
                let name = required(name, NodeKind::ImportItem, "its name")?;
                let alias = match leaves.next() {
                    Some(_as) => {
                        let alias = leaves.next().and_then(super::decls::name);
                        Some(required(alias, NodeKind::ImportItem, "its alias")?)
                    }
                    None => None,
                };
                Ok(ImportItem { name, alias })
            })
            .collect::<Lowering<Vec<_>>>()?;
        Ok(Import {
            path,
            items,
            everything,
            span: keyword.span().to(close.span()),
        })
    }

    /// `test "name" := e`
    pub(super) fn test(&self, root: Node<'f>) -> Lowering<Decl> {
        let kind = NodeKind::Test;
        let keyword = required(root.first_leaf_is(&Tok::KwTest), kind, "`test`")?;
        let name = match as_leaf(root.after(&Tok::KwTest)).map(|leaf| leaf.tok()) {
            Some(Tok::Str(text)) => text.clone(),
            _ => return Err(Unsupported::Missing(kind, "its name")),
        };
        let body = required(root.child(NodeKind::Body), kind, "its body")?;
        let expr = required(body.after(&Tok::ColonEq), NodeKind::Body, "its expression")?;
        let expr = self.expr(expr)?;
        Ok(Decl::Test {
            span: keyword.span().to(expr.span()),
            name,
            expr,
        })
    }

    /// A declaration that didn't parse: the names it would have declared,
    /// read off its tokens as the parser does, marked with its first error.
    pub(super) fn failed(&self, root: Node<'f>) -> Lowering<Vec<FailedName>> {
        if let Some(raw) = root.raw_text_range() {
            let error_at = self.first_error_in(raw.start, raw.end);
            return Ok(failed_names_in(self.file, self.text, &raw, error_at));
        }
        let Some(span) = root.span() else {
            return Ok(Vec::new());
        };
        if self.split_failed() {
            return Ok(Vec::new());
        }
        // Its first token after its attributes. Attributes that didn't
        // finish are no node, and fail the declaration before its keyword.
        let first = root.children().find_map(|child| match child {
            Element::Node(node) if node.kind() == NodeKind::Attributes => None,
            Element::Node(_) => Some(None),
            Element::Leaf(leaf) => Some(Some(leaf.tok())),
        });
        if matches!(
            first,
            Some(Some(
                Tok::KwDef | Tok::KwTheorem | Tok::KwExport | Tok::KwOpaque
            ))
        ) {
            return Err(Unsupported::FailedDefinition);
        }
        let tokens = &self.tree.tokens()[root.token_range()];
        let error_at = self.first_error_in(span.start as usize, span.end as usize);
        Ok(failed_names_of(tokens, error_at))
    }

    /// The position of the first error the parser reported in
    /// `text[start..=end]`.
    fn first_error_in(&self, start: usize, end: usize) -> Option<crate::Span> {
        self.errors
            .iter()
            .filter_map(|error| error.primary_span())
            .find(|span| (start..=end).contains(&(span.start as usize)))
    }

    /// Whether the file's first token isn't at the start of a line, which
    /// fails the whole file as one error.
    pub(super) fn split_failed(&self) -> bool {
        self.tree.tokens().first().is_some_and(|t| t.column != 0)
    }
}
