//! D3565: adjacent parameters of the same kind and the same type are
//! merged, `(a: Nat) (b: Nat)` into `(a b: Nat)`, in definition and theorem
//! headers, `∀` binders and lambdas (docs/proposals/formatter-style.md §4).
//!
//! This is pass P4 of docs/proposals/fmt-passes.md §2: it returns the merges
//! as edits, which [`crate::passes::run`] applies and re-parses. The
//! compiler's tree keeps a group as one binder with several names; a type
//! that mentions a name of the group is never merged, since splitting
//! `(x y: P x)` would change which `x` the second type means.

use std::ops::Range;

use stitchwort_syntax::Tok;
use stitchwort_syntax::tree::{Element, Node, NodeKind, SyntaxFile};

use crate::passes::Edit;
use crate::printer::token_text_range;

/// A parameter in brackets, read from its node: `(a b: T)` or `[a: T]`.
struct Param {
    /// Its bracket: `(` or `[`.
    open: Tok,
    names: Vec<String>,
    /// The type's tokens' texts, to compare types by.
    ty: Vec<String>,
    /// The type's source text, from its first token to its last.
    ty_text: String,
    /// Its bytes in the source.
    range: Range<usize>,
}

/// Reads a parameter that may be merged or split: names, a colon and a
/// type, no default, no `auto`, no attribute, and no comment inside.
fn param(tree: &SyntaxFile, text: &str, node: Node<'_>) -> Option<Param> {
    let tokens = tree.tokens();
    let range = node.token_range();
    let trivia = tree.trivia();
    // A comment on any of its tokens, or before its first, stays put: no
    // merge across or inside one.
    if trivia[range.clone()].iter().any(|t| t.trailing.is_some())
        || trivia[range.start + 1..range.end]
            .iter()
            .any(|t| !t.leading.is_empty())
    {
        return None;
    }
    let children: Vec<Element> = node.children().collect();
    let leaf_tok = |el: &Element| match el {
        Element::Leaf(leaf) => Some(&tokens[leaf.index()].tok),
        Element::Node(_) => None,
    };
    let open = leaf_tok(children.first()?)?.clone();
    let close = leaf_tok(children.last()?)?;
    if !matches!(
        (&open, close),
        (Tok::LParen, Tok::RParen) | (Tok::LBracket, Tok::RBracket)
    ) {
        return None;
    }
    let colon = children
        .iter()
        .position(|el| leaf_tok(el) == Some(&Tok::Colon))?;
    let mut names = Vec::new();
    for el in &children[1..colon] {
        match leaf_tok(el) {
            Some(Tok::Lower(name)) if name != "auto" => names.push(name.clone()),
            _ => return None,
        }
    }
    let ty_els = &children[colon + 1..children.len() - 1];
    if names.is_empty()
        || ty_els.is_empty()
        || ty_els
            .iter()
            .any(|el| matches!(el, Element::Node(n) if n.kind() == NodeKind::Default))
    {
        return None;
    }
    let first = match ty_els[0] {
        Element::Leaf(leaf) => leaf.index(),
        Element::Node(n) => n.token_range().start,
    };
    let last = range.end - 2;
    let ty = (first..=last)
        .map(|i| text[token_text_range(&tokens[i])].to_string())
        .collect();
    let ty_text = text[token_text_range(&tokens[first]).start..token_text_range(&tokens[last]).end]
        .to_string();
    let start = token_text_range(&tokens[range.start]).start;
    let end = token_text_range(&tokens[range.end - 1]).end;
    Some(Param {
        open,
        names,
        ty,
        ty_text,
        range: start..end,
    })
}

fn bracket(open: &Tok) -> (&'static str, &'static str) {
    match open {
        Tok::LBracket => ("[", "]"),
        _ => ("(", ")"),
    }
}

/// Visits every node under `node`, children before their parent's next
/// sibling.
fn walk<'f>(node: Node<'f>, f: &mut impl FnMut(Node<'f>)) {
    f(node);
    for child in node.children() {
        if let Element::Node(child) = child {
            walk(child, f);
        }
    }
}

/// P4: the parameter groups in `text`, as edits, one per group made; empty
/// if there are none.
pub fn merge_parameters(tree: &SyntaxFile, text: &str) -> Vec<Edit> {
    let mut edits = Vec::new();
    for decl in tree.decls() {
        walk(decl, &mut |node| {
            let kind = match node.kind() {
                NodeKind::Def | NodeKind::Theorem => NodeKind::Param,
                NodeKind::Forall | NodeKind::Lambda => NodeKind::LambdaParam,
                _ => return,
            };
            // Runs of adjacent parameters that merge, as (first, params).
            let mut run: Vec<Param> = Vec::new();
            let mut flush = |run: &mut Vec<Param>| {
                if run.len() >= 2 {
                    let (open, close) = bracket(&run[0].open);
                    let names: Vec<&str> = run
                        .iter()
                        .flat_map(|p| p.names.iter().map(String::as_str))
                        .collect();
                    let merged = format!("{open}{}: {}{close}", names.join(" "), run[0].ty_text);
                    let range = run[0].range.start..run[run.len() - 1].range.end;
                    edits.push(Edit {
                        range,
                        text: merged,
                    });
                }
                run.clear();
            };
            let mut previous_end = None;
            for child in node.children() {
                let next = match child {
                    Element::Node(n) if n.kind() == kind => param(tree, text, n),
                    _ => None,
                };
                let Some(next) = next else {
                    flush(&mut run);
                    previous_end = None;
                    continue;
                };
                let joins = run.last().is_some_and(|last: &Param| {
                    let mentions = |p: &Param, names: &[String]| {
                        p.ty.iter().any(|t| names.iter().any(|n| n == t))
                    };
                    let mut names: Vec<String> = run.iter().flat_map(|p| p.names.clone()).collect();
                    names.extend(next.names.clone());
                    last.open == next.open
                        && last.ty == next.ty
                        && previous_end
                            .is_some_and(|end| text[end..next.range.start].trim().is_empty())
                        && !mentions(&next, &names)
                });
                if !joins {
                    flush(&mut run);
                }
                previous_end = Some(next.range.end);
                run.push(next);
            }
            flush(&mut run);
        });
    }
    edits
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::SourceMap;

    use super::*;

    /// The text after the pass, and how many groups it made.
    fn merged(text: &str) -> (String, usize) {
        let file = SourceMap::new().add("t.sw", text);
        let tidied = crate::passes::run(file, text, &[merge_parameters]);
        (tidied.text, tidied.edits[0])
    }

    #[test]
    fn adjacent_parameters_of_one_type_merge() {
        let text = "def f (a: Nat) (b: Nat) [t: Type] [u: Type] (x: t): Nat := a\n\
                    theorem g ∀ (xs: List Nat) (ys: List Nat): xs = ys := h\n\
                    def h: Nat := forall (x: Nat) (y: Nat) => (p: Nat) (q: Nat) => x\n";
        let (merged, groups) = merged(text);
        assert_eq!(groups, 5);
        assert_eq!(
            merged,
            "def f (a b: Nat) [t u: Type] (x: t): Nat := a\n\
             theorem g ∀ (xs ys: List Nat): xs = ys := h\n\
             def h: Nat := forall (x y: Nat) => (p q: Nat) => x\n"
        );
    }

    #[test]
    fn the_guards_keep_parameters_apart() {
        // A type that mentions a name of the group, a comment between, a
        // default, an `auto`, different brackets, a constructor's fields.
        let text = "def f (x: P x) (y: P x): Nat := a\n\
                    def g (a: Nat) -- a\n  (b: Nat): Nat := a\n\
                    def h (a: Nat := 1) (b: Nat): Nat := a\n\
                    def i [auto e: Eq a] [auto f: Eq a]: Nat := 1\n\
                    def j (a: Nat) [b: Nat]: Nat := a\n\
                    type T = | C (a: Nat) (b: Nat)\n";
        let (out, groups) = merged(text);
        assert_eq!(groups, 0);
        assert_eq!(out, text);
    }
}
