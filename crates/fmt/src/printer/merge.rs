//! D3565: adjacent parameters of the same kind and the same type are
//! merged, `(a: Nat) (b: Nat)` into `(a b: Nat)`, in definition and theorem
//! headers, `∀` binders and lambdas (docs/proposals/formatter-style.md §4).
//!
//! It is a rewrite of tokens, done before layout and checked on its own
//! ([`check`]). The compiler's tree keeps a group as one binder with
//! several names, so the check compares the two texts with every group
//! split into one binder a name ([`split`]). Splitting `(x y: P x)` would
//! change which `x` the second type means, which is why a type that
//! mentions a name of the group is never merged: then splitting is exact,
//! and the comparison sees everything the merge did.

use stitchwort_syntax::tree::{Element, Node, NodeKind, SyntaxFile, token_text_range};
use stitchwort_syntax::{DEFAULT_STACK, SourceMap, Tok, equivalence, parse_tree};

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
    range: std::ops::Range<usize>,
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

/// Replaces byte ranges of `text`; `edits` don't overlap.
fn apply(text: &str, mut edits: Vec<(std::ops::Range<usize>, String)>) -> String {
    edits.sort_by_key(|(range, _)| range.start);
    let mut out = String::with_capacity(text.len());
    let mut at = 0;
    for (range, replacement) in edits {
        out.push_str(&text[at..range.start]);
        out.push_str(&replacement);
        at = range.end;
    }
    out.push_str(&text[at..]);
    out
}

/// `text` with D3565's merges made, and how many groups they made; `None`
/// if there are none.
pub(crate) fn merge(text: &str) -> Option<(String, usize)> {
    let file = SourceMap::new().next_id();
    let tree = parse_tree(file, text, DEFAULT_STACK).ok()?;
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
                    edits.push((range, merged));
                }
                run.clear();
            };
            let mut previous_end = None;
            for child in node.children() {
                let next = match child {
                    Element::Node(n) if n.kind() == kind => param(&tree, text, n),
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
    let groups = edits.len();
    (groups > 0).then(|| (apply(text, edits), groups))
}

/// `text` with every parameter group split into one binder a name, `(a b:
/// T)` into `(a: T) (b: T)`, for comparing trees.
fn split(text: &str) -> Option<String> {
    let file = SourceMap::new().next_id();
    let tree = parse_tree(file, text, DEFAULT_STACK).ok()?;
    let mut edits = Vec::new();
    for decl in tree.decls() {
        walk(decl, &mut |node| {
            if !matches!(node.kind(), NodeKind::Param | NodeKind::LambdaParam) {
                return;
            }
            if let Some(p) = param(&tree, text, node)
                && p.names.len() > 1
            {
                let (open, close) = bracket(&p.open);
                let parts: Vec<String> = p
                    .names
                    .iter()
                    .map(|name| format!("{open}{name}: {}{close}", p.ty_text))
                    .collect();
                edits.push((p.range, parts.join(" ")));
            }
        });
    }
    Some(apply(text, edits))
}

/// Checks a merge on its own: the same comments in the same order, and the
/// same tree once every group on either side is split.
pub(crate) fn check(before: &str, after: &str) -> Result<(), String> {
    let file = SourceMap::new().next_id();
    let comments = |text: &str| -> Option<Vec<String>> {
        let lexed = stitchwort_syntax::lex_with_trivia(file, text).ok()?;
        let mut out = Vec::new();
        for trivia in lexed.trivia.iter().chain([&lexed.eof]) {
            out.extend(trivia.leading.iter().map(|c| c.text.clone()));
            out.extend(trivia.trailing.iter().map(|c| c.text.clone()));
        }
        Some(out)
    };
    if comments(before) != comments(after) {
        return Err("merging parameters moved a comment".into());
    }
    let (Some(a), Some(b)) = (split(before), split(after)) else {
        return Err("merging parameters made text that doesn't parse".into());
    };
    let (a, b) = (equivalence::parse_shape(&a), equivalence::parse_shape(&b));
    match (a, b) {
        (Ok(a), Ok(b)) if a == b => Ok(()),
        (Ok(_), Ok(_)) => Err("merging parameters changed the tree".into()),
        _ => Err("merging parameters made text that doesn't parse".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adjacent_parameters_of_one_type_merge() {
        let text = "def f (a: Nat) (b: Nat) [t: Type] [u: Type] (x: t): Nat := a\n\
                    theorem g ∀ (xs: List Nat) (ys: List Nat): xs = ys := h\n\
                    def h: Nat := forall (x: Nat) (y: Nat) => (p: Nat) (q: Nat) => x\n";
        let (merged, groups) = merge(text).unwrap();
        assert_eq!(groups, 5);
        assert_eq!(
            merged,
            "def f (a b: Nat) [t u: Type] (x: t): Nat := a\n\
             theorem g ∀ (xs ys: List Nat): xs = ys := h\n\
             def h: Nat := forall (x y: Nat) => (p q: Nat) => x\n"
        );
        assert_eq!(check(text, &merged), Ok(()));
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
        assert_eq!(merge(text), None);
    }

    #[test]
    fn a_merge_that_changes_the_tree_is_caught() {
        let before = "def f (a: Nat) (b: Nat): Nat := a\n";
        assert!(check(before, "def f (a b: Int): Nat := a\n").is_err());
        assert!(check(before, "def f (a b: Nat): Nat := a\n").is_ok());
    }
}
