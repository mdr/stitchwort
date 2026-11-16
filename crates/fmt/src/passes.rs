//! The tidy passes of docs/proposals/fmt-passes.md §2: each reads the
//! syntax tree and returns edits to the text. [`run`] applies a pass's edits
//! and parses the result again, so every intermediate is a real program
//! with rule N ([`crate::tidy`]) in force for whoever reads its tree, and a
//! pass that has nothing to do costs nothing.
//!
//! After them, a file has:
//!
//! - P1: a `∀` after the name of every theorem with explicit parameters and
//!   a result type;
//! - P2: no comma before the closing bracket of a comma bracket;
//! - P3: no redundant round brackets after a row or around a binder's whole
//!   type;
//! - P4: no adjacent parameters of one type that merge into one group.

use std::ops::Range;

use stitchwort_syntax::tree::{Element, Node, NodeKind, SyntaxFile};
use stitchwort_syntax::{DEFAULT_STACK, FileId, Tok, parse_tree};

pub use crate::merge::merge_parameters;
pub use crate::parens::drop_parens;

/// A change to the text: the bytes in `range` become `text`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edit {
    pub range: Range<usize>,
    pub text: String,
}

/// A tidy pass: the edits that make the tree tidy for it, none if it is.
/// The text is what the tree was parsed from, which a pass that tries a
/// candidate needs to parse it.
pub type Pass = fn(&SyntaxFile, &str) -> Vec<Edit>;

/// The passes, in the order they run (docs/proposals/fmt-passes.md §3.1).
pub const PASSES: [Pass; 4] = [
    theorem_forall,
    trailing_comma,
    drop_parens,
    merge_parameters,
];

/// A file's text after the passes, and its tree.
pub struct Tidied {
    pub text: String,
    pub tree: SyntaxFile,
    /// How many edits each pass made, in the order they ran.
    pub edits: Vec<usize>,
}

/// Runs each of `passes` on the file, in order.
pub fn run(file: FileId, text: &str, passes: &[Pass]) -> Tidied {
    let mut text = text.to_string();
    let mut tree = parse_tree(file, &text, DEFAULT_STACK);
    let mut made = Vec::with_capacity(passes.len());
    for pass in passes {
        let edits = pass(&tree, &text);
        made.push(edits.len());
        if edits.is_empty() {
            continue;
        }
        text = apply(&text, edits);
        tree = parse_tree(file, &text, DEFAULT_STACK);
    }
    Tidied {
        text,
        tree,
        edits: made,
    }
}

/// `text` with the edits made. They must not overlap.
fn apply(text: &str, mut edits: Vec<Edit>) -> String {
    edits.sort_by_key(|edit| std::cmp::Reverse(edit.range.start));
    let mut out = text.to_string();
    for edit in edits {
        out.replace_range(edit.range, &edit.text);
    }
    out
}

/// Calls `f` on every node of the file, outside in.
fn each_node<'f>(tree: &'f SyntaxFile, f: &mut impl FnMut(Node<'f>)) {
    fn walk<'f>(node: Node<'f>, f: &mut impl FnMut(Node<'f>)) {
        f(node);
        for child in node.children() {
            if let Element::Node(child) = child {
                walk(child, f);
            }
        }
    }
    for decl in tree.decls() {
        walk(decl, f);
    }
}

/// The index of the first token of `element`.
fn first_token(element: Element<'_>) -> usize {
    match element {
        Element::Leaf(leaf) => leaf.index(),
        Element::Node(node) => node.token_range().start,
    }
}

/// P1, D3472: a theorem with explicit parameters says `∀` before them,
/// `theorem leTrans ∀ (a b c: Nat) (h: a ≤ b): …`. It is cosmetic (the
/// parser reads the same tree either way), so the formatter writes it, and
/// leaves it off a header whose parameters are all implicit, which says
/// nothing is quantified over by name. The edit goes before the first
/// parameter when it is on the name's line, else at the end of the name's
/// line.
pub fn theorem_forall(tree: &SyntaxFile, _text: &str) -> Vec<Edit> {
    let tokens = tree.tokens();
    let mut edits = Vec::new();
    each_node(tree, &mut |node| {
        if node.kind() != NodeKind::Theorem {
            return;
        }
        let children: Vec<Element> = node.children().collect();
        // Attributes may come first, then `theorem`, the name (one token,
        // qualified or not), then the header.
        let Some(keyword) = children.iter().position(
            |child| matches!(child, Element::Leaf(leaf) if leaf.token().tok == Tok::KwTheorem),
        ) else {
            return;
        };
        let [name, first, ..] = &children[keyword + 1..] else {
            return;
        };
        let Element::Leaf(name) = name else {
            return;
        };
        if matches!(first, Element::Leaf(leaf) if leaf.token().tok == Tok::KwForall) {
            return;
        }
        let explicit = children[keyword + 2..].iter().any(|child| {
            matches!(child, Element::Node(param)
                if param.kind() == NodeKind::Param
                    && tokens[param.token_range().start].tok == Tok::LParen)
        });
        let has_result = children[keyword + 2..].iter().any(
            |child| matches!(child, Element::Node(result) if result.kind() == NodeKind::ResultType),
        );
        if !(explicit && has_result) {
            return;
        }
        let first = &tokens[first_token(*first)];
        if first.line_start {
            let end = name.token().span.end as usize;
            edits.push(Edit {
                range: end..end,
                text: " ∀".to_string(),
            });
        } else {
            let start = first.span.start as usize;
            edits.push(Edit {
                range: start..start,
                text: "∀ ".to_string(),
            });
        }
    });
    edits
}

/// P2, D1012: no comma before the closing bracket of a comma bracket. Rule
/// N has already moved the comma's comments elsewhere, so deleting it
/// leaves every comment on the token it belongs to.
pub fn trailing_comma(tree: &SyntaxFile, _text: &str) -> Vec<Edit> {
    use NodeKind::*;
    let tokens = tree.tokens();
    fn tok<'f>(element: &Element<'f>) -> Option<&'f Tok> {
        match element {
            Element::Leaf(leaf) => Some(&leaf.token().tok),
            Element::Node(_) => None,
        }
    }
    let mut edits = Vec::new();
    each_node(tree, &mut |node| {
        if !matches!(
            node.kind(),
            List | Tuple
                | Record
                | Fields
                | PatternList
                | PatternTuple
                | PatternRecord
                | Attributes
                | Import
        ) {
            return;
        }
        let children: Vec<Element> = node.children().collect();
        let [.., item, comma, closer] = children.as_slice() else {
            return;
        };
        let opens = children
            .iter()
            .any(|el| matches!(tok(el), Some(Tok::LParen | Tok::LBracket | Tok::LBrace)));
        let ends = matches!(tok(closer), Some(Tok::RParen | Tok::RBracket | Tok::RBrace));
        // Something has to be before the comma: `[,]` is not a trailing one.
        let has_item = !matches!(
            tok(item),
            Some(Tok::LParen | Tok::LBracket | Tok::LBrace | Tok::Comma | Tok::Pipe)
        );
        if opens && ends && has_item && matches!(tok(comma), Some(Tok::Comma)) {
            let span = tokens[first_token(*comma)].span;
            edits.push(Edit {
                range: span.start as usize..span.end as usize,
                text: String::new(),
            });
        }
    });
    edits
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::SourceMap;

    use super::*;

    fn tidied(text: &str, passes: &[Pass]) -> String {
        let file = SourceMap::new().add("t.sw", text);
        run(file, text, passes).text
    }

    #[test]
    fn a_theorem_with_explicit_parameters_gets_a_forall_where_it_can_be_read() {
        assert_eq!(
            tidied("theorem t (a: Nat): a = a := rfl\n", &PASSES),
            "theorem t ∀ (a: Nat): a = a := rfl\n"
        );
        assert_eq!(
            tidied("theorem t\n  (a: Nat): a = a := rfl\n", &PASSES),
            "theorem t ∀\n  (a: Nat): a = a := rfl\n"
        );
    }

    #[test]
    fn a_theorem_with_attributes_gets_its_forall_after_the_name() {
        assert_eq!(
            tidied(
                "@[reading]\ntheorem t (a: Nat): a = a := rfl\n",
                &[theorem_forall]
            ),
            "@[reading]\ntheorem t ∀ (a: Nat): a = a := rfl\n"
        );
    }

    #[test]
    fn a_theorem_that_is_tidy_for_forall_is_left_alone() {
        for text in [
            "theorem t ∀ (a: Nat): a = a := rfl\n",
            "theorem t: 1 = 1 := rfl\n",
        ] {
            assert_eq!(tidied(text, &[theorem_forall]), text);
        }
    }

    #[test]
    fn the_trailing_comma_of_a_comma_bracket_is_deleted() {
        assert_eq!(
            tidied("def x: T := [1, 2,]\n", &PASSES),
            "def x: T := [1, 2]\n"
        );
        assert_eq!(
            tidied("def x: T := (1, 2,)\n", &PASSES),
            "def x: T := (1, 2)\n"
        );
        assert_eq!(
            tidied("def x: T := [\n  1, -- one\n  2, -- two\n]\n", &PASSES),
            "def x: T := [\n  1, -- one\n  2 -- two\n]\n"
        );
        let text = "def x: T := [1, 2]\n";
        assert_eq!(tidied(text, &PASSES), text);
    }

    #[test]
    fn the_runner_applies_a_pass_to_the_tree_the_one_before_it_left() {
        assert_eq!(
            tidied("theorem t (a: Nat): f [a,] := rfl\n", &PASSES),
            "theorem t ∀ (a: Nat): f [a] := rfl\n"
        );
    }

    #[test]
    fn the_redundant_brackets_after_a_row_and_around_a_binder_type_are_dropped() {
        assert_eq!(
            tidied("def a: {Fail} (List Nat) := []\n", &[drop_parens]),
            "def a: {Fail} List Nat := []\n"
        );
        assert_eq!(
            tidied(
                "theorem c ∀ (h: (∀ (i: Nat) => i = i)): True := h\n",
                &[drop_parens]
            ),
            "theorem c ∀ (h: ∀ (i: Nat) => i = i): True := h\n"
        );
    }

    #[test]
    fn adjacent_parameters_of_one_type_are_merged() {
        assert_eq!(
            tidied("def f (a: Nat) (b: Nat): Nat := a\n", &[merge_parameters]),
            "def f (a b: Nat): Nat := a\n"
        );
    }

    #[test]
    fn the_brackets_of_a_parameter_are_dropped_before_the_group_is_merged() {
        assert_eq!(
            tidied("def f (a: (Nat)) (b: Nat): Nat := a\n", &PASSES),
            "def f (a b: Nat): Nat := a\n"
        );
    }
}
