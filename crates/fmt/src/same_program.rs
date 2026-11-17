//! The tree check: the output parses to the original file's tree, up to the
//! changes the tidy passes ([`crate::passes`]) are allowed to make
//! (SW-3610). It reads the original as written, not the tidied text, and
//! shares no code with the passes, so a pass that changed the program is
//! caught here rather than checked against its own result.
//!
//! The trees compared are the compiler's ([`equivalence::shape`], every
//! field of the parser's result except positions). Of the passes:
//!
//! - P1 (`∀` before a theorem's parameters), P2 (trailing commas) and P3
//!   (spare round brackets) change nothing in that tree: it records none of
//!   them. The one bracket it does record, around an application's head
//!   ([`stitchwort_syntax::ast::Expr::Bracketed`]), is one P3 never drops.
//! - P4 (merged parameter groups) does: `(a: Nat) (b: Nat)` is two binders
//!   and `(a b: Nat)` one with two names. [`one_binder_per_name`] splits
//!   groups on both sides.
//!
//! Each tolerated change is one small function on the tree below; nothing
//! else may differ.

use stitchwort_syntax::ast::Module;
use stitchwort_syntax::equivalence;

/// A node of the compiler's tree, read back from its `Debug` dump: a head
/// (`Pi`, `Some`, or empty for a list or tuple) and its items, each with
/// its field name in a `{ … }`, or an atom (a name, number, text or `_`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Tree<'a> {
    Atom(&'a str),
    Node {
        head: &'a str,
        open: u8,
        items: Vec<(Option<&'a str>, Tree<'a>)>,
    },
}

/// What differs first between the two modules' trees once the tolerated
/// changes are normalised away, or nothing.
pub(crate) fn difference(original: &Module, output: &Module) -> Result<Option<String>, String> {
    let (before, after) = (equivalence::shape(original), equivalence::shape(output));
    let (before, after) = (
        one_binder_per_name(parse(&before)?),
        one_binder_per_name(parse(&after)?),
    );
    if before == after {
        return Ok(None);
    }
    let (mut x, mut y) = (String::new(), String::new());
    print(&before, 0, &mut x);
    print(&after, 0, &mut y);
    let (mut x, mut y) = (x.lines(), y.lines());
    loop {
        let (a, b) = (x.next(), y.next());
        if a != b {
            return Ok(Some(format!(
                "the output parses to a different tree: the original has `{}` where the output has `{}`",
                a.map_or("nothing", str::trim),
                b.map_or("nothing", str::trim)
            )));
        }
    }
}

/// P4: a `Pi` binding several names to one type, `(a b: T) -> R`, becomes
/// one `Pi` per name, `(a: T) -> (b: T) -> R`. A group whose type mentions
/// one of its own names is left whole: split, the later binders' types
/// would mean the earlier names, not the outer ones.
fn one_binder_per_name(tree: Tree<'_>) -> Tree<'_> {
    let Tree::Node { head, open, items } = tree else {
        return tree;
    };
    let items: Vec<_> = items
        .into_iter()
        .map(|(key, item)| (key, one_binder_per_name(item)))
        .collect();
    if head != "Pi" {
        return Tree::Node { head, open, items };
    }
    let field = |name: &str| items.iter().position(|(key, _)| *key == Some(name));
    let (Some(names), Some(dom), Some(cod)) = (field("names"), field("dom"), field("cod")) else {
        return Tree::Node { head, open, items };
    };
    let Tree::Node { items: group, .. } = &items[names].1 else {
        return Tree::Node { head, open, items };
    };
    if group.len() < 2
        || group
            .iter()
            .filter_map(|(_, name)| name_text(name))
            .any(|text| mentions(&items[dom].1, text))
    {
        return Tree::Node { head, open, items };
    }
    let group = group.clone();
    let mut inner = items[cod].1.clone();
    for name in group.into_iter().rev() {
        let mut one = items.clone();
        one[names].1 = Tree::Node {
            head: "",
            open: b'[',
            items: vec![name],
        };
        one[cod].1 = inner;
        inner = Tree::Node {
            head,
            open,
            items: one,
        };
    }
    inner
}

/// The text of a `Name { text: "a", … }`, quoted as in the dump.
fn name_text<'a>(tree: &Tree<'a>) -> Option<&'a str> {
    let Tree::Node { items, .. } = tree else {
        return None;
    };
    items.iter().find_map(|(key, value)| match (key, value) {
        (Some("text"), Tree::Atom(text)) => Some(*text),
        _ => None,
    })
}

/// Whether a name with this (quoted) text occurs anywhere in `tree`: over
/// counting only keeps a group whole that could have been split.
fn mentions(tree: &Tree<'_>, text: &str) -> bool {
    match tree {
        Tree::Atom(atom) => *atom == text,
        Tree::Node { items, .. } => items.iter().any(|(_, item)| mentions(item, text)),
    }
}

/// The bracket that closes `open`.
fn closer(open: u8) -> u8 {
    match open {
        b'{' => b'}',
        b'(' => b')',
        _ => b']',
    }
}

/// Prints `tree` one item per line, indented, for [`difference`]'s message.
fn print(tree: &Tree<'_>, depth: usize, out: &mut String) {
    match tree {
        Tree::Atom(atom) => out.push_str(atom),
        Tree::Node { head, open, items } => {
            out.push_str(head);
            out.push(char::from(*open));
            for (key, item) in items {
                out.push('\n');
                out.push_str(&"  ".repeat(depth + 1));
                if let Some(key) = key {
                    out.push_str(key);
                    out.push_str(": ");
                }
                print(item, depth + 1, out);
            }
            out.push('\n');
            out.push_str(&"  ".repeat(depth));
            out.push(char::from(closer(*open)));
        }
    }
}

const PUNCTUATION: &[u8] = b"{}()[],:";

/// Reads a `{:#?}` dump: heads and field names are atoms, items are
/// separated by commas, and texts and characters are read with their
/// escapes, so brackets inside them are not structure.
fn parse(text: &str) -> Result<Tree<'_>, String> {
    let tokens = lex(text)?;
    let mut at = 0;
    let tree = parse_value(&tokens, &mut at)?;
    if at != tokens.len() {
        return Err(format!("the tree dump has more after item {at}"));
    }
    Ok(tree)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Token<'a> {
    Atom(&'a str),
    Punct(u8),
}

/// The dump's tokens. Every byte that ends a token is ASCII, so the slices
/// fall on character boundaries.
fn lex(text: &str) -> Result<Vec<Token<'_>>, String> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c.is_ascii_whitespace() {
            i += 1;
        } else if PUNCTUATION.contains(&c) {
            tokens.push(Token::Punct(c));
            i += 1;
        } else if c == b'"' || c == b'\'' {
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i] != c {
                i += if bytes[i] == b'\\' { 2 } else { 1 };
            }
            if i >= bytes.len() {
                return Err("the tree dump has an unclosed text".into());
            }
            i += 1;
            tokens.push(Token::Atom(&text[start..i]));
        } else {
            let start = i;
            while i < bytes.len()
                && !bytes[i].is_ascii_whitespace()
                && !PUNCTUATION.contains(&bytes[i])
                && bytes[i] != b'"'
                && bytes[i] != b'\''
            {
                i += 1;
            }
            tokens.push(Token::Atom(&text[start..i]));
        }
    }
    Ok(tokens)
}

fn parse_value<'a>(tokens: &[Token<'a>], at: &mut usize) -> Result<Tree<'a>, String> {
    let head = match tokens.get(*at) {
        Some(Token::Atom(atom)) => {
            *at += 1;
            *atom
        }
        Some(Token::Punct(b'{' | b'(' | b'[')) => "",
        other => {
            return Err(format!(
                "the tree dump has `{other:?}` where an item belongs"
            ));
        }
    };
    let open = match tokens.get(*at) {
        Some(Token::Punct(open @ (b'{' | b'(' | b'['))) => *open,
        _ => return Ok(Tree::Atom(head)),
    };
    *at += 1;
    let close = closer(open);
    let mut items = Vec::new();
    loop {
        if tokens.get(*at) == Some(&Token::Punct(close)) {
            *at += 1;
            return Ok(Tree::Node { head, open, items });
        }
        let first = parse_value(tokens, at)?;
        let item = if tokens.get(*at) == Some(&Token::Punct(b':')) {
            *at += 1;
            let Tree::Atom(key) = first else {
                return Err("the tree dump has a key that isn't a name".into());
            };
            (Some(key), parse_value(tokens, at)?)
        } else {
            (None, first)
        };
        items.push(item);
        match tokens.get(*at) {
            Some(Token::Punct(b',')) => *at += 1,
            Some(Token::Punct(c)) if *c == close => {}
            other => return Err(format!("the tree dump has `{other:?}` after an item")),
        }
    }
}

#[cfg(test)]
mod tests {
    use stitchwort_syntax::{DEFAULT_STACK, SourceMap, parse_module_within};

    use super::*;

    fn module(text: &str) -> Module {
        let file = SourceMap::new().add("t.sw", text);
        parse_module_within(file, text, DEFAULT_STACK).expect("parses")
    }

    fn same(a: &str, b: &str) -> bool {
        difference(&module(a), &module(b)).expect("reads").is_none()
    }

    #[test]
    fn the_tidy_passes_changes_are_tolerated() {
        // P1, P2, P3, P4.
        assert!(same(
            "theorem t (a: Nat): a = a := byComputing\n",
            "theorem t ∀ (a: Nat): a = a := byComputing\n"
        ));
        assert!(same("def x: T := [1, 2,]\n", "def x: T := [1, 2]\n"));
        assert!(same(
            "def a: {Fail} (List Nat) := []\n",
            "def a: {Fail} List Nat := []\n"
        ));
        assert!(same(
            "def f (a: Nat) (b: Nat) [c: Type] [d: Type]: Nat := a\n",
            "def f (a b: Nat) [c d: Type]: Nat := a\n"
        ));
        assert!(same(
            "theorem t: ∀ (a: Nat) (b: Nat) (c: Nat) => a = a := byComputing\n",
            "theorem t: ∀ (a b: Nat) (c: Nat) => a = a := byComputing\n"
        ));
    }

    #[test]
    fn other_changes_are_not() {
        assert!(!same("def x: Nat := f a b\n", "def x: Nat := f b a\n"));
        assert!(!same("def x: Nat := f (g a)\n", "def x: Nat := f g a\n"));
        assert!(!same(
            "def x: Text := \"a{b\"\n",
            "def x: Text := \"a}b\"\n"
        ));
        // Kinds of parameter don't merge.
        assert!(!same(
            "def f (a: Nat) [b: Nat]: Nat := a\n",
            "def f (a b: Nat): Nat := a\n"
        ));
        // A group is its split form (D3679), so in both the second `x`
        // means the first parameter.
        assert!(same(
            "def f (x: P x) (y: P x): Nat := 1\n",
            "def f (x y: P x): Nat := 1\n"
        ));
    }

    #[test]
    fn the_dump_reads_back_as_written() {
        for text in [
            "A { b: [c, \"d)\", '}'], e: F(1) }",
            "[]",
            "Some('\\'')",
            "x",
        ] {
            let tree = parse(text).expect(text);
            assert!(matches!(tree, Tree::Node { .. } | Tree::Atom(_)), "{text}");
        }
        assert!(parse("A { b: c").is_err());
    }
}
