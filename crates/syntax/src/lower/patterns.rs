//! Patterns: dispatch on the kind, one function per kind, and the
//! expansions they hold: tuples nest to the right, lists are `Cons` cells
//! ending in `Nil` (or the `..` tail), and brackets round a constructor
//! widen its span to them.

use crate::Span;
use crate::ast::{Expr, Name, Pattern};
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
            Element::Node(node) => self.node_pattern(node),
        }
    }

    /// The pattern a node is. Out of line, with each kind's function, so
    /// that nested patterns keep small frames.
    #[inline(never)]
    fn node_pattern(&self, node: Node<'f>) -> Lowering<Pattern> {
        if self.stack.exceeded() {
            return Err(Unsupported::TooDeep);
        }
        use NodeKind::*;
        match node.kind() {
            PatternAbsurd => absurd(node),
            PatternCtor => self.pattern_ctor(node),
            PatternTuple => self.pattern_tuple(node),
            PatternList => self.pattern_list(node),
            PatternNamed => self.pattern_named(node),
            PatternRecord => self.pattern_record(node),
            PatternCtorFields => self.pattern_ctor_fields(node),
            PatternOr => self.pattern_or(node),
            PatternParen => self.pattern_paren(node),
            PatternNegative => pattern_negative(node),
            kind => Err(Unsupported::Kind(kind)),
        }
    }

    /// `C p q`: a constructor with arguments, spanning them.
    #[inline(never)]
    fn pattern_ctor(&self, node: Node<'f>) -> Lowering<Pattern> {
        let kind = NodeKind::PatternCtor;
        let mut parts = node.children();
        let ctor = match parts.next() {
            Some(Element::Leaf(leaf)) => name(leaf),
            _ => None,
        };
        let ctor = required(ctor, kind, "its constructor")?;
        let args = parts
            .map(|arg| self.pattern(arg))
            .collect::<Lowering<Vec<_>>>()?;
        Ok(Pattern::Ctor(ctor, args, whole(node)?))
    }

    /// `(a, b, c)`: `(a, (b, c))`, the outermost pair covering the brackets
    /// and each inner one running from its first component to the closing
    /// bracket, as tuple expressions do.
    #[inline(never)]
    fn pattern_tuple(&self, node: Node<'f>) -> Lowering<Pattern> {
        let kind = NodeKind::PatternTuple;
        let span = whole(node)?;
        let close = required(node.leaf(&Tok::RParen), kind, "`)`")?.span();
        let mut items = items(node, &[Tok::LParen, Tok::Comma, Tok::RParen])
            .into_iter()
            .map(|item| self.pattern(item))
            .collect::<Lowering<Vec<_>>>()?;
        if items.len() < 2 {
            return Err(Unsupported::Missing(kind, "two components"));
        }
        let mut last = items.pop().expect("two components");
        while let Some(first) = items.pop() {
            let s = if items.is_empty() {
                span
            } else {
                first.span().to(close)
            };
            last = Pattern::Tuple(Box::new(first), Box::new(last), s);
        }
        Ok(last)
    }

    /// `[a, b, ..rest]`: `Cons a (Cons b rest)`, or ending in `Nil` without
    /// a tail. The first cell covers the brackets, each later one runs from
    /// its item to the `]`, and the `Nil` ending `[a, b]` is its `]` (`[]`
    /// on its own spans both brackets).
    #[inline(never)]
    fn pattern_list(&self, node: Node<'f>) -> Lowering<Pattern> {
        let kind = NodeKind::PatternList;
        let span = whole(node)?;
        let close = required(node.leaf(&Tok::RBracket), kind, "`]`")?.span();
        let mut items = Vec::new();
        let mut tail = None;
        let mut parts = node.children();
        while let Some(part) = parts.next() {
            match part {
                Element::Leaf(leaf)
                    if matches!(leaf.tok(), Tok::LBracket | Tok::Comma | Tok::RBracket) => {}
                Element::Leaf(leaf) if leaf.tok() == &Tok::DotDot => {
                    let rest = required(parts.next(), kind, "its tail")?;
                    tail = Some(self.pattern(rest)?);
                }
                item => items.push(self.pattern(item)?),
            }
        }
        let nil = if items.is_empty() { span } else { close };
        let mut list = tail.unwrap_or(Pattern::Nil(nil));
        while let Some(item) = items.pop() {
            let s = if items.is_empty() {
                span
            } else {
                item.span().to(close)
            };
            list = Pattern::Cons(Box::new(item), Box::new(list), s);
        }
        Ok(list)
    }

    /// `[n := p]` among a constructor's arguments: an implicit field by
    /// name.
    #[inline(never)]
    fn pattern_named(&self, node: Node<'f>) -> Lowering<Pattern> {
        let kind = NodeKind::PatternNamed;
        let field = match node.after(&Tok::LBracket) {
            Some(Element::Leaf(leaf)) => name(leaf),
            _ => None,
        };
        let field = required(field, kind, "its field")?;
        let inner = required(node.after(&Tok::ColonEq), kind, "its pattern")?;
        Ok(Pattern::Named(
            field,
            Box::new(self.pattern(inner)?),
            whole(node)?,
        ))
    }

    /// `{ name = p, age, .. }`
    #[inline(never)]
    fn pattern_record(&self, node: Node<'f>) -> Lowering<Pattern> {
        let (fields, rest) = self.field_patterns(node)?;
        Ok(Pattern::Record {
            fields,
            rest,
            span: whole(node)?,
        })
    }

    /// `C { f = p, g, .. }`: the braces are the constructor's own, not a
    /// record pattern of their own.
    #[inline(never)]
    fn pattern_ctor_fields(&self, node: Node<'f>) -> Lowering<Pattern> {
        let kind = NodeKind::PatternCtorFields;
        let ctor = match node.children().next() {
            Some(Element::Leaf(leaf)) => name(leaf),
            _ => None,
        };
        let ctor = required(ctor, kind, "its constructor")?;
        let (fields, rest) = self.field_patterns(node)?;
        Ok(Pattern::ctor_fields(ctor, fields, rest, whole(node)?))
    }

    /// The fields in a node's braces, each a pattern after `=` or punned (a
    /// variable of the field's name), and whether they end with `..`.
    fn field_patterns(&self, node: Node<'f>) -> Lowering<(Vec<(Name, Pattern)>, bool)> {
        let kind = node.kind();
        let mut fields = Vec::new();
        let mut rest = false;
        let parts: Vec<_> = node
            .children()
            .skip_while(|part| !is(part, &Tok::LBrace))
            .skip(1)
            .collect();
        let mut i = 0;
        while let Some(&part) = parts.get(i) {
            i += 1;
            match part {
                Element::Leaf(leaf) if matches!(leaf.tok(), Tok::Comma | Tok::RBrace) => {}
                Element::Leaf(leaf) if leaf.tok() == &Tok::DotDot => rest = true,
                Element::Leaf(leaf) => {
                    let field = required(name(leaf), kind, "a field's name")?;
                    let pattern = if parts.get(i).is_some_and(|next| is(next, &Tok::Equals)) {
                        let pattern =
                            required(parts.get(i + 1).copied(), kind, "a field's pattern")?;
                        i += 2;
                        self.pattern(pattern)?
                    } else {
                        Pattern::Var(field.clone())
                    };
                    fields.push((field, pattern));
                }
                Element::Node(_) => return Err(Unsupported::Missing(kind, "a field's name")),
            }
        }
        Ok((fields, rest))
    }

    /// `p | q | …`, spanning its first alternative to its last.
    #[inline(never)]
    fn pattern_or(&self, node: Node<'f>) -> Lowering<Pattern> {
        let alternatives = items(node, &[Tok::Pipe])
            .into_iter()
            .map(|alternative| self.pattern(alternative))
            .collect::<Lowering<Vec<_>>>()?;
        let (first, last) = match alternatives.as_slice() {
            [first, .., last] => (first.span(), last.span()),
            _ => {
                return Err(Unsupported::Missing(
                    NodeKind::PatternOr,
                    "two alternatives",
                ));
            }
        };
        Ok(Pattern::Or(alternatives, first.to(last)))
    }

    /// `(p)`: `p`, except that a constructor written first inside, `(Some
    /// x)`, and a negative number, `(-1)`, take the brackets' span. Other
    /// patterns keep their own, `((Some x))` the inner brackets'.
    #[inline(never)]
    fn pattern_paren(&self, node: Node<'f>) -> Lowering<Pattern> {
        let kind = NodeKind::PatternParen;
        let inner = required(node.after(&Tok::LParen), kind, "its pattern")?;
        let pattern = self.pattern(inner)?;
        let first = node.token_range().start + 1;
        let widened = match self.tree.tokens().get(first).map(|token| &token.tok) {
            Some(Tok::Upper(_)) => true,
            Some(Tok::Lower(text)) => text == "Quot.mk",
            Some(Tok::Minus) => matches!(pattern, Pattern::NegNum(..)),
            _ => false,
        };
        if !widened {
            return Ok(pattern);
        }
        let span = whole(node)?;
        Ok(match pattern {
            Pattern::NegNum(n, _) => Pattern::NegNum(n, span),
            other => with_span(other, span),
        })
    }

    /// `((a, b): A)`, a lambda's parameter: the pattern and its type
    /// ([`NodeKind::PatternTyped`]).
    #[allow(dead_code)] // For lane L3's lambdas.
    pub(crate) fn pattern_typed(&self, node: Node<'f>) -> Lowering<(Pattern, Expr)> {
        let kind = NodeKind::PatternTyped;
        let pattern = required(node.after(&Tok::LParen), kind, "its pattern")?;
        let ty = required(node.after(&Tok::Colon), kind, "its type")?;
        Ok((self.pattern(pattern)?, self.expr(ty)?))
    }
}

/// A constructor pattern, its span widened to `span` (its brackets).
pub(crate) fn with_span(p: Pattern, span: Span) -> Pattern {
    match p {
        Pattern::Ctor(name, args, _) => Pattern::Ctor(name, args, span),
        Pattern::CtorFields {
            ctor, fields, rest, ..
        } => Pattern::ctor_fields(ctor, fields, rest, span),
        other => other,
    }
}

/// A pattern of one token: a variable, `_`, a number, a character, or a
/// constructor without arguments (`Quot.mk` among them: it isn't one, but
/// is read as one so that the elaborator can say why).
fn leaf_pattern(leaf: Leaf<'_>) -> Lowering<Pattern> {
    let span = leaf.span();
    Ok(match leaf.tok() {
        Tok::Lower(text) if text != "Quot.mk" => Pattern::Var(name(leaf).expect("a name")),
        Tok::Lower(_) | Tok::Upper(_) => {
            Pattern::Ctor(name(leaf).expect("a name"), Vec::new(), span)
        }
        Tok::Underscore => Pattern::Wildcard(span),
        Tok::Num(n) => Pattern::Num(n.clone(), span),
        Tok::Char(c) => Pattern::Char(*c, span),
        _ => return Err(Unsupported::Token),
    })
}

/// `()`: the pattern of an empty type.
fn absurd(node: Node<'_>) -> Lowering<Pattern> {
    Ok(Pattern::Absurd(whole(node)?))
}

/// `-3`, in brackets, a tuple or a constructor's arguments.
fn pattern_negative(node: Node<'_>) -> Lowering<Pattern> {
    let kind = NodeKind::PatternNegative;
    let n = match node.after(&Tok::Minus) {
        Some(Element::Leaf(leaf)) => match leaf.tok() {
            Tok::Num(n) => Some(n.clone()),
            _ => None,
        },
        _ => None,
    };
    let n = required(n, kind, "its number")?;
    Ok(Pattern::NegNum(n, whole(node)?))
}

fn whole(node: Node<'_>) -> Lowering<Span> {
    required(node.span(), node.kind(), "tokens")
}

fn is(element: &Element<'_>, tok: &Tok) -> bool {
    matches!(element, Element::Leaf(leaf) if leaf.tok() == tok)
}

/// A node's parts other than its own tokens in `punctuation`.
fn items<'f>(node: Node<'f>, punctuation: &[Tok]) -> Vec<Element<'f>> {
    node.children()
        .filter(|child| !matches!(child, Element::Leaf(leaf) if punctuation.contains(leaf.tok())))
        .collect()
}
