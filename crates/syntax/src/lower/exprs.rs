//! Expressions: dispatch on the kind, one function per kind (or small
//! family), and the expansions of the shorthand they hold. The parser
//! still builds the compiler's tree itself and shares the expansions
//! ([`chain`], [`binary`], [`prefix_op`], [`piped`]), so both routes expand
//! the same way.
//!
//! Some kinds lower differently by where they are, which the caller says:
//! an application's argument `-x` is a [`NegForm::Argument`] and its
//! argument `C { … }` is marked as one; a `(f a)` at the head of an
//! application with arguments is [`Expr::Bracketed`], and so is a list's
//! only item `(a ..< b)`. Everywhere else brackets leave no trace.

use super::sections::{fill_receiver, leads_with_section, section_dot};
use crate::Span;
use crate::ast::{BinOp, Bracket, CHAIN, Expr, Name, NegForm, SECTION};
use crate::lexer::Tok;
use crate::negation::{argument_minus, negative_numeral};
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::{Lower, Lowering, Unsupported};

impl<'f> Lower<'f> {
    /// The expression an element of the tree is.
    pub(crate) fn expr(&self, element: Element<'f>) -> Lowering<Expr> {
        match element {
            Element::Leaf(leaf) => leaf_expr(leaf),
            Element::Node(node) => self.node_expr(node),
        }
    }

    /// The expression a node is. Each kind's function is out of line, so
    /// that this one, which every level of a nested expression goes
    /// through, keeps a small frame (the depth is bounded by stack, as the
    /// parser's is).
    fn node_expr(&self, node: Node<'f>) -> Lowering<Expr> {
        if self.stack.exceeded() {
            return Err(Unsupported::TooDeep);
        }
        use NodeKind::*;
        match node.kind() {
            Paren => self.paren(node),
            Unit => Ok(Expr::Unit(whole(node)?)),
            Annotation => self.annotation(node),
            Tuple => self.tuple(node),
            NamedArg => self.named_arg(node),
            List => self.list(node),
            Spread => self.spread(node),
            Record => self.record(node),
            CtorFields => self.ctor_fields(node, false).map(Argument::into_expr),
            App => self.app(node),
            FieldAccess => self.field_access(node),
            Prefix => self.prefix(node, false),
            Binary => self.binary(node),
            Chain => self.chain(node),
            Membership => self.membership(node),
            Range => self.range(node),
            Pipe => self.pipe(node),
            Arrow => self.arrow(node),
            Iff => self.iff(node),
            Interpolated => self.interpolated(node),
            Universe => universe(node),
            Include => include(node),
            FunctionType => self.function_type(node),
            Effect => self.effect(node),
            Section => self.section(node),
            OperatorSection => self.operator_section(node),
            Block => self.block(node),
            LetExpr => self.let_expr(node),
            Seq => self.seq(node),
            Lambda => self.lambda(node),
            Exists => self.exists(node),
            Forall => self.forall(node),
            If => self.if_expr(node),
            ClauseLambda => self.clause_lambda(node),
            kind => Err(Unsupported::Kind(kind)),
        }
    }

    /// `(e)`: `e`, the brackets leaving no trace (but see [`Self::app`] and
    /// [`Self::list`]).
    #[inline(never)]
    fn paren(&self, node: Node<'f>) -> Lowering<Expr> {
        let inner = node.after(&Tok::LParen);
        self.expr(required(inner, NodeKind::Paren, "its expression")?)
    }

    /// `(e : T)`
    #[inline(never)]
    fn annotation(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Annotation;
        let inner = required(node.after(&Tok::LParen), kind, "its expression")?;
        let ty = required(node.after(&Tok::Colon), kind, "its type")?;
        Ok(Expr::Ann(
            Box::new(self.expr(inner)?),
            Box::new(self.expr(ty)?),
            whole(node)?,
        ))
    }

    /// `(a, b, c)`: `(a, (b, c))`, the outermost pair covering the
    /// brackets and each inner one running from its first component to the
    /// closing bracket.
    #[inline(never)]
    fn tuple(&self, node: Node<'f>) -> Lowering<Expr> {
        let span = whole(node)?;
        let close = required(node.leaf(&Tok::RParen), NodeKind::Tuple, "`)`")?.span();
        let mut items = items(node, &[Tok::LParen, Tok::Comma, Tok::RParen])
            .into_iter()
            .map(|item| self.expr(item))
            .collect::<Lowering<Vec<_>>>()?;
        if items.len() < 2 {
            return Err(Unsupported::Missing(NodeKind::Tuple, "two components"));
        }
        let mut last = items.pop().expect("two components");
        while let Some(first) = items.pop() {
            let s = if items.is_empty() {
                span
            } else {
                first.span().to(close)
            };
            last = Expr::Tuple(Box::new(first), Box::new(last), s);
        }
        Ok(last)
    }

    /// `(x := e)` or `[x := e]`, an argument by name; `[decreasing := p]`.
    #[inline(never)]
    fn named_arg(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::NamedArg;
        let mut leaves = node.own_leaves();
        let open = required(leaves.next(), kind, "its bracket")?;
        let bracket = match open.tok() {
            Tok::LParen => Bracket::Round,
            Tok::LBracket => Bracket::Square,
            _ => return Err(Unsupported::Missing(kind, "its bracket")),
        };
        let label = required(leaves.next(), kind, "its name")?;
        let label = match label.tok() {
            Tok::KwDecreasing => Name {
                text: "decreasing".to_string(),
                span: label.span(),
            },
            _ => required(name(label), kind, "its name")?,
        };
        let value = required(node.after(&Tok::ColonEq), kind, "its value")?;
        Ok(Expr::NamedArg(
            label,
            Box::new(self.expr(value)?),
            whole(node)?,
            bracket,
        ))
    }

    /// `[a, b, ..xs]`. A list of one bracketed range, `[(0 ..< n)]`, keeps
    /// its brackets as [`Expr::Bracketed`], so `W-RANGE-IN-BRACKETS`, which
    /// warns about `[0 ..< n]`, stays quiet.
    #[inline(never)]
    fn list(&self, node: Node<'f>) -> Lowering<Expr> {
        let mut items = items(node, &[Tok::LBracket, Tok::Comma, Tok::RBracket])
            .into_iter()
            .map(|item| Ok((item, self.expr(item)?)))
            .collect::<Lowering<Vec<_>>>()?;
        let bracketed_range = match items.as_slice() {
            [(Element::Node(paren), Expr::Binary(BinOp::Range | BinOp::RangeThrough, ..))] => {
                paren.kind() == NodeKind::Paren && node.leaf(&Tok::Comma).is_none()
            }
            _ => false,
        };
        if bracketed_range {
            let (_, range) = items.pop().expect("one item");
            let span = range.span();
            return Ok(Expr::List(
                vec![Expr::Bracketed(Box::new(range), span)],
                whole(node)?,
            ));
        }
        Ok(Expr::List(
            items.into_iter().map(|(_, item)| item).collect(),
            whole(node)?,
        ))
    }

    /// `..xs` in a list.
    #[inline(never)]
    fn spread(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Spread;
        let dots = required(node.first_leaf_is(&Tok::DotDot), kind, "`..`")?;
        let list = required(node.after(&Tok::DotDot), kind, "its list")?;
        let list = self.expr(list)?;
        let span = dots.span().to(list.span());
        Ok(Expr::Spread(Box::new(list), span))
    }

    /// `{ x = e, y }` (a punned `y` is `y = y`), or an update
    /// `{ base | x = e }`.
    #[inline(never)]
    fn record(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Record;
        let base = match node.leaf(&Tok::Pipe) {
            Some(_) => {
                let base = required(node.after(&Tok::LBrace), kind, "its base")?;
                Some(Box::new(self.expr(base)?))
            }
            None => None,
        };
        // The fields follow the `|` of an update, or the `{`.
        let mut fields = Vec::new();
        let mut in_fields = base.is_none();
        for child in node.children() {
            match child {
                Element::Leaf(leaf) => match leaf.tok() {
                    Tok::Pipe => in_fields = true,
                    Tok::Lower(_) if in_fields => {
                        let field = name(leaf).expect("a name");
                        fields.push((field.clone(), Expr::Var(field)));
                    }
                    _ => {}
                },
                Element::Node(field) if in_fields => {
                    if field.kind() != NodeKind::RecordField {
                        return Err(Unsupported::Missing(kind, "a field"));
                    }
                    fields.push(self.record_field(field)?);
                }
                Element::Node(_) => {}
            }
        }
        Ok(Expr::Record {
            base,
            fields,
            span: whole(node)?,
        })
    }

    /// `x = e` in a record.
    fn record_field(&self, node: Node<'f>) -> Lowering<(Name, Expr)> {
        let kind = NodeKind::RecordField;
        let field = node.own_leaves().next().and_then(name);
        let field = required(field, kind, "its name")?;
        let value = required(node.after(&Tok::Equals), kind, "its value")?;
        Ok((field, self.expr(value)?))
    }

    /// `C { x = e }`: kept as [`Expr::CtorFields`] for the elaborator to
    /// read as construction by name or a record argument, as `C` is
    /// declared; `argument` says it is an application's argument. An
    /// update `C { r | x = e }` is never a construction: `C` applied to the
    /// updated record.
    #[inline(never)]
    fn ctor_fields(&self, node: Node<'f>, argument: bool) -> Lowering<Argument> {
        let kind = NodeKind::CtorFields;
        let ctor = node.own_leaves().next().and_then(name);
        let ctor = required(ctor, kind, "its constructor")?;
        let record = required(node.child(NodeKind::Record), kind, "its record")?;
        let mut record = self.record(record)?;
        let Expr::Record { base, fields, span } = &mut record else {
            unreachable!("a record lowers to a record")
        };
        if base.is_some() {
            return Ok(Argument::Two(Expr::Var(ctor), record));
        }
        let (fields, span) = (std::mem::take(fields), *span);
        Ok(Argument::One(Expr::CtorFields {
            span: ctor.span.to(span),
            ctor,
            fields,
            argument,
        }))
    }

    /// `f a b`: `App(App(f, a), b)`, one node however many arguments; a
    /// call `f()`, its argument a `Unit`. A call in brackets with arguments
    /// after it, `(f a) b`, keeps the brackets as [`Expr::Bracketed`], which
    /// finish the call.
    #[inline(never)]
    fn app(&self, node: Node<'f>) -> Lowering<Expr> {
        let mut parts = node.children();
        let head = required(parts.next(), NodeKind::App, "its function")?;
        if section_dot(head).is_some() {
            return self.method_section(node);
        }
        let mut expr = self.expr(head)?;
        // Its first token, which may be inside a child: `(f)()` is a call.
        let bracketed = match head {
            Element::Node(head) => head
                .token_range()
                .next()
                .is_some_and(|first| self.tree.tokens()[first].tok == Tok::LParen),
            Element::Leaf(_) => false,
        };
        let mut parts = parts.peekable();
        if bracketed && matches!(expr, Expr::App(..)) && parts.peek().is_some() {
            let span = whole_element(head)?;
            expr = Expr::Bracketed(Box::new(expr), span);
        }
        for arg in parts {
            expr = match self.argument(arg)? {
                Argument::One(arg) => Expr::App(Box::new(expr), Box::new(arg)),
                Argument::Two(first, second) => Expr::App(
                    Box::new(Expr::App(Box::new(expr), Box::new(first))),
                    Box::new(second),
                ),
            };
        }
        Ok(expr)
    }

    /// An application's argument: as anywhere else, except for a minus
    /// (`f -x`, an argument minus) and `C { … }`.
    pub(super) fn argument(&self, arg: Element<'f>) -> Lowering<Argument> {
        match arg {
            Element::Node(node) if node.kind() == NodeKind::Prefix => {
                if self.stack.exceeded() {
                    return Err(Unsupported::TooDeep);
                }
                self.prefix(node, true).map(Argument::One)
            }
            Element::Node(node) if node.kind() == NodeKind::CtorFields => {
                self.ctor_fields(node, true)
            }
            arg => self.expr(arg).map(Argument::One),
        }
    }

    /// `e.f`. One that starts with a field without a receiver, `.f.g`, is
    /// a method section.
    #[inline(never)]
    fn field_access(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::FieldAccess;
        let receiver = required(node.children().next(), kind, "its receiver")?;
        if section_dot(Element::Node(node)).is_some() {
            return self.method_section(node);
        }
        let field = match node.after(&Tok::Dot) {
            Some(Element::Leaf(leaf)) => name(leaf),
            _ => None,
        };
        let field = required(field, kind, "its field")?;
        Ok(Expr::Field(Box::new(self.expr(receiver)?), field))
    }

    /// `-x`, `!b` (and `¬p`, the same token), a negative numeral `-1`. As
    /// an application's `argument`, `f -x`, the minus is an argument minus.
    /// A negative numeral is one by its spacing wherever it is, as the
    /// parser reads it ([`argument_minus`]).
    #[inline(never)]
    fn prefix(&self, node: Node<'f>, argument: bool) -> Lowering<Expr> {
        let kind = NodeKind::Prefix;
        let op = required(node.own_leaves().next(), kind, "its operator")?;
        let operand = required(node.after(op.tok()), kind, "its operand")?;
        match op.tok() {
            Tok::Bang => Ok(prefix_op(true, op.span(), self.expr(operand)?)),
            Tok::Minus => {
                let tokens = self.tree.tokens();
                let numeral = matches!(operand, Element::Leaf(leaf)
                    if matches!(leaf.tok(), Tok::Num(_) | Tok::Float(_)))
                    && negative_numeral(tokens, op.index());
                let form = if numeral {
                    if argument_minus(tokens, op.index()) {
                        NegForm::Argument
                    } else {
                        NegForm::Operand
                    }
                } else if argument {
                    NegForm::Argument
                } else {
                    return Ok(prefix_op(false, op.span(), self.expr(operand)?));
                };
                let operand = self.expr(operand)?;
                let span = op.span().to(operand.span());
                Ok(Expr::Neg(Box::new(operand), span, form))
            }
            _ => Err(Unsupported::Missing(kind, "its operator")),
        }
    }

    /// `a + b`, `a && b`, `a = b` and the other binary operators; `a > b`
    /// is `b < a` and `a >= b` is `b <= a`, so goals and messages show `<`
    /// and `<=`.
    #[inline(never)]
    fn binary(&self, node: Node<'f>) -> Lowering<Expr> {
        let (lhs, op, rhs) = operation(node)?;
        let (op, flip) = match op.tok() {
            Tok::Plus => (BinOp::Add, false),
            Tok::Minus => (BinOp::Sub, false),
            Tok::Star => (BinOp::Mul, false),
            Tok::Slash => (BinOp::Div, false),
            Tok::Percent => (BinOp::Mod, false),
            Tok::PlusPlus => (BinOp::Append, false),
            Tok::AndAnd => (BinOp::And, false),
            Tok::OrOr => (BinOp::Or, false),
            Tok::Equals => (BinOp::Eq, false),
            Tok::NotEq => (BinOp::Ne, false),
            Tok::EqEq => (BinOp::EqEq, false),
            Tok::Lt => (BinOp::Lt, false),
            Tok::Le => (BinOp::Le, false),
            Tok::Gt => (BinOp::Lt, true),
            Tok::Ge => (BinOp::Le, true),
            _ => return Err(Unsupported::Missing(NodeKind::Binary, "its operator")),
        };
        Ok(binary(op, flip, self.expr(lhs)?, self.expr(rhs)?))
    }

    /// `a <= b < c …`: the links joined with `&&`, its middle operands
    /// bound once ([`chain`]).
    #[inline(never)]
    fn chain(&self, node: Node<'f>) -> Lowering<Expr> {
        let mut operands = Vec::new();
        let mut links = Vec::new();
        for (i, part) in node.children().enumerate() {
            if i % 2 == 0 {
                operands.push(self.expr(part)?);
                continue;
            }
            let link = match part {
                Element::Leaf(op) => match op.tok() {
                    Tok::Lt => Some((BinOp::Lt, false)),
                    Tok::Le => Some((BinOp::Le, false)),
                    Tok::Gt => Some((BinOp::Lt, true)),
                    Tok::Ge => Some((BinOp::Le, true)),
                    _ => None,
                },
                Element::Node(_) => None,
            };
            links.push(required(link, NodeKind::Chain, "an operator")?);
        }
        if operands.len() < 3 || operands.len() != links.len() + 1 {
            return Err(Unsupported::Missing(NodeKind::Chain, "an operand"));
        }
        Ok(chain(operands, &links))
    }

    /// `x in c`; `x !in c` is `!(x in c)`.
    #[inline(never)]
    fn membership(&self, node: Node<'f>) -> Lowering<Expr> {
        let (lhs, op, rhs) = operation(node)?;
        let negated = match op.tok() {
            Tok::KwIn => false,
            Tok::NotIn => true,
            _ => return Err(Unsupported::Missing(NodeKind::Membership, "`in`")),
        };
        let at = op.span();
        let member = Expr::Binary(
            BinOp::In(at),
            Box::new(self.expr(lhs)?),
            Box::new(self.expr(rhs)?),
        );
        Ok(if negated {
            prefix_op(true, at, member)
        } else {
            member
        })
    }

    /// `a ..< b`, `a ..= b`
    #[inline(never)]
    fn range(&self, node: Node<'f>) -> Lowering<Expr> {
        let (lhs, op, rhs) = operation(node)?;
        let op = match op.tok() {
            Tok::DotDotLt => BinOp::Range,
            Tok::DotDotEq => BinOp::RangeThrough,
            _ => return Err(Unsupported::Missing(NodeKind::Range, "its operator")),
        };
        Ok(Expr::Binary(
            op,
            Box::new(self.expr(lhs)?),
            Box::new(self.expr(rhs)?),
        ))
    }

    /// `x |> f` ([`piped`]).
    #[inline(never)]
    fn pipe(&self, node: Node<'f>) -> Lowering<Expr> {
        let (lhs, _, rhs) = operation(node)?;
        Ok(piped(self.expr(lhs)?, self.expr(rhs)?))
    }

    /// `A -> B`
    #[inline(never)]
    fn arrow(&self, node: Node<'f>) -> Lowering<Expr> {
        let (lhs, _, rhs) = operation(node)?;
        Ok(Expr::Arrow(
            Box::new(self.expr(lhs)?),
            Box::new(self.expr(rhs)?),
        ))
    }

    /// `p <-> q`: `Std.Iff p q`, the name at the operator.
    #[inline(never)]
    fn iff(&self, node: Node<'f>) -> Lowering<Expr> {
        let (lhs, op, rhs) = operation(node)?;
        let iff = Expr::Var(Name {
            text: "Std.Iff".into(),
            span: op.span(),
        });
        Ok(Expr::App(
            Box::new(Expr::App(Box::new(iff), Box::new(self.expr(lhs)?))),
            Box::new(self.expr(rhs)?),
        ))
    }

    /// `"a${x}b${y}c"`: the pieces joined with `++`, each interpolation
    /// `Std.Show.toText e` spanning its `${…}`, empty pieces left out, all
    /// of it wrapped to span the literal, quotes included.
    #[inline(never)]
    fn interpolated(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Interpolated;
        let mut items = Vec::new();
        // The text before the next interpolation, or after the last.
        let mut text: Option<(String, Span)> = None;
        let push_text = |items: &mut Vec<Expr>, text: Option<(String, Span)>| {
            if let Some((text, span)) = text
                && !text.is_empty()
            {
                items.push(Expr::Str(text, span));
            }
        };
        for child in node.children() {
            match child {
                Element::Leaf(leaf) => match leaf.tok() {
                    Tok::StrStart(piece) | Tok::StrMid(piece) | Tok::StrEnd(piece) => {
                        push_text(&mut items, text.take());
                        text = Some((piece.clone(), leaf.span()));
                    }
                    _ => return Err(Unsupported::Missing(kind, "a piece of text")),
                },
                Element::Node(interpolation) => {
                    push_text(&mut items, text.take());
                    items.push(self.interpolation(interpolation)?);
                }
            }
        }
        push_text(&mut items, text.take());
        let mut items = items.into_iter().rev();
        let mut expr = required(items.next(), kind, "a piece")?;
        for lhs in items {
            expr = Expr::Binary(BinOp::Append, Box::new(lhs), Box::new(expr));
        }
        Ok(Expr::Interpolated(Box::new(expr), whole(node)?))
    }

    /// `${x}` in a text: `Std.Show.toText x`.
    fn interpolation(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::Interpolation;
        if node.kind() != kind {
            return Err(Unsupported::Missing(
                NodeKind::Interpolated,
                "an interpolation",
            ));
        }
        let value = required(node.after(&Tok::InterpOpen), kind, "its expression")?;
        let to_text = Expr::Var(Name {
            text: "Std.Show.toText".into(),
            span: whole(node)?,
        });
        Ok(Expr::App(Box::new(to_text), Box::new(self.expr(value)?)))
    }
}

/// What an application's argument adds: one argument, or two (`f C { r |
/// x = e }` is `f C { r | x = e }`, `C` and then the updated record).
pub(super) enum Argument {
    One(Expr),
    Two(Expr, Expr),
}

impl Argument {
    /// `C { … }` on its own: the construction, or `C` applied to the
    /// updated record.
    pub(super) fn into_expr(self) -> Expr {
        match self {
            Argument::One(expr) => expr,
            Argument::Two(f, arg) => Expr::App(Box::new(f), Box::new(arg)),
        }
    }
}

/// From a node's first token to its last.
fn whole(node: Node<'_>) -> Lowering<Span> {
    required(node.span(), node.kind(), "tokens")
}

fn whole_element(element: Element<'_>) -> Lowering<Span> {
    match element {
        Element::Leaf(leaf) => Ok(leaf.span()),
        Element::Node(node) => whole(node),
    }
}

/// A node's parts other than its own tokens in `punctuation`: the
/// components of a tuple, the items of a list.
fn items<'f>(node: Node<'f>, punctuation: &[Tok]) -> Vec<Element<'f>> {
    node.children()
        .filter(|child| !matches!(child, Element::Leaf(leaf) if punctuation.contains(leaf.tok())))
        .collect()
}

/// A binary operation's three parts: its left operand, its operator and
/// its right operand.
fn operation(node: Node<'_>) -> Lowering<(Element<'_>, Leaf<'_>, Element<'_>)> {
    let mut parts = node.children();
    let lhs = required(parts.next(), node.kind(), "its left operand")?;
    let op = match parts.next() {
        Some(Element::Leaf(op)) => op,
        _ => return Err(Unsupported::Missing(node.kind(), "its operator")),
    };
    let rhs = required(parts.next(), node.kind(), "its right operand")?;
    if parts.next().is_some() {
        return Err(Unsupported::Missing(node.kind(), "one operator"));
    }
    Ok((lhs, op, rhs))
}

/// `Type 1`
fn universe(node: Node<'_>) -> Lowering<Expr> {
    let level = match node.after(&Tok::TypeU) {
        Some(Element::Leaf(leaf)) => match leaf.tok() {
            Tok::Num(n) => u32::try_from(n).ok(),
            _ => None,
        },
        _ => None,
    };
    let level = required(level, NodeKind::Universe, "its level")?;
    Ok(Expr::Type(level, whole(node)?))
}

/// `include "inputs/day04.txt"`
fn include(node: Node<'_>) -> Lowering<Expr> {
    let path = match node.after(&Tok::KwInclude) {
        Some(Element::Leaf(leaf)) => match leaf.tok() {
            Tok::Str(path) => Some(path.clone()),
            _ => None,
        },
        _ => None,
    };
    let path = required(path, NodeKind::Include, "its path")?;
    Ok(Expr::Include(path, whole(node)?))
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

/// Whether `expr` can be used twice with no cost and no effect: a name or
/// a literal. Anything else (a call, a field, which may be a method) is
/// computed once.
fn is_atom(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Var(_) | Expr::Num(..) | Expr::Float(..) | Expr::Str(..) | Expr::Char(..)
    )
}

/// `a <= b < c`: `a <= b && b < c`, where a middle operand `b` that is not
/// an atom is bound once, `let %chain := b`, and `a` (if it isn't an atom
/// either) is bound before it, so the operands run in the order written. A
/// later operand is bound inside the `&&`'s right side, so it only runs when
/// the earlier links hold. A `>` link is `<` turned round, as a single one
/// is, with the links in the order written. The result is one operand of a
/// longer `&&`.
pub(crate) fn chain(operands: Vec<Expr>, links: &[(BinOp, bool)]) -> Expr {
    struct Chain<'a> {
        links: &'a [(BinOp, bool)],
        spans: Vec<Span>,
        last: usize,
    }
    impl Chain<'_> {
        fn name(&self, i: usize) -> Name {
            Name {
                text: format!("{CHAIN}{}", self.spans[i].start),
                span: self.spans[i],
            }
        }

        /// The links from `i - 1` on, with `left` standing for operand
        /// `i - 1`.
        fn go(&self, i: usize, left: Expr, operands: &mut [Option<Expr>]) -> Expr {
            let operand = operands[i].take().expect("each operand is used once");
            let (op, flip) = self.links[i - 1];
            if i == self.last {
                return binary(op, flip, left, operand);
            }
            let (middle, bound) = if is_atom(&operand) {
                (operand, None)
            } else {
                (Expr::Var(self.name(i)), Some(operand))
            };
            let rest = self.go(i + 1, middle.clone(), operands);
            let body = Expr::Binary(
                BinOp::And,
                Box::new(binary(op, flip, left, middle)),
                Box::new(rest),
            );
            match bound {
                Some(value) => self.bind(i, value, body),
                None => body,
            }
        }

        fn bind(&self, i: usize, value: Expr, body: Expr) -> Expr {
            Expr::Let {
                name: self.name(i),
                ty: None,
                // The links it binds for, so a chain's outermost `let` spans
                // the chain as written.
                span: value.span().to(body.span()),
                value: Box::new(value),
                body: Box::new(body),
            }
        }
    }
    let chain = Chain {
        links,
        spans: operands.iter().map(Expr::span).collect(),
        last: operands.len() - 1,
    };
    let mut operands: Vec<Option<Expr>> = operands.into_iter().map(Some).collect();
    let first = operands[0].take().expect("a chain has operands");
    // A chain has three operands at least, so the second is a middle.
    if is_atom(&first) || operands[1].as_ref().is_some_and(is_atom) {
        return chain.go(1, first, &mut operands);
    }
    // Both ends of the first link perform, `a` first.
    let rest = chain.go(1, Expr::Var(chain.name(0)), &mut operands);
    chain.bind(0, first, rest)
}

/// `lhs op rhs`, or with `flip` `rhs op lhs`. Out of line, so the recursive
/// parsing functions keep small stack frames (nesting depth is bounded by
/// stack use).
#[inline(never)]
pub(crate) fn binary(op: BinOp, flip: bool, lhs: Expr, rhs: Expr) -> Expr {
    if flip {
        Expr::Binary(op, Box::new(rhs), Box::new(lhs))
    } else {
        Expr::Binary(op, Box::new(lhs), Box::new(rhs))
    }
}

/// `-operand`, or with `bang` `!operand`, which is `Std.Bool.not operand`.
#[inline(never)]
pub(crate) fn prefix_op(bang: bool, start: Span, operand: Expr) -> Expr {
    if bang {
        let not = Expr::Var(Name {
            text: "Std.Bool.not".into(),
            span: start,
        });
        return Expr::App(Box::new(not), Box::new(operand));
    }
    let span = start.to(operand.span());
    Expr::Neg(Box::new(operand), span, NegForm::Operand)
}

/// `lhs |> rhs`; when `rhs` is a method section, the call it stands for on
/// `lhs`: `xs |> .drop 1` is `xs.drop 1`, with no function in between.
#[inline(never)]
pub(crate) fn piped(lhs: Expr, mut rhs: Expr) -> Expr {
    let Expr::Lam(names, body, _) = &mut rhs else {
        return Expr::Pipe(Box::new(lhs), Box::new(rhs));
    };
    if names.len() != 1 || names[0].text != SECTION || !leads_with_section(body) {
        return Expr::Pipe(Box::new(lhs), Box::new(rhs));
    }
    let mut body = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
    fill_receiver(&mut body, lhs);
    body
}

#[cfg(test)]
mod tests {
    use super::super::oracle::{Report, compare};
    use crate::SourceMap;
    use crate::tree::NodeKind;

    fn report(text: &str) -> Report {
        let file = SourceMap::new().next_id();
        compare(file, text, crate::DEFAULT_STACK, true)
    }

    fn differences(report: &Report) -> Vec<String> {
        report
            .differences
            .iter()
            .map(|d| format!("{} at {}:\n{}", d.what, d.at, d.detail))
            .collect()
    }

    /// Each expression kind of lane L1, in the forms whose lowering depends
    /// on where they are or on spacing, comes out as the parser builds it,
    /// spans and hidden names included.
    #[test]
    fn expressions_lower_as_parsed() {
        let bodies = [
            "(x)",
            "(f a) b",
            "((f a)) b",
            "(f a).g b",
            "(f)() x",
            "(!x) y",
            "()",
            "f()",
            "x.f().g",
            "f () x",
            "f (x := 1) [y := 2] [decreasing := h]",
            "p.a.b",
            "a + b * c - d / e % f ++ g ++ h",
            "a = b && c != d || e == f && g < h",
            "a > b && a >= b && a ≤ b",
            "-x + -f y",
            "!b && ¬p",
            "-1.abs + f -1 -x !y",
            "f (-x) [-1]",
            "x ∈ xs && y ∉ ys && z !in zs",
            "0 ..< n ++ (1 ..= m)",
            "[(0 ..< n)]",
            "[(0 ..< n),]",
            "xs |> f a |> g",
            "Nat -> List Nat -> Type 1",
            "(x : Nat)",
            "p ↔ q && r",
            "a ≤ b < c",
            "f a ≤ g b < h c ≤ d",
            "a > f b >= c",
            "\"a${x}b${f y}\"",
            "\"${x}\"",
            "\"${x}${y}c\"",
            "(a, b, c)",
            "(a, (b, c), d,)",
            "{ x = 1, y }",
            "{ r | x = 1, y, }",
            "{}",
            "C { x = 1 }",
            "C { r | x = 1 }",
            "C { x = 1 }.x",
            "f C { x = 1 } D { r | y }",
            "[1, ..xs, 3]",
            "[]",
            "include \"x.txt\"",
            "omega",
        ];
        let text: String = bodies
            .iter()
            .enumerate()
            .map(|(i, body)| format!("test \"{i}\" := {body}\n"))
            .collect();
        let report = report(&text);
        assert_eq!(differences(&report), Vec::<String>::new());
        assert_eq!(report.unsupported, []);
        assert_eq!(report.lowered, vec![NodeKind::Test; bodies.len()]);
        assert_eq!(report.expressions.unsupported, []);
        assert_eq!(report.expressions.lowered, bodies.len());
    }

    /// An expression nested as deeply as the parser can parse it lowers
    /// within the same stack: the lowering takes fewer and smaller frames
    /// per level. One level deeper, the parser's `E-RESOURCE` fails the
    /// declaration, which the lowering gives as failed.
    #[test]
    fn deep_nesting_lowers_within_the_parsers_stack() {
        let shapes: [(&str, &str); 8] = [
            ("(", ")"),
            ("f (", ")"),
            ("-(1 + ", ")"),
            ("[(a, ", ")]"),
            ("(x => ", ")"),
            ("(if a then b else ", ")"),
            ("(∀ n => ", ")"),
            ("(.f ", ")"),
        ];
        let nested = |(open, close): (&str, &str), depth: usize| {
            format!(
                "test \"deep\" := {}0{}\n",
                open.repeat(depth),
                close.repeat(depth)
            )
        };
        let parses = |text: &str| {
            let file = SourceMap::new().next_id();
            crate::parse_module_recovering(file, text, crate::DEFAULT_STACK)
                .1
                .is_empty()
        };
        // A thread of its own, with room for the oracle's `Debug` printing,
        // which recurses without a limit.
        std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || {
                for shape in shapes {
                    // The deepest nesting that parses: debug builds' frames
                    // are much larger than release builds'.
                    let (mut deep, mut too_deep) = (1, 40_000);
                    assert!(parses(&nested(shape, deep)) && !parses(&nested(shape, too_deep)));
                    while too_deep - deep > 1 {
                        let middle = (deep + too_deep) / 2;
                        if parses(&nested(shape, middle)) {
                            deep = middle;
                        } else {
                            too_deep = middle;
                        }
                    }
                    for (depth, kind) in [(deep, NodeKind::Test), (too_deep, NodeKind::Error)] {
                        let report = report(&nested(shape, depth));
                        assert_eq!(differences(&report), Vec::<String>::new());
                        assert_eq!(report.unsupported, [], "{shape:?} at {depth}");
                        assert_eq!(report.lowered, [kind], "{shape:?} at {depth}");
                    }
                }
            })
            .expect("a thread")
            .join()
            .expect("no failure");
    }
}
