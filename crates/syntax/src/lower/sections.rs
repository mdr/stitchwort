//! Sections: method sections `.f a` (the function `x => x.f a`), which
//! take the whole expression they start (`.id == id` is `x => x.id == id`,
//! D1192); operator sections `(== 'S')` and `(k +)` (D1193); and a bare
//! operator as a function, `(&&)` (D1195) (docs/proposals/anonymous-lambdas.md).
//! All of them are lambdas, the same tree as the hand-written lambda. The
//! parser still builds them itself and shares the expansions here
//! ([`operation`], [`widen`], [`fill_receiver`]).

use crate::Span;
use crate::ast::{BinOp, Expr, Name, SECTION};
use crate::lexer::Tok;
use crate::tree::{Element, Leaf, Node, NodeKind};

use super::access::required;
use super::decls::name;
use super::exprs::{binary, prefix_op};
use super::{Lower, Lowering, Unsupported};

/// The hidden parameters of a bare operator, `(&&)`.
pub(crate) const LEFT: &str = "%left";
pub(crate) const RIGHT: &str = "%right";

/// Whether `tok` is a binary operator that can be a section or a bare
/// function. `-` is one for the bare form only.
pub(crate) fn is_operator(tok: &Tok) -> bool {
    matches!(
        tok,
        Tok::Plus
            | Tok::Minus
            | Tok::Star
            | Tok::Slash
            | Tok::Percent
            | Tok::PlusPlus
            | Tok::Equals
            | Tok::NotEq
            | Tok::EqEq
            | Tok::Lt
            | Tok::Le
            | Tok::Gt
            | Tok::Ge
            | Tok::AndAnd
            | Tok::OrOr
            | Tok::KwIn
            | Tok::NotIn
            | Tok::Iff
    )
}

/// Whether `tok` can be the operator of a section: `-` can't, so `(- 1)` is
/// the number.
pub(crate) fn is_section_operator(tok: &Tok) -> bool {
    is_operator(tok) && *tok != Tok::Minus
}

/// `lhs op rhs` for the operator token `tok` written at `at`.
pub(crate) fn operation(tok: &Tok, at: Span, lhs: Expr, rhs: Expr) -> Expr {
    let plain = |op, lhs, rhs| Expr::Binary(op, Box::new(lhs), Box::new(rhs));
    match tok {
        Tok::Plus => plain(BinOp::Add, lhs, rhs),
        Tok::Minus => plain(BinOp::Sub, lhs, rhs),
        Tok::Star => plain(BinOp::Mul, lhs, rhs),
        Tok::Slash => plain(BinOp::Div, lhs, rhs),
        Tok::Percent => plain(BinOp::Mod, lhs, rhs),
        Tok::PlusPlus => plain(BinOp::Append, lhs, rhs),
        Tok::Equals => plain(BinOp::Eq, lhs, rhs),
        Tok::NotEq => plain(BinOp::Ne, lhs, rhs),
        Tok::EqEq => plain(BinOp::EqEq, lhs, rhs),
        Tok::Lt => plain(BinOp::Lt, lhs, rhs),
        Tok::Le => plain(BinOp::Le, lhs, rhs),
        Tok::Gt => binary(BinOp::Lt, true, lhs, rhs),
        Tok::Ge => binary(BinOp::Le, true, lhs, rhs),
        Tok::AndAnd => plain(BinOp::And, lhs, rhs),
        Tok::OrOr => plain(BinOp::Or, lhs, rhs),
        Tok::KwIn => plain(BinOp::In(at), lhs, rhs),
        Tok::NotIn => prefix_op(true, at, plain(BinOp::In(at), lhs, rhs)),
        Tok::Iff => {
            let iff = var("Std.Iff", at);
            Expr::App(
                Box::new(Expr::App(Box::new(iff), Box::new(lhs))),
                Box::new(rhs),
            )
        }
        _ => unreachable!("not an operator"),
    }
}

pub(crate) fn var(text: &str, span: Span) -> Expr {
    Expr::Var(Name {
        text: text.into(),
        span,
    })
}

pub(crate) fn param(text: &str, span: Span) -> Name {
    Name {
        text: text.into(),
        span,
    }
}

fn is_section_var(e: &Expr) -> bool {
    matches!(e, Expr::Var(v) if v.text == SECTION)
}

/// One step left from an operation to its first operand: the part of an
/// expression that a leading section stands in for.
fn leftmost_child(e: &Expr) -> Option<&Expr> {
    match e {
        Expr::Binary(_, lhs, rhs) => Some(if lhs.span().start <= rhs.span().start {
            lhs
        } else {
            rhs
        }),
        Expr::Pipe(lhs, _) | Expr::Field(lhs, _) => Some(lhs),
        Expr::App(f, arg) => match &**f {
            Expr::Var(n) if n.text == "Std.Bool.not" => Some(arg),
            Expr::App(g, lhs) if matches!(&**g, Expr::Var(n) if n.text == "Std.Iff") => Some(lhs),
            _ => Some(f),
        },
        _ => None,
    }
}

fn leftmost_child_mut(e: &mut Expr) -> Option<&mut Expr> {
    // Which operand is first: 0 the function, 1 the argument, 2 the
    // left operand of `Iff`.
    let which = match e {
        Expr::App(f, _) => match &**f {
            Expr::Var(n) if n.text == "Std.Bool.not" => 1,
            Expr::App(g, _) if matches!(&**g, Expr::Var(n) if n.text == "Std.Iff") => 2,
            _ => 0,
        },
        _ => 0,
    };
    match e {
        Expr::Binary(_, lhs, rhs) => Some(if lhs.span().start <= rhs.span().start {
            lhs
        } else {
            rhs
        }),
        Expr::Pipe(lhs, _) | Expr::Field(lhs, _) => Some(lhs),
        Expr::App(f, arg) => match which {
            1 => Some(arg),
            2 => match &mut **f {
                Expr::App(_, lhs) => Some(lhs),
                _ => unreachable!(),
            },
            _ => Some(f),
        },
        _ => None,
    }
}

/// Whether `e` is, at its left edge, a field access on the section's
/// parameter, as `x.id == id` is with `x` the parameter.
pub(crate) fn leads_with_section(e: &Expr) -> bool {
    let mut cur = e;
    loop {
        if matches!(cur, Expr::Field(r, _) if is_section_var(r)) {
            return true;
        }
        match leftmost_child(cur) {
            Some(child) => cur = child,
            None => return false,
        }
    }
}

/// Puts `value` where the section's parameter is, in an expression that
/// `leads_with_section`.
pub(crate) fn fill_receiver(e: &mut Expr, value: Expr) {
    let mut cur = e;
    loop {
        if matches!(cur, Expr::Field(r, _) if is_section_var(r)) {
            let Expr::Field(r, _) = cur else {
                unreachable!()
            };
            **r = value;
            return;
        }
        match leftmost_child_mut(cur) {
            Some(child) => cur = child,
            None => unreachable!("checked by leads_with_section"),
        }
    }
}

/// An expression that started with a method section. If operators follow
/// the section, it takes them all, and the whole expression is the function
/// (D1192): `.id == id`, parsed as `(.id) == id`, becomes `x => x.id == id`.
/// Returns whether it did: not when `expr` is the section already.
pub(crate) fn widen(expr: &mut Expr) -> bool {
    if expr.section_name().is_some() {
        return false;
    }
    let mut cur: &mut Expr = expr;
    while cur.section_name().is_none() {
        match leftmost_child_mut(cur) {
            Some(child) => cur = child,
            None => return false,
        }
    }
    let Expr::Lam(names, body, span) = cur else {
        unreachable!("a section is a lambda")
    };
    let (name, start) = (names[0].clone(), *span);
    let inner = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
    *cur = inner;
    let whole = std::mem::replace(expr, Expr::Hole(Span::NOWHERE));
    let span = start.to(whole.span());
    *expr = Expr::Lam(vec![name], Box::new(whole), span);
    true
}

/// The `.` a method section starts with, if `element` is one or is applied
/// to arguments: a field access with no receiver, `.f`, or one on such an
/// access or call, `.f.g`, `.f()`, `.f a`.
pub(super) fn section_dot(element: Element<'_>) -> Option<Leaf<'_>> {
    let Element::Node(node) = element else {
        return None;
    };
    match node.kind() {
        NodeKind::FieldAccess => match node.children().next()? {
            Element::Leaf(dot) if *dot.tok() == Tok::Dot => Some(dot),
            receiver => section_dot(receiver),
        },
        NodeKind::App => section_dot(node.children().next()?),
        _ => None,
    }
}

impl<'f> Lower<'f> {
    /// A method section, `.f`, `.f.g()` or `.f a b`: the function
    /// `%section => %section.f a b`, its parameter named at the `.`. The
    /// arguments of a section at the head of an application are its own,
    /// except a `C { … }`, which is applied to the section.
    #[inline(never)]
    pub(super) fn method_section(&self, node: Node<'f>) -> Lowering<Expr> {
        let dot = required(section_dot(Element::Node(node)), node.kind(), "its `.`")?;
        if node.kind() == NodeKind::FieldAccess {
            let body = self.section_body(node, dot)?;
            let span = dot.span().to(body.span());
            let param = param(SECTION, dot.span());
            return Ok(Expr::Lam(vec![param], Box::new(body), span));
        }
        let mut parts = node.children();
        let head = required(parts.next(), NodeKind::App, "its function")?;
        let Element::Node(head) = head else {
            return Err(Unsupported::Missing(NodeKind::Section, "its `.`"));
        };
        let mut expr = self.method_section(head)?;
        for arg in parts {
            self.section_apply(&mut expr, arg)?;
        }
        Ok(expr)
    }

    /// A method section `expr` applied to `arg`: inside its lambda, except
    /// a `C { … }`, which is applied to the section. Out of line, for the
    /// same reason as [`Self::apply`].
    #[inline(never)]
    fn section_apply(&self, expr: &mut Expr, arg: Element<'f>) -> Lowering<()> {
        if matches!(arg, Element::Node(n) if n.kind() == NodeKind::CtorFields) {
            return self.apply(expr, arg);
        }
        let arg = self.argument(arg)?;
        if let Expr::Lam(_, body, span) = expr {
            *span = span.to(arg.span());
            let f = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
            **body = Expr::App(Box::new(f), Box::new(arg));
        } else {
            let f = std::mem::replace(expr, Expr::Hole(Span::NOWHERE));
            *expr = Expr::App(Box::new(f), Box::new(arg));
        }
        Ok(())
    }

    /// A method section's body, before its arguments: `%section.f`, with
    /// the fields and calls `()` after it.
    fn section_body(&self, node: Node<'f>, dot: Leaf<'f>) -> Lowering<Expr> {
        let mut parts = node.children();
        let first = required(parts.next(), node.kind(), "its first part")?;
        match node.kind() {
            NodeKind::FieldAccess => {
                let receiver = match first {
                    Element::Leaf(leaf) if *leaf.tok() == Tok::Dot => var(SECTION, dot.span()),
                    Element::Node(receiver) => self.section_body(receiver, dot)?,
                    Element::Leaf(_) => return Err(Unsupported::Missing(node.kind(), "a `.`")),
                };
                let field = match node.children().last() {
                    Some(Element::Leaf(leaf)) => name(leaf),
                    _ => None,
                };
                let field = required(field, node.kind(), "its field")?;
                Ok(Expr::Field(Box::new(receiver), field))
            }
            // `.f()`, which is one atom.
            NodeKind::App => {
                let Element::Node(head) = first else {
                    return Err(Unsupported::Missing(node.kind(), "a `.`"));
                };
                let mut expr = self.section_body(head, dot)?;
                for arg in parts {
                    expr = Expr::App(Box::new(expr), Box::new(self.expr(arg)?));
                }
                Ok(expr)
            }
            kind => Err(Unsupported::Kind(kind)),
        }
    }

    /// A method section: one on its own or with its arguments, or one that
    /// starts an expression, which then takes the whole expression
    /// (D1192): `.id == id` is `%section => %section.id == id`.
    #[inline(never)]
    pub(super) fn section(&self, node: Node<'f>) -> Lowering<Expr> {
        let mut parts = node.children();
        let inner = required(parts.next(), NodeKind::Section, "its expression")?;
        if parts.next().is_some() {
            return Err(Unsupported::Missing(NodeKind::Section, "one expression"));
        }
        let mut expr = self.expr(inner)?;
        widen(&mut expr);
        Ok(expr)
    }

    /// `(&&)`, `(== 'S')` or `(k +)`: a lambda over the operation.
    #[inline(never)]
    pub(super) fn operator_section(&self, node: Node<'f>) -> Lowering<Expr> {
        let kind = NodeKind::OperatorSection;
        let parts: Vec<Element<'f>> = node.children().collect();
        let open = match parts.first() {
            Some(Element::Leaf(leaf)) if *leaf.tok() == Tok::LParen => leaf.span(),
            _ => return Err(Unsupported::Missing(kind, "`(`")),
        };
        let end = match parts.last() {
            Some(Element::Leaf(leaf)) if *leaf.tok() == Tok::RParen => leaf.span(),
            _ => return Err(Unsupported::Missing(kind, "`)`")),
        };
        let span = open.to(end);
        let operator = |i: usize| match parts.get(i) {
            Some(Element::Leaf(leaf)) if is_operator(leaf.tok()) => Some(*leaf),
            _ => None,
        };
        match (parts.len(), operator(1)) {
            // `(&&)`: the operator as a function of two arguments.
            (3, Some(op)) => {
                let at = op.span();
                let body = operation(op.tok(), at, var(LEFT, at), var(RIGHT, at));
                let names = vec![param(LEFT, at), param(RIGHT, at)];
                Ok(Expr::Lam(names, Box::new(body), span))
            }
            // `(== 'S')`: the left operand is the argument.
            (4, Some(op)) => {
                let at = op.span();
                let rhs = self.expr(parts[2])?;
                let body = operation(op.tok(), at, var(SECTION, at), rhs);
                Ok(Expr::Lam(vec![param(SECTION, at)], Box::new(body), span))
            }
            // `(k +)`: the right operand is the argument.
            (4, None) => {
                let op = required(operator(2), kind, "its operator")?;
                let at = op.span();
                let lhs = self.expr(parts[1])?;
                let body = operation(op.tok(), at, lhs, var(SECTION, at));
                Ok(Expr::Lam(vec![param(SECTION, at)], Box::new(body), span))
            }
            _ => Err(Unsupported::Missing(kind, "an operator")),
        }
    }
}
