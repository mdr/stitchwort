//! Sections without a method name (docs/proposals/anonymous-lambdas.md):
//! a method section that starts an expression takes the whole expression
//! (`(.id == id)` is `x => x.id == id`, D1192); operator sections
//! `(== 'S')` and `(k +)` (D1193); and a bare operator as a function,
//! `(&&)` (D1195). All of them are lambdas, parsed to the same tree as the
//! hand-written lambda.
//!
//! Like the declarations, each function here is `#[inline(never)]` or only
//! called from one that is, so the expression parser's frames stay small.

use super::{NO_PARTNER, Parser, Result, binary, prefix_op};
use crate::Span;
use crate::ast::{BinOp, Expr, Name, SECTION};
use crate::lexer::Tok;

/// The hidden parameters of a bare operator, `(&&)`.
const LEFT: &str = "%left";
const RIGHT: &str = "%right";

/// Whether `tok` is a binary operator that can be a section or a bare
/// function. `-` is one for the bare form only.
fn is_operator(tok: &Tok) -> bool {
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
fn is_section_operator(tok: &Tok) -> bool {
    is_operator(tok) && *tok != Tok::Minus
}

/// `lhs op rhs` for the operator token `tok` written at `at`.
fn operation(tok: &Tok, at: Span, lhs: Expr, rhs: Expr) -> Expr {
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

fn var(text: &str, span: Span) -> Expr {
    Expr::Var(Name {
        text: text.into(),
        span,
    })
}

fn param(text: &str, span: Span) -> Name {
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
pub(super) fn leads_with_section(e: &Expr) -> bool {
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
pub(super) fn fill_receiver(e: &mut Expr, value: Expr) {
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
pub(super) fn widen(expr: &mut Expr) {
    if expr.section_name().is_some() {
        return;
    }
    let mut cur: &mut Expr = expr;
    while cur.section_name().is_none() {
        match leftmost_child_mut(cur) {
            Some(child) => cur = child,
            None => return,
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
}

impl Parser<'_> {
    /// Whether the `(` here opens an operator section or a bare operator:
    /// `(&&)`, `(== 'S')` or `(k +)`.
    pub(super) fn operator_section_ahead(&self) -> bool {
        if self.peek() != Some(&Tok::LParen) {
            return false;
        }
        let bare =
            self.peek_at(1).is_some_and(is_operator) && self.peek_at(2) == Some(&Tok::RParen);
        bare || self.peek_at(1).is_some_and(is_section_operator) || self.right_operator().is_some()
    }

    /// For a `(` opening a right section, the index of its operator: the
    /// token before the closing bracket.
    fn right_operator(&self) -> Option<usize> {
        let close = *self.matching.get(self.pos)?;
        let at = (close as usize).checked_sub(1)?;
        (close != NO_PARTNER
            && at > self.pos
            && self
                .tokens
                .get(at)
                .is_some_and(|t| is_section_operator(&t.tok)))
        .then_some(at)
    }

    /// `(&&)`, `(== 'S')` or `(k +)`, at the `(`.
    #[inline(never)]
    pub(super) fn operator_section(&mut self) -> Result<Expr> {
        let right = self.right_operator();
        let open = self.bump().span;
        let first = self.peek().cloned().unwrap_or(Tok::RParen);
        // `(&&)`: the operator as a function of two arguments.
        if is_operator(&first) && self.peek_at(1) == Some(&Tok::RParen) {
            let at = self.bump().span;
            let end = self.bump().span;
            let body = operation(&first, at, var(LEFT, at), var(RIGHT, at));
            let names = vec![param(LEFT, at), param(RIGHT, at)];
            return Ok(Expr::Lam(names, Box::new(body), open.to(end)));
        }
        // `(== 'S')`: the left operand is the argument.
        if is_section_operator(&first) {
            let at = self.bump().span;
            let rhs = self.section_operand(&first)?;
            if self.peek() != Some(&Tok::RParen) {
                return Err(self
                    .unexpected("`)` after the operand of a section")
                    .with_note(
                        "a section takes one operand, the one that binds tighter than its \
                     operator: bracket a longer one, as in `(+ (1 + 2))`",
                    ));
            }
            let end = self.bump().span;
            let body = operation(&first, at, var(SECTION, at), rhs);
            return Ok(Expr::Lam(
                vec![param(SECTION, at)],
                Box::new(body),
                open.to(end),
            ));
        }
        // `(k +)`: the right operand is the argument.
        let operator = right.expect("checked by operator_section_ahead");
        let tok = self.tokens[operator].tok.clone();
        let lhs = match tok {
            Tok::Plus => self.mul_expr()?,
            Tok::Star | Tok::Slash | Tok::Percent => self.unary()?,
            Tok::PlusPlus => self.add_expr()?,
            Tok::AndAnd | Tok::OrOr | Tok::Iff => self.cmp_expr()?,
            _ => self.append_expr()?,
        };
        let at = self.tokens[operator].span;
        if self.pos != operator {
            return Err(self
                .unexpected("`)` after the operator of a section")
                .with_note(
                    "a section's operand must bind tighter than its operator: bracket the \
                     operand, as in `((a + b) *)`",
                ));
        }
        self.bump();
        let end = self.expect(Tok::RParen, "`)`")?.span;
        let body = operation(&tok, at, lhs, var(SECTION, at));
        Ok(Expr::Lam(
            vec![param(SECTION, at)],
            Box::new(body),
            open.to(end),
        ))
    }

    /// The right operand of a left section with operator `tok`: what binds
    /// tighter than the operator, so `(+ 1 + 2)` needs brackets.
    fn section_operand(&mut self, tok: &Tok) -> Result<Expr> {
        match tok {
            Tok::Plus => self.mul_expr(),
            Tok::Star | Tok::Slash | Tok::Percent => self.unary(),
            Tok::AndAnd => self.cmp_expr(),
            Tok::OrOr => {
                let mut conjuncts = vec![self.cmp_expr()?];
                while self.eat(&Tok::AndAnd) {
                    conjuncts.push(self.cmp_expr()?);
                }
                Ok(conjuncts
                    .into_iter()
                    .rev()
                    .reduce(|rhs, lhs| Expr::Binary(BinOp::And, Box::new(lhs), Box::new(rhs)))
                    .expect("never empty"))
            }
            Tok::Iff => {
                let mut rhs = self.cmp_expr()?;
                if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
                    self.logic_chain(&mut rhs)?;
                }
                Ok(rhs)
            }
            _ => self.append_expr(),
        }
    }
}
