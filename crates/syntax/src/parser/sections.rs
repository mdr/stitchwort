//! Parsing operator sections `(== 'S')` and `(k +)` (D1193) and a bare
//! operator as a function, `(&&)` (D1195). What they mean, and the
//! method sections' widening (D1192), is in `lower/sections.rs`, which both
//! routes share.
//!
//! Like the declarations, each function here is `#[inline(never)]` or only
//! called from one that is, so the expression parser's frames stay small.

use super::{NO_PARTNER, Parser, Result};
use crate::Span;
use crate::ast::{BinOp, Expr, SECTION};
use crate::lexer::Tok;
use crate::lower::sections::{
    LEFT, RIGHT, is_operator, is_section_operator, operation, param, var,
};
use crate::tree::NodeKind;

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
        let section = self.operator_section_inner(right, open)?;
        self.node_at(open, NodeKind::OperatorSection);
        Ok(section)
    }

    fn operator_section_inner(&mut self, right: Option<usize>, open: Span) -> Result<Expr> {
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
                    )
                    .into());
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
                )
                .into());
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
                // `a && b && c`, grouping to the right.
                let mut starts = vec![self.mark()];
                let mut conjuncts = vec![self.cmp_expr()?];
                while self.eat(&Tok::AndAnd) {
                    starts.push(self.mark());
                    conjuncts.push(self.cmp_expr()?);
                }
                starts.pop();
                for start in starts {
                    self.node(start, NodeKind::Binary);
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
