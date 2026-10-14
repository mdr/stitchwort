//! Recursive-descent parser for the surface syntax. See `docs/syntax.md`.
//!
//! Layout rule (interim): a declaration starts at column 0, and every following
//! line that is indented belongs to it. A line containing only `export` attaches
//! to the declaration after it.

use crate::ast::{BinOp, Binder, CtorDecl, Decl, Expr, Module, Name, Pattern};
use crate::lexer::{Tok, Token, lex};
use crate::{Diagnostic, FileId, Span};

type Result<T> = std::result::Result<T, Diagnostic>;

pub fn parse_module(file: FileId, text: &str) -> std::result::Result<Module, Vec<Diagnostic>> {
    let tokens = lex(file, text).map_err(|d| vec![d])?;
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    for group in split_decls(&tokens).map_err(|d| vec![d])? {
        let mut parser = Parser::new(group, file, text.len());
        match parser
            .decl()
            .and_then(|decl| parser.finish().map(|()| decl))
        {
            Ok(decl) => decls.push(decl),
            Err(diagnostic) => errors.push(diagnostic),
        }
    }
    if errors.is_empty() {
        Ok(Module { decls })
    } else {
        Err(errors)
    }
}

pub fn parse_expression(file: FileId, text: &str) -> Result<Expr> {
    let tokens = lex(file, text)?;
    let mut parser = Parser::new(&tokens, file, text.len());
    let expr = parser.expr()?;
    parser.finish()?;
    Ok(expr)
}

fn split_decls(tokens: &[Token]) -> Result<Vec<&[Token]>> {
    if let Some(first) = tokens.first()
        && first.column != 0
    {
        return Err(error(
            first.span,
            "declarations must start at the beginning of a line",
        ));
    }
    let mut starts: Vec<usize> = (0..tokens.len())
        .filter(|&i| tokens[i].column == 0)
        .collect();
    // A line holding only `export` belongs to the declaration that follows it.
    starts.retain(|&i| i == 0 || !(tokens[i - 1].tok == Tok::KwExport && is_alone(tokens, i - 1)));
    let mut groups = Vec::new();
    for (n, &start) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(tokens.len());
        groups.push(&tokens[start..end]);
    }
    Ok(groups)
}

/// Whether the token at `i` starts a group and is the only token in it.
fn is_alone(tokens: &[Token], i: usize) -> bool {
    tokens[i].column == 0 && tokens.get(i + 1).is_some_and(|next| next.column == 0)
}

struct Parser<'t> {
    tokens: &'t [Token],
    pos: usize,
    file: FileId,
    eof: u32,
}

impl<'t> Parser<'t> {
    fn new(tokens: &'t [Token], file: FileId, text_len: usize) -> Self {
        let eof = tokens.last().map_or(text_len as u32, |t| t.span.end);
        Parser {
            tokens,
            pos: 0,
            file,
            eof,
        }
    }

    fn peek(&self) -> Option<&'t Tok> {
        self.tokens.get(self.pos).map(|t| &t.tok)
    }

    fn peek_at(&self, offset: usize) -> Option<&'t Tok> {
        self.tokens.get(self.pos + offset).map(|t| &t.tok)
    }

    fn here(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map_or(Span::point(self.file, self.eof), |t| t.span)
    }

    fn prev_span(&self) -> Span {
        self.tokens[self.pos - 1].span
    }

    fn bump(&mut self) -> &'t Token {
        let token = &self.tokens[self.pos];
        self.pos += 1;
        token
    }

    fn eat(&mut self, tok: &Tok) -> bool {
        if self.peek() == Some(tok) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, tok: Tok, what: &str) -> Result<&'t Token> {
        if self.peek() == Some(&tok) {
            Ok(self.bump())
        } else {
            Err(self.unexpected(what))
        }
    }

    fn unexpected(&self, expected: &str) -> Diagnostic {
        let found = match self.tokens.get(self.pos) {
            Some(token) => format!("found {}", describe(&token.tok)),
            None => "reached the end of the declaration".to_string(),
        };
        error(self.here(), format!("expected {expected}, but {found}"))
    }

    fn finish(&self) -> Result<()> {
        if self.pos < self.tokens.len() {
            Err(self.unexpected("the end of the declaration"))
        } else {
            Ok(())
        }
    }

    fn lower(&mut self, what: &str) -> Result<Name> {
        match self.peek() {
            Some(Tok::Lower(text)) => {
                let span = self.bump().span;
                Ok(Name {
                    text: text.clone(),
                    span,
                })
            }
            _ => Err(self.unexpected(what)),
        }
    }

    fn def_name(&mut self) -> Result<Name> {
        match self.peek() {
            Some(Tok::Upper(_)) => self.upper("a name"),
            _ => self.lower("a name"),
        }
    }

    fn upper(&mut self, what: &str) -> Result<Name> {
        match self.peek() {
            Some(Tok::Upper(text)) => {
                let span = self.bump().span;
                Ok(Name {
                    text: text.clone(),
                    span,
                })
            }
            _ => Err(self.unexpected(what)),
        }
    }

    // Declarations

    fn decl(&mut self) -> Result<Decl> {
        let start = self.here();
        match self.peek() {
            Some(Tok::KwType) => self.data(),
            Some(Tok::KwTest) => {
                self.bump();
                let name = match self.peek() {
                    Some(Tok::Str(text)) => {
                        self.bump();
                        text.clone()
                    }
                    _ => return Err(self.unexpected("the test's name, in quotes")),
                };
                self.expect(Tok::Equals, "`=`")?;
                let expr = self.expr()?;
                Ok(Decl::Test {
                    span: start.to(expr.span()),
                    name,
                    expr,
                })
            }
            Some(Tok::KwExport) => {
                self.bump();
                let theorem = self.eat(&Tok::KwTheorem);
                self.signature(start, theorem, true)
            }
            Some(Tok::KwTheorem) => {
                self.bump();
                self.signature(start, true, false)
            }
            // Definitions may be named in either case: `length`, or `Not` for a
            // function returning a type.
            Some(Tok::Lower(_) | Tok::Upper(_)) if self.peek_at(1) == Some(&Tok::Colon) => {
                self.signature(start, false, false)
            }
            Some(Tok::Lower(_) | Tok::Upper(_)) => self.equation(),
            _ => Err(self.unexpected("a declaration")),
        }
    }

    fn signature(&mut self, start: Span, theorem: bool, export: bool) -> Result<Decl> {
        let name = self.def_name()?;
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.expr()?;
        Ok(Decl::Signature {
            name,
            span: start.to(ty.span()),
            ty,
            theorem,
            export,
        })
    }

    fn equation(&mut self) -> Result<Decl> {
        let name = self.def_name()?;
        let mut patterns = Vec::new();
        while self.peek().is_some() && self.peek() != Some(&Tok::Equals) {
            patterns.push(self.pattern()?);
        }
        let absurd = patterns.iter().any(|p| matches!(p, Pattern::Absurd(_)));
        if absurd && self.peek().is_none() {
            // `f ()` needs no right-hand side.
            return Ok(Decl::Equation {
                span: name.span.to(self.prev_span()),
                name,
                patterns,
                rhs: None,
            });
        }
        self.expect(Tok::Equals, "`=`")?;
        let rhs = self.expr()?;
        Ok(Decl::Equation {
            span: name.span.to(rhs.span()),
            name,
            patterns,
            rhs: Some(rhs),
        })
    }

    fn pattern(&mut self) -> Result<Pattern> {
        let span = self.here();
        match self.peek() {
            Some(Tok::Lower(_)) => Ok(Pattern::Var(self.lower("a pattern")?)),
            Some(Tok::Underscore) => {
                self.bump();
                Ok(Pattern::Wildcard(span))
            }
            Some(Tok::Num(n)) => {
                self.bump();
                Ok(Pattern::Num(*n, span))
            }
            Some(Tok::Upper(_)) => {
                let name = self.upper("a constructor")?;
                Ok(Pattern::Ctor(name, Vec::new(), span))
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                let end = self.bump().span;
                Ok(Pattern::Absurd(span.to(end)))
            }
            Some(Tok::LParen) => {
                self.bump();
                let pattern = if let Some(Tok::Upper(_)) = self.peek() {
                    let name = self.upper("a constructor")?;
                    let mut args = Vec::new();
                    while self.peek() != Some(&Tok::RParen) {
                        args.push(self.pattern()?);
                    }
                    let end = self.expect(Tok::RParen, "`)`")?.span;
                    Pattern::Ctor(name, args, span.to(end))
                } else {
                    let inner = self.pattern()?;
                    self.expect(Tok::RParen, "`)`")?;
                    inner
                };
                Ok(pattern)
            }
            _ => Err(self.unexpected("a pattern or `=`")),
        }
    }

    fn data(&mut self) -> Result<Decl> {
        let start = self.bump().span;
        let name = self.upper("a data type name (starting with an uppercase letter)")?;
        let mut params = Vec::new();
        while self.peek() == Some(&Tok::LParen) {
            params.push(self.binder()?);
        }
        let sort = if self.eat(&Tok::Colon) {
            Some(self.app()?)
        } else {
            None
        };
        let mut ctors = Vec::new();
        if self.eat(&Tok::Equals) {
            while self.eat(&Tok::Pipe) {
                let name = self.upper("a constructor name (starting with an uppercase letter)")?;
                let mut fields = Vec::new();
                while self.peek() == Some(&Tok::LParen) {
                    fields.push(self.binder()?);
                }
                ctors.push(CtorDecl { name, fields });
            }
            if ctors.is_empty() {
                return Err(self.unexpected("`|` and a constructor"));
            }
        }
        Ok(Decl::Data {
            span: start.to(self.prev_span()),
            name,
            params,
            sort,
            ctors,
        })
    }

    fn binder(&mut self) -> Result<Binder> {
        self.expect(Tok::LParen, "`(`")?;
        let mut names = vec![self.lower("a name")?];
        while let Some(Tok::Lower(_)) = self.peek() {
            names.push(self.lower("a name")?);
        }
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.expr()?;
        self.expect(Tok::RParen, "`)`")?;
        Ok(Binder { names, ty })
    }

    // Expressions, loosest-binding first

    fn expr(&mut self) -> Result<Expr> {
        let start = self.here();
        if self.eat(&Tok::Backslash) {
            let mut names = Vec::new();
            loop {
                match self.peek() {
                    Some(Tok::Lower(_)) => names.push(self.lower("a name")?),
                    Some(Tok::Underscore) => {
                        let span = self.bump().span;
                        names.push(Name {
                            text: "_".to_string(),
                            span,
                        });
                    }
                    _ => break,
                }
            }
            if names.is_empty() {
                return Err(self.unexpected("a parameter name"));
            }
            self.expect(Tok::Arrow, "`->`")?;
            let body = self.expr()?;
            let span = start.to(body.span());
            return Ok(Expr::Lam(names, Box::new(body), span));
        }
        if self.eat(&Tok::KwIf) {
            // `if h : P then …` binds a proof; `if c then …` tests a `Bool`.
            let binder = if matches!(self.peek(), Some(Tok::Lower(_)))
                && self.peek_at(1) == Some(&Tok::Colon)
            {
                let name = self.lower("a name")?;
                self.bump();
                Some(name)
            } else {
                None
            };
            let cond = self.expr()?;
            self.expect(Tok::KwThen, "`then`")?;
            let then = self.expr()?;
            self.expect(Tok::KwElse, "`else`")?;
            let otherwise = self.expr()?;
            let span = start.to(otherwise.span());
            return Ok(Expr::If {
                binder,
                cond: Box::new(cond),
                then: Box::new(then),
                otherwise: Box::new(otherwise),
                span,
            });
        }
        let implicit = self.is_implicit_binder();
        if implicit || self.is_pi_binder() {
            let (binder, auto) = if implicit {
                self.implicit_binder()?
            } else {
                (self.binder()?, false)
            };
            self.expect(Tok::Arrow, "`->`")?;
            let cod = self.expr()?;
            let span = start.to(cod.span());
            return Ok(Expr::Pi {
                names: binder.names,
                implicit,
                auto,
                dom: Box::new(binder.ty),
                cod: Box::new(cod),
                span,
            });
        }
        let lhs = self.cmp_expr()?;
        if self.eat(&Tok::Arrow) {
            let rhs = self.expr()?;
            return Ok(Expr::Arrow(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    /// `[ name+ :` starts an implicit binder; `[a, b]` is a list literal.
    fn is_implicit_binder(&self) -> bool {
        if self.peek() != Some(&Tok::LBracket) {
            return false;
        }
        let mut i = self.pos + 1;
        while let Some(Token {
            tok: Tok::Lower(_), ..
        }) = self.tokens.get(i)
        {
            i += 1;
        }
        i > self.pos + 1 && self.tokens.get(i).map(|t| &t.tok) == Some(&Tok::Colon)
    }

    /// `[x y : A]`, or `[auto x : P]`. Returns whether it's `auto`.
    fn implicit_binder(&mut self) -> Result<(Binder, bool)> {
        self.expect(Tok::LBracket, "`[`")?;
        let mut names = vec![self.lower("a name")?];
        while let Some(Tok::Lower(_)) = self.peek() {
            names.push(self.lower("a name")?);
        }
        // `auto` is only special as the first word of a binder with names after it.
        let auto = names.len() > 1 && names[0].text == "auto";
        if auto {
            names.remove(0);
        }
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.expr()?;
        self.expect(Tok::RBracket, "`]`")?;
        Ok((Binder { names, ty }, auto))
    }

    /// `( name+ : ... ) ->`
    fn is_pi_binder(&self) -> bool {
        if self.peek() != Some(&Tok::LParen) {
            return false;
        }
        let mut i = self.pos + 1;
        let first_name = i;
        while let Some(Token {
            tok: Tok::Lower(_), ..
        }) = self.tokens.get(i)
        {
            i += 1;
        }
        if i == first_name || self.tokens.get(i).map(|t| &t.tok) != Some(&Tok::Colon) {
            return false;
        }
        let mut depth = 0;
        for (j, token) in self.tokens.iter().enumerate().skip(self.pos) {
            match token.tok {
                Tok::LParen => depth += 1,
                Tok::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return self.tokens.get(j + 1).map(|t| &t.tok) == Some(&Tok::Arrow);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// `a = b`, `a != b`, `a < b`, `a <= b`: not associative.
    fn cmp_expr(&mut self) -> Result<Expr> {
        let lhs = self.add_expr()?;
        let op = match self.peek() {
            Some(Tok::Equals) => BinOp::Eq,
            Some(Tok::NotEq) => BinOp::Ne,
            Some(Tok::Lt) => BinOp::Lt,
            Some(Tok::Le) => BinOp::Le,
            _ => return Ok(lhs),
        };
        self.bump();
        let rhs = self.add_expr()?;
        Ok(Expr::Binary(op, Box::new(lhs), Box::new(rhs)))
    }

    /// `+`, `-`: left-associative.
    fn add_expr(&mut self) -> Result<Expr> {
        let mut lhs = self.mul_expr()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Plus) => BinOp::Add,
                Some(Tok::Minus) => BinOp::Sub,
                _ => return Ok(lhs),
            };
            self.bump();
            let rhs = self.mul_expr()?;
            lhs = Expr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
    }

    /// `*`, `/`, `%`: left-associative, binding tighter than `+`.
    fn mul_expr(&mut self) -> Result<Expr> {
        let mut lhs = self.app()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Star) => BinOp::Mul,
                Some(Tok::Slash) => BinOp::Div,
                Some(Tok::Percent) => BinOp::Mod,
                _ => return Ok(lhs),
            };
            self.bump();
            let rhs = self.app()?;
            lhs = Expr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
    }

    fn app(&mut self) -> Result<Expr> {
        let mut expr = self.atom()?;
        while self.starts_atom() {
            let arg = self.atom()?;
            expr = Expr::App(Box::new(expr), Box::new(arg));
        }
        Ok(expr)
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Some(
                Tok::Lower(_)
                    | Tok::Upper(_)
                    | Tok::Num(_)
                    | Tok::TypeU
                    | Tok::Prop
                    | Tok::LParen
                    | Tok::LBracket
                    | Tok::Underscore
            )
        )
    }

    fn atom(&mut self) -> Result<Expr> {
        let span = self.here();
        match self.peek() {
            Some(Tok::Lower(_)) => Ok(Expr::Var(self.lower("an expression")?)),
            Some(Tok::Upper(_)) => Ok(Expr::Var(self.upper("an expression")?)),
            Some(Tok::Num(n)) => {
                self.bump();
                Ok(Expr::Num(*n, span))
            }
            Some(Tok::Underscore) => {
                self.bump();
                Ok(Expr::Hole(span))
            }
            Some(Tok::TypeU) => {
                self.bump();
                if let Some(Tok::Num(n)) = self.peek() {
                    let end = self.bump().span;
                    let level =
                        u32::try_from(*n).map_err(|_| error(end, "universe level is too large"))?;
                    return Ok(Expr::Type(level, span.to(end)));
                }
                Ok(Expr::Type(0, span))
            }
            Some(Tok::Prop) => {
                self.bump();
                Ok(Expr::Prop(span))
            }
            Some(Tok::LParen) => {
                self.bump();
                let inner = self.expr()?;
                if self.eat(&Tok::Colon) {
                    let ty = self.expr()?;
                    let end = self.expect(Tok::RParen, "`)`")?.span;
                    return Ok(Expr::Ann(Box::new(inner), Box::new(ty), span.to(end)));
                }
                self.expect(Tok::RParen, "`)`")?;
                Ok(inner)
            }
            Some(Tok::LBracket)
                if matches!(self.peek_at(1), Some(Tok::Lower(_)))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                let name = self.lower("a name")?;
                self.bump();
                let value = self.expr()?;
                let end = self.expect(Tok::RBracket, "`]`")?.span;
                Ok(Expr::NamedArg(name, Box::new(value), span.to(end)))
            }
            Some(Tok::LBracket) => {
                self.bump();
                let mut items = Vec::new();
                if self.peek() != Some(&Tok::RBracket) {
                    items.push(self.expr()?);
                    while self.eat(&Tok::Comma) {
                        items.push(self.expr()?);
                    }
                }
                let end = self.expect(Tok::RBracket, "`,` or `]`")?.span;
                Ok(Expr::List(items, span.to(end)))
            }
            _ => Err(self.unexpected("an expression")),
        }
    }
}

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Lower(s) | Tok::Upper(s) => format!("`{s}`"),
        Tok::Num(n) => format!("`{n}`"),
        Tok::Str(s) => format!("`\"{s}\"`"),
        Tok::KwTest => "`test`".into(),
        Tok::KwType => "`type`".into(),
        Tok::KwTheorem => "`theorem`".into(),
        Tok::KwExport => "`export`".into(),
        Tok::TypeU => "`Type`".into(),
        Tok::Prop => "`Prop`".into(),
        Tok::LParen => "`(`".into(),
        Tok::RParen => "`)`".into(),
        Tok::LBracket => "`[`".into(),
        Tok::RBracket => "`]`".into(),
        Tok::Comma => "`,`".into(),
        Tok::Colon => "`:`".into(),
        Tok::ColonEq => "`:=`".into(),
        Tok::Equals => "`=`".into(),
        Tok::Arrow => "`->`".into(),
        Tok::Backslash => "`\\`".into(),
        Tok::Pipe => "`|`".into(),
        Tok::Plus => "`+`".into(),
        Tok::Underscore => "`_`".into(),
        Tok::Minus => "`-`".into(),
        Tok::Star => "`*`".into(),
        Tok::Slash => "`/`".into(),
        Tok::Percent => "`%`".into(),
        Tok::NotEq => "`!=`".into(),
        Tok::Lt => "`<`".into(),
        Tok::Le => "`<=`".into(),
        Tok::KwIf => "`if`".into(),
        Tok::KwThen => "`then`".into(),
        Tok::KwElse => "`else`".into(),
    }
}

fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic::error("E-PARSE", message.clone()).with_label(span, message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;

    fn parse(text: &str) -> Module {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_module(file, text).unwrap_or_else(|errors| panic!("{errors:?}"))
    }

    #[test]
    fn indented_lines_continue_a_declaration() {
        let module = parse(
            "type List (a : Type) : Type =\n  | Nil\n  | Cons (head : a) (tail : List a)\n\nlength : (a : Type) -> List a -> Nat\nlength a Nil = 0\n",
        );
        assert_eq!(module.decls.len(), 3);
        let Decl::Data { ctors, .. } = &module.decls[0] else {
            panic!("expected a data declaration");
        };
        assert_eq!(ctors.len(), 2);
    }

    #[test]
    fn export_on_its_own_line_attaches_to_the_next_declaration() {
        let module = parse("export\nf : Nat -> Nat\nf n = n\n");
        assert_eq!(module.decls.len(), 2);
        assert!(matches!(
            module.decls[0],
            Decl::Signature { export: true, .. }
        ));
    }

    #[test]
    fn equality_binds_looser_than_addition_and_tighter_than_arrows() {
        let module = parse("p : (n : Nat) -> n + 0 = n -> Nat\n");
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a signature");
        };
        let Expr::Pi { cod, .. } = ty else {
            panic!("expected a dependent function type, got {ty:?}");
        };
        let Expr::Arrow(lhs, _) = cod.as_ref() else {
            panic!("expected an arrow, got {cod:?}");
        };
        let Expr::Binary(BinOp::Eq, sum, _) = lhs.as_ref() else {
            panic!("expected an equation, got {lhs:?}");
        };
        assert!(matches!(sum.as_ref(), Expr::Binary(BinOp::Add, ..)));
    }

    fn expr(text: &str) -> Expr {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_expression(file, text).unwrap_or_else(|e| panic!("{e:?}"))
    }

    #[test]
    fn multiplication_binds_tighter_than_addition_and_both_associate_left() {
        let Expr::Binary(BinOp::Sub, lhs, rhs) = expr("a + b * c - d") else {
            panic!("expected `(a + b * c) - d`");
        };
        assert!(matches!(*rhs, Expr::Var(_)));
        let Expr::Binary(BinOp::Add, _, product) = *lhs else {
            panic!("expected `a + (b * c)`");
        };
        assert!(matches!(*product, Expr::Binary(BinOp::Mul, ..)));
        assert!(matches!(expr("a / b % c"), Expr::Binary(BinOp::Mod, ..)));
        assert!(matches!(expr("a <= b + 1"), Expr::Binary(BinOp::Le, ..)));
        assert!(matches!(expr("a != b"), Expr::Binary(BinOp::Ne, ..)));
        assert!(matches!(expr("a < b"), Expr::Binary(BinOp::Lt, ..)));
    }

    #[test]
    fn parses_tests() {
        let module = parse("test \"two \\\"words\\\"\" =\n  1 + 1 = 2\n");
        let Decl::Test { name, expr, .. } = &module.decls[0] else {
            panic!("expected a test");
        };
        assert_eq!(name, "two \"words\"");
        assert!(matches!(expr, Expr::Binary(BinOp::Eq, ..)));
    }

    #[test]
    fn parses_both_kinds_of_if() {
        assert!(matches!(
            expr("if b then 1 else 2"),
            Expr::If { binder: None, .. }
        ));
        assert!(matches!(
            expr("if h : d != 0 then n / d else 0"),
            Expr::If {
                binder: Some(_),
                ..
            }
        ));
    }

    #[test]
    fn parses_auto_binders_and_absurd_patterns() {
        let module = parse(
            "div : (n d : Nat) -> [auto ok : d != 0] -> Nat\nabsurd : Void -> a\nabsurd ()\n",
        );
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a signature");
        };
        let Expr::Pi { cod, .. } = ty else {
            panic!("expected a function type");
        };
        assert!(
            matches!(cod.as_ref(), Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == "ok")
        );
        let Decl::Equation { patterns, rhs, .. } = &module.decls[2] else {
            panic!("expected an equation");
        };
        assert!(matches!(patterns[..], [Pattern::Absurd(_)]));
        assert!(rhs.is_none());
        // `auto` alone is an ordinary name.
        let module = parse("f : [auto : Type] -> auto\n");
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a signature");
        };
        assert!(matches!(ty, Expr::Pi { auto: false, .. }));
    }

    #[test]
    fn square_brackets_are_implicit_binders_named_arguments_or_lists() {
        let module = parse("f : [a : Type] -> List a -> Nat\nx = g [a := Nat] [1] _\n");
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a signature");
        };
        assert!(matches!(ty, Expr::Pi { implicit: true, .. }));
        let Decl::Equation { rhs, .. } = &module.decls[1] else {
            panic!("expected an equation");
        };
        let Some(Expr::App(f, hole)) = rhs else {
            panic!("expected an application, got {rhs:?}");
        };
        assert!(matches!(hole.as_ref(), Expr::Hole(_)));
        let Expr::App(f, list) = f.as_ref() else {
            panic!("expected an application, got {f:?}");
        };
        assert!(matches!(list.as_ref(), Expr::List(..)));
        let Expr::App(_, named) = f.as_ref() else {
            panic!("expected an application, got {f:?}");
        };
        assert!(matches!(named.as_ref(), Expr::NamedArg(..)));
    }

    #[test]
    fn parenthesised_names_without_an_arrow_are_annotations() {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", "(x : Nat)");
        assert!(matches!(
            parse_expression(file, "(x : Nat)"),
            Ok(Expr::Ann(..))
        ));
    }
}
