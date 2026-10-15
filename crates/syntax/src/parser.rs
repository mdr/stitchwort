//! Recursive-descent parser for the surface syntax. See `docs/syntax.md`.
//!
//! Layout rule (interim): a declaration starts at column 0, and every following
//! line that is indented belongs to it. A line containing only `export` attaches
//! to the declaration after it.
//!
//! Blocks: an expression that starts on a new line is a block, whose lines
//! start at that line's column. Each line is a statement (`let x = e`, or an
//! expression run for its effects) and the last is the result. Lines indented
//! further continue the line above. A line at the block's column right after
//! one ending in an operator (like `->`) continues it too.

use crate::ast::{BinOp, Binder, Clause, CtorDecl, Decl, Expr, Module, Name, Pattern, Row};
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
    /// Inside a block: its column. A token starting a line at or left of it
    /// ends the current statement, so `peek` doesn't see it.
    limit: Option<u32>,
    /// The token starting the current statement, which `limit` doesn't stop.
    allow: Option<usize>,
    /// Whether `=` ends the expression, as in the type of `let x : T = e`.
    no_equals: bool,
}

/// One line of a block.
enum Stmt {
    Let(Name, Option<Expr>, Expr, Span),
    Expr(Expr),
}

impl<'t> Parser<'t> {
    fn new(tokens: &'t [Token], file: FileId, text_len: usize) -> Self {
        let eof = tokens.last().map_or(text_len as u32, |t| t.span.end);
        Parser {
            tokens,
            pos: 0,
            file,
            eof,
            limit: None,
            allow: None,
            no_equals: false,
        }
    }

    /// Whether the token at `i` ends the current statement of a block.
    fn is_stop(&self, i: usize) -> bool {
        let Some(limit) = self.limit else {
            return false;
        };
        self.allow != Some(i)
            && self
                .tokens
                .get(i)
                .is_some_and(|t| t.line_start && t.column <= limit)
    }

    fn peek(&self) -> Option<&'t Tok> {
        if self.is_stop(self.pos) {
            return None;
        }
        self.tokens.get(self.pos).map(|t| &t.tok)
    }

    fn peek_at(&self, offset: usize) -> Option<&'t Tok> {
        if (0..=offset).any(|k| self.is_stop(self.pos + k)) {
            return None;
        }
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
            Some(Tok::KwAbility) => self.ability(),
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
        // `{State Nat} Nat`: a computation that's not a function.
        let ty = self.result_type()?;
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
        fn has_absurd(p: &Pattern) -> bool {
            match p {
                Pattern::Absurd(_) => true,
                Pattern::Ctor(_, args, _) => args.iter().any(has_absurd),
                _ => false,
            }
        }
        let absurd = patterns.iter().any(has_absurd);
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
                Ok(Pattern::Num(n.clone(), span))
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

    /// `ability Name (params) where`, then one operation per line.
    fn ability(&mut self) -> Result<Decl> {
        let start = self.bump().span;
        let name = self.upper("an ability name (starting with an uppercase letter)")?;
        let mut params = Vec::new();
        while self.peek() == Some(&Tok::LParen) {
            params.push(self.binder()?);
        }
        self.expect(Tok::KwWhere, "`where`")?;
        let Some(first) = self.tokens.get(self.pos).filter(|_| self.peek().is_some()) else {
            return Err(self.unexpected("the ability's operations"));
        };
        let column = first.column;
        let saved = (self.limit, self.allow);
        self.limit = Some(column);
        let mut ops = Vec::new();
        let result = loop {
            self.allow = Some(self.pos);
            let op = (|| {
                let op = self.lower("an operation name")?;
                self.expect(Tok::Colon, "`:`")?;
                Ok((op, self.expr_inline()?))
            })();
            match op {
                Ok(op) => ops.push(op),
                Err(e) => break Err(e),
            }
            if !self.starts_line_at(column) {
                break Ok(());
            }
        };
        (self.limit, self.allow) = saved;
        result?;
        Ok(Decl::Ability {
            span: start.to(self.prev_span()),
            name,
            params,
            ops,
        })
    }

    /// Whether the next token starts a line at exactly `column`.
    fn starts_line_at(&self, column: u32) -> bool {
        self.tokens
            .get(self.pos)
            .is_some_and(|t| t.line_start && t.column == column)
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

    /// An expression, or a block if it starts on a new line.
    fn expr(&mut self) -> Result<Expr> {
        if let Some(token) = self.tokens.get(self.pos)
            && token.line_start
            && self.pos > 0
            && self.allow != Some(self.pos)
        {
            match self.limit {
                None => return self.block(token.column, true),
                Some(limit) if token.column > limit => return self.block(token.column, true),
                // A line at the block's own column after a line ending in an
                // operator: it continues that line.
                Some(limit) if token.column == limit => return self.block(token.column, false),
                Some(_) => {}
            }
        }
        self.expr_inline()
    }

    /// Lines at `column`, each a statement, the last being the result. With
    /// `many` false, just one line.
    fn block(&mut self, column: u32, many: bool) -> Result<Expr> {
        let saved = (self.limit, self.allow);
        self.limit = Some(column);
        let mut stmts = Vec::new();
        let result = loop {
            self.allow = Some(self.pos);
            match self.statement() {
                Ok(stmt) => stmts.push(stmt),
                Err(e) => break Err(e),
            }
            if !(many && self.starts_line_at(column)) {
                break Ok(());
            }
        };
        (self.limit, self.allow) = saved;
        result?;
        let mut rest = match stmts.pop() {
            Some(Stmt::Expr(e)) => e,
            Some(Stmt::Let(_, _, _, span)) => {
                return Err(error(
                    span,
                    "a block must end with an expression, not `let`",
                ));
            }
            None => return Err(self.unexpected("an expression")),
        };
        for stmt in stmts.into_iter().rev() {
            rest = match stmt {
                Stmt::Let(name, ty, value, span) => Expr::Let {
                    span: span.to(rest.span()),
                    name,
                    ty: ty.map(Box::new),
                    value: Box::new(value),
                    body: Box::new(rest),
                },
                Stmt::Expr(e) => Expr::Seq(Box::new(e), Box::new(rest)),
            };
        }
        Ok(rest)
    }

    fn statement(&mut self) -> Result<Stmt> {
        if self.peek() != Some(&Tok::KwLet) {
            return Ok(Stmt::Expr(self.expr_inline()?));
        }
        let start = self.bump().span;
        let name = self.lower("a name")?;
        let ty = if self.eat(&Tok::Colon) {
            let saved = std::mem::replace(&mut self.no_equals, true);
            let ty = self.expr_inline();
            self.no_equals = saved;
            Some(ty?)
        } else {
            None
        };
        self.expect(Tok::Equals, "`=`")?;
        let value = self.expr()?;
        Ok(Stmt::Let(name, ty, value, start))
    }

    /// A function's result type, possibly with abilities: `{State s} Nat`.
    fn result_type(&mut self) -> Result<Expr> {
        if self.peek() != Some(&Tok::LBrace) {
            return self.expr();
        }
        let row = self.row()?;
        let ty = self.expr()?;
        Ok(Expr::Effect(row, Box::new(ty)))
    }

    /// `{A, B args | e}`, `{e}` or `{}`.
    fn row(&mut self) -> Result<Row> {
        let start = self.expect(Tok::LBrace, "`{`")?.span;
        let mut abilities = Vec::new();
        let mut tail = None;
        if self.peek() != Some(&Tok::RBrace) && self.peek() != Some(&Tok::Pipe) {
            abilities.push(self.app()?);
            while self.eat(&Tok::Comma) {
                abilities.push(self.app()?);
            }
        }
        if self.eat(&Tok::Pipe) {
            tail = Some(self.lower("a row variable")?);
        } else if let Some(Expr::Var(name)) = abilities.last()
            && name.text.starts_with(|c: char| c.is_ascii_lowercase())
        {
            tail = Some(name.clone());
            abilities.pop();
        }
        let end = self.expect(Tok::RBrace, "`}`")?.span;
        Ok(Row {
            abilities,
            tail,
            span: start.to(end),
        })
    }

    /// `handle e with | return x -> … | op arg => k -> …`
    fn handle(&mut self, start: Span) -> Result<Expr> {
        let body = self.expr_inline()?;
        self.expect(Tok::KwWith, "`with`")?;
        let mut clauses = Vec::new();
        // Clauses on their own lines line up: a `|` at another column belongs
        // to an enclosing handler (or isn't a clause at all).
        let mut column = None;
        while self.peek() == Some(&Tok::Pipe) {
            let token = &self.tokens[self.pos];
            if token.line_start {
                match column {
                    None => column = Some(token.column),
                    Some(c) if c != token.column => break,
                    Some(_) => {}
                }
            }
            self.bump();
            if self.eat(&Tok::KwReturn) {
                let var = self.lower("a name for the result")?;
                self.expect(Tok::Arrow, "`->`")?;
                let body = self.expr()?;
                clauses.push(Clause::Return { var, body });
            } else {
                let op = self.lower("an operation, or `return`")?;
                let arg = self.pattern()?;
                self.expect(Tok::FatArrow, "`=>`")?;
                let k = self.lower("a name for the continuation")?;
                self.expect(Tok::Arrow, "`->`")?;
                let body = self.expr()?;
                clauses.push(Clause::Op { op, arg, k, body });
            }
        }
        if clauses.is_empty() {
            return Err(self.unexpected("`|` and a handler clause"));
        }
        Ok(Expr::Handle {
            span: start.to(self.prev_span()),
            body: Box::new(body),
            clauses,
        })
    }

    fn expr_inline(&mut self) -> Result<Expr> {
        let start = self.here();
        if self.eat(&Tok::KwHandle) {
            return self.handle(start);
        }
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
            let cod = self.result_type()?;
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
            let rhs = self.result_type()?;
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

    /// `a = b`, `a != b`, `a == b`, `a < b`, `a <= b`: not associative.
    fn cmp_expr(&mut self) -> Result<Expr> {
        let lhs = self.append_expr()?;
        let op = match self.peek() {
            Some(Tok::Equals) if !self.no_equals => BinOp::Eq,
            Some(Tok::NotEq) => BinOp::Ne,
            Some(Tok::EqEq) => BinOp::EqEq,
            Some(Tok::Lt) => BinOp::Lt,
            Some(Tok::Le) => BinOp::Le,
            _ => return Ok(lhs),
        };
        self.bump();
        let rhs = self.append_expr()?;
        Ok(Expr::Binary(op, Box::new(lhs), Box::new(rhs)))
    }

    /// `++`: right-associative, binding more loosely than `+`, so
    /// `"n = " ++ natToText (n + 1)` and `a ++ b ++ c` mean what they look like.
    fn append_expr(&mut self) -> Result<Expr> {
        let lhs = self.add_expr()?;
        if self.peek() != Some(&Tok::PlusPlus) {
            return Ok(lhs);
        }
        self.bump();
        let rhs = self.append_expr()?;
        Ok(Expr::Binary(BinOp::Append, Box::new(lhs), Box::new(rhs)))
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
                    | Tok::Char(_)
                    | Tok::Str(_)
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
                Ok(Expr::Num(n.clone(), span))
            }
            Some(Tok::Str(s)) => {
                let s = s.clone();
                self.bump();
                Ok(Expr::Str(s, span))
            }
            Some(Tok::Char(c)) => {
                let c = *c;
                self.bump();
                Ok(Expr::Char(c, span))
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
                        u32::try_from(n).map_err(|_| error(end, "universe level is too large"))?;
                    return Ok(Expr::Type(level, span.to(end)));
                }
                Ok(Expr::Type(0, span))
            }
            Some(Tok::Prop) => {
                self.bump();
                Ok(Expr::Prop(span))
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                let end = self.bump().span;
                Ok(Expr::Unit(span.to(end)))
            }
            Some(Tok::LParen) => {
                self.bump();
                let saved = std::mem::replace(&mut self.no_equals, false);
                let inner = self.expr();
                self.no_equals = saved;
                let inner = inner?;
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
        Tok::Char(c) => format!("`'{c}'`"),
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
        Tok::PlusPlus => "`++`".into(),
        Tok::Underscore => "`_`".into(),
        Tok::Minus => "`-`".into(),
        Tok::Star => "`*`".into(),
        Tok::Slash => "`/`".into(),
        Tok::Percent => "`%`".into(),
        Tok::NotEq => "`!=`".into(),
        Tok::KwAbility => "`ability`".into(),
        Tok::KwWhere => "`where`".into(),
        Tok::KwHandle => "`handle`".into(),
        Tok::KwWith => "`with`".into(),
        Tok::KwReturn => "`return`".into(),
        Tok::KwLet => "`let`".into(),
        Tok::LBrace => "`{`".into(),
        Tok::RBrace => "`}`".into(),
        Tok::FatArrow => "`=>`".into(),
        Tok::EqEq => "`==`".into(),
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
        assert!(matches!(expr("a == b + 1"), Expr::Binary(BinOp::EqEq, ..)));
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

    /// The right-hand side of the only equation in `text`.
    fn rhs(text: &str) -> Expr {
        match parse(text).decls.into_iter().next() {
            Some(Decl::Equation { rhs: Some(rhs), .. }) => rhs,
            other => panic!("expected an equation, got {other:?}"),
        }
    }

    /// The block's lines, as `let x` or `_` for an expression, then the result.
    fn lines(mut e: &Expr) -> Vec<String> {
        let mut out = Vec::new();
        loop {
            match e {
                Expr::Let { name, body, .. } => {
                    out.push(format!("let {}", name.text));
                    e = body;
                }
                Expr::Seq(_, rest) => {
                    out.push("_".into());
                    e = rest;
                }
                _ => {
                    out.push("result".into());
                    return out;
                }
            }
        }
    }

    #[test]
    fn a_block_is_lines_at_one_column() {
        let body = rhs("f u =\n  let n = get ()\n  put (n +\n    1)\n  n\n");
        assert_eq!(lines(&body), ["let n", "_", "result"]);
        // On one line, or with one line, it's just the expression.
        assert!(matches!(rhs("f u = g u\n"), Expr::App(..)));
        assert!(matches!(rhs("f u =\n  g\n    u\n"), Expr::App(..)));
    }

    #[test]
    fn a_line_ending_in_an_operator_continues() {
        let module = parse("f : Nat ->\n  Nat ->\n  Nat\n");
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!()
        };
        let Expr::Arrow(_, rest) = ty else {
            panic!("{ty:?}")
        };
        assert!(matches!(rest.as_ref(), Expr::Arrow(..)), "{rest:?}");
    }

    #[test]
    fn blocks_nest() {
        let body = rhs("f u =\n  let g = \\x ->\n    say x\n    x\n  g 1\n");
        assert_eq!(lines(&body), ["let g", "result"]);
        let Expr::Let { value, .. } = &body else {
            panic!()
        };
        let Expr::Lam(_, inner, _) = value.as_ref() else {
            panic!("{value:?}")
        };
        assert_eq!(lines(inner), ["_", "result"]);
    }

    #[test]
    fn let_takes_a_type() {
        let body = rhs("f u =\n  let r : s -> {e} a = run\n  r\n");
        let Expr::Let { ty: Some(ty), .. } = &body else {
            panic!("{body:?}")
        };
        assert!(matches!(ty.as_ref(), Expr::Arrow(..)));
    }

    #[test]
    fn rows_list_abilities_then_a_tail() {
        let row = |text: &str| {
            let module = parse(&format!("f : Nat -> {text} Nat\n"));
            let Decl::Signature {
                ty: Expr::Arrow(_, cod),
                ..
            } = &module.decls[0]
            else {
                panic!()
            };
            let Expr::Effect(row, _) = cod.as_ref() else {
                panic!("{cod:?}")
            };
            (
                row.abilities.len(),
                row.tail.as_ref().map(|t| t.text.clone()),
            )
        };
        assert_eq!(row("{State s, Abort | e}"), (2, Some("e".into())));
        assert_eq!(row("{State s}"), (1, None));
        assert_eq!(row("{e}"), (0, Some("e".into())));
        assert_eq!(row("{| e}"), (0, Some("e".into())));
        assert_eq!(row("{}"), (0, None));
    }

    #[test]
    fn parses_abilities_and_handlers() {
        let module = parse(
            "ability State (s : Type) where\n  get : () -> {State s} s\n  put : s -> {State s} ()\n",
        );
        let Decl::Ability { params, ops, .. } = &module.decls[0] else {
            panic!()
        };
        assert_eq!(params.len(), 1);
        let names: Vec<_> = ops.iter().map(|(n, _)| n.text.as_str()).collect();
        assert_eq!(names, ["get", "put"]);

        let body = rhs(
            "f p =\n  handle p () with\n    | return x -> x\n    | get () => k -> k 1\n    | put s => k ->\n      k ()\n",
        );
        let Expr::Handle { clauses, .. } = body else {
            panic!("{body:?}")
        };
        assert!(matches!(clauses[0], Clause::Return { .. }));
        assert!(matches!(
            &clauses[1],
            Clause::Op {
                arg: Pattern::Absurd(_),
                ..
            }
        ));
        assert!(matches!(
            &clauses[2],
            Clause::Op {
                arg: Pattern::Var(_),
                ..
            }
        ));
    }

    #[test]
    fn unit_is_a_value_and_a_pattern() {
        assert!(matches!(rhs("f u = g ()\n"), Expr::App(_, ref a) if matches!(**a, Expr::Unit(_))));
        let module = parse("f () = 1\n");
        let Decl::Equation { patterns, .. } = &module.decls[0] else {
            panic!()
        };
        assert!(matches!(patterns[0], Pattern::Absurd(_)));
    }

    #[test]
    fn rejects_malformed_blocks_and_handlers() {
        let fails = |text: &str| {
            let mut sources = SourceMap::new();
            let file = sources.add("test.sw", text);
            parse_module(file, text).is_err()
        };
        assert!(fails("f u =\n  let x = 1\n"), "a block ending in `let`");
        assert!(fails("f p = handle p with\n"), "a handler with no clauses");
        assert!(
            fails("f p = handle p with | get x k -> k\n"),
            "a clause without `=>`"
        );
        assert!(fails("ability A where\n"), "an ability without operations");
        assert!(fails("f : Nat -> {State s Nat\n"), "an unclosed row");
    }
}
