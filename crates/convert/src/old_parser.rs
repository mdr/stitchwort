//! The old declaration syntax's parser (a signature line, then equations;
//! `->` in lambdas and arms; `let x = e`), as it was at the switch to the
//! `def` syntax (docs/proposals/declaration-syntax.md §5.6): a copy of
//! `crates/syntax/src/parser.rs`, which reads either syntax. The language's
//! parser only reads the new one; this one is for the converter alone.

use stitchwort_syntax::ast::{
    Alt, BinOp, Binder, Clause, CtorDecl, Decl, Expr, Import, MatchKind, Module, Name, Pattern,
    Row, Scrutinee,
};
use stitchwort_syntax::stack::StackLimit;
use stitchwort_syntax::{Diagnostic, FileId, Span};
use stitchwort_syntax::{Tok, Token, lex};

mod declarations;

type Result<T> = std::result::Result<T, Diagnostic>;

/// Bytes of stack the parser may use when the caller doesn't say: safe on a
/// 2 MiB thread (Rust's default for spawned threads and tests), like the
/// core's default `Limits`.
pub const DEFAULT_STACK: usize = 1536 * 1024;

/// Which declaration syntax a source is written in
/// (docs/proposals/declaration-syntax.md). The old one (a signature line,
/// then equations) is the default until the whole code base is converted;
/// the switch is a change to [`Syntax::default`]. A file is wholly in one
/// syntax.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Syntax {
    /// `f : Nat -> Nat` then `f n = n`; `->` in lambdas, `match` and
    /// handlers; `let x = e`; `test "n" = e`.
    #[default]
    Old,
    /// `def f (n : Nat) : Nat := n`, or arms `| p => e` under the header;
    /// `=>` in lambdas, `match` and handlers; `let x := e`; `test "n" := e`.
    New,
}

impl Syntax {
    /// `"old"` or `"new"`, as a command-line option names them.
    pub fn from_name(name: &str) -> Option<Syntax> {
        match name {
            "old" => Some(Syntax::Old),
            "new" => Some(Syntax::New),
            _ => None,
        }
    }
}

pub fn parse_module(file: FileId, text: &str) -> std::result::Result<Module, Vec<Diagnostic>> {
    parse_module_within(file, text, DEFAULT_STACK)
}

pub fn parse_expression(file: FileId, text: &str) -> Result<Expr> {
    parse_expression_within(file, text, DEFAULT_STACK)
}

/// Parses a module, using at most `stack` bytes of stack: a program nested
/// more deeply than that allows is an `E-RESOURCE` error, not a crash.
pub fn parse_module_within(
    file: FileId,
    text: &str,
    stack: usize,
) -> std::result::Result<Module, Vec<Diagnostic>> {
    parse_module_in(Syntax::default(), file, text, stack)
}

/// Parses a module written in `syntax`, using at most `stack` bytes of stack.
pub fn parse_module_in(
    syntax: Syntax,
    file: FileId,
    text: &str,
    stack: usize,
) -> std::result::Result<Module, Vec<Diagnostic>> {
    let limit = StackLimit::from_here(stack);
    let tokens = lex(file, text).map_err(|d| vec![d])?;
    let mut imports = Vec::new();
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    for group in split_decls(&tokens, syntax).map_err(|d| vec![d])? {
        let mut parser = Parser::new(group, file, text.len(), limit, syntax);
        if parser.peek() == Some(&Tok::KwImport) {
            if !decls.is_empty() {
                errors.push(
                    error(group[0].span, "imports go at the top of the file")
                        .with_note("move it before the first declaration"),
                );
                continue;
            }
            match parser
                .import()
                .and_then(|import| parser.finish().map(|()| import))
            {
                Ok(import) => imports.push(import),
                Err(diagnostic) => errors.push(diagnostic),
            }
            continue;
        }
        let parsed = match syntax {
            Syntax::Old => parser.decl().map(|decl| vec![decl]),
            Syntax::New => parser.new_decl(),
        };
        match parsed.and_then(|parsed| parser.finish().map(|()| parsed)) {
            Ok(parsed) => decls.extend(parsed),
            Err(diagnostic) => errors.push(diagnostic),
        }
    }
    if errors.is_empty() {
        Ok(Module { imports, decls })
    } else {
        Err(errors)
    }
}

/// Parses an expression, using at most `stack` bytes of stack.
pub fn parse_expression_within(file: FileId, text: &str, stack: usize) -> Result<Expr> {
    parse_expression_in(Syntax::default(), file, text, stack)
}

/// Parses an expression written in `syntax`, using at most `stack` bytes of
/// stack.
pub fn parse_expression_in(syntax: Syntax, file: FileId, text: &str, stack: usize) -> Result<Expr> {
    let limit = StackLimit::from_here(stack);
    let tokens = lex(file, text)?;
    let mut parser = Parser::new(&tokens, file, text.len(), limit, syntax);
    let expr = parser.expr()?;
    parser.finish()?;
    Ok(expr)
}

/// `name`, unless it's qualified: a binder, a field or a constructor being
/// declared has a short name.
fn unqualified(name: Name) -> Result<Name> {
    if name.text.contains('.') {
        return Err(error(
            name.span,
            format!(
                "`{}` is a qualified name, which can't be used here",
                name.text
            ),
        )
        .with_note("only declarations and references can be qualified; write a short name"));
    }
    Ok(name)
}

/// Whether a pattern contains the absurd pattern `()`, so its equation or
/// arm needs no right-hand side.
fn has_absurd(p: &Pattern) -> bool {
    match p {
        Pattern::Absurd(_) => true,
        Pattern::Ctor(_, args, _) => args.iter().any(has_absurd),
        Pattern::Tuple(a, b, _) => has_absurd(a) || has_absurd(b),
        Pattern::Cons(a, b, _) => has_absurd(a) || has_absurd(b),
        Pattern::Record { fields, .. } => fields.iter().any(|(_, p)| has_absurd(p)),
        _ => false,
    }
}

fn split_decls(tokens: &[Token], syntax: Syntax) -> Result<Vec<&[Token]>> {
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
    // A line holding only `export` belongs to the declaration that follows
    // it. (In the new syntax, `export` is on the same line: `export def`.)
    if syntax == Syntax::Old {
        starts.retain(|&i| {
            i == 0 || !(tokens[i - 1].tok == Tok::KwExport && is_alone(tokens, i - 1))
        });
    }
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
    /// How deep the recursion may go.
    stack: StackLimit,
    /// Which declaration syntax this is.
    syntax: Syntax,
}

/// One line of a block.
enum Stmt {
    Let(Name, Option<Expr>, Expr, Span),
    /// `let (a, b) = e`: a pattern binding, desugared to a `match` in `block`.
    LetPattern(Pattern, Option<Expr>, Expr, Span),
    Expr(Expr),
}

impl<'t> Parser<'t> {
    fn new(
        tokens: &'t [Token],
        file: FileId,
        text_len: usize,
        stack: StackLimit,
        syntax: Syntax,
    ) -> Self {
        let eof = tokens.last().map_or(text_len as u32, |t| t.span.end);
        Parser {
            tokens,
            pos: 0,
            file,
            eof,
            limit: None,
            allow: None,
            no_equals: false,
            stack,
            syntax,
        }
    }

    /// The arrow after a pattern or a lambda's parameters: `=>` in the new
    /// syntax, `->` in the old.
    fn case_arrow(&self) -> (Tok, &'static str) {
        match self.syntax {
            Syntax::Old => (Tok::Arrow, "`->`"),
            Syntax::New => (Tok::FatArrow, "`=>`"),
        }
    }

    /// What gives a name its value in `let` and `test`: `:=` in the new
    /// syntax, `=` in the old.
    fn binding_equals(&self) -> (Tok, &'static str) {
        match self.syntax {
            Syntax::Old => (Tok::Equals, "`=`"),
            Syntax::New => (Tok::ColonEq, "`:=`"),
        }
    }

    /// Called by each function the parser recurses through (`expr`,
    /// `append_expr` and `pattern`), before going deeper.
    fn deeper(&self) -> Result<()> {
        if self.stack.exceeded() {
            return Err(Diagnostic::error(
                "E-RESOURCE",
                "ran out of resources: the program is nested too deeply to parse",
            )
            .with_label(self.here(), "nested too deeply here")
            .with_note(
                "this isn't a syntax error: there's a limit on how deeply expressions nest",
            ));
        }
        Ok(())
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

    /// The column of the first token on the line that token `i` is on.
    fn line_indent(&self, i: usize) -> u32 {
        let start = (0..=i).rev().find(|&k| self.tokens[k].line_start);
        start.map_or(0, |k| self.tokens[k].column)
    }

    /// Like `expect`, for `then` and `else`, which can also start a line at
    /// or left of the enclosing block's column (where other tokens would
    /// start a new statement) if it's at least `indent`.
    fn expect_keyword(&mut self, tok: Tok, what: &str, indent: u32) -> Result<&'t Token> {
        if self.peek().is_none()
            && let Some(token) = self.tokens.get(self.pos)
            && token.tok == tok
            && token.line_start
            && token.column >= indent
        {
            return Ok(self.bump());
        }
        self.expect(tok, what)
    }

    fn unexpected(&self, expected: &str) -> Diagnostic {
        let found = match self.tokens.get(self.pos) {
            Some(token) if self.is_stop(self.pos) => {
                return error(
                    self.here(),
                    format!(
                        "expected {expected}, but the line starting with {} is at or left of \
                         the enclosing block's column, so it starts a new statement",
                        describe(&token.tok)
                    ),
                );
            }
            Some(token) => format!("found {}", describe(&token.tok)),
            None => "reached the end of the declaration".to_string(),
        };
        error(self.here(), format!("expected {expected}, but {found}"))
    }

    /// The rest of `(a, b, c)` after its first component, as nested pairs.
    /// Its own function, so the stack frame of the parser's recursive
    /// functions stays small (the nesting limit is measured in stack).
    #[inline(never)]
    fn tuple_expr(&mut self, first: Expr, span: Span) -> Result<Expr> {
        let mut items = vec![first];
        while self.eat(&Tok::Comma) {
            let saved = std::mem::replace(&mut self.no_equals, false);
            let item = self.expr();
            self.no_equals = saved;
            items.push(item?);
        }
        if self.peek() == Some(&Tok::Colon) {
            return Err(self.tuple_annotation());
        }
        let end = self.expect(Tok::RParen, "`)`")?.span;
        let mut last = items.pop().expect("two components");
        while let Some(first) = items.pop() {
            // The outermost tuple covers the brackets too.
            let s = if items.is_empty() {
                span.to(end)
            } else {
                first.span().to(end)
            };
            last = Expr::Tuple(Box::new(first), Box::new(last), s);
        }
        Ok(last)
    }

    /// The same for patterns.
    #[inline(never)]
    fn tuple_pattern(&mut self, first: Pattern, span: Span) -> Result<Pattern> {
        let mut items = vec![first];
        while self.eat(&Tok::Comma) {
            items.push(self.tuple_component()?);
        }
        let end = self.expect(Tok::RParen, "`)`")?.span;
        let mut last = items.pop().expect("two components");
        while let Some(first) = items.pop() {
            let s = if items.is_empty() {
                span.to(end)
            } else {
                first.span().to(end)
            };
            last = Pattern::Tuple(Box::new(first), Box::new(last), s);
        }
        Ok(last)
    }

    /// A component of a list pattern: a constructor's arguments run to the
    /// next `,` or `]`; `-k` is allowed, as in a tuple.
    fn list_component(&mut self) -> Result<Pattern> {
        if let Some(Tok::Upper(_)) = self.peek() {
            let start = self.here();
            let name = self.upper_q("a constructor")?;
            let mut args = Vec::new();
            while !matches!(self.peek(), Some(Tok::Comma | Tok::RBracket) | None) {
                args.push(self.pattern()?);
            }
            return Ok(Pattern::Ctor(name, args, start.to(self.prev_span())));
        }
        self.tuple_component()
    }

    /// A component of a tuple pattern: a pattern, or `-k`, which the
    /// tuple's brackets already delimit (`(-1, 0)`, `(0, -1)`).
    fn tuple_component(&mut self) -> Result<Pattern> {
        if self.peek() != Some(&Tok::Minus) {
            return self.pattern();
        }
        let start = self.bump().span;
        let Some(Tok::Num(n)) = self.peek() else {
            return Err(self.unexpected("a number"));
        };
        let n = n.clone();
        let end = self.bump().span;
        Ok(Pattern::NegNum(n, start.to(end)))
    }

    /// `(a, b : T)`, or `(a : T, b)`: an annotation inside a tuple.
    fn tuple_annotation(&self) -> Diagnostic {
        error(
            self.here(),
            "an annotation can't be written inside a tuple without brackets",
        )
        .with_note(
            "to annotate one component, write `(a, (b : T))`; to annotate the pair, write \
             `((a, b) : T)`",
        )
    }

    fn finish(&self) -> Result<()> {
        if self.pos < self.tokens.len() {
            Err(self.unexpected("the end of the declaration"))
        } else {
            Ok(())
        }
    }

    /// A lowercase name that's bound here, so it can't be qualified.
    fn lower(&mut self, what: &str) -> Result<Name> {
        let name = self.lower_q(what)?;
        unqualified(name)
    }

    /// A lowercase name, possibly qualified: `length` or `List.length`.
    fn lower_q(&mut self, what: &str) -> Result<Name> {
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
            Some(Tok::Upper(_)) => self.upper_q("a name"),
            _ => self.lower_q("a name"),
        }
    }

    /// An uppercase name that's declared here, so it can't be qualified.
    fn upper(&mut self, what: &str) -> Result<Name> {
        let name = self.upper_q(what)?;
        unqualified(name)
    }

    /// An uppercase name, possibly qualified: `Cons` or `List.Cons`.
    fn upper_q(&mut self, what: &str) -> Result<Name> {
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

    /// `import List (map, filter)`: a namespace, then the names to use from
    /// it, at least one.
    fn import(&mut self) -> Result<Import> {
        let start = self.expect(Tok::KwImport, "`import`")?.span;
        let path = match self.peek() {
            Some(Tok::Upper(text)) => {
                let name = Name {
                    text: text.clone(),
                    span: self.here(),
                };
                self.bump();
                name
            }
            _ => return Err(self.unexpected("a namespace, such as `List`")),
        };
        self.expect(Tok::LParen, "`(` and the names to import")?;
        let mut items = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::Lower(text) | Tok::Upper(text)) if !text.contains('.') => {
                    items.push(Name {
                        text: text.clone(),
                        span: self.here(),
                    });
                    self.bump();
                }
                _ => return Err(self.unexpected("a name to import")),
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let end = self.expect(Tok::RParen, "`)`")?.span;
        Ok(Import {
            path,
            items,
            span: start.to(end),
        })
    }

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
        let absurd = patterns.iter().any(has_absurd);
        if absurd && self.peek().is_none() {
            // `f ()` needs no right-hand side.
            return Ok(Decl::Equation {
                span: name.span.to(self.prev_span()),
                name,
                patterns,
                rhs: None,
                arm: None,
            });
        }
        self.expect(Tok::Equals, "`=`")?;
        let rhs = self.expr()?;
        Ok(Decl::Equation {
            span: name.span.to(rhs.span()),
            name,
            patterns,
            rhs: Some(rhs),
            arm: None,
        })
    }

    fn pattern(&mut self) -> Result<Pattern> {
        self.deeper()?;
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
                let name = self.upper_q("a constructor")?;
                Ok(Pattern::Ctor(name, Vec::new(), span))
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                let end = self.bump().span;
                Ok(Pattern::Absurd(span.to(end)))
            }
            Some(Tok::LBrace) => self.record_pattern(),
            Some(Tok::LBracket) => {
                self.bump();
                let mut items = Vec::new();
                if self.peek() != Some(&Tok::RBracket) {
                    items.push(self.list_component()?);
                    while self.eat(&Tok::Comma) {
                        items.push(self.list_component()?);
                    }
                }
                let end = self.expect(Tok::RBracket, "`,` or `]`")?.span;
                let mut list = Pattern::Nil(end);
                while let Some(item) = items.pop() {
                    let s = if items.is_empty() {
                        span.to(end)
                    } else {
                        item.span().to(end)
                    };
                    list = Pattern::Cons(Box::new(item), Box::new(list), s);
                }
                Ok(list)
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::Minus) => {
                // `(-k)`: a negative number pattern, only in brackets (a
                // tuple's included: `(-k, p)`).
                self.bump();
                let inner = self.tuple_component()?;
                if self.peek() == Some(&Tok::Comma) {
                    return self.tuple_pattern(inner, span);
                }
                let end = self.expect(Tok::RParen, "`)`")?.span;
                Ok(match inner {
                    Pattern::NegNum(n, _) => Pattern::NegNum(n, span.to(end)),
                    other => other,
                })
            }
            Some(Tok::LParen) => {
                self.bump();
                let pattern = if let Some(Tok::Upper(_)) = self.peek() {
                    let name = self.upper_q("a constructor")?;
                    let mut args = Vec::new();
                    while !matches!(self.peek(), Some(Tok::RParen | Tok::Comma) | None) {
                        args.push(self.pattern()?);
                    }
                    if self.peek() == Some(&Tok::Comma) {
                        // `(Just a, b)`: a constructor as a tuple's first component.
                        let first = Pattern::Ctor(name, args, span.to(self.prev_span()));
                        return self.tuple_pattern(first, span);
                    }
                    let end = self.expect(Tok::RParen, "`)`")?.span;
                    Pattern::Ctor(name, args, span.to(end))
                } else {
                    let inner = self.pattern()?;
                    if self.peek() == Some(&Tok::Comma) {
                        return self.tuple_pattern(inner, span);
                    }
                    self.expect(Tok::RParen, "`)`")?;
                    inner
                };
                Ok(pattern)
            }
            _ => Err(self.unexpected("a pattern or `=`")),
        }
    }

    /// `{ name = p, age, .. }`: fields in any order, each a pattern or punned
    /// (a variable of the field's name), optionally ending with `..`.
    fn record_pattern(&mut self) -> Result<Pattern> {
        let start = self.expect(Tok::LBrace, "`{`")?.span;
        let mut fields = Vec::new();
        let mut rest = false;
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                if self.eat(&Tok::DotDot) {
                    rest = true;
                    break;
                }
                let name = self.lower("a field name, or `..`")?;
                let pattern = if self.eat(&Tok::Equals) {
                    // A constructor's arguments run to the next `,` or `}`.
                    if let Some(Tok::Upper(_)) = self.peek() {
                        let start = self.here();
                        let name = self.upper_q("a constructor")?;
                        let mut args = Vec::new();
                        while !matches!(self.peek(), Some(Tok::Comma | Tok::RBrace) | None) {
                            args.push(self.pattern()?);
                        }
                        Pattern::Ctor(name, args, start.to(self.prev_span()))
                    } else {
                        self.pattern()?
                    }
                } else {
                    Pattern::Var(name.clone())
                };
                fields.push((name, pattern));
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        let end = self.expect(Tok::RBrace, "`,` or `}`")?.span;
        Ok(Pattern::Record {
            fields,
            rest,
            span: start.to(end),
        })
    }

    fn data(&mut self) -> Result<Decl> {
        let start = self.bump().span;
        let name = self.upper_q("a data type name (starting with an uppercase letter)")?;
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
        let mut record = false;
        if self.eat(&Tok::Equals) {
            if self.peek() == Some(&Tok::LBrace) {
                record = true;
                ctors.push(self.record_fields(&name)?);
            } else {
                while self.eat(&Tok::Pipe) {
                    let name =
                        self.upper("a constructor name (starting with an uppercase letter)")?;
                    let mut fields = Vec::new();
                    while self.peek() == Some(&Tok::LParen) {
                        fields.push(self.binder()?);
                    }
                    ctors.push(CtorDecl { name, fields });
                }
                if ctors.is_empty() {
                    return Err(
                        self.unexpected("`|` and a constructor, or `{` and a record's fields")
                    );
                }
            }
        }
        Ok(Decl::Data {
            span: start.to(self.prev_span()),
            name,
            params,
            sort,
            ctors,
            record,
        })
    }

    /// A record's fields, `{ name : Text, age : Nat }`, as the one
    /// constructor of the data type `data`, named `%mk`, which source can't
    /// write (so `data.mk` is free for a function).
    fn record_fields(&mut self, data: &Name) -> Result<CtorDecl> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                let field = self.lower("a field name")?;
                self.expect(Tok::Colon, "`:`")?;
                let ty = self.expr()?;
                fields.push(Binder {
                    names: vec![field],
                    ty,
                });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RBrace, "`,` or `}`")?;
        Ok(CtorDecl {
            name: Name {
                text: "%mk".into(),
                span: data.span,
            },
            fields,
        })
    }

    /// `ability Name (params) where`, then one operation per line.
    fn ability(&mut self) -> Result<Decl> {
        let start = self.bump().span;
        let name = self.upper_q("an ability name (starting with an uppercase letter)")?;
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
            let op: Result<_> = (|| {
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
        self.deeper()?;
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
            if !(many && self.starts_line_at(column)) || self.ends_blocks() {
                break Ok(());
            }
        };
        (self.limit, self.allow) = saved;
        result?;
        let mut rest = match stmts.pop() {
            Some(Stmt::Expr(e)) => e,
            Some(Stmt::Let(_, _, _, span) | Stmt::LetPattern(_, _, _, span)) => {
                return Err(error(
                    span,
                    "a block must end with an expression, not `let`",
                ));
            }
            None => return Err(self.unexpected("an expression")),
        };
        for stmt in stmts.into_iter().rev() {
            rest = match stmt {
                Stmt::LetPattern(pattern, ty, value, span) => {
                    let expr = match ty {
                        Some(ty) => {
                            let ann_span = value.span().to(ty.span());
                            Expr::Ann(Box::new(value), Box::new(ty), ann_span)
                        }
                        None => value,
                    };
                    let alt_span = pattern.span().to(rest.span());
                    let span = span.to(rest.span());
                    Expr::Match {
                        scrutinees: vec![Scrutinee { name: None, expr }],
                        alts: vec![Alt {
                            patterns: vec![pattern],
                            body: rest,
                            span: alt_span,
                        }],
                        span,
                        kind: MatchKind::Let,
                    }
                }
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

    /// Whether the next token can't start a line of a block, but ends it, and
    /// the blocks around it, for an enclosing construct: a `|` (the next arm
    /// of a definition), `where` or `:=` (after a type that's a block).
    fn ends_blocks(&self) -> bool {
        self.tokens
            .get(self.pos)
            .is_some_and(|t| matches!(t.tok, Tok::Pipe | Tok::KwWhere | Tok::ColonEq))
    }

    fn statement(&mut self) -> Result<Stmt> {
        if self.peek() != Some(&Tok::KwLet) {
            return Ok(Stmt::Expr(self.expr_inline()?));
        }
        self.let_statement()
    }

    /// `let p = e`, or `let p := e` in the new syntax.
    #[inline(never)]
    fn let_statement(&mut self) -> Result<Stmt> {
        let start = self.bump().span;
        let pattern = self.let_pattern()?;
        let ty = if self.eat(&Tok::Colon) {
            // In the old syntax the type stops at `=`; in the new one it
            // stops at `:=`, so it may contain `=`.
            let saved = std::mem::replace(&mut self.no_equals, self.syntax == Syntax::Old);
            let ty = self.expr_inline();
            self.no_equals = saved;
            Some(ty?)
        } else {
            None
        };
        let (equals, text) = self.binding_equals();
        if self.syntax == Syntax::New && self.peek() == Some(&Tok::Equals) {
            return Err(self.def_equals());
        }
        self.expect(equals, text)?;
        let value = self.expr()?;
        Ok(match pattern {
            Pattern::Var(name) => Stmt::Let(name, ty, value, start),
            pattern => Stmt::LetPattern(pattern, ty, value, start),
        })
    }

    /// The pattern after `let`: a constructor may take arguments without
    /// brackets (`let MkPair a b = p`), running to the `=` or `:`.
    fn let_pattern(&mut self) -> Result<Pattern> {
        if let Some(Tok::Upper(_)) = self.peek() {
            let start = self.here();
            let name = self.upper_q("a constructor")?;
            let mut args = Vec::new();
            while !matches!(
                self.peek(),
                Some(Tok::Equals | Tok::ColonEq | Tok::Colon) | None
            ) {
                args.push(self.pattern()?);
            }
            return Ok(Pattern::Ctor(name, args, start.to(self.prev_span())));
        }
        self.tuple_component()
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
            if self.syntax == Syntax::New {
                clauses.push(self.handler_clause()?);
            } else if self.eat(&Tok::KwReturn) {
                let var = self.lower("a name for the result")?;
                self.expect(Tok::Arrow, "`->`")?;
                let body = self.expr()?;
                clauses.push(Clause::Return { var, body });
            } else {
                let op = self.lower_q("an operation, or `return`")?;
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

    /// `match e, h : e2 with | p, q -> body | …`
    fn match_expr(&mut self, start: Span) -> Result<Expr> {
        let mut scrutinees = Vec::new();
        loop {
            let name = if matches!(self.peek(), Some(Tok::Lower(_)))
                && self.peek_at(1) == Some(&Tok::Colon)
            {
                let name = self.lower("a name")?;
                self.bump();
                Some(name)
            } else {
                None
            };
            let expr = self.expr_inline()?;
            scrutinees.push(Scrutinee { name, expr });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::KwWith, "`with`")?;
        let mut alts = Vec::new();
        // Alternatives on their own lines line up, as a handler's clauses do.
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
            let bar = self.bump().span;
            let mut patterns = vec![self.alt_pattern()?];
            while self.eat(&Tok::Comma) {
                patterns.push(self.alt_pattern()?);
            }
            if patterns.len() != scrutinees.len() {
                let (n, m) = (patterns.len(), scrutinees.len());
                return Err(error(
                    bar.to(self.prev_span()),
                    format!(
                        "this alternative has {n} pattern{}, but the `match` has {m} scrutinee{}",
                        if n == 1 { "" } else { "s" },
                        if m == 1 { "" } else { "s" },
                    ),
                ));
            }
            let (arrow, text) = self.case_arrow();
            self.expect(arrow, text)?;
            let body = self.expr()?;
            alts.push(Alt {
                span: bar.to(body.span()),
                patterns,
                body,
            });
        }
        if alts.is_empty() {
            return Err(self.unexpected("`|` and an alternative"));
        }
        Ok(Expr::Match {
            span: start.to(self.prev_span()),
            scrutinees,
            alts,
            kind: MatchKind::Match,
        })
    }

    /// A pattern of a `match` alternative: what may stand inside brackets in
    /// an equation, so a constructor's arguments need no parentheses
    /// (`Cons x Nil`).
    fn alt_pattern(&mut self) -> Result<Pattern> {
        if let Some(Tok::Upper(_)) = self.peek() {
            let start = self.here();
            let name = self.upper_q("a constructor")?;
            let mut args = Vec::new();
            while !matches!(
                self.peek(),
                Some(Tok::Comma | Tok::Arrow | Tok::FatArrow) | None
            ) {
                args.push(self.pattern()?);
            }
            return Ok(Pattern::Ctor(name, args, start.to(self.prev_span())));
        }
        self.tuple_component()
    }

    /// `\x (a, b) -> body`, after the `\`. Out of line, so that
    /// `expr_inline`, which every nested expression recurses through, keeps
    /// a small stack frame.
    #[inline(never)]
    fn lambda(&mut self, start: Span) -> Result<Expr> {
        // Each parameter is a name, with the pattern it stands for if it
        // was written as one.
        let mut params: Vec<(Name, Option<Pattern>)> = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::Lower(_)) => params.push((self.lower("a name")?, None)),
                Some(Tok::Underscore) => {
                    let span = self.bump().span;
                    let name = Name {
                        text: "_".to_string(),
                        span,
                    };
                    params.push((name, None));
                }
                Some(Tok::LParen)
                    if matches!(self.peek_at(1), Some(Tok::Lower(_)))
                        && self.peek_at(2) == Some(&Tok::Colon) =>
                {
                    let span = self.here().to(self.tokens[self.pos + 2].span);
                    return Err(error(
                        span,
                        "a lambda's parameter can't have a type here: annotate the lambda \
                             instead, `((\\x -> …) : A -> B)`",
                    ));
                }
                Some(Tok::LParen | Tok::LBrace | Tok::Upper(_) | Tok::Num(_)) => {
                    match self.pattern()? {
                        Pattern::Var(name) => params.push((name, None)),
                        pattern => {
                            let i = params.len();
                            let name = Name {
                                text: format!("%arg{i}"),
                                span: pattern.span(),
                            };
                            params.push((name, Some(pattern)));
                        }
                    }
                }
                _ => break,
            }
        }
        if params.is_empty() {
            return Err(self.unexpected("a parameter name"));
        }
        let (arrow, text) = self.case_arrow();
        self.expect(arrow, text)?;
        let body = self.expr()?;
        let span = start.to(body.span());
        if params.iter().all(|(_, p)| p.is_none()) {
            let names = params.into_iter().map(|(n, _)| n).collect();
            return Ok(Expr::Lam(names, Box::new(body), span));
        }
        let mut names = Vec::new();
        let mut scrutinees = Vec::new();
        let mut patterns = Vec::new();
        for (name, pattern) in params {
            if let Some(pattern) = pattern {
                scrutinees.push(Scrutinee {
                    name: None,
                    expr: Expr::Var(name.clone()),
                });
                patterns.push(pattern);
            }
            names.push(name);
        }
        let alt_span = patterns[0].span().to(body.span());
        let matched = Expr::Match {
            scrutinees,
            alts: vec![Alt {
                patterns,
                body,
                span: alt_span,
            }],
            span,
            kind: MatchKind::Lambda,
        };
        Ok(Expr::Lam(names, Box::new(matched), span))
    }

    fn expr_inline(&mut self) -> Result<Expr> {
        let start = self.here();
        if self.eat(&Tok::KwHandle) {
            return self.handle(start);
        }
        if self.eat(&Tok::KwMatch) {
            return self.match_expr(start);
        }
        if self.eat(&Tok::Backslash) {
            return self.lambda(start);
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
            // `then` and `else` may start a line, as long as it's indented at
            // least as far as the line `if` is on.
            let indent = self.line_indent(self.pos - 1);
            let cond = self.expr()?;
            self.expect_keyword(Tok::KwThen, "`then`", indent)?;
            let then = self.expr()?;
            self.expect_keyword(Tok::KwElse, "`else`", indent)?;
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
        self.deeper()?;
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
        let mut lhs = self.unary()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Star) => BinOp::Mul,
                Some(Tok::Slash) => BinOp::Div,
                Some(Tok::Percent) => BinOp::Mod,
                _ => return Ok(lhs),
            };
            self.bump();
            let rhs = self.unary()?;
            lhs = Expr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
    }

    /// A prefix minus (which may repeat), tighter than `*` and looser than
    /// application and dots: `-x.abs` is `-(x.abs)`, `-f x` is `-(f x)`.
    fn unary(&mut self) -> Result<Expr> {
        // A `match` as an operand: `1 + match n with | …`. Its last
        // alternative's body takes whatever follows.
        if self.peek() == Some(&Tok::KwMatch) {
            let start = self.bump().span;
            return self.match_expr(start);
        }
        if self.peek() == Some(&Tok::Minus) {
            self.deeper()?;
            let start = self.bump().span;
            let operand = self.unary()?;
            let span = start.to(operand.span());
            return Ok(Expr::Neg(Box::new(operand), span));
        }
        self.app()
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
                    | Tok::LBrace
                    | Tok::Underscore
            )
        )
    }

    /// An atom followed by any field accesses, `p.address.city`. The `.` is
    /// written with no space on either side.
    fn atom(&mut self) -> Result<Expr> {
        let mut expr = self.atom_base()?;
        while self.peek() == Some(&Tok::Dot) {
            let dot = self.tokens[self.pos].span;
            let field = match self.tokens.get(self.pos + 1) {
                Some(Token {
                    tok: Tok::Lower(text),
                    span,
                    ..
                }) if self.peek_at(1).is_some() => Name {
                    text: text.clone(),
                    span: *span,
                },
                _ => {
                    return Err(error(dot, "expected a field name after `.`")
                        .with_note("`.` is for field access, as in `p.name`"));
                }
            };
            if self.prev_span().end != dot.start || dot.end != field.span.start {
                return Err(
                    error(dot, "field access is written without spaces around the `.`")
                        .with_note(format!("write `….{}`", field.text)),
                );
            }
            self.pos += 2;
            expr = Expr::Field(Box::new(expr), field);
        }
        Ok(expr)
    }

    /// `{ name = e, age }` (a literal; `age` is punned) or `{ base | age = e }`
    /// (an update). A literal's fields are in the order written.
    fn record_expr(&mut self) -> Result<Expr> {
        let start = self.expect(Tok::LBrace, "`{`")?.span;
        let saved = std::mem::replace(&mut self.no_equals, false);
        let result = self.record_body(start);
        self.no_equals = saved;
        result
    }

    fn record_body(&mut self, start: Span) -> Result<Expr> {
        if self.peek() == Some(&Tok::RBrace) {
            let end = self.bump().span;
            return Ok(Expr::Record {
                base: None,
                fields: Vec::new(),
                span: start.to(end),
            });
        }
        let literal = matches!(self.peek(), Some(Tok::Lower(_)))
            && matches!(
                self.peek_at(1),
                Some(Tok::Equals | Tok::Comma | Tok::RBrace)
            );
        let base = if literal {
            None
        } else {
            let base = self.expr()?;
            self.expect(Tok::Pipe, "`|` and the fields to update")?;
            Some(Box::new(base))
        };
        let mut fields = Vec::new();
        loop {
            let name = self.lower("a field name")?;
            let value = if self.eat(&Tok::Equals) {
                self.expr()?
            } else {
                Expr::Var(name.clone())
            };
            fields.push((name, value));
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let end = self.expect(Tok::RBrace, "`,` or `}`")?.span;
        Ok(Expr::Record {
            base,
            fields,
            span: start.to(end),
        })
    }

    fn atom_base(&mut self) -> Result<Expr> {
        let span = self.here();
        match self.peek() {
            Some(Tok::Lower(_)) => Ok(Expr::Var(self.lower_q("an expression")?)),
            Some(Tok::Upper(_)) => Ok(Expr::Var(self.upper_q("an expression")?)),
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
                if self.peek() == Some(&Tok::Comma) {
                    return self.tuple_expr(inner, span);
                }
                if self.eat(&Tok::Colon) {
                    let ty = self.expr()?;
                    if self.peek() == Some(&Tok::Comma) {
                        return Err(self.tuple_annotation());
                    }
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
            Some(Tok::LBrace) => self.record_expr(),
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
        Tok::KwDef => "`def`".into(),
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
        Tok::KwMatch => "`match`".into(),
        Tok::KwReturn => "`return`".into(),
        Tok::KwLet => "`let`".into(),
        Tok::KwImport => "`import`".into(),
        Tok::LBrace => "`{`".into(),
        Tok::RBrace => "`}`".into(),
        Tok::FatArrow => "`=>`".into(),
        Tok::EqEq => "`==`".into(),
        Tok::Lt => "`<`".into(),
        Tok::Le => "`<=`".into(),
        Tok::KwIf => "`if`".into(),
        Tok::KwThen => "`then`".into(),
        Tok::KwElse => "`else`".into(),
        Tok::Dot => "`.`".into(),
        Tok::DotDot => "`..`".into(),
    }
}

fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic::error("E-PARSE", message.clone()).with_label(span, message)
}
