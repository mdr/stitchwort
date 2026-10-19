//! Recursive-descent parser for the surface syntax. See `docs/syntax.md`.
//!
//! Layout rule: a declaration starts at column 0, and every following line
//! that is indented belongs to it. Definitions are `def` and `theorem`
//! headers with a `:=` body or arms (`parser/declarations.rs`).
//!
//! Blocks: an expression that starts on a new line is a block, whose lines
//! start at that line's column. Each line is a statement (`let x := e`, a local
//! `def` or `theorem`, with its arms indented further, or an
//! expression run for its effects) and the last is the result. Lines indented
//! further continue the line above. A line at the block's column right after
//! one ending in an operator (like `->`) continues it too.

use crate::ast::{
    Alt, BinOp, Binder, CtorDecl, Decl, Expr, Import, LocalDef, MatchKind, Module, Name,
    NamespaceDecl, Pattern, Row, SECTION, Scrutinee,
};
use crate::lexer::{Tok, Token, lex};
use crate::stack::StackLimit;
use crate::{Diagnostic, FileId, Span};

mod declarations;

type Result<T> = std::result::Result<T, Diagnostic>;

/// Bytes of stack the parser may use when the caller doesn't say: safe on a
/// 2 MiB thread (Rust's default for spawned threads and tests), like the
/// core's default `Limits`.
pub const DEFAULT_STACK: usize = 1536 * 1024;

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
    let limit = StackLimit::from_here(stack);
    let tokens = lex(file, text).map_err(|d| vec![d])?;
    let mut namespace = None;
    let mut imports = Vec::new();
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    for group in split_decls(&tokens).map_err(|d| vec![d])? {
        let mut parser = Parser::new(group, file, text.len(), limit);
        if parser.peek() == Some(&Tok::KwNamespace) {
            if namespace.is_some() {
                errors.push(
                    error(group[0].span, "a file has only one namespace line").with_note(
                        "everything in a file goes in the namespace on its first line; to use another namespace, import from it or write its name in full",
                    ),
                );
                continue;
            }
            if !imports.is_empty() || !decls.is_empty() {
                errors.push(
                    error(
                        group[0].span,
                        "the namespace line goes at the top of the file",
                    )
                    .with_note("move it before the imports and declarations"),
                );
                continue;
            }
            match parser
                .namespace()
                .and_then(|decl| parser.finish().map(|()| decl))
            {
                Ok(decl) => namespace = Some(decl),
                Err(diagnostic) => errors.push(diagnostic),
            }
            continue;
        }
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
        match parser
            .decl()
            .and_then(|parsed| parser.finish().map(|()| parsed))
        {
            Ok(parsed) => decls.extend(parsed),
            Err(diagnostic) => errors.push(diagnostic),
        }
    }
    if errors.is_empty() {
        Ok(Module {
            namespace,
            imports,
            decls,
        })
    } else {
        Err(errors)
    }
}

/// Reads only a file's namespace line: `Some` if the file's first
/// declaration group is one, `None` if it starts with anything else. For
/// finding a file's namespace when the rest of it doesn't parse.
pub fn parse_namespace_line(file: FileId, text: &str) -> Result<Option<NamespaceDecl>> {
    let limit = StackLimit::from_here(DEFAULT_STACK);
    let tokens = lex(file, text)?;
    let groups = split_decls(&tokens)?;
    let Some(group) = groups.first() else {
        return Ok(None);
    };
    let mut parser = Parser::new(group, file, text.len(), limit);
    if parser.peek() != Some(&Tok::KwNamespace) {
        return Ok(None);
    }
    let decl = parser.namespace()?;
    parser.finish()?;
    Ok(Some(decl))
}

/// Parses an expression, using at most `stack` bytes of stack.
pub fn parse_expression_within(file: FileId, text: &str, stack: usize) -> Result<Expr> {
    let limit = StackLimit::from_here(stack);
    let tokens = lex(file, text)?;
    let mut parser = Parser::new(&tokens, file, text.len(), limit);
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

fn split_decls(tokens: &[Token]) -> Result<Vec<&[Token]>> {
    if let Some(first) = tokens.first()
        && first.column != 0
    {
        return Err(error(
            first.span,
            "declarations must start at the beginning of a line",
        ));
    }
    let starts: Vec<usize> = (0..tokens.len())
        .filter(|&i| tokens[i].column == 0)
        .collect();
    let mut groups = Vec::new();
    for (n, &start) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(tokens.len());
        groups.push(&tokens[start..end]);
    }
    Ok(groups)
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
    /// How deep the recursion may go.
    stack: StackLimit,
}

/// One line of a block.
enum Stmt {
    Let(Name, Option<Expr>, Expr, Span),
    /// `let (a, b) = e`: a pattern binding, desugared to a `match` in `block`.
    LetPattern(Pattern, Option<Expr>, Expr, Span),
    /// A local `def` or `theorem`; the span is where it starts.
    Def(LocalDef, Span),
    Expr(Expr),
}

impl<'t> Parser<'t> {
    fn new(tokens: &'t [Token], file: FileId, text_len: usize, stack: StackLimit) -> Self {
        let eof = tokens.last().map_or(text_len as u32, |t| t.span.end);
        Parser {
            tokens,
            pos: 0,
            file,
            eof,
            limit: None,
            allow: None,
            stack,
        }
    }

    /// `=>` after a lambda's parameters or an alternative's patterns, with a
    /// hint if it's the old syntax's `->`.
    fn expect_fat_arrow(&mut self, what: &str) -> Result<&'t Token> {
        if self.peek() == Some(&Tok::Arrow) {
            return Err(self
                .unexpected(what)
                .with_note("lambdas and arms use `=>`: `\\x => e`, `| p => e`"));
        }
        self.expect(Tok::FatArrow, what)
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
            && !self.continues_bracket(i)
    }

    /// Whether the token at `i`, a `,` or a closing bracket, is inside an
    /// open bracket: such a line continues it however far left it starts
    /// (`, "c"` or `]` on a line of its own below a list's `[`).
    #[inline(never)]
    fn continues_bracket(&self, i: usize) -> bool {
        if !matches!(
            self.tokens[i].tok,
            Tok::Comma | Tok::RBracket | Tok::RParen | Tok::RBrace
        ) {
            return false;
        }
        let depth = self.tokens[..i].iter().fold(0i64, |d, t| match t.tok {
            Tok::LBracket | Tok::LParen | Tok::LBrace => d + 1,
            Tok::RBracket | Tok::RParen | Tok::RBrace => d - 1,
            _ => d,
        });
        depth > 0
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
            if self.peek() == Some(&Tok::RParen) && items.len() >= 2 {
                break;
            }
            items.push(self.expr()?);
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
            if self.peek() == Some(&Tok::RParen) && items.len() >= 2 {
                break;
            }
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
            "to annotate one component, write `(a, (b: T))`; to annotate the pair, write \
             `((a, b): T)`",
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

    /// `namespace Day05`: the namespace a file's declarations go in.
    fn namespace(&mut self) -> Result<NamespaceDecl> {
        let start = self.expect(Tok::KwNamespace, "`namespace`")?.span;
        match self.peek() {
            Some(Tok::Upper(text)) => {
                let path = Name {
                    text: text.clone(),
                    span: self.here(),
                };
                self.bump();
                Ok(NamespaceDecl {
                    span: start.to(path.span),
                    path,
                })
            }
            Some(Tok::Lower(_)) => Err(error(
                self.here(),
                "each part of a namespace's name starts with a capital letter",
            )),
            _ => Err(self.unexpected("a namespace, such as `Day05`")),
        }
    }

    /// `import List (map, filter)`: a namespace, then the names to use from
    /// it, at least one; or `import List (..)` for all of them.
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
        let mixed = |dots: Span, path: &Name| {
            error(
                dots,
                format!(
                    "`..` imports everything from a namespace, so it goes on its own: `import {} (..)`",
                    path.text
                ),
            )
        };
        let mut items = Vec::new();
        let mut everything = None;
        if self.peek() == Some(&Tok::DotDot) {
            let dots = self.here();
            self.bump();
            if self.peek() != Some(&Tok::RParen) {
                return Err(mixed(dots, &path));
            }
            everything = Some(dots);
        }
        while everything.is_none() {
            match self.peek() {
                Some(Tok::Lower(text) | Tok::Upper(text)) if !text.contains('.') => {
                    items.push(Name {
                        text: text.clone(),
                        span: self.here(),
                    });
                    self.bump();
                }
                Some(Tok::DotDot) if !items.is_empty() => return Err(mixed(self.here(), &path)),
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
            everything,
            span: start.to(end),
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
            Some(Tok::Char(c)) => {
                let c = *c;
                self.bump();
                Ok(Pattern::Char(c, span))
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
                let mut tail = None;
                if self.peek() != Some(&Tok::RBracket) {
                    loop {
                        if self.peek() == Some(&Tok::RBracket) {
                            break;
                        }
                        if self.eat(&Tok::DotDot) {
                            // `..rest`: the tail pattern, which must be last.
                            tail = Some(self.pattern()?);
                            break;
                        }
                        items.push(self.list_component()?);
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                let end = self
                    .expect(
                        Tok::RBracket,
                        if tail.is_some() {
                            "`]`: a `..` tail must be the last item"
                        } else {
                            "`,` or `]`"
                        },
                    )?
                    .span;
                let mut list = tail.unwrap_or(Pattern::Nil(end));
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
                if self.peek() == Some(&Tok::RBrace) {
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

    fn data(&mut self) -> Result<Vec<Decl>> {
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
            if !matches!(self.peek(), Some(Tok::LBrace | Tok::Pipe)) {
                return self.type_synonym(start, name, params, sort);
            }
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
        Ok(vec![Decl::Data {
            span: start.to(self.prev_span()),
            name,
            params,
            sort,
            ctors,
            record,
        }])
    }

    /// A record's fields, `{ name : Text, age : Nat }`, as the one
    /// constructor of the data type `data`, named `%mk`, which source can't
    /// write (so `data.mk` is free for a function).
    fn record_fields(&mut self, data: &Name) -> Result<CtorDecl> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                if self.peek() == Some(&Tok::RBrace) {
                    break;
                }
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
            Some(Stmt::Def(_, span)) => {
                return Err(error(
                    span,
                    "a block must end with an expression, not a local `def` or `theorem`",
                ));
            }
            None => return Err(self.unexpected("an expression")),
        };
        // Whether `rest` is a `LocalDefs` made from the line after this one,
        // which another local definition joins.
        let mut grouping = false;
        for stmt in stmts.into_iter().rev() {
            let was_grouping = std::mem::replace(&mut grouping, false);
            rest = match stmt {
                Stmt::Def(def, span) => {
                    grouping = true;
                    if was_grouping
                        && let Expr::LocalDefs {
                            defs, span: end, ..
                        } = &mut rest
                    {
                        defs.insert(0, def);
                        *end = span.to(*end);
                        rest
                    } else {
                        Expr::LocalDefs {
                            defs: vec![def],
                            span: span.to(rest.span()),
                            body: Box::new(rest),
                        }
                    }
                }
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
        match self.peek() {
            Some(Tok::KwLet) => self.let_statement(),
            Some(Tok::KwDef | Tok::KwTheorem) => self.local_def(),
            Some(Tok::KwExport) => Err(error(
                self.here(),
                "local definitions can't be exported: only top-level ones are",
            )),
            _ => Ok(Stmt::Expr(self.expr_inline()?)),
        }
    }

    /// A local `def` or `theorem`, written as at top level, but with a body.
    #[inline(never)]
    fn local_def(&mut self) -> Result<Stmt> {
        let start = self.here();
        let mut decls = self.definition(start, false)?.into_iter();
        let signature = decls.next().expect("a definition has a signature");
        let equations: Vec<Decl> = decls.collect();
        if equations.is_empty() {
            return Err(error(
                signature.span(),
                "a local definition needs a body: `:=` and an expression, or arms starting with `|`",
            ));
        }
        Ok(Stmt::Def(
            LocalDef {
                signature,
                equations,
            },
            start,
        ))
    }

    /// `let p := e`, or `let p : T := e`; the type may contain `=`.
    #[inline(never)]
    fn let_statement(&mut self) -> Result<Stmt> {
        let start = self.bump().span;
        let pattern = self.let_pattern()?;
        let ty = if self.eat(&Tok::Colon) {
            Some(self.expr_inline()?)
        } else {
            None
        };
        if self.peek() == Some(&Tok::Equals) {
            return Err(self.def_equals());
        }
        self.expect(Tok::ColonEq, "`:=`")?;
        let value = self.expr()?;
        Ok(match pattern {
            Pattern::Var(name) => Stmt::Let(name, ty, value, start),
            pattern => Stmt::LetPattern(pattern, ty, value, start),
        })
    }

    /// The pattern after `let`: a constructor may take arguments without
    /// brackets (`let MkPair a b := p`), running to the `:=` or `:` (or a
    /// mistaken `=`, reported by `let_statement`).
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

    /// `handle e with | return x => … | op arg, k => …`
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
            clauses.push(self.handler_clause()?);
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

    /// `match e, h : e2 with | p, q => body | …`
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
            self.expect_fat_arrow("`=>`")?;
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

    /// `\x (a, b) => body`, after the `\`. Out of line, so that
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
                             instead, `((\\x => …): A -> B)`",
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
        self.expect_fat_arrow("`=>`")?;
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

    /// `if c then a else b`, after the `if`. Its own function, so the stack
    /// frame of the parser's recursive functions stays small (the nesting
    /// limit is measured in stack).
    #[inline(never)]
    fn if_expr(&mut self, start: Span) -> Result<Expr> {
        // `if h : P then …` binds a proof; `if c then …` tests a `Bool`.
        let binder =
            if matches!(self.peek(), Some(Tok::Lower(_))) && self.peek_at(1) == Some(&Tok::Colon) {
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
        Ok(Expr::If {
            binder,
            cond: Box::new(cond),
            then: Box::new(then),
            otherwise: Box::new(otherwise),
            span,
        })
    }

    /// `(x : A) -> B` or `[x : A] -> B`. Out of line, as `if_expr` is.
    #[inline(never)]
    fn pi_expr(&mut self, start: Span, implicit: bool) -> Result<Expr> {
        let (binder, auto) = if implicit {
            self.implicit_binder()?
        } else {
            (self.binder()?, false)
        };
        self.expect(Tok::Arrow, "`->`")?;
        let cod = self.result_type()?;
        let span = start.to(cod.span());
        Ok(Expr::Pi {
            names: binder.names,
            implicit,
            auto,
            dom: Box::new(binder.ty),
            cod: Box::new(cod),
            span,
        })
    }

    fn expr_inline(&mut self) -> Result<Expr> {
        let start = self.here();
        if self.eat(&Tok::KwHandle) {
            return self.handle(start);
        }
        if self.eat(&Tok::KwMatch) {
            return self.match_piped(start);
        }
        if self.eat(&Tok::Backslash) {
            return self.lambda(start);
        }
        if self.eat(&Tok::KwIf) {
            return self.if_expr(start);
        }
        let implicit = self.is_implicit_binder();
        if implicit || self.is_pi_binder() {
            return self.pi_expr(start, implicit);
        }
        let mut lhs = self.cmp_expr()?;
        if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
            self.logic_chain(&mut lhs)?;
        }
        if self.at_pipe() {
            self.pipe_chain(&mut lhs)?;
        }
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

    /// `a && b` and `a || b`: binding more loosely than comparisons, `&&`
    /// tighter than `||`, both grouping to the right. The operands are
    /// collected in a loop, so a chain costs one stack frame, not one per
    /// operator. `operand` is the first operand, already parsed, and is
    /// replaced by the whole chain. Every expression is parsed by the
    /// caller, and this is only entered at a `&&` or `||`, out of line and
    /// with nothing moved through the caller's frame, so the frames nested
    /// expressions pile up (and so how deeply they can nest) stay as they
    /// were: the `check-nested-parens` benchmark fails otherwise.
    #[inline(never)]
    fn logic_chain(&mut self, operand: &mut Expr) -> Result<()> {
        let first = std::mem::replace(operand, Expr::Prop(Span::NOWHERE));
        // `a || b && c || d` is gathered as `[[a], [b, c], [d]]`.
        let mut disjuncts = vec![vec![first]];
        loop {
            match self.peek() {
                Some(Tok::AndAnd) => {}
                Some(Tok::OrOr) => disjuncts.push(Vec::new()),
                _ => break,
            }
            self.bump();
            let operand = self.cmp_expr()?;
            disjuncts.last_mut().expect("never empty").push(operand);
        }
        let right = |op: BinOp, items: Vec<Expr>| {
            items
                .into_iter()
                .rev()
                .reduce(|rhs, lhs| Expr::Binary(op, Box::new(lhs), Box::new(rhs)))
                .expect("never empty")
        };
        let conjunctions = disjuncts
            .into_iter()
            .map(|items| right(BinOp::And, items))
            .collect();
        *operand = right(BinOp::Or, conjunctions);
        Ok(())
    }

    /// Whether a `|>` comes next: on this line, or starting a line (which a
    /// block would otherwise end the statement at, as with `then`; how far
    /// left it may start is checked by `pipe_chain`).
    #[inline(never)]
    fn at_pipe(&self) -> bool {
        self.tokens
            .get(self.pos)
            .is_some_and(|t| t.tok == Tok::PipeGt && (!self.is_stop(self.pos) || t.line_start))
    }

    /// `x |> f a |> g`: the loosest operator, grouping to the left, so a
    /// pipeline reads top to bottom. A line may start with `|>` to continue
    /// the expression, if it's indented at least as far as the line the
    /// expression starts on. The right side is an operand at the level of
    /// `||` (an application, usually), or a lambda, whose body takes the rest
    /// of the pipeline: `x |> \y => f y |> g` is `x |> \y => (f y |> g)`,
    /// which means the same as `(x |> \y => f y) |> g`. Out of line and in a
    /// loop, as `logic_chain` is.
    #[inline(never)]
    fn pipe_chain(&mut self, operand: &mut Expr) -> Result<()> {
        let mut lhs = std::mem::replace(operand, Expr::Prop(Span::NOWHERE));
        let first = lhs.span().start;
        let indent = self.line_indent(self.tokens.partition_point(|t| t.span.start < first));
        loop {
            let continues = match self.tokens.get(self.pos) {
                Some(t) if t.tok == Tok::PipeGt => {
                    !self.is_stop(self.pos) || (t.line_start && t.column >= indent)
                }
                _ => false,
            };
            if !continues {
                break;
            }
            self.bump();
            let rhs = if self.peek() == Some(&Tok::Backslash) {
                let start = self.bump().span;
                self.lambda(start)?
            } else {
                let mut rhs = self.cmp_expr()?;
                if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
                    self.logic_chain(&mut rhs)?;
                }
                rhs
            };
            lhs = piped(lhs, rhs);
        }
        *operand = lhs;
        Ok(())
    }

    /// A `match` starting an expression, then a pipeline it feeds: a `|>`
    /// line left of the last alternative's line (which would otherwise
    /// take it), but at least as far right as the `match`'s line.
    #[inline(never)]
    fn match_piped(&mut self, start: Span) -> Result<Expr> {
        let mut matched = self.match_expr(start)?;
        if self.at_pipe() {
            self.pipe_chain(&mut matched)?;
        }
        Ok(matched)
    }

    /// `a = b`, `a != b`, `a == b`, `a < b`, `a <= b`: not associative.
    fn cmp_expr(&mut self) -> Result<Expr> {
        let lhs = self.append_expr()?;
        let op = match self.peek() {
            Some(Tok::Equals) => BinOp::Eq,
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
        // A section's arguments are its own: `.drop 1` is `\x => x.drop 1`.
        let section = self.peek() == Some(&Tok::Dot);
        let mut expr = self.atom()?;
        while self.starts_atom() {
            if self.peek() == Some(&Tok::Dot) && self.tokens[self.pos].line_start {
                return Err(self.section_line());
            }
            let arg = self.atom()?;
            if section && let Expr::Lam(_, body, span) = &mut expr {
                *span = span.to(arg.span());
                let f = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
                **body = Expr::App(Box::new(f), Box::new(arg));
                continue;
            }
            expr = Expr::App(Box::new(expr), Box::new(arg));
        }
        Ok(expr)
    }

    /// A line starting with `.name`, as an argument of the line before.
    #[inline(never)]
    fn section_line(&self) -> Diagnostic {
        error(
            self.tokens[self.pos].span,
            "a line can't start with a method section",
        )
        .with_note(
            "`.name` on its own line would be an argument of the line above, not a call on \
             it: continue a pipeline with `|> .name`, or write `(.name)` to pass the section",
        )
    }

    /// Whether a method section `.name` starts at token `i`: a `.` right
    /// before a name, not right after the atom before it (that's a field,
    /// `p.name`).
    fn section_at(&self, i: usize) -> bool {
        let (Some(dot), Some(next)) = (self.tokens.get(i), self.tokens.get(i + 1)) else {
            return false;
        };
        dot.tok == Tok::Dot
            && matches!(next.tok, Tok::Lower(_))
            && dot.span.end == next.span.start
            && (i == 0 || self.tokens[i - 1].span.end != dot.span.start)
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
                    | Tok::StrStart(_)
                    | Tok::TypeU
                    | Tok::Prop
                    | Tok::LParen
                    | Tok::LBracket
                    | Tok::LBrace
                    | Tok::Underscore
            )
        ) || (self.peek() == Some(&Tok::Dot) && self.section_at(self.pos))
    }

    /// An atom followed by any field accesses, `p.address.city`. The `.` is
    /// written with no space on either side.
    fn atom(&mut self) -> Result<Expr> {
        let section = self.peek() == Some(&Tok::Dot);
        let start = self.here();
        let mut expr = self.atom_base()?;
        while self.peek() == Some(&Tok::Dot) && !self.section_at(self.pos) {
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
        if section {
            let span = start.to(expr.span());
            let param = Name {
                text: SECTION.into(),
                span: start,
            };
            expr = Expr::Lam(vec![param], Box::new(expr), span);
        }
        Ok(expr)
    }

    /// `.name`, starting a method section: its body's start, `%section.name`.
    #[inline(never)]
    fn section_start(&mut self) -> Result<Expr> {
        let dot = self.bump().span;
        let field = match self.tokens.get(self.pos) {
            Some(Token {
                tok: Tok::Lower(text),
                span,
                ..
            }) if span.start == dot.end && !text.contains('.') && self.peek().is_some() => Name {
                text: text.clone(),
                span: *span,
            },
            _ => {
                return Err(error(dot, "expected a name right after `.`").with_note(
                    "`.name args` is a method section, the function `\\x => x.name args`",
                ));
            }
        };
        self.pos += 1;
        let recv = Expr::Var(Name {
            text: SECTION.into(),
            span: dot,
        });
        Ok(Expr::Field(Box::new(recv), field))
    }

    /// `{ name = e, age }` (a literal; `age` is punned) or `{ base | age = e }`
    /// (an update). A literal's fields are in the order written.
    fn record_expr(&mut self) -> Result<Expr> {
        let start = self.expect(Tok::LBrace, "`{`")?.span;
        self.record_body(start)
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
            if self.peek() == Some(&Tok::RBrace) && !fields.is_empty() {
                break;
            }
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

    #[inline(never)]
    fn list_expr(&mut self, span: Span) -> Result<Expr> {
        self.bump();
        let mut items = Vec::new();
        if self.peek() != Some(&Tok::RBracket) {
            items.push(self.expr()?);
            while self.eat(&Tok::Comma) {
                if self.peek() == Some(&Tok::RBracket) {
                    break;
                }
                items.push(self.expr()?);
            }
        }
        let end = self.expect(Tok::RBracket, "`,` or `]`")?.span;
        Ok(Expr::List(items, span.to(end)))
    }

    /// `"a${x}b${y}c"`: text pieces joined with `++`, each interpolation
    /// becoming `(e).toText`. Empty pieces are left out.
    fn interpolated_str(&mut self) -> Result<Expr> {
        let token = self.bump();
        let (mut text, mut text_span) = match &token.tok {
            Tok::StrStart(text) => (text.clone(), token.span),
            _ => unreachable!("called at a StrStart"),
        };
        let mut items = Vec::new();
        loop {
            if !text.is_empty() {
                items.push(Expr::Str(text, text_span));
            }
            let value = self.expr()?;
            let next = self
                .tokens
                .get(self.pos)
                .cloned()
                .ok_or_else(|| self.unexpected("`}`"))?;
            let span = Span::new(self.file, text_span.end, next.span.start);
            items.push(Expr::Field(
                Box::new(value),
                Name {
                    text: "toText".into(),
                    span,
                },
            ));
            let (end, piece) = match &next.tok {
                Tok::StrMid(piece) => (false, piece.clone()),
                Tok::StrEnd(piece) => (true, piece.clone()),
                _ => return Err(self.unexpected("`}`")),
            };
            text_span = next.span;
            text = piece;
            self.bump();
            if end {
                if !text.is_empty() {
                    items.push(Expr::Str(text, text_span));
                }
                break;
            }
        }
        let mut items = items.into_iter().rev();
        let mut expr = items.next().expect("a string has at least one piece");
        for lhs in items {
            expr = Expr::Binary(BinOp::Append, Box::new(lhs), Box::new(expr));
        }
        Ok(expr)
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
            Some(Tok::StrStart(_)) => self.interpolated_str(),
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
                let inner = self.expr()?;
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
            Some(Tok::LBracket) => self.list_expr(span),
            Some(Tok::LBrace) => self.record_expr(),
            Some(Tok::Dot) => self.section_start(),
            _ => Err(self.unexpected("an expression")),
        }
    }
}

/// `lhs |> rhs`; when `rhs` is a method section, the call it stands for on
/// `lhs`: `xs |> .drop 1` is `xs.drop 1`, with no function in between.
#[inline(never)]
fn piped(lhs: Expr, mut rhs: Expr) -> Expr {
    if rhs.section_name().is_none() {
        return Expr::Pipe(Box::new(lhs), Box::new(rhs));
    }
    let Expr::Lam(_, body, _) = &mut rhs else {
        unreachable!("a section is a lambda");
    };
    let mut body = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
    let mut slot: &mut Expr = &mut body;
    while !matches!(slot, Expr::Field(r, _) if matches!(&**r, Expr::Var(v) if v.text == SECTION)) {
        match slot {
            Expr::App(f, _) | Expr::Field(f, _) => slot = f,
            _ => unreachable!("a section's body is a call on its parameter"),
        }
    }
    if let Expr::Field(r, _) = slot {
        **r = lhs;
    }
    body
}

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Lower(s) | Tok::Upper(s) => format!("`{s}`"),
        Tok::Num(n) => format!("`{n}`"),
        Tok::Str(s) => format!("`\"{s}\"`"),
        Tok::StrStart(_) | Tok::StrMid(_) | Tok::StrEnd(_) => "a text literal".into(),
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
        Tok::AndAnd => "`&&`".into(),
        Tok::OrOr => "`||`".into(),
        Tok::PipeGt => "`|>`".into(),
        Tok::KwAbility => "`ability`".into(),
        Tok::KwWhere => "`where`".into(),
        Tok::KwHandle => "`handle`".into(),
        Tok::KwWith => "`with`".into(),
        Tok::KwMatch => "`match`".into(),
        Tok::KwReturn => "`return`".into(),
        Tok::KwLet => "`let`".into(),
        Tok::KwImport => "`import`".into(),
        Tok::KwNamespace => "`namespace`".into(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;
    use crate::ast::Clause;

    fn parse(text: &str) -> Module {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_module(file, text).unwrap_or_else(|errors| panic!("{errors:?}"))
    }

    fn expression(text: &str) -> Result<Expr> {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_expression(file, text)
    }

    #[test]
    fn a_record_declaration_is_one_constructor() {
        let module =
            parse("type Person =\n  { name : Text\n  , age : Nat\n  }\n\ntype Empty = {}\n");
        let Decl::Data {
            ctors,
            record: true,
            ..
        } = &module.decls[0]
        else {
            panic!("expected a record");
        };
        assert_eq!(ctors.len(), 1);
        assert_eq!(ctors[0].name.text, "%mk");
        let names: Vec<&str> = ctors[0]
            .fields
            .iter()
            .map(|b| b.names[0].text.as_str())
            .collect();
        assert_eq!(names, ["name", "age"]);
        assert!(
            matches!(&module.decls[1], Decl::Data { ctors, record: true, .. } if ctors[0].fields.is_empty())
        );
    }

    #[test]
    fn record_literals_updates_and_puns() {
        let e = expression("{ b = f x, a }").unwrap();
        let Expr::Record {
            base: None, fields, ..
        } = &e
        else {
            panic!("expected a literal");
        };
        // In the order written; a pun is a variable.
        assert_eq!(fields[0].0.text, "b");
        assert!(matches!(&fields[0].1, Expr::App(..)));
        assert!(matches!(&fields[1].1, Expr::Var(n) if n.text == "a"));
        let e = expression("{ f p | age = 1 }").unwrap();
        let Expr::Record {
            base: Some(base),
            fields,
            ..
        } = &e
        else {
            panic!("expected an update");
        };
        assert!(matches!(**base, Expr::App(..)));
        assert_eq!(fields.len(), 1);
        let e = expression("{}").unwrap();
        assert!(matches!(&e, Expr::Record { base: None, fields, .. } if fields.is_empty()));
        // An update needs a field.
        assert!(expression("{ p | }").is_err());
    }

    #[test]
    fn field_access_binds_tighter_than_application() {
        // `f p.name q` is `f (p.name) q`.
        let e = expression("f p.name q").unwrap();
        let Expr::App(f, q) = &e else {
            panic!("expected an application");
        };
        assert!(matches!(**q, Expr::Var(_)));
        let Expr::App(_, arg) = &**f else {
            panic!("expected `f (p.name)`");
        };
        assert!(
            matches!(&**arg, Expr::Field(e, n) if n.text == "name" && matches!(**e, Expr::Var(_)))
        );
        // Chains, and parenthesised expressions.
        let e = expression("t.lead.name").unwrap();
        assert!(matches!(&e, Expr::Field(inner, _) if matches!(**inner, Expr::Field(..))));
        assert!(matches!(expression("(f x).age").unwrap(), Expr::Field(..)));
        // No spaces around the dot, and a field name after it.
        for bad in ["p. name", "p.Name", "p.1"] {
            assert!(expression(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn record_patterns() {
        let module = parse(
            "def f : R -> R -> Nat\n  | { name, age = Succ n, .. }, { tag = (Cons x xs) } => 0\n",
        );
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!("expected an equation");
        };
        let Pattern::Record {
            fields, rest: true, ..
        } = &patterns[0]
        else {
            panic!("expected a record pattern with `..`");
        };
        assert!(matches!(&fields[0].1, Pattern::Var(n) if n.text == "name"));
        assert!(
            matches!(&fields[1].1, Pattern::Ctor(n, args, _) if n.text == "Succ" && args.len() == 1)
        );
        assert!(matches!(&patterns[1], Pattern::Record { rest: false, .. }));
    }

    #[test]
    fn indented_lines_continue_a_declaration() {
        let module = parse(
            "type List (a : Type) : Type =\n  | Nil\n  | Cons (head : a) (tail : List a)\n\ndef length (a : Type) : List a -> Nat\n  | Nil => 0\n",
        );
        assert_eq!(module.decls.len(), 3);
        let Decl::Data { ctors, .. } = &module.decls[0] else {
            panic!("expected a data declaration");
        };
        assert_eq!(ctors.len(), 2);
    }

    #[test]
    fn export_attaches_to_the_definition_it_precedes() {
        let module = parse("export def f (n : Nat) : Nat := n\n");
        assert_eq!(module.decls.len(), 2);
        assert!(matches!(
            module.decls[0],
            Decl::Signature { export: true, .. }
        ));
    }

    #[test]
    fn equality_binds_looser_than_addition_and_tighter_than_arrows() {
        let module = parse("def p : (n : Nat) -> n + 0 = n -> Nat\n");
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

    #[test]
    fn or_binds_looser_than_and() {
        let Expr::Binary(BinOp::Or, a, rhs) = &expr("a || b && c") else {
            panic!("expected an or");
        };
        assert!(matches!(a.as_ref(), Expr::Var(..)));
        assert!(matches!(rhs.as_ref(), Expr::Binary(BinOp::And, ..)));
    }

    #[test]
    fn and_associates_right() {
        let Expr::Binary(BinOp::And, a, rhs) = &expr("a && b && c") else {
            panic!("expected an and");
        };
        assert!(matches!(a.as_ref(), Expr::Var(..)));
        assert!(matches!(rhs.as_ref(), Expr::Binary(BinOp::And, ..)));
    }

    #[test]
    fn and_then_or_groups_the_and_first() {
        let Expr::Binary(BinOp::Or, lhs, c) = &expr("a && b || c") else {
            panic!("expected an or");
        };
        assert!(matches!(lhs.as_ref(), Expr::Binary(BinOp::And, ..)));
        assert!(matches!(c.as_ref(), Expr::Var(..)));
    }

    #[test]
    fn comparisons_bind_tighter_than_and() {
        let Expr::Binary(BinOp::And, l, r) = &expr("x < y && y < z") else {
            panic!("expected an and");
        };
        assert!(matches!(l.as_ref(), Expr::Binary(BinOp::Lt, ..)));
        assert!(matches!(r.as_ref(), Expr::Binary(BinOp::Lt, ..)));
    }

    #[test]
    fn and_binds_tighter_than_arrow() {
        let Expr::Arrow(lhs, _) = &expr("a && b -> c") else {
            panic!("expected an arrow");
        };
        assert!(matches!(lhs.as_ref(), Expr::Binary(BinOp::And, ..)));
    }

    fn expr(text: &str) -> Expr {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_expression(file, text).unwrap_or_else(|e| panic!("{e:?}"))
    }

    #[test]
    fn multiplication_binds_tighter_than_addition_and_both_associate_left() {
        let Expr::Binary(BinOp::Sub, lhs, rhs) = &expr("a + b * c - d") else {
            panic!("expected `(a + b * c) - d`");
        };
        assert!(matches!(**rhs, Expr::Var(_)));
        let Expr::Binary(BinOp::Add, _, product) = &**lhs else {
            panic!("expected `a + (b * c)`");
        };
        assert!(matches!(**product, Expr::Binary(BinOp::Mul, ..)));
        assert!(matches!(expr("a / b % c"), Expr::Binary(BinOp::Mod, ..)));
        assert!(matches!(expr("a <= b + 1"), Expr::Binary(BinOp::Le, ..)));
        assert!(matches!(expr("a != b"), Expr::Binary(BinOp::Ne, ..)));
        assert!(matches!(expr("a == b + 1"), Expr::Binary(BinOp::EqEq, ..)));
        assert!(matches!(expr("a < b"), Expr::Binary(BinOp::Lt, ..)));
    }

    #[test]
    fn parses_tests() {
        let module = parse("test \"two \\\"words\\\"\" :=\n  1 + 1 = 2\n");
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
            "def div : (n d : Nat) -> [auto ok : d != 0] -> Nat\ndef absurd : Void -> a\n  | ()\n",
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
        let module = parse("def f : [auto : Type] -> auto\n");
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a signature");
        };
        assert!(matches!(ty, Expr::Pi { auto: false, .. }));
    }

    #[test]
    fn square_brackets_are_implicit_binders_named_arguments_or_lists() {
        let module =
            parse("def f : [a : Type] -> List a -> Nat\ndef x : Nat := g [a := Nat] [1] _\n");
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a signature");
        };
        assert!(matches!(ty, Expr::Pi { implicit: true, .. }));
        let Decl::Equation { rhs, .. } = &module.decls[2] else {
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
    fn colon_spacing_does_not_change_the_parse() {
        let shape = |text| crate::equivalence::parse_shape(text).expect(text);
        assert_eq!(
            shape("def f (n : Nat) : Nat := n\n"),
            shape("def f (n: Nat): Nat := n\n")
        );
        assert_eq!(
            shape("def f (n : Nat) : Nat := n\n"),
            shape("def f (n:Nat):Nat := n\n")
        );
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
        match parse(text)
            .decls
            .into_iter()
            .find(|d| matches!(d, Decl::Equation { .. }))
        {
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
        let body = rhs("def f (u : Nat) : Nat :=\n  let n := get ()\n  put (n +\n    1)\n  n\n");
        assert_eq!(lines(&body), ["let n", "_", "result"]);
        // On one line, or with one line, it's just the expression.
        assert!(matches!(
            rhs("def f (u : Nat) : Nat := g u\n"),
            Expr::App(..)
        ));
        assert!(matches!(
            rhs("def f (u : Nat) : Nat :=\n  g\n    u\n"),
            Expr::App(..)
        ));
    }

    #[test]
    fn a_line_ending_in_an_operator_continues() {
        let module = parse("def f : Nat ->\n  Nat ->\n  Nat\n");
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
        let body = rhs("def f (u : Nat) : Nat :=\n  let g := \\x =>\n    say x\n    x\n  g 1\n");
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
        let body = rhs("def f (u : Nat) : Nat :=\n  let r : s -> {e} a := run\n  r\n");
        let Expr::Let { ty: Some(ty), .. } = &body else {
            panic!("{body:?}")
        };
        assert!(matches!(ty.as_ref(), Expr::Arrow(..)));
    }

    #[test]
    fn rows_list_abilities_then_a_tail() {
        let row = |text: &str| {
            let module = parse(&format!("def f : Nat -> {text} Nat\n"));
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
            "def f (p : Nat) : Nat :=\n  handle p () with\n    | return x => x\n    | get (), k => k 1\n    | put s, k =>\n      k ()\n",
        );
        let Expr::Handle { clauses, .. } = &body else {
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
        assert!(
            matches!(rhs("def f (u : Nat) : Nat := g ()\n"), Expr::App(_, ref a) if matches!(**a, Expr::Unit(_)))
        );
        let module = parse("def f : () -> Nat\n  | () => 1\n");
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
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
        assert!(
            fails("def f (u : Nat) : Nat :=\n  let x := 1\n"),
            "a block ending in `let`"
        );
        assert!(
            fails("def f (p : Nat) : Nat := handle p with\n"),
            "a handler with no clauses"
        );
        assert!(
            fails("def f (p : Nat) : Nat := handle p with | get x, k -> k\n"),
            "a clause without `=>`"
        );
        assert!(fails("ability A where\n"), "an ability without operations");
        assert!(fails("def f : Nat -> {State s Nat\n"), "an unclosed row");
    }

    fn match_parts(e: &Expr) -> (&[Scrutinee], &[Alt]) {
        let Expr::Match {
            scrutinees, alts, ..
        } = e
        else {
            panic!("expected a `match`, got {e:?}");
        };
        (scrutinees, alts)
    }

    #[test]
    fn parses_match_expressions() {
        // Alternatives on their own lines.
        let e = rhs(
            "def f (xs : List Nat) : Nat :=\n  match xs with\n    | Nil => 0\n    | Cons x Nil => x\n    | _ => 2\n",
        );
        let (s, alts) = match_parts(&e);
        assert_eq!(s.len(), 1);
        assert!(s[0].name.is_none());
        assert_eq!(alts.len(), 3);
        assert!(matches!(&alts[1].patterns[0], Pattern::Ctor(_, args, _) if args.len() == 2));
        assert!(matches!(alts[2].patterns[0], Pattern::Wildcard(_)));

        // All on one line.
        let e = rhs("def f (xs : List Nat) : Nat := match xs with | Nil => 0 | Cons x _ => x\n");
        let (_, alts) = match_parts(&e);
        assert_eq!(alts.len(), 2);
        assert!(matches!(&alts[1].patterns[0], Pattern::Ctor(_, args, _) if args.len() == 2));

        // Two scrutinees.
        let e = rhs(
            "def f (a : Nat) (b : Nat) : Nat := match a, b with | Zero, _ => 0 | Succ m, Zero => m | _, _ => 1\n",
        );
        let (s, alts) = match_parts(&e);
        assert_eq!(s.len(), 2);
        assert!(alts.iter().all(|a| a.patterns.len() == 2));

        // A named equation.
        let e = rhs(
            "def f (xs : List Nat) : Nat := match h : length xs with | Zero => 0 | Succ k => k\n",
        );
        let (s, _) = match_parts(&e);
        assert_eq!(s[0].name.as_ref().unwrap().text, "h");
        assert!(matches!(s[0].expr, Expr::App(..)));

        // Other pattern forms.
        let e = rhs(
            "def f (p : Nat) : Nat := match p with | (a, b) => a | { name = n } => n | () => 0 | 0 => 1\n",
        );
        let (_, alts) = match_parts(&e);
        assert!(matches!(alts[0].patterns[0], Pattern::Tuple(..)));
        assert!(matches!(alts[1].patterns[0], Pattern::Record { .. }));
        assert!(matches!(alts[2].patterns[0], Pattern::Absurd(_)));
        assert!(matches!(alts[3].patterns[0], Pattern::Num(..)));

        // As an operand.
        let e = rhs("def f (n : Nat) : Nat := 1 + match n with | Zero => 0 | Succ k => k\n");
        let Expr::Binary(_, _, r) = &e else {
            panic!("{e:?}")
        };
        assert_eq!(match_parts(r).1.len(), 2);
    }

    #[test]
    fn nested_match_alternatives_line_up_by_column() {
        let e = rhs(
            "def f (a : Nat) (b : Nat) : Nat :=\n  match a with\n    | Zero =>\n      match b with\n        | Zero => 1\n        | Succ _ => 2\n    | Succ _ => 3\n",
        );
        let (_, outer) = match_parts(&e);
        assert_eq!(outer.len(), 2);
        assert_eq!(match_parts(&outer[0].body).1.len(), 2);
        assert!(is_num(&outer[1].body, 3));
    }

    #[test]
    fn rejects_malformed_matches() {
        let fails = |text: &str| rhs_of(text).is_err();
        assert!(
            fails("def f (xs : List Nat) : Nat := match xs with\n"),
            "no alternatives"
        );
        assert!(
            fails("def f (xs : List Nat) : Nat := match xs with | Nil, _ => 0\n"),
            "too many patterns"
        );
        assert!(
            fails("def f (a : Nat) (b : Nat) : Nat := match a, b with | Nil => 0\n"),
            "too few patterns"
        );
        let message = rhs_of("def f (xs : List Nat) : Nat := match xs with | Nil, _ => 0\n")
            .unwrap_err()
            .message;
        assert!(
            message.contains("has 2 patterns, but the `match` has 1 scrutinee"),
            "{message}"
        );
    }

    fn rhs_of(text: &str) -> Result<Expr> {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        let module = parse_module(file, text).map_err(|mut e| e.remove(0))?;
        match module.decls.into_iter().last() {
            Some(Decl::Equation { rhs: Some(rhs), .. }) => Ok(rhs),
            _ => panic!("expected an equation"),
        }
    }

    fn else_branch(e: &Expr) -> &Expr {
        let Expr::If { otherwise, .. } = e else {
            panic!("expected an `if`, got {e:?}");
        };
        otherwise
    }

    fn is_num(e: &Expr, n: u32) -> bool {
        matches!(e, Expr::Num(v, _) if *v == n.into())
    }

    #[test]
    fn else_on_its_own_line_continues_the_if() {
        let e = rhs_of("def g (n : Nat) : Nat :=\n  if n == 0 then 1\n  else 2\n").unwrap();
        assert!(is_num(else_branch(&e), 2));
    }

    #[test]
    fn then_and_else_chain_across_lines() {
        let text = "def g (n : Nat) : Nat :=\n  if a\n  then 1\n  else if b then 2\n  else if c then 3\n  else 4\n";
        let e = rhs_of(text).unwrap();
        assert!(is_num(else_branch(else_branch(else_branch(&e))), 4));
    }

    #[test]
    fn a_proof_binder_and_a_let_value_can_span_lines() {
        let e = rhs_of("def g (n : Nat) : Nat :=\n  if h : n != 0 then 1\n  else 2\n").unwrap();
        assert!(matches!(
            e,
            Expr::If {
                binder: Some(_),
                ..
            }
        ));
        let e = rhs_of("def g (n : Nat) : Nat :=\n  let x := if n == 0 then 1\n  else 2\n  x\n")
            .unwrap();
        assert!(matches!(e, Expr::Let { .. }));
    }

    #[test]
    fn the_inner_if_takes_the_closest_else() {
        let e = rhs_of(
            "def g (a : Nat) (b : Nat) : Nat :=\n  if a then\n    if b then 1\n    else 2\n  else 3\n",
        ).unwrap();
        assert!(is_num(else_branch(&e), 3));
    }

    #[test]
    fn an_else_left_of_its_if_is_explained() {
        let e = rhs_of("def g (a : Nat) : Nat :=\n  if a then\n    if a then 1\n  else 2\n")
            .unwrap_err();
        assert!(
            e.message.contains("starts a new statement"),
            "{}",
            e.message
        );
    }

    /// An expression's shape, fully bracketed.
    fn shape(e: &Expr) -> String {
        match e {
            Expr::Var(n) => n.text.clone(),
            Expr::Num(n, _) => n.to_string(),
            Expr::Neg(x, _) => format!("(- {})", shape(x)),
            Expr::App(f, a) => format!("({} {})", shape(f), shape(a)),
            Expr::Field(x, n) => format!("{}.{}", shape(x), n.text),
            Expr::Binary(op, a, b) => format!("({op:?} {} {})", shape(a), shape(b)),
            other => panic!("unexpected {other:?}"),
        }
    }

    fn shape_of(text: &str) -> String {
        shape(
            &rhs_of(&format!(
                "def g (x : Nat) (y : Nat) (f : Nat) (a : Nat) (b : Nat) : Nat := {text}\n"
            ))
            .unwrap(),
        )
    }

    #[test]
    fn prefix_minus_precedence() {
        let cases = [
            ("-x.abs", "(- x.abs)"),
            ("(-x).abs", "(- x).abs"),
            ("-f x", "(- (f x))"),
            ("f -x", "(Sub f x)"),
            ("-a * b", "(Mul (- a) b)"),
            ("a * -b", "(Mul a (- b))"),
            ("-18 % 100", "(Mod (- 18) 100)"),
            ("-(18 % 100)", "(- (Mod 18 100))"),
            ("a - -b", "(Sub a (- b))"),
            ("- -x", "(- (- x))"),
            ("a + -b * c", "(Add a (Mul (- b) c))"),
            ("f (-5)", "(f (- 5))"),
            ("f -5", "(Sub f 5)"),
        ];
        for (text, want) in cases {
            assert_eq!(shape_of(text), want, "{text}");
        }
        // `--` starts a comment.
        assert_eq!(shape_of("a --b"), "a");
    }

    #[test]
    fn negative_number_patterns() {
        let module =
            parse("def f : Int -> Nat -> Maybe Int -> Nat\n  | (-1), 0, (Just (-20)) => 1\n");
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(matches!(&patterns[0], Pattern::NegNum(n, _) if *n == 1u32.into()));
        assert!(matches!(&patterns[1], Pattern::Num(..)));
        let Pattern::Ctor(_, args, _) = &patterns[2] else {
            panic!()
        };
        assert!(matches!(&args[0], Pattern::NegNum(n, _) if *n == 20u32.into()));
        for bad in [
            "def f : Int -> Nat\n  | (-x) => 1\n",
            "def f : Int -> Nat\n  | (- - 1) => 1\n",
            "def f : Int -> Nat\n  | (-1 + 2) => 1\n",
        ] {
            let mut sources = SourceMap::new();
            let file = sources.add("test.sw", bad);
            assert!(parse_module(file, bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn parses_tuples() {
        // Components nest to the right; `()` and `(e)` are unchanged.
        let e = rhs("def f : Nat := (1, 2, 3)\n");
        let Expr::Tuple(a, rest, _) = &e else {
            panic!("{e:?}")
        };
        assert!(matches!(**a, Expr::Num(..)));
        assert!(matches!(**rest, Expr::Tuple(..)));
        let e = rhs("def f : Nat := ((1, 2), 3)\n");
        assert!(matches!(&e, Expr::Tuple(a, b, _)
            if matches!(**a, Expr::Tuple(..)) && matches!(**b, Expr::Num(..))));
        assert!(matches!(rhs("def f : Nat := ()\n"), Expr::Unit(_)));
        assert!(matches!(rhs("def f : Nat := (1)\n"), Expr::Num(..)));
        assert!(matches!(rhs("def f : Nat := (1 : Nat)\n"), Expr::Ann(..)));
        // A tuple is a function's domain, and `(x : A)` is still a binder.
        assert!(matches!(&rhs("def f : Nat := (A, B) -> C\n"),
            Expr::Arrow(d, _) if matches!(**d, Expr::Tuple(..))));
        assert!(matches!(
            rhs("def f : Nat := (x : A) -> B\n"),
            Expr::Pi { .. }
        ));
        // The tuple's span covers its brackets.
        let e = rhs("def f : Nat := (1, 2, 3)\n");
        assert_eq!((e.span().start, e.span().end), (15, 24));
    }

    #[test]
    fn parses_list_patterns() {
        let module = parse(
            "def f : A -> B -> C -> D -> E -> Nat\n  | [], [a], [a, b], [Just x, (-1)], (xs, [y]) => a\n",
        );
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(matches!(patterns[0], Pattern::Nil(_)));
        assert!(matches!(&patterns[1], Pattern::Cons(_, t, _) if matches!(**t, Pattern::Nil(_))));
        let Pattern::Cons(_, rest, _) = &patterns[2] else {
            panic!()
        };
        assert!(matches!(&**rest, Pattern::Cons(_, t, _) if matches!(**t, Pattern::Nil(_))));
        let Pattern::Cons(head, _, _) = &patterns[3] else {
            panic!()
        };
        assert!(matches!(&**head, Pattern::Ctor(_, args, _) if args.len() == 1));
        assert!(
            matches!(&patterns[4], Pattern::Tuple(_, r, _) if matches!(**r, Pattern::Cons(..)))
        );
    }

    #[test]
    fn parses_tuple_patterns() {
        let module = parse(
            "def f : A -> B -> C -> Nat\n  | (a, b, c), ((d, e) , _), (Cons (x, y) ys) => a\n",
        );
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(
            matches!(&patterns[0], Pattern::Tuple(_, r, _) if matches!(**r, Pattern::Tuple(..)))
        );
        assert!(
            matches!(&patterns[1], Pattern::Tuple(l, _, _) if matches!(**l, Pattern::Tuple(..)))
        );
        assert!(matches!(&patterns[2], Pattern::Ctor(_, args, _)
            if matches!(args[0], Pattern::Tuple(..))));
    }

    #[test]
    fn parses_a_constructor_as_a_tuples_first_component() {
        let module = parse("def f : A -> Nat\n  | (Just a, b) => a\n");
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(matches!(&patterns[0], Pattern::Tuple(l, _, _)
            if matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1)));

        let e = rhs("def f (p : Nat) : Nat :=\n  let (Just a, b) := p\n  a\n");
        let (_, p, _) = let_parts(&e);
        assert!(matches!(p, Pattern::Tuple(l, _, _)
            if matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1)));
    }

    #[test]
    fn parses_negative_numbers_in_tuple_patterns() {
        let text = "def f : A -> B -> C -> Nat\n  | (-1, 0), (0, -2), (-3) => a\n";
        let module = parse(text);
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(matches!(&patterns[0], Pattern::Tuple(l, _, _)
            if matches!(&**l, Pattern::NegNum(n, _) if *n == 1u32.into())));
        assert!(matches!(&patterns[1], Pattern::Tuple(_, r, _)
            if matches!(&**r, Pattern::NegNum(n, _) if *n == 2u32.into())));
        // `(-3)` still spans the whole bracketed pattern.
        let Pattern::NegNum(n, span) = &patterns[2] else {
            panic!()
        };
        assert!(*n == 3u32.into());
        let start = text.find("(-3)").unwrap() as u32;
        assert_eq!((span.start, span.end), (start, start + 4));
        let bad = "def f : A -> Nat\n  | (-x, 0) => a\n";
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", bad);
        assert!(parse_module(file, bad).is_err(), "{bad}");
    }

    #[test]
    fn rejects_bad_tuples() {
        for bad in [
            "def f : Nat := (1,)\n",
            "def f : Nat := (a, b : T)\n",
            "def f : Nat := (a : T, b)\n",
            "def f : A -> Nat\n  | (a,) => a\n",
        ] {
            let mut sources = SourceMap::new();
            let file = sources.add("test.sw", bad);
            assert!(parse_module(file, bad).is_err(), "{bad}");
        }
    }

    /// A `let`-pattern's match: its scrutinee, pattern and body.
    fn let_parts(e: &Expr) -> (&Expr, &Pattern, &Expr) {
        let Expr::Match {
            scrutinees,
            alts,
            kind: MatchKind::Let,
            ..
        } = e
        else {
            panic!("expected a `let` match, got {e:?}");
        };
        assert_eq!(scrutinees.len(), 1);
        assert_eq!(alts.len(), 1);
        (&scrutinees[0].expr, &alts[0].patterns[0], &alts[0].body)
    }

    #[test]
    fn parses_let_patterns() {
        let e = rhs("def f (e : Nat) : Nat :=\n  let (a, b) := e\n  a\n");
        let (s, p, body) = let_parts(&e);
        assert!(matches!(s, Expr::Var(_)));
        assert!(matches!(p, Pattern::Tuple(..)));
        assert!(matches!(body, Expr::Var(_)));

        let e = rhs("def f (p : Nat) : Nat :=\n  let MkPair a b := p\n  a\n");
        let (_, p, _) = let_parts(&e);
        assert!(matches!(p, Pattern::Ctor(_, args, _) if args.len() == 2));

        let e = rhs("def f (p : Nat) : Nat :=\n  let Pair.MkPair a b := p\n  a\n");
        let (_, p, _) = let_parts(&e);
        assert!(
            matches!(p, Pattern::Ctor(n, args, _) if args.len() == 2 && n.text == "Pair.MkPair")
        );

        let e = rhs("def f (r : Nat) : Nat :=\n  let { x, .. } := r\n  x\n");
        let (_, p, _) = let_parts(&e);
        assert!(matches!(p, Pattern::Record { rest: true, .. }));

        let e = rhs("def f (e : Nat) : Nat :=\n  let (a, b) : (Nat, Nat) := e\n  a\n");
        let (s, _, _) = let_parts(&e);
        assert!(matches!(s, Expr::Ann(..)));

        let e = rhs("def f (e : Nat) : Nat :=\n  let _ := e\n  0\n");
        let (_, p, _) = let_parts(&e);
        assert!(matches!(p, Pattern::Wildcard(_)));

        // Plain lets are unchanged.
        for text in [
            "def f (e : Nat) : Nat :=\n  let x := e\n  x\n",
            "def f (e : Nat) : Nat :=\n  let (x) := e\n  x\n",
        ] {
            assert!(matches!(rhs(text), Expr::Let { .. }), "{text}");
        }

        // Later lines nest inside the match.
        let e = rhs("def f (e : Nat) : Nat :=\n  let (a, b) := e\n  let c := a\n  c\n");
        let (_, _, body) = let_parts(&e);
        assert!(matches!(body, Expr::Let { .. }));
    }

    #[test]
    fn parses_lambda_patterns() {
        let lam = |text: &str| match &rhs(text) {
            Expr::Lam(names, body, _) => (names.clone(), body.as_ref().clone()),
            other => panic!("expected a lambda, got {other:?}"),
        };
        let lambda_match = |body: &Expr| match body {
            Expr::Match {
                scrutinees,
                alts,
                kind: MatchKind::Lambda,
                ..
            } => (scrutinees.len(), alts[0].patterns.len()),
            other => panic!("expected a lambda match, got {other:?}"),
        };

        let (names, body) = lam("def f : Nat := \\(a, b) => a\n");
        assert_eq!(names[0].text, "%arg0");
        assert_eq!(lambda_match(&body), (1, 1));

        let (names, body) = lam("def f : Nat := \\acc (k, v) => acc\n");
        let texts: Vec<_> = names.iter().map(|n| n.text.as_str()).collect();
        assert_eq!(texts, ["acc", "%arg1"]);
        assert_eq!(lambda_match(&body), (1, 1));

        let (names, body) = lam("def f : Nat := \\{ name, .. } => name\n");
        assert_eq!(names[0].text, "%arg0");
        assert_eq!(lambda_match(&body), (1, 1));

        let (_, body) = lam("def f : Nat := \\(MkPair a b) => a\n");
        assert_eq!(lambda_match(&body), (1, 1));

        let (names, body) = lam("def f : Nat := \\(a, b) (c, d) => a\n");
        assert_eq!(names.len(), 2);
        assert_eq!(lambda_match(&body), (2, 2));

        // Plain parameters are unchanged.
        let (names, body) = lam("def f : Nat := \\x y => x\n");
        assert_eq!(names.len(), 2);
        assert!(matches!(body, Expr::Var(_)));
        let (names, body) = lam("def f : Nat := \\(x) _ => x\n");
        assert_eq!(names.len(), 2);
        assert!(matches!(body, Expr::Var(_)));
    }

    #[test]
    fn rejects_bad_pattern_bindings() {
        let message = rhs_of("def f : Nat := \\(x : Nat) => x\n")
            .unwrap_err()
            .message;
        assert!(message.contains("can't have a type"), "{message}");
        assert!(rhs_of("def f (e : Nat) : Nat :=\n  let (a, b) := e\n").is_err());
        assert!(rhs_of("def f (e : Nat) : Nat :=\n  let (a, b)\n  e\n").is_err());
    }

    /// Like `shape`, for the expressions pipelines are made of.
    fn pshape(e: &Expr) -> String {
        match e {
            Expr::Var(n) => n.text.clone(),
            Expr::Num(n, _) => n.to_string(),
            Expr::App(f, a) => format!("({} {})", pshape(f), pshape(a)),
            Expr::Field(x, n) => format!("{}.{}", pshape(x), n.text),
            Expr::Binary(op, a, b) => format!("({op:?} {} {})", pshape(a), pshape(b)),
            Expr::Pipe(a, b) => format!("(|> {} {})", pshape(a), pshape(b)),
            Expr::Arrow(a, b) => format!("(-> {} {})", pshape(a), pshape(b)),
            Expr::Lam(names, body, _) => {
                let names: Vec<&str> = names.iter().map(|n| n.text.as_str()).collect();
                format!("(\\{} {})", names.join(" "), pshape(body))
            }
            Expr::List(xs, _) => {
                let xs: Vec<String> = xs.iter().map(pshape).collect();
                format!("[{}]", xs.join(" "))
            }
            Expr::Let {
                name, value, body, ..
            } => format!("(let {} {} {})", name.text, pshape(value), pshape(body)),
            Expr::Match {
                scrutinees, alts, ..
            } => {
                let s: Vec<String> = scrutinees.iter().map(|s| pshape(&s.expr)).collect();
                let a: Vec<String> = alts.iter().map(|a| pshape(&a.body)).collect();
                format!("(match {} | {})", s.join(","), a.join(" | "))
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    fn pipe_shape(text: &str) -> String {
        pshape(&rhs_of(&format!("def g : Nat := {text}\n")).unwrap())
    }

    /// A definition's body, written on the lines after `def g (x : Nat) : Nat :=`.
    fn pipe_body(body: &str) -> String {
        pshape(&rhs_of(&format!("def g (x : Nat) : Nat :=\n{body}\n")).unwrap())
    }

    #[test]
    fn pipe_is_looser_than_every_operator_but_the_arrow() {
        let cases = [
            ("x |> f", "(|> x f)"),
            ("x |> f a b", "(|> x ((f a) b))"),
            ("a + b |> f", "(|> (Add a b) f)"),
            ("a ++ b |> f", "(|> (Append a b) f)"),
            ("a || b |> f", "(|> (Or a b) f)"),
            ("a && b |> f", "(|> (And a b) f)"),
            ("a = b |> f", "(|> (Eq a b) f)"),
            ("x |> f a == y", "(|> x (EqEq (f a) y))"),
            ("x |> f || y", "(|> x (Or f y))"),
            ("x |> f |> g", "(|> (|> x f) g)"),
            ("x |> f |> g |> h", "(|> (|> (|> x f) g) h)"),
            ("x |> f -> T", "(-> (|> x f) T)"),
            ("A -> x |> f", "(-> A (|> x f))"),
            ("(x |> f) = y", "(Eq (|> x f) y)"),
            ("x |> (f = y)", "(|> x (Eq f y))"),
            ("[a |> f, b]", "[(|> a f) b]"),
        ];
        for (text, want) in cases {
            assert_eq!(pipe_shape(text), want, "{text}");
        }
    }

    #[test]
    fn a_lambda_on_the_right_takes_the_rest_of_the_pipeline() {
        let cases = [
            ("x |> \\y => f y", "(|> x (\\y (f y)))"),
            ("x |> \\y => f y |> g", "(|> x (\\y (|> (f y) g)))"),
            ("x |> f |> \\y => y + 1", "(|> (|> x f) (\\y (Add y 1)))"),
            (
                "x |> List.map (\\y => y |> f)",
                "(|> x (List.map (\\y (|> y f))))",
            ),
        ];
        for (text, want) in cases {
            assert_eq!(pipe_shape(text), want, "{text}");
        }
    }

    fn section_shape(text: &str) -> String {
        pshape(&expression(text).unwrap())
    }

    #[test]
    fn a_method_section_is_a_lambda_over_a_dot_call() {
        let cases = [
            (".name", "(\\%section %section.name)"),
            // The head section takes its arguments.
            (".drop 1", "(\\%section (%section.drop 1))"),
            (".fold a b", "(\\%section ((%section.fold a) b))"),
            // Chains.
            (".name.length", "(\\%section %section.name.length)"),
            // As an argument it takes none, unless it's in brackets.
            (
                "List.map .name ps",
                "((List.map (\\%section %section.name)) ps)",
            ),
            (
                "ps.map (.greet h)",
                "(ps.map (\\%section (%section.greet h)))",
            ),
            ("(.split c)", "(\\%section (%section.split c))"),
            // A space before the dot makes it a section; none, a field.
            ("f p .name", "((f p) (\\%section %section.name))"),
            ("f p.name", "(f p.name)"),
        ];
        for (text, want) in cases {
            assert_eq!(section_shape(text), want, "{text}");
        }
    }

    #[test]
    fn a_section_in_a_pipe_is_a_plain_dot_call() {
        // No lambda and no `Pipe`: the same tree as writing the calls out.
        let cases = [
            ("xs |> .drop 1", "(xs.drop 1)"),
            ("xs |> .name", "xs.name"),
            ("xs |> .drop 1 |> .sum", "(xs.drop 1).sum"),
            ("xs |> .name.length", "xs.name.length"),
            ("xs |> .drop 1 |> f", "(|> (xs.drop 1) f)"),
        ];
        for (text, want) in cases {
            assert_eq!(section_shape(text), want, "{text}");
        }
        assert_eq!(section_shape("xs |> .drop 1"), section_shape("xs.drop 1"));
        assert_eq!(
            section_shape("xs |> .drop 1 |> .sum"),
            section_shape("(xs.drop 1).sum")
        );
    }

    #[test]
    fn a_pipe_line_may_start_with_a_section() {
        let want = "(x.map f).sum";
        assert_eq!(pipe_body("  x\n    |> .map f\n    |> .sum"), want);
        assert_eq!(pipe_body("  x\n  |> .map f\n  |> .sum"), want);
        assert_eq!(pipe_body("  x |> .map f\n    |> .sum"), want);
    }

    #[test]
    fn a_line_cant_start_with_a_section_as_an_argument() {
        let err = parse_error("def g (x : Nat) : Nat :=\n  foo x\n    .map f\n");
        assert!(
            err.message
                .contains("a line can't start with a method section"),
            "{}",
            err.message
        );
    }

    #[test]
    fn a_section_needs_a_lowercase_name_right_after_the_dot() {
        for bad in [". name", ".Name", ".1", "(. name)", "f .Name"] {
            assert!(expression(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn a_line_starting_with_a_pipe_continues_the_expression() {
        let want = "(|> (|> x f) g)";
        // Deeper than the expression, and at the block's own column.
        assert_eq!(pipe_body("  x\n    |> f\n    |> g"), want);
        assert_eq!(pipe_body("  x\n  |> f\n  |> g"), want);
        assert_eq!(pipe_body("  x |> f\n    |> g"), want);
        assert_eq!(pipe_body("  x |> f\n  |> g"), want);
        assert_eq!(pipe_body("  x\n    |> f\n  |> g"), want);
        // Inside a `let` block, the rest of the block is the body.
        assert_eq!(
            pipe_body("  let y := x\n  y\n  |> f\n  |> g"),
            "(let y x (|> (|> y f) g))"
        );
        assert_eq!(
            pipe_body("  let y := x\n    |> f\n  y |> g"),
            "(let y (|> x f) (|> y g))"
        );
        assert_eq!(pipe_body("  x + 1\n  |> f"), "(|> (Add x 1) f)");
    }

    #[test]
    fn a_pipe_is_not_a_bar() {
        // `|` still separates the arms of a definition and a `match`.
        let module = parse("def f : Nat -> Nat\n  | 0 => 1 |> g\n  | n => n |> h\n");
        let arms: Vec<String> = module
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::Equation { rhs: Some(rhs), .. } => Some(pshape(rhs)),
                _ => None,
            })
            .collect();
        assert_eq!(arms, ["(|> 1 g)", "(|> n h)"]);
        assert_eq!(
            pipe_body("  match x with\n    | 0 => a |> f\n    | n => n |> g"),
            "(match x | (|> a f) | (|> n g))"
        );
        // `||` is still `Or`, and a row's `|` still has its tail after it.
        assert_eq!(pipe_shape("a || b"), "(Or a b)");
        let module = parse("def f (h : Nat -> {IO | e} Nat) : Nat := 1\n");
        assert!(matches!(module.decls.last(), Some(Decl::Equation { .. })));
        let module = parse("def f (h : Nat -> {IO | e} Nat) : Nat :=\n  1\n  |> g\n");
        assert!(matches!(module.decls.last(), Some(Decl::Equation { .. })));
    }

    #[test]
    fn a_pipe_after_a_match_pipes_the_whole_match_or_the_last_body() {
        // Left of the last alternative's body, at least at the `match` line:
        // the whole match.
        assert_eq!(
            pipe_body("  match x with\n    | 0 => a\n    | n => n\n  |> f"),
            "(|> (match x | a | n) f)"
        );
        // At the alternatives' own column it already belongs to the last body.
        assert_eq!(
            pipe_body("  match x with\n    | 0 => a\n    | n => n\n    |> f"),
            "(match x | a | (|> n f))"
        );
        // Under the last alternative's body: just that body.
        assert_eq!(
            pipe_body("  match x with\n    | 0 => a\n    | n => g n\n      |> f"),
            "(match x | a | (|> (g n) f))"
        );
        // The scrutinee can be piped.
        assert_eq!(
            pipe_body("  match x |> f with\n    | _ => a"),
            "(match (|> x f) | a)"
        );
    }

    // Local definitions in blocks

    /// The names of a `LocalDefs`' definitions and its body.
    fn local(e: &Expr) -> (Vec<String>, &Expr) {
        let Expr::LocalDefs { defs, body, .. } = e else {
            panic!("expected local definitions, got {e:?}");
        };
        let names = defs
            .iter()
            .map(|d| match &d.signature {
                Decl::Signature { name, .. } => name.text.to_string(),
                other => panic!("{other:?}"),
            })
            .collect();
        (names, body)
    }

    fn parse_error(text: &str) -> Diagnostic {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_module(file, text).unwrap_err().remove(0)
    }

    #[test]
    fn a_local_def_with_arms_then_the_result() {
        let body = rhs(
            "def sumTo (n : Nat) : Nat :=\n  let start := 0\n  def go : Nat -> Nat -> Nat\n    | Zero, acc => acc\n    | Succ k, acc => go k (acc + Succ k)\n  go n start\n",
        );
        assert_eq!(lines(&body), ["let start", "result"]);
        let Expr::Let { body, .. } = &body else {
            panic!()
        };
        let (names, rest) = local(body);
        assert_eq!(names, ["go"]);
        assert!(matches!(rest, Expr::App(..)), "{rest:?}");
        let Expr::LocalDefs { defs, .. } = body.as_ref() else {
            panic!()
        };
        assert_eq!(defs[0].equations.len(), 2);
    }

    #[test]
    fn a_local_def_with_a_body_and_a_local_theorem() {
        let body = rhs(
            "def f (n : Nat) : Nat :=\n  def double (x : Nat) : Nat := x + x\n  theorem t : double 0 = 0 := refl\n  double n\n",
        );
        let (names, rest) = local(&body);
        assert_eq!(names, ["double", "t"]);
        assert!(matches!(rest, Expr::App(..)), "{rest:?}");
        let Expr::LocalDefs { defs, .. } = &body else {
            panic!()
        };
        assert!(matches!(
            defs[1].signature,
            Decl::Signature { theorem: true, .. }
        ));
        // A `:=` body on a further-indented block.
        let body = rhs(
            "def f (n : Nat) : Nat :=\n  def g (x : Nat) : Nat :=\n    let y := x\n    y\n  g n\n",
        );
        let (names, _) = local(&body);
        assert_eq!(names, ["g"]);
    }

    #[test]
    fn interleaved_lets_and_defs_nest() {
        let body = rhs(
            "def f (n : Nat) : Nat :=\n  let a := 1\n  def g (x : Nat) : Nat := x\n  let b := 2\n  def h (x : Nat) : Nat := x\n  h b\n",
        );
        let Expr::Let { body, .. } = &body else {
            panic!("{body:?}")
        };
        let (names, rest) = local(body);
        assert_eq!(names, ["g"]);
        let Expr::Let { body, .. } = rest else {
            panic!("{rest:?}")
        };
        let (names, rest) = local(body);
        assert_eq!(names, ["h"]);
        assert!(matches!(rest, Expr::App(..)));
    }

    #[test]
    fn local_defs_nest_in_blocks_arms_and_alternatives() {
        // In a nested block.
        let body = rhs(
            "def f (n : Nat) : Nat :=\n  let r :=\n    def g (x : Nat) : Nat := x\n    g n\n  r\n",
        );
        let Expr::Let { value, .. } = &body else {
            panic!("{body:?}")
        };
        assert_eq!(local(value).0, ["g"]);
        // In an arm body: the outer arms still parse.
        let module = parse(
            "def f : Nat -> Nat\n  | Zero =>\n    def g (x : Nat) : Nat := x\n    g 1\n  | Succ k =>\n    def h : Nat -> Nat\n      | Zero => 0\n      | Succ j => j\n    h k\n",
        );
        let arms: Vec<_> = module
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::Equation { rhs: Some(r), .. } => Some(r),
                _ => None,
            })
            .collect();
        assert_eq!(arms.len(), 2);
        assert_eq!(local(arms[0]).0, ["g"]);
        assert_eq!(local(arms[1]).0, ["h"]);
        // In a match alternative.
        let body = rhs(
            "def f (n : Nat) : Nat :=\n  match n with\n    | Zero =>\n      def g (x : Nat) : Nat := x\n      g 1\n    | Succ k => k\n",
        );
        let Expr::Match { alts, .. } = &body else {
            panic!("{body:?}")
        };
        assert_eq!(alts.len(), 2);
        assert_eq!(local(&alts[0].body).0, ["g"]);
    }

    #[test]
    fn local_def_errors() {
        let e = parse_error("def f (n : Nat) : Nat :=\n  let a := 1\n  def g : Nat := a\n");
        assert!(e.message.contains("must end with an expression"), "{e:?}");
        assert!(e.message.contains("def"), "{e:?}");
        let e = parse_error("def f (n : Nat) : Nat :=\n  export def g : Nat := 1\n  g\n");
        assert!(e.message.contains("can't be exported"), "{e:?}");
        let e = parse_error("def f (n : Nat) : Nat :=\n  def g : Nat\n  n\n");
        assert!(e.message.contains("needs a body"), "{e:?}");
        let e = parse_error("def f (n : Nat) : Nat := g n\n  where\n    g : Nat\n");
        assert_eq!(e.code, "E-WHERE");
        assert!(e.message.contains("local `def`"), "{e:?}");
    }

    #[test]
    fn a_namespace_line_is_read_with_its_path() {
        let module = parse("-- a file\nnamespace Day05\n\nimport List (map)\n\ndef x: Nat := 1\n");
        assert_eq!(module.namespace.unwrap().path.text, "Day05");
        assert_eq!(module.imports.len(), 1);
        assert!(!module.decls.is_empty());
        let module = parse("namespace Aoc.Day05\ndef x: Nat := 1\n");
        assert_eq!(module.namespace.unwrap().path.text, "Aoc.Day05");
        assert!(parse("def x: Nat := 1\n").namespace.is_none());
    }

    #[test]
    fn import_everything_is_read_with_its_dots() {
        let module = parse("import List (..)\n\ndef x: Nat := 1\n");
        let import = &module.imports[0];
        assert_eq!(import.path.text, "List");
        assert!(import.items.is_empty());
        let dots = import.everything.expect("`(..)`");
        assert_eq!((dots.start, dots.end), (13, 15));
        let module = parse("import Std.List (..)\n");
        assert_eq!(module.imports[0].path.text, "Std.List");
        assert!(module.imports[0].everything.is_some());
        let module = parse("import List (map)\n");
        assert!(module.imports[0].everything.is_none());
        for source in ["import Aoc (Range, ..)\n", "import Aoc (.., Range)\n"] {
            let e = parse_error(source);
            assert!(
                e.message.contains("so it goes on its own: `import Aoc (..)`"),
                "{e:?}"
            );
        }
        let e = parse_error("import List ()\n");
        assert!(e.message.contains("a name to import"), "{e:?}");
        let e = parse_error("import List\n");
        assert!(e.message.contains("`(` and the names to import"), "{e:?}");
    }

    #[test]
    fn a_namespace_line_has_to_be_well_formed_and_first() {
        let e = parse_error("namespace Demo.day\n");
        assert!(e.message.contains("starts with a capital letter"), "{e:?}");
        let e = parse_error("namespace demo.Day\n");
        assert!(e.message.contains("starts with a capital letter"), "{e:?}");
        let e = parse_error("namespace\n");
        assert!(e.message.contains("a namespace, such as `Day05`"), "{e:?}");
        let e = parse_error("namespace 5\n");
        assert!(e.message.contains("a namespace, such as `Day05`"), "{e:?}");
        let e = parse_error("namespace A\nnamespace B\n");
        assert!(e.message.contains("only one namespace line"), "{e:?}");
        assert!(e.notes[0].contains("import from it"), "{e:?}");
        let e = parse_error("import List (map)\nnamespace A\n");
        assert!(e.message.contains("goes at the top of the file"), "{e:?}");
        let e = parse_error("def x: Nat := 1\nnamespace A\n");
        assert!(e.message.contains("goes at the top of the file"), "{e:?}");
    }

    #[test]
    fn namespace_is_a_keyword() {
        assert!(parse_module_text("def namespace: Nat := 1\n").is_err());
    }

    fn parse_module_text(text: &str) -> std::result::Result<Module, Vec<Diagnostic>> {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_module(file, text)
    }
}
