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
    Alt, BinOp, Binder, Bracket, CalcStep, Clause, CtorDecl, Decl, Expr, Import, LocalDef,
    MatchKind, Mode, Module, Name, NamespaceDecl, Pattern, RewriteRule, Row, SECTION, Scrutinee,
};
use crate::lexer::{Tok, Token, lex};
use crate::stack::StackLimit;
use crate::{Diagnostic, FileId, Span};

mod declarations;
mod sections;
use declarations::{Param, misplaced_attributes};

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
    match parse_module_recovering(file, text, stack) {
        (module, errors) if errors.is_empty() => Ok(module),
        (_, errors) => Err(errors),
    }
}

/// Like [`parse_module_within`], but keeps going after a syntax error
/// (docs/proposals/language-server.md, stage 0a). Parsing recovers at
/// declaration boundaries: a declaration that doesn't parse is left out of
/// the module, and its names (found by scanning its tokens) are in
/// `Module::failed`, so the declarations after it that use them aren't
/// reported as using unknown names. Returns the declarations that did
/// parse and every error, in file order. A lexical error, or a first
/// declaration not at the start of a line, stops everything: the module is
/// empty.
pub fn parse_module_recovering(
    file: FileId,
    text: &str,
    stack: usize,
) -> (Module, Vec<Diagnostic>) {
    let limit = StackLimit::from_here(stack);
    let tokens = match lex(file, text) {
        Ok(tokens) => tokens,
        Err(d) => return (Module::default(), vec![d]),
    };
    let mut namespace = None;
    let mut imports = Vec::new();
    let mut decls = Vec::new();
    let mut errors = Vec::new();
    let mut failed = Vec::new();
    let groups = match split_decls(&tokens) {
        Ok(groups) => groups,
        Err(d) => return (Module::default(), vec![d]),
    };
    for group in groups {
        let mut parser = Parser::new(group, file, text.len(), limit);
        // The attributes before the declaration, which belong to it.
        let attrs = match parser.attributes() {
            Ok(attrs) => attrs,
            Err(diagnostic) => {
                errors.push(diagnostic);
                failed.extend(declared_names_of(group));
                continue;
            }
        };
        if let Some(first) = attrs.first() {
            let refused = match parser.peek() {
                None => Some(
                    Diagnostic::error(
                        "E-PARSE",
                        "attributes must be followed by the declaration they apply to",
                    )
                    .with_label(first.span, "nothing follows these attributes"),
                ),
                Some(Tok::KwNamespace) => Some(misplaced_attributes(first, "a namespace line")),
                Some(Tok::KwImport) => Some(misplaced_attributes(first, "an import")),
                Some(Tok::KwTest) => Some(misplaced_attributes(first, "a test")),
                Some(Tok::KwAbility) => Some(misplaced_attributes(first, "an ability")),
                _ => None,
            };
            if let Some(diagnostic) = refused {
                errors.push(diagnostic);
                failed.extend(declared_names_of(group));
                continue;
            }
        }
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
                let name = parser.namespace().ok().map(|decl| decl.path.text);
                let message = "the namespace line must come first, before imports and declarations";
                let mut diagnostic = Diagnostic::error("E-NAMESPACE-NOT-FIRST", message)
                    .with_label(group[0].span, message);
                if let Some(name) = name {
                    diagnostic = diagnostic
                        .with_note(format!("move `namespace {name}` to the top of the file"));
                }
                errors.push(diagnostic);
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
            Ok(mut parsed) => {
                // A declaration with attributes is a data type or a
                // definition (the others are refused above): its first part.
                match parsed.first_mut() {
                    Some(Decl::Data { attrs: a, .. } | Decl::Signature { attrs: a, .. }) => {
                        *a = attrs;
                    }
                    _ => debug_assert!(attrs.is_empty()),
                }
                decls.extend(parsed)
            }
            Err(diagnostic) => {
                errors.push(diagnostic);
                failed.extend(declared_names_of(group));
            }
        }
    }
    (
        Module {
            namespace,
            imports,
            decls,
            failed,
        },
        errors,
    )
}

/// The names a declaration that didn't parse would have declared, read off
/// its tokens: after its keyword (`def`, `theorem`, `instance`, `type`,
/// `interface`, `ability`), and for the last three, each name after a `|`
/// outside brackets (a constructor or operation). Best effort: a
/// declaration that broke before its name declares nothing.
fn declared_names_of(group: &[Token]) -> Vec<Name> {
    // Past the attributes before the declaration.
    let matching = match_brackets(group);
    let mut i = 0;
    while group.get(i).map(|t| &t.tok) == Some(&Tok::At)
        && let Some(&close) = matching.get(i + 1)
        && close != NO_PARTNER
    {
        i = close as usize + 1;
    }
    let group = &group[i..];
    let mut i = 0;
    if group.first().map(|t| &t.tok) == Some(&Tok::KwExport) {
        i = 1;
    }
    if group.get(i).map(|t| &t.tok) == Some(&Tok::KwOpaque) {
        i += 1;
    }
    let Some(keyword) = group.get(i).map(|t| &t.tok) else {
        return Vec::new();
    };
    let has_members = match keyword {
        Tok::KwDef | Tok::KwTheorem | Tok::KwInstance => false,
        Tok::KwType | Tok::KwInterface | Tok::KwAbility => true,
        _ => return Vec::new(),
    };
    let name_at = |j: usize| match group.get(j) {
        Some(Token {
            tok: Tok::Lower(text) | Tok::Upper(text),
            span,
            ..
        }) => Some(Name {
            text: text.clone(),
            span: *span,
        }),
        _ => None,
    };
    let mut names: Vec<Name> = name_at(i + 1).into_iter().collect();
    if has_members {
        let matching = match_brackets(group);
        let mut depth = 0usize;
        for (j, token) in group.iter().enumerate() {
            match token.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth = depth.saturating_sub(1),
                Tok::Pipe if depth == 0 => {
                    // Past a constructor's attributes, `| @[js.name "X"] C`.
                    let mut k = j + 1;
                    while group.get(k).map(|t| &t.tok) == Some(&Tok::At)
                        && let Some(&close) = matching.get(k + 1)
                        && close != NO_PARTNER
                    {
                        k = close as usize + 1;
                    }
                    names.extend(name_at(k));
                }
                _ => {}
            }
        }
    }
    names
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

/// A constructor pattern, its span widened to `span` (its brackets).
fn with_span(p: Pattern, span: Span) -> Pattern {
    match p {
        Pattern::Ctor(name, args, _) => Pattern::Ctor(name, args, span),
        Pattern::CtorFields {
            ctor, fields, rest, ..
        } => Pattern::CtorFields {
            ctor,
            fields,
            rest,
            span,
        },
        other => other,
    }
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
        Pattern::CtorFields { fields, .. } => fields.iter().any(|(_, p)| has_absurd(p)),
        Pattern::Or(alternatives, _) => alternatives.iter().any(has_absurd),
        _ => false,
    }
}

/// The first variable a pattern binds, if any (a punned record field is
/// one).
fn first_bound(p: &Pattern) -> Option<&Name> {
    match p {
        Pattern::Var(name) => Some(name),
        Pattern::Ctor(_, args, _) => args.iter().find_map(first_bound),
        Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
            first_bound(a).or_else(|| first_bound(b))
        }
        Pattern::Named(_, p, _) => first_bound(p),
        Pattern::Record { fields, .. } | Pattern::CtorFields { fields, .. } => {
            fields.iter().find_map(|(_, p)| first_bound(p))
        }
        Pattern::Or(alternatives, _) => alternatives.iter().find_map(first_bound),
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => None,
    }
}

/// The token range of each top-level declaration, in order: the column-0 split
/// the parser uses (attributes belong to the declaration after them). Together
/// the ranges cover `tokens`, except that tokens before the first range (a file
/// whose first column-0 token is `:=`, which starts no declaration) are in
/// none. Fails if the first token isn't at column 0.
pub fn decl_ranges(tokens: &[Token]) -> Result<Vec<std::ops::Range<usize>>> {
    let groups = split_decls(tokens)?;
    // The groups run to the end of `tokens`, so the first starts after
    // whatever precedes it.
    let mut start = tokens.len() - groups.iter().map(|group| group.len()).sum::<usize>();
    Ok(groups
        .into_iter()
        .map(|group| {
            let range = start..start + group.len();
            start = range.end;
            range
        })
        .collect())
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
    // A token at column 0 starts a declaration, except:
    // - `:=`, which ends a header (`decreasing e` then `:=`,
    //   docs/proposals/well-founded-recursion.md §6.1);
    // - a token inside an open `@[`, so a group of attributes may close with
    //   `]` at column 0 (but a declaration's keyword still starts one, so an
    //   unclosed `@[` doesn't swallow the rest of the file);
    // - a `,` or closing bracket while any bracket of the declaration is
    //   still open, so a multi-line bracket may close (or continue with a
    //   comma) in column 0, however far left (docs/syntax.md, Brackets
    //   continue lines). A declaration's keyword in column 0 still starts a
    //   declaration, so an unclosed `{` doesn't swallow the rest of the file;
    // - the first token after a group that is only attributes so far: they
    //   belong to the next declaration (docs/syntax.md, Attributes).
    let mut starts: Vec<usize> = Vec::new();
    // Brackets open inside the current `@[`, counting its own `[`.
    let mut depth = 0usize;
    let mut opening = false;
    let mut attributes_only = false;
    // Brackets open in the current declaration, of any kind.
    let mut open_brackets = 0usize;
    for (i, token) in tokens.iter().enumerate() {
        if token.column == 0 && token.tok != Tok::ColonEq {
            let keyword = matches!(
                token.tok,
                Tok::KwType
                    | Tok::KwInterface
                    | Tok::KwDef
                    | Tok::KwTheorem
                    | Tok::KwExport
                    | Tok::KwOpaque
                    | Tok::KwInstance
                    | Tok::KwAbility
                    | Tok::KwTest
                    | Tok::KwNamespace
                    | Tok::KwImport
            );
            let inside = depth > 0 || opening;
            let continues = open_brackets > 0
                && matches!(
                    token.tok,
                    Tok::Comma | Tok::RParen | Tok::RBracket | Tok::RBrace
                );
            if starts.is_empty()
                || (!inside && !attributes_only && !continues)
                || (inside && keyword)
            {
                starts.push(i);
                depth = 0;
                open_brackets = 0;
                opening = false;
                attributes_only = true;
            }
        }
        match token.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => open_brackets += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                open_brackets = open_brackets.saturating_sub(1);
            }
            _ => {}
        }
        match token.tok {
            Tok::At if depth == 0 => opening = true,
            Tok::LParen | Tok::LBracket | Tok::LBrace if depth > 0 || opening => {
                depth += 1;
                opening = false;
            }
            Tok::RParen | Tok::RBracket | Tok::RBrace if depth > 0 => depth -= 1,
            _ if depth == 0 => {
                attributes_only = false;
                opening = false;
            }
            _ => {}
        }
    }
    let mut groups = Vec::new();
    for (n, &start) in starts.iter().enumerate() {
        let end = starts.get(n + 1).copied().unwrap_or(tokens.len());
        groups.push(&tokens[start..end]);
    }
    Ok(groups)
}

/// A lambda parameter: a name (with the pattern it stands for, if it was
/// written as one), or a name with a written type and its mode.
enum LamParam {
    Plain(Name, Option<Pattern>),
    Typed(Name, Mode, Expr),
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
    /// How many `calc`s the parser is inside. In one, a line starting with
    /// `_` is the next step, not an argument of the line before.
    calc_depth: u32,
    /// While a `rewrite` rule or target is being parsed: the token it starts
    /// at. An `in` outside brackets ends it (`in` is an ordinary name
    /// elsewhere).
    rewrite_rule: Option<usize>,
    /// Whether an `at` outside brackets, after the first token, ends the
    /// `rewrite` rule too: true for a rule, false for the target after `at`.
    rewrite_at: bool,
    /// For each opening bracket (`(`, `[`, `{`), the index of its partner,
    /// and `NO_PARTNER` for every other token and for unmatched brackets.
    /// Built once per declaration, so that skipping a bracketed group is one
    /// lookup (the lambda scan and `is_pi_binder`).
    matching: Vec<u32>,
    /// How deep the recursion may go.
    stack: StackLimit,
}

const NO_PARTNER: u32 = u32::MAX;

/// For each opening bracket in `tokens`, the index of its closing partner.
/// The table is its own stack: while an opener is unmatched its entry holds
/// the opener below it, so there is a single allocation (the nesting
/// benchmarks' allocation and heap counts depend on that).
fn match_brackets(tokens: &[Token]) -> Vec<u32> {
    let mut matching = vec![NO_PARTNER; tokens.len()];
    let mut top = NO_PARTNER;
    for (i, token) in tokens.iter().enumerate() {
        match token.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => {
                matching[i] = top;
                top = i as u32;
            }
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                if top == NO_PARTNER {
                    continue;
                }
                let want = match token.tok {
                    Tok::RParen => Tok::LParen,
                    Tok::RBracket => Tok::LBracket,
                    _ => Tok::LBrace,
                };
                if tokens[top as usize].tok == want {
                    let below = matching[top as usize];
                    matching[top as usize] = i as u32;
                    top = below;
                }
            }
            _ => {}
        }
    }
    // Openers never closed: forget the links.
    while top != NO_PARTNER {
        let below = matching[top as usize];
        matching[top as usize] = NO_PARTNER;
        top = below;
    }
    matching
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
            calc_depth: 0,
            rewrite_rule: None,
            rewrite_at: false,
            matching: match_brackets(tokens),
            stack,
        }
    }

    /// `=>` after a lambda's parameters or an alternative's patterns, with a
    /// hint if it's the old syntax's `->`.
    fn expect_fat_arrow(&mut self, what: &str) -> Result<&'t Token> {
        if self.peek() == Some(&Tok::Arrow) {
            return Err(self
                .unexpected(what)
                .with_note("lambdas and arms use `=>`: `x => e`, `| p => e`"));
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

    /// Whether the token at `i` is a `_` starting a line, which inside a
    /// `calc` is the next step.
    #[inline(never)]
    fn starts_calc_step(&self, i: usize) -> bool {
        self.tokens
            .get(i)
            .is_some_and(|t| t.line_start && t.tok == Tok::Underscore)
    }

    /// Whether the token at `i` ends the current statement of a block.
    fn is_stop(&self, i: usize) -> bool {
        if self.calc_depth > 0 && self.starts_calc_step(i) {
            return true;
        }
        if let Some(start) = self.rewrite_rule
            && self.ends_rewrite_rule(i, start)
        {
            return true;
        }
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

    /// Whether the token at `i` is the `in` (or, in a rule, the `at`) that
    /// ends the `rewrite` rule or target starting at token `start`: one not
    /// inside brackets opened since, nor a field (`p.at`). An `at` that starts
    /// the rule is a name (`rewrite at b h in t`).
    #[inline(never)]
    fn ends_rewrite_rule(&self, i: usize, start: usize) -> bool {
        let word = match self.tokens.get(i).map(|t| &t.tok) {
            Some(Tok::KwIn) => true,
            Some(Tok::Lower(w)) => w == "at" && self.rewrite_at && i > start,
            _ => false,
        };
        if !word || (i > 0 && self.tokens[i - 1].tok == Tok::Dot) {
            return false;
        }
        let depth = self.tokens[start..i].iter().fold(0i64, |d, t| match t.tok {
            Tok::LBracket | Tok::LParen | Tok::LBrace => d + 1,
            Tok::RBracket | Tok::RParen | Tok::RBrace => d - 1,
            _ => d,
        });
        depth <= 0
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

    /// [`Parser::unexpected`] where a name could be written: a keyword found
    /// there is reported as one, since it can't be a name.
    fn unexpected_name(&self, expected: &str) -> Diagnostic {
        let keyword = match self.tokens.get(self.pos) {
            Some(token) if !self.is_stop(self.pos) => token.tok.keyword().filter(|word| {
                // `∈` and `∃` are the same tokens as `in` and `exists`.
                (token.span.end - token.span.start) as usize == word.len()
            }),
            _ => None,
        };
        match keyword {
            Some(word) => error(
                self.here(),
                format!("expected {expected}, but found the keyword `{word}`"),
            )
            .with_note(format!(
                "`{word}` is a keyword, so it can't be used as a name"
            )),
            None => self.unexpected(expected),
        }
    }

    fn unexpected(&self, expected: &str) -> Diagnostic {
        if !self.is_stop(self.pos) && self.tokens.get(self.pos).map(|t| &t.tok) == Some(&Tok::At) {
            return Diagnostic::error("E-ATTRIBUTE", "attributes can't be written here")
                .with_label(self.here(), format!("expected {expected}"))
                .with_note(declarations::ATTRIBUTE_PLACES);
        }
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
        let found_arrow = self
            .tokens
            .get(self.pos)
            .is_some_and(|t| t.tok == Tok::FatArrow);
        let diagnostic = error(self.here(), format!("expected {expected}, but {found}"));
        if self
            .tokens
            .get(self.pos)
            .is_some_and(|t| t.tok == Tok::KwUnfolding)
        {
            return diagnostic.with_note(
                "`unfolding f` goes in a declaration's header, after its result type and before \
                 `:=` or the arms: `theorem t: … unfolding f := …`; it can't be written in a body",
            );
        }
        if found_arrow {
            return diagnostic.with_note(
                "to pass a lambda as an argument, put it in brackets: `List.map xs (x => …)`",
            );
        }
        diagnostic
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
            items.push(self.tuple_item()?);
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

    /// A component of a tuple pattern, or several, `p | q`.
    fn tuple_item(&mut self) -> Result<Pattern> {
        let first = self.tuple_component()?;
        self.alternatives(first, Self::tuple_component)
    }

    /// An element of a list pattern, or several, `p | q`.
    fn list_item(&mut self) -> Result<Pattern> {
        let first = self.list_component()?;
        self.alternatives(first, Self::list_component)
    }

    /// A component of a list pattern: a constructor's arguments run to the
    /// next `,` or `]`; `-k` is allowed, as in a tuple.
    fn list_component(&mut self) -> Result<Pattern> {
        if self.ctor_ahead() {
            let start = self.here();
            let name = self.ctor_name()?;
            return self.ctor_args(name, start, |t| {
                matches!(t, Some(Tok::Comma | Tok::RBracket | Tok::Pipe) | None)
            });
        }
        self.tuple_component()
    }

    /// A component of a tuple pattern: a pattern, or `-k`, which the
    /// tuple's brackets already delimit (`(-1, 0)`, `(0, -1)`).
    fn tuple_component(&mut self) -> Result<Pattern> {
        if self.ctor_ahead() {
            // A constructor's arguments run to the next `,` or `)`:
            // `(Some x, Some y)`.
            let start = self.here();
            let name = self.ctor_name()?;
            return self.ctor_args(name, start, |t| {
                matches!(t, Some(Tok::Comma | Tok::RParen | Tok::Pipe) | None)
            });
        }
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

    /// A parameter's name: like `lower`, but says why an uppercase name isn't one.
    fn param_name(&mut self) -> Result<Name> {
        if let Some(Tok::Upper(text)) = self.peek() {
            let text = text.clone();
            return Err(self.unexpected("a parameter's name").with_note(format!(
                "parameter names start with a lowercase letter; an uppercase name such as \
                 `{text}` is a constructor"
            )));
        }
        self.lower("a parameter's name")
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
            _ => Err(self.unexpected_name(what)),
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

    /// Whether a constructor pattern starts here: an uppercase name, or
    /// `Quot.mk`. `Quot.mk` isn't a constructor (a quotient can't be matched
    /// on), but it's read as one so that the elaborator can say why, rather
    /// than the parser refusing a qualified name
    /// (docs/proposals/map-equality.md §7.6, R2).
    fn ctor_ahead(&self) -> bool {
        match self.peek() {
            Some(Tok::Upper(_)) => true,
            Some(Tok::Lower(text)) => text == "Quot.mk",
            _ => false,
        }
    }

    /// The name of a constructor pattern, once [`Self::ctor_ahead`] has
    /// said one starts here.
    fn ctor_name(&mut self) -> Result<Name> {
        match self.peek() {
            Some(Tok::Lower(_)) => self.lower_q("a constructor"),
            _ => self.upper_q("a constructor"),
        }
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
            Some(Tok::Lower(_)) if !self.ctor_ahead() => Ok(Pattern::Var(self.lower("a pattern")?)),
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
            Some(Tok::Upper(_) | Tok::Lower(_)) => {
                let name = self.ctor_name()?;
                Ok(Pattern::Ctor(name, Vec::new(), span))
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                let end = self.bump().span;
                Ok(Pattern::Absurd(span.to(end)))
            }
            Some(Tok::LBrace) => self.record_pattern(),
            // `[n := p]`: an implicit field of a constructor, by name.
            Some(Tok::LBracket)
                if matches!(self.peek_at(1), Some(Tok::Lower(_)))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                let field = self.lower("a field name")?;
                self.bump();
                let inner = self.pattern()?;
                let end = self.expect(Tok::RBracket, "`]`")?.span;
                Ok(Pattern::Named(field, Box::new(inner), span.to(end)))
            }
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
                        items.push(self.list_item()?);
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
                let inner = self.tuple_item()?;
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
                let pattern = if self.ctor_ahead() {
                    let name = self.ctor_name()?;
                    let first = self.ctor_args(name, span, |t| {
                        matches!(t, Some(Tok::RParen | Tok::Comma | Tok::Pipe) | None)
                    })?;
                    let first = self.alternatives(first, Self::tuple_component)?;
                    if self.peek() == Some(&Tok::Comma) {
                        // `(Some a, b)`: a constructor as a tuple's first component.
                        return self.tuple_pattern(first, span);
                    }
                    let end = self.expect(Tok::RParen, "`)`")?.span;
                    with_span(first, span.to(end))
                } else {
                    let inner = self.pattern()?;
                    let inner = self.alternatives(inner, Self::tuple_component)?;
                    if self.peek() == Some(&Tok::Comma) {
                        return self.tuple_pattern(inner, span);
                    }
                    self.expect(Tok::RParen, "`)`")?;
                    inner
                };
                Ok(pattern)
            }
            _ => Err(self.unexpected_name("a pattern or `=`")),
        }
    }

    /// Constructor `name`'s arguments, from here to a token `stop` accepts:
    /// positional patterns, or braces naming its fields, `C { f = p, g, .. }`
    /// (docs/proposals/variant-fields.md §4). Braces right after a
    /// constructor always name its fields and take no further arguments; a
    /// record pattern as a positional argument is written in brackets,
    /// `C ({ … })`.
    fn ctor_args(
        &mut self,
        name: Name,
        start: Span,
        stop: fn(Option<&Tok>) -> bool,
    ) -> Result<Pattern> {
        if self.peek() == Some(&Tok::LBrace) {
            let Pattern::Record { fields, rest, .. } = self.record_pattern()? else {
                unreachable!("a record pattern");
            };
            let span = start.to(self.prev_span());
            if !stop(self.peek()) {
                return Err(error(
                    self.here(),
                    format!(
                        "braces after `{}` name its fields, and take no further arguments",
                        name.text
                    ),
                )
                .with_note(format!(
                    "to match a record as `{0}`'s first argument, write it in brackets: \
                     `{0} ({{ … }}) …`",
                    name.text
                )));
            }
            return Ok(Pattern::CtorFields {
                ctor: name,
                fields,
                rest,
                span,
            });
        }
        let mut args = Vec::new();
        while !stop(self.peek()) {
            if self.peek() == Some(&Tok::LBrace) {
                return Err(error(
                    self.here(),
                    format!(
                        "a record pattern as an argument of `{}` is written in brackets: `({{ … }})`",
                        name.text
                    ),
                )
                .with_note(
                    "braces name a constructor's fields only right after it: `C { f = p, .. }`",
                ));
            }
            args.push(self.pattern()?);
        }
        Ok(Pattern::Ctor(name, args, start.to(self.prev_span())))
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
                    if self.ctor_ahead() {
                        let start = self.here();
                        let name = self.ctor_name()?;
                        self.ctor_args(name, start, |t| {
                            matches!(t, Some(Tok::Comma | Tok::RBrace) | None)
                        })?
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
        let interface = self.tokens[self.pos - 1].tok == Tok::KwInterface;
        let name = if interface {
            self.upper_q("an interface name (starting with an uppercase letter)")?
        } else {
            self.upper_q("a data type name (starting with an uppercase letter)")?
        };
        let mut params = Vec::new();
        let mut auto_params = Vec::new();
        loop {
            if self.peek() == Some(&Tok::LParen) {
                let binder = self.binder()?;
                if let Some(first) = binder.attrs.first() {
                    return Err(misplaced_attributes(first, "a data type's parameter"));
                }
                params.push(binder);
                auto_params.push(false);
            } else if self.is_implicit_binder() {
                // `[auto ord: Ord k]`, filled in by instance search wherever
                // the type is written (docs/proposals/interfaces.md §7.5).
                let start = self.here();
                let (binder, auto) = self.implicit_binder()?;
                if let Some(first) = binder.attrs.first() {
                    return Err(misplaced_attributes(first, "a data type's parameter"));
                }
                if !auto {
                    return Err(error(
                        start.to(self.prev_span()),
                        "a type's parameters in brackets must be `auto`, like `[auto ord: Ord k]`",
                    )
                    .with_note(
                        "a type's other parameters are always given, so they're written \
                         `(a: Type)`",
                    ));
                }
                if binder.names[0].text == crate::ast::NAMELESS {
                    return Err(error(
                        start.to(self.prev_span()),
                        "a type's `auto` parameter needs a name, so it can be given by name: \
                         `[auto ord: Ord k]`",
                    ));
                }
                params.push(binder);
                auto_params.push(true);
            } else {
                break;
            }
        }
        // After the colon: index types, each followed by `->`, then the
        // universe (docs/proposals/indexed-families.md §7.1).
        let mut indices = Vec::new();
        let sort = if self.eat(&Tok::Colon) {
            loop {
                if self.is_pi_binder() {
                    let binder = self.binder()?;
                    if let Some(first) = binder.attrs.first() {
                        return Err(misplaced_attributes(first, "a data type's index"));
                    }
                    self.expect(Tok::Arrow, "`->`")?;
                    for n in binder.names {
                        indices.push((Some(n), binder.ty.clone()));
                    }
                    continue;
                }
                let ty = self.app()?;
                if self.eat(&Tok::Arrow) {
                    indices.push((None, ty));
                    continue;
                }
                break Some(ty);
            }
        } else {
            None
        };
        let mut ctors = Vec::new();
        let mut record = false;
        // An interface is a record (docs/proposals/interfaces.md §5.1).
        if interface {
            if let Some((_, ty)) = indices.first() {
                return Err(error(ty.span(), "an interface can't have indices"));
            }
            self.expect(Tok::Equals, "`=` and the interface's fields, `{ … }`")?;
            if self.peek() != Some(&Tok::LBrace) {
                return Err(self.unexpected("`{` and the interface's fields"));
            }
            let ctor = self.record_fields(&name)?;
            return Ok(vec![Decl::Data {
                span: start.to(self.prev_span()),
                name,
                params,
                auto_params,
                indices,
                sort,
                ctors: vec![ctor],
                record: true,
                interface: true,
                attrs: Vec::new(),
            }]);
        }
        if self.eat(&Tok::Equals) {
            if !matches!(self.peek(), Some(Tok::LBrace | Tok::Pipe)) {
                if let Some((_, ty)) = indices.first() {
                    return Err(error(
                        ty.span(),
                        "a type synonym can't have indices: `->` after the colon is only for a \
                         data type's indices",
                    ));
                }
                return self.type_synonym(start, name, params, auto_params, sort);
            }
            if self.peek() == Some(&Tok::LBrace) {
                record = true;
                ctors.push(self.record_fields(&name)?);
            } else {
                while self.eat(&Tok::Pipe) {
                    let attrs = self.attributes()?;
                    let name =
                        self.upper("a constructor name (starting with an uppercase letter)")?;
                    let mut fields = Vec::new();
                    let mut implicit = Vec::new();
                    let mut defaults = Vec::new();
                    loop {
                        if self.peek() == Some(&Tok::LParen) {
                            let (binder, default) = self.binder_with_default()?;
                            fields.push(binder);
                            implicit.push(false);
                            defaults.push(default);
                        } else if self.is_implicit_binder() {
                            let (binder, auto) = self.implicit_binder()?;
                            if auto {
                                return Err(error(
                                    binder.names[0].span,
                                    "a constructor's implicit fields can't be `auto`",
                                ));
                            }
                            fields.push(binder);
                            implicit.push(true);
                            defaults.push(None);
                        } else {
                            break;
                        }
                    }
                    // The result type, `: Vec a (Succ n)`.
                    let result = if self.eat(&Tok::Colon) {
                        Some(self.app()?)
                    } else {
                        None
                    };
                    if defaults.iter().all(Option::is_none) {
                        defaults.clear();
                    }
                    ctors.push(CtorDecl {
                        attrs,
                        name,
                        fields,
                        implicit,
                        defaults,
                        result,
                    });
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
            auto_params,
            indices,
            sort,
            ctors,
            record,
            interface: false,
            attrs: Vec::new(),
        }])
    }

    /// A record's fields, `{ name : Text, age : Nat }`, as the one
    /// constructor of the data type `data`, named `%mk`, which source can't
    /// write (so `data.mk` is free for a function).
    fn record_fields(&mut self, data: &Name) -> Result<CtorDecl> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        let mut defaults = Vec::new();
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                if self.peek() == Some(&Tok::RBrace) {
                    break;
                }
                let attrs = self.attributes()?;
                let field = self.lower("a field name")?;
                self.expect(Tok::Colon, "`:`")?;
                let ty = self.expr()?;
                defaults.push(if self.eat(&Tok::ColonEq) {
                    Some(self.expr()?)
                } else {
                    None
                });
                fields.push(Binder {
                    names: vec![field],
                    ty,
                    attrs,
                });
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RBrace, "`,` or `}`")?;
        if defaults.iter().all(Option::is_none) {
            defaults.clear();
        }
        Ok(CtorDecl {
            attrs: Vec::new(),
            name: Name {
                text: "%mk".into(),
                span: data.span,
            },
            fields,
            implicit: Vec::new(),
            defaults,
            result: None,
        })
    }

    /// `ability Name (params) where`, then one operation per line.
    fn ability(&mut self) -> Result<Decl> {
        let start = self.bump().span;
        let name = self.upper_q("an ability name (starting with an uppercase letter)")?;
        let mut params = Vec::new();
        while self.peek() == Some(&Tok::LParen) {
            let binder = self.binder()?;
            if let Some(first) = binder.attrs.first() {
                return Err(misplaced_attributes(first, "an ability's parameter"));
            }
            params.push(binder);
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

    /// `(x y : A)`, with any attributes before the names (which only a
    /// constructor's field may have: the callers refuse them elsewhere).
    fn binder(&mut self) -> Result<Binder> {
        let (binder, default) = self.binder_with_default()?;
        if let Some(default) = default {
            return Err(
                error(default.span(), declarations::DEFAULT_PLACES).with_note(
                    "a definition's explicit parameters, `def range (step: Nat := 1)`, a \
                     record's fields, `{ step: Nat := 1 }`, and a constructor's, \
                     `| Circle (id: Text := \"a\")`, can have one; a function type can't",
                ),
            );
        }
        Ok(binder)
    }

    /// `(x y : A)`, or with a default value, `(x y : A := v)`, which only a
    /// constructor's field may have (docs/proposals/named-arguments.md
    /// §5.1).
    fn binder_with_default(&mut self) -> Result<(Binder, Option<Expr>)> {
        self.expect(Tok::LParen, "`(`")?;
        let attrs = self.attributes()?;
        let mut names = vec![self.lower("a name")?];
        while let Some(Tok::Lower(_)) = self.peek() {
            names.push(self.lower("a name")?);
        }
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.expr()?;
        let default = if self.eat(&Tok::ColonEq) {
            Some(self.expr()?)
        } else {
            None
        };
        self.expect(Tok::RParen, "`)`")?;
        Ok((Binder { names, ty, attrs }, default))
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
    /// of a definition), `where`, `:=`, `decreasing` or `unfolding` (after a
    /// type that's a block).
    fn ends_blocks(&self) -> bool {
        self.tokens.get(self.pos).is_some_and(|t| {
            matches!(
                t.tok,
                Tok::Pipe | Tok::KwWhere | Tok::ColonEq | Tok::KwDecreasing | Tok::KwUnfolding
            )
        })
    }

    fn statement(&mut self) -> Result<Stmt> {
        match self.peek() {
            Some(Tok::KwLet) => self.let_statement(),
            Some(Tok::KwDef | Tok::KwTheorem) => self.local_def(),
            Some(Tok::KwExport) => Err(error(
                self.here(),
                "local definitions can't be exported: only top-level ones are",
            )),
            Some(Tok::KwOpaque) => Err(error(
                self.here(),
                "local definitions can't be `opaque`: only top-level ones can",
            )),
            _ => Ok(Stmt::Expr(self.expr_inline()?)),
        }
    }

    /// A local `def` or `theorem`, written as at top level, but with a body.
    #[inline(never)]
    fn local_def(&mut self) -> Result<Stmt> {
        let start = self.here();
        let mut decls = self.definition(start, false, false)?.into_iter();
        let signature = decls.next().expect("a definition has a signature");
        if let Decl::Signature { unfolding, .. } = &signature
            && let Some(first) = unfolding.first()
        {
            return Err(error(
                first.span,
                "a local definition can't have `unfolding`",
            )
            .with_note(
                "it unfolds what the declaration it's in unfolds: write `unfolding` on that one",
            ));
        }
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
        if self.ctor_ahead() {
            let start = self.here();
            let name = self.ctor_name()?;
            return self.ctor_args(name, start, |t| {
                matches!(t, Some(Tok::Equals | Tok::ColonEq | Tok::Colon) | None)
            });
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
        if matches!(self.peek(), Some(Tok::Lower(_))) && self.peek_at(1) == Some(&Tok::Colon) {
            return Err(Diagnostic::error(
                "E-PARSE",
                "a record type can't be written here: `{` in a type starts an ability row",
            )
            .with_label(start, "this `{` starts an ability row")
            .with_note(
                "anonymous record types aren't supported: give it a name with `type`, then write \
                 that name after `->`",
            ));
        }
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
        let clauses = self.handler_clauses()?;
        Ok(Expr::Handle {
            span: start.to(self.prev_span()),
            body: Box::new(body),
            clauses,
        })
    }

    /// A handler's clauses, each after a `|`; at least one.
    fn handler_clauses(&mut self) -> Result<Vec<Clause>> {
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
        Ok(clauses)
    }

    /// Whether `reify` starts here as the keyword it is after `match`
    /// (D1148): followed by the computation, not by `with` or `,` (where it
    /// is an ordinary name).
    fn reify_ahead(&self) -> bool {
        matches!(self.peek(), Some(Tok::Lower(name)) if name == "reify")
            && !matches!(
                self.peek_at(1),
                Some(Tok::KwWith | Tok::Comma | Tok::Colon) | None
            )
    }

    /// `match reify t with | return x => … | op arg, k => …`, after `match`
    /// and `reify` (docs/proposals/proof-reification.md §3 (iii)).
    fn reify_expr(&mut self, start: Span) -> Result<Expr> {
        let thunk = self.expr_inline()?;
        if self.peek() == Some(&Tok::Comma) {
            return Err(error(
                self.here(),
                "`match reify` takes one computation, with nothing else to match",
            ));
        }
        self.expect(Tok::KwWith, "`with`")?;
        let clauses = self.handler_clauses()?;
        Ok(Expr::Reify {
            span: start.to(self.prev_span()),
            thunk: Box::new(thunk),
            clauses,
        })
    }

    /// `match e, h : e2 with | p, q => body | …`
    fn match_expr(&mut self, start: Span) -> Result<Expr> {
        if self.reify_ahead() {
            self.bump();
            return self.reify_expr(start);
        }
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
            if name.is_some() && self.reify_ahead() {
                return Err(
                    Diagnostic::error("E-PARSE", "`match reify` can't name an equation")
                        .with_label(start.to(self.here()), "`h:` names an equation here")
                        .with_note(
                            "both sides would be computations, whose type has no spelling; in each \
                     clause the goal already says what the computation did",
                        ),
                );
            }
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
    /// (`Cons x Nil`); or several, `p | q`.
    fn alt_pattern(&mut self) -> Result<Pattern> {
        let first = self.alt_pattern_one()?;
        self.alternatives(first, Self::alt_pattern_one)
    }

    fn alt_pattern_one(&mut self) -> Result<Pattern> {
        if self.ctor_ahead() {
            let start = self.here();
            let name = self.ctor_name()?;
            return self.ctor_args(name, start, |t| {
                matches!(
                    t,
                    Some(Tok::Comma | Tok::Arrow | Tok::FatArrow | Tok::Pipe) | None
                )
            });
        }
        self.tuple_component()
    }

    /// Whether a `|` between alternatives of an or-pattern is next: one on
    /// the same line, since a `|` that starts a line starts the next arm.
    fn or_bar_ahead(&self) -> bool {
        self.peek() == Some(&Tok::Pipe) && !self.tokens[self.pos].line_start
    }

    /// `first | q | …`, each further alternative parsed by `next`; just
    /// `first` if no `|` follows. No alternative may bind a variable.
    fn alternatives(
        &mut self,
        first: Pattern,
        next: fn(&mut Self) -> Result<Pattern>,
    ) -> Result<Pattern> {
        if !self.or_bar_ahead() {
            return Ok(first);
        }
        let mut alternatives = vec![first];
        while self.or_bar_ahead() {
            self.bump();
            alternatives.push(next(self)?);
        }
        if let Some(name) = alternatives.iter().find_map(first_bound) {
            return Err(Diagnostic::error(
                "E-OR-PATTERN-BINDS",
                "an or-pattern can't bind names",
            )
            .with_label(name.span, format!("`{}` is bound here", name.text))
            .with_note(
                "write `_` for a part that isn't used, or match each alternative in an arm of its own",
            ));
        }
        let span = alternatives[0]
            .span()
            .to(alternatives[alternatives.len() - 1].span());
        Ok(Pattern::Or(alternatives, span))
    }

    /// `x (a, b) => body`, once `lambda_ahead` has said this is one. Out of
    /// line, so that
    /// `expr_inline`, which every nested expression recurses through, keeps
    /// a small stack frame.
    #[inline(never)]
    fn lambda(&mut self, start: Span) -> Result<Expr> {
        // Each parameter is a name, with the pattern it stands for if it
        // was written as one.
        let mut params: Vec<LamParam> = Vec::new();
        loop {
            match self.peek() {
                Some(Tok::Lower(_)) => params.push(LamParam::Plain(self.lower("a name")?, None)),
                Some(Tok::Underscore) => {
                    let span = self.bump().span;
                    let name = Name {
                        text: "_".to_string(),
                        span,
                    };
                    params.push(LamParam::Plain(name, None));
                }
                // `(x: A)`, `(x y: A)`: parameters with a written type, as in
                // a definition's header.
                Some(Tok::LParen) if self.annotated_param_ahead() => {
                    let Param::Named {
                        names, ty, default, ..
                    } = self.header_param()?
                    else {
                        unreachable!("an annotated parameter is a named one")
                    };
                    if let Some(default) = default {
                        return Err(lambda_default(&default));
                    }
                    for name in names {
                        params.push(LamParam::Typed(name, Mode::Explicit, ty.clone()));
                    }
                }
                // `[a: Type]`, `[auto h: P]`, `[auto P]`: implicit and auto
                // parameters, as in a header (§4.3, D91).
                Some(Tok::LBracket)
                    if self.implicit_group_at(self.pos) || self.nameless_auto_at(self.pos) =>
                {
                    let Param::Named {
                        names, ty, auto, ..
                    } = self.header_param()?
                    else {
                        unreachable!("an implicit parameter is a named one")
                    };
                    let mode = if auto { Mode::Auto } else { Mode::Implicit };
                    for name in names {
                        params.push(LamParam::Typed(name, mode, ty.clone()));
                    }
                }
                Some(Tok::LParen | Tok::LBrace) => match self.pattern()? {
                    Pattern::Var(name) => params.push(LamParam::Plain(name, None)),
                    pattern => {
                        let i = params.len();
                        let name = Name {
                            text: format!("%arg{i}"),
                            span: pattern.span(),
                        };
                        params.push(LamParam::Plain(name, Some(pattern)));
                    }
                },
                _ => break,
            }
        }
        if params.is_empty() {
            return Err(self.unexpected("a parameter name"));
        }
        self.expect_fat_arrow("`=>`")?;
        let body = self.expr()?;
        let span = start.to(body.span());
        let mut scrutinees = Vec::new();
        let mut patterns = Vec::new();
        for param in &params {
            if let LamParam::Plain(name, Some(pattern)) = param {
                scrutinees.push(Scrutinee {
                    name: None,
                    expr: Expr::Var(name.clone()),
                });
                patterns.push(pattern.clone());
            }
        }
        let mut result = if patterns.is_empty() {
            body
        } else {
            let alt_span = patterns[0].span().to(body.span());
            Expr::Match {
                scrutinees,
                alts: vec![Alt {
                    patterns,
                    body,
                    span: alt_span,
                }],
                span,
                kind: MatchKind::Lambda,
            }
        };
        // Build from the last parameter outwards: a run of untyped ones is
        // one `Lam`, and each typed one is a `TypedLam`.
        let mut run: Vec<Name> = Vec::new();
        for param in params.into_iter().rev() {
            match param {
                LamParam::Plain(name, _) => run.push(name),
                LamParam::Typed(name, mode, ty) => {
                    if !run.is_empty() {
                        run.reverse();
                        result = Expr::Lam(std::mem::take(&mut run), Box::new(result), span);
                    }
                    result = Expr::TypedLam(name, mode, Box::new(ty), Box::new(result), span);
                }
            }
        }
        if !run.is_empty() {
            run.reverse();
            result = Expr::Lam(run, Box::new(result), span);
        }
        Ok(result)
    }

    /// Whether a `(` here opens an annotated parameter, `(x: A)` or
    /// `(x y: A)`, rather than a pattern.
    fn annotated_param_ahead(&self) -> bool {
        let mut i = 1;
        while matches!(self.peek_at(i), Some(Tok::Lower(_))) {
            i += 1;
        }
        i > 1 && self.peek_at(i) == Some(&Tok::Colon)
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

    /// `calc e0` and its steps, one per line: `_ = e1 := proof`, `_ <= e2`
    /// (no proof: closed by computation). The steps line up, and are
    /// indented past the line `calc` is on.
    #[inline(never)]
    fn calc_expr(&mut self, start: Span) -> Result<Expr> {
        let indent = self.line_indent(self.pos - 1);
        self.calc_depth += 1;
        let result = self.calc_body(start, indent);
        self.calc_depth -= 1;
        result
    }

    /// A `calc` expression: above the relations, so `a || b`, `a && b` and
    /// `xs |> f` need no parentheses.
    fn calc_operand(&mut self) -> Result<Expr> {
        let mut e = self.append_expr()?;
        if self.at_pipe() {
            self.pipe_chain(&mut e)?;
        }
        if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
            self.logic_chain(&mut e)?;
        }
        Ok(e)
    }

    #[inline(never)]
    fn calc_body(&mut self, start: Span, indent: u32) -> Result<Expr> {
        let first = self.calc_operand()?;
        if matches!(
            self.peek(),
            Some(Tok::Equals | Tok::Le | Tok::Lt | Tok::Gt | Tok::Ge | Tok::NotEq | Tok::EqEq)
        ) {
            return Err(error(
                self.here(),
                "`calc` starts with one expression; each relation goes on a line of its own",
            )
            .with_note("write `calc a` and then, indented below it, `_ = b := proof`"));
        }
        let mut steps: Vec<CalcStep> = Vec::new();
        let mut column = None;
        // Whether any step is `<`/`<=` (`ascending`) or `>`/`>=` (`descending`).
        let mut ascending = false;
        let mut descending = false;
        while let Some(token) = self.tokens.get(self.pos)
            && token.tok == Tok::Underscore
            && token.line_start
            && token.column > indent
            && self.limit.is_none_or(|limit| token.column > limit)
        {
            match column {
                None => column = Some(token.column),
                Some(c) if c != token.column => {
                    return Err(error(
                        token.span,
                        "this step isn't lined up with the steps above it",
                    ));
                }
                Some(_) => {}
            }
            let underscore = self.bump().span;
            let (rel, rel_span) = match self.peek() {
                Some(Tok::Equals) => (BinOp::Eq, self.bump().span),
                Some(Tok::Le) => {
                    ascending = true;
                    (BinOp::Le, self.bump().span)
                }
                Some(Tok::Lt) => {
                    ascending = true;
                    (BinOp::Lt, self.bump().span)
                }
                Some(Tok::Ge) => {
                    descending = true;
                    (BinOp::Le, self.bump().span)
                }
                Some(Tok::Gt) => {
                    descending = true;
                    (BinOp::Lt, self.bump().span)
                }
                Some(Tok::NotEq | Tok::EqEq) => {
                    return Err(error(
                        self.here(),
                        "a `calc` step is `=`, `<=`, `<`, `>=` or `>`: other relations can't \
                         be chained",
                    ));
                }
                _ => return Err(self.unexpected("`=`, `<=`, `<`, `>=` or `>` after `_`")),
            };
            let rhs = self.calc_operand()?;
            let proof = if self.eat(&Tok::ColonEq) {
                Some(self.expr()?)
            } else {
                None
            };
            steps.push(CalcStep {
                rel,
                rel_span,
                rhs,
                proof,
                span: underscore.to(self.prev_span()),
            });
        }
        let Some(last) = steps.last() else {
            return Err(self
                .unexpected("a step `_ = e` on the next line, indented past `calc`")
                .with_note("a `calc` needs at least one step"));
        };
        let span = start.to(last.span);
        if descending && ascending {
            return Err(Diagnostic::error(
                "E-CALC-RELATION",
                "a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`",
            )
            .with_label(span, "this chain has steps in both directions")
            .with_note(
                "write the steps all with `<`/`<=` or all with `>`/`>=` (`=` goes with either)",
            ));
        }
        if descending {
            let (first, steps) = reverse_calc(first, steps);
            return Ok(Expr::Calc {
                span,
                first: Box::new(first),
                steps,
            });
        }
        Ok(Expr::Calc {
            span,
            first: Box::new(first),
            steps,
        })
    }

    /// `rewrite p, <- q at h in t`, after `rewrite`: rules separated by
    /// commas, each optionally `<-`, then (optionally) `at` and the target,
    /// then (optionally) `in` and the body. `at` and `in` are only special
    /// where a rule could end: outside brackets, inside a rule (and `in`
    /// inside the target).
    #[inline(never)]
    fn rewrite_expr(&mut self, start: Span) -> Result<Expr> {
        let saved = (self.rewrite_rule.take(), self.rewrite_at);
        let result = self.rewrite_body(start);
        (self.rewrite_rule, self.rewrite_at) = saved;
        result
    }

    #[inline(never)]
    fn rewrite_body(&mut self, start: Span) -> Result<Expr> {
        let column = self.tokens[self.pos - 1].column;
        let mut rules: Vec<RewriteRule> = Vec::new();
        loop {
            let rule_start = self.here();
            let reverse = self.peek() == Some(&Tok::Lt)
                && self.peek_at(1) == Some(&Tok::Minus)
                && self.tokens[self.pos].span.end == self.tokens[self.pos + 1].span.start;
            if reverse {
                self.bump();
                self.bump();
            }
            self.rewrite_rule = Some(self.pos);
            self.rewrite_at = true;
            let proof = self.append_expr();
            self.rewrite_rule = None;
            let proof = proof?;
            rules.push(RewriteRule {
                reverse,
                span: rule_start.to(proof.span()),
                proof,
            });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        let word = |p: &Self, w: &str| matches!(p.peek(), Some(Tok::Lower(x)) if x == w);
        let target = if word(self, "at") {
            let at = self.bump().span;
            if self.peek().is_none_or(|t| *t == Tok::KwIn) || self.is_stop(self.pos) {
                return Err(rewrite_at_without_target(at));
            }
            self.rewrite_rule = Some(self.pos);
            self.rewrite_at = false;
            let target = self.append_expr();
            self.rewrite_rule = None;
            Some(Box::new(target?))
        } else {
            None
        };
        // `in` may also start a line of its own, at the `rewrite`'s column or
        // right of it, where the enclosing block's column would end the
        // expression: no statement starts with `in`.
        let own_line = self
            .tokens
            .get(self.pos)
            .is_some_and(|t| t.tok == Tok::KwIn && t.line_start && t.column >= column);
        let body = if self.peek() == Some(&Tok::KwIn) || own_line {
            let first = self.bump().span;
            let body_start = self.pos;
            let body = self.expr()?;
            self.rewrite_membership(&body, body_start, first)?;
            Some(Box::new(body))
        } else {
            None
        };
        let end = body
            .as_ref()
            .or(target.as_ref())
            .map_or_else(|| rules.last().expect("a rule").span, |b| b.span());
        Ok(Expr::Rewrite {
            rules,
            target,
            body,
            span: start.to(end),
        })
    }

    /// `cases` or `cases in t`, after the `cases` (docs/proposals/simp.md
    /// §5.1). As for `rewrite`, the body runs to the end of the expression.
    fn cases_expr(&mut self, start: Span) -> Result<Expr> {
        if self.peek() != Some(&Tok::KwIn) {
            return Ok(Expr::Cases {
                body: None,
                span: start,
            });
        }
        self.bump();
        let body = self.expr()?;
        Ok(Expr::Cases {
            span: start.to(body.span()),
            body: Some(Box::new(body)),
        })
    }

    /// A `rewrite` body that is a membership test, `x in xs`, its `in` not
    /// in brackets: `rewrite h x in xs in t` reads as the rule `h x` and the
    /// body `xs in t`, since a bare `in` ends a rule. Whichever was meant,
    /// brackets say it (D1201).
    #[inline(never)]
    fn rewrite_membership(&self, body: &Expr, body_start: usize, first: Span) -> Result<()> {
        let Expr::Binary(BinOp::In(op), ..) = body else {
            return Ok(());
        };
        let op_index = self.tokens.partition_point(|t| t.span.start < op.start);
        let depth = self.tokens[body_start..op_index]
            .iter()
            .fold(0i64, |d, t| match t.tok {
                Tok::LBracket | Tok::LParen | Tok::LBrace => d + 1,
                Tok::RBracket | Tok::RParen | Tok::RBrace => d - 1,
                _ => d,
            });
        if depth > 0 {
            return Ok(());
        }
        Err(Diagnostic::error(
            "E-PARSE",
            "a membership test in a `rewrite` needs brackets",
        )
        .with_label(first, "this `in` ends the rewrite rule")
        .with_label(*op, "so this `in` is read as a membership test in the body")
        .with_note(
            "a bare `in` ends a `rewrite` rule, so membership in a rule is written in brackets, \
             `rewrite h (x in xs) in …`; a membership test as the body is bracketed too, \
             `rewrite h in (x in xs)`",
        ))
    }

    /// `(x : A) -> B` or `[x : A] -> B`. Out of line, as `if_expr` is.
    #[inline(never)]
    fn pi_expr(&mut self, start: Span, implicit: bool) -> Result<Expr> {
        let (binder, auto) = if implicit {
            self.implicit_binder()?
        } else {
            (self.binder()?, false)
        };
        if let Some(first) = binder.attrs.first() {
            return Err(misplaced_attributes(first, "a function type's parameter"));
        }
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
        if self.eat(&Tok::KwCalc) {
            return self.calc_expr(start);
        }
        if self.eat(&Tok::KwRewrite) {
            return self.rewrite_expr(start);
        }
        if self.eat(&Tok::KwCases) {
            return self.cases_expr(start);
        }
        if self.lambda_ahead()? {
            return self.lambda(start);
        }
        if let Some(colon) = self.lambda_result_type_ahead() {
            return Err(lambda_result_type(self.tokens[colon].span));
        }
        if self.peek() == Some(&Tok::KwExists) {
            return self.exists_expr();
        }
        if self.eat(&Tok::KwIf) {
            return self.if_expr(start);
        }
        let implicit = self.is_implicit_binder();
        if implicit || self.is_pi_binder() {
            return self.pi_expr(start, implicit);
        }
        let section = self.peek() == Some(&Tok::Dot);
        let mut lhs = self.cmp_expr()?;
        if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
            self.logic_chain(&mut lhs)?;
        }
        if self.peek() == Some(&Tok::Iff) {
            self.iff(&mut lhs)?;
        }
        if self.eat(&Tok::Arrow) {
            let rhs = self.result_type()?;
            return Ok(Expr::Arrow(Box::new(lhs), Box::new(rhs)));
        }
        if section {
            sections::widen(&mut lhs);
        }
        Ok(lhs)
    }

    /// `p <-> q`, after `p`: `Iff p q` (D1202). Looser than `&&` and `||`,
    /// tighter than `->`, and not associative, as in Rocq. The right
    /// side may be an `exists`. Out of line, as `logic_chain` is.
    #[inline(never)]
    fn iff(&mut self, operand: &mut Expr) -> Result<()> {
        let op = self.bump().span;
        let rhs = if self.peek() == Some(&Tok::KwExists) {
            self.exists_expr()?
        } else {
            let mut rhs = self.cmp_expr()?;
            if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
                self.logic_chain(&mut rhs)?;
            }
            rhs
        };
        if self.peek() == Some(&Tok::Iff) {
            return Err(Diagnostic::error("E-PARSE", "`<->` doesn't chain")
                .with_label(self.here(), "a second `<->`")
                .with_note("`p <-> q <-> r` could mean either grouping: add brackets"));
        }
        let lhs = std::mem::replace(operand, Expr::Prop(Span::NOWHERE));
        let iff = Expr::Var(Name {
            text: "Std.Iff".into(),
            span: op,
        });
        *operand = Expr::App(
            Box::new(Expr::App(Box::new(iff), Box::new(lhs))),
            Box::new(rhs),
        );
        Ok(())
    }

    /// `exists (x: T) => P`, at the `exists`: `Exists T ((x: T) => P)`
    /// (D1203). What follows is a lambda, its type left out where it can be
    /// inferred (`exists k => P k`); several parameters nest, so
    /// `exists (a b: Nat) => P` is `exists (a: Nat) => exists (b: Nat) => P`.
    #[inline(never)]
    fn exists_expr(&mut self) -> Result<Expr> {
        let keyword = self.bump().span;
        if !self.lambda_ahead()? {
            return Err(self
                .unexpected("a parameter and `=>` after `exists`")
                .with_note("\"there exists\" is written `exists (x: T) => P`"));
        }
        let start = self.here();
        let lambda = self.lambda(start)?;
        let outer = lambda.span();
        Ok(exists_chain(keyword, lambda, outer))
    }

    /// `[ name+ :` starts an implicit binder, as does `[auto` followed by an
    /// uppercase name (`[auto Ord a] -> …`, an auto parameter without a
    /// name); `[a, b]` is a list literal.
    fn is_implicit_binder(&self) -> bool {
        if self.peek() != Some(&Tok::LBracket) {
            return false;
        }
        if self.nameless_auto_at(self.pos) {
            return true;
        }
        let mut i = self.pos + 1;
        // Past attributes, `[@[js.name "n"] count: Nat]`.
        while self.tokens.get(i).map(|t| &t.tok) == Some(&Tok::At)
            && let Some(&close) = self.matching.get(i + 1)
            && close != NO_PARTNER
        {
            i = close as usize + 1;
        }
        let first_name = i;
        while let Some(Token {
            tok: Tok::Lower(_), ..
        }) = self.tokens.get(i)
        {
            i += 1;
        }
        i > first_name && self.tokens.get(i).map(|t| &t.tok) == Some(&Tok::Colon)
    }

    /// Whether the `[` at token `i` opens an auto binder without a name,
    /// `[auto Ord a]`: `auto` followed by an uppercase name.
    fn nameless_auto_at(&self, i: usize) -> bool {
        matches!(self.tokens.get(i + 1).map(|t| &t.tok), Some(Tok::Lower(w)) if w == "auto")
            && matches!(self.tokens.get(i + 2).map(|t| &t.tok), Some(Tok::Upper(_)))
    }

    /// `[x y : A]`, or `[auto x : P]`, or `[auto P]`. Returns whether it's
    /// `auto`.
    fn implicit_binder(&mut self) -> Result<(Binder, bool)> {
        if self.nameless_auto_at(self.pos) {
            self.bump();
            let auto = self.bump().span;
            let ty = self.expr()?;
            self.expect(Tok::RBracket, "`]`")?;
            let names = vec![Name {
                text: crate::ast::NAMELESS.to_string(),
                span: auto,
            }];
            return Ok((
                Binder {
                    names,
                    ty,
                    attrs: Vec::new(),
                },
                true,
            ));
        }
        self.expect(Tok::LBracket, "`[`")?;
        let attrs = self.attributes()?;
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
        Ok((Binder { names, ty, attrs }, auto))
    }

    /// Whether a lambda starts here: a run of one or more parameters followed
    /// by `=>` (docs/proposals/lambda-syntax.md §5.1). A parameter is a
    /// lower-case name (unqualified), `_`, or a bracketed group (`(`, `{`, or
    /// `[` opening an implicit binder), which the scan skips in one step with
    /// the bracket table. The run continues while the next token isn't a
    /// stop, and the `=>` after it isn't one either. Nothing is consumed.
    /// An implicit group is `[a: Type]`, `[auto h: P]` or `[auto P]` (§4.3).
    #[inline(never)]
    fn lambda_ahead(&self) -> Result<bool> {
        let mut i = self.pos;
        let mut count = 0;
        while i < self.tokens.len() && !self.is_stop(i) {
            match &self.tokens[i].tok {
                Tok::Lower(w) if !w.contains('.') => i += 1,
                Tok::Underscore => i += 1,
                Tok::LParen | Tok::LBrace => match self.matching[i] {
                    NO_PARTNER => return Ok(false),
                    close => i = close as usize + 1,
                },
                Tok::LBracket if self.implicit_group_at(i) || self.nameless_auto_at(i) => {
                    match self.matching[i] {
                        NO_PARTNER => return Ok(false),
                        close => i = close as usize + 1,
                    }
                }
                _ => break,
            }
            count += 1;
        }
        Ok(count > 0
            && i < self.tokens.len()
            && self.tokens[i].tok == Tok::FatArrow
            && !self.is_stop(i))
    }

    /// The `:` of a lambda written with a result type, `(x: A): B => body`:
    /// a run of parameters ending in a bracketed one, then `:`, then a `=>`
    /// later in the expression. Nothing is consumed.
    #[inline(never)]
    fn lambda_result_type_ahead(&self) -> Option<usize> {
        let mut i = self.pos;
        let mut bracketed_last = false;
        while i < self.tokens.len() && !self.is_stop(i) {
            match &self.tokens[i].tok {
                Tok::Lower(w) if !w.contains('.') => {
                    i += 1;
                    bracketed_last = false;
                }
                Tok::Underscore => {
                    i += 1;
                    bracketed_last = false;
                }
                Tok::LParen | Tok::LBracket => match self.matching[i] {
                    NO_PARTNER => return None,
                    close => {
                        i = close as usize + 1;
                        bracketed_last = true;
                    }
                },
                _ => break,
            }
        }
        if !bracketed_last || self.tokens.get(i).map(|t| &t.tok) != Some(&Tok::Colon) {
            return None;
        }
        let colon = i;
        i += 1;
        while i < self.tokens.len() && !self.is_stop(i) {
            match &self.tokens[i].tok {
                Tok::FatArrow => return Some(colon),
                Tok::ColonEq => return None,
                Tok::LParen | Tok::LBracket | Tok::LBrace => match self.matching[i] {
                    NO_PARTNER => return None,
                    close => i = close as usize + 1,
                },
                _ => i += 1,
            }
        }
        None
    }

    /// Whether the `[` at token `i` opens an implicit binder: `[name+ :`
    /// (this covers `[auto name :`), or `[name+]`, one missing its type,
    /// which `header_param` reports when it ends a lambda's run.
    fn implicit_group_at(&self, i: usize) -> bool {
        let mut j = i + 1;
        while matches!(
            self.tokens.get(j),
            Some(Token {
                tok: Tok::Lower(_),
                ..
            })
        ) {
            j += 1;
        }
        j > i + 1
            && matches!(
                self.tokens.get(j),
                Some(Token {
                    tok: Tok::Colon | Tok::RBracket,
                    ..
                })
            )
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
        match self.matching[self.pos] {
            NO_PARTNER => false,
            close => self.tokens.get(close as usize + 1).map(|t| &t.tok) == Some(&Tok::Arrow),
        }
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
            // `p && exists (x: T) => q`: the `exists` takes the rest.
            let operand = if self.peek() == Some(&Tok::KwExists) {
                self.exists_expr()?
            } else {
                self.cmp_expr()?
            };
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

    /// `x |> f a |> g`: tighter than comparisons, `in`, `&&` and `||`,
    /// looser than `++`, grouping to the left, so a pipeline reads top to
    /// bottom and `xs |> List.sum == 6` compares the sum. A line may start
    /// with `|>` to continue the expression, if it's indented at least as
    /// far as the line the expression starts on. The right side is an
    /// operand at the level of `++` (an application, usually), or a lambda,
    /// whose body takes the rest of the expression: `x |> y => f y |> g` is
    /// `x |> y => (f y |> g)`, which means the same as
    /// `(x |> y => f y) |> g`. Out of line and in a loop, as `logic_chain`
    /// is.
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
            let rhs = if self.lambda_ahead()? {
                let start = self.here();
                self.lambda(start)?
            } else {
                let section = self.peek() == Some(&Tok::Dot);
                let mut rhs = self.append_expr()?;
                if section {
                    sections::widen(&mut rhs);
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

    /// `a = b`, `a != b`, `a == b`, `a < b`, `a <= b`, `a > b`, `a >= b`: not
    /// associative. Each operand may be a pipeline.
    fn cmp_expr(&mut self) -> Result<Expr> {
        let lhs_start = self.pos;
        let mut lhs = self.append_expr()?;
        if self.at_pipe() {
            self.pipe_chain(&mut lhs)?;
        }
        if matches!(self.peek(), Some(Tok::KwIn | Tok::NotIn)) {
            return self.membership(lhs, lhs_start);
        }
        let (op, flip) = match self.peek() {
            Some(Tok::Equals) => (BinOp::Eq, false),
            Some(Tok::NotEq) => (BinOp::Ne, false),
            Some(Tok::EqEq) => (BinOp::EqEq, false),
            Some(Tok::Lt) => (BinOp::Lt, false),
            Some(Tok::Le) => (BinOp::Le, false),
            // `a > b` is `b < a`, `a >= b` is `b <= a`: the same terms, so
            // goals and messages show `<` and `<=`.
            Some(Tok::Gt) => (BinOp::Lt, true),
            Some(Tok::Ge) => (BinOp::Le, true),
            _ => return Ok(lhs),
        };
        self.bump();
        let mut rhs = self.append_expr()?;
        if self.at_pipe() {
            self.pipe_chain(&mut rhs)?;
        }
        Ok(binary(op, flip, lhs, rhs))
    }

    /// `x in c` or `x !in c`, after `x` (which starts at token `lhs_start`):
    /// at the level of `=`, not associative (D1201). `x !in c` is `!(x in c)`.
    #[inline(never)]
    fn membership(&mut self, lhs: Expr, lhs_start: usize) -> Result<Expr> {
        let token = self.bump();
        let (op, negated) = (token.span, token.tok == Tok::NotIn);
        // `!x in xs` is `(!x) in xs`, since `!` binds tighter: almost
        // certainly not what was meant.
        if self.tokens[lhs_start].tok == Tok::Bang {
            let bang = self.tokens[lhs_start].span;
            return Err(Diagnostic::error(
                "E-PARSE",
                "`!` here applies to the element, not to the membership test",
            )
            .with_label(bang, "this `!` binds tighter than `in`")
            .with_label(
                op,
                "so this tests whether the negated element is in the collection",
            )
            .with_note(
                "for \"not in\", write `x !in xs`; if the element really is negated, bracket \
                 it: `(!x) in xs`",
            ));
        }
        let mut rhs = self.append_expr()?;
        if self.at_pipe() {
            self.pipe_chain(&mut rhs)?;
        }
        let member = Expr::Binary(BinOp::In(op), Box::new(lhs), Box::new(rhs));
        if !negated {
            return Ok(member);
        }
        Ok(prefix_op(true, op, member))
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

    /// A prefix minus or `!` (which may repeat), tighter than `*` and looser
    /// than application and dots: `-x.abs` is `-(x.abs)`, `-f x` is `-(f x)`,
    /// `!xs.isEmpty` is `Bool.not (xs.isEmpty)`.
    fn unary(&mut self) -> Result<Expr> {
        // A `match` as an operand: `1 + match n with | …`. Its last
        // alternative's body takes whatever follows.
        if self.peek() == Some(&Tok::KwMatch) {
            let start = self.bump().span;
            return self.match_expr(start);
        }
        if let Some(prefix @ (Tok::Minus | Tok::Bang)) = self.peek() {
            self.deeper()?;
            let start = self.bump().span;
            let operand = self.unary()?;
            return Ok(prefix_op(prefix == &Tok::Bang, start, operand));
        }
        self.app()
    }

    fn app(&mut self) -> Result<Expr> {
        // A section's arguments are its own: `.drop 1` is `x => x.drop 1`.
        let section = self.peek() == Some(&Tok::Dot);
        let start = self.here();
        let bracketed = self.peek() == Some(&Tok::LParen);
        let mut expr = self.atom(true)?;
        if bracketed && matches!(expr, Expr::App(..)) && self.starts_atom() {
            let end = self.tokens[self.pos - 1].span;
            expr = Expr::Bracketed(Box::new(expr), start.to(end));
        }
        if let Expr::CtorFields { ctor, .. } = &expr
            && self.starts_atom()
        {
            return Err(self.ctor_fields_then_argument(ctor));
        }
        while self.starts_atom() {
            if self.peek() == Some(&Tok::Dot) && self.tokens[self.pos].line_start {
                return Err(self.section_line());
            }
            let arg = self.atom(false)?;
            if section && let Expr::Lam(_, body, span) = &mut expr {
                *span = span.to(arg.span());
                let f = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
                **body = Expr::App(Box::new(f), Box::new(arg));
                continue;
            }
            expr = Expr::App(Box::new(expr), Box::new(arg));
        }
        if self.peek() == Some(&Tok::KwCases) && self.peek_at(1) == Some(&Tok::KwIn) {
            return Err(self.cases_in_argument());
        }
        Ok(expr)
    }

    /// `C { … } x`: an argument after named construction. Out of line, like
    /// the other errors here, so it doesn't add to `app`'s stack frame, which
    /// every level of nesting pays for.
    #[inline(never)]
    fn ctor_fields_then_argument(&self, ctor: &Name) -> Diagnostic {
        error(
            self.here(),
            format!(
                "braces after `{}` name its fields, and take no further arguments",
                ctor.text
            ),
        )
        .with_note(format!(
            "to pass a record as `{0}`'s first argument, write it in brackets: \
             `{0} ({{ … }}) …`",
            ctor.text
        ))
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
                    | Tok::Float(_)
                    | Tok::Char(_)
                    | Tok::Str(_)
                    | Tok::StrStart(_)
                    | Tok::KwInclude
                    | Tok::KwOmega
                    | Tok::KwRing
                    | Tok::TypeU
                    | Tok::Prop
                    | Tok::LParen
                    | Tok::LBracket
                    | Tok::LBrace
                    | Tok::Underscore
                    | Tok::Question
            )
        ) || (self.peek() == Some(&Tok::Dot) && self.section_at(self.pos))
            || self.bare_cases()
    }

    /// Whether the next token is a `cases` with no `in` after it, which is
    /// a whole term and so can be an argument, as `omega` can.
    fn bare_cases(&self) -> bool {
        self.peek() == Some(&Tok::KwCases) && self.peek_at(1) != Some(&Tok::KwIn)
    }

    /// `f cases in t`: a `cases in` as an argument, whose body would take
    /// the rest of the line.
    #[inline(never)]
    fn cases_in_argument(&self) -> Diagnostic {
        error(
            self.tokens[self.pos].span,
            "`cases in …` as an argument needs brackets",
        )
        .with_note(
            "the body of `cases in` runs to the end of the expression, so as an argument \
             it's written `(cases in t)`",
        )
    }

    /// Whether the next tokens are `()` written right after the name or field
    /// before them, with the parens touching: `f()`, a zero-argument call. It
    /// is one atom, so `g f()` is `g (f())` and `f().x` is `(f()).x`. With a
    /// space, `f ()` is ordinary application to the unit.
    fn unit_call(&self) -> bool {
        let at = |i: usize| self.tokens.get(self.pos + i);
        let (Some(open), Some(close)) = (at(0), at(1)) else {
            return false;
        };
        open.tok == Tok::LParen
            && close.tok == Tok::RParen
            && self.pos > 0
            && self.tokens[self.pos - 1].span.end == open.span.start
            && open.span.end == close.span.start
    }

    /// An atom followed by any field accesses, `p.address.city`. The `.` is
    /// written with no space on either side.
    ///
    /// At the head of an application (`head`), a constructor followed by
    /// braces is named construction, `C { f = e, … }`
    /// (docs/proposals/variant-fields.md §4.5). As an argument it is
    /// refused: `f C { … }` could mean either `f (C { … })` or `f C ({ … })`.
    fn atom(&mut self, head: bool) -> Result<Expr> {
        let section = self.peek() == Some(&Tok::Dot);
        let start = self.here();
        let upper = matches!(self.peek(), Some(Tok::Upper(_)));
        let mut expr = self.atom_base()?;
        if upper && self.peek() == Some(&Tok::LBrace) {
            expr = self.ctor_fields_expr(expr, head)?;
        }
        loop {
            if matches!(expr, Expr::Var(_) | Expr::Field(..)) && self.unit_call() {
                let open = self.bump().span;
                let close = self.bump().span;
                expr = Expr::App(Box::new(expr), Box::new(Expr::Unit(open.to(close))));
            }
            if !(self.peek() == Some(&Tok::Dot) && !self.section_at(self.pos)) {
                break;
            }
            let dot = self.tokens[self.pos].span;
            let field = match self.tokens.get(self.pos + 1) {
                Some(Token {
                    tok: Tok::Lower(text) | Tok::Upper(text),
                    span,
                    ..
                }) if !text.contains('.') && self.peek_at(1).is_some() => Name {
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
                    "`.name args` is a method section, the function `x => x.name args`",
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

    /// `C { f = e, g }` after constructor `ctor`: its fields, named
    /// (docs/proposals/variant-fields.md §4.5). Not as an argument (`head`
    /// false), and not an update: those are written in brackets.
    #[inline(never)]
    fn ctor_fields_expr(&mut self, ctor: Expr, head: bool) -> Result<Expr> {
        let Expr::Var(ctor) = &ctor else {
            unreachable!("an uppercase name is a variable")
        };
        let ctor = ctor.clone();
        let brace = self.here();
        if !head {
            return Err(error(
                brace,
                format!("braces after `{}` as an argument need brackets", ctor.text),
            )
            .with_note(format!(
                "write `({0} {{ … }})` to build a `{0}` by its fields, or `{0} ({{ … }})` to \
                 pass `{0}` and a record",
                ctor.text
            )));
        }
        let Expr::Record { base, fields, span } = &mut self.record_expr()? else {
            unreachable!("record_expr makes a record")
        };
        let (fields, span) = (std::mem::take(fields), *span);
        if base.is_some() {
            return Err(error(
                brace,
                format!(
                    "braces after `{}` name its fields; an update isn't one of them",
                    ctor.text
                ),
            )
            .with_note(format!(
                "to pass an updated record as `{0}`'s argument, write it in brackets: \
                 `{0} ({{ r | … }})`",
                ctor.text
            )));
        }
        Ok(Expr::CtorFields {
            span: ctor.span.to(span),
            ctor,
            fields,
        })
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
    /// becoming `Std.Show.toText e`. Empty pieces are left out; the whole
    /// is wrapped so its span runs from the opening quote to the closing one.
    fn interpolated_str(&mut self) -> Result<Expr> {
        let token = self.bump();
        let open = token.span;
        let (mut text, mut text_span) = match &token.tok {
            Tok::StrStart(text) => (text.clone(), token.span),
            _ => unreachable!("called at a StrStart"),
        };
        let mut items = Vec::new();
        let mut first = true;
        let close;
        loop {
            if !text.is_empty() {
                items.push(Expr::Str(text, text_span));
            }
            // The `${` starts at the end of the first piece, and ends the
            // later ones.
            let dollar = if first {
                text_span.end
            } else {
                text_span.end - 2
            };
            first = false;
            let value = self.expr()?;
            let next = self
                .tokens
                .get(self.pos)
                .cloned()
                .ok_or_else(|| self.unexpected("`}`"))?;
            let span = Span::new(self.file, dollar, next.span.start);
            items.push(Expr::App(
                Box::new(Expr::Var(Name {
                    text: "Std.Show.toText".into(),
                    span,
                })),
                Box::new(value),
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
                close = next.span;
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
        Ok(Expr::Interpolated(Box::new(expr), open.to(close)))
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
            Some(Tok::Float(text)) => {
                let text = text.clone();
                self.bump();
                Ok(Expr::Float(text, span))
            }
            Some(Tok::Str(s)) => {
                let s = s.clone();
                self.bump();
                Ok(Expr::Str(s, span))
            }
            Some(Tok::StrStart(_)) => self.interpolated_str(),
            Some(Tok::KwInclude) => {
                self.bump();
                match self.peek() {
                    Some(Tok::Str(path)) => {
                        let path = path.clone();
                        let end = self.here();
                        self.bump();
                        Ok(Expr::Include(path, span.to(end)))
                    }
                    _ => {
                        Err(self
                            .unexpected("a path in quotes, as in `include \"inputs/day04.txt\"`"))
                    }
                }
            }
            Some(Tok::Char(c)) => {
                let c = *c;
                self.bump();
                Ok(Expr::Char(c, span))
            }
            Some(Tok::KwOmega) => {
                self.bump();
                // `omega [e1, e2]`: extra facts, by term.
                if self.peek() != Some(&Tok::LBracket) {
                    return Ok(Expr::Omega {
                        facts: Vec::new(),
                        span,
                    });
                }
                let Expr::List(facts, list_span) = &mut self.list_expr(self.here())? else {
                    unreachable!("list_expr makes a list")
                };
                Ok(Expr::Omega {
                    facts: std::mem::take(facts),
                    span: span.to(*list_span),
                })
            }
            Some(Tok::KwRing) => {
                self.bump();
                // `ring [h1, h2]`: hypotheses, by term.
                if self.peek() != Some(&Tok::LBracket) {
                    return Ok(Expr::Ring {
                        facts: Vec::new(),
                        span,
                    });
                }
                let Expr::List(facts, list_span) = &mut self.list_expr(self.here())? else {
                    unreachable!("list_expr makes a list")
                };
                Ok(Expr::Ring {
                    facts: std::mem::take(facts),
                    span: span.to(*list_span),
                })
            }
            Some(Tok::KwCases) if self.bare_cases() => {
                self.bump();
                Ok(Expr::Cases { body: None, span })
            }
            Some(Tok::Underscore) => {
                self.bump();
                Ok(Expr::Hole(span))
            }
            Some(Tok::Question) => {
                self.bump();
                Ok(Expr::Goal(span))
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
            // `(x := e)`: an explicit argument by name
            // (docs/proposals/named-arguments.md §4.1).
            Some(Tok::LParen)
                if matches!(self.peek_at(1), Some(Tok::Lower(_)))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                let name = self.lower("a name")?;
                self.bump();
                let value = self.expr()?;
                let end = self.expect(Tok::RParen, "`)`")?.span;
                Ok(Expr::NamedArg(
                    name,
                    Box::new(value),
                    span.to(end),
                    Bracket::Round,
                ))
            }
            Some(Tok::LParen) if self.operator_section_ahead() => self.operator_section(),
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
                if matches!(self.peek_at(1), Some(Tok::Lower(_) | Tok::KwDecreasing))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                // `[decreasing := p]`: the proof a recursive call of a
                // definition with `decreasing` needs.
                let name = if self.peek() == Some(&Tok::KwDecreasing) {
                    let span = self.bump().span;
                    Name {
                        text: "decreasing".to_string(),
                        span,
                    }
                } else {
                    self.lower("a name")?
                };
                self.bump();
                let value = self.expr()?;
                let end = self.expect(Tok::RBracket, "`]`")?.span;
                Ok(Expr::NamedArg(
                    name,
                    Box::new(value),
                    span.to(end),
                    Bracket::Square,
                ))
            }
            Some(Tok::LBracket) => self.list_expr(span),
            Some(Tok::LBrace) => self.record_expr(),
            Some(Tok::Dot) => self.section_start(),
            // A keyword as a lambda's parameter: `(test => …)`.
            _ if self.peek_at(1) == Some(&Tok::FatArrow) => {
                Err(self.unexpected_name("an expression"))
            }
            _ => Err(self.unexpected("an expression")),
        }
    }
}

/// `lhs op rhs`, or with `flip` `rhs op lhs`. Out of line, so the recursive
/// parsing functions keep small stack frames (nesting depth is bounded by
/// stack use).
#[inline(never)]
fn binary(op: BinOp, flip: bool, lhs: Expr, rhs: Expr) -> Expr {
    if flip {
        Expr::Binary(op, Box::new(rhs), Box::new(lhs))
    } else {
        Expr::Binary(op, Box::new(lhs), Box::new(rhs))
    }
}

/// `Exists _ (x => body)` for each parameter of `lambda`, the lambda after
/// `exists` at `keyword`: its layers are those whose span is `outer` (a
/// lambda in the body has a span of its own).
fn exists_chain(keyword: Span, lambda: Expr, outer: Span) -> Expr {
    let wrap = |param: Expr| {
        let exists = Expr::Var(Name {
            text: "Std.Exists".into(),
            span: keyword,
        });
        let applied = Expr::App(Box::new(exists), Box::new(Expr::Hole(keyword)));
        Expr::App(Box::new(applied), Box::new(param))
    };
    let mut lambda = lambda;
    let take = |b: &mut Box<Expr>| std::mem::replace(&mut **b, Expr::Prop(Span::NOWHERE));
    match &mut lambda {
        Expr::TypedLam(_, _, _, body, span) if *span == outer => {
            let inner = exists_chain(keyword, take(body), outer);
            **body = inner;
            wrap(lambda)
        }
        Expr::Lam(names, body, span) if *span == outer => {
            let span = *span;
            let mut inner = exists_chain(keyword, take(body), outer);
            let mut names = std::mem::take(names);
            while names.len() > 1 {
                let last = names.pop().expect("more than one");
                inner = wrap(Expr::Lam(vec![last], Box::new(inner), span));
            }
            wrap(Expr::Lam(names, Box::new(inner), span))
        }
        _ => lambda,
    }
}

/// `-operand`, or with `bang` `!operand`, which is `Std.Bool.not operand`.
#[inline(never)]
fn prefix_op(bang: bool, start: Span, operand: Expr) -> Expr {
    if bang {
        let not = Expr::Var(Name {
            text: "Std.Bool.not".into(),
            span: start,
        });
        return Expr::App(Box::new(not), Box::new(operand));
    }
    let span = start.to(operand.span());
    Expr::Neg(Box::new(operand), span)
}

/// `lhs |> rhs`; when `rhs` is a method section, the call it stands for on
/// `lhs`: `xs |> .drop 1` is `xs.drop 1`, with no function in between.
#[inline(never)]
fn piped(lhs: Expr, mut rhs: Expr) -> Expr {
    let Expr::Lam(names, body, _) = &mut rhs else {
        return Expr::Pipe(Box::new(lhs), Box::new(rhs));
    };
    if names.len() != 1 || names[0].text != SECTION || !sections::leads_with_section(body) {
        return Expr::Pipe(Box::new(lhs), Box::new(rhs));
    }
    let mut body = std::mem::replace(&mut **body, Expr::Hole(Span::NOWHERE));
    sections::fill_receiver(&mut body, lhs);
    body
}

/// A chain `a > b >= c` (its steps stored as `<`/`<=`, the proofs being of
/// the flipped forms `b < a`, `c <= b`) read the other way round:
/// `c <= b < a`. A step `_ = x` flips its proof with `Eq.sym`.
fn reverse_calc(first: Expr, steps: Vec<CalcStep>) -> (Expr, Vec<CalcStep>) {
    let mut elements = vec![first];
    elements.extend(steps.iter().map(|step| step.rhs.clone()));
    let mut reversed = Vec::new();
    for (i, mut step) in steps.into_iter().enumerate().rev() {
        step.rhs = elements[i].clone();
        if step.rel == BinOp::Eq
            && let Some(proof) = step.proof.take()
        {
            let sym = Expr::Var(Name {
                text: "Std.Eq.sym".into(),
                span: step.rel_span,
            });
            step.proof = Some(Expr::App(Box::new(sym), Box::new(proof)));
        }
        reversed.push(step);
    }
    (elements.pop().expect("a last element"), reversed)
}

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Lower(s) | Tok::Upper(s) => format!("`{s}`"),
        Tok::Num(n) => format!("`{n}`"),
        Tok::Float(text) => format!("`{text}`"),
        Tok::Str(s) => format!("`\"{s}\"`"),
        Tok::StrStart(_) | Tok::StrMid(_) | Tok::StrEnd(_) => "a text literal".into(),
        Tok::Char(c) => format!("`'{c}'`"),
        Tok::KwTest => "`test`".into(),
        Tok::KwInterface => "`interface`".into(),
        Tok::KwInstance => "`instance`".into(),
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
        Tok::Pipe => "`|`".into(),
        Tok::Plus => "`+`".into(),
        Tok::PlusPlus => "`++`".into(),
        Tok::Underscore => "`_`".into(),
        Tok::Question => "`?`".into(),
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
        Tok::KwInclude => "`include`".into(),
        Tok::KwNamespace => "`namespace`".into(),
        Tok::KwCalc => "`calc`".into(),
        Tok::KwRewrite => "`rewrite`".into(),
        Tok::KwOmega => "`omega`".into(),
        Tok::KwRing => "`ring`".into(),
        Tok::KwCases => "`cases`".into(),
        Tok::KwDecreasing => "`decreasing`".into(),
        Tok::KwOpaque => "`opaque`".into(),
        Tok::KwUnfolding => "`unfolding`".into(),
        Tok::LBrace => "`{`".into(),
        Tok::RBrace => "`}`".into(),
        Tok::FatArrow => "`=>`".into(),
        Tok::EqEq => "`==`".into(),
        Tok::Lt => "`<`".into(),
        Tok::Le => "`<=`".into(),
        Tok::Gt => "`>`".into(),
        Tok::Ge => "`>=`".into(),
        Tok::Bang => "`!`".into(),
        Tok::KwIn => "`in`".into(),
        Tok::NotIn => "`!in`".into(),
        Tok::Iff => "`<->`".into(),
        Tok::KwExists => "`exists`".into(),
        Tok::KwIf => "`if`".into(),
        Tok::KwThen => "`then`".into(),
        Tok::KwElse => "`else`".into(),
        Tok::Dot => "`.`".into(),
        Tok::DotDot => "`..`".into(),
        Tok::At => "`@[`".into(),
    }
}

/// `E-PARSE`: a lambda's parameter with a default value.
fn lambda_default(default: &Expr) -> Diagnostic {
    error(default.span(), declarations::DEFAULT_PLACES).with_note(
        "a lambda has no declaration to keep a default with: define the function with `def` \
         to give its parameters defaults",
    )
}

/// `E-PARSE`: a lambda written with a result type, `(x: A): B => body`.
fn lambda_result_type(colon: Span) -> Diagnostic {
    error(colon, "a lambda doesn't take a result type").with_note(
        "write the parameters' types only, `(x: A) => body`; to give the result's type too, \
         annotate the body, `(x: A) => (body: B)`, or the `let`, `let f: A → B := x => body`",
    )
}

/// `rewrite h at in t`: the `at` after a rule starts the hypothesis to
/// rewrite, so a hypothesis called `at` can't be an argument of the rule.
fn rewrite_at_without_target(at: Span) -> Diagnostic {
    error(
        at,
        "`at` after a `rewrite` rule names the hypothesis to rewrite, but no hypothesis follows it",
    )
    .with_note(
        "`at` is reserved after a rule, so a hypothesis called `at` can't be passed to the rule: \
         give the hypothesis another name",
    )
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
    fn indexed_families_have_indices_result_types_and_implicit_fields() {
        let module = parse(
            "type Sub (a: Type): (n: Nat) -> Fin n -> Type =\n  \
             | Here [m: Nat] (x: a): Sub a (Succ m) FZero\n  | There\n\n\
             def f: Vec a n -> Nat\n  | VCons [n := k] _ _ => k\n",
        );
        let Decl::Data {
            indices,
            sort,
            ctors,
            ..
        } = &module.decls[0]
        else {
            panic!("expected a data type");
        };
        let names: Vec<Option<&str>> = indices
            .iter()
            .map(|(n, _)| n.as_ref().map(|n| n.text.as_str()))
            .collect();
        assert_eq!(names, [Some("n"), None]);
        assert!(matches!(sort, Some(Expr::Type(0, _))));
        assert_eq!(ctors[0].implicit, [true, false]);
        assert!(ctors[0].result.is_some());
        assert!(ctors[1].result.is_none() && ctors[1].fields.is_empty());
        let Decl::Equation { patterns, .. } = &module.decls[2] else {
            panic!("expected an arm");
        };
        let Pattern::Ctor(_, args, _) = &patterns[0] else {
            panic!("expected a constructor pattern");
        };
        assert!(matches!(&args[0], Pattern::Named(n, p, _)
            if n.text == "n" && matches!(**p, Pattern::Var(_))));
        // A synonym has no indices.
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", "");
        assert!(parse_module(file, "type T: Nat -> Type = Nat\n").is_err());
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
    fn unit_call_is_one_atom() {
        let shape = |text: &str| match &expression(text).unwrap() {
            Expr::Field(r, n) => format!("{:?}.{}", matches!(**r, Expr::App(..)), n.text),
            Expr::App(f, _) => format!("app({})", matches!(**f, Expr::Field(..))),
            _ => "other".into(),
        };
        // `f().x` is `(f()).x`; `IO.readAll().lines` too.
        assert_eq!(shape("f().x"), "true.x");
        assert_eq!(shape("IO.readAll().lines"), "true.lines");
        // `f().g y` is `(f()).g y`: an application of a field of the call.
        let e = expression("f().g y").unwrap();
        let Expr::App(g, _) = &e else { panic!("{e:?}") };
        assert!(matches!(&**g, Expr::Field(r, n) if n.text == "g" && matches!(**r, Expr::App(..))));
        // Chains.
        let e = expression("f().x.y").unwrap();
        assert!(matches!(&e, Expr::Field(r, _) if matches!(**r, Expr::Field(..))));
        let e = expression("p.f().x").unwrap();
        assert!(matches!(&e, Expr::Field(r, _) if matches!(**r, Expr::App(..))));
        // A space keeps ordinary application: `f ().x` is `f (().x)`.
        assert_eq!(shape("f ().x"), "app(false)");
        // Without a following `.name`, `f()` is still one atom: `g f()` is
        // `g (f())`, while `g f ()` is `g f ()`.
        let e = expression("g f()").unwrap();
        assert!(matches!(&e, Expr::App(g, a)
            if matches!(**g, Expr::Var(_)) && matches!(**a, Expr::App(..))));
        let e = expression("g f ()").unwrap();
        assert!(matches!(&e, Expr::App(f, u)
            if matches!(**f, Expr::App(..)) && matches!(**u, Expr::Unit(..))));
        let e = expression("parseTurns IO.readAllLines()").unwrap();
        assert!(matches!(&e, Expr::App(_, a) if matches!(**a, Expr::App(..))));
        // `()` alone and `f ()` are unchanged.
        assert!(matches!(expression("()").unwrap(), Expr::Unit(..)));
        assert!(matches!(expression("f ()").unwrap(), Expr::App(..)));
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
        for bad in ["p. name", "p.1", "p.Foo.Bar"] {
            assert!(expression(bad).is_err(), "{bad}");
        }
        // A capitalised field names a function of the value's type, as in
        // `xs.Distinct` for `List.Distinct xs`.
        let e = expression("xs.Distinct").unwrap();
        assert!(
            matches!(&e, Expr::Field(r, n) if n.text == "Distinct" && matches!(**r, Expr::Var(_)))
        );
        let e = expression("on.Subsequence bank").unwrap();
        let Expr::App(_, arg) = &e else {
            panic!("{e:?}")
        };
        assert!(matches!(&**arg, Expr::Var(n) if n.text == "bank"));
        let Expr::App(f, _) = &e else { panic!("{e:?}") };
        assert!(matches!(&**f, Expr::Field(_, n) if n.text == "Subsequence"));
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

    /// Braces right after a constructor name its fields; a record pattern
    /// as its argument is in brackets (docs/proposals/variant-fields.md §4).
    #[test]
    fn constructor_field_patterns() {
        let module = parse(
            "def f : S -> S -> S -> Nat\n  | C { id, text = Cons x _, .. }, (W ({ name, .. })), (D { }) => 0\n",
        );
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!("expected an equation");
        };
        let Pattern::CtorFields {
            ctor,
            fields,
            rest: true,
            ..
        } = &patterns[0]
        else {
            panic!("expected named fields: {:?}", patterns[0]);
        };
        assert_eq!(ctor.text, "C");
        assert!(matches!(&fields[0].1, Pattern::Var(n) if n.text == "id"));
        assert!(
            matches!(&fields[1].1, Pattern::Ctor(n, args, _) if n.text == "Cons" && args.len() == 2)
        );
        assert!(matches!(&patterns[1], Pattern::Ctor(n, args, _)
            if n.text == "W" && matches!(&args[..], [Pattern::Record { rest: true, .. }])));
        assert!(
            matches!(&patterns[2], Pattern::CtorFields { fields, rest: false, .. }
            if fields.is_empty())
        );
        // Parses in a `match` arm, a `let`, a tuple, a list and after a
        // field's `=` (`parse` panics on an error).
        parse(
            "def g (s: S): Nat :=\n  let C { id, .. } := s\n  match s with\n    | (C { id }, [D { .. }]) => 0\n    | W { p = C { id, .. }, .. } => 1\n",
        );
    }

    #[test]
    fn braces_after_a_constructor_take_no_further_arguments() {
        let e = parse_error("def f : L -> Nat\n  | Cons { name, .. } rest => 0\n");
        assert!(e.message.contains("take no further arguments"), "{e:?}");
        assert!(e.notes[0].contains("Cons ({ … })"), "{e:?}");
        let e = parse_error("def f : E -> Nat\n  | MkEntry r { name, .. } => 0\n");
        assert!(e.message.contains("written in brackets"), "{e:?}");
    }

    /// Named construction (docs/proposals/variant-fields.md §4.5): braces
    /// right after a constructor at the head of an application name its
    /// fields; `C ({ … })` is a record argument.
    #[test]
    fn constructor_field_expressions() {
        let Expr::CtorFields { ctor, fields, .. } =
            &rhs("def f : S := Shape.Circle { id = \"a\", ref }\n")
        else {
            panic!("expected named construction");
        };
        assert_eq!(ctor.text, "Shape.Circle");
        assert_eq!(fields.len(), 2);
        assert!(matches!(&fields[1].1, Expr::Var(n) if n.text == "ref"));
        let Expr::App(head, arg) = &rhs("def f : S := W ({ name = n })\n") else {
            panic!("expected an application");
        };
        assert!(matches!(&**head, Expr::Var(n) if n.text == "W"));
        assert!(matches!(&**arg, Expr::Record { base: None, .. }));
        // After an operator, in brackets and lists, after a field's `=`, and
        // with a field access after the braces.
        assert!(matches!(
            &rhs("def f : Bool := x == C { }\n"),
            Expr::Binary(_, _, rhs) if matches!(&**rhs, Expr::CtorFields { .. })
        ));
        assert!(matches!(
            &rhs("def f : T := (C { a = 1 }).a\n"),
            Expr::Field(e, _) if matches!(&**e, Expr::CtorFields { .. })
        ));
        assert!(matches!(
            &rhs("def f : T := C { a = 1 }.a\n"),
            Expr::Field(e, _) if matches!(&**e, Expr::CtorFields { .. })
        ));
        parse("def f : T := [C { a = D { b } }, g (C { a })]\n");
        // A lower-case name keeps a record argument: `f { a = 1 }`.
        assert!(matches!(
            &rhs("def f : T := g { a = 1 }\n"),
            Expr::App(_, arg) if matches!(&**arg, Expr::Record { .. })
        ));
    }

    #[test]
    fn braces_after_a_constructor_expression_are_its_fields_alone() {
        let e = parse_error("def f : L := Cons { head = 1 } rest\n");
        assert!(e.message.contains("take no further arguments"), "{e:?}");
        assert!(e.notes[0].contains("Cons ({ … })"), "{e:?}");
        let e = parse_error("def f : L := g Cons { head = 1 }\n");
        assert!(e.message.contains("as an argument need brackets"), "{e:?}");
        assert!(e.notes[0].contains("(Cons { … })"), "{e:?}");
        let e = parse_error("def f : L := Some { r | a = 1 }\n");
        assert!(e.message.contains("an update isn't one of them"), "{e:?}");
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
    fn parses_interfaces_instances_and_auto_binders_without_names() {
        let module = parse(
            "interface Pretty (a: Type) = { pretty: a -> Text }\n\
             instance List.instPretty [auto Pretty a]: Pretty (List a) := { pretty = xs => \"\" }\n\
             def f: [auto Pretty a] -> a -> Text := x => Pretty.pretty x\n\
             def g: List [auto] -> Nat := 0\n",
        );
        assert!(matches!(
            &module.decls[0],
            Decl::Data { record: true, interface: true, ctors, .. } if ctors[0].fields.len() == 1
        ));
        let Decl::Signature { ty, instance, .. } = &module.decls[1] else {
            panic!("expected a signature");
        };
        assert!(*instance);
        assert!(matches!(
            ty,
            Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == crate::ast::NAMELESS
        ));
        let Decl::Signature { ty, instance, .. } = &module.decls[3] else {
            panic!("expected a signature");
        };
        assert!(!*instance);
        assert!(matches!(
            ty,
            Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == crate::ast::NAMELESS
        ));
        // `[auto]` is still a list.
        let Decl::Signature { ty, .. } = &module.decls[5] else {
            panic!("expected a signature");
        };
        assert!(matches!(ty, Expr::Arrow(..)));
        // An instance needs a body.
        let mut sources = SourceMap::new();
        let text = "interface I (a: Type) = { x: a }\ninstance n: I Nat\n";
        let file = sources.add("test.sw", text);
        assert!(parse_module(file, text).is_err());
    }

    #[test]
    fn parses_auto_parameters_of_types() {
        // docs/proposals/interfaces.md §7.5.
        let module = parse(
            "type Map (k: Type) (v: Type) [auto ord: Ord k] = { entries: List (k, v) }\n\
             type Tree (k: Type) [auto ord: Ord k] = | Leaf | Node (l: Tree k)\n\
             type Set (k: Type) [auto ord: Ord k] = Map k () [ord := ord]\n",
        );
        assert!(matches!(
            &module.decls[0],
            Decl::Data { record: true, params, auto_params, .. }
                if params.len() == 3 && auto_params == &[false, false, true]
        ));
        assert!(matches!(
            &module.decls[1],
            Decl::Data { record: false, auto_params, .. } if auto_params == &[false, true]
        ));
        // A synonym's is the definition's.
        let Decl::Signature {
            ty, synonym: true, ..
        } = &module.decls[2]
        else {
            panic!("expected a synonym");
        };
        let Expr::Pi { cod, .. } = ty else {
            panic!("expected a function type, got {ty:?}");
        };
        assert!(matches!(
            &**cod,
            Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == "ord"
        ));
        let d = parse_error("type T [a: Type] = { x: a }\n");
        assert!(d.message.contains("must be `auto`"), "{}", d.message);
        let d = parse_error("type T (a: Type) [auto Ord a] = { x: a }\n");
        assert!(d.message.contains("needs a name"), "{}", d.message);
    }

    #[test]
    fn decreasing_goes_after_the_result_type() {
        // `:=` may start a line at the declaration's column after it.
        for source in [
            "def f (n: Nat): Nat\n  decreasing n\n:=\n  f (n / 2) [decreasing := p]\n",
            "def f (n: Nat): Nat decreasing n := f (n / 2) [decreasing := p]\n",
            "def f (n: Nat): Nat -> Nat\n  decreasing n\n  | Zero => 0\n  | Succ k => k\n",
        ] {
            let module = parse(source);
            assert!(
                matches!(
                    &module.decls[0],
                    Decl::Signature {
                        decreasing: Some(_),
                        ..
                    }
                ),
                "{source}"
            );
            assert!(module.decls.len() >= 2, "{source}");
        }
        let module = parse("def f (n: Nat): Nat decreasing n := f (n / 2) [decreasing := p]\n");
        let Decl::Equation { rhs: Some(rhs), .. } = &module.decls[1] else {
            panic!("expected the body");
        };
        let Expr::App(_, arg) = rhs else {
            panic!("expected a call, got {rhs:?}");
        };
        assert!(matches!(&**arg, Expr::NamedArg(n, ..) if n.text == "decreasing"));
    }

    /// `opaque def`, and `unfolding` after the result type and after
    /// `decreasing` (docs/proposals/opaque-definitions.md §6.2, §6.3).
    #[test]
    fn opaque_and_unfolding() {
        for (source, export, names) in [
            ("opaque def f (n: Nat): Nat := n\n", false, vec![]),
            ("export opaque def f (n: Nat): Nat := n\n", true, vec![]),
            (
                "opaque def f (n: Nat): Nat unfolding g, Code := n\n",
                false,
                vec!["g", "Code"],
            ),
            (
                "opaque def f (n: Nat): Nat\n    decreasing n\n    unfolding A.g\n:=\n  n\n",
                false,
                vec!["A.g"],
            ),
            (
                "opaque def f: Nat -> Nat\n    unfolding g\n  | Zero => 0\n  | Succ k => k\n",
                false,
                vec!["g"],
            ),
        ] {
            let module = parse(source);
            let Decl::Signature {
                opaque: true,
                export: e,
                unfolding,
                ..
            } = &module.decls[0]
            else {
                panic!("not an opaque signature: {source}");
            };
            assert_eq!(*e, export, "{source}");
            let found: Vec<&str> = unfolding.iter().map(|n| n.text.as_str()).collect();
            assert_eq!(found, names, "{source}");
            assert!(module.decls.len() >= 2, "{source}");
        }
        let module = parse("theorem t: f 1 = 1\n    unfolding f\n  := rfl\n");
        assert!(matches!(
            &module.decls[0],
            Decl::Signature { theorem: true, opaque: false, unfolding, .. } if unfolding.len() == 1
        ));
        // A type that starts on its own line is a block; the clause on a line
        // at the block's column still ends it.
        for source in [
            "theorem t:\n  f 1 = 1\n  unfolding f\n  := rfl\n",
            "opaque def g (n: Nat):\n  Nat\n  decreasing n\n  unfolding f\n  := n\n",
        ] {
            let module = parse(source);
            assert!(
                matches!(&module.decls[0], Decl::Signature { unfolding, .. } if unfolding.len() == 1),
                "{source}"
            );
        }
        for (source, message) in [
            (
                "opaque theorem t: 1 = 1 := rfl\n",
                "a theorem can't be `opaque`",
            ),
            (
                "opaque instance i: Show Nat := s\n",
                "an instance can't be `opaque`",
            ),
            (
                "opaque export def f: Nat := 1\n",
                "`export` goes before `opaque`",
            ),
            (
                "instance i: Show Nat unfolding f := s\n",
                "an instance can't have `unfolding`",
            ),
            (
                "def f (n: Nat): Nat unfolding g decreasing n := n\n",
                "`decreasing` goes before `unfolding`",
            ),
            (
                "def f (n: Nat): Nat :=\n  def g (m: Nat): Nat unfolding h := m\n  g n\n",
                "a local definition can't have `unfolding`",
            ),
            (
                "def f (n: Nat): Nat :=\n  opaque def g (m: Nat): Nat := m\n  g n\n",
                "local definitions can't be `opaque`: only top-level ones can",
            ),
        ] {
            assert_eq!(parse_error(source).message, message, "{source}");
        }
    }

    /// `?` is a goal: an atom, so an argument too, and never a hole.
    #[test]
    fn a_question_mark_is_a_goal() {
        let module = parse("def x : Nat := f ? (?, _)\n");
        let Decl::Equation { rhs, .. } = &module.decls[1] else {
            panic!("expected an equation");
        };
        let Some(Expr::App(f, pair)) = rhs else {
            panic!("expected an application, got {rhs:?}");
        };
        let Expr::Tuple(first, second, _) = pair.as_ref() else {
            panic!("expected a tuple, got {pair:?}");
        };
        assert!(matches!(first.as_ref(), Expr::Goal(_)));
        assert!(matches!(second.as_ref(), Expr::Hole(_)));
        let Expr::App(_, goal) = f.as_ref() else {
            panic!("expected an application, got {f:?}");
        };
        assert!(matches!(goal.as_ref(), Expr::Goal(_)));
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
        let body = rhs("def f (u : Nat) : Nat :=\n  let g := x =>\n    say x\n    x\n  g 1\n");
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

    /// The alternatives of an or-pattern.
    fn or_alternatives(p: &Pattern) -> &[Pattern] {
        let Pattern::Or(alternatives, _) = p else {
            panic!("expected an or-pattern, got {p:?}");
        };
        alternatives
    }

    #[test]
    fn parses_or_patterns() {
        // On one line, one arm; a `|` that starts a line starts the next.
        let e = rhs(
            "def f (c : Char) : Nat :=\n  match c with\n    | 'k' | 'w' => 1\n    | Red | Green _ => 2\n    | _ => 3\n",
        );
        let (_, alts) = match_parts(&e);
        assert_eq!(alts.len(), 3);
        let first = or_alternatives(&alts[0].patterns[0]);
        assert!(matches!(
            first,
            [Pattern::Char('k', _), Pattern::Char('w', _)]
        ));
        assert!(matches!(
            or_alternatives(&alts[1].patterns[0]),
            [Pattern::Ctor(_, none, _), Pattern::Ctor(_, one, _)] if none.is_empty() && one.len() == 1
        ));
        assert!(matches!(alts[2].patterns[0], Pattern::Wildcard(_)));

        // `|` binds tighter than `,`.
        let e =
            rhs("def f (a : Nat) (b : Nat) : Nat := match a, b with | 0 | 1, Red | Green => 0\n");
        let (_, alts) = match_parts(&e);
        assert_eq!(alts.len(), 1);
        assert_eq!(or_alternatives(&alts[0].patterns[0]).len(), 2);
        assert_eq!(or_alternatives(&alts[0].patterns[1]).len(), 2);

        // Nested in brackets, a tuple and a list.
        let e = rhs(
            "def f (p : Nat) : Nat := match p with | Some ('a' | 'b') => 0 | (0 | 1, _) => 1 | [_, 'x' | 'y'] => 2\n",
        );
        let (_, alts) = match_parts(&e);
        let Pattern::Ctor(_, args, _) = &alts[0].patterns[0] else {
            panic!("{:?}", alts[0].patterns[0])
        };
        assert_eq!(or_alternatives(&args[0]).len(), 2);
        let Pattern::Tuple(a, _, _) = &alts[1].patterns[0] else {
            panic!("{:?}", alts[1].patterns[0])
        };
        assert_eq!(or_alternatives(a).len(), 2);
        let Pattern::Cons(_, rest, _) = &alts[2].patterns[0] else {
            panic!("{:?}", alts[2].patterns[0])
        };
        assert!(matches!(&**rest, Pattern::Cons(x, _, _) if or_alternatives(x).len() == 2));

        // In a definition's arms.
        let module = parse("def f: Colour -> Nat\n  | Red | Blue => 1\n  | _ => 2\n");
        let arms: Vec<&Pattern> = module
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::Equation { patterns, .. } => Some(&patterns[0]),
                _ => None,
            })
            .collect();
        assert_eq!(arms.len(), 2);
        assert_eq!(or_alternatives(arms[0]).len(), 2);
    }

    #[test]
    fn rejects_binding_in_or_patterns() {
        for text in [
            "def f (o : Nat) : Nat := match o with | Some x | None => 0\n",
            "def f (o : Nat) : Nat := match o with | Some (x | 0) => 0\n",
            "def f (o : Nat) : Nat := match o with | { name } | _ => 0\n",
        ] {
            let error = rhs_of(text).unwrap_err();
            assert_eq!(error.code, "E-OR-PATTERN-BINDS", "{text}");
        }
        assert!(rhs_of("def f (o : Nat) : Nat := match o with | Some _ | None => 0\n").is_ok());
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
    fn greater_than_is_less_than_flipped() {
        let cases = [
            ("a > b", "(Lt b a)"),
            ("a >= b", "(Le b a)"),
            ("a + 1 > b * 2", "(Lt (Mul b 2) (Add a 1))"),
            ("f x > y", "(Lt y (f x))"),
            ("a ++ b > y", "(Lt y (Append a b))"),
            ("a < b", "(Lt a b)"),
        ];
        for (text, want) in cases {
            assert_eq!(shape_of(text), want, "{text}");
        }
        // Not associative, like `<`.
        assert!(rhs_of("def g : Nat := a > b > c\n").is_err());
        // `>>` is not a token (yet).
        assert!(rhs_of("def g : Nat := a >> b\n").is_err());
    }

    #[test]
    fn bang_precedence() {
        let n = "Std.Bool.not";
        let cases = [
            ("!a", format!("({n} a)")),
            ("!f x", format!("({n} (f x))")),
            ("!x.abs", format!("({n} x.abs)")),
            ("!!a", format!("({n} ({n} a))")),
            ("!a > b", format!("(Lt b ({n} a))")),
            ("!a = b", format!("(Eq ({n} a) b)")),
            ("f (!a)", format!("(f ({n} a))")),
            ("a != b", "(Ne a b)".to_string()),
        ];
        for (text, want) in cases {
            assert_eq!(shape_of(text), want, "{text}");
        }
        let e = rhs_of("def g : Bool := !a && b\n").unwrap();
        assert!(matches!(e, Expr::Binary(BinOp::And, ..)), "{e:?}");
    }

    #[test]
    fn arrows_and_pipes_still_parse_beside_greater_than() {
        assert!(rhs_of("def g : Nat := x |> f\n").is_ok());
        assert!(rhs_of("def g : Nat := (x => y) a\n").is_ok());
        assert!(rhs_of("def g : Type := a -> b\n").is_ok());
        assert!(rhs_of("def g : Bool := x |> f > y\n").is_ok());
    }

    #[test]
    fn negative_number_patterns() {
        let module =
            parse("def f : Int -> Nat -> Option Int -> Nat\n  | (-1), 0, (Some (-20)) => 1\n");
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
    fn an_interpolated_text_spans_its_quotes() {
        for literal in [
            "\"${a}\"",
            "\"${a} and ${b}\"",
            "\"x ${a}\"",
            "\"${a} x\"",
            "\"x ${a} y\"",
            "\"${\"${a}\"}\"",
        ] {
            let source = format!("def f : Text := {literal}\n");
            let e = rhs(&source);
            assert!(matches!(e, Expr::Interpolated(..)), "{literal}: {e:?}");
            let span = e.span();
            assert_eq!(
                &source[span.start as usize..span.end as usize],
                literal,
                "{literal}"
            );
        }
    }

    #[test]
    fn parses_list_patterns() {
        let module = parse(
            "def f : A -> B -> C -> D -> E -> Nat\n  | [], [a], [a, b], [Some x, (-1)], (xs, [y]) => a\n",
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
        let module = parse("def f : A -> Nat\n  | (Some a, b) => a\n");
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(matches!(&patterns[0], Pattern::Tuple(l, _, _)
            if matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1)));

        let e = rhs("def f (p : Nat) : Nat :=\n  let (Some a, b) := p\n  a\n");
        let (_, p, _) = let_parts(&e);
        assert!(matches!(p, Pattern::Tuple(l, _, _)
            if matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1)));
    }

    #[test]
    fn parses_constructors_with_arguments_in_later_tuple_components() {
        let module = parse("def f : A -> Nat\n  | (Some x, Some y, Some z) => x\n");
        let Decl::Equation { patterns, .. } = &module.decls[1] else {
            panic!()
        };
        // (Some x, (Some y, Some z)): every component keeps its argument.
        let Pattern::Tuple(l, r, _) = &patterns[0] else {
            panic!()
        };
        assert!(matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1));
        assert!(matches!(&**r, Pattern::Tuple(m, n, _)
            if matches!(&**m, Pattern::Ctor(_, a, _) if a.len() == 1)
                && matches!(&**n, Pattern::Ctor(_, a, _) if a.len() == 1)));
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

        let (names, body) = lam("def f : Nat := (a, b) => a\n");
        assert_eq!(names[0].text, "%arg0");
        assert_eq!(lambda_match(&body), (1, 1));

        let (names, body) = lam("def f : Nat := acc (k, v) => acc\n");
        let texts: Vec<_> = names.iter().map(|n| n.text.as_str()).collect();
        assert_eq!(texts, ["acc", "%arg1"]);
        assert_eq!(lambda_match(&body), (1, 1));

        let (names, body) = lam("def f : Nat := { name, .. } => name\n");
        assert_eq!(names[0].text, "%arg0");
        assert_eq!(lambda_match(&body), (1, 1));

        let (_, body) = lam("def f : Nat := (MkPair a b) => a\n");
        assert_eq!(lambda_match(&body), (1, 1));

        let (names, body) = lam("def f : Nat := (a, b) (c, d) => a\n");
        assert_eq!(names.len(), 2);
        assert_eq!(lambda_match(&body), (2, 2));

        // Plain parameters are unchanged.
        let (names, body) = lam("def f : Nat := x y => x\n");
        assert_eq!(names.len(), 2);
        assert!(matches!(body, Expr::Var(_)));
        let (names, body) = lam("def f : Nat := (x) _ => x\n");
        assert_eq!(names.len(), 2);
        assert!(matches!(body, Expr::Var(_)));
    }

    #[test]
    fn lambda_parameters_may_be_annotated() {
        // (name, type, body) of a typed lambda.
        fn typed(e: &Expr) -> (String, String, Expr) {
            match e {
                Expr::TypedLam(name, Mode::Explicit, ty, body, _) => {
                    (name.text.clone(), pshape(ty), body.as_ref().clone())
                }
                other => panic!("expected a typed lambda, got {other:?}"),
            }
        }
        let (name, ty, body) = typed(&rhs("def f : Nat := (x: Nat) => x\n"));
        assert_eq!((name.as_str(), ty.as_str()), ("x", "Nat"));
        assert!(matches!(body, Expr::Var(_)));
        // With a space before the colon, too.
        typed(&rhs("def f : Nat := (x : Nat) => x\n"));
        // Several parameters nest, in order; a group shares one type.
        let (name, _, body) = typed(&rhs("def f : Nat := (x y: Nat) => x\n"));
        assert_eq!(name, "x");
        let (name, ty, _) = typed(&body);
        assert_eq!((name.as_str(), ty.as_str()), ("y", "Nat"));
        let (_, _, body) = typed(&rhs("def f : Nat := (x: Nat) (y: Bool) => x\n"));
        assert!(matches!(body, Expr::TypedLam(..)));
        // Mixed with plain parameters: `x (y: Nat)` is a `Lam` around a
        // `TypedLam`.
        match &rhs("def f : Nat := x (y: Nat) => x\n") {
            Expr::Lam(names, body, _) => {
                assert_eq!(names.len(), 1);
                assert!(matches!(**body, Expr::TypedLam(..)));
            }
            other => panic!("expected a lambda, got {other:?}"),
        }
        let (_, _, body) = typed(&rhs("def f : Nat := (x: Nat) y z => x\n"));
        assert!(matches!(&body, Expr::Lam(names, _, _) if names.len() == 2));
        // A parenthesised name alone is still a plain parameter.
        assert!(matches!(rhs("def f : Nat := (x) => x\n"), Expr::Lam(..)));
        // A missing type or closing bracket is an error.
        assert!(rhs_of("def f : Nat := (x:) => x\n").is_err());
        assert!(rhs_of("def f : Nat := (x: Nat => x\n").is_err());
    }

    /// The first error's message and notes, for a source that must fail.
    fn error_text(text: &str) -> String {
        let e = rhs_of(text).expect_err("expected a parse error");
        format!("{} {}", e.message, e.notes.join(" "))
    }

    /// docs/proposals/lambda-syntax.md §5.1, layout rule: the run and its
    /// `=>` follow the parser's existing continuation rule.
    #[test]
    fn a_lambdas_run_follows_the_layout_rule() {
        let lam_names = |e: &Expr| match e {
            Expr::Lam(names, _, _) => names.len(),
            other => panic!("expected a lambda, got {other:?}"),
        };
        // The body on the next line, indented.
        let e = rhs("def f : Nat :=\n  x y =>\n    x\n");
        assert_eq!(lam_names(&e), 2);
        // A second parameter on a continuation line.
        let e = rhs("def f : Nat :=\n  x\n    y =>\n      x\n");
        assert_eq!(lam_names(&e), 2);
        // `=>` at the block's column is a stop: `x y` is a statement.
        let text = "def f : Nat :=\n  x y\n  => x\n";
        assert!(error_text(text).contains("=>"), "{}", error_text(text));
        // A second line at the block's column starts a new statement.
        let e = rhs("def f : Nat :=\n  f x\n  y => y\n");
        assert_eq!(lines(&e), ["_", "result"]);
        let Expr::Seq(_, last) = &e else { panic!() };
        assert_eq!(lam_names(last), 1);
    }

    #[test]
    fn lambda_positions() {
        let is_lam = |e: &Expr| matches!(e, Expr::Lam(..) | Expr::TypedLam(..));
        // `_` as a parameter, and a lambda returning a lambda.
        assert!(is_lam(&rhs("def f : Nat := _ => 0\n")));
        assert!(is_lam(&rhs("def f : Nat := x => y => x\n")));
        // Arguments need brackets, and with them the application is ordinary.
        assert!(matches!(
            rhs("def f : Nat := List.map (x => x) xs\n"),
            Expr::App(..)
        ));
        // Both branches of an `if`, and a record field.
        let e = rhs("def f : Nat := if c then x => a else y => b\n");
        let Expr::If {
            then, otherwise, ..
        } = &e
        else {
            panic!("expected an if")
        };
        assert!(is_lam(then) && is_lam(otherwise));
        assert!(matches!(
            rhs("def f : Nat := { f = x => x + 1 }\n"),
            Expr::Record { .. }
        ));
        // In an arm's result, and after `|>`.
        let e = rhs("def f : Nat := match n with | Zero => x => x | Succ k => g k\n");
        assert!(matches!(e, Expr::Match { .. }));
        assert!(matches!(
            rhs("def f : Nat := xs |> ys => ys\n"),
            Expr::Pipe(..)
        ));
        // `f x => e` is a lambda with parameters `f` and `x`.
        let e = rhs("def f : Nat := map x => x + 1\n");
        let Expr::Lam(names, _, _) = &e else {
            panic!("expected a lambda")
        };
        assert_eq!(names.len(), 2);
    }

    #[test]
    fn what_is_not_a_lambda() {
        // A bare constructor or number isn't a parameter: use brackets.
        assert!(rhs_of("def f : Nat := Trivial => 1\n").is_err());
        assert!(rhs_of("def f : Nat := 0 => 1\n").is_err());
        assert!(matches!(
            rhs("def f : Nat := (Trivial) => 1\n"),
            Expr::Lam(..)
        ));
        // A qualified name or dot access can't be a parameter, so a forgotten
        // bracket is an error with a note.
        for text in [
            "def f : Nat := List.map x => x + 1\n",
            "def f : Nat := xs.map x => x + 1\n",
            "def f : Nat := Some x => x\n",
        ] {
            let message = error_text(text);
            assert!(message.contains("put it in brackets"), "{text}: {message}");
        }
        // After an operator the operand isn't a lambda position.
        assert!(rhs_of("def f : Nat := a + x => e\n").is_err());
        // An unclosed bracket isn't skipped over.
        assert!(rhs_of("def f : Nat := (a, b => e\n").is_err());
    }

    #[test]
    fn a_lambda_takes_no_result_type() {
        for text in [
            "def f : Nat := (x: Nat): Nat => x\n",
            "def f : Nat := a (x: Nat): List (Nat) => x\n",
            "def f : Nat :=\n  let g := (x: Nat): Nat => x\n  g 1\n",
        ] {
            let message = error_text(text);
            assert!(
                message.contains("doesn't take a result type"),
                "{text}: {message}"
            );
        }
        // An annotated body is still a lambda.
        assert!(matches!(
            rhs("def f : Nat := (x: Nat) => (x: Nat)\n"),
            Expr::TypedLam(..)
        ));
    }

    #[test]
    fn the_backslash_is_gone() {
        assert!(rhs_of("def f : Nat := \\x => x\n").is_err());
        let mut sources = SourceMap::new();
        let file = sources.add("t.sw", "\\");
        assert!(crate::lex(file, "\\").is_err());
    }

    /// docs/proposals/lambda-syntax.md §4.3 (D91): implicit and auto
    /// parameters are written as in a header, and each gets its mode.
    #[test]
    fn lambdas_bind_implicit_and_auto_parameters() {
        // (name, mode, type, body) of a typed lambda.
        fn typed(e: &Expr) -> (String, Mode, String, Expr) {
            match e {
                Expr::TypedLam(name, mode, ty, body, _) => {
                    (name.text.clone(), *mode, pshape(ty), body.as_ref().clone())
                }
                other => panic!("expected a typed lambda, got {other:?}"),
            }
        }
        let (name, mode, ty, body) = typed(&rhs("def f : Nat := [a: Kind] (x: a) => x\n"));
        assert_eq!(
            (name.as_str(), mode, ty.as_str()),
            ("a", Mode::Implicit, "Kind")
        );
        let (name, mode, _, body) = typed(&body);
        assert_eq!((name.as_str(), mode), ("x", Mode::Explicit));
        assert!(matches!(body, Expr::Var(_)));
        // On its own, and as a group sharing one type.
        let (_, mode, _, body) = typed(&rhs("def f : Nat := [a b: Kind] => a\n"));
        assert_eq!(mode, Mode::Implicit);
        let (name, mode, _, _) = typed(&body);
        assert_eq!((name.as_str(), mode), ("b", Mode::Implicit));
        // `auto`, with a name and without one.
        let (name, mode, ty, _) = typed(&rhs("def f : Nat := [auto h: Ord a] => h\n"));
        assert_eq!(
            (name.as_str(), mode, ty.as_str()),
            ("h", Mode::Auto, "(Ord a)")
        );
        let (name, mode, _, _) = typed(&rhs("def f : Nat := [auto Ord a] => 0\n"));
        assert_eq!((name.as_str(), mode), (crate::ast::NAMELESS, Mode::Auto));
        // Mixed with plain parameters, in any order.
        match &rhs("def f : Nat := x [a: Kind] y => x\n") {
            Expr::Lam(names, body, _) => {
                assert_eq!(names.len(), 1);
                let (_, mode, _, body) = typed(body);
                assert_eq!(mode, Mode::Implicit);
                assert!(matches!(&body, Expr::Lam(names, _, _) if names.len() == 1));
            }
            other => panic!("expected a lambda, got {other:?}"),
        }
        // The function type with the same start is unaffected, and so is a
        // list.
        assert!(matches!(
            rhs("def f : Nat := [a: Type] -> a -> a\n"),
            Expr::Pi { implicit: true, .. }
        ));
        assert!(matches!(rhs("def f : Nat := [a, b]\n"), Expr::List(..)));
        // A missing type is the header's error.
        let message = error_text("def f : Nat := [a] => a\n");
        assert!(message.contains("needs a type"), "{message}");
    }

    #[test]
    fn rejects_bad_pattern_bindings() {
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
    fn pipe_is_tighter_than_comparisons_and_looser_than_append() {
        let cases = [
            ("x |> f", "(|> x f)"),
            ("x |> f a b", "(|> x ((f a) b))"),
            ("a + b |> f", "(|> (Add a b) f)"),
            ("a ++ b |> f", "(|> (Append a b) f)"),
            ("x |> f ++ y", "(|> x (Append f y))"),
            ("a || b |> f", "(Or a (|> b f))"),
            ("a && b |> f", "(And a (|> b f))"),
            ("a = b |> f", "(Eq a (|> b f))"),
            ("a == b |> f", "(EqEq a (|> b f))"),
            ("(a == b) |> f", "(|> (EqEq a b) f)"),
            ("x |> f a == y", "(EqEq (|> x (f a)) y)"),
            ("xs |> List.sum == 6", "(EqEq (|> xs List.sum) 6)"),
            ("xs |> List.sum = 6", "(Eq (|> xs List.sum) 6)"),
            ("x |> f < y |> g", "(Lt (|> x f) (|> y g))"),
            ("x |> f || y", "(Or (|> x f) y)"),
            ("x |> f && y", "(And (|> x f) y)"),
            ("a && xs |> f == 4", "(And a (EqEq (|> xs f) 4))"),
            ("x |> f |> g", "(|> (|> x f) g)"),
            ("x |> f |> g |> h", "(|> (|> (|> x f) g) h)"),
            ("x |> f -> T", "(-> (|> x f) T)"),
            ("A -> x |> f", "(-> A (|> x f))"),
            ("x |> f <-> y", "((Std.Iff (|> x f)) y)"),
            ("(x |> f) = y", "(Eq (|> x f) y)"),
            ("x |> (f = y)", "(|> x (Eq f y))"),
            ("[a |> f, b]", "[(|> a f) b]"),
        ];
        for (text, want) in cases {
            assert_eq!(pipe_shape(text), want, "{text}");
        }
    }

    #[test]
    fn a_theorem_statement_compares_the_pipeline() {
        for (source, want) in [
            ("theorem t: xs |> .length = n := rfl\n", "(Eq xs.length n)"),
            (
                "theorem t: xs |> List.length = n := rfl\n",
                "(Eq (|> xs List.length) n)",
            ),
            (
                "theorem t:\n  xs\n    |> .map f\n    |> .length = n\n  := rfl\n",
                "(Eq (xs.map f).length n)",
            ),
        ] {
            let module = parse(source);
            let Decl::Signature { ty, .. } = &module.decls[0] else {
                panic!("expected a theorem: {source}");
            };
            assert_eq!(pshape(ty), want, "{source}");
        }
    }

    #[test]
    fn a_lambda_on_the_right_takes_the_rest_of_the_pipeline() {
        let cases = [
            ("x |> y => f y", "(|> x (\\y (f y)))"),
            ("x |> y => f y |> g", "(|> x (\\y (|> (f y) g)))"),
            ("x |> f |> y => y + 1", "(|> (|> x f) (\\y (Add y 1)))"),
            (
                "x |> List.map (y => y |> f)",
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
    fn a_section_at_the_start_of_an_expression_takes_the_whole_expression() {
        let cases = [
            ("(.id == id)", "(\\%section (EqEq %section.id id))"),
            ("(.a + 1 * 2)", "(\\%section (Add %section.a (Mul 1 2)))"),
            (
                "(.drop 1 == xs)",
                "(\\%section (EqEq (%section.drop 1) xs))",
            ),
            (
                "(.items |> List.sum)",
                "(\\%section (|> %section.items List.sum))",
            ),
            ("(.a <-> b)", "(\\%section ((Std.Iff %section.a) b))"),
            // A section alone, or as an argument, is as it was.
            ("(.id)", "(\\%section %section.id)"),
            ("f .a == b", "(EqEq (f (\\%section %section.a)) b)"),
            // Only the first section is the function's argument.
            (
                "(.a && .b)",
                "(\\%section (And %section.a (\\%section %section.b)))",
            ),
            // After `|>` the section is the call it stands for, and a
            // comparison after it compares the result.
            ("xs |> .sum == 6", "(EqEq xs.sum 6)"),
            ("a && xs |> .length == 4", "(And a (EqEq xs.length 4))"),
            ("xs |> .show ++ y", "(Append xs.show y)"),
        ];
        for (text, want) in cases {
            assert_eq!(section_shape(text), want, "{text}");
        }
        assert_eq!(
            section_shape("xs |> .drop 1 |> .sum"),
            section_shape("(xs.drop 1).sum")
        );
        let membership = section_shape("(.a !in xs)");
        assert!(
            membership.starts_with("(\\%section (Std.Bool.not (In("),
            "{membership}"
        );
    }

    #[test]
    fn an_operator_section_is_a_lambda_with_the_operand_missing() {
        let cases = [
            ("(== s)", "(\\%section (EqEq %section s))"),
            ("(!= s)", "(\\%section (Ne %section s))"),
            ("(> 3)", "(\\%section (Lt 3 %section))"),
            ("(<= 3)", "(\\%section (Le %section 3))"),
            ("(+ 1)", "(\\%section (Add %section 1))"),
            ("(* 2 )", "(\\%section (Mul %section 2))"),
            ("(++ ys)", "(\\%section (Append %section ys))"),
            ("(|| a && b)", "(\\%section (Or %section (And a b)))"),
            ("(&& a == b)", "(\\%section (And %section (EqEq a b)))"),
            ("(<-> q)", "(\\%section ((Std.Iff %section) q))"),
            ("(k +)", "(\\%section (Add k %section))"),
            ("(k ++)", "(\\%section (Append k %section))"),
            ("(n * 2 ==)", "(\\%section (EqEq (Mul n 2) %section))"),
            ("(a * b +)", "(\\%section (Add (Mul a b) %section))"),
            ("(p &&)", "(\\%section (And p %section))"),
        ];
        for (text, want) in cases {
            assert_eq!(section_shape(text), want, "{text}");
        }
        assert!(section_shape("(in xs)").starts_with("(\\%section (In("));
        assert!(section_shape("(!in xs)").starts_with("(\\%section (Std.Bool.not (In("));
        assert!(section_shape("(k in)").starts_with("(\\%section (In("));
    }

    #[test]
    fn a_bare_operator_is_a_function_of_two_arguments() {
        let cases = [
            ("(&&)", "(\\%left %right (And %left %right))"),
            ("(+)", "(\\%left %right (Add %left %right))"),
            ("(-)", "(\\%left %right (Sub %left %right))"),
            ("(==)", "(\\%left %right (EqEq %left %right))"),
            ("(>)", "(\\%left %right (Lt %right %left))"),
        ];
        for (text, want) in cases {
            assert_eq!(section_shape(text), want, "{text}");
        }
    }

    #[test]
    fn minus_is_not_an_operator_section() {
        assert!(matches!(expression("(- 1)").unwrap(), Expr::Neg(..)));
        assert!(matches!(expression("(-1)").unwrap(), Expr::Neg(..)));
        for bad in ["(k -)", "(+ 1 + 2)", "(a + b *)", "(k + 1 +)", "(== == 1)"] {
            assert!(expression(bad).is_err(), "{bad}");
        }
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
        // A comparison on the last line compares the pipeline's result.
        assert_eq!(
            pipe_body("  x\n    |> f\n    |> g == y"),
            "(EqEq (|> (|> x f) g) y)"
        );
        assert_eq!(
            pipe_body("  x\n    |> .map f\n    |> .sum = y"),
            "(Eq (x.map f).sum y)"
        );
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
                e.message
                    .contains("so it goes on its own: `import Aoc (..)`"),
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
        assert_eq!(e.code, "E-NAMESPACE-NOT-FIRST", "{e:?}");
        assert!(e.message.contains("must come first"), "{e:?}");
        assert!(
            e.notes[0].contains("move `namespace A` to the top"),
            "{e:?}"
        );
        let e = parse_error("def x: Nat := 1\nnamespace A\n");
        assert!(e.message.contains("must come first"), "{e:?}");
    }

    #[test]
    fn namespace_is_a_keyword() {
        assert!(parse_module_text("def namespace: Nat := 1\n").is_err());
    }

    #[test]
    fn calc_steps_are_lines_starting_with_an_underscore() {
        let text = "def f (a: Nat): a = a :=\n  calc a\n    _ = a := rfl\n    _ <= a\n    _ < a := Nat.f _\n";
        let expr = rhs(text);
        let Expr::Calc { steps, .. } = &expr else {
            panic!("expected a calc");
        };
        let shape: Vec<(BinOp, bool)> = steps.iter().map(|s| (s.rel, s.proof.is_some())).collect();
        assert_eq!(
            shape,
            vec![(BinOp::Eq, true), (BinOp::Le, false), (BinOp::Lt, true)]
        );
        // The `_` argument stays an argument when it isn't at the start of a line.
        assert!(matches!(&steps[2].proof, Some(Expr::App(..))));
    }

    #[test]
    fn omega_takes_an_optional_list_of_facts() {
        let expr = rhs("theorem t (a: Nat): a <= a := omega\n");
        assert!(
            matches!(&expr, Expr::Omega { facts, .. } if facts.is_empty()),
            "{expr:?}"
        );
        let expr = rhs("theorem t (a: Nat): a <= a := omega [h a, Nat.leRefl a]\n");
        let Expr::Omega { facts, .. } = &expr else {
            panic!("expected omega, got {expr:?}");
        };
        assert_eq!(facts.len(), 2);
        assert!(facts.iter().all(|f| matches!(f, Expr::App(..))));
        // As an argument, and as a calc step's proof.
        let expr = rhs("theorem t (a: Nat): a <= a := f omega x\n");
        assert!(matches!(&expr, Expr::App(..)));
        let expr = rhs("def f (a: Nat): a <= a :=\n  calc a\n    _ <= a := omega\n");
        let Expr::Calc { steps, .. } = &expr else {
            panic!("expected a calc");
        };
        assert!(matches!(&steps[0].proof, Some(Expr::Omega { .. })));
    }

    #[test]
    fn ring_takes_an_optional_list_of_hypotheses() {
        let expr = rhs("theorem t (a: Nat): a + 1 = 1 + a := ring\n");
        assert!(
            matches!(&expr, Expr::Ring { facts, .. } if facts.is_empty()),
            "{expr:?}"
        );
        let expr = rhs("theorem t (a: Nat): a = a := ring [h a, g]\n");
        let Expr::Ring { facts, .. } = &expr else {
            panic!("expected ring, got {expr:?}");
        };
        assert_eq!(facts.len(), 2);
        // As an argument, and as a calc step's proof.
        let expr = rhs("theorem t (a: Nat): a = a := f ring x\n");
        assert!(matches!(&expr, Expr::App(..)));
        let expr = rhs("def f (a: Nat): a = a :=\n  calc a\n    _ = a := ring\n");
        let Expr::Calc { steps, .. } = &expr else {
            panic!("expected a calc");
        };
        assert!(matches!(&steps[0].proof, Some(Expr::Ring { .. })));
    }

    #[test]
    fn membership_sits_with_the_comparisons() {
        // `x in xs && y !in ys`: no brackets needed.
        let Expr::Binary(BinOp::And, l, r) = &expr("x in xs && y !in ys") else {
            panic!("expected `&&`");
        };
        assert!(matches!(l.as_ref(), Expr::Binary(BinOp::In(_), ..)));
        // `!in` is `!(y in ys)`.
        let Expr::App(not, member) = r.as_ref() else {
            panic!("expected `!(…)`");
        };
        assert!(matches!(not.as_ref(), Expr::Var(n) if n.text == "Std.Bool.not"));
        assert!(matches!(member.as_ref(), Expr::Binary(BinOp::In(_), ..)));
        // Tighter than `++` loses: `x in xs ++ ys` is `x in (xs ++ ys)`.
        let Expr::Binary(BinOp::In(_), _, rhs) = &expr("x in xs ++ ys") else {
            panic!("expected `in`");
        };
        assert!(matches!(rhs.as_ref(), Expr::Binary(BinOp::Append, ..)));
        // Not associative.
        assert!(parse_module_text("def t: Bool := a in b in c\n").is_err());
        // `!x in xs` would be `(!x) in xs`: refused, with brackets allowed.
        let error = parse_errors("def t: Bool := !x in xs\n");
        assert!(error.contains("applies to the element"), "{error}");
        assert!(parse_errors("def t: Bool := ¬x ∈ xs\n").contains("applies to the element"));
        assert!(parse_module_text("def t: Bool := (!x) in xs\n").is_ok());
        assert!(parse_module_text("def t: Bool := !(x in xs)\n").is_ok());
    }

    #[test]
    fn iff_sits_between_arrow_and_or() {
        let iff = |e: &Expr| -> Option<(Expr, Expr)> {
            let Expr::App(f, q) = e else { return None };
            let Expr::App(head, p) = f.as_ref() else {
                return None;
            };
            matches!(head.as_ref(), Expr::Var(n) if n.text == "Std.Iff")
                .then(|| (p.as_ref().clone(), q.as_ref().clone()))
        };
        // `p && q <-> r` is `(p && q) <-> r`.
        let (p, _) = iff(&expr("p && q <-> r || s")).expect("an iff");
        assert!(matches!(p, Expr::Binary(BinOp::And, ..)));
        // `p -> q <-> r` is `p -> (q <-> r)`, and `p <-> q -> r` is
        // `(p <-> q) -> r`.
        let Expr::Arrow(_, rhs) = &expr("p -> q <-> r") else {
            panic!("expected an arrow");
        };
        assert!(iff(rhs).is_some());
        let Expr::Arrow(lhs, _) = &expr("p <-> q -> r") else {
            panic!("expected an arrow");
        };
        assert!(iff(lhs).is_some());
        // Not associative.
        assert!(parse_errors("def t: Prop := p <-> q <-> r\n").contains("doesn't chain"));
        assert!(parse_module_text("def t: Prop := (p <-> q) <-> r\n").is_ok());
    }

    #[test]
    fn exists_takes_a_lambda() {
        let exists = |e: &Expr| -> Option<Expr> {
            let Expr::App(f, lam) = e else { return None };
            let Expr::App(head, _) = f.as_ref() else {
                return None;
            };
            matches!(head.as_ref(), Expr::Var(n) if n.text == "Std.Exists")
                .then(|| lam.as_ref().clone())
        };
        let lam = exists(&expr("exists (n: Nat) => n * n = 49")).expect("an exists");
        assert!(matches!(lam, Expr::TypedLam(..)));
        // Several parameters nest, the body's own lambda doesn't.
        let lam = exists(&expr("exists a b => f (x => x)")).expect("an exists");
        let Expr::Lam(names, body, _) = &lam else {
            panic!("expected a lambda");
        };
        assert_eq!(names.len(), 1);
        let inner = exists(body).expect("a second exists");
        let Expr::Lam(_, body, _) = &inner else {
            panic!("expected a lambda");
        };
        assert!(matches!(body.as_ref(), Expr::App(..)));
        // After `&&`, `||`, `<->` and `->` it takes the rest.
        assert!(matches!(
            expr("p && exists k => q k"),
            Expr::Binary(BinOp::And, ..)
        ));
        assert!(parse_module_text("def t: Prop := p <-> exists k => q k\n").is_ok());
        assert!(parse_module_text("def t: Prop := p -> ∃ (k: Nat) => q k\n").is_ok());
        assert!(parse_errors("def t: Prop := exists 3\n").contains("after `exists`"));
        // After a `.` it's a name: `x.exists` and `Foo.exists` still parse.
        assert!(parse_module_text("def t: Bool := (Some 3).exists (v => v > 2)\n").is_ok());
        assert!(parse_module_text("def t: Bool := Foo.exists (v => v > 2) (Some 3)\n").is_ok());
    }

    #[test]
    fn membership_in_a_rewrite_needs_brackets() {
        let error = parse_errors("def f (a: Nat): a = a :=\n  rewrite h x in xs in t\n");
        assert!(error.contains("needs brackets"), "{error}");
        let error = parse_errors("def f (a: Nat): a = a :=\n  rewrite h in x in xs\n");
        assert!(error.contains("needs brackets"), "{error}");
        // In brackets, either side is fine.
        assert!(
            parse_module_text("def f (a: Nat): a = a :=\n  rewrite h (x in xs) in t\n").is_ok()
        );
        assert!(parse_module_text("def f (a: Nat): a = a :=\n  rewrite h in (x in xs)\n").is_ok());
        assert!(
            parse_module_text("def f (a: Nat): a = a :=\n  rewrite h in (x in xs) && b\n").is_ok()
        );
    }

    fn parse_errors(text: &str) -> String {
        match parse_module_text(text) {
            Ok(_) => panic!("expected an error for {text:?}"),
            Err(errors) => errors
                .iter()
                .map(|d| format!("{}: {:?}", d.message, d.notes))
                .collect::<Vec<_>>()
                .join("\n"),
        }
    }

    #[test]
    fn omega_is_a_keyword() {
        assert!(parse_module_text("def omega: Nat := 1\n").is_err());
    }

    #[test]
    fn rewrite_takes_rules_left_to_right_and_an_optional_body() {
        let text = "def f (a: Nat): a = a :=\n  rewrite p, <- q x, r (y in ys) in Nat.f _\n";
        let expr = rhs(text);
        let Expr::Rewrite { rules, body, .. } = &expr else {
            panic!("expected a rewrite");
        };
        let shape: Vec<bool> = rules.iter().map(|r| r.reverse).collect();
        assert_eq!(shape, vec![false, true, false]);
        assert!(matches!(&rules[1].proof, Expr::App(..)));
        // A bracketed membership is an ordinary argument; the bare `in`
        // ended the rule.
        let Expr::App(_, arg) = &rules[2].proof else {
            panic!("expected an application");
        };
        assert!(matches!(&**arg, Expr::Binary(BinOp::In(_), ..)));
        assert!(matches!(body.as_deref(), Some(Expr::App(..))));
        // No `in`: the body is `rfl`, left to the elaborator.
        let text = "def f (a: Nat): a = a :=\n  rewrite p x\n";
        let expr = rhs(text);
        let Expr::Rewrite { rules, body, .. } = &expr else {
            panic!("expected a rewrite");
        };
        assert_eq!(rules.len(), 1);
        assert!(body.is_none());
    }

    #[test]
    fn rewrite_in_can_start_its_own_line() {
        let body = |text: &str| {
            let expr = rhs(text);
            let Expr::Rewrite { rules, body, .. } = &expr else {
                panic!("expected a rewrite");
            };
            (rules.len(), body.clone())
        };
        for text in [
            "def f (a: Nat): a = a :=\n  rewrite p,\n    q x\n  in t\n",
            "def f (a: Nat): a = a :=\n  rewrite p, q x\n  in t\n",
            "def f (a: Nat): a = a :=\n  rewrite p, q x\n    in t\n",
            "def f (a: Nat): a = a :=\n  rewrite p at h\n  in t\n",
        ] {
            let (rules, body) = body(text);
            assert!(rules >= 1, "{text}");
            assert!(
                matches!(body.as_deref(), Some(Expr::Var(n)) if n.text == "t"),
                "{text}"
            );
        }
        // Left of the `rewrite`, an `in` isn't its.
        assert!(
            parse_module_text("def f (a: Nat): a = a :=\n  g\n    rewrite p\n  in t\n").is_err()
        );
    }

    #[test]
    fn rewrite_at_takes_a_target_before_the_body() {
        let parts = |text: &str| {
            let expr = rhs(text);
            let Expr::Rewrite {
                rules,
                target,
                body,
                ..
            } = &expr
            else {
                panic!("expected a rewrite");
            };
            (rules.clone(), target.clone(), body.clone())
        };
        // `at` ends the rules, `in` ends the target.
        let (rules, target, body) =
            parts("def f (a: Nat): a = a :=\n  rewrite p, <- q x at h y in t\n");
        assert_eq!(rules.len(), 2);
        assert!(matches!(&rules[1].proof, Expr::App(..)));
        assert!(matches!(target.as_deref(), Some(Expr::App(..))));
        assert!(matches!(body.as_deref(), Some(Expr::Var(n)) if n.text == "t"));
        // Without `in`, the rewritten target is the value.
        let (_, target, body) = parts("def f (a: Nat): a = a :=\n  rewrite p at h\n");
        assert!(matches!(target.as_deref(), Some(Expr::Var(n)) if n.text == "h"));
        assert!(body.is_none());
        // An `at` that starts a rule is a name, so is a bracketed one, and so
        // is a field `.at`.
        let (rules, target, body) =
            parts("def f (a: Nat): a = a :=\n  rewrite at b (at) r.at at at in at\n");
        let Expr::App(f, arg) = &rules[0].proof else {
            panic!("expected an application");
        };
        assert!(matches!(&**arg, Expr::Field(_, n) if n.text == "at"));
        assert!(matches!(&**f, Expr::App(_, a) if matches!(&**a, Expr::Var(n) if n.text == "at")));
        assert!(matches!(target.as_deref(), Some(Expr::Var(n)) if n.text == "at"));
        assert!(matches!(body.as_deref(), Some(Expr::Var(n)) if n.text == "at"));
        // `at` is an ordinary name elsewhere.
        assert!(parse_module_text("def f (at: Nat): Nat := at\n").is_ok());
        let (_, target, _) = parts("def f (a: Nat): a = a :=\n  rewrite p in at\n");
        assert!(target.is_none());
    }

    #[test]
    fn rewrite_and_in_are_keywords() {
        assert!(parse_module_text("def rewrite: Nat := 1\n").is_err());
        // `in` is reserved since it became membership (D1201).
        assert!(parse_module_text("def f (in: Nat): Nat := in\n").is_err());
        // `<` then `-` apart is a comparison, not an arrow.
        assert!(parse_module_text("def f (a: Nat): a = a :=\n  rewrite < - p in rfl\n").is_err());
    }

    #[test]
    fn calc_expressions_may_use_logic_operators() {
        let text = "def f (a: Bool) (b: Bool): a || b = b || a :=\n  calc a || b\n    _ = b || a := g a b\n    _ = b || a && a\n";
        let Expr::Calc { ref steps, .. } = rhs(text) else {
            panic!("expected a calc");
        };
        assert_eq!(steps.len(), 2);
    }

    #[test]
    fn calc_expressions_may_use_pipes() {
        // `|>` binds tighter than the step's relation: `_ = (xs |> List.sum)`.
        let text = "def f (xs: List Nat): xs.sum = xs.sum :=\n  calc xs |> List.sum\n    _ = xs |> List.sum := h\n    _ = xs |> .sum\n";
        let Expr::Calc {
            ref first,
            ref steps,
            ..
        } = rhs(text)
        else {
            panic!("expected a calc");
        };
        assert!(matches!(**first, Expr::Pipe(..)));
        assert_eq!(steps.len(), 2);
        assert!(matches!(steps[0].rhs, Expr::Pipe(..)));
        assert!(steps[0].proof.is_some());
        assert!(matches!(steps[1].rhs, Expr::Field(..)));
    }

    #[test]
    fn a_keyword_where_a_name_goes_is_called_a_keyword() {
        for text in [
            "def f (then: Nat): Nat := 0\n",
            "def f: Nat := (test => test) 0\n",
            "def f: Nat :=\n  let with := 0\n  0\n",
            "def f (n: Nat): Nat := match n with\n  | Succ return => 0\n  | Zero => 0\n",
        ] {
            let message = first_error(text);
            assert!(message.contains("found the keyword"), "{text}: {message}");
        }
        // `∈` is `in`, but isn't written as a word.
        let message = first_error("def f (∈: Nat): Nat := 0\n");
        assert!(!message.contains("keyword"), "{message}");
    }

    fn first_error(text: &str) -> String {
        match parse_module_text(text) {
            Ok(_) => panic!("{text}: parsed"),
            Err(errors) => errors[0].message.clone(),
        }
    }

    #[test]
    fn calc_needs_steps_on_their_own_lines() {
        assert!(parse_module_text("def f (a: Nat): a = a := calc a = a := rfl\n").is_err());
        assert!(parse_module_text("def f (a: Nat): a = a :=\n  calc a\n").is_err());
        assert!(
            parse_module_text("def f (a: Nat): a = a :=\n  calc a\n    _ = a\n   _ = a\n").is_err()
        );
    }

    #[test]
    fn recovery_keeps_good_declarations_and_names_the_broken() {
        let text = "def a: Nat := 1\n\ndef b (n: Nat): Nat := n +\n\n\
                    type T\n  | MkT (x: Nat\n\ndef c: Nat := (\n\ndef d: Nat := 2\n";
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        let (module, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
        assert_eq!(errors.len(), 3);
        let kept: Vec<&str> = module
            .decls
            .iter()
            .filter_map(|d| match d {
                Decl::Signature { name, .. } => Some(name.text.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(kept, ["a", "d"]);
        let failed: Vec<&str> = module.failed.iter().map(|n| n.text.as_str()).collect();
        assert_eq!(failed, ["b", "T", "MkT", "c"]);
    }

    fn parse_module_text(text: &str) -> std::result::Result<Module, Vec<Diagnostic>> {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_module(file, text)
    }

    /// The names and arguments of attributes, as written.
    fn attr_texts(attrs: &[crate::ast::Attribute]) -> Vec<String> {
        attrs
            .iter()
            .map(|a| match &a.arg {
                Some((arg, _)) => format!("{} {arg:?}", a.name.text),
                None => a.name.text.clone(),
            })
            .collect()
    }

    /// A data type's attributes as written: its own, each constructor's, and
    /// each field's.
    type DataAttrs = (Vec<String>, Vec<Vec<String>>, Vec<Vec<Vec<String>>>);

    fn data_attrs(decl: &Decl) -> DataAttrs {
        let Decl::Data { attrs, ctors, .. } = decl else {
            panic!("expected a data type: {decl:?}");
        };
        (
            attr_texts(attrs),
            ctors.iter().map(|c| attr_texts(&c.attrs)).collect(),
            ctors
                .iter()
                .map(|c| c.fields.iter().map(|b| attr_texts(&b.attrs)).collect())
                .collect(),
        )
    }

    #[test]
    fn attributes_on_types_constructors_and_fields() {
        let module = parse(
            "@[js.tag \"type\"] type Shape =\n  \
             | @[js.name \"DOT\"] Dot\n  \
             | @[js.name \"CIRCLE\", js.other] Circle (@[js.name \"center_x\"] x: Nat) [@[js.name \"n\"] n: Nat]\n\n\
             type R = { @[js.name \"type\"] kind: Text, size: Nat }\n",
        );
        let (on_type, on_ctors, on_fields) = data_attrs(&module.decls[0]);
        assert_eq!(on_type, ["js.tag \"type\""]);
        assert_eq!(
            on_ctors,
            [
                vec!["js.name \"DOT\""],
                vec!["js.name \"CIRCLE\"", "js.other"]
            ]
        );
        assert_eq!(
            on_fields,
            [
                vec![],
                vec![vec!["js.name \"center_x\""], vec!["js.name \"n\""]]
            ]
        );
        let (_, _, on_fields) = data_attrs(&module.decls[1]);
        assert_eq!(on_fields, [vec![vec!["js.name \"type\""], vec![]]]);
    }

    #[test]
    fn a_multi_line_attribute_group_may_close_at_column_0() {
        let module = parse(
            "@[\n  js.tag \"type\",\n  js.other \"x\",\n]\n-- a comment\n\n@[js.more]\ntype T =\n  | A\n\ndef f: Nat := 1\n",
        );
        assert_eq!(module.decls.len(), 3);
        let (on_type, _, _) = data_attrs(&module.decls[0]);
        assert_eq!(on_type, ["js.tag \"type\"", "js.other \"x\"", "js.more"]);
        let Decl::Signature { attrs, .. } = &module.decls[1] else {
            panic!()
        };
        assert!(attrs.is_empty());
    }

    #[test]
    fn attributes_before_a_definition_belong_to_its_signature() {
        let module = parse("@[js.name \"draw\"] export def render (n: Nat): Nat := n\n");
        let Decl::Signature { attrs, export, .. } = &module.decls[0] else {
            panic!()
        };
        assert!(*export);
        assert_eq!(attr_texts(attrs), ["js.name \"draw\""]);
    }

    #[test]
    fn misplaced_attributes_are_refused() {
        for (text, code) in [
            // Attributes always attach to the next declaration, never drift.
            ("@[js.tag \"x\"]\nnamespace N\n", "E-ATTRIBUTE"),
            ("@[js.tag \"x\"]\nimport List (map)\n", "E-ATTRIBUTE"),
            ("@[js.tag \"x\"]\ntest \"t\" := True\n", "E-ATTRIBUTE"),
            (
                "@[js.tag \"x\"]\nability A where\n  op: Nat -> Nat\n",
                "E-ATTRIBUTE",
            ),
            ("def f (@[js.name \"x\"] n: Nat): Nat := n\n", "E-ATTRIBUTE"),
            (
                "def f: (@[js.name \"x\"] n: Nat) -> Nat := n => n\n",
                "E-ATTRIBUTE",
            ),
            (
                "def f: Nat -> Nat := (@[js.name \"x\"] n) => n\n",
                "E-ATTRIBUTE",
            ),
            ("type T (@[js.name \"x\"] a: Type) = | A\n", "E-ATTRIBUTE"),
            (
                "def f (n: Nat): Nat :=\n  @[js.name \"x\"] def g (m: Nat): Nat := m\n  g n\n",
                "E-ATTRIBUTE",
            ),
            // The grammar: one name, then at most one plain string.
            ("@[js.name 123] type T = | A\n", "E-PARSE"),
            ("@[js.name \"x\" \"y\"] type T = | A\n", "E-PARSE"),
            ("@[] type T = | A\n", "E-PARSE"),
            ("@[js.name \"${1}\"] type T = | A\n", "E-PARSE"),
            ("@ type T = | A\n", "E-PARSE"),
            // Attributes with nothing after them.
            ("def f: Nat := 1\n\n@[js.tag \"x\"]\n", "E-PARSE"),
            (
                "def f: Nat := 1\n@[js.tag \"x\"]\n@[js.name \"y\"]\n",
                "E-PARSE",
            ),
        ] {
            let errors = parse_module_text(text).expect_err(text);
            assert_eq!(errors[0].code, code, "{text}: {:?}", errors[0].message);
        }
    }

    #[test]
    fn an_unclosed_attribute_group_stops_at_the_next_declaration() {
        let text = "@[js.tag \"x\"\ntype T = | A\n\ndef f: Nat := 1\n";
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        let (module, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
        assert_eq!(errors.len(), 1);
        // `T`, and `f`'s signature and equation.
        assert_eq!(module.decls.len(), 3, "{module:?}");
    }
}
