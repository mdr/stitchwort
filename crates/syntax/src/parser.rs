//! Recursive-descent parser for the surface syntax. See `docs/syntax.md`.
//!
//! It builds no trees: it records where each construct starts and ends
//! ([`Mark`]s), from which the lossless tree is built ([`crate::tree`]), and
//! the compiler's tree is lowered from that ([`crate::lower`]). It decides
//! only how the tokens group, from the tokens; checks on what has been
//! grouped, such as a parameter named twice, are the lowering's. (A few
//! still read the marks back to make a message or a choice, which breaks the
//! rule in [`crate::tree`]'s "Marks" until docs/proposals/parser-end-state.md's
//! T2 moves them to the lowering.)
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

use crate::ast::{Expr, MatchKind, Pattern};
use crate::lexer::{Tok, Token, Trivia};
use crate::lower::Lower;
use crate::negation::{
    argument_bang, argument_minus, argument_prefix, negative_numeral, opens_atom,
};
use crate::stack::StackLimit;
use crate::tree::{DeclMarks, Mark, NodeKind, Recovery, RecoveryPoint, SyntaxFile};
use crate::{Diagnostic, FileId, Span};

mod declarations;
mod entry;
mod failed_names;
mod sections;
use declarations::misplaced_attributes;

#[cfg(test)]
pub(crate) use entry::parse_with_tree;
pub use entry::{
    parse_expression, parse_expression_tree, parse_expression_within, parse_module,
    parse_module_and_tree, parse_module_recovering, parse_module_within, parse_namespace_line,
    parse_tree,
};
pub(crate) use failed_names::{failed_names_in, failed_names_of};

/// The parser's results box their error: with an unboxed `Diagnostic`,
/// every `Result<()>` would be as large as a `Diagnostic`, and each level
/// of a nested expression (`((…(0)…))`) holds several on the stack. When
/// b0f1a3ea (SW-914) grew `Diagnostic` from 96 to 112 bytes, each level took
/// about 350 bytes more and the bench's check-nested-parens (12,000
/// brackets) stopped parsing. An error happens
/// once per declaration at most, so the box costs nothing that matters.
type Result<T> = std::result::Result<T, Box<Diagnostic>>;

/// What the public functions return: the error unboxed.
type Parsed<T> = std::result::Result<T, Diagnostic>;

/// Bytes of stack the parser may use when the caller doesn't say: safe on a
/// 2 MiB thread (Rust's default for spawned threads and tests), like the
/// core's default `Limits`.
pub const DEFAULT_STACK: usize = 1536 * 1024;

/// The largest `n` in `Type n`: the kernel's top universe
/// (`stitchwort_core::MAX_LEVEL`, docs/core.md "Universes"; a core test
/// checks they agree). Far below `u32::MAX`, so no arithmetic on levels can
/// wrap (SW-902).
pub const MAX_UNIVERSE_LEVEL: u32 = 65535;

/// `E-RESOURCE`, from the parser or the lowering running out of stack at
/// `at`.
pub(super) fn nested_too_deeply(at: Span) -> Diagnostic {
    Diagnostic::error(
        "E-RESOURCE",
        "ran out of resources: the program is nested too deeply to parse",
    )
    .with_label(at, "nested too deeply here")
    .with_note("this isn't a syntax error: there's a limit on how deeply expressions nest")
}

/// The name a name token holds, or "" for any other token.
fn name_text(token: &Token) -> &str {
    match &token.tok {
        Tok::Lower(text) | Tok::Upper(text) => text,
        _ => "",
    }
}

/// That the name `token` isn't qualified: a binder, a field or a
/// constructor being declared has a short name.
fn unqualified(token: &Token) -> Result<()> {
    let text = name_text(token);
    if text.contains('.') {
        return Err(error(
            token.span,
            format!("`{text}` is a qualified name, which can't be used here"),
        )
        .with_note("only declarations and references can be qualified; write a short name")
        .into());
    }
    Ok(())
}

/// What a lowering in the parser gave ([`Parser::lowered`]).
enum Lowered {
    Expr(Expr),
    Pattern(Pattern),
}

/// A line of a block, as far as the block needs to know: the last line
/// must be an expression.
enum Line {
    Expr,
    /// A `let`, at this keyword.
    Let(Span),
    /// A local definition, at its keyword.
    Def(Span),
}

/// The first attribute of a group, for messages about where attributes
/// can't go ([`declarations::misplaced_attributes`]).
pub(super) struct FirstAttribute {
    pub(super) name: String,
    pub(super) span: Span,
}

/// What the callers of the binder parsers check: the binder's first
/// attribute, whether it is `auto` and has no name, where its first name
/// is (past `auto`), and the tokens of its type and default value.
struct BinderRead {
    attribute: Option<FirstAttribute>,
    auto: bool,
    nameless: bool,
    first_name: Span,
    ty: (u32, u32),
    default: Option<(u32, u32)>,
}

/// The token range of each top-level declaration, in order: the column-0 split
/// the parser uses (attributes belong to the declaration after them). Together
/// the ranges cover `tokens`, except that tokens before the first range (a file
/// whose first column-0 token is `:=`, which starts no declaration) are in
/// none. Fails if the first token isn't at column 0.
pub fn decl_ranges(tokens: &[Token]) -> Parsed<Vec<std::ops::Range<usize>>> {
    let groups = split_decls(tokens).map_err(|d| *d)?;
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
        )
        .into());
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

/// The parser's modes: the state that says how the tokens ahead are read
/// (which ones end the current construct), as opposed to where the parser
/// is. Each construct that sets one saves the old value and puts it back
/// when it finishes. A recovery point snapshots them all ([`Snapshot`]),
/// since a construct that fails doesn't put back what it set
/// (docs/proposals/syntax-error-recovery.md §2.5).
#[derive(Clone, Copy, Debug, Default)]
struct Modes {
    /// Whether the item being parsed is in a list literal's brackets, for the
    /// bare-`..` error's note.
    in_list: bool,
    /// Inside a block: its column. A token starting a line at or left of it
    /// ends the current statement, so `peek` doesn't see it.
    limit: Option<u32>,
    /// The token starting the current statement, which `limit` doesn't stop.
    allow: Option<usize>,
    /// How many `calc`s the parser is inside. In one, a line starting with
    /// `_` is the next step, not an argument of the line before.
    calc_depth: u32,
    /// While a `rewrite` rule or target is being parsed: the token it starts
    /// at. A `then` outside brackets ends it, and so does an `in`, so that
    /// the old spelling `rewrite h in t` gets an error naming `then`.
    rewrite_rule: Option<usize>,
    /// While an arm's guard is being parsed: the token it starts at. A `=>`
    /// outside brackets ends it, so `| x if flag => e` is not a lambda.
    guard_start: Option<usize>,
    /// Whether an `at` outside brackets, after the first token, ends the
    /// `rewrite` rule too: true for a rule, false for the target after `at`.
    rewrite_at: bool,
    /// While a `let`'s value is being parsed: the token the `let` starts
    /// at. A `;` outside brackets opened since ends the value (the
    /// expression `let`'s body follows it), so it doesn't start a sequence
    /// `a; b` (SW-888). A block resets it.
    let_value: Option<usize>,
    /// Whether the parser is in a top-level definition's body, where it
    /// recovers from syntax errors (docs/proposals/syntax-error-recovery.md
    /// §2.2): elsewhere, as in a header or a data type, an error still
    /// fails the declaration whole.
    recover: bool,
    /// The token of a method section that starts an expression, `.f x + 1`,
    /// which the expression's parser marks as the `Section` once it has
    /// read the whole expression it takes (D1192), so the application at
    /// the section's head doesn't. Only the application starting at this
    /// token reads it, before reading anything, so it is never put back: a
    /// value left from an expression already read names a token behind the
    /// parser.
    section_head: Option<usize>,
}

/// What a recovery point restores before it carries on past an error
/// ([`Parser::recover_to`]): the modes. The position isn't in it, since
/// recovery only moves forward; marks recorded since stay, as finished
/// constructs inside the skipped tokens, and nest in the `Error` node the
/// recovery point marks from where the construct that failed started.
#[derive(Clone, Copy, Debug)]
struct Snapshot {
    modes: Modes,
}

struct Parser<'t> {
    tokens: &'t [Token],
    pos: usize,
    file: FileId,
    eof: u32,
    modes: Modes,
    /// For each opening bracket (`(`, `[`, `{`), the index of its partner,
    /// and `NO_PARTNER` for every other token and for unmatched brackets.
    /// Built once per declaration, so that skipping a bracketed group is one
    /// lookup (the lambda scan and `is_pi_binder`).
    matching: Vec<u32>,
    /// How deep the recursion may go.
    stack: StackLimit,
    /// Set by recovery before a top-level `def` or `theorem`, which takes
    /// it: that definition sets `header_kept` once its header has parsed
    /// and its body starts.
    keep_header: bool,
    /// Whether the top-level definition being parsed has a whole header
    /// and a body after it, if `keep_header` asked: then if the body
    /// doesn't parse, the declaration keeps its signature
    /// (docs/proposals/tests-with-errors.md §3.3).
    header_kept: bool,
    /// The constructs finished so far, in the order they finished, for the
    /// lossless tree (`crate::tree`, "Marks").
    marks: Vec<Mark>,
    /// The syntax errors recovered from so far, in the order met. The entry
    /// points that give one error fail on any, as they do on an error that
    /// unwinds ([`Parser::strict`]).
    errors: Vec<Diagnostic>,
    /// Where each error in [`Self::errors`] was recovered from, and how: a
    /// declaration with any is failed ([`crate::tree::Node::recoveries`]).
    recovered: Vec<Recovery>,
    /// The token position of the last R1 gap ([`Self::ran_out`]): a
    /// bracket whose contents ran out there and has read nothing since was
    /// left open ([`Self::close_bracket`]).
    ran_out_at: Option<usize>,
}

const NO_PARTNER: u32 = u32::MAX;

/// Whether the `{` at `tokens[open]`, where a result type starts (after a
/// declaration's `:` or an arrow), is a record literal or update rather
/// than an ability row (SW-1015): a theorem's statement may start with one,
/// `{ p | x = 3 }.x = 3`. A row is always followed by its type, and holds
/// only abilities and a row variable, never an `=` outside brackets. So the
/// braces are a record when they hold such an `=` (`{ id = 2 }`,
/// `{ p | x = 3 }`), or when they don't start with an ability's name and
/// what follows them can't start a type (`{ p | x }.x`, `{} = r`). A row
/// missing its type (`{IO} :=`) is still read as a row, and reported as one,
/// and so is a record type (`{ name: Nat }`), which `row` explains can't be
/// written there. The parser and the formatter (which spaces a row's braces
/// tightly) both ask this.
pub fn record_braces(tokens: &[Token], open: usize) -> bool {
    let first = tokens.get(open + 1).map(|t| &t.tok);
    if matches!(first, Some(Tok::Lower(_)))
        && tokens.get(open + 2).map(|t| &t.tok) == Some(&Tok::Colon)
    {
        return false;
    }
    let mut depth = 0usize;
    let mut close = None;
    for (i, token) in tokens.iter().enumerate().skip(open + 1) {
        match token.tok {
            Tok::Equals if depth == 0 => return true,
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace if depth > 0 => depth -= 1,
            Tok::RBrace => {
                close = Some(i);
                break;
            }
            _ => {}
        }
    }
    let Some(close) = close else {
        return false;
    };
    if matches!(first, Some(Tok::Upper(_))) {
        return false;
    }
    tokens
        .get(close + 1)
        .is_some_and(|t| !(opens_atom(&t.tok) || matches!(t.tok, Tok::TypeU | Tok::Prop)))
}

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

impl<'t> Parser<'t> {
    fn new(tokens: &'t [Token], file: FileId, text_len: usize, stack: StackLimit) -> Self {
        let eof = tokens.last().map_or(text_len as u32, |t| t.span.end);
        Parser {
            tokens,
            pos: 0,
            file,
            eof,
            modes: Modes::default(),
            matching: match_brackets(tokens),
            stack,
            keep_header: false,
            header_kept: false,
            marks: Vec::new(),
            errors: Vec::new(),
            recovered: Vec::new(),
            ran_out_at: None,
        }
    }

    /// Where a construct starting at the next token starts, for
    /// [`Self::node`].
    #[inline(always)]
    fn mark(&self) -> u32 {
        self.pos as u32
    }

    /// Records the construct of kind `kind` from token `start` (a
    /// [`Self::mark`] its parsing function kept) to the last token read.
    /// The one way a construct is marked: when it has finished, so the
    /// marks are in finishing order, which is what the tree's builder
    /// checks (`crate::tree`, "Marks").
    #[inline(always)]
    fn node(&mut self, start: u32, kind: NodeKind) {
        self.record(start, kind);
    }

    #[inline(never)]
    fn record(&mut self, start: u32, kind: NodeKind) {
        let end = self.pos as u32;
        self.marks.push(Mark { kind, start, end });
    }

    /// The compiler's tree for the expression (or with `pattern`, the
    /// pattern) in tokens `start..end`, lowered from the marks finished so
    /// far, if they hold one: for messages and the rare decisions that need
    /// what the lowering derives, such as a span (`f (x)` spans `f x`, not
    /// its bracket). Slow, since it builds a tree: only on paths that end in
    /// an error, or for rare constructs.
    #[cold]
    #[inline(never)]
    fn lowered(&self, (start, end): (u32, u32), pattern: bool) -> Option<Lowered> {
        let marks = self
            .marks
            .iter()
            .filter(|m| start <= m.start && m.end <= end && m.start < m.end)
            .map(|m| Mark {
                kind: m.kind,
                start: m.start - start,
                end: m.end - start,
            })
            .collect();
        let tokens: Vec<Token> = self.tokens[start as usize..end as usize].to_vec();
        let trivia = vec![Trivia::default(); tokens.len()];
        let root = DeclMarks {
            tokens: 0..tokens.len() as u32,
            root: NodeKind::Expression,
            marks,
            raw: None,
            signature_kept: false,
            recovered: Vec::new(),
        };
        let tree = SyntaxFile::build(tokens, trivia, Trivia::default(), Vec::new(), vec![root]);
        let lower = Lower::new(&tree, "", self.file, &[]);
        let root = tree.decls().next()?;
        let mut elements = root.children();
        let (Some(only), None) = (elements.next(), elements.next()) else {
            return None;
        };
        if pattern {
            lower.pattern(only).ok().map(Lowered::Pattern)
        } else {
            lower.expr(only).ok().map(Lowered::Expr)
        }
    }

    /// The span the compiler's tree gives the expression in tokens `range`
    /// ([`Self::lowered`]), or the tokens' own if it can't be lowered.
    #[cold]
    #[inline(never)]
    fn lowered_span(&self, range: (u32, u32)) -> Span {
        match self.lowered(range, false) {
            Some(Lowered::Expr(expr)) => expr.span(),
            _ => self.tokens_span(range),
        }
    }

    /// [`Self::lowered_span`] for a pattern.
    #[cold]
    #[inline(never)]
    fn lowered_pattern_span(&self, range: (u32, u32)) -> Span {
        match self.lowered(range, true) {
            Some(Lowered::Pattern(pattern)) => pattern.span(),
            _ => self.tokens_span(range),
        }
    }

    /// From the first token of `start..end` to its last. An empty range
    /// is a part R1 found missing ([`Self::ran_out`]), possibly at the end
    /// of the input: the point where the text ran out, after the token
    /// before it.
    fn tokens_span(&self, (start, end): (u32, u32)) -> Span {
        if end <= start {
            return match (start as usize).checked_sub(1) {
                Some(last) => Span::point(self.file, self.tokens[last].span.end),
                None => self
                    .tokens
                    .first()
                    .map_or(Span::point(self.file, self.eof), |t| {
                        Span::point(self.file, t.span.start)
                    }),
            };
        }
        let first = self.tokens[start as usize].span;
        first.to(self.tokens[end as usize - 1].span)
    }

    /// Whether a pattern read since token `from` holds the absurd pattern
    /// `()`, not under a named implicit field (`[n := p]`): such an arm or
    /// equation needs no right-hand side.
    fn absurd_since(&self, from: u32) -> bool {
        self.absurd_in(from, self.pos as u32)
    }

    /// [`Self::absurd_since`] for the tokens `from..to`. Marks finish inner
    /// first, so a named field's mark comes after those inside it.
    #[inline(never)]
    fn absurd_in(&self, from: u32, to: u32) -> bool {
        let mut named: Vec<(u32, u32)> = Vec::new();
        for mark in self.marks.iter().rev() {
            if mark.start < from {
                break;
            }
            if mark.end > to {
                continue;
            }
            match mark.kind {
                NodeKind::PatternNamed => named.push((mark.start, mark.end)),
                NodeKind::PatternAbsurd
                    if !named
                        .iter()
                        .any(|&(start, end)| start <= mark.start && mark.end <= end) =>
                {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    /// `=>` after a lambda's parameters or an alternative's patterns, with a
    /// hint if it's the old syntax's `->`.
    fn expect_fat_arrow(&mut self, what: &str) -> Result<&'t Token> {
        if self.peek() == Some(&Tok::Arrow) {
            return Err(self
                .unexpected(what)
                .with_note("lambdas and arms use `=>`: `x => e`, `| p => e`")
                .into());
        }
        self.expect(Tok::FatArrow, what)
    }

    /// Called by each function the parser recurses through (`expr`,
    /// `append_expr` and `pattern`), before going deeper.
    fn deeper(&self) -> Result<()> {
        if self.stack.exceeded() {
            return Err(nested_too_deeply(self.here()).into());
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
        if self.ends_construct(i) {
            return true;
        }
        let Some(limit) = self.modes.limit else {
            return false;
        };
        self.modes.allow != Some(i)
            && self
                .tokens
                .get(i)
                .is_some_and(|t| t.line_start && t.column <= limit)
            && !self.continues_bracket(i)
            && !self.continues_with_operator(i, limit)
    }

    /// Whether the token at `i` belongs to an enclosing construct, whatever
    /// its column: the next `calc` step, the `then` or `at` ending a `rewrite`
    /// rule, a guard's `=>`. No block starts there.
    fn ends_construct(&self, i: usize) -> bool {
        if self.modes.calc_depth > 0 && self.starts_calc_step(i) {
            return true;
        }
        if let Some(start) = self.modes.rewrite_rule
            && self.ends_rewrite_rule(i, start)
        {
            return true;
        }
        self.ends_guard(i)
    }

    /// Whether the token at `i` is the `=>` that ends the guard being parsed:
    /// its condition runs up to the next `=>` outside brackets, or after a
    /// bracket with no partner.
    fn ends_guard(&self, i: usize) -> bool {
        self.modes.guard_start.is_some_and(|start| {
            self.tokens.get(i).is_some_and(|t| t.tok == Tok::FatArrow)
                && (self.bracket_depth(start, i) <= 0 || self.left_open_between(start, i))
        })
    }

    /// Whether a bracket opened in `start..i` has no partner anywhere in the
    /// declaration: someone left it open, so a guard's `=>` after it still
    /// ends the guard rather than being read inside the bracket.
    fn left_open_between(&self, start: usize, i: usize) -> bool {
        (start..i).any(|k| {
            matches!(
                self.tokens[k].tok,
                Tok::LParen | Tok::LBracket | Tok::LBrace
            ) && self.matching[k] == NO_PARTNER
        })
    }

    /// Whether the token at `i`, starting a line at the block's own column
    /// `limit`, is an infix operator that continues the statement above, as
    /// if that line ended with it. Only operators that can't begin an
    /// expression qualify: `-` and `!` (negation), `|` (an arm), `in` (which
    /// ends a `let` or a `rewrite` target) and `=>` are left out.
    fn continues_with_operator(&self, i: usize, limit: u32) -> bool {
        self.tokens
            .get(i)
            .is_some_and(|t| t.column == limit && self.is_infix_only(&t.tok))
    }

    /// Whether the token at `i` is the `then` or `in` (or, in a rule, the
    /// `at`) that ends the `rewrite` rule or target starting at token `start`: one not
    /// inside brackets opened since, nor a field (`p.at`). An `at` that starts
    /// the rule is a name (`rewrite at b h then t`).
    #[inline(never)]
    fn ends_rewrite_rule(&self, i: usize, start: usize) -> bool {
        let word = match self.tokens.get(i).map(|t| &t.tok) {
            Some(Tok::KwThen | Tok::KwIn) => true,
            Some(Tok::Lower(w)) => w == "at" && self.modes.rewrite_at && i > start,
            _ => false,
        };
        if !word || (i > 0 && self.tokens[i - 1].tok == Tok::Dot) {
            return false;
        }
        self.bracket_depth(start, i) <= 0
    }

    /// How many brackets opened in the tokens `start..i` are still open.
    fn bracket_depth(&self, start: usize, i: usize) -> i64 {
        self.tokens[start..i].iter().fold(0i64, |d, t| match t.tok {
            Tok::LBracket | Tok::LParen | Tok::LBrace => d + 1,
            Tok::RBracket | Tok::RParen | Tok::RBrace => d - 1,
            _ => d,
        })
    }

    /// `if c` or `if h: P` after an arm's patterns, if there is one
    /// (docs/proposals/pattern-guards.md §2). The condition runs up to a
    /// `=>` outside brackets, or to the end of the arm.
    #[inline(never)]
    pub(super) fn guard(&mut self) -> Result<()> {
        if self.peek() != Some(&Tok::KwIf) {
            return Ok(());
        }
        let mark = self.mark();
        self.bump();
        if matches!(self.peek(), Some(Tok::Lower(_))) && self.peek_at(1) == Some(&Tok::Colon) {
            self.lower("a name")?;
            self.bump();
        }
        let saved = self.modes.guard_start.replace(self.pos);
        let cond = self.expr();
        self.modes.guard_start = saved;
        cond?;
        self.node(mark, NodeKind::Guard);
        Ok(())
    }

    /// The right side of an arm or equation whose patterns (`absurd` if one
    /// holds the absurd pattern) and condition, if any, were just read:
    /// `=> body`, or nothing when a pattern is the absurd `()` and no `=>`
    /// follows
    /// (`| Rock, ()`). Equations and `match` alternatives share it, so the
    /// two forms mean the same. `what` names the `=>` in the error when it
    /// is missing. (An arm with no body and a condition is the lowering's
    /// error.)
    pub(super) fn arm_body(&mut self, absurd: bool, what: &str) -> Result<()> {
        if self.peek() != Some(&Tok::FatArrow) && absurd {
            return Ok(());
        }
        self.expect_fat_arrow(what)?;
        self.expr()
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
            Err(self.unexpected(what).into())
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

    /// `token` as the source wrote it: the Unicode spelling of an operator
    /// (`∧`) shares its token with the ASCII one (`&&`), and the span's
    /// length tells them apart.
    fn spelled(&self, token: &Token) -> String {
        let unicode = match token.tok {
            Tok::AndAnd => "∧",
            Tok::OrOr => "∨",
            Tok::Arrow => "→",
            Tok::Iff => "↔",
            Tok::NotEq => "≠",
            Tok::Le => "≤",
            Tok::Ge => "≥",
            Tok::Bang => "¬",
            Tok::KwIn => "∈",
            Tok::NotIn => "∉",
            Tok::KwExists => "∃",
            Tok::KwForall => "∀",
            _ => return describe(&token.tok),
        };
        let ascii = describe(&token.tok);
        if (token.span.end - token.span.start) as usize == ascii.len() - 2 {
            ascii
        } else {
            format!("`{unicode}`")
        }
    }

    /// Whether `tok` is an infix operator that no expression starts with.
    fn is_infix_only(&self, tok: &Tok) -> bool {
        matches!(
            tok,
            Tok::AndAnd
                | Tok::OrOr
                | Tok::Iff
                | Tok::Arrow
                | Tok::Equals
                | Tok::EqEq
                | Tok::NotEq
                | Tok::Lt
                | Tok::Le
                | Tok::Gt
                | Tok::Ge
                | Tok::Plus
                | Tok::PlusPlus
                | Tok::Star
                | Tok::Slash
                | Tok::Percent
                | Tok::NotIn
        )
    }

    fn unexpected(&self, expected: &str) -> Diagnostic {
        if !self.is_stop(self.pos) && self.tokens.get(self.pos).map(|t| &t.tok) == Some(&Tok::At) {
            return Diagnostic::error("E-ATTRIBUTE", "attributes can't be written here")
                .with_label(self.here(), format!("expected {expected}"))
                .with_generic_note(declarations::ATTRIBUTE_PLACES);
        }
        let found = match self.tokens.get(self.pos) {
            Some(_) if self.modes.calc_depth > 0 && self.starts_calc_step(self.pos) => {
                return error(
                    self.here(),
                    format!("expected {expected}, but the next `calc` step starts here"),
                )
                .with_note(
                    "inside a `calc`, a line starting with `_` is the next step, even inside \
                     brackets: is a bracket on the step above left open?",
                );
            }
            Some(_) if self.ends_guard(self.pos) => {
                let diagnostic = error(
                    self.here(),
                    format!("expected {expected}, but the guard's `=>` starts here"),
                );
                let left_open = self
                    .modes
                    .guard_start
                    .is_some_and(|start| self.left_open_between(start, self.pos));
                return if left_open {
                    diagnostic.with_note(
                        "a guard's condition runs up to its arm's `=>`, even inside brackets: was \
                         a bracket in the guard left open?",
                    )
                } else {
                    diagnostic.with_note(
                        "the guard's condition is incomplete: it needs a complete expression \
                         before the arm's `=>`",
                    )
                };
            }
            Some(token) if self.is_stop(self.pos) && !self.ends_construct(self.pos) => {
                let diagnostic = error(
                    self.here(),
                    format!(
                        "expected {expected}, but the line starting with {} (in column {}) is at or \
                         left of the enclosing block's column ({}), so it starts a new statement",
                        self.spelled(token),
                        token.column + 1,
                        self.modes.limit.map_or(0, |l| l + 1)
                    ),
                );
                return if self.is_infix_only(&token.tok) {
                    diagnostic.with_note(
                        "to continue the expression on the line above, indent this line \
                         further than the block's column",
                    )
                } else if token.tok == Tok::Pipe {
                    diagnostic.with_note(
                        "the alternatives of a `match` that ends a block (after `let` or \
                         another statement) go further right than the block's column: \
                         indent them",
                    )
                } else {
                    diagnostic
                };
            }
            Some(token) => format!("found {}", self.spelled(token)),
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
        // `x :: xs` lexes as two colons; there's no infix cons (D2323).
        if let (Some(a), Some(b)) = (self.tokens.get(self.pos), self.tokens.get(self.pos + 1))
            && a.tok == Tok::Colon
            && b.tok == Tok::Colon
            && a.span.end == b.span.start
        {
            return diagnostic.with_note(
                "there is no `::` for a list: write `[x, ..xs]` to put `x` in front of `xs`, \
                 in an expression and in a pattern alike",
            );
        }
        if found_arrow {
            return diagnostic.with_note(
                "to pass a lambda as an argument, put it in brackets: `List.map xs (x => …)`",
            );
        }
        if self
            .tokens
            .get(self.pos)
            .is_some_and(|t| t.tok == Tok::KwIf)
        {
            return diagnostic.with_note(
                "an `if` inside an expression goes in brackets: `a + (if c then x else y)`; \
                 only after `=` or another comparison can it be written without them",
            );
        }
        diagnostic
    }

    /// The rest of `(a, b, c)` after its first component, which starts at
    /// `span`. Its own function, so the stack frame of the parser's
    /// recursive functions stays small (the nesting limit is measured in
    /// stack).
    #[inline(never)]
    fn tuple_expr(&mut self, start: u32) -> Result<()> {
        let mut items = 1;
        while self.eat(&Tok::Comma) {
            if self.peek() == Some(&Tok::RParen) && items >= 2 {
                break;
            }
            self.expr()?;
            items += 1;
        }
        if self.peek() == Some(&Tok::Colon) {
            return Err(self.tuple_annotation().into());
        }
        self.close_bracket(start, Tok::RParen, "`)`", NodeKind::Tuple)
    }

    /// The same for patterns.
    #[inline(never)]
    fn tuple_pattern(&mut self, start: u32) -> Result<()> {
        let mut items = 1;
        while self.eat(&Tok::Comma) {
            if self.peek() == Some(&Tok::RParen) && items >= 2 {
                break;
            }
            self.tuple_item()?;
            items += 1;
        }
        self.expect(Tok::RParen, "`)`")?;
        self.node(start, NodeKind::PatternTuple);
        Ok(())
    }

    /// A component of a tuple pattern, or several, `p | q`.
    fn tuple_item(&mut self) -> Result<()> {
        let start = self.mark();
        self.tuple_component()?;
        self.alternatives(start, Self::tuple_component)
    }

    /// An element of a list pattern, or several, `p | q`.
    fn list_item(&mut self) -> Result<()> {
        let start = self.mark();
        self.list_component()?;
        self.alternatives(start, Self::list_component)
    }

    /// A component of a list pattern: a constructor's arguments run to the
    /// next `,` or `]`; `-k` is allowed, as in a tuple.
    fn list_component(&mut self) -> Result<()> {
        let start = self.mark();
        if self.ctor_ahead() {
            self.ctor_name()?;
            self.ctor_args(start, |t| {
                matches!(
                    t,
                    Some(Tok::Comma | Tok::RBracket | Tok::Pipe | Tok::PlusPlus) | None
                )
            })?;
            return self.pattern_append(start, Self::list_component);
        }
        self.tuple_component()
    }

    /// A component of a tuple pattern: a pattern, or `-k`, which the
    /// tuple's brackets already delimit (`(-1, 0)`, `(0, -1)`).
    fn tuple_component(&mut self) -> Result<()> {
        let start = self.mark();
        if self.ctor_ahead() {
            // A constructor's arguments run to the next `,` or `)`:
            // `(Some x, Some y)`.
            self.ctor_name()?;
            self.ctor_args(start, |t| {
                matches!(
                    t,
                    Some(Tok::Comma | Tok::RParen | Tok::Pipe | Tok::PlusPlus) | None
                )
            })?;
            return self.pattern_append(start, Self::tuple_component);
        }
        if self.peek() != Some(&Tok::Minus) {
            self.pattern()?;
            return self.pattern_append(start, Self::tuple_component);
        }
        self.bump();
        let Some(Tok::Num(_)) = self.peek() else {
            return Err(self.unexpected("a number").into());
        };
        self.bump();
        self.node(start, NodeKind::PatternNegative);
        Ok(())
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
            let error = self.unexpected("the end of the declaration");
            // Haskell's `deriving` and Lean's `deriving instance` have no
            // Stitchwort spelling: the instances are made with the type.
            if self.text_at(self.pos as u32) == "deriving" {
                return Err(error
                    .with_note(
                        "there's no `deriving`: a declared type gets `==`, `<` and `${…}` derived \
                         when its fields have them (and `Finite` when they're all finite), \
                         so delete this line",
                    )
                    .into());
            }
            Err(error.into())
        } else {
            Ok(())
        }
    }

    /// What [`Self::recover_to`] goes back to, taken before a recovery point
    /// tries the construct it may recover from.
    fn snapshot(&self) -> Snapshot {
        Snapshot { modes: self.modes }
    }

    /// Undoes what a construct that failed left behind, before the parser
    /// carries on past it: the modes it set and didn't put back. The
    /// position stays where the error left it, for the recovery point to
    /// move on from.
    fn recover_to(&mut self, snapshot: Snapshot) {
        self.modes = snapshot.modes;
    }

    /// Records a syntax error the parser carries on from.
    fn report(&mut self, point: RecoveryPoint, error: Diagnostic) {
        let at = error.primary_span().unwrap_or(Span::NOWHERE);
        self.recovered.push(Recovery { point, at });
        self.errors.push(error);
    }

    /// R1 (docs/proposals/syntax-error-recovery.md §2.2): `expected` was
    /// wanted where the line or the declaration ended. Reported, and
    /// nothing is read: the construct being parsed lacks that part, which
    /// the lowering reads as a missing expression.
    #[cold]
    #[inline(never)]
    fn ran_out(&mut self, expected: &str) -> Result<()> {
        let error = match self.pos.checked_sub(1).map(|last| self.tokens[last].span) {
            Some(last) => self.ran_out_after(Span::point(self.file, last.end), expected),
            None => self.unexpected(expected),
        };
        self.report(RecoveryPoint::RanOut, error);
        self.ran_out_at = Some(self.pos);
        Ok(())
    }

    /// Ends the bracketed construct of kind `kind` that started at token
    /// `start`, whose closer `tok` is next. A closer that isn't there
    /// because the contents ran out at an R1 gap (nothing read since) is no
    /// second error: the gap is the one error, and the unclosed bracket is
    /// an `Error` node, not a `kind` node, so that a declaration holding it
    /// is failed and nothing is checked against a bracket that was never
    /// closed (SW-3289).
    fn close_bracket(&mut self, start: u32, tok: Tok, what: &str, kind: NodeKind) -> Result<()> {
        if self.peek() != Some(&tok) && self.bracket_ran_out() {
            self.node(start, NodeKind::Error);
            return Ok(());
        }
        self.expect(tok, what)?;
        self.node(start, kind);
        Ok(())
    }

    /// Whether the bracket being parsed was left open by an R1 gap at the
    /// current position, with nothing read since: the one error is the gap,
    /// so the bracket needs no second error for a closer that isn't there.
    fn bracket_ran_out(&self) -> bool {
        self.modes.recover && self.ran_out_at == Some(self.pos)
    }

    /// The error of R1 at `at`, the end of the last token read, which is
    /// where the text ran out (usually where the cursor is). A line at the
    /// block's column that ended it gets a second label, and a note says
    /// why; another stop (a `calc` step, a guard's `=>`) is the error as
    /// without recovery, at the token that stopped it.
    fn ran_out_after(&self, at: Span, expected: &str) -> Diagnostic {
        let Some(token) = self.tokens.get(self.pos) else {
            return error(
                at,
                format!("expected {expected}, but reached the end of the declaration"),
            );
        };
        let ends_line = self
            .modes
            .limit
            .is_some_and(|l| token.line_start && token.column <= l);
        if !ends_line {
            return self.unexpected(expected);
        }
        let diagnostic = error(at, format!("expected {expected}, but the line ends here"))
            .with_label(token.span, "this line starts a new statement")
            .with_note(format!(
                "the line starting with {} (in column {}) is at or left of the enclosing \
                 block's column ({}), so it starts a new statement",
                self.spelled(token),
                token.column + 1,
                self.modes.limit.map_or(0, |l| l + 1)
            ));
        if self.is_infix_only(&token.tok) {
            diagnostic.with_note(
                "to continue the expression on the line above, indent this line further than \
                 the block's column",
            )
        } else {
            diagnostic
        }
    }

    /// R6: parses a top-level definition's body (from its `:=` or first
    /// `|`) with `body`, recovering from any syntax error in it or after it
    /// that nothing inside caught. The error is reported, and the rest of
    /// the declaration is an `Error` node from where the body's expression
    /// or its arms start, so what finished before the error nests in it:
    /// inside the `Body` node after `:=`, or in place of the arms. The
    /// definition is then a definition whose body is missing, never a
    /// primitive (one with no body at all). `body` doesn't mark the `Body`
    /// after `:=`, which ends where the error's node does.
    pub(super) fn recovering_body(
        &mut self,
        body: impl FnOnce(&mut Self) -> Result<bool>,
    ) -> Result<bool> {
        let snapshot = self.snapshot();
        let at = self.pos;
        let colon = self.tokens[at].tok == Tok::ColonEq;
        self.modes.recover = true;
        let parsed = body(self).and_then(|read| self.finish().map(|()| read));
        self.modes.recover = snapshot.modes.recover;
        let read = match parsed {
            Ok(read) => read,
            Err(error) if error.code == "E-RESOURCE" => return Err(error),
            Err(error) => {
                self.recover_to(snapshot);
                // One error a place: an `R1` gap may have left what came
                // after it nothing to stand on.
                if self.errors.last().and_then(Diagnostic::primary_span) != error.primary_span() {
                    self.report(RecoveryPoint::Body, *error);
                }
                let from = at + usize::from(colon);
                self.pos = self.tokens.len();
                if from < self.pos {
                    self.node(from as u32, NodeKind::Error);
                }
                true
            }
        };
        if colon {
            self.node(at as u32, NodeKind::Body);
        }
        Ok(read)
    }

    /// `result`, the outcome of parsing a whole declaration or expression,
    /// unless an error was recovered from on the way: then the first such
    /// error, which comes before anything `result` holds, since the parser
    /// only moves forward. Taken out of [`Self::errors`]; any others stay.
    /// The entry points that return one error go through this, so they stop
    /// at the first syntax error whether or not the parser recovered from it.
    fn strict<T>(&mut self, result: Result<T>) -> Result<T> {
        if self.errors.is_empty() {
            result
        } else {
            Err(Box::new(self.errors.remove(0)))
        }
    }

    /// A lowercase name that's bound here, so it can't be qualified.
    fn lower(&mut self, what: &str) -> Result<&'t Token> {
        let name = self.lower_q(what)?;
        unqualified(name)?;
        Ok(name)
    }

    /// A parameter's name: like `lower`, but says why an uppercase name isn't one.
    fn param_name(&mut self) -> Result<&'t Token> {
        if let Some(Tok::Upper(text)) = self.peek() {
            return Err(self
                .unexpected("a parameter's name")
                .with_note(format!(
                    "parameter names start with a lowercase letter; an uppercase name such as \
                 `{text}` is a constructor"
                ))
                .into());
        }
        // `((x, y): Point)` or `({ x, y }: Point)`: a pattern, which a
        // definition's parameter can't be (SW-950).
        if matches!(self.peek(), Some(Tok::LParen | Tok::LBrace)) {
            return Err(self
                .unexpected("a parameter's name")
                .with_note(
                    "a definition's parameter is a name, not a pattern: name it, `(point: \
                     Point)`, and take it apart in the body with `let (x, y) := point` (or a \
                     `match`); a lambda's parameter can be a pattern, as in `((x, y)) => …`",
                )
                .into());
        }
        self.lower("a parameter's name")
    }

    /// A lowercase name, possibly qualified: `length` or `List.length`.
    fn lower_q(&mut self, what: &str) -> Result<&'t Token> {
        match self.peek() {
            Some(Tok::Lower(_)) => Ok(self.bump()),
            _ => Err(self.unexpected_name(what).into()),
        }
    }

    fn def_name(&mut self) -> Result<&'t Token> {
        match self.peek() {
            Some(Tok::Upper(_)) => self.upper_q("a name"),
            _ => self.lower_q("a name"),
        }
    }

    /// An uppercase name that's declared here, so it can't be qualified.
    fn upper(&mut self, what: &str) -> Result<&'t Token> {
        let name = self.upper_q(what)?;
        unqualified(name)?;
        Ok(name)
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
    fn ctor_name(&mut self) -> Result<&'t Token> {
        match self.peek() {
            Some(Tok::Lower(_)) => self.lower_q("a constructor"),
            _ => self.upper_q("a constructor"),
        }
    }

    /// An uppercase name, possibly qualified: `Cons` or `List.Cons`.
    fn upper_q(&mut self, what: &str) -> Result<&'t Token> {
        match self.peek() {
            Some(Tok::Upper(_)) => Ok(self.bump()),
            _ => Err(self.unexpected(what).into()),
        }
    }

    // Declarations

    /// `namespace Day05`: the namespace a file's declarations go in. Its
    /// name, for messages.
    fn namespace(&mut self) -> Result<&'t str> {
        self.expect(Tok::KwNamespace, "`namespace`")?;
        match self.peek() {
            Some(Tok::Upper(text)) => {
                self.bump();
                Ok(text)
            }
            Some(Tok::Lower(_)) => Err(error(
                self.here(),
                "each part of a namespace's name starts with a capital letter",
            )
            .into()),
            _ => Err(self.unexpected("a namespace, such as `Day05`").into()),
        }
    }

    /// `import List (map, filter)`: a namespace, then the names to use from
    /// it, at least one; or `import List (..)` for all of them.
    fn import(&mut self) -> Result<()> {
        self.expect(Tok::KwImport, "`import`")?;
        let path = match self.peek() {
            Some(Tok::Upper(text)) => {
                self.bump();
                text.as_str()
            }
            _ => return Err(self.unexpected("a namespace, such as `List`").into()),
        };
        if matches!(self.peek(), Some(Tok::Lower(word)) if word == "as") {
            return Err(self.import_as(path).into());
        }
        self.expect(Tok::LParen, "`(` and the names to import")?;
        let mixed = |dots: Span, path: &str| {
            error(
                dots,
                format!(
                    "`..` imports everything from a namespace, so it goes on its own: `import {path} (..)`"
                ),
            )
        };
        if self.peek() == Some(&Tok::DotDot) {
            let dots = self.here();
            self.bump();
            if self.peek() != Some(&Tok::RParen) {
                return Err(mixed(dots, path).into());
            }
        } else {
            let mut items = 0;
            loop {
                match self.peek() {
                    Some(Tok::Lower(text) | Tok::Upper(text)) if !text.contains('.') => {
                        let item = self.mark();
                        self.bump();
                        if self.peek() == Some(&Tok::Dot) {
                            return Err(self.import_qualified(path, text, self.pos).into());
                        }
                        self.import_alias(text)?;
                        self.node(item, NodeKind::ImportItem);
                        items += 1;
                    }
                    Some(Tok::Lower(text) | Tok::Upper(text)) => {
                        return Err(self.import_qualified(path, text, self.pos + 1).into());
                    }
                    Some(Tok::DotDot) if items > 0 => {
                        return Err(mixed(self.here(), path).into());
                    }
                    _ => return Err(self.unexpected("a name to import").into()),
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(())
    }

    /// `import A (B.c)` writes an item's namespace inside the brackets:
    /// the form that works puts it in the import's path, `import A.B (c)`.
    /// `first` is the item as written, and `from` is the token after it
    /// (a `.` when the source spaced the parts out).
    fn import_qualified(&self, path: &str, first: &str, mut from: usize) -> Diagnostic {
        let mut written = first.to_string();
        while self.tokens.get(from).is_some_and(|t| t.tok == Tok::Dot) {
            let Some(Tok::Lower(part) | Tok::Upper(part)) =
                self.tokens.get(from + 1).map(|t| &t.tok)
            else {
                break;
            };
            written.push('.');
            written.push_str(part);
            from += 2;
        }
        let (namespace, item) = match written.rsplit_once('.') {
            Some((namespace, item)) => (namespace.to_string(), item.to_string()),
            None => (String::new(), written.clone()),
        };
        self.unexpected("a name to import").with_note(format!(
            "an item of a namespace is imported with the namespace in the path before the \
             brackets: `import {path}.{namespace} ({item})`"
        ))
    }

    /// After an import's item `name`: `as y`, the name it has in this file.
    /// A name and its alias both start with a capital letter, or neither
    /// does, since that says what kind of name it is.
    fn import_alias(&mut self, name: &str) -> Result<()> {
        if !matches!(self.peek(), Some(Tok::Lower(word)) if word == "as") {
            return Ok(());
        }
        self.bump();
        let alias = match self.peek() {
            Some(Tok::Lower(text) | Tok::Upper(text)) if !text.contains('.') => text,
            _ => {
                return Err(self
                    .unexpected("the name to use instead, as in `x as y`")
                    .into());
            }
        };
        let upper = |n: &str| n.starts_with(|c: char| c.is_uppercase());
        if upper(name) != upper(alias) {
            let (case, example) = if upper(name) {
                ("a capital letter", "`Tree as T`")
            } else {
                ("a lower-case letter", "`length as len`")
            };
            return Err(Diagnostic::error(
                "E-PARSE",
                format!("`{name}` starts with {case}, so its new name must too"),
            )
            .with_label(
                self.here(),
                format!("`{alias}` would change what kind of name it is"),
            )
            .with_note(format!(
                "a type, ability or namespace is written with a capital letter, and a function \
                 or theorem without one: e.g. {example}"
            ))
            .into());
        }
        self.bump();
        Ok(())
    }

    /// `import M as A`, which isn't Stitchwort: what to write instead
    /// (docs/proposals/import-aliases.md, D2072). The cursor is at `as`.
    fn import_as(&self, path: &str) -> Diagnostic {
        let at = self.here();
        let alias = match self.tokens.get(self.pos + 1).map(|t| &t.tok) {
            Some(Tok::Upper(a) | Tok::Lower(a)) => Some(a.as_str()),
            _ => None,
        };
        let d = Diagnostic::error(
            "E-PARSE",
            "`import M as A` isn't Stitchwort: a namespace is imported as an item of the \
             namespace above it",
        )
        .with_label(at, "`as` goes inside the brackets, after an item");
        match (path.rsplit_once('.'), alias) {
            (Some((parent, last)), Some(alias)) if alias != last => d.with_note(format!(
                "to write `{alias}.x` for `{path}.x`: `import {parent} ({last} as {alias})`; \
                 or `import {parent} ({last})` to write `{last}.x`"
            )),
            (Some((parent, last)), _) => d.with_note(format!(
                "to write `{last}.x` for `{path}.x`: `import {parent} ({last})`"
            )),
            (None, _) => d.with_note(format!(
                "`{path}` is a root namespace, which has no other name: write `{path}.x` (no \
                 import needed in a project), or import names, `import {path} (x)`, `import \
                 {path} (x as y)` or `import {path} (..)`"
            )),
        }
    }

    fn pattern(&mut self) -> Result<()> {
        self.deeper()?;
        let start = self.mark();
        match self.peek() {
            Some(Tok::Lower(_)) if !self.ctor_ahead() => {
                self.lower("a pattern")?;
            }
            Some(Tok::Underscore | Tok::Num(_) | Tok::Char(_) | Tok::Str(_)) => {
                self.bump();
            }
            Some(Tok::StrStart(_)) => return Err(self.interpolated_pattern().into()),
            Some(Tok::Upper(_) | Tok::Lower(_)) => {
                self.ctor_name()?;
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                self.bump();
                self.node(start, NodeKind::PatternAbsurd);
            }
            Some(Tok::LBrace) => self.record_pattern()?,
            // `[n := p]`: an implicit field of a constructor, by name.
            Some(Tok::LBracket)
                if matches!(self.peek_at(1), Some(Tok::Lower(_)))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                self.lower("a field name")?;
                self.bump();
                self.pattern()?;
                self.expect(Tok::RBracket, "`]`")?;
                self.node(start, NodeKind::PatternNamed);
            }
            Some(Tok::LBracket) => {
                self.bump();
                let mut tail = false;
                if self.peek() != Some(&Tok::RBracket) {
                    loop {
                        if self.peek() == Some(&Tok::RBracket) {
                            break;
                        }
                        if self.eat(&Tok::DotDot) {
                            // `..rest`: the tail pattern, which must be last.
                            self.pattern()?;
                            tail = true;
                            break;
                        }
                        self.list_item()?;
                        if !self.eat(&Tok::Comma) {
                            break;
                        }
                    }
                }
                if tail && self.peek() == Some(&Tok::Comma) {
                    return Err(error(
                        self.here(),
                        "a `..` tail must be the last item of a list pattern",
                    )
                    .with_note(
                        "patterns take `..` only last, as in `[x, y, ..rest]`, because a list \
                         can be taken apart from the front only; to reach the end of a list, \
                         use `List.last` or `List.reverse`, or write a recursive function",
                    )
                    .into());
                }
                self.expect(
                    Tok::RBracket,
                    if tail {
                        "`]`: a `..` tail must be the last item"
                    } else {
                        "`,` or `]`"
                    },
                )?;
                self.node(start, NodeKind::PatternList);
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::Minus) => {
                // `(-k)`: a negative number pattern, only in brackets (a
                // tuple's included: `(-k, p)`).
                self.bump();
                self.tuple_item()?;
                if self.peek() == Some(&Tok::Comma) {
                    return self.tuple_pattern(start);
                }
                self.expect(Tok::RParen, "`)`")?;
                self.node(start, NodeKind::PatternParen);
            }
            Some(Tok::LParen) => {
                self.bump();
                let first = self.mark();
                if self.ctor_ahead() {
                    self.ctor_name()?;
                    self.ctor_args(first, |t| {
                        matches!(
                            t,
                            Some(Tok::RParen | Tok::Comma | Tok::Pipe | Tok::PlusPlus) | None
                        )
                    })?;
                } else {
                    self.pattern()?;
                }
                self.pattern_append(first, Self::tuple_component)?;
                self.alternatives(first, Self::tuple_component)?;
                if self.peek() == Some(&Tok::Comma) {
                    // `(Some a, b)`: a constructor as a tuple's first component.
                    return self.tuple_pattern(start);
                }
                self.expect(Tok::RParen, "`)`")?;
                self.node(start, NodeKind::PatternParen);
            }
            _ => return Err(self.unexpected_name("a pattern or `=`").into()),
        }
        Ok(())
    }

    /// `"${a}b"` where a pattern should be: a text pattern is one fixed text
    /// (docs/proposals/text-patterns.md §4.1). The cursor is at its
    /// `StrStart`; the error spans the whole literal when it parses.
    fn interpolated_pattern(&mut self) -> Diagnostic {
        let start = self.here();
        let span = match self.interpolated_str() {
            Ok(()) => Span {
                end: self.tokens[self.pos - 1].span.end,
                ..start
            },
            Err(_) => start,
        };
        Diagnostic::error("E-TEXT-PATTERN", "a text pattern can't interpolate")
            .with_label(span, "a pattern matches one fixed text")
            .with_note(
                "to match a text that starts a certain way, write its start and a pattern for \
                 the rest: `\"--\" ++ rest`; to match one that ends a certain way, bind it to \
                 a variable and test it in a guard: `| t if t.endsWith \".sw\" => …`",
            )
    }

    /// The text of the name at token `i`.
    fn text_at(&self, i: u32) -> &'t str {
        match &self.tokens[i as usize].tok {
            Tok::Lower(text) | Tok::Upper(text) => text,
            _ => "",
        }
    }

    /// The arguments of the constructor whose name is token `name`, from
    /// here to a token `stop` accepts: positional patterns, or braces right
    /// after the name, `C { f = p, g, .. }`. The braces name `C`'s fields if
    /// it is declared with its fields in braces, and are a record pattern
    /// for its argument if it is declared with brackets: the elaborator
    /// decides (`Pattern::CtorFields`). They take no further arguments; a
    /// pattern with more is written `C ({ … }) …`.
    fn ctor_args(&mut self, name: u32, stop: fn(Option<&Tok>) -> bool) -> Result<()> {
        if self.peek() == Some(&Tok::LBrace) {
            let open = self.here();
            self.record_pattern_braces()?;
            if !stop(self.peek()) {
                let name = self.text_at(name);
                let braces = Span {
                    end: self.tokens[self.pos - 1].span.end,
                    ..open
                };
                return Err(error(
                    self.here(),
                    format!("braces after `{name}` in a pattern take no further arguments"),
                )
                .with_label(
                    braces,
                    format!("these braces are matched as `{name}`'s own"),
                )
                .with_note(format!(
                    "to match a record as `{name}`'s first argument and then more, write it \
                     in brackets: `{name} ({{ … }}) …`"
                ))
                .into());
            }
            self.node(name, NodeKind::PatternCtorFields);
            return Ok(());
        }
        let mut args = false;
        while !stop(self.peek()) {
            args = true;
            if self.peek() == Some(&Tok::LBrace) {
                // A record pattern after another argument is one more
                // argument; after a constructor name it would be that
                // constructor's braces.
                if matches!(self.tokens[self.pos - 1].tok, Tok::Upper(_)) {
                    return Err(error(
                        self.here(),
                        format!(
                            "a record pattern after a constructor in an argument of `{}` is written in brackets: `({{ … }})`",
                            self.text_at(name)
                        ),
                    )
                    .with_note("braces after a constructor name are matched as its own: `C { f = p, .. }`")
                    .into());
                }
                self.record_pattern()?;
                continue;
            }
            if self.argument_minus_at(self.pos) {
                // `Some -1`: a negative number, as `(-1)` is (D1470).
                let start = self.mark();
                self.bump();
                let Some(Tok::Num(_)) = self.peek() else {
                    return Err(self.unexpected("a number").into());
                };
                self.bump();
                self.node(start, NodeKind::PatternNegative);
                continue;
            }
            self.pattern()?;
        }
        if args {
            self.node(name, NodeKind::PatternCtor);
        }
        Ok(())
    }

    /// `{ name = p, age, .. }`: fields in any order, each a pattern or punned
    /// (a variable of the field's name), optionally ending with `..`.
    fn record_pattern(&mut self) -> Result<()> {
        let start = self.mark();
        self.record_pattern_braces()?;
        self.node(start, NodeKind::PatternRecord);
        Ok(())
    }

    /// [`Self::record_pattern`] without its mark: a constructor's braces,
    /// `C { f = p }`, are part of the constructor's own node.
    fn record_pattern_braces(&mut self) -> Result<()> {
        self.expect(Tok::LBrace, "`{`")?;
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                if self.eat(&Tok::DotDot) {
                    break;
                }
                if self.peek() == Some(&Tok::RBrace) {
                    break;
                }
                self.lower("a field name, or `..`")?;
                if self.eat(&Tok::Equals) {
                    // A constructor's arguments run to the next `,` or `}`.
                    if self.ctor_ahead() {
                        let start = self.mark();
                        self.ctor_name()?;
                        self.ctor_args(start, |t| {
                            matches!(t, Some(Tok::Comma | Tok::RBrace) | None)
                        })?;
                    } else {
                        self.pattern()?;
                    }
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RBrace, "`,` or `}`")?;
        Ok(())
    }

    /// `type T …` or `interface I …`: a data type, record, interface or type
    /// synonym, which it says.
    fn data(&mut self) -> Result<NodeKind> {
        self.bump();
        let interface = self.tokens[self.pos - 1].tok == Tok::KwInterface;
        let name = if interface {
            self.upper_q("an interface name (starting with an uppercase letter)")?
        } else {
            self.upper_q("a data type name (starting with an uppercase letter)")?
        };
        loop {
            if self.peek() == Some(&Tok::LParen) {
                let binder = self.binder()?;
                if let Some(first) = binder.attribute {
                    return Err(misplaced_attributes(&first, "a data type's parameter").into());
                }
            } else if self.is_implicit_binder() {
                // `[auto ord: Ord k]`, filled in by instance search wherever
                // the type is written (docs/proposals/interfaces.md §7.5).
                let start = self.here();
                let binder = self.implicit_binder()?;
                if let Some(first) = binder.attribute {
                    return Err(misplaced_attributes(&first, "a data type's parameter").into());
                }
                if !binder.auto {
                    return Err(error(
                        start.to(self.prev_span()),
                        "a type's parameters in brackets must be `auto`, like `[auto ord: Ord k]`",
                    )
                    .with_note(
                        "a type's other parameters are always given, so they're written \
                         `(a: Type)`",
                    )
                    .into());
                }
                if binder.nameless {
                    return Err(error(
                        start.to(self.prev_span()),
                        "a type's `auto` parameter needs a name, so it can be given by name: \
                         `[auto ord: Ord k]`",
                    )
                    .into());
                }
            } else if let Some(Tok::Lower(param)) = self.peek()
                && !param.contains('.')
            {
                let keyword = if interface { "interface" } else { "type" };
                return Err(error(
                    self.here(),
                    format!("a {keyword}'s parameter `{param}` needs its type, in brackets"),
                )
                .with_note(format!(
                    "write `{keyword} {} ({param}: Type) …`",
                    name_text(name)
                ))
                .into());
            } else {
                break;
            }
        }
        // After the colon: index types, each followed by `->`, then the
        // universe (docs/proposals/indexed-families.md §7.1). The first
        // index's type, for messages.
        let mut first_index = None;
        let colon = self.mark();
        if self.eat(&Tok::Colon) {
            loop {
                if self.is_pi_binder() {
                    let binder = self.binder()?;
                    if let Some(first) = binder.attribute {
                        return Err(misplaced_attributes(&first, "a data type's index").into());
                    }
                    self.expect(Tok::Arrow, "`->`")?;
                    first_index.get_or_insert(binder.ty);
                    continue;
                }
                let ty = self.mark();
                self.app()?;
                if self.eat(&Tok::Arrow) {
                    first_index.get_or_insert((ty, self.mark() - 1));
                    continue;
                }
                break;
            }
            self.node(colon, NodeKind::ResultType);
        }
        // An interface is a record (docs/proposals/interfaces.md §5.1).
        if interface {
            if let Some(ty) = first_index {
                return Err(error(self.lowered_span(ty), "an interface can't have indices").into());
            }
            self.expect(Tok::Equals, "`=` and the interface's fields, `{ … }`")?;
            if self.peek() != Some(&Tok::LBrace) {
                return Err(self.unexpected("`{` and the interface's fields").into());
            }
            self.braced_fields()?;
            return Ok(NodeKind::Interface);
        }
        if !self.eat(&Tok::Equals) {
            return Ok(NodeKind::DataType);
        }
        if !matches!(self.peek(), Some(Tok::LBrace | Tok::Pipe)) {
            if let Some(ty) = first_index {
                return Err(error(
                    self.lowered_span(ty),
                    "a type synonym can't have indices: `->` after the colon is only for a \
                     data type's indices",
                )
                .into());
            }
            self.type_synonym(name)?;
            return Ok(NodeKind::TypeSynonym);
        }
        if self.peek() == Some(&Tok::LBrace) {
            if let Some(row) = self.ability_row_in_braces() {
                return Err(Diagnostic::error(
                    "E-PARSE",
                    format!(
                        "an ability row like `{{{row}}}` can't be given a name with `type` \
                         yet; write the row where it's used, such as `() -> {{{row}}} Nat`"
                    ),
                )
                .with_label(
                    self.here(),
                    "this `{` starts an ability row, not a record type",
                )
                .into());
            }
            self.braced_fields()?;
            return Ok(NodeKind::RecordType);
        }
        let mut ctors = 0;
        while self.peek() == Some(&Tok::Pipe) {
            let ctor = self.mark();
            self.bump();
            self.attributes()?;
            let name = self.upper("a constructor name (starting with an uppercase letter)")?;
            let name = name_text(name);
            // Whether an explicit field was declared in brackets or in braces.
            let (mut bracketed, mut braced) = (false, false);
            loop {
                if self.peek() == Some(&Tok::LBrace) && !braced {
                    // `| C { f: T, … }`: the explicit fields in
                    // braces, instead of brackets.
                    if bracketed {
                        return Err(error(
                            self.here(),
                            format!(
                                "`{name}` has fields in brackets already; declare all of \
                                 its explicit fields in brackets or all in braces"
                            ),
                        )
                        .into());
                    }
                    braced = true;
                    let open = self.here();
                    if self.braced_fields()? == 0 {
                        return Err(error(
                            open,
                            format!("`{name}` declares no fields in its braces"),
                        )
                        .with_note("a constructor without fields is just `| C`")
                        .into());
                    }
                } else if self.peek() == Some(&Tok::LParen) {
                    if braced {
                        return Err(error(
                            self.here(),
                            format!(
                                "`{name}` has its fields in braces already; declare all of \
                                 its explicit fields in braces or all in brackets"
                            ),
                        )
                        .into());
                    }
                    self.binder_with_default()?;
                    bracketed = true;
                } else if self.is_implicit_binder() {
                    let binder = self.implicit_binder()?;
                    if binder.auto {
                        return Err(error(
                            binder.first_name,
                            "a constructor's implicit fields can't be `auto`",
                        )
                        .into());
                    }
                } else {
                    break;
                }
            }
            // The result type, `: Vec a (Succ n)`.
            let colon = self.mark();
            if self.eat(&Tok::Colon) {
                self.app()?;
                self.node(colon, NodeKind::ResultType);
            }
            ctors += 1;
            self.node(ctor, NodeKind::Constructor);
        }
        if ctors == 0 {
            return Err(self
                .unexpected("`|` and a constructor, or `{` and a record's fields")
                .into());
        }
        Ok(NodeKind::DataType)
    }

    /// The abilities in a record type's braces at the cursor, if they hold an
    /// ability row instead of fields: a capitalised name followed by `,` or
    /// `}`, as in `{IO, Fail}` or `{IO}`. A row can't be named with `type`
    /// yet, so the parser reports it rather than reading `IO` as a field name.
    fn ability_row_in_braces(&self) -> Option<String> {
        let (Some(Tok::Upper(first)), Some(Tok::Comma | Tok::RBrace)) =
            (self.peek_at(1), self.peek_at(2))
        else {
            return None;
        };
        let mut names = vec![first.clone()];
        let mut at = self.pos + 2;
        while self.tokens.get(at).map(|t| &t.tok) == Some(&Tok::Comma) {
            // Only a plain ability name, followed by `,` or `}`: an entry
            // with arguments (`State s`) is named by its first ability only.
            match (
                self.tokens.get(at + 1).map(|t| &t.tok),
                self.tokens.get(at + 2).map(|t| &t.tok),
            ) {
                (Some(Tok::Upper(name)), Some(Tok::Comma | Tok::RBrace)) => {
                    names.push(name.clone())
                }
                _ => break,
            }
            at += 2;
        }
        let row = names.join(", ");
        Some(
            if self.tokens.get(at).map(|t| &t.tok) == Some(&Tok::RBrace) {
                row
            } else {
                format!("{row}, …")
            },
        )
    }

    /// Fields in braces, `{ name : Text, step : Nat := 1 }`, each with its
    /// default if it has one: a record's, or a constructor's declared with
    /// `| C { … }`. How many there are.
    fn braced_fields(&mut self) -> Result<usize> {
        let mark = self.mark();
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = 0;
        if self.peek() != Some(&Tok::RBrace) {
            loop {
                if self.peek() == Some(&Tok::RBrace) {
                    break;
                }
                let field_start = self.mark();
                self.attributes()?;
                self.lower("a field name")?;
                self.expect(Tok::Colon, "`:`")?;
                self.expr()?;
                let default_start = self.mark();
                if self.eat(&Tok::ColonEq) {
                    self.expr()?;
                    self.node(default_start, NodeKind::Default);
                }
                self.node(field_start, NodeKind::Field);
                fields += 1;
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(Tok::RBrace, "`,` or `}`")?;
        self.node(mark, NodeKind::Fields);
        Ok(fields)
    }

    /// `ability Name (params) where`, then one operation per line.
    fn ability(&mut self) -> Result<()> {
        self.bump();
        self.upper_q("an ability name (starting with an uppercase letter)")?;
        while self.peek() == Some(&Tok::LParen) {
            let binder = self.binder()?;
            if let Some(first) = binder.attribute {
                return Err(misplaced_attributes(&first, "an ability's parameter").into());
            }
        }
        self.expect(Tok::KwWhere, "`where`")?;
        let Some(first) = self.tokens.get(self.pos).filter(|_| self.peek().is_some()) else {
            return Err(self.unexpected("the ability's operations").into());
        };
        let column = first.column;
        let saved = (self.modes.limit, self.modes.allow);
        self.modes.limit = Some(column);
        let result = loop {
            self.modes.allow = Some(self.pos);
            let op = (|| -> Result<()> {
                let start = self.mark();
                self.lower("an operation name")?;
                self.expect(Tok::Colon, "`:`")?;
                self.expr_inline()?;
                self.node(start, NodeKind::AbilityOp);
                Ok(())
            })();
            if let Err(e) = op {
                break Err(e);
            }
            if !self.starts_line_at(column) {
                break Ok(());
            }
        };
        (self.modes.limit, self.modes.allow) = saved;
        result
    }

    /// Whether the next token starts a line at exactly `column`.
    fn starts_line_at(&self, column: u32) -> bool {
        self.tokens
            .get(self.pos)
            .is_some_and(|t| t.line_start && t.column == column)
    }

    /// `(x y : A)`, with any attributes before the names (which only a
    /// constructor's field may have: the callers refuse them elsewhere).
    fn binder(&mut self) -> Result<BinderRead> {
        let binder = self.binder_with_default()?;
        if let Some(default) = binder.default {
            return Err(
                error(self.lowered_span(default), declarations::DEFAULT_PLACES)
                    .with_note(
                        "a definition's explicit parameters, `def range (step: Nat := 1)`, a \
                     record's fields, `{ step: Nat := 1 }`, and a constructor's, \
                     `| Circle (id: Text := \"a\")`, can have one; a function type can't",
                    )
                    .into(),
            );
        }
        Ok(binder)
    }

    /// `(x y : A)`, or with a default value, `(x y : A := v)`, which only a
    /// constructor's field may have (docs/proposals/named-arguments.md
    /// §5.1).
    fn binder_with_default(&mut self) -> Result<BinderRead> {
        let mark = self.mark();
        self.expect(Tok::LParen, "`(`")?;
        let attribute = self.attributes()?;
        let first_name = self.lower("a name")?.span;
        while let Some(Tok::Lower(_)) = self.peek() {
            self.lower("a name")?;
        }
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.mark();
        self.binder_type()?;
        let ty = (ty, self.mark());
        let default_start = self.mark();
        let default = if self.eat(&Tok::ColonEq) {
            let value = self.mark();
            self.expr()?;
            self.node(default_start, NodeKind::Default);
            Some((value, self.mark()))
        } else {
            None
        };
        self.expect(Tok::RParen, "`)`")?;
        self.node(mark, NodeKind::Binder);
        Ok(BinderRead {
            attribute,
            auto: false,
            nameless: false,
            first_name,
            ty,
            default,
        })
    }

    /// A binder's type, after its `:`. An ability row is written only on a
    /// result type (D1141 (d)), so `{…} T` here, braces followed by a type,
    /// is refused with what to write instead, rather than read as a record
    /// literal applied to `T` (SW-908): `{} Nat` gave "can't tell which
    /// record type this literal is", `{IO} Nat` "expected `|` and the
    /// fields to update".
    fn binder_type(&mut self) -> Result<()> {
        self.allow_brace_at_block_column();
        if self.peek() == Some(&Tok::LBrace)
            && let close = self.matching[self.pos]
            && close != NO_PARTNER
            && self.tokens.get(close as usize + 1).is_some_and(|t| {
                matches!(
                    t.tok,
                    Tok::Upper(_)
                        | Tok::Lower(_)
                        | Tok::LParen
                        | Tok::LBracket
                        | Tok::TypeU
                        | Tok::Prop
                )
            })
        {
            let span = self.tokens[self.pos]
                .span
                .to(self.tokens[close as usize].span);
            let note = if close as usize == self.pos + 1 {
                "a row written `{}` is no row: `{} Nat` is `Nat`, so write the type without it"
            } else {
                "a computation type is written only as a result type: to take a computation, \
                 take a function returning it, as in `(c: () -> {IO} Nat)`"
            };
            return Err(Diagnostic::error(
                "E-PARSE",
                "an ability row can't be written in a parameter's type",
            )
            .with_label(span, "this `{…}` is an ability row")
            .with_note(note)
            .into());
        }
        self.expr()
    }

    // Expressions, loosest-binding first

    /// An expression, or a block if it starts on a new line.
    fn expr(&mut self) -> Result<()> {
        self.deeper()?;
        if let Some(token) = self.tokens.get(self.pos)
            && token.line_start
            && self.pos > 0
            && self.modes.allow != Some(self.pos)
            && !self.ends_construct(self.pos)
        {
            match self.modes.limit {
                None => return self.block(token.column, true),
                Some(limit) if token.column > limit => return self.block(token.column, true),
                // R1: a statement line at the block's column after `:=` or
                // an operator is the next statement, and the line above ran
                // out, unless it is an expression `let` (`let x := e; body`).
                Some(limit)
                    if token.column == limit
                        && self.modes.recover
                        && matches!(token.tok, Tok::KwLet | Tok::KwDef | Tok::KwTheorem)
                        && !self.line_has_semicolon(self.pos, limit) =>
                {
                    return self.ran_out("an expression");
                }
                // A line at the block's own column after a line ending in an
                // operator: it continues that line.
                Some(limit) if token.column == limit => return self.block(token.column, false),
                Some(_) => {}
            }
        }
        self.expr_inline()
    }

    /// Whether the line starting at token `start` has a `;` before the next
    /// line at or left of `limit`, in brackets or not.
    fn line_has_semicolon(&self, start: usize, limit: u32) -> bool {
        (self.tokens[start..].iter())
            .enumerate()
            .take_while(|(k, t)| *k == 0 || !(t.line_start && t.column <= limit))
            .any(|(_, t)| t.tok == Tok::Semi)
    }

    /// Lines at `column`, each a statement, the last being the result. With
    /// `many` false, just one line.
    fn block(&mut self, column: u32, many: bool) -> Result<()> {
        let saved = (self.modes.limit, self.modes.allow);
        // A new block's lines may be sequences, even inside a `let`'s value;
        // a line continuing the one before (`many` false) stays in it.
        let let_value = self.modes.let_value;
        if many {
            self.modes.let_value = None;
        }
        self.modes.limit = Some(column);
        let start = self.mark();
        let mut lines = 0;
        let mut last = Line::Expr;
        let result = loop {
            let before = self.pos;
            self.modes.allow = Some(self.pos);
            match self.statement() {
                Ok(line) => {
                    last = line;
                    lines += 1;
                }
                Err(e) => break Err(e),
            }
            // A statement that read nothing (R1 reporting a gap at a stop)
            // leaves the same line at the block's column, and reading it
            // again would report the same gap forever (SW-3285).
            if self.pos == before || !(many && self.starts_line_at(column)) || self.ends_blocks() {
                break Ok(());
            }
        };
        (self.modes.limit, self.modes.allow) = saved;
        self.modes.let_value = let_value;
        result?;
        if lines > 1 {
            self.node(start, NodeKind::Block);
        }
        match last {
            Line::Expr => Ok(()),
            Line::Let(span) => {
                Err(error(span, "a block must end with an expression, not `let`").into())
            }
            Line::Def(span) => Err(error(
                span,
                "a block must end with an expression, not a local `def` or `theorem`",
            )
            .into()),
        }
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

    fn statement(&mut self) -> Result<Line> {
        let start = self.mark();
        match self.peek() {
            Some(Tok::KwLet) => {
                let span = self.let_statement()?;
                // `let x := e; body` on a line is the expression `let`.
                if self.peek() == Some(&Tok::Semi) {
                    self.let_body()?;
                    self.node(start, NodeKind::LetExpr);
                    Ok(Line::Expr)
                } else {
                    Ok(Line::Let(span))
                }
            }
            Some(Tok::KwDef | Tok::KwTheorem) => self.local_def(start),
            // `@[tailrec] def go …`: the `def` may be on the next line, at
            // the block's column.
            Some(Tok::At) => {
                let first = self.attributes()?;
                if self
                    .modes
                    .limit
                    .is_some_and(|column| self.starts_line_at(column))
                {
                    self.modes.allow = Some(self.pos);
                }
                if !matches!(self.peek(), Some(Tok::KwDef | Tok::KwTheorem)) {
                    let first = first.expect("an attribute");
                    return Err(misplaced_attributes(
                        &first,
                        "a statement that isn't a local definition",
                    )
                    .into());
                }
                self.local_def(start)
            }
            Some(Tok::KwExport) => Err(error(
                self.here(),
                "local definitions can't be exported: only top-level ones are",
            )
            .into()),
            Some(Tok::KwOpaque) => Err(error(
                self.here(),
                "local definitions can't be `opaque`: only top-level ones can",
            )
            .into()),
            _ => {
                self.expr_inline()?;
                Ok(Line::Expr)
            }
        }
    }

    /// A local `def` or `theorem`, written as at top level, but with a body.
    /// `mark` is where it starts, at its attributes if it has any.
    #[inline(never)]
    fn local_def(&mut self, mark: u32) -> Result<Line> {
        let start = self.here();
        let definition = self.definition(start, false, false)?;
        self.node(mark, definition.kind);
        if let Some(first) = definition.unfolding {
            return Err(error(
                first,
                "a local definition can't have `unfolding`",
            )
            .with_note(
                "it unfolds what the declaration it's in unfolds: write `unfolding` on that one",
            ).into());
        }
        if !definition.body {
            // An empty result type ran out (R1), which reported the gap;
            // at the gap's own span, R6 keeps this as the same error.
            let (from, to) = definition.result;
            let at = if from == to {
                self.tokens_span(definition.result)
            } else {
                start.to(self.lowered_span(definition.result))
            };
            return Err(error(
                at,
                "a local definition needs a body: `:=` and an expression, or arms starting with `|`",
            ).into());
        }
        Ok(Line::Def(start))
    }

    /// After an expression `let`'s header and value (`let x := e`): the `;`
    /// and the body, which together with them make the same tree as a block
    /// `let` followed by its rest (D1425, D1453: `in` is membership).
    #[inline(never)]
    fn let_body(&mut self) -> Result<()> {
        if self.peek() != Some(&Tok::Semi) {
            return Err(self
                .unexpected("`;` after the value of `let`")
                .with_note(
                    "an expression `let` is written `(let x := e; body)`; `in` is membership, \
                     not a separator",
                )
                .into());
        }
        self.bump();
        let at_end = self.tokens.get(self.pos).is_none_or(|t| {
            matches!(
                t.tok,
                Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Comma
            )
        });
        if at_end {
            return Err(error(
                self.here(),
                "`let` needs a body after `;`: `(let x := e; body)`",
            )
            .into());
        }
        self.expr()
    }

    /// `let p := e`, or `let p : T := e`; the type may contain `=`. The
    /// span of its `let`.
    #[inline(never)]
    fn let_statement(&mut self) -> Result<Span> {
        let start_index = self.pos;
        let start = self.bump().span;
        self.let_pattern()?;
        // A single lowercase name, which `let_pattern` reads as a variable.
        let var = (self.pos == start_index + 2)
            .then(|| &self.tokens[start_index + 1].tok)
            .and_then(|tok| match tok {
                Tok::Lower(name) => Some(name),
                _ => None,
            });
        let typed = self.eat(&Tok::Colon);
        if typed {
            self.expr_inline()?;
        }
        if self.peek() == Some(&Tok::Equals) {
            return Err(self.def_equals().into());
        }
        // `let f (y: Nat) …` is a local function, which a `let` can't bind:
        // point at the local `def` form (docs/syntax.md "Local definitions").
        if !typed
            && let Some(name) = var
            && self.peek() == Some(&Tok::LParen)
            && !self.is_stop(self.pos)
        {
            return Err(self
                .unexpected("`:=`")
                .with_note(format!(
                    "a `let` binds a value; for a function write a local `def {name} (y: Nat) …: \
                     T := …`, or `let {name} := (y: Nat) => …`"
                ))
                .into());
        }
        self.expect(Tok::ColonEq, "`:=`")?;
        let outer = self.modes.let_value.replace(start_index);
        let value = self.expr();
        self.modes.let_value = outer;
        value?;
        self.node(start_index as u32, NodeKind::Let);
        Ok(start)
    }

    /// The pattern after `let`: a constructor may take arguments without
    /// brackets (`let MkPair a b := p`), running to the `:=` or `:` (or a
    /// mistaken `=`, reported by `let_statement`).
    fn let_pattern(&mut self) -> Result<()> {
        if self.ctor_ahead() {
            let start = self.mark();
            self.ctor_name()?;
            return self.ctor_args(start, |t| {
                matches!(t, Some(Tok::Equals | Tok::ColonEq | Tok::Colon) | None)
            });
        }
        self.tuple_component()
    }

    /// A `{` starting a line at the block's own column continues the line
    /// above when that ended in `:` or an arrow ([`Self::expr`]), so in a
    /// type it is a row, as on the arrow's line, not a record: `peek` would
    /// otherwise hide it as the start of a new statement (SW-3582, SW-3594).
    fn allow_brace_at_block_column(&mut self) {
        if let Some(token) = self.tokens.get(self.pos)
            && token.tok == Tok::LBrace
            && token.line_start
            && self.modes.limit == Some(token.column)
            && !self.ends_construct(self.pos)
        {
            self.modes.allow = Some(self.pos);
        }
    }

    /// A function's result type, possibly with abilities: `{State s} Nat`.
    ///
    /// A theorem's statement is a result type too, and may start with a
    /// record literal or update: `{ p | x = 3 }.x = 3` ([`record_braces`]).
    fn result_type(&mut self) -> Result<()> {
        self.allow_brace_at_block_column();
        if self.peek() != Some(&Tok::LBrace) || record_braces(self.tokens, self.pos) {
            return self.expr();
        }
        let start = self.mark();
        self.row()?;
        self.node(start, NodeKind::Row);
        self.expr()?;
        self.node(start, NodeKind::Effect);
        Ok(())
    }

    /// `{A, B args | e}`, `{e}` or `{}`.
    fn row(&mut self) -> Result<()> {
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
            )
            .into());
        }
        if self.peek() != Some(&Tok::RBrace) && self.peek() != Some(&Tok::Pipe) {
            self.app()?;
            while self.eat(&Tok::Comma) {
                self.app()?;
            }
        }
        if self.eat(&Tok::Pipe) {
            self.lower("a row variable")?;
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(())
    }

    /// `handle e with | return x => … | op arg, k => …`
    fn handle(&mut self, start: u32) -> Result<()> {
        self.expr_inline()?;
        self.expect(Tok::KwWith, "`with`")?;
        self.handler_clauses()?;
        self.node(start, NodeKind::Handle);
        Ok(())
    }

    /// A handler's clauses, each after a `|`; at least one.
    fn handler_clauses(&mut self) -> Result<()> {
        let mut clauses = 0;
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
            let clause = self.mark();
            self.bump();
            self.handler_clause()?;
            self.node(clause, NodeKind::HandlerClause);
            clauses += 1;
        }
        if clauses == 0 {
            return Err(self.unexpected("`|` and a handler clause").into());
        }
        Ok(())
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
    fn reify_expr(&mut self, start: u32) -> Result<()> {
        self.expr_inline()?;
        if self.peek() == Some(&Tok::Comma) {
            return Err(error(
                self.here(),
                "`match reify` takes one computation, with nothing else to match",
            )
            .into());
        }
        self.expect(Tok::KwWith, "`with`")?;
        self.handler_clauses()?;
        self.node(start, NodeKind::Reify);
        Ok(())
    }

    /// Whether `induct` starts here as the keyword it is after `match`: followed
    /// by the call, not by `with`, `,` or `:` (where it is an ordinary name).
    fn induct_ahead(&self) -> bool {
        matches!(self.peek(), Some(Tok::Lower(name)) if name == "induct")
            && !matches!(
                self.peek_at(1),
                Some(Tok::KwWith | Tok::Comma | Tok::Colon) | None
            )
    }

    /// `match induct (f args) with | eqK x y ih => … | …`, or `with ?` to list
    /// the cases, after `match` and `induct` (docs/proposals/function-equations.md §5.3).
    fn induct_expr(&mut self, start: u32) -> Result<()> {
        self.expr_inline()?;
        if self.peek() == Some(&Tok::Comma) {
            return Err(error(
                self.here(),
                "`match induct` takes one call, with nothing else to match",
            )
            .into());
        }
        self.expect(Tok::KwWith, "`with`")?;
        // `?`: the cases are listed, none written yet.
        if self.peek() == Some(&Tok::Question) {
            self.bump();
            self.node(start, NodeKind::Induct);
            return Ok(());
        }
        let mut alts = 0;
        // Alternatives on their own lines line up, as a match's do.
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
            let arm = self.mark();
            // `| eq1 x | eq3 y => body`: cases that share a proof.
            loop {
                self.bump();
                self.lower("the name of a case of `f.induct`")?;
                loop {
                    match self.peek() {
                        Some(Tok::Lower(_)) => {
                            self.lower("a name")?;
                        }
                        Some(Tok::Underscore) => {
                            self.bump();
                        }
                        _ => break,
                    }
                }
                if self.peek() != Some(&Tok::Pipe) {
                    break;
                }
            }
            self.expect_fat_arrow("`=>`")?;
            self.expr()?;
            self.node(arm, NodeKind::InductArm);
            alts += 1;
        }
        if alts == 0 {
            return Err(self
                .unexpected("`|` and an alternative named after a case")
                .into());
        }
        self.node(start, NodeKind::Induct);
        Ok(())
    }

    /// `match e, h : e2 with | p, q => body | …`
    fn match_expr(&mut self, start: u32) -> Result<()> {
        if self.induct_ahead() {
            self.bump();
            return self.induct_expr(start);
        }
        if self.reify_ahead() {
            self.bump();
            return self.reify_expr(start);
        }
        if self.peek() == Some(&Tok::Pipe) {
            return self.clause_lambda(start, MatchKind::Clause);
        }
        if self.some_bar_ahead() {
            self.bump();
            return self.clause_lambda(start, MatchKind::ClauseSome);
        }
        let mut scrutinees = 0;
        loop {
            let scrutinee = self.mark();
            let named =
                matches!(self.peek(), Some(Tok::Lower(_))) && self.peek_at(1) == Some(&Tok::Colon);
            if named {
                self.lower("a name")?;
                self.bump();
            }
            if named && self.reify_ahead() {
                return Err(
                    Diagnostic::error("E-PARSE", "`match reify` can't name an equation")
                        .with_label(
                            self.tokens[start as usize].span.to(self.here()),
                            "`h:` names an equation here",
                        )
                        .with_note(
                            "both sides would be computations, whose type has no spelling; in each \
                     clause the goal already says what the computation did",
                        )
                        .into(),
                );
            }
            self.expr_inline()?;
            self.node(scrutinee, NodeKind::Scrutinee);
            scrutinees += 1;
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::KwWith, "`with`")?;
        let mut alts = 0;
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
            let arm = self.mark();
            let bar = self.bump().span;
            let patterns = self.mark();
            let mut n = 1;
            self.alt_pattern()?;
            while self.eat(&Tok::Comma) {
                self.alt_pattern()?;
                n += 1;
            }
            if n != scrutinees {
                let m = scrutinees;
                let mut e = error(
                    bar.to(self.prev_span()),
                    format!(
                        "this alternative has {n} pattern{}, but the `match` has {m} scrutinee{}",
                        if n == 1 { "" } else { "s" },
                        if m == 1 { "" } else { "s" },
                    ),
                );
                // `| Rock, () | Paper, ()` on one line: the second `|` is
                // read as an or-pattern's.
                if self.or_with_absurd(patterns) {
                    e = e.with_note(
                        "an absurd alternative ends at its `()`: start the next `|` on a new line",
                    );
                }
                return Err(e.into());
            }
            let absurd = self.absurd_since(patterns);
            self.guard()?;
            self.arm_body(absurd, "`=>`")?;
            self.node(arm, NodeKind::Arm);
            alts += 1;
        }
        if alts == 0 {
            return Err(self.unexpected("`|` and an alternative").into());
        }
        self.node(start, NodeKind::Match);
        Ok(())
    }

    /// Whether one of the patterns read since token `from` is an
    /// or-pattern with an absurd pattern among its alternatives: a pattern
    /// of its own, one no other mark since `from` holds.
    #[cold]
    #[inline(never)]
    fn or_with_absurd(&self, from: u32) -> bool {
        let marks: Vec<&Mark> = self.marks.iter().filter(|m| m.start >= from).collect();
        marks.iter().any(|or| {
            or.kind == NodeKind::PatternOr
                && !marks.iter().any(|outer| {
                    outer.start <= or.start
                        && or.end <= outer.end
                        && (outer.start, outer.end) != (or.start, or.end)
                })
                && self.absurd_in(or.start, or.end)
        })
    }

    /// Whether `some |` is next, after `match`: the keyword of the partial
    /// clause lambda. `some` is a name anywhere else, so `match some with`
    /// still matches on a variable called `some`.
    fn some_bar_ahead(&self) -> bool {
        matches!(self.peek(), Some(Tok::Lower(word)) if word == "some")
            && self.peek_at(1) == Some(&Tok::Pipe)
    }

    /// Whether `matches |` is next: the Boolean clause lambda. Not a record
    /// update `{matches | field = e}`, whose `|` is followed by a field.
    fn matches_bar_ahead(&self) -> bool {
        matches!(self.peek(), Some(Tok::Lower(word)) if word == "matches")
            && self.peek_at(1) == Some(&Tok::Pipe)
            && !(matches!(self.peek_at(2), Some(Tok::Lower(_)))
                && self.peek_at(3) == Some(&Tok::Equals))
    }

    /// `match | p, q => e | …`, after `match` (or `match some`, or the
    /// `matches` word): a lambda over a `match` on its parameters, which the
    /// alternatives' patterns are for (docs/proposals/partial-lambdas.md).
    /// For `ClauseSome` each result is wrapped in `Some` and for
    /// `ClauseMatches` an alternative may leave its result out, which is
    /// `True`.
    #[inline(never)]
    fn clause_lambda(&mut self, start: u32, kind: MatchKind) -> Result<()> {
        // The first alternative's pattern count and first pattern.
        let mut first: Option<(usize, (u32, u32))> = None;
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
            let arm = self.mark();
            let bar = self.bump().span;
            let patterns = self.mark();
            let mut n = 1;
            self.alt_pattern()?;
            let first_pattern = (patterns, self.mark());
            while self.eat(&Tok::Comma) {
                self.alt_pattern()?;
                n += 1;
            }
            match first {
                Some((m, pattern)) if m != n => {
                    return Err(error(
                        bar.to(self.prev_span()),
                        format!(
                            "this alternative has {n} pattern{}, but the first has {m}",
                            if n == 1 { "" } else { "s" },
                        ),
                    )
                    .with_label(
                        self.lowered_pattern_span(pattern),
                        format!("the first alternative has {m}"),
                    )
                    .with_note(
                        "every alternative of a clause lambda has one pattern for each parameter",
                    )
                    .into());
                }
                Some(_) => {}
                None => first = Some((n, first_pattern)),
            }
            let absurd = self.absurd_since(patterns);
            self.guard()?;
            if kind == MatchKind::ClauseMatches && self.peek() != Some(&Tok::FatArrow) {
            } else if kind == MatchKind::Clause {
                self.arm_body(absurd, "`=>`")?;
            } else {
                self.expect_fat_arrow("`=>`")?;
                self.expr()?;
            }
            self.node(arm, NodeKind::Arm);
        }
        if first.is_none() {
            return Err(self.unexpected("`|` and an alternative").into());
        }
        self.node(start, NodeKind::ClauseLambda);
        Ok(())
    }

    /// A pattern of a `match` alternative: what may stand inside brackets in
    /// an equation, so a constructor's arguments need no parentheses
    /// (`Cons x Nil`); or several, `p | q`.
    fn alt_pattern(&mut self) -> Result<()> {
        let start = self.mark();
        self.alt_pattern_one()?;
        self.alternatives(start, Self::alt_pattern_one)
    }

    fn alt_pattern_one(&mut self) -> Result<()> {
        if self.ctor_ahead() {
            let start = self.mark();
            self.ctor_name()?;
            self.ctor_args(start, |t| {
                matches!(
                    t,
                    Some(
                        Tok::Comma
                            | Tok::Arrow
                            | Tok::FatArrow
                            | Tok::Pipe
                            | Tok::KwIf
                            | Tok::PlusPlus
                            // After the last pattern of a `matches | A` in brackets.
                            | Tok::RParen
                            | Tok::RBracket
                            | Tok::RBrace
                    ) | None
                )
            })?;
            return self.pattern_append(start, Self::alt_pattern_one);
        }
        self.tuple_component()
    }

    /// After a pattern from token `start`, `++ q`: a text pattern's fixed
    /// start and the pattern for the rest (docs/proposals/text-patterns.md
    /// §4.2), with `q` parsed by `next`, so that `"a" ++ "b" ++ rest` nests
    /// to the right as the expression does. Only a text literal can be the
    /// start: a suffix or a middle part would need a search.
    fn pattern_append(&mut self, start: u32, next: fn(&mut Self) -> Result<()>) -> Result<()> {
        if self.peek() != Some(&Tok::PlusPlus) {
            return Ok(());
        }
        let literal = self.pos == start as usize + 1
            && matches!(self.tokens[start as usize].tok, Tok::Str(_));
        if !literal {
            let left = self.tokens[start as usize]
                .span
                .to(self.tokens[self.pos - 1].span);
            let d = Diagnostic::error(
                "E-TEXT-PATTERN",
                "a text pattern can only take a fixed start",
            )
            .with_label(
                left,
                "only a text literal can stand before `++` in a pattern",
            );
            // `Some "a" ++ rest` groups as `(Some "a") ++ rest`, as the
            // expression does.
            if matches!(self.tokens[self.pos - 1].tok, Tok::Str(_))
                && matches!(
                    self.tokens[start as usize].tok,
                    Tok::Upper(_) | Tok::Lower(_)
                )
            {
                let ctor = self.text_at(start);
                return Err(d
                    .with_note(format!(
                        "a constructor's arguments end before `++`, as in an expression; to match \
                         an argument of `{ctor}` that starts with a text, write it in brackets: \
                         `{ctor} (\"…\" ++ rest)`"
                    ))
                    .into());
            }
            return Err(d
                .with_note(
                    "a pattern can match a text that starts a certain way, `\"--\" ++ rest`; to \
                     match one that ends a certain way or has a part in the middle, bind it to a \
                     variable and test it in a guard: `| t if t.endsWith \".sw\" => …`, or \
                     take it apart with `Text.stripSuffix` or `Text.splitOn`",
                )
                .into());
        }
        self.bump();
        next(self)?;
        self.node(start, NodeKind::PatternAppend);
        Ok(())
    }

    /// Whether a `|` between alternatives of an or-pattern is next: one on
    /// the same line, since a `|` that starts a line starts the next arm.
    fn or_bar_ahead(&self) -> bool {
        self.peek() == Some(&Tok::Pipe) && !self.tokens[self.pos].line_start
    }

    /// After a pattern from token `start`, `| q | …`, each further
    /// alternative parsed by `next`; nothing more if no `|` follows. (That
    /// no alternative binds a variable is the lowering's check.)
    fn alternatives(&mut self, start: u32, next: fn(&mut Self) -> Result<()>) -> Result<()> {
        if !self.or_bar_ahead() {
            return Ok(());
        }
        while self.or_bar_ahead() {
            self.bump();
            next(self)?;
        }
        self.node(start, NodeKind::PatternOr);
        Ok(())
    }

    /// `x (a, b) => body`, once `lambda_ahead` has said this is one, from
    /// token `start`, as a `kind`: a `Lambda`, or an `Exists` whose
    /// keyword `start` is. Out of line, so that `expr_inline`, which every
    /// nested expression recurses through, keeps a small stack frame.
    #[inline(never)]
    fn lambda(&mut self, start: u32, kind: NodeKind) -> Result<()> {
        let mut params = 0;
        loop {
            let first = self.mark();
            // A parameter that is a name is its token, and a pattern is its
            // own node; the others are `LambdaParam`s.
            match self.peek() {
                Some(Tok::Lower(_)) => {
                    self.lower("a name")?;
                }
                Some(Tok::Underscore) => {
                    self.bump();
                }
                // `(x: A)`, `(x y: A)`: parameters with a written type, as in
                // a definition's header.
                Some(Tok::LParen) if self.annotated_param_ahead() => {
                    if let Some(default) = self.header_param_parts()?.default {
                        return Err(lambda_default(self.lowered_span(default)).into());
                    }
                    self.node(first, NodeKind::LambdaParam);
                }
                // `[a: Type]`, `[auto h: P]`, `[auto P]`: implicit and auto
                // parameters, as in a header (§4.3, D91).
                Some(Tok::LBracket)
                    if self.implicit_group_at(self.pos) || self.nameless_auto_at(self.pos) =>
                {
                    self.header_param_parts()?;
                    self.node(first, NodeKind::LambdaParam);
                }
                // `((a, b): A)`: a pattern with a written type.
                Some(Tok::LParen) if self.annotated_pattern_ahead() => {
                    self.bump();
                    self.pattern()?;
                    self.expect(Tok::Colon, "`:`")?;
                    self.binder_type()?;
                    self.expect(Tok::RParen, "`)`")?;
                    self.node(first, NodeKind::PatternTyped);
                }
                Some(Tok::LParen | Tok::LBrace) => self.pattern()?,
                _ => break,
            }
            params += 1;
        }
        if params == 0 {
            return Err(self.unexpected("a parameter name").into());
        }
        self.expect_fat_arrow("`=>`")?;
        self.expr()?;
        self.node(start, kind);
        Ok(())
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

    /// Whether a `(` here opens a pattern with a written type, `((a, b): A)`:
    /// a bracketed group with a `:` at its top level and no comma before it.
    fn annotated_pattern_ahead(&self) -> bool {
        let close = match self.matching[self.pos] {
            NO_PARTNER => return false,
            close => close as usize,
        };
        let mut i = self.pos + 1;
        while i < close {
            match &self.tokens[i].tok {
                Tok::Colon => return i > self.pos + 1,
                Tok::Comma => return false,
                Tok::LParen | Tok::LBracket | Tok::LBrace => match self.matching[i] {
                    NO_PARTNER => return false,
                    inner => i = inner as usize + 1,
                },
                _ => i += 1,
            }
        }
        false
    }

    /// `if c then a else b`, after the `if`. Its own function, so the stack
    /// frame of the parser's recursive functions stays small (the nesting
    /// limit is measured in stack).
    #[inline(never)]
    fn if_expr(&mut self, start: u32) -> Result<()> {
        // `then` and `else` may start a line, as long as it's indented at
        // least as far as the line `if` is on (not the line its binder is
        // on, when a comment puts that on a later line).
        let indent = self.line_indent(self.pos - 1);
        // `if h : P then …` binds a proof; `if c then …` tests a `Bool`.
        let binder =
            if matches!(self.peek(), Some(Tok::Lower(_))) && self.peek_at(1) == Some(&Tok::Colon) {
                let name = self.lower("a name")?;
                self.bump();
                Some(name_text(name))
            } else {
                None
            };
        self.expr()?;
        let bool_test = self.peek() == Some(&Tok::Equals);
        self.expect_keyword(Tok::KwThen, "`then`", indent)
            .map_err(|e| match binder {
                Some(h) if bool_test => e
                    .with_note(format!(
                        "in `if {h}: …` the guard is already a proposition: write `if {h}: a < b \
                         then` for `a < b`, without `= True`"
                    ))
                    .into(),
                _ => e,
            })?;
        self.expr()?;
        self.expect_keyword(Tok::KwElse, "`else`", indent)?;
        self.expr()?;
        self.node(start, NodeKind::If);
        Ok(())
    }

    /// `calc e0` and its steps, one per line: `_ = e1 := proof`, `_ <= e2`
    /// (no proof: closed by computation). The steps line up, and are
    /// indented past the line `calc` is on.
    #[inline(never)]
    fn calc_expr(&mut self, start: u32) -> Result<()> {
        let indent = self.line_indent(self.pos - 1);
        self.modes.calc_depth += 1;
        let result = self.calc_body(start, indent);
        self.modes.calc_depth -= 1;
        result
    }

    /// A `calc` expression: above the relations, so `a || b`, `a && b` and
    /// `xs |> f` need no parentheses.
    fn calc_operand(&mut self) -> Result<()> {
        let start = self.mark();
        self.range_expr()?;
        if self.at_pipe() {
            self.pipe_chain(start)?;
        }
        if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
            self.logic_chain(start)?;
        }
        Ok(())
    }

    #[inline(never)]
    fn calc_body(&mut self, start: u32, indent: u32) -> Result<()> {
        self.calc_operand()?;
        if matches!(
            self.peek(),
            Some(Tok::Equals | Tok::Le | Tok::Lt | Tok::Gt | Tok::Ge | Tok::NotEq | Tok::EqEq)
        ) {
            return Err(error(
                self.here(),
                "`calc` starts with one expression; each relation goes on a line of its own",
            )
            .with_note("write `calc a` and then, indented below it, `_ = b := proof`")
            .into());
        }
        let mut last = None;
        let mut column = None;
        // Whether any step is `<`/`<=` (`ascending`) or `>`/`>=` (`descending`).
        let mut ascending = false;
        let mut descending = false;
        while let Some(token) = self.tokens.get(self.pos)
            && token.tok == Tok::Underscore
            && token.line_start
            && token.column > indent
            && self.modes.limit.is_none_or(|limit| token.column > limit)
        {
            match column {
                None => column = Some(token.column),
                Some(c) if c != token.column => {
                    return Err(error(
                        token.span,
                        "this step isn't lined up with the steps above it",
                    )
                    .into());
                }
                Some(_) => {}
            }
            let underscore = self.mark();
            self.bump();
            match self.peek() {
                Some(Tok::Equals) => {}
                Some(Tok::Le | Tok::Lt) => ascending = true,
                Some(Tok::Ge | Tok::Gt) => descending = true,
                Some(Tok::NotEq | Tok::EqEq) => {
                    return Err(error(
                        self.here(),
                        "a `calc` step is `=`, `<=`, `<`, `>=` or `>`: other relations can't \
                         be chained",
                    )
                    .into());
                }
                _ => {
                    return Err(self
                        .unexpected("`=`, `<=`, `<`, `>=` or `>` after `_`")
                        .into());
                }
            }
            self.bump();
            self.calc_operand()?;
            if self.eat(&Tok::ColonEq) {
                self.expr()?;
            }
            last = Some(self.prev_span());
            self.node(underscore, NodeKind::CalcStep);
        }
        let Some(last) = last else {
            return Err(self
                .unexpected("a step `_ = e` on the next line, indented past `calc`")
                .with_note("a `calc` needs at least one step")
                .into());
        };
        self.node(start, NodeKind::Calc);
        if descending && ascending {
            return Err(Diagnostic::error(
                "E-CALC-RELATION",
                "a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`",
            )
            .with_label(
                self.tokens[start as usize].span.to(last),
                "this chain has steps in both directions",
            )
            .with_note(
                "write the steps all with `<`/`<=` or all with `>`/`>=` (`=` goes with either)",
            )
            .into());
        }
        Ok(())
    }

    /// `rewrite p, <- q at h then t`, after `rewrite`: rules separated by
    /// commas, each optionally `<-`, then (optionally) `at` and the target,
    /// then (optionally) `then` and the body. `at` and `then` are only
    /// special where a rule could end: outside brackets, inside a rule (and
    /// `then` inside the target).
    #[inline(never)]
    fn rewrite_expr(&mut self, start: u32) -> Result<()> {
        let saved = (self.modes.rewrite_rule.take(), self.modes.rewrite_at);
        let result = self.rewrite_body(start);
        (self.modes.rewrite_rule, self.modes.rewrite_at) = saved;
        result
    }

    #[inline(never)]
    fn rewrite_body(&mut self, start: u32) -> Result<()> {
        let column = self.tokens[self.pos - 1].column;
        // `rewrite repeatedly [r1, r2]`: `repeatedly` is a word only here,
        // before a `[`, so a rule called `repeatedly` still reads as one.
        if matches!(self.peek(), Some(Tok::Lower(w)) if w == "repeatedly")
            && self.peek_at(1) == Some(&Tok::LBracket)
        {
            self.bump();
            self.repeated_rules()?;
            self.rewrite_target()?;
            return self.rewrite_then(start, column);
        }
        loop {
            let rule_start = self.mark();
            let reverse = self.peek() == Some(&Tok::Lt)
                && self.peek_at(1) == Some(&Tok::Minus)
                && self.tokens[self.pos].span.end == self.tokens[self.pos + 1].span.start;
            if reverse {
                self.bump();
                self.bump();
            }
            self.modes.rewrite_rule = Some(self.pos);
            self.modes.rewrite_at = true;
            let proof = self.append_expr();
            self.modes.rewrite_rule = None;
            proof?;
            self.node(rule_start, NodeKind::RewriteRule);
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.rewrite_target()?;
        self.rewrite_then(start, column)
    }

    /// A `rewrite`'s optional `at` and target, after its rules.
    fn rewrite_target(&mut self) -> Result<()> {
        if matches!(self.peek(), Some(Tok::Lower(x)) if x == "at") {
            let at = self.bump().span;
            if self
                .peek()
                .is_none_or(|t| matches!(t, Tok::KwThen | Tok::KwIn))
                || self.is_stop(self.pos)
            {
                return Err(rewrite_at_without_target(at).into());
            }
            self.modes.rewrite_rule = Some(self.pos);
            self.modes.rewrite_at = false;
            let target = self.append_expr();
            self.modes.rewrite_rule = None;
            target?;
        }
        Ok(())
    }

    /// The rules of `rewrite repeatedly [r1, <- r2]`, from the `[`: each a
    /// rule as in `rewrite`, `<-` allowed, in a `RewriteRules` node.
    fn repeated_rules(&mut self) -> Result<()> {
        let open = self.mark();
        self.bump();
        if self.peek() == Some(&Tok::RBracket) {
            return Err(error(
                self.here(),
                "`rewrite repeatedly` needs at least one rule between its brackets",
            )
            .into());
        }
        loop {
            let rule_start = self.mark();
            let reverse = self.peek() == Some(&Tok::Lt)
                && self.peek_at(1) == Some(&Tok::Minus)
                && self.tokens[self.pos].span.end == self.tokens[self.pos + 1].span.start;
            if reverse {
                self.bump();
                self.bump();
            }
            self.expr()?;
            self.node(rule_start, NodeKind::RewriteRule);
            if !self.eat(&Tok::Comma) || self.peek() == Some(&Tok::RBracket) {
                break;
            }
        }
        self.close_bracket(open, Tok::RBracket, "`,` or `]`", NodeKind::RewriteRules)
    }

    /// A `rewrite`'s optional `then t`, after its rules (and target).
    fn rewrite_then(&mut self, start: u32, column: u32) -> Result<()> {
        // `then` may also start a line of its own, at the `rewrite`'s column
        // or right of it, where the enclosing block's column would end the
        // expression: no statement starts with `then`.
        let own_line = |tok: Tok| {
            self.tokens
                .get(self.pos)
                .is_some_and(|t| t.tok == tok && t.line_start && t.column >= column)
        };
        if self.peek() == Some(&Tok::KwIn) || own_line(Tok::KwIn) {
            return Err(old_in(self.tokens[self.pos].span, "rewrite").into());
        }
        if self.peek() == Some(&Tok::KwThen) || own_line(Tok::KwThen) {
            self.bump();
            self.then_body()?;
        }
        self.node(start, NodeKind::Rewrite);
        Ok(())
    }

    /// The body after a `then` that ends its line: the lines that follow it
    /// at the enclosing block's own column are the body (a block of its
    /// own), not new statements of the block, since a `rewrite … then` with
    /// nothing after it can't be a statement of its own. Otherwise an
    /// ordinary expression (SW-3733).
    fn then_body(&mut self) -> Result<()> {
        if let Some(token) = self.tokens.get(self.pos)
            && token.line_start
            && self.pos > 0
            && self.modes.allow != Some(self.pos)
            && !self.ends_construct(self.pos)
            && self.modes.limit == Some(token.column)
        {
            return self.block(token.column, true);
        }
        self.expr()
    }

    /// `cases` or `cases then t`, after the `cases` (docs/proposals/simp.md
    /// §5.1). As for `rewrite`, the body runs to the end of the expression.
    fn cases_expr(&mut self, start: u32) -> Result<()> {
        if self.peek() == Some(&Tok::KwIn) {
            return Err(old_in(self.tokens[self.pos].span, "cases").into());
        }
        if self.peek() != Some(&Tok::KwThen) {
            return Ok(());
        }
        self.bump();
        self.then_body()?;
        self.node(start, NodeKind::Cases);
        Ok(())
    }

    /// `byWalking [items] then t`, at the word (docs/syntax.md,
    /// "byWalking"): the items are a list's (`[]` too), and the body, as
    /// for `rewrite`, runs to the end of the expression. The word is a word
    /// only before a `[`, so a name `byWalking` elsewhere stays a name.
    #[inline(never)]
    fn walk_expr(&mut self, start: u32) -> Result<()> {
        let column = self.tokens[self.pos].column;
        self.bump();
        self.fact_list()?;
        let own_line = self
            .tokens
            .get(self.pos)
            .is_some_and(|t| t.tok == Tok::KwThen && t.line_start && t.column >= column);
        if self.peek() == Some(&Tok::KwThen) || own_line {
            self.bump();
            self.then_body()?;
        }
        self.node(start, NodeKind::Walk);
        Ok(())
    }

    /// `(x : A) -> B` or `[x : A] -> B`. Out of line, as `if_expr` is.
    #[inline(never)]
    fn pi_expr(&mut self, start: u32, implicit: bool) -> Result<()> {
        let binder = if implicit {
            self.implicit_binder()?
        } else {
            self.binder()?
        };
        if let Some(first) = binder.attribute {
            return Err(misplaced_attributes(&first, "a function type's parameter").into());
        }
        self.expect(Tok::Arrow, "`->`")?;
        self.result_type()?;
        self.node(start, NodeKind::FunctionType);
        Ok(())
    }

    /// `let x := e; body` as an expression. Out of line, as the others are.
    #[inline(never)]
    fn expression_let(&mut self) -> Result<()> {
        let start = self.mark();
        self.let_statement()?;
        self.let_body()?;
        self.node(start, NodeKind::LetExpr);
        Ok(())
    }

    fn expr_inline(&mut self) -> Result<()> {
        let start = self.mark();
        if self.eat(&Tok::KwHandle) {
            return self.handle(start);
        }
        if self.peek() == Some(&Tok::KwLet) {
            return self.expression_let();
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
        if matches!(self.peek(), Some(Tok::Lower(w)) if w == crate::ast::WALK_WORD)
            && self.peek_at(1) == Some(&Tok::LBracket)
        {
            return self.walk_expr(start);
        }
        if self.lambda_ahead()? {
            return self.lambda(start, NodeKind::Lambda);
        }
        if let Some(colon) = self.lambda_result_type_ahead() {
            return Err(lambda_result_type(self.tokens[colon].span).into());
        }
        if self.at_quantifier() {
            return self.quantifier();
        }
        if self.eat(&Tok::KwIf) {
            return self.if_expr(start);
        }
        let implicit = self.is_implicit_binder();
        if implicit || self.is_pi_binder() {
            return self.pi_expr(start, implicit);
        }
        // A method section at the start takes the expression up to a `->`
        // or `;` (D1192): its `Section` is marked here, around it.
        let section = self.peek() == Some(&Tok::Dot);
        if section {
            self.modes.section_head = Some(self.pos);
        }
        self.cmp_expr()?;
        if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
            self.logic_chain(start)?;
        }
        if self.peek() == Some(&Tok::Iff) {
            self.iff(start)?;
        }
        if section {
            self.node(start, NodeKind::Section);
        }
        if self.peek() == Some(&Tok::Arrow) {
            self.bump();
            self.result_type()?;
            self.node(start, NodeKind::Arrow);
            return Ok(());
        }
        if self.peek() == Some(&Tok::Semi) && self.sequence_ahead() {
            return self.sequence(start);
        }
        Ok(())
    }

    /// Whether the `;` at the current token continues a sequence `a; b`
    /// rather than ending a `let`'s value (`let x := a; body`): it does
    /// unless a `let`'s value is being parsed and the `;` isn't inside
    /// brackets opened since that `let`.
    #[inline(never)]
    fn sequence_ahead(&self) -> bool {
        let Some(start) = self.modes.let_value else {
            return true;
        };
        let depth = self.tokens[start..self.pos]
            .iter()
            .fold(0i64, |d, t| match t.tok {
                Tok::LBracket | Tok::LParen | Tok::LBrace => d + 1,
                Tok::RBracket | Tok::RParen | Tok::RBrace => d - 1,
                _ => d,
            });
        depth > 0
    }

    /// `a; b`, after `a`, which starts at token `start`: run `a`, then give
    /// `b`'s value (SW-888, D1700).
    /// The same tree as the block lines `a` and `b`, so `a; b; c` is
    /// `Seq(a, Seq(b, c))` and `a; let x := e; b` binds `x` for `b`. The
    /// rest runs as far as an expression can, as an expression `let`'s body
    /// does.
    #[inline(never)]
    fn sequence(&mut self, start: u32) -> Result<()> {
        let semi = self.bump().span;
        let at_end = self
            .peek()
            .is_none_or(|t| matches!(t, Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Comma));
        if at_end {
            let message =
                "`;` needs an expression after it: `(a; b)` runs `a`, then gives `b`'s value";
            // The next line is the block's next line, which needs no `;`.
            let note = if self.tokens.get(self.pos).is_some_and(|t| t.line_start) {
                "the next line starts a new line of the block: leave out the `;` at the end of this one"
            } else {
                "`;` goes between two expressions: leave out a `;` at the end"
            };
            return Err(error(semi, message).with_note(note).into());
        }
        self.expr()?;
        self.node(start, NodeKind::Seq);
        Ok(())
    }

    /// `p <-> q`, after `p`, which starts at token `start` (D1202). Looser
    /// than `&&` and `||`, tighter than `->`, and not associative, as in
    /// Rocq. The right
    /// side may be an `exists` or a `forall`. Out of line, as `logic_chain`
    /// is.
    #[inline(never)]
    fn iff(&mut self, start: u32) -> Result<()> {
        self.bump();
        if self.at_quantifier() {
            self.quantifier()?;
        } else {
            let right = self.mark();
            self.cmp_expr()?;
            if matches!(self.peek(), Some(Tok::AndAnd | Tok::OrOr)) {
                self.logic_chain(right)?;
            }
        }
        if self.peek() == Some(&Tok::Iff) {
            return Err(Diagnostic::error("E-PARSE", "`<->` doesn't chain")
                .with_label(self.here(), "a second `<->`")
                .with_note("`p <-> q <-> r` could mean either grouping: add brackets")
                .into());
        }
        self.node(start, NodeKind::Iff);
        Ok(())
    }

    /// `exists (x: T) => P`, at the `exists`: `Exists T ((x: T) => P)`
    /// (D1203). What follows is a lambda, its type left out where it can be
    /// inferred (`exists k => P k`); several parameters nest, so
    /// `exists (a b: Nat) => P` is `exists (a: Nat) => exists (b: Nat) => P`.
    #[inline(never)]
    fn exists_expr(&mut self) -> Result<()> {
        let keyword = self.mark();
        self.bump();
        if !self.lambda_ahead()? {
            return Err(self
                .unexpected("a parameter and `=>` after `exists`")
                .with_note("\"there exists\" is written `exists (x: T) => P`")
                .into());
        }
        self.lambda(keyword, NodeKind::Exists)
    }

    /// Whether an `exists` or a `forall` starts here.
    fn at_quantifier(&self) -> bool {
        matches!(self.peek(), Some(Tok::KwExists | Tok::KwForall))
    }

    /// `exists …` or `forall …`, at the keyword.
    #[inline(never)]
    fn quantifier(&mut self) -> Result<()> {
        if self.peek() == Some(&Tok::KwForall) {
            self.forall_expr()
        } else {
            self.exists_expr()
        }
    }

    /// `forall (x: T) => P`, at the `forall`: the function type `(x: T) ->
    /// P`, the same term (D3458). The parameters are a lambda's without
    /// patterns: `(x y: T)`, `[a: Type]`, `[auto h: P]`, `[auto P]`, or a
    /// bare name, its type inferred (`forall n => n + 0 = n`). Each group is
    /// one function type, as `(x y: T) -> P` is. The body runs to the end of
    /// the expression, as an `exists`'s does.
    #[inline(never)]
    fn forall_expr(&mut self) -> Result<()> {
        let written = self.spelled(&self.tokens[self.pos]);
        let keyword = self.mark();
        self.bump();
        let mut groups = 0;
        loop {
            let first = self.mark();
            match self.peek() {
                Some(Tok::Lower(w)) if !w.contains('.') => {
                    self.lower("a name")?;
                }
                Some(Tok::Underscore) => {
                    self.bump();
                }
                Some(Tok::LParen) if self.annotated_param_ahead() => {
                    if let Some(default) = self.header_param_parts()?.default {
                        return Err(error(
                            self.lowered_span(default),
                            "a `forall` parameter can't have a default",
                        )
                        .with_note(
                            "defaults belong to a definition's parameters: `def f (x: Nat := 0)`",
                        )
                        .into());
                    }
                    self.node(first, NodeKind::LambdaParam);
                }
                Some(Tok::LBracket)
                    if self.implicit_group_at(self.pos) || self.nameless_auto_at(self.pos) =>
                {
                    self.header_param_parts()?;
                    self.node(first, NodeKind::LambdaParam);
                }
                _ => break,
            }
            groups += 1;
        }
        if groups == 0 || self.peek() != Some(&Tok::FatArrow) {
            let expected = if groups == 0 {
                format!("a parameter after {written}")
            } else {
                format!("`=>` after the parameters of {written}")
            };
            let note = if self.peek() == Some(&Tok::Comma) {
                "\"for all\" is written `forall (x: T) => P` or `∀ (x: T) => P`: `=>` follows \
                 the parameters, not `,`"
            } else {
                "\"for all\" is written `forall (x: T) => P` or `∀ (x: T) => P`: its \
                 parameters are names or bracketed groups, `(x y: T)` or `[a: Type]`, then `=>`"
            };
            return Err(self.unexpected(&expected).with_note(note).into());
        }
        self.bump();
        self.expr()?;
        self.node(keyword, NodeKind::Forall);
        Ok(())
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

    /// `[x y : A]`, or `[auto x : P]`, or `[auto P]`.
    fn implicit_binder(&mut self) -> Result<BinderRead> {
        let mark = self.mark();
        let binder = self.implicit_binder_parts()?;
        self.node(mark, NodeKind::Binder);
        Ok(binder)
    }

    fn implicit_binder_parts(&mut self) -> Result<BinderRead> {
        if self.nameless_auto_at(self.pos) {
            self.bump();
            let auto = self.bump().span;
            let ty = self.mark();
            self.expr()?;
            let ty = (ty, self.mark());
            self.expect(Tok::RBracket, "`]`")?;
            return Ok(BinderRead {
                attribute: None,
                auto: true,
                nameless: true,
                first_name: auto,
                ty,
                default: None,
            });
        }
        self.expect(Tok::LBracket, "`[`")?;
        let attribute = self.attributes()?;
        let first = self.lower("a name")?;
        let mut names = 1;
        let mut second = None;
        while let Some(Tok::Lower(_)) = self.peek() {
            let name = self.lower("a name")?;
            second.get_or_insert(name.span);
            names += 1;
        }
        // `auto` is only special as the first word of a binder with names after it.
        let auto = names > 1 && name_text(first) == "auto";
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.mark();
        self.binder_type()?;
        let ty = (ty, self.mark());
        self.expect(Tok::RBracket, "`]`")?;
        Ok(BinderRead {
            attribute,
            auto,
            nameless: false,
            first_name: if auto {
                second.unwrap_or(first.span)
            } else {
                first.span
            },
            ty,
            default: None,
        })
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
    /// later in the expression, before the bracket around it closes. Nothing
    /// is consumed.
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
                // A closer here ends the bracket the expression is in, so a
                // `=>` after it belongs to an enclosing lambda.
                Tok::ColonEq | Tok::RParen | Tok::RBracket | Tok::RBrace => return None,
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
    /// tighter than `||`, both grouping to the right, so `a || b && c || d`
    /// is `a || ((b && c) || d)`. The first operand, from token `start`, has
    /// been read. The operands are read in a loop, so a chain costs one
    /// stack frame, not one per operator, and its `Binary` nodes are marked
    /// as they finish: a conjunction's at the `||` after it or at the end,
    /// inner first, then the disjunctions', inner first. Every expression is
    /// parsed by the caller, and this is only entered at a `&&` or `||`, out
    /// of line, so the frames nested expressions pile up (and so how deeply
    /// they can nest) stay as they were: the `check-nested-parens` benchmark
    /// fails otherwise.
    #[inline(never)]
    fn logic_chain(&mut self, start: u32) -> Result<()> {
        // Where each disjunct starts, and each operand of the last.
        let mut disjuncts = vec![start];
        let mut operands = vec![start];
        while let Some(Tok::AndAnd | Tok::OrOr) = self.peek() {
            let or = self.peek() == Some(&Tok::OrOr);
            if or {
                self.mark_right_nested(&operands);
                operands.clear();
            }
            self.bump();
            operands.push(self.mark());
            if or {
                disjuncts.push(self.mark());
            }
            // `p && exists (x: T) => q`: the `exists` takes the rest, as
            // does a `forall`.
            if self.at_quantifier() {
                self.quantifier()?;
            } else {
                self.cmp_expr()?;
            }
        }
        self.mark_right_nested(&operands);
        self.mark_right_nested(&disjuncts);
        Ok(())
    }

    /// The `Binary` nodes of operands from tokens `starts` that end here,
    /// grouped to the right: one from each start but the last, the last
    /// start's first, since it finishes first.
    pub(super) fn mark_right_nested(&mut self, starts: &[u32]) {
        for &start in starts[..starts.len() - 1].iter().rev() {
            self.node(start, NodeKind::Binary);
        }
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

    /// `x |> f a |> g`, after `x`, which starts at token `start`: tighter
    /// than comparisons, `in`, `&&` and `||`,
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
    fn pipe_chain(&mut self, start: u32) -> Result<()> {
        let indent = self.line_indent(self.written_start(start));
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
            let operand = self.mark();
            if self.lambda_ahead()? {
                self.lambda(operand, NodeKind::Lambda)?;
            } else {
                // A method section takes the operand it starts, as it
                // takes an expression (`expr_inline`).
                let section = self.peek() == Some(&Tok::Dot);
                if section {
                    self.modes.section_head = Some(self.pos);
                }
                self.append_expr()?;
                if section {
                    self.node(operand, NodeKind::Section);
                }
            }
            self.node(start, NodeKind::Pipe);
        }
        Ok(())
    }

    /// The token where the compiler's tree's span of the operand from token
    /// `start` to the last token read starts: its first token, or inside
    /// brackets it starts with (`(f x) |> g`'s operand is `f x`). Only which
    /// line it is on matters: when the brackets before it don't start a
    /// line, that of `start`.
    fn written_start(&self, start: u32) -> usize {
        let mut i = start as usize;
        while self.tokens[i].tok == Tok::LParen && i + 1 < self.pos {
            i += 1;
            if self.tokens[i].line_start {
                let span = self.lowered_span((start, self.pos as u32));
                return self.tokens.partition_point(|t| t.span.start < span.start);
            }
        }
        start as usize
    }

    /// A `match` starting an expression, then a pipeline it feeds: a `|>`
    /// line left of the last alternative's line (which would otherwise
    /// take it), but at least as far right as the `match`'s line.
    #[inline(never)]
    fn match_piped(&mut self, start: u32) -> Result<()> {
        self.match_expr(start)?;
        if self.at_pipe() {
            self.pipe_chain(start)?;
        }
        Ok(())
    }

    /// `a = b`, `a != b`, `a == b`, `a < b`, `a <= b`, `a > b`, `a >= b`: not
    /// associative, except that `<`/`<=` chain together, as do `>`/`>=`
    /// (`lo <= x < hi`). Each operand may be a pipeline.
    fn cmp_expr(&mut self) -> Result<()> {
        let lhs_start = self.pos;
        self.range_expr()?;
        if self.at_pipe() {
            self.pipe_chain(lhs_start as u32)?;
        }
        if matches!(self.peek(), Some(Tok::KwIn | Tok::NotIn)) {
            return self.membership(lhs_start);
        }
        let descending = match self.peek() {
            Some(Tok::Equals | Tok::NotEq | Tok::EqEq | Tok::Lt | Tok::Le) => false,
            Some(Tok::Gt | Tok::Ge) => true,
            _ => return Ok(()),
        };
        let first_tok = self.peek();
        let first_op = self.mark();
        self.bump();
        // `a = if c then x else y`: the `if` on the right runs to the end of
        // the expression, as it does anywhere else.
        if self.peek() == Some(&Tok::KwIf) {
            let start = self.mark();
            self.bump();
            self.if_expr(start)?;
            self.node(lhs_start as u32, NodeKind::Binary);
            return Ok(());
        }
        let second = self.mark();
        self.range_expr()?;
        if self.at_pipe() {
            self.pipe_chain(second)?;
        }
        if !matches!(
            self.peek(),
            Some(
                Tok::Equals
                    | Tok::NotEq
                    | Tok::EqEq
                    | Tok::Lt
                    | Tok::Le
                    | Tok::Gt
                    | Tok::Ge
                    | Tok::KwIn
                    | Tok::NotIn
            )
        ) {
            self.node(lhs_start as u32, NodeKind::Binary);
            return Ok(());
        }
        let equality = matches!(first_tok, Some(Tok::Equals | Tok::NotEq | Tok::EqEq));
        self.comparison_chain(lhs_start as u32, first_op, second, equality, descending)
    }

    /// The rest of `a <= b < c …`, after `a <= b`, where `a` starts at
    /// token `first_start`, its operator is token `first_op` and `b` starts
    /// at `second` (SW-1339, D2386).
    /// `equality` if the first operator is `=`, `!=` or `==`, which can't
    /// start a chain; `descending` if it is `>` or `>=`.
    #[inline(never)]
    fn comparison_chain(
        &mut self,
        first_start: u32,
        first_op: u32,
        second: u32,
        equality: bool,
        descending: bool,
    ) -> Result<()> {
        let first_symbol = written(Some(&self.tokens[first_op as usize].tok));
        if equality {
            let next = written(self.peek());
            return Err(chain_error(
                (
                    self.tokens[first_op as usize].span,
                    "this comparison can't start a chain",
                ),
                (self.here(), "so this one can't follow it"),
                format!("`{first_symbol}` can't be part of a chain of comparisons"),
                format!(
                    "for now only `<` and `<=`, or `>` and `>=`, chain; write the comparisons \
                     separately, joined with `&&`: `a {first_symbol} b && b {next} c`"
                ),
            ));
        }
        // Each operand's tokens, for messages.
        let mut operands = vec![(first_start, first_op), (second, self.mark())];
        let mut last_symbol = first_symbol;
        loop {
            let symbol = written(self.peek());
            let flip = match self.peek() {
                Some(Tok::Lt | Tok::Le) => false,
                Some(Tok::Gt | Tok::Ge) => true,
                Some(Tok::Equals | Tok::EqEq) if matches!(self.peek_at(1), Some(Tok::Upper(b)) if b == "True" || b == "False") =>
                {
                    let (a, b) = (
                        self.operand_text(operands[0], "a"),
                        self.operand_text(operands[1], "b"),
                    );
                    return Err(chain_error(
                        (self.lowered_span(operands[0]), "this comparison"),
                        (self.here(), "isn't compared with a Bool"),
                        format!("`{symbol}` can't be part of a chain of comparisons"),
                        format!(
                            "a comparison is already a proposition (and decided where a `Bool` \
                             is wanted): write `{a} {last_symbol} {b}` for it, without `= True`, \
                             and `¬({a} {last_symbol} {b})` without `= False`"
                        ),
                    ));
                }
                Some(Tok::Equals | Tok::EqEq) => {
                    return Err(chain_error(
                        (self.lowered_span(operands[0]), "the chain starts here"),
                        (self.here(), "this operator can't continue it"),
                        format!("`{symbol}` can't be part of a chain of comparisons"),
                        format!(
                            "for now only `<` and `<=`, or `>` and `>=`, chain; write the \
                             comparisons separately, joined with `&&`: `a {last_symbol} b && b \
                             {symbol} c`"
                        ),
                    ));
                }
                Some(Tok::NotEq) => {
                    return Err(chain_error(
                        (self.lowered_span(operands[0]), "the chain starts here"),
                        (self.here(), "this operator can't continue it"),
                        "`!=` can't be part of a chain of comparisons".into(),
                        "`a != b != c` would not mean that all three differ; write the \
                         comparisons separately, joined with `&&`: `a != b && b != c`",
                    ));
                }
                Some(Tok::KwIn | Tok::NotIn) => {
                    return Err(chain_error(
                        (self.lowered_span(operands[0]), "the chain starts here"),
                        (self.here(), "this operator can't continue it"),
                        "`in` can't be part of a chain of comparisons".into(),
                        "write the comparison and the membership test separately, joined \
                         with `&&`: `a <= x && x in xs`",
                    ));
                }
                _ => break,
            };
            if flip != descending {
                let n = operands.len();
                let (before, left) = if n == 2 {
                    (
                        self.operand_text(operands[0], "a"),
                        self.operand_text(operands[1], "b"),
                    )
                } else {
                    (
                        self.operand_text(operands[n - 2], "a"),
                        self.operand_text(operands[n - 1], "b"),
                    )
                };
                let right = "c";
                return Err(chain_error(
                    (self.lowered_span(operands[0]), "the chain starts here"),
                    (self.here(), "this operator can't continue it"),
                    "a chain of comparisons goes one way: `<` and `<=` can't be mixed with \
                     `>` and `>=`"
                        .into(),
                    format!(
                        "write the comparisons separately, joined with `&&`: `{before} \
                         {last_symbol} {left} && {left} {symbol} {right}`, or turn the \
                         later ones round"
                    ),
                ));
            }
            last_symbol = symbol;
            self.bump();
            let operand = self.mark();
            self.range_expr()?;
            if self.at_pipe() {
                self.pipe_chain(operand)?;
            }
            operands.push((operand, self.mark()));
        }
        self.node(first_start, NodeKind::Chain);
        Ok(())
    }

    /// The operand in tokens `range` as a suggestion writes it: a name or a
    /// number as written, otherwise the placeholder `fallback`.
    #[cold]
    #[inline(never)]
    fn operand_text(&self, range: (u32, u32), fallback: &str) -> String {
        match self.lowered(range, false) {
            Some(Lowered::Expr(expr)) => match &expr {
                Expr::Var(name) => name.text.clone(),
                Expr::Num(n, _) => n.to_string(),
                _ => fallback.to_string(),
            },
            _ => fallback.to_string(),
        }
    }

    /// `x in c` or `x !in c`, after `x` (which starts at token `lhs_start`):
    /// at the level of `=`, not associative (D1201). `x !in c` is `!(x in c)`.
    #[inline(never)]
    fn membership(&mut self, lhs_start: usize) -> Result<()> {
        let op = self.bump().span;
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
            )
            .into());
        }
        let right = self.mark();
        self.range_expr()?;
        if self.at_pipe() {
            self.pipe_chain(right)?;
        }
        self.node(lhs_start as u32, NodeKind::Membership);
        Ok(())
    }

    /// `a ..< b`, `a ..= b`: a range, not associative, binding more loosely
    /// than `++` and more tightly than the comparisons and `|>`, so
    /// `0 ..< xs.length` and `x in 0 ..< n |> f` read as they look
    /// (docs/proposals/ranges.md §11).
    fn range_expr(&mut self) -> Result<()> {
        let start = self.mark();
        self.append_expr()?;
        match self.peek() {
            Some(Tok::DotDotLt | Tok::DotDotEq) => {}
            Some(Tok::DotDot) => return Err(self.bare_range().into()),
            _ => return Ok(()),
        }
        let first = self.bump().span;
        self.append_expr()?;
        self.node(start, NodeKind::Range);
        if let Some(Tok::DotDotLt | Tok::DotDotEq) = self.peek() {
            return Err(error(self.here(), "ranges don't chain")
                .with_label(first, "this range already has both ends")
                .with_note(
                    "`a ..< b ..< c` has no meaning; to join two ranges, write \
                     `[..a ..< b, ..c ..< d]`",
                )
                .into());
        }
        Ok(())
    }

    /// `E-PARSE` for `a .. b` or `a..b`: the forms of a range are `..<` and
    /// `..=`, and a spread is `..xs` after a comma.
    fn bare_range(&self) -> Diagnostic {
        let mut d = error(
            self.here(),
            "a range is `a ..< b` (up to, not including, `b`) or `a ..= b` (through `b`)",
        )
        .with_label(self.here(), "write `..<` or `..=` here");
        if self.modes.in_list {
            d = d.with_note(
                "inside brackets, a spread is `[2, ..n]` (with a comma), and a range needs no \
                 brackets: `2 ..< n` is already a list",
            );
        }
        d
    }

    /// `++`: right-associative, binding more loosely than `+`, so
    /// `"n = " ++ natToText (n + 1)` and `a ++ b ++ c` mean what they look like.
    fn append_expr(&mut self) -> Result<()> {
        self.deeper()?;
        let start = self.mark();
        self.add_expr()?;
        if self.peek() != Some(&Tok::PlusPlus) {
            return Ok(());
        }
        self.bump();
        self.append_expr()?;
        self.node(start, NodeKind::Binary);
        Ok(())
    }

    /// `+`, `-`: left-associative.
    fn add_expr(&mut self) -> Result<()> {
        let start = self.mark();
        self.mul_expr()?;
        while matches!(self.peek(), Some(Tok::Plus | Tok::Minus)) {
            self.bump();
            self.mul_expr()?;
            self.node(start, NodeKind::Binary);
        }
        Ok(())
    }

    /// `*`, `/`, `%`: left-associative, binding tighter than `+`.
    fn mul_expr(&mut self) -> Result<()> {
        let start = self.mark();
        self.unary()?;
        while matches!(self.peek(), Some(Tok::Star | Tok::Slash | Tok::Percent)) {
            self.bump();
            self.unary()?;
            self.node(start, NodeKind::Binary);
        }
        Ok(())
    }

    /// A prefix minus or `!` (which may repeat), tighter than `*` and looser
    /// than application and dots: `-x.abs` is `-(x.abs)`, `-f x` is `-(f x)`,
    /// `!xs.isEmpty` is `!(xs.isEmpty)`.
    fn unary(&mut self) -> Result<()> {
        // A `match` as an operand: `1 + match n with | …`. Its last
        // alternative's body takes whatever follows.
        let start = self.mark();
        if self.peek() == Some(&Tok::KwMatch) {
            self.bump();
            return self.match_expr(start);
        }
        if self.matches_bar_ahead() {
            self.bump();
            return self.clause_lambda(start, MatchKind::ClauseMatches);
        }
        // A negative numeral is one atom (D1474): `-1.abs` is `(-1).abs`.
        if self.peek() == Some(&Tok::Minus) && negative_numeral(self.tokens, self.pos) {
            return self.app();
        }
        if let Some(Tok::Minus | Tok::Bang) = self.peek() {
            self.deeper()?;
            self.bump();
            self.unary()?;
            self.node(start, NodeKind::Prefix);
            return Ok(());
        }
        self.app()
    }

    fn app(&mut self) -> Result<()> {
        let start = self.mark();
        // A section's arguments are its own: `.drop 1` is `x => x.drop 1`.
        // One that starts an expression is marked by its parser, around
        // more ([`Modes::section_head`]).
        let section =
            self.peek() == Some(&Tok::Dot) && self.modes.section_head != Some(start as usize);
        self.atom(true)?;
        // `f a b` is one `App` node, however many arguments.
        if self.starts_atom() {
            loop {
                if self.peek() == Some(&Tok::Dot) && self.tokens[self.pos].line_start {
                    return Err(self.section_line().into());
                }
                if matches!(self.peek(), Some(Tok::Upper(_)))
                    && self.peek_at(1) == Some(&Tok::LBrace)
                {
                    self.brace_argument()?;
                } else {
                    self.atom(false)?;
                }
                if !self.starts_atom() {
                    break;
                }
            }
            self.node(start, NodeKind::App);
        }
        // A section at the head takes the arguments: `.drop 1`.
        if section {
            self.node(start, NodeKind::Section);
        }
        if self.peek() == Some(&Tok::KwCases) && self.peek_at(1) == Some(&Tok::KwIn) {
            return Err(old_in(self.tokens[self.pos + 1].span, "cases").into());
        }
        if self.peek() == Some(&Tok::KwCases) && self.peek_at(1) == Some(&Tok::KwThen) {
            return Err(self.cases_then_argument().into());
        }
        Ok(())
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
                    | Tok::KwArithmetic
                    | Tok::KwAlgebra
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
            || self.argument_prefix_at(self.pos)
    }

    /// Whether the `-` at token `i` is an argument minus (`f -2`): the
    /// shared token test, and not at a statement stop, so a block line `-y`
    /// stays a new statement.
    fn argument_minus_at(&self, i: usize) -> bool {
        argument_minus(self.tokens, i) && !self.is_stop(i)
    }

    /// Whether the `-` or `!` at token `i` is an argument prefix (`f -2`,
    /// `f !x`), by the one shared test, and not at a statement stop, so a
    /// block line `!c` stays a new statement.
    fn argument_prefix_at(&self, i: usize) -> bool {
        argument_prefix(self.tokens, i) && !self.is_stop(i)
    }

    /// Whether the next token is a `cases` with no `then` after it, which
    /// is a whole term and so can be an argument, as `arithmetic` can.
    fn bare_cases(&self) -> bool {
        self.peek() == Some(&Tok::KwCases)
            && !matches!(self.peek_at(1), Some(Tok::KwThen | Tok::KwIn))
    }

    /// `f cases then t`: a `cases then` as an argument, whose body would take
    /// the rest of the line.
    #[inline(never)]
    fn cases_then_argument(&self) -> Diagnostic {
        error(
            self.tokens[self.pos].span,
            "`cases then …` as an argument needs brackets",
        )
        .with_note(
            "the body of `cases then` runs to the end of the expression, so as an argument \
             it's written `(cases then t)`",
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
    /// At the head of an application (`head`), an uppercase name followed by
    /// braces is `C { f = e, … }`: named construction or a record argument,
    /// as `C` is declared (`ctor_fields_expr`). As an argument (`f C { … }`)
    /// `app` takes it (`brace_argument`).
    fn atom(&mut self, head: bool) -> Result<()> {
        let section = self.peek() == Some(&Tok::Dot);
        let start = self.mark();
        let upper = matches!(self.peek(), Some(Tok::Upper(_)));
        // Whether what has been read is a name or a field, which `()`
        // written against it calls; in brackets, `(f)()`, it may be one.
        let paren = self.peek() == Some(&Tok::LParen);
        let mut callable = matches!(self.peek(), Some(Tok::Lower(_) | Tok::Upper(_) | Tok::Dot));
        self.atom_base(start)?;
        if upper && head && self.peek() == Some(&Tok::LBrace) {
            self.ctor_fields_expr()?;
            callable = false;
        }
        loop {
            if self.unit_call() && (callable || paren && self.callable_paren(start)) {
                let open = self.mark();
                self.bump();
                self.bump();
                self.node(open, NodeKind::Unit);
                self.node(start, NodeKind::App);
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
                }) if !text.contains('.') && self.peek_at(1).is_some() => (text, *span),
                _ => {
                    return Err(error(dot, "expected a field name after `.`")
                        .with_note("`.` is for field access, as in `p.name`")
                        .into());
                }
            };
            if self.prev_span().end != dot.start || dot.end != field.1.start {
                return Err(
                    error(dot, "field access is written without spaces around the `.`")
                        .with_note(format!("write `….{}`", field.0))
                        .into(),
                );
            }
            self.pos += 2;
            self.node(start, NodeKind::FieldAccess);
            callable = true;
        }
        // At the head of an application, `app` marks the section, around
        // the arguments.
        if section && !head {
            self.node(start, NodeKind::Section);
        }
        Ok(())
    }

    /// Whether the bracketed atom from token `first` to here holds a name or
    /// a field access, which `()` written against it calls: `(f)()`.
    #[cold]
    #[inline(never)]
    fn callable_paren(&self, first: u32) -> bool {
        let is_paren = |m: &&Mark| (m.start, m.end) == (first, self.pos as u32);
        if !self
            .marks
            .last()
            .is_some_and(|m| m.kind == NodeKind::Paren && is_paren(&m))
        {
            return false;
        }
        let (mut start, mut end) = (first + 1, self.pos as u32 - 1);
        loop {
            if end == start + 1 {
                return matches!(
                    self.tokens[start as usize].tok,
                    Tok::Lower(_) | Tok::Upper(_)
                );
            }
            let outer = self
                .marks
                .iter()
                .rev()
                .find(|m| (m.start, m.end) == (start, end))
                .map(|m| m.kind);
            match outer {
                Some(NodeKind::FieldAccess) => return true,
                Some(NodeKind::Paren) => (start, end) = (start + 1, end - 1),
                _ => return false,
            }
        }
    }

    /// `.name`, starting a method section: the start of its body.
    #[inline(never)]
    fn section_start(&mut self) -> Result<()> {
        let start = self.mark();
        let dot = self.bump().span;
        match self.tokens.get(self.pos) {
            Some(Token {
                tok: Tok::Lower(text),
                span,
                ..
            }) if span.start == dot.end && !text.contains('.') && self.peek().is_some() => {}
            _ => {
                return Err(error(dot, "expected a name right after `.`")
                    .with_note("`.name args` is a method section, the function `x => x.name args`")
                    .into());
            }
        }
        self.pos += 1;
        self.node(start, NodeKind::FieldAccess);
        Ok(())
    }

    /// `C { f = e, g }` at the head of an application: braces right after an
    /// uppercase name, already read. Whether they name `C`'s fields or are a
    /// record passed to it depends on how `C` is declared, which the
    /// elaborator knows (docs/proposals/brace-syntax-review.md §5).
    #[inline(never)]
    fn ctor_fields_expr(&mut self) -> Result<()> {
        let ctor = self.mark() - 1;
        self.record_expr()?;
        self.node(ctor, NodeKind::CtorFields);
        Ok(())
    }

    /// `f C { … }`: braces right after an uppercase name that is an argument
    /// of `f`.
    #[inline(never)]
    fn brace_argument(&mut self) -> Result<()> {
        let ctor = self.mark();
        self.atom_base(ctor)?;
        self.record_expr()?;
        self.node(ctor, NodeKind::CtorFields);
        Ok(())
    }

    /// `{ name = e, age }` (a literal; `age` is punned) or `{ base | age = e }`
    /// (an update). A literal's fields are in the order written.
    fn record_expr(&mut self) -> Result<()> {
        let start = self.mark();
        self.expect(Tok::LBrace, "`{`")?;
        self.record_body(start)
    }

    fn record_body(&mut self, start: u32) -> Result<()> {
        if self.peek() == Some(&Tok::RBrace) {
            self.bump();
            self.node(start, NodeKind::Record);
            return Ok(());
        }
        let literal = matches!(self.peek(), Some(Tok::Lower(_)))
            && matches!(
                self.peek_at(1),
                Some(Tok::Equals | Tok::Comma | Tok::RBrace)
            );
        // A `{` with its contents on the following lines is how a proof
        // block from another language is written: point that out rather
        // than only saying that a record update needs a `|`.
        let block = self
            .tokens
            .get(start as usize + 1)
            .is_some_and(|token| token.line_start);
        if !literal {
            self.expr()?;
            // The `{` at the end of a line: the contents ran out before the
            // `|` that starts an update's fields, so the brace is left open
            // ([`Self::close_bracket`]).
            if self.peek() != Some(&Tok::Pipe) && self.bracket_ran_out() {
                self.node(start, NodeKind::Error);
                return Ok(());
            }
            if self.peek() != Some(&Tok::Pipe) {
                let mut diagnostic = self.unexpected("`|` and the fields to update");
                if block {
                    diagnostic = diagnostic.with_note(
                        "braces make a record or a record update; a proof block is written by \
                         indentation, with each `let …` on its own line before the term",
                    );
                }
                return Err(diagnostic.into());
            }
            self.bump();
        }
        let mut fields = 0;
        loop {
            if self.peek() == Some(&Tok::RBrace) && fields > 0 {
                break;
            }
            let name = self.mark();
            self.lower("a field name")?;
            if self.eat(&Tok::Equals) {
                self.expr()?;
                self.node(name, NodeKind::RecordField);
            }
            fields += 1;
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        self.close_bracket(start, Tok::RBrace, "`,` or `}`", NodeKind::Record)?;
        Ok(())
    }

    /// A list literal, at its `[`. The first `..` spread's tokens, if it
    /// has one.
    #[inline(never)]
    fn list_expr(&mut self, start: u32) -> Result<Option<(u32, u32)>> {
        self.bump();
        let mut spread = None;
        if self.peek() != Some(&Tok::RBracket) {
            loop {
                let item = self.mark();
                if self.list_expr_item()? {
                    spread.get_or_insert((item, self.mark()));
                }
                if !self.eat(&Tok::Comma) || self.peek() == Some(&Tok::RBracket) {
                    break;
                }
            }
        }
        self.close_bracket(start, Tok::RBracket, "`,` or `]`", NodeKind::List)?;
        Ok(spread)
    }

    /// An element, or a `..xs` spread (docs/proposals/list-spread.md): a
    /// list joined in at that place. Whether it was a spread.
    fn list_expr_item(&mut self) -> Result<bool> {
        let outer = std::mem::replace(&mut self.modes.in_list, true);
        let item = self.list_expr_item_inner();
        self.modes.in_list = outer;
        item
    }

    fn list_expr_item_inner(&mut self) -> Result<bool> {
        if self.peek() != Some(&Tok::DotDot) {
            self.expr()?;
            return Ok(false);
        }
        let dots = self.mark();
        self.bump();
        if matches!(self.peek(), Some(Tok::Comma | Tok::RBracket)) {
            return Err(error(self.here(), "expected a list after `..`, as in `[x, ..xs]`").into());
        }
        self.expr()?;
        self.node(dots, NodeKind::Spread);
        Ok(true)
    }

    /// The facts of `arithmetic [..]`, `algebra [..]` and the like: a list of terms
    /// with no spread.
    fn fact_list(&mut self) -> Result<()> {
        if let Some((dots, end)) = self.list_expr(self.mark())? {
            let at = self.tokens[dots as usize]
                .span
                .to(self.lowered_span((dots + 1, end)));
            return Err(error(at, "a list of facts can't have a `..` spread")
                .with_note("this list is the facts to use, one term each; `..` builds a list value")
                .into());
        }
        Ok(())
    }

    /// `"a${x}b${y}c"`: text pieces and interpolations.
    fn interpolated_str(&mut self) -> Result<()> {
        let open = self.mark();
        self.bump();
        loop {
            // The lexer ends every text piece but the last with a `${`.
            let interpolation = self.mark();
            match self.peek() {
                Some(Tok::InterpOpen) => self.bump(),
                _ => return Err(self.unexpected("`${`").into()),
            };
            self.expr()?;
            match self.peek() {
                Some(Tok::InterpClose) => self.bump(),
                _ => return Err(self.unexpected("`}`").into()),
            };
            self.node(interpolation, NodeKind::Interpolation);
            if let Some(Tok::StrMid(_)) = self.peek() {
                self.bump();
            }
            match self.peek() {
                Some(Tok::StrEnd(_)) => {
                    self.bump();
                    break;
                }
                Some(Tok::InterpOpen) => {}
                _ => return Err(self.unexpected("`${` or the end of the text").into()),
            }
        }
        self.node(open, NodeKind::Interpolated);
        Ok(())
    }

    /// `-` at the start of an atom: a negative numeral (`-1`, the base of
    /// `-1.abs`), or an argument minus (`f -x`), which negates one atom with
    /// its dots and `()` calls, as any argument takes them.
    #[inline(never)]
    fn negative_atom(&mut self) -> Result<()> {
        let numeral = negative_numeral(self.tokens, self.pos);
        if !argument_minus(self.tokens, self.pos) && !numeral {
            return Err(self.unexpected_name("an expression").into());
        }
        let start = self.mark();
        self.bump();
        if numeral {
            // The number `negative_numeral` saw, read here rather than by
            // `atom_base`, so that `atom` stays its only caller.
            self.bump();
        } else {
            self.atom(false)?;
        }
        self.node(start, NodeKind::Prefix);
        Ok(())
    }

    /// An argument `!` (`f !x`): the `!` and one atom with its dots and `()`
    /// calls, as any argument takes them.
    #[inline(never)]
    fn bang_atom(&mut self) -> Result<()> {
        if !argument_bang(self.tokens, self.pos) {
            return Err(self.unexpected_name("an expression").into());
        }
        let start = self.mark();
        self.bump();
        self.atom(false)?;
        self.node(start, NodeKind::Prefix);
        Ok(())
    }

    /// An atom without its dots and `()` calls, starting at token `start`,
    /// the next. Always inlined, into `atom` and `brace_argument`: every
    /// level of a nested expression (`((…(0)…))`) goes through `atom` and
    /// this, and as two functions their frames don't share slots. Without
    /// the attribute, when 7a14ec83 gave it a second caller it stopped
    /// being inlined, and each level took about 780 bytes more of the
    /// stack (SW-875).
    #[inline(always)]
    fn atom_base(&mut self, start: u32) -> Result<()> {
        match self.peek() {
            Some(Tok::Minus) => return self.negative_atom(),
            Some(Tok::Bang) => return self.bang_atom(),
            Some(Tok::Lower(_)) => {
                self.lower_q("an expression")?;
            }
            Some(Tok::Upper(_)) => {
                self.upper_q("an expression")?;
            }
            Some(
                Tok::Num(_)
                | Tok::Float(_)
                | Tok::Str(_)
                | Tok::Char(_)
                | Tok::Underscore
                | Tok::Question
                | Tok::Prop,
            ) => {
                self.bump();
            }
            Some(Tok::StrStart(_)) => return self.interpolated_str(),
            Some(Tok::KwInclude) => {
                self.bump();
                match self.peek() {
                    Some(Tok::Str(_)) => {
                        self.bump();
                        self.node(start, NodeKind::Include);
                    }
                    _ => {
                        return Err(self
                            .unexpected("a path in quotes, as in `include \"inputs/day04.txt\"`")
                            .into());
                    }
                }
            }
            Some(Tok::KwArithmetic) => {
                self.bump();
                // `arithmetic [e1, e2]`: extra facts, by term.
                if self.peek() == Some(&Tok::LBracket) {
                    self.fact_list()?;
                    self.node(start, NodeKind::Omega);
                }
            }
            Some(Tok::KwAlgebra) => {
                self.bump();
                // `algebra [h1, h2]`: hypotheses, by term.
                if self.peek() == Some(&Tok::LBracket) {
                    self.fact_list()?;
                    self.node(start, NodeKind::Ring);
                }
            }
            Some(Tok::KwCases) if self.bare_cases() => {
                self.bump();
            }
            Some(Tok::TypeU) => {
                self.bump();
                if let Some(Tok::Num(n)) = self.peek() {
                    let end = self.bump().span;
                    if u32::try_from(n).ok().is_none_or(|l| l > MAX_UNIVERSE_LEVEL) {
                        return Err(error(end, "universe level is too large")
                            .with_note(format!(
                                "the largest universe is `Type {MAX_UNIVERSE_LEVEL}`"
                            ))
                            .into());
                    }
                    self.node(start, NodeKind::Universe);
                }
            }
            Some(Tok::LParen) if self.peek_at(1) == Some(&Tok::RParen) => {
                self.bump();
                self.bump();
                self.node(start, NodeKind::Unit);
            }
            // `(x := e)`: an explicit argument by name
            // (docs/proposals/named-arguments.md §4.1).
            Some(Tok::LParen)
                if matches!(self.peek_at(1), Some(Tok::Lower(_)))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                self.lower("a name")?;
                self.bump();
                self.expr()?;
                self.close_bracket(start, Tok::RParen, "`)`", NodeKind::NamedArg)?;
            }
            Some(Tok::LParen) if self.operator_section_ahead() => return self.operator_section(),
            Some(Tok::LParen) => {
                self.bump();
                self.expr()?;
                if self.peek() == Some(&Tok::Comma) {
                    return self.tuple_expr(start);
                }
                if self.eat(&Tok::Colon) {
                    self.expr()?;
                    if self.peek() == Some(&Tok::Comma) {
                        return Err(self.tuple_annotation().into());
                    }
                    self.close_bracket(start, Tok::RParen, "`)`", NodeKind::Annotation)?;
                    return Ok(());
                }
                self.close_bracket(start, Tok::RParen, "`)`", NodeKind::Paren)?;
            }
            Some(Tok::LBracket)
                if matches!(self.peek_at(1), Some(Tok::Lower(_) | Tok::KwDecreasing))
                    && self.peek_at(2) == Some(&Tok::ColonEq) =>
            {
                self.bump();
                // `[decreasing := p]`: the proof a recursive call of a
                // definition with `decreasing` needs.
                if self.peek() == Some(&Tok::KwDecreasing) {
                    self.bump();
                } else {
                    self.lower("a name")?;
                }
                self.bump();
                self.expr()?;
                self.expect(Tok::RBracket, "`]`")?;
                self.node(start, NodeKind::NamedArg);
            }
            Some(Tok::LBracket) => {
                self.list_expr(start)?;
            }
            Some(Tok::LBrace) => return self.record_expr(),
            Some(Tok::Dot) => return self.section_start(),
            // A keyword as a lambda's parameter: `(test => …)`.
            None if self.modes.recover => return self.ran_out("an expression"),
            _ if self.peek_at(1) == Some(&Tok::FatArrow) => {
                return Err(self.unexpected_name("an expression").into());
            }
            _ => return Err(self.unexpected("an expression").into()),
        }
        Ok(())
    }
}

/// A `Diagnostic` for a chain of comparisons that isn't allowed: `first`
/// says why it started a chain, `at` why it can't go on.
fn chain_error(
    (first, first_label): (Span, &str),
    (at, at_label): (Span, &str),
    message: String,
    note: impl Into<String>,
) -> Box<Diagnostic> {
    Box::new(
        Diagnostic::error("E-COMPARISON-CHAIN", message)
            .with_label(first, first_label)
            .with_label(at, at_label)
            .with_note(note.into()),
    )
}

/// How a comparison operator is written in a suggestion.
fn written(tok: Option<&Tok>) -> &'static str {
    match tok {
        Some(Tok::Lt) => "<",
        Some(Tok::Le) => "<=",
        Some(Tok::Gt) => ">",
        Some(Tok::Ge) => ">=",
        Some(Tok::Equals) => "=",
        Some(Tok::EqEq) => "==",
        Some(Tok::NotEq) => "!=",
        _ => "<",
    }
}

fn describe(tok: &Tok) -> String {
    match tok {
        Tok::Lower(s) | Tok::Upper(s) => format!("`{s}`"),
        Tok::Num(n) => format!("`{n}`"),
        Tok::Float(text) => format!("`{text}`"),
        Tok::Str(s) => format!("`\"{s}\"`"),
        Tok::StrStart(_) | Tok::StrMid(_) | Tok::StrEnd(_) => "a text literal".into(),
        Tok::InterpOpen => "`${`".into(),
        Tok::InterpClose => "`}` closing a `${…}`".into(),
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
        Tok::Semi => "`;`".into(),
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
        Tok::KwArithmetic => "`arithmetic`".into(),
        Tok::KwAlgebra => "`algebra`".into(),
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
        Tok::KwForall => "`forall`".into(),
        Tok::KwIf => "`if`".into(),
        Tok::KwThen => "`then`".into(),
        Tok::KwElse => "`else`".into(),
        Tok::Dot => "`.`".into(),
        Tok::DotDot => "`..`".into(),
        Tok::DotDotLt => "`..<`".into(),
        Tok::DotDotEq => "`..=`".into(),
        Tok::At => "`@[`".into(),
    }
}

/// `E-PARSE`: a lambda's parameter with a default value.
fn lambda_default(default: Span) -> Diagnostic {
    error(default, declarations::DEFAULT_PLACES).with_note(
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

/// `rewrite h at then t`: the `at` after a rule starts the hypothesis to
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

/// `rewrite h in t` or `cases in t`: the spelling before `then` replaced
/// `in` there (D3648), so `in` is only membership.
fn old_in(at: Span, construct: &str) -> Diagnostic {
    error(at, format!("write `then`, not `in`, after `{construct}`")).with_note(format!(
        "the proof that follows a `{construct}` comes after `then`: `{construct} … then t`; \
         `in` is only a membership test"
    ))
}

/// An `E-PARSE` error at `span`, labelled with its message.
pub(crate) fn error(span: Span, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic::error("E-PARSE", message.clone()).with_label(span, message)
}

#[cfg(test)]
mod tests;
