use std::collections::VecDeque;

use num_bigint::BigUint;

use crate::{Diagnostic, FileId, Span};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    /// Identifier starting with a lowercase letter or `_`: variables and functions.
    Lower(String),
    /// Identifier starting with an uppercase letter: data types and constructors.
    Upper(String),
    /// A number literal, of any size.
    Num(BigUint),
    /// A decimal or exponent literal, `1.5`, `1e3`, `2.5E-7`, as written: a
    /// `Float` (docs/proposals/float.md §2.3).
    Float(String),
    /// A string literal, used for test names: `"reverse twice"`.
    Str(String),
    /// The opening quote (`"` or `"""` and its line break) and the text
    /// before the first `${` of an interpolated string: `"a` in `"a${x}"`.
    /// Every text token's span is exactly the source it was read from.
    StrStart(String),
    /// The text between a `}` and the next `${` in an interpolated string.
    /// Left out when there is none (`"${x}${y}"`).
    StrMid(String),
    /// The text after the last `}` of an interpolated string, with the
    /// closing quote: `b"` in `"${x}b"`.
    StrEnd(String),
    /// The `${` that opens an interpolation inside a text literal.
    InterpOpen,
    /// The `}` that closes an interpolation inside a text literal.
    InterpClose,
    /// A character literal: `'a'`.
    Char(char),
    /// `type`, which starts a data type declaration.
    KwType,
    KwTheorem,
    /// `def`, which starts a definition in the new declaration syntax
    /// (docs/proposals/declaration-syntax.md).
    KwDef,
    KwExport,
    KwTest,
    /// `interface Ord (a: Type) = { … }`: a record the compiler finds
    /// instances of (docs/proposals/interfaces.md §5.1).
    KwInterface,
    /// `instance Nat.instOrd: Ord Nat := …`: a definition the compiler finds
    /// by its type (docs/proposals/interfaces.md §5.2).
    KwInstance,
    /// `Type`, the universe.
    TypeU,
    Prop,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    /// `;`, which ends the value of an expression `let`: `(let x := e; body)`.
    Semi,
    Colon,
    /// `:=`
    ColonEq,
    Equals,
    Arrow,
    Pipe,
    /// `||`
    OrOr,
    /// `|>`: pipe forward, `x |> f a` is `f a x`.
    PipeGt,
    /// `&&`
    AndAnd,
    Plus,
    /// `++`
    PlusPlus,
    Minus,
    Star,
    Slash,
    Percent,
    /// `!=`
    NotEq,
    EqEq,
    Lt,
    /// `<=`
    Le,
    /// `>`, `>=`: written the other way round (`a > b` is `b < a`).
    Gt,
    Ge,
    /// `!`, prefix "not". Also written `¬`.
    Bang,
    /// `in` (or `∈`): membership, `x in xs` (D1201). Also ends a `rewrite`
    /// rule or target: `rewrite h in body`.
    KwIn,
    /// `!in` (or `∉`): `x !in xs` is `!(x in xs)` (D1201).
    NotIn,
    /// `<->` (or `↔`): `p <-> q` is `Iff p q` (D1202).
    Iff,
    /// `exists` (or `∃`), followed by a lambda: `exists (x: T) => P` is
    /// `Exists T ((x: T) => P)` (D1203). Right after a `.` it's an ordinary
    /// name: `x.exists` is a field or method called `exists`.
    KwExists,
    /// `forall` (or `∀`), followed by parameters and `=>`: `forall (x: T) =>
    /// P` is the function type `(x: T) -> P` (D3458). After a `.` it's an
    /// ordinary name, as `exists` is.
    KwForall,
    KwIf,
    KwThen,
    KwElse,
    /// `ability Name params where`, then its operations.
    KwAbility,
    KwWhere,
    /// `handle e with | clause …`
    KwHandle,
    KwWith,
    /// `match e with | p => …`
    KwMatch,
    /// `| return x => …`, a handler's clause for the result.
    KwReturn,
    /// `let x := e`, binding `x` for the following lines of a block.
    KwLet,
    /// `import List (map, filter)`, at the top of a file.
    KwImport,
    KwInclude,
    /// `namespace Day05`, the first line of a file.
    KwNamespace,
    /// `calc e` followed by steps `_ = e := proof`, one per line.
    KwCalc,
    /// `rewrite p in t`: replace `p`'s left side in the goal by its right.
    KwRewrite,
    /// `omega` or `omega [e1, e2]`: a linear arithmetic proof found by the
    /// compiler (docs/proposals/omega.md).
    KwOmega,
    /// `ring` or `ring [h1, h2]`: an equation between polynomials, checked by
    /// normalising both sides (docs/proposals/proof-automation.md §6.2).
    KwRing,
    /// `cases` or `cases in t`: a proof by automatic case splitting
    /// (docs/proposals/simp.md §5).
    KwCases,
    /// `decreasing e` in a definition's header, and `[decreasing := p]`
    /// at a recursive call (docs/proposals/well-founded-recursion.md).
    KwDecreasing,
    /// `opaque def f …`: a definition opaque to the checker
    /// (docs/proposals/opaque-definitions.md §6.2).
    KwOpaque,
    /// `unfolding f, g` in a declaration's header: the opaque definitions
    /// its body may unfold (docs/proposals/opaque-definitions.md §6.3).
    KwUnfolding,
    LBrace,
    RBrace,
    /// `=>`: a lambda `x => e`, a `match` arm `| p => e`, a handler clause
    /// `| get (), k => e`.
    FatArrow,
    Underscore,
    /// `?`: an open goal, a part of a proof or program still to write
    /// (docs/proposals/lsp-goal-holes.md).
    Question,
    /// `.`, in field access: `p.name`.
    Dot,
    /// `..`, the rest of a record pattern: `{ name, .. }`.
    DotDot,
    /// `..<`: a range that stops before its end, `0 ..< n`.
    DotDotLt,
    /// `..=`: a range that includes its end, `1 ..= n`.
    DotDotEq,
    /// `@`, always followed by `[`: `@[js.name "X"]` writes attributes
    /// (docs/syntax.md, Attributes). The `[` is an ordinary [`Tok::LBracket`].
    At,
}

/// The one list of keywords. The lexer's word lookup, [`Tok::keyword`] and
/// [`keywords`] are all generated from it, so a keyword is added here only.
/// Keep it alphabetical: [`keywords`] returns the words in this order.
macro_rules! keyword_table {
    ($($word:literal => $tok:ident),* $(,)?) => {
        impl Tok {
            /// The word of a keyword written as one: `test`, `then`. `in`,
            /// `exists` and `forall` may also be written `∈`, `∃` and `∀`,
            /// which this can't tell apart.
            pub fn keyword(&self) -> Option<&'static str> {
                match self {
                    $(Tok::$tok => Some($word),)*
                    _ => None,
                }
            }
        }

        /// The keyword token a word lexes to, ignoring context.
        fn keyword_tok(word: &str) -> Option<Tok> {
            match word {
                $($word => Some(Tok::$tok),)*
                _ => None,
            }
        }

        /// Every word that lexes to a keyword token, in alphabetical order.
        /// Tools that mirror the lexer, such as the editor grammar and the
        /// playground's colouring, read this instead of copying the list.
        pub fn keywords() -> &'static [&'static str] {
            &[$($word),*]
        }
    };
}

keyword_table! {
    "ability" => KwAbility,
    "calc" => KwCalc,
    "cases" => KwCases,
    "decreasing" => KwDecreasing,
    "def" => KwDef,
    "else" => KwElse,
    "exists" => KwExists,
    "export" => KwExport,
    "forall" => KwForall,
    "handle" => KwHandle,
    "if" => KwIf,
    "import" => KwImport,
    "in" => KwIn,
    "include" => KwInclude,
    "instance" => KwInstance,
    "interface" => KwInterface,
    "let" => KwLet,
    "match" => KwMatch,
    "namespace" => KwNamespace,
    "omega" => KwOmega,
    "opaque" => KwOpaque,
    "return" => KwReturn,
    "rewrite" => KwRewrite,
    "ring" => KwRing,
    "test" => KwTest,
    "then" => KwThen,
    "theorem" => KwTheorem,
    "type" => KwType,
    "unfolding" => KwUnfolding,
    "where" => KwWhere,
    "with" => KwWith,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
    /// Byte offset from the start of the line. Declarations start at column 0, except that a `,` or
    /// closing bracket there continues an open bracket.
    pub column: u32,
    /// Whether this is the first token on its line. Blocks use this to find
    /// where each line starts.
    pub line_start: bool,
}

/// A `--` comment, kept by [`lex_with_trivia`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comment {
    /// The comment as written, from `--` to the end of the line (without a
    /// trailing `\r`).
    pub text: String,
    pub span: Span,
    /// Byte offset of the `--` from the start of its line.
    pub column: u32,
    /// For an own-line comment, the blank lines directly before it (after the
    /// previous comment, or the previous token). Always 0 for a trailing comment.
    pub blank_lines_before: u32,
}

/// What surrounds one token (or the end of the file) besides spaces.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Trivia {
    /// Comments on lines of their own before the token, in order.
    pub leading: Vec<Comment>,
    /// Blank lines directly before the token's own line (after the last
    /// leading comment, if any). 0 for a token that doesn't start its line.
    pub blank_lines_before: u32,
    /// A comment on the same line after the token. Only the last token of a
    /// line has one.
    pub trailing: Option<Comment>,
}

/// The result of [`lex_with_trivia`].
#[derive(Clone, Debug)]
pub struct Lexed {
    /// The same tokens [`lex`] returns.
    pub tokens: Vec<Token>,
    /// `trivia[i]` belongs to `tokens[i]`.
    pub trivia: Vec<Trivia>,
    /// What follows the last token: own-line comments, and the blank lines
    /// after them (or after the last token). Never has a trailing comment.
    pub eof: Trivia,
    /// The spans of the `--|` comments (to the end of the line, without a
    /// trailing `\r`), kept even without trivia: the doc links checked after
    /// a namespace (docs/proposals/documentation.md §7) are read from them.
    pub bars: Vec<Span>,
}

/// The tokens of `text`, without comments.
pub fn lex(file: FileId, text: &str) -> Result<Vec<Token>, Diagnostic> {
    lex_keeping(file, text, false).map(|lexed| lexed.tokens)
}

/// [`lex`], and the spans of the `--|` comments.
pub fn lex_with_bars(file: FileId, text: &str) -> Result<(Vec<Token>, Vec<Span>), Diagnostic> {
    lex_keeping(file, text, false).map(|lexed| (lexed.tokens, lexed.bars))
}

/// The tokens of `text` with the comments and blank lines around each. A
/// `--` inside a string or text literal is part of the literal, not a comment.
pub fn lex_with_trivia(file: FileId, text: &str) -> Result<Lexed, Diagnostic> {
    lex_keeping(file, text, true)
}

/// A declaration that didn't lex, from [`lex_recovering`].
#[derive(Clone, Debug)]
pub struct LexFailure {
    /// The lexical error, as [`lex`] reports it.
    pub error: Diagnostic,
    /// The bytes of the declaration (its attributes through to just before
    /// the next declaration), which the tokens leave out.
    pub range: std::ops::Range<usize>,
}

/// What [`lex_recovering`] read.
#[derive(Clone, Debug)]
pub struct Recovered {
    /// The tokens of the parts that lexed, at their positions in `text`.
    pub tokens: Vec<Token>,
    /// The `--|` comments' spans, as [`lex_with_bars`] gives them.
    pub bars: Vec<Span>,
    /// One per declaration that has a lexical error, in file order.
    pub failures: Vec<LexFailure>,
}

/// Whether a line starting with `line` can begin a declaration (or its
/// attributes): it starts in column 0 with something other than a comment, or
/// a bracket or `:=` that continues the line before.
fn starts_declaration(line: &[u8]) -> bool {
    match line.first() {
        None | Some(b' ' | b'\t' | b'\r' | b'\n' | b',' | b')' | b']' | b'}') => false,
        Some(b'-') => line.get(1) != Some(&b'-'),
        Some(b':') => line.get(1) != Some(&b'='),
        Some(_) => true,
    }
}

/// [`lex_with_bars`] that survives lexical errors. A declaration with one is
/// left out of the tokens and reported in `failures`, so the declarations
/// around it still lex and the parser can recover from it as it does from a
/// parse error. The declaration is the lines from the nearest line above the
/// error that starts in column 0 (and the `@[…]` lines before that) to the next
/// such line below it, less the comments just before that one. A file that
/// lexes gives the tokens of [`lex_with_bars`] and no failures.
pub fn lex_recovering(file: FileId, text: &str) -> Recovered {
    let bytes = text.as_bytes();
    let line_of = |at: usize| text[..at].rfind('\n').map_or(0, |newline| newline + 1);
    let next_line = |at: usize| text[at..].find('\n').map_or(text.len(), |n| at + n + 1);
    // `text` with the failed declarations' bytes replaced by spaces, so every
    // other token keeps its position.
    let mut current = text.to_string();
    let mut failures: Vec<LexFailure> = Vec::new();
    loop {
        let error = match lex_keeping(file, &current, false) {
            Ok(lexed) => {
                failures.sort_by_key(|failure| failure.range.start);
                return Recovered {
                    tokens: lexed.tokens,
                    bars: lexed.bars,
                    failures,
                };
            }
            Err(error) => error,
        };
        let (start, end) = error.primary_span().map_or((0, 0), |span| {
            let start = (span.start as usize).min(text.len());
            (start, (span.end as usize).clamp(start, text.len()))
        });
        // Back to the declaration's first line, and over the attributes above it.
        let mut from = line_of(start);
        while from > 0 && !starts_declaration(&bytes[from..]) {
            from = line_of(from - 1);
        }
        while from > 0 {
            let above = line_of(from - 1);
            if !bytes[above..].starts_with(b"@[") {
                break;
            }
            from = above;
        }
        // Forward to the next declaration's first line, less its comments.
        let mut to = next_line(line_of(end));
        while to < text.len() && !starts_declaration(&bytes[to..]) {
            to = next_line(to);
        }
        while to > from {
            let above = line_of(to - 1);
            if above <= from || !bytes[above..].starts_with(b"--") {
                break;
            }
            to = above;
        }
        let mut blanked = std::mem::take(&mut current).into_bytes();
        let mut changed = false;
        for byte in &mut blanked[from..to] {
            if !matches!(*byte, b' ' | b'\n') {
                *byte = b' ';
                changed = true;
            }
        }
        current = String::from_utf8(blanked).expect("spaces replace whole characters");
        if !changed {
            // The error is in text that is already blank, which can't
            // happen; give up on the file rather than loop.
            return Recovered {
                tokens: Vec::new(),
                bars: Vec::new(),
                failures: vec![LexFailure {
                    error,
                    range: 0..text.len(),
                }],
            };
        }
        failures.push(LexFailure {
            error,
            range: from..to,
        });
    }
}

/// Lexes `text`, recording the trivia only if `keep_trivia` (otherwise
/// `trivia` and `eof` are empty). Only the formatter needs it, and it takes
/// more memory than the tokens, so checking doesn't record it.
fn lex_keeping(file: FileId, text: &str, keep_trivia: bool) -> Result<Lexed, Diagnostic> {
    lex_from(file, text, 0, keep_trivia, None).map(|(lexed, _)| lexed)
}

/// Lexes `text` from `from`. With `interp: Some(dollar)`, `from` is just
/// after the `${` at `dollar` in a `"""` text, and lexing stops at the `}`
/// that closes it, returning its position. `scan_block` uses that to find
/// where each `${…}` ends, so it ends exactly where the main pass, lexing the
/// same bytes in the same state, will close it. Otherwise lexing runs to the
/// end of the text, and the position is its length.
fn lex_from(
    file: FileId,
    text: &str,
    from: usize,
    keep_trivia: bool,
    interp: Option<usize>,
) -> Result<(Lexed, usize), Diagnostic> {
    let bytes = text.as_bytes();
    let mut tokens: Vec<Token> = Vec::new();
    let mut trivia: Vec<Trivia> = Vec::new();
    // Own-line comments and blank lines waiting for the next token.
    let mut pending: Vec<Comment> = Vec::new();
    let mut blank_run = 0u32;
    // Whether the current line has had a token or comment, and how many
    // tokens there were when we last looked.
    let mut line_blank = true;
    let mut seen = 0;
    let mut i = from;
    let mut line_start = from;
    let mut fresh_line = true;
    // In `interp` mode the bottom entry stands for the `${` being scanned.
    let mut interps: Vec<Interp> = Vec::new();
    if let Some(dollar) = interp {
        interps.push(Interp {
            depth: 0,
            start: dollar,
            block: None,
            scanned: true,
        });
    }
    let mut closed_at = None;
    let mut bars: Vec<Span> = Vec::new();
    // The span of the last comment lexed, if the last thing lexed was one.
    let mut last_comment: Option<(usize, usize)> = None;

    while i < bytes.len() {
        if tokens.len() != seen {
            seen = tokens.len();
            line_blank = false;
        }
        while keep_trivia && trivia.len() < tokens.len() {
            trivia.push(Trivia {
                leading: std::mem::take(&mut pending),
                blank_lines_before: std::mem::take(&mut blank_run),
                trailing: None,
            });
        }
        let c = bytes[i];
        match c {
            b'\n' => {
                if let Some(&Interp {
                    start: string_start,
                    scanned,
                    ..
                }) = interps.last()
                {
                    if scanned {
                        if let Some((start, end)) = last_comment {
                            return Err(error(
                                file,
                                start,
                                end,
                                "a comment in a `${…}` runs to the end of the line, so it \
                                 takes the `}`",
                            ));
                        }
                        return Err(error(
                            file,
                            string_start,
                            i,
                            "a `${…}` in a `\"\"\"` text stays on one line",
                        ));
                    }
                    return Err(error(
                        file,
                        string_start,
                        i,
                        "this string isn't closed with `\"`",
                    ));
                }
                if line_blank {
                    blank_run += 1;
                }
                line_blank = true;
                i += 1;
                line_start = i;
                fresh_line = true;
                continue;
            }
            b' ' | b'\r' => {
                i += 1;
                continue;
            }
            b'\t' => {
                return Err(error(
                    file,
                    i,
                    i + 1,
                    "tabs aren't allowed; indent with spaces",
                ));
            }
            b'-' if bytes.get(i + 1) == Some(&b'-') => {
                let start = i;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                let end = if bytes[start..i].ends_with(b"\r") {
                    i - 1
                } else {
                    i
                };
                last_comment = Some((start, end));
                if fresh_line && bytes[start..end].starts_with(b"--|") {
                    bars.push(Span::new(file, start as u32, end as u32));
                }
                if !keep_trivia {
                    continue;
                }
                let mut comment = Comment {
                    text: text[start..end].to_string(),
                    span: Span::new(file, start as u32, end as u32),
                    column: (start - line_start) as u32,
                    blank_lines_before: 0,
                };
                if fresh_line {
                    comment.blank_lines_before = std::mem::take(&mut blank_run);
                    pending.push(comment);
                    line_blank = false;
                } else {
                    trivia
                        .last_mut()
                        .expect("a token precedes a trailing comment")
                        .trailing = Some(comment);
                }
                continue;
            }
            _ => {}
        }

        // A token from here on is the last thing lexed, not a comment.
        last_comment = None;
        let start = i;
        let column = (start - line_start) as u32;
        let tok = if c.is_ascii_alphabetic() || c == b'_' {
            while i < bytes.len()
                && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'')
            {
                i += 1;
            }
            // A qualified name, `List.map` or `Std.List.Cons`: components
            // after an uppercase one, joined by `.` with no spaces. It's one
            // token, upper or lower by its last component. After a lowercase
            // component, `.` is field access (`p.name`).
            let mut last = start;
            while text.as_bytes()[last].is_ascii_uppercase()
                && bytes.get(i) == Some(&b'.')
                && bytes.get(i + 1).is_some_and(|b| b.is_ascii_alphabetic())
            {
                i += 1;
                last = i;
                while i < bytes.len()
                    && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'\'')
                {
                    i += 1;
                }
            }
            let word = &text[start..i];
            if last > start {
                let qualified = word.to_string();
                if bytes[last].is_ascii_uppercase() {
                    Tok::Upper(qualified)
                } else {
                    Tok::Lower(qualified)
                }
            } else {
                match word {
                    "_" => Tok::Underscore,
                    // After a `.`, a field or a dot call: `x.exists p`.
                    "exists" | "forall" if start > 0 && bytes[start - 1] == b'.' => {
                        Tok::Lower(word.to_string())
                    }
                    _ if let Some(tok) = keyword_tok(word) => tok,
                    "Type" => Tok::TypeU,
                    "Prop" => Tok::Prop,
                    _ if c.is_ascii_uppercase() => Tok::Upper(word.to_string()),
                    _ => Tok::Lower(word.to_string()),
                }
            }
        } else if c.is_ascii_digit() {
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            // A decimal point needs a digit after it (so `1..n` is a
            // range), and an exponent at least one digit. A number right
            // after a `.` is digits only, so `xs.0.1` stays `xs` `.` `0`
            // `.` `1` (docs/proposals/float.md §2.3).
            let after_dot = start > 0 && bytes[start - 1] == b'.';
            let mut float = false;
            if !after_dot {
                if bytes.get(i) == Some(&b'.') && bytes.get(i + 1).is_some_and(u8::is_ascii_digit) {
                    i += 1;
                    while i < bytes.len() && bytes[i].is_ascii_digit() {
                        i += 1;
                    }
                    float = true;
                }
                if matches!(bytes.get(i), Some(b'e' | b'E')) {
                    let sign = usize::from(matches!(bytes.get(i + 1), Some(b'+' | b'-')));
                    if bytes.get(i + 1 + sign).is_some_and(u8::is_ascii_digit) {
                        i += 1 + sign;
                        while i < bytes.len() && bytes[i].is_ascii_digit() {
                            i += 1;
                        }
                        float = true;
                    }
                }
            }
            if float {
                Tok::Float(text[start..i].to_string())
            } else {
                let n = text[start..i]
                    .parse()
                    .expect("a run of ASCII digits is a valid number");
                Tok::Num(n)
            }
        } else if c == b'"' {
            let block = text[i..].starts_with("\"\"\"");
            if block && let Some(dollar) = interp {
                // A `"""` text needs a line of its own, so it can't be in a
                // one-line `${…}`. Refusing it here also keeps `scan_block`
                // from recursing.
                return Err(error(
                    file,
                    dollar,
                    i + 3,
                    "a `${…}` in a `\"\"\"` text stays on one line, so it can't hold a \
                     `\"\"\"` text",
                ));
            }
            let (chars, stop, interpolation, rest) = if block {
                let mut segs = scan_block(file, text, i)?;
                let piece = segs.pop_front().expect("a block has a piece");
                (piece.text, piece.stop, piece.interpolation, Some(segs))
            } else {
                let (chars, stop, interpolation) = scan_string(file, text, i + 1, i)?;
                (chars, stop, interpolation, None)
            };
            let close_len = if block { 3 } else { 1 };
            if interpolation {
                tokens.push(Token {
                    tok: Tok::StrStart(chars),
                    span: Span::new(file, start as u32, stop as u32),
                    column,
                    line_start: fresh_line,
                });
                if let Some(newline) = text[start..stop].rfind('\n') {
                    line_start = start + newline + 1;
                }
                tokens.push(Token {
                    tok: Tok::InterpOpen,
                    span: Span::new(file, stop as u32, (stop + 2) as u32),
                    column: (stop - line_start) as u32,
                    line_start: false,
                });
                interps.push(Interp {
                    depth: 0,
                    start,
                    block: rest,
                    scanned: false,
                });
                i = stop + 2;
            } else {
                tokens.push(Token {
                    tok: Tok::Str(chars),
                    span: Span::new(file, start as u32, (stop + close_len) as u32),
                    column,
                    line_start: fresh_line,
                });
                i = stop + close_len;
            }
            if let Some(newline) = text[start..stop].rfind('\n') {
                line_start = start + newline + 1;
            }
            fresh_line = false;
            continue;
        } else if c == b'\'' {
            i += 1;
            let mut chars = String::new();
            loop {
                match bytes.get(i) {
                    None | Some(b'\n') => {
                        return Err(error(
                            file,
                            start,
                            i,
                            "this character isn't closed with `'`",
                        ));
                    }
                    Some(b'\'') => {
                        i += 1;
                        break;
                    }
                    Some(b'\\') => {
                        let (ch, len) = escape(file, text, i)?;
                        chars.push(ch);
                        i += len;
                    }
                    Some(_) => {
                        let ch = text[i..].chars().next().expect("non-empty");
                        chars.push(ch);
                        i += ch.len_utf8();
                    }
                }
            }
            let mut it = chars.chars();
            let tok = match (it.next(), it.next()) {
                (Some(ch), None) => Tok::Char(ch),
                _ => {
                    return Err(error(
                        file,
                        start,
                        i,
                        "a character literal holds exactly one character",
                    ));
                }
            };
            tokens.push(Token {
                tok,
                span: Span::new(file, start as u32, i as u32),
                column,
                line_start: fresh_line,
            });
            fresh_line = false;
            continue;
        } else if !c.is_ascii() {
            let ch = text[start..].chars().next().expect("non-empty");
            let end = start + ch.len_utf8();
            match unicode_alias(ch) {
                Some(tok) => {
                    i = end;
                    tok
                }
                None => return Err(unicode_error(file, start, end, ch)),
            }
        } else {
            i += 1;
            if c == b'{'
                && let Some(interp) = interps.last_mut()
            {
                interp.depth += 1;
            }
            if c == b'}' && matches!(interps.last(), Some(Interp { depth: 0, .. })) {
                let mut interp = interps.pop().expect("checked");
                if interp.scanned {
                    closed_at = Some(start);
                    break;
                }
                tokens.push(Token {
                    tok: Tok::InterpClose,
                    span: Span::new(file, start as u32, i as u32),
                    column,
                    line_start: fresh_line,
                });
                let text_start = i;
                let (chars, stop, interpolation) = match &mut interp.block {
                    Some(pieces) => {
                        // `scan_block` found this `}` with this same lexer, so
                        // the two agree; if they ever don't, say so rather
                        // than slice the text backwards.
                        let piece = pieces
                            .pop_front()
                            .filter(|piece| piece.from == text_start)
                            .ok_or_else(|| {
                                error(
                                    file,
                                    interp.start,
                                    text_start,
                                    "this `${…}` can't be read: the `\"\"\"` text's pieces \
                                     don't line up with it (a compiler bug; please report it)",
                                )
                            })?;
                        (piece.text, piece.stop, piece.interpolation)
                    }
                    None => scan_string(file, text, i, interp.start)?,
                };
                let close_len = if interp.block.is_some() { 3 } else { 1 };
                // The text up to the next `${` (or through the closing
                // quote), then that `${`. A `}${` has no text between.
                let text_end = if interpolation {
                    stop
                } else {
                    stop + close_len
                };
                if !interpolation || text_end > text_start {
                    tokens.push(Token {
                        tok: if interpolation {
                            Tok::StrMid(chars)
                        } else {
                            Tok::StrEnd(chars)
                        },
                        span: Span::new(file, text_start as u32, text_end as u32),
                        column: (text_start - line_start) as u32,
                        line_start: false,
                    });
                }
                if let Some(newline) = text[text_start..stop].rfind('\n') {
                    line_start = text_start + newline + 1;
                }
                if interpolation {
                    tokens.push(Token {
                        tok: Tok::InterpOpen,
                        span: Span::new(file, stop as u32, (stop + 2) as u32),
                        column: (stop - line_start) as u32,
                        line_start: false,
                    });
                    i = stop + 2;
                } else {
                    i = text_end;
                }
                if interpolation {
                    interps.push(interp);
                }
                fresh_line = false;
                continue;
            }
            if c == b'}'
                && let Some(interp) = interps.last_mut()
            {
                interp.depth -= 1;
            }
            match c {
                b'(' => Tok::LParen,
                b')' => Tok::RParen,
                b'[' => Tok::LBracket,
                b'{' => Tok::LBrace,
                b'}' => Tok::RBrace,
                b']' => Tok::RBracket,
                b',' => Tok::Comma,
                b';' => Tok::Semi,
                b'.' if bytes.get(i) == Some(&b'.') && bytes.get(i + 1) == Some(&b'<') => {
                    i += 2;
                    Tok::DotDotLt
                }
                b'.' if bytes.get(i) == Some(&b'.') && bytes.get(i + 1) == Some(&b'=') => {
                    i += 2;
                    Tok::DotDotEq
                }
                b'.' if bytes.get(i) == Some(&b'.') => {
                    i += 1;
                    Tok::DotDot
                }
                b'.' => Tok::Dot,
                b':' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::ColonEq
                }
                b':' => Tok::Colon,
                b'=' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::EqEq
                }
                b'=' if bytes.get(i) == Some(&b'>') => {
                    i += 1;
                    Tok::FatArrow
                }
                b'=' => Tok::Equals,
                b'|' if bytes.get(i) == Some(&b'|') => {
                    i += 1;
                    Tok::OrOr
                }
                b'|' if bytes.get(i) == Some(&b'>') => {
                    i += 1;
                    Tok::PipeGt
                }
                b'|' => Tok::Pipe,
                b'&' if bytes.get(i) == Some(&b'&') => {
                    i += 1;
                    Tok::AndAnd
                }
                b'+' if bytes.get(i) == Some(&b'+') => {
                    i += 1;
                    Tok::PlusPlus
                }
                b'+' => Tok::Plus,
                b'-' if bytes.get(i) == Some(&b'>') => {
                    i += 1;
                    Tok::Arrow
                }
                b'-' => Tok::Minus,
                b'*' => Tok::Star,
                b'/' => Tok::Slash,
                b'%' => Tok::Percent,
                b'!' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::NotEq
                }
                // `!in`, but not `!inside` (`!` and a name).
                b'!' if text[i..].starts_with("in")
                    && !bytes.get(i + 2).is_some_and(|b| {
                        b.is_ascii_alphanumeric() || *b == b'_' || *b == b'\''
                    }) =>
                {
                    i += 2;
                    Tok::NotIn
                }
                b'<' if text[i..].starts_with("->") => {
                    i += 2;
                    Tok::Iff
                }
                b'<' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::Le
                }
                b'<' => Tok::Lt,
                b'>' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::Ge
                }
                b'>' => Tok::Gt,
                b'!' => Tok::Bang,
                b'?' => Tok::Question,
                // `@[` opens attributes; the `[` is its own token, so every
                // count of brackets counts it.
                b'@' if bytes.get(i) == Some(&b'[') => Tok::At,
                b'@' => {
                    return Err(error(
                        file,
                        start,
                        i,
                        "unexpected character `@`: it's only used in `@[…]`, which writes \
                         attributes"
                            .to_string(),
                    ));
                }
                _ => {
                    return Err(error(
                        file,
                        start,
                        i,
                        format!("unexpected character {}", shown(c as char)),
                    ));
                }
            }
        };
        tokens.push(Token {
            tok,
            span: Span::new(file, start as u32, i as u32),
            column,
            line_start: fresh_line,
        });
        fresh_line = false;
    }
    if let Some(dollar) = interp {
        return match closed_at {
            Some(close) => Ok((
                Lexed {
                    tokens: Vec::new(),
                    trivia: Vec::new(),
                    eof: Trivia::default(),
                    bars: Vec::new(),
                },
                close,
            )),
            None => Err(error(
                file,
                dollar,
                bytes.len(),
                "this `${…}` isn't closed with `}`",
            )),
        };
    }
    if let Some(&Interp {
        start: string_start,
        ..
    }) = interps.last()
    {
        return Err(error(
            file,
            string_start,
            bytes.len(),
            "this string isn't closed with `\"`",
        ));
    }
    while keep_trivia && trivia.len() < tokens.len() {
        trivia.push(Trivia {
            leading: std::mem::take(&mut pending),
            blank_lines_before: std::mem::take(&mut blank_run),
            trailing: None,
        });
    }
    Ok((
        Lexed {
            tokens,
            trivia,
            eof: Trivia {
                leading: pending,
                blank_lines_before: blank_run,
                trailing: None,
            },
            bars,
        },
        bytes.len(),
    ))
}

/// A text literal whose `${…}` is being lexed.
struct Interp {
    /// Braces opened inside the expression and not yet closed.
    depth: usize,
    /// Where the literal starts.
    start: usize,
    /// For a `"""` literal, the rest of its pieces, already de-indented
    /// (see `scan_block`).
    block: Option<VecDeque<Piece>>,
    /// Whether this is the `${` that `lex_from` was asked to find the end of.
    scanned: bool,
}

/// A piece of a `"""` literal's text.
struct Piece {
    /// The text, de-indented and with its escapes read.
    text: String,
    /// Where the piece's text starts in the source: after the opening line,
    /// or just after the `}` of the `${…}` before it.
    from: usize,
    /// The position of the `${` or the closing `"""` after it.
    stop: usize,
    /// Whether it was a `${`.
    interpolation: bool,
}

/// The pieces of the `"""` literal starting at `open`. The text is the lines
/// after the opening line, with the common indentation removed (the
/// smallest among the non-blank lines and a closing line of only spaces),
/// whitespace-only lines emptied, and `\r\n` read as `\n`. A closing `"""`
/// alone on its line adds nothing, so the text ends with the last line's
/// newline; right after text, the text ends there. Escapes are read after
/// the indentation is removed.
fn scan_block(file: FileId, text: &str, open: usize) -> Result<VecDeque<Piece>, Diagnostic> {
    let bytes = text.as_bytes();
    let unclosed = || error(file, open, open + 3, "this text isn't closed with `\"\"\"`");
    // The opening line holds nothing after the `"""`.
    let mut i = open + 3;
    while bytes.get(i) == Some(&b' ') || bytes.get(i) == Some(&b'\r') {
        i += 1;
    }
    if i >= bytes.len() {
        return Err(unclosed());
    }
    if bytes[i] != b'\n' {
        return Err(error(
            file,
            open,
            i + 1,
            "a `\"\"\"` text starts on the next line: nothing may follow the opening `\"\"\"` (use `\"…\"` for one line)",
        ));
    }
    let body = i + 1;
    // Pass 1: where the lines start, the `${…}` ranges, and the closing.
    let mut line_starts = vec![body];
    let mut interps: Vec<(usize, usize)> = Vec::new();
    let mut i = body;
    let close = loop {
        match bytes.get(i) {
            None => return Err(unclosed()),
            Some(b'\n') => {
                i += 1;
                line_starts.push(i);
            }
            Some(b'\\') => {
                i += 1;
                match text[i..].chars().next() {
                    Some('\n') | None => {}
                    Some(ch) => i += ch.len_utf8(),
                }
            }
            Some(b'"') if text[i..].starts_with("\"\"\"") => break i,
            Some(b'$') if bytes.get(i + 1) == Some(&b'{') => {
                // The `}` that closes it, found by the lexer itself, so that
                // a `}` in a nested literal (`${"}"}`, `${1'}'}`) is read the
                // same way here as in the main pass.
                let dollar = i;
                let (_, close) = lex_from(file, text, i + 2, false, Some(dollar))?;
                interps.push((dollar, close));
                i = close + 1;
            }
            Some(_) => i += 1,
        }
    };
    // Each line, as (start, end of its text without the `\n`).
    let mut lines: Vec<(usize, usize)> = Vec::new();
    for (k, &ls) in line_starts.iter().enumerate() {
        let le = line_starts.get(k + 1).map_or(close, |&n| n - 1);
        lines.push((ls, le));
    }
    let blank = |&(ls, le): &(usize, usize)| {
        bytes[ls..le]
            .iter()
            .all(|b| matches!(b, b' ' | b'\t' | b'\r'))
    };
    let last = lines.len() - 1;
    let mut indent = usize::MAX;
    for (k, line) in lines.iter().enumerate() {
        if k < last && blank(line) {
            continue;
        }
        let (ls, le) = *line;
        let width = bytes[ls..le].iter().take_while(|&&b| b == b' ').count();
        if bytes.get(ls + width) == Some(&b'\t') {
            return Err(error(
                file,
                ls + width,
                ls + width + 1,
                "tabs aren't allowed in a `\"\"\"` text's indentation; indent with spaces",
            ));
        }
        indent = indent.min(if blank(line) { le - ls } else { width });
    }
    // Pass 2: the pieces.
    let mut pieces = VecDeque::new();
    let mut chars = String::new();
    let mut from = body;
    let mut next_interp = 0;
    for (k, line) in lines.iter().enumerate() {
        let (ls, le) = *line;
        if k == last && blank(line) {
            break;
        }
        let mut j = if blank(line) { le } else { ls + indent };
        while j < le {
            match bytes[j] {
                b'$' if bytes.get(j + 1) == Some(&b'{') => {
                    let close = match interps.get(next_interp) {
                        Some(&(dollar, close)) if dollar == j => close,
                        _ => {
                            return Err(error(
                                file,
                                j,
                                j + 2,
                                "this `${…}` can't be read: the `\"\"\"` text's scans \
                                 disagree about it (a compiler bug; please report it)",
                            ));
                        }
                    };
                    pieces.push_back(Piece {
                        text: std::mem::take(&mut chars),
                        from,
                        stop: j,
                        interpolation: true,
                    });
                    j = close + 1;
                    from = j;
                    next_interp += 1;
                }
                b'\\' => {
                    let (ch, len) = escape(file, text, j)?;
                    chars.push(ch);
                    j += len;
                }
                b'\r' if j + 1 == le => j += 1,
                _ => {
                    let ch = text[j..].chars().next().expect("non-empty");
                    chars.push(ch);
                    j += ch.len_utf8();
                }
            }
        }
        if k < last {
            chars.push('\n');
        }
    }
    pieces.push_back(Piece {
        text: chars,
        from,
        stop: close,
        interpolation: false,
    });
    Ok(pieces)
}

/// The text of a string from `i` up to its closing `"` or a `${`. Returns
/// the text, the position of that `"` or `$`, and whether it was a `${`.
fn scan_string(
    file: FileId,
    text: &str,
    mut i: usize,
    start: usize,
) -> Result<(String, usize, bool), Diagnostic> {
    let bytes = text.as_bytes();
    let mut chars = String::new();
    loop {
        match bytes.get(i) {
            None | Some(b'\n') => {
                return Err(error(file, start, i, "this string isn't closed with `\"`"));
            }
            Some(b'$') if bytes.get(i + 1) == Some(&b'{') => {
                return Ok((chars, i, true));
            }
            Some(b'"') => return Ok((chars, i, false)),
            Some(b'\\') => {
                let (ch, len) = escape(file, text, i)?;
                chars.push(ch);
                i += len;
            }
            Some(_) => {
                let ch = text[i..].chars().next().expect("non-empty");
                chars.push(ch);
                i += ch.len_utf8();
            }
        }
    }
}

/// The escape sequence starting with the `\\` at `i`: the character it
/// stands for, and its length in bytes. `\\u{…}` takes 1 to 6 hex digits and
/// must name a Unicode scalar value, so it can't be a surrogate.
fn escape(file: FileId, text: &str, i: usize) -> Result<(char, usize), Diagnostic> {
    let bytes = text.as_bytes();
    let simple = match bytes.get(i + 1) {
        Some(b'n') => Some('\n'),
        Some(b't') => Some('\t'),
        Some(b'r') => Some('\r'),
        Some(b'\\') => Some('\\'),
        Some(b'"') => Some('"'),
        Some(b'\'') => Some('\''),
        Some(b'$') => Some('$'),
        _ => None,
    };
    if let Some(ch) = simple {
        return Ok((ch, 2));
    }
    if bytes.get(i + 1) != Some(&b'u') {
        let end = text[i + 1..]
            .chars()
            .next()
            .map_or(i + 1, |c| i + 1 + c.len_utf8());
        return Err(error(
            file,
            i,
            end,
            "unknown escape: use `\\n`, `\\t`, `\\r`, `\\\\`, `\\\"`, `\\'`, `\\$` or `\\u{…}`",
        ));
    }
    let bad = |end: usize| {
        error(
            file,
            i,
            end,
            "`\\u{…}` takes 1 to 6 hexadecimal digits in braces",
        )
    };
    if bytes.get(i + 2) != Some(&b'{') {
        return Err(bad(i + 2));
    }
    let digits_start = i + 3;
    let mut j = digits_start;
    while j < bytes.len() && bytes[j].is_ascii_hexdigit() {
        j += 1;
    }
    if bytes.get(j) != Some(&b'}') || j == digits_start || j - digits_start > 6 {
        return Err(bad(j));
    }
    let code = u32::from_str_radix(&text[digits_start..j], 16).expect("1 to 6 hex digits");
    let Some(ch) = char::from_u32(code) else {
        return Err(error(
            file,
            i,
            j + 1,
            format!("U+{code:X} isn't a Unicode scalar value, so it can't be a character"),
        ));
    };
    Ok((ch, j + 1 - i))
}

/// The Unicode spellings of operators (D1200), with the ASCII each stands
/// for. Each lexes to exactly the token its ASCII form does, so its meaning,
/// precedence and errors are the same.
pub const UNICODE_ALIASES: &[(char, &str)] = &[
    ('∈', "in"),
    ('∉', "!in"),
    ('→', "->"),
    ('↔', "<->"),
    ('∧', "&&"),
    ('∨', "||"),
    ('¬', "!"),
    ('≤', "<="),
    ('≥', ">="),
    ('≠', "!="),
    ('∃', "exists"),
    ('∀', "forall"),
];

/// The token a Unicode alias stands for.
fn unicode_alias(ch: char) -> Option<Tok> {
    Some(match ch {
        '∈' => Tok::KwIn,
        '∉' => Tok::NotIn,
        '→' => Tok::Arrow,
        '↔' => Tok::Iff,
        '∧' => Tok::AndAnd,
        '∨' => Tok::OrOr,
        '¬' => Tok::Bang,
        '≤' => Tok::Le,
        '≥' => Tok::Ge,
        '≠' => Tok::NotEq,
        '∃' => Tok::KwExists,
        '∀' => Tok::KwForall,
        _ => return None,
    })
}

/// Symbols from logic and mathematics that aren't aliases, with what to
/// write instead (D1208).
const UNSUPPORTED: &[(char, &str)] = &[
    (
        '⇒',
        "write `=>` for a lambda or a match arm, or `->` (or `→`) for implication",
    ),
    ('⟹', "write `->` for implication"),
    ('⇔', "write `<->`"),
    ('⟺', "write `<->`"),
    ('←', "write `<-`, as in `rewrite <- h`"),
    ('λ', "a lambda is written `x => body`"),
    ('≡', "write `=`"),
    ('≢', "write `!=`"),
    ('≔', "write `:=`"),
    (
        '⊆',
        "there are no set operators: write it with a function, such as `List.All`",
    ),
    ('⊂', "there are no set operators: write it with a function"),
    (
        '⊇',
        "there are no set operators: write it with a function, such as `List.All`",
    ),
    ('⊃', "there are no set operators: write it with a function"),
    ('∪', "there are no set operators: write `Set.union`"),
    ('∩', "there are no set operators: write `Set.intersect`"),
    ('∖', "there are no set operators: write `Set.difference`"),
    ('∅', "write `Set.empty` or `[]`"),
    ('⊥', "write `Void`"),
    ('⊤', "write `Unit`"),
    ('ℕ', "write `Nat`"),
    ('ℤ', "write `Int`"),
    (
        '×',
        "write `*` for multiplication, or `(A, B)` for a pair type",
    ),
    ('·', "write `*`"),
    ('÷', "write `/`"),
    ('∘', "there's no composition operator: write a lambda"),
];

/// The error for a character the lexer doesn't know. For a symbol from
/// logic or mathematics it says what to write instead, or that it isn't
/// supported (D1208).
fn unicode_error(file: FileId, start: usize, end: usize, ch: char) -> Diagnostic {
    let d = error(
        file,
        start,
        end,
        format!("unexpected character {}", shown(ch)),
    );
    if let Some(note) = invisible(ch).and_then(|(_, note)| note) {
        return d.with_note(note);
    }
    if let Some((_, hint)) = UNSUPPORTED.iter().find(|(c, _)| *c == ch) {
        return d.with_note(format!("`{ch}` isn't supported: {hint}"));
    }
    // The blocks of arrows and mathematical operators.
    if matches!(ch as u32, 0x2190..=0x22FF | 0x27C0..=0x27FF | 0x2900..=0x2AFF) {
        return d.with_note(format!(
            "`{ch}` isn't supported. Operators are written in ASCII; these Unicode spellings \
             may be used instead: {}",
            alias_list()
        ));
    }
    d
}

/// A character for a message: in backticks, or by its code point and name
/// if it would show as nothing or as a plain space (`U+00A0 NO-BREAK SPACE`).
fn shown(ch: char) -> String {
    match invisible(ch) {
        Some((name, _)) if !name.is_empty() => format!("U+{:04X} {name}", ch as u32),
        Some(_) => format!("U+{:04X}", ch as u32),
        None => format!("`{ch}`"),
    }
}

/// For a character that shows as nothing or as a space: its Unicode name
/// (empty if it isn't in the table) and what to do about it. The table holds
/// the ones text pasted from the web or a word processor tends to carry.
fn invisible(ch: char) -> Option<(&'static str, Option<&'static str>)> {
    const SPACE: Option<&str> = Some("it looks like a space but isn't one: type a plain space");
    const NOTHING: Option<&str> = Some("it shows as nothing: delete it");
    let entry = match ch {
        '\u{00A0}' => ("NO-BREAK SPACE", SPACE),
        '\u{1680}' => ("OGHAM SPACE MARK", SPACE),
        '\u{2000}' => ("EN QUAD", SPACE),
        '\u{2001}' => ("EM QUAD", SPACE),
        '\u{2002}' => ("EN SPACE", SPACE),
        '\u{2003}' => ("EM SPACE", SPACE),
        '\u{2004}' => ("THREE-PER-EM SPACE", SPACE),
        '\u{2005}' => ("FOUR-PER-EM SPACE", SPACE),
        '\u{2006}' => ("SIX-PER-EM SPACE", SPACE),
        '\u{2007}' => ("FIGURE SPACE", SPACE),
        '\u{2008}' => ("PUNCTUATION SPACE", SPACE),
        '\u{2009}' => ("THIN SPACE", SPACE),
        '\u{200A}' => ("HAIR SPACE", SPACE),
        '\u{202F}' => ("NARROW NO-BREAK SPACE", SPACE),
        '\u{205F}' => ("MEDIUM MATHEMATICAL SPACE", SPACE),
        '\u{3000}' => ("IDEOGRAPHIC SPACE", SPACE),
        '\u{00AD}' => ("SOFT HYPHEN", NOTHING),
        '\u{034F}' => ("COMBINING GRAPHEME JOINER", NOTHING),
        '\u{180E}' => ("MONGOLIAN VOWEL SEPARATOR", NOTHING),
        '\u{200B}' => ("ZERO WIDTH SPACE", NOTHING),
        '\u{200C}' => ("ZERO WIDTH NON-JOINER", NOTHING),
        '\u{200D}' => ("ZERO WIDTH JOINER", NOTHING),
        '\u{200E}' => ("LEFT-TO-RIGHT MARK", NOTHING),
        '\u{200F}' => ("RIGHT-TO-LEFT MARK", NOTHING),
        '\u{2060}' => ("WORD JOINER", NOTHING),
        '\u{2061}'..='\u{2064}' => ("", NOTHING),
        '\u{FEFF}' => ("ZERO WIDTH NO-BREAK SPACE (byte-order mark)", NOTHING),
        '\u{2028}' => ("LINE SEPARATOR", Some("end lines with an ordinary newline")),
        '\u{2029}' => (
            "PARAGRAPH SEPARATOR",
            Some("end lines with an ordinary newline"),
        ),
        '\u{061C}' | '\u{202A}'..='\u{202E}' | '\u{2066}'..='\u{2069}' => (
            "",
            Some(
                "it's a text-direction control, which changes how the line shows without showing \
             itself: delete it",
            ),
        ),
        '\u{FFF9}'..='\u{FFFB}' => ("", NOTHING),
        '\u{E0001}' | '\u{E0020}'..='\u{E007F}' => ("", NOTHING),
        _ if ch.is_whitespace() || ch.is_control() => ("", None),
        _ => return None,
    };
    Some(entry)
}

/// The Unicode spellings and the ASCII each stands for, for messages.
fn alias_list() -> String {
    UNICODE_ALIASES
        .iter()
        .map(|(c, ascii)| format!("`{c}` for `{ascii}`"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn error(file: FileId, start: usize, end: usize, message: impl Into<String>) -> Diagnostic {
    let message = message.into();
    Diagnostic::error("E-PARSE", message.clone())
        .with_label(Span::new(file, start as u32, end as u32), message)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;

    fn tokens(text: &str) -> Result<Vec<Tok>, &'static str> {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        lex(file, text)
            .map(|ts| ts.into_iter().map(|t| t.tok).collect())
            .map_err(|d| d.code)
    }

    /// The declared names left after recovering, the names marked failed, and
    /// the error messages' first lines' spans' starts.
    fn recover(text: &str) -> (Vec<String>, Vec<String>, Vec<u32>) {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        let (module, errors) = crate::parse_module_recovering(file, text, crate::DEFAULT_STACK);
        let kept = module
            .decls
            .iter()
            .filter_map(|decl| match decl {
                crate::ast::Decl::Signature { name, .. } => Some(name.text.clone()),
                _ => None,
            })
            .collect();
        let failed = module.failed.iter().map(|f| f.name.text.clone()).collect();
        let at = errors
            .iter()
            .map(|e| e.primary_span().expect("a span").start)
            .collect();
        (kept, failed, at)
    }

    #[test]
    fn recovers_from_an_unclosed_string_at_the_next_declaration() {
        let text =
            "def a : Nat := 1\n\ndef b : Str := \"oops\n  + 1\n\n-- about c\ndef c : Nat := 3\n";
        let (kept, failed, at) = recover(text);
        assert_eq!(kept, ["a", "c"]);
        assert_eq!(failed, ["b"]);
        assert_eq!(at, [text.find('"').unwrap() as u32]);
    }

    #[test]
    fn recovers_from_each_lexical_error_and_keeps_attributes_with_their_declaration() {
        let text = "def a : Nat := 1 # 2\n@[inline]\ndef b : Nat := 2\n@[inline]\ndef c : Nat := \t3\ndef d : Nat := 4\n";
        let (kept, failed, at) = recover(text);
        assert_eq!(kept, ["b", "d"]);
        assert_eq!(failed, ["a", "c"]);
        assert_eq!(at.len(), 2);
    }

    #[test]
    fn a_file_that_lexes_has_no_failures() {
        let mut sources = SourceMap::new();
        let text = "def a : Nat := 1\n";
        let file = sources.add("test.sw", text);
        let recovered = lex_recovering(file, text);
        assert!(recovered.failures.is_empty());
        assert_eq!(recovered.tokens.len(), lex(file, text).unwrap().len());
    }

    #[test]
    fn distinguishes_keywords_names_and_symbols() {
        assert_eq!(
            tokens(
                "type Type x Xs _ _y x' := : = -> [ ] ( ) , | + 42 - * / % != < <= > >= ! if then else"
            ),
            Ok(vec![
                Tok::KwType,
                Tok::TypeU,
                Tok::Lower("x".into()),
                Tok::Upper("Xs".into()),
                Tok::Underscore,
                Tok::Lower("_y".into()),
                Tok::Lower("x'".into()),
                Tok::ColonEq,
                Tok::Colon,
                Tok::Equals,
                Tok::Arrow,
                Tok::LBracket,
                Tok::RBracket,
                Tok::LParen,
                Tok::RParen,
                Tok::Comma,
                Tok::Pipe,
                Tok::Plus,
                Tok::Num(42u32.into()),
                Tok::Minus,
                Tok::Star,
                Tok::Slash,
                Tok::Percent,
                Tok::NotEq,
                Tok::Lt,
                Tok::Le,
                Tok::Gt,
                Tok::Ge,
                Tok::Bang,
                Tok::KwIf,
                Tok::KwThen,
                Tok::KwElse,
            ])
        );
    }

    #[test]
    fn a_question_mark_is_its_own_token() {
        assert_eq!(
            tokens("f ? x?"),
            Ok(vec![
                Tok::Lower("f".into()),
                Tok::Question,
                Tok::Lower("x".into()),
                Tok::Question,
            ])
        );
    }

    #[test]
    fn decimal_and_exponent_literals() {
        let float = |s: &str| Tok::Float(s.into());
        let num = |n: u32| Tok::Num(n.into());
        assert_eq!(
            tokens("1.5 80281.87 0.25 1e3 1.5e-7 2.0E21 3e+2 42"),
            Ok(vec![
                float("1.5"),
                float("80281.87"),
                float("0.25"),
                float("1e3"),
                float("1.5e-7"),
                float("2.0E21"),
                float("3e+2"),
                num(42),
            ])
        );
        // `..<` and `..=` are one token each; a spread stays `..`.
        assert_eq!(
            tokens("0..<n 1 ..= 2 [..xs] a .. b"),
            Ok(vec![
                num(0),
                Tok::DotDotLt,
                Tok::Lower("n".into()),
                num(1),
                Tok::DotDotEq,
                num(2),
                Tok::LBracket,
                Tok::DotDot,
                Tok::Lower("xs".into()),
                Tok::RBracket,
                Tok::Lower("a".into()),
                Tok::DotDot,
                Tok::Lower("b".into()),
            ])
        );
        // A digit is needed after `.` and in an exponent: ranges, spreads and
        // names are untouched.
        assert_eq!(
            tokens("1..n [x, ..rest] 5. 2e 2ex x.y List.map"),
            Ok(vec![
                num(1),
                Tok::DotDot,
                Tok::Lower("n".into()),
                Tok::LBracket,
                Tok::Lower("x".into()),
                Tok::Comma,
                Tok::DotDot,
                Tok::Lower("rest".into()),
                Tok::RBracket,
                num(5),
                Tok::Dot,
                num(2),
                Tok::Lower("e".into()),
                num(2),
                Tok::Lower("ex".into()),
                Tok::Lower("x".into()),
                Tok::Dot,
                Tok::Lower("y".into()),
                Tok::Lower("List.map".into()),
            ])
        );
    }

    #[test]
    fn a_number_right_after_a_dot_is_digits_only() {
        // `xs.0.1` stays `xs` `.` `0` `.` `1`, never `xs` `.` `0.1`
        // (docs/proposals/float.md §2.3), and `p.fst.snd` is unchanged.
        assert_eq!(
            tokens("xs.0.1 p.fst.snd x.1e3"),
            Ok(vec![
                Tok::Lower("xs".into()),
                Tok::Dot,
                Tok::Num(0u32.into()),
                Tok::Dot,
                Tok::Num(1u32.into()),
                Tok::Lower("p".into()),
                Tok::Dot,
                Tok::Lower("fst".into()),
                Tok::Dot,
                Tok::Lower("snd".into()),
                Tok::Lower("x".into()),
                Tok::Dot,
                Tok::Num(1u32.into()),
                Tok::Lower("e3".into()),
            ])
        );
    }

    #[test]
    fn skips_comments_but_not_arrows() {
        assert_eq!(
            tokens("a -- comment -> b\n-> c"),
            Ok(vec![
                Tok::Lower("a".into()),
                Tok::Arrow,
                Tok::Lower("c".into()),
            ])
        );
    }

    #[test]
    fn records_columns_for_layout() {
        let mut sources = SourceMap::new();
        let text = "f x\n  = y\n";
        let file = sources.add("test.sw", text);
        let columns: Vec<u32> = lex(file, text).unwrap().iter().map(|t| t.column).collect();
        assert_eq!(columns, vec![0, 2, 2, 4]);
    }

    #[test]
    fn rejects_tabs_and_unknown_characters() {
        assert_eq!(tokens("\tx"), Err("E-PARSE"));
        assert_eq!(tokens("a λ b"), Err("E-PARSE"));
        assert_eq!(tokens("a ⊆ b"), Err("E-PARSE"));
        assert_eq!(tokens("a # b"), Err("E-PARSE"));
        assert_eq!(
            tokens("a; b"),
            Ok(vec![
                Tok::Lower("a".into()),
                Tok::Semi,
                Tok::Lower("b".into())
            ])
        );
    }

    #[test]
    fn comparison_and_not_symbols() {
        assert_eq!(
            tokens("a>b a>=b !a a!=b a=>b x|>f a->b"),
            Ok(vec![
                Tok::Lower("a".into()),
                Tok::Gt,
                Tok::Lower("b".into()),
                Tok::Lower("a".into()),
                Tok::Ge,
                Tok::Lower("b".into()),
                Tok::Bang,
                Tok::Lower("a".into()),
                Tok::Lower("a".into()),
                Tok::NotEq,
                Tok::Lower("b".into()),
                Tok::Lower("a".into()),
                Tok::FatArrow,
                Tok::Lower("b".into()),
                Tok::Lower("x".into()),
                Tok::PipeGt,
                Tok::Lower("f".into()),
                Tok::Lower("a".into()),
                Tok::Arrow,
                Tok::Lower("b".into()),
            ])
        );
        // `>>` is two `>` tokens: the parser rejects them, and a later
        // composition operator can claim them.
        assert_eq!(
            tokens("a >> b"),
            Ok(vec![
                Tok::Lower("a".into()),
                Tok::Gt,
                Tok::Gt,
                Tok::Lower("b".into()),
            ])
        );
    }

    #[test]
    fn logic_operators_and_their_unicode_aliases() {
        let ascii =
            tokens("x in xs y !in ys p <-> q exists a forall b -> b && c || !d <= e >= f != g");
        let unicode = tokens("x ∈ xs y ∉ ys p ↔ q ∃ a ∀ b → b ∧ c ∨ ¬d ≤ e ≥ f ≠ g");
        assert_eq!(ascii, unicode);
        let toks = ascii.unwrap();
        for tok in [
            Tok::KwIn,
            Tok::NotIn,
            Tok::Iff,
            Tok::KwExists,
            Tok::KwForall,
        ] {
            assert!(toks.contains(&tok), "{tok:?}");
        }
        // Every alias is a token, and the table says what it stands for.
        for (alias, ascii) in UNICODE_ALIASES {
            assert_eq!(tokens(&alias.to_string()), tokens(ascii), "{alias}");
        }
    }

    #[test]
    fn not_in_and_iff_are_longest_matches() {
        let lower = |s: &str| Tok::Lower(s.into());
        // `!inside` is `!` and a name; `!in(` is `!in`.
        assert_eq!(tokens("!inside"), Ok(vec![Tok::Bang, lower("inside")]));
        assert_eq!(tokens("!in_"), Ok(vec![Tok::Bang, lower("in_")]));
        assert_eq!(tokens("x!in(y)").unwrap()[1], Tok::NotIn);
        // `<-` alone is still `<` and `-` (as in `rewrite <- h`).
        assert_eq!(tokens("<- h"), Ok(vec![Tok::Lt, Tok::Minus, lower("h")]));
        assert_eq!(tokens("p<->q").unwrap()[1], Tok::Iff);
        // `inside` is a name; `in` is a keyword.
        assert_eq!(tokens("inside in"), Ok(vec![lower("inside"), Tok::KwIn]));
    }

    #[test]
    fn exists_and_forall_after_a_dot_are_names() {
        let lower = |s: &str| Tok::Lower(s.into());
        assert_eq!(
            tokens("o.exists Option.exists exists"),
            Ok(vec![
                lower("o"),
                Tok::Dot,
                lower("exists"),
                lower("Option.exists"),
                Tok::KwExists
            ])
        );
        assert_eq!(
            tokens("o.forall forall"),
            Ok(vec![lower("o"), Tok::Dot, lower("forall"), Tok::KwForall])
        );
    }

    #[test]
    fn other_logic_symbols_say_what_to_write() {
        let note = |text: &str| {
            let mut sources = SourceMap::new();
            let file = sources.add("test.sw", text);
            let d = lex(file, text).expect_err("an error");
            d.notes.join(" ")
        };
        assert!(note("⇒").contains("`=>`"));
        assert!(note("⊆").contains("set operators"));
        assert!(note("≡").contains("write `=`"));
        // A symbol the table doesn't name lists the aliases.
        assert!(note("⊗").contains("`∈` for `in`"));
        // Other characters say nothing more.
        assert_eq!(note("é"), "");
    }

    #[test]
    fn character_and_string_literals_with_escapes() {
        assert_eq!(tokens("'a'"), Ok(vec![Tok::Char('a')]));
        assert_eq!(tokens("'é'"), Ok(vec![Tok::Char('é')]));
        assert_eq!(tokens("'\\''"), Ok(vec![Tok::Char('\'')]));
        assert_eq!(tokens("'\"'"), Ok(vec![Tok::Char('"')]));
        assert_eq!(tokens("'\\u{0}'"), Ok(vec![Tok::Char('\0')]));
        assert_eq!(tokens("'\\u{10FFFF}'"), Ok(vec![Tok::Char('\u{10FFFF}')]));
        assert_eq!(tokens("'\\u{d7ff}'"), Ok(vec![Tok::Char('\u{D7FF}')]));
        assert_eq!(tokens("'\\u{E000}'"), Ok(vec![Tok::Char('\u{E000}')]));
        assert_eq!(
            tokens(r#""a\n\t\\\"\'\u{1F600}b""#),
            Ok(vec![Tok::Str("a\n\t\\\"'\u{1F600}b".into())])
        );
        assert_eq!(
            tokens("a ++ b + +c"),
            Ok(vec![
                Tok::Lower("a".into()),
                Tok::PlusPlus,
                Tok::Lower("b".into()),
                Tok::Plus,
                Tok::Plus,
                Tok::Lower("c".into()),
            ])
        );
        // `'` inside a name is still part of the name.
        assert_eq!(
            tokens("x' 'y'"),
            Ok(vec![Tok::Lower("x'".into()), Tok::Char('y')])
        );
    }

    #[test]
    fn string_interpolation() {
        assert_eq!(
            tokens("\"a${x}b\""),
            Ok(vec![
                Tok::StrStart("a".into()),
                Tok::InterpOpen,
                Tok::Lower("x".into()),
                Tok::InterpClose,
                Tok::StrEnd("b".into()),
            ])
        );
        assert_eq!(
            tokens("\"a${x}b${y}c\""),
            Ok(vec![
                Tok::StrStart("a".into()),
                Tok::InterpOpen,
                Tok::Lower("x".into()),
                Tok::InterpClose,
                Tok::StrMid("b".into()),
                Tok::InterpOpen,
                Tok::Lower("y".into()),
                Tok::InterpClose,
                Tok::StrEnd("c".into()),
            ])
        );
        assert_eq!(
            tokens("\"${ {value = 1} }\""),
            Ok(vec![
                Tok::StrStart(String::new()),
                Tok::InterpOpen,
                Tok::LBrace,
                Tok::Lower("value".into()),
                Tok::Equals,
                Tok::Num(1u32.into()),
                Tok::RBrace,
                Tok::InterpClose,
                Tok::StrEnd(String::new()),
            ])
        );
        assert_eq!(
            tokens("\"${f \"x\"}\""),
            Ok(vec![
                Tok::StrStart(String::new()),
                Tok::InterpOpen,
                Tok::Lower("f".into()),
                Tok::Str("x".into()),
                Tok::InterpClose,
                Tok::StrEnd(String::new()),
            ])
        );
        assert_eq!(tokens("\"\\${x}\""), Ok(vec![Tok::Str("${x}".into())]));
        assert_eq!(tokens("\"${x\""), Err("E-PARSE"));
        assert_eq!(tokens("\"${x\ny}\""), Err("E-PARSE"));
    }

    /// Each token's source text, so a test can see which bytes it covers.
    fn pieces(text: &str) -> Vec<(Tok, &str)> {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        lex(file, text)
            .expect("lexes")
            .into_iter()
            .map(|t| (t.tok, &text[t.span.start as usize..t.span.end as usize]))
            .collect()
    }

    #[test]
    fn interpolation_delimiters_are_tokens_and_spans_are_their_text() {
        assert_eq!(
            pieces("\"a${x}b${y}c\""),
            vec![
                (Tok::StrStart("a".into()), "\"a"),
                (Tok::InterpOpen, "${"),
                (Tok::Lower("x".into()), "x"),
                (Tok::InterpClose, "}"),
                (Tok::StrMid("b".into()), "b"),
                (Tok::InterpOpen, "${"),
                (Tok::Lower("y".into()), "y"),
                (Tok::InterpClose, "}"),
                (Tok::StrEnd("c".into()), "c\""),
            ]
        );
    }

    #[test]
    fn interpolation_with_braces_inside() {
        assert_eq!(
            pieces("\"${ {a := 1}.a }\""),
            vec![
                (Tok::StrStart(String::new()), "\""),
                (Tok::InterpOpen, "${"),
                (Tok::LBrace, "{"),
                (Tok::Lower("a".into()), "a"),
                (Tok::ColonEq, ":="),
                (Tok::Num(1u32.into()), "1"),
                (Tok::RBrace, "}"),
                (Tok::Dot, "."),
                (Tok::Lower("a".into()), "a"),
                (Tok::InterpClose, "}"),
                (Tok::StrEnd(String::new()), "\""),
            ]
        );
    }

    #[test]
    fn back_to_back_interpolations_have_no_middle_text() {
        assert_eq!(
            tokens("\"${x}${y}\""),
            Ok(vec![
                Tok::StrStart(String::new()),
                Tok::InterpOpen,
                Tok::Lower("x".into()),
                Tok::InterpClose,
                Tok::InterpOpen,
                Tok::Lower("y".into()),
                Tok::InterpClose,
                Tok::StrEnd(String::new()),
            ])
        );
        assert_eq!(
            tokens("\"\"\"\n  ${x}${y}\n  \"\"\""),
            Ok(vec![
                Tok::StrStart(String::new()),
                Tok::InterpOpen,
                Tok::Lower("x".into()),
                Tok::InterpClose,
                Tok::InterpOpen,
                Tok::Lower("y".into()),
                Tok::InterpClose,
                Tok::StrEnd("\n".into()),
            ])
        );
    }

    #[test]
    fn rejects_malformed_literals() {
        for bad in [
            "''",
            "'ab'",
            "'a",
            "'\\q'",
            "'\\u{D800}'",
            "'\\u{DFFF}'",
            "'\\u{110000}'",
            "'\\u{}'",
            "'\\u{1234567}'",
            "'\\u41'",
            "'\\u{41'",
            "\"\\u{D800}\"",
            "\"\\x\"",
            "\"abc",
        ] {
            assert_eq!(tokens(bad), Err("E-PARSE"), "{bad}");
        }
    }

    #[test]
    fn numbers_can_be_any_size() {
        let huge = "99999999999999999999999999999999999999";
        assert_eq!(tokens(huge), Ok(vec![Tok::Num(huge.parse().unwrap())]));
    }

    fn block(text: &str) -> Result<String, &'static str> {
        match tokens(text)?.as_slice() {
            [Tok::Str(s)] => Ok(s.clone()),
            other => panic!("expected one text, got {other:?}"),
        }
    }

    #[test]
    fn text_block_removes_common_indentation() {
        assert_eq!(
            block("\"\"\"\n  a\n    b\n  c\n  \"\"\""),
            Ok("a\n  b\nc\n".into())
        );
        // The closing line's indentation counts too, so it can keep some.
        assert_eq!(block("\"\"\"\n    a\n  \"\"\""), Ok("  a\n".into()));
        assert_eq!(block("\"\"\"\na\n\"\"\""), Ok("a\n".into()));
    }

    #[test]
    fn text_block_trailing_newline_follows_the_closing_quotes() {
        assert_eq!(block("\"\"\"\n  a\n  b\"\"\""), Ok("a\nb".into()));
        assert_eq!(block("\"\"\"\n  a\n  b\n  \"\"\""), Ok("a\nb\n".into()));
        assert_eq!(block("\"\"\"\n  a\n\n  \"\"\""), Ok("a\n\n".into()));
        assert_eq!(block("\"\"\"\n\"\"\""), Ok("".into()));
    }

    #[test]
    fn text_block_blank_lines_do_not_count_for_indentation() {
        assert_eq!(
            block("\"\"\"\n    a\n\n  \n    b\n    \"\"\""),
            Ok("a\n\n\nb\n".into())
        );
    }

    #[test]
    fn text_block_keeps_quotes_and_reads_escapes() {
        assert_eq!(
            block("\"\"\"\n  say \"hi\" and \"\"x\"\"\n  \"\"\""),
            Ok("say \"hi\" and \"\"x\"\"\n".into())
        );
        assert_eq!(
            block("\"\"\"\n  a\\tb\\n\\u{41}\\$\n  \\\"\"\"\n  \"\"\""),
            Ok("a\tb\nA$\n\"\"\"\n".into())
        );
        // An escaped `\n` isn't a line, so it doesn't affect indentation.
        assert_eq!(block("\"\"\"\n  a\\nb\n  \"\"\""), Ok("a\nb\n".into()));
    }

    #[test]
    fn text_block_reads_crlf_as_lf() {
        assert_eq!(
            block("\"\"\"\r\n  a\r\n  b\r\n  \"\"\""),
            Ok("a\nb\n".into())
        );
    }

    #[test]
    fn text_block_interpolation() {
        assert_eq!(
            tokens("\"\"\"\n  a ${x} b\n    c ${f \"}\" '}' {}}\n  \"\"\""),
            Ok(vec![
                Tok::StrStart("a ".into()),
                Tok::InterpOpen,
                Tok::Lower("x".into()),
                Tok::InterpClose,
                Tok::StrMid(" b\n  c ".into()),
                Tok::InterpOpen,
                Tok::Lower("f".into()),
                Tok::Str("}".into()),
                Tok::Char('}'),
                Tok::LBrace,
                Tok::RBrace,
                Tok::InterpClose,
                Tok::StrEnd("\n".into()),
            ])
        );
    }

    #[test]
    fn text_block_errors() {
        for bad in [
            "\"\"\"x\"\"\"",
            "\"\"\"x\n  y\n\"\"\"",
            "\"\"\"\n  a",
            "\"\"\"",
            "\"\"\"\n\ta\n\"\"\"",
            "\"\"\"\n  ${f\n  x}\n\"\"\"",
            "\"\"\"\n  ${x\n\"\"\"",
            "\"\"\"\n  \\q\n\"\"\"",
        ] {
            assert_eq!(tokens(bad), Err("E-PARSE"), "{bad:?}");
        }
    }

    fn failure(text: &str) -> Diagnostic {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        lex(file, text).expect_err("doesn't lex")
    }

    // F1 of docs/reviews/code-review-syntax-opus.md: the `"""` pre-scan once
    // ended a `${…}` by its own rules, at a `}` the lexer read as part of a
    // literal, and the lexer then sliced the text backwards and panicked.
    #[test]
    fn text_block_interpolation_ends_where_the_lexer_says() {
        // `1'}'` is the number `1` and the character `'}'`.
        assert_eq!(
            tokens("def t: Text := \"\"\"\n  ${1'}' ++ \"${x}\"}\n  \"\"\""),
            Ok(vec![
                Tok::KwDef,
                Tok::Lower("t".into()),
                Tok::Colon,
                Tok::Upper("Text".into()),
                Tok::ColonEq,
                Tok::StrStart("".into()),
                Tok::InterpOpen,
                Tok::Num(1u32.into()),
                Tok::Char('}'),
                Tok::PlusPlus,
                Tok::StrStart("".into()),
                Tok::InterpOpen,
                Tok::Lower("x".into()),
                Tok::InterpClose,
                Tok::StrEnd("".into()),
                Tok::InterpClose,
                Tok::StrEnd("\n".into()),
            ])
        );
        // A nested interpolated text holding a `}` and a quote.
        assert_eq!(
            tokens("\"\"\"\n  ${\"${\"}\"}\"} ${y}\n  \"\"\""),
            Ok(vec![
                Tok::StrStart("".into()),
                Tok::InterpOpen,
                Tok::StrStart("".into()),
                Tok::InterpOpen,
                Tok::Str("}".into()),
                Tok::InterpClose,
                Tok::StrEnd("".into()),
                Tok::InterpClose,
                Tok::StrMid(" ".into()),
                Tok::InterpOpen,
                Tok::Lower("y".into()),
                Tok::InterpClose,
                Tok::StrEnd("\n".into()),
            ])
        );
        // A name ending in `'` doesn't start a character.
        assert_eq!(
            tokens("\"\"\"\n  ${x'} ${y}\n  \"\"\""),
            Ok(vec![
                Tok::StrStart("".into()),
                Tok::InterpOpen,
                Tok::Lower("x'".into()),
                Tok::InterpClose,
                Tok::StrMid(" ".into()),
                Tok::InterpOpen,
                Tok::Lower("y".into()),
                Tok::InterpClose,
                Tok::StrEnd("\n".into()),
            ])
        );
    }

    #[test]
    fn text_block_interpolation_errors_instead_of_panicking() {
        for bad in [
            // A comment runs to the end of the line, taking the `}`.
            "\"\"\"\n  ${x -- }\n  \"\"\"",
            // A `"""` text can't be in a one-line `${…}`.
            "\"\"\"\n  ${\"\"\"\n  x\n  \"\"\"}\n  \"\"\"",
            // Unclosed at the end of the file.
            "\"\"\"\n  ${x",
            "\"\"\"\n  ${\"${x",
            // A one-line text inside, unclosed.
            "\"\"\"\n  ${\"a}\n  \"\"\"",
        ] {
            assert_eq!(tokens(bad), Err("E-PARSE"), "{bad:?}");
        }
        assert!(
            failure("\"\"\"\n  ${\"\"\"\n  x\n  \"\"\"}\n  \"\"\"")
                .message
                .contains("stays on one line")
        );
    }

    // F6: a character that shows as nothing, or as a plain space, is named.
    #[test]
    fn invisible_characters_are_named() {
        for (text, shown) in [
            ("a\u{00A0}b", "U+00A0 NO-BREAK SPACE"),
            ("a\u{200B}b", "U+200B ZERO WIDTH SPACE"),
            ("a\u{2028}b", "U+2028 LINE SEPARATOR"),
            ("\u{FEFF}def x := 1", "U+FEFF ZERO WIDTH NO-BREAK SPACE"),
            ("a\u{202E}b", "U+202E"),
            ("a\u{0B}b", "U+000B"),
            ("a\u{85}b", "U+0085"),
            ("a\u{034F}b", "U+034F COMBINING GRAPHEME JOINER"),
            ("a\u{180E}b", "U+180E MONGOLIAN VOWEL SEPARATOR"),
            ("a\u{2061}b", "U+2061"),
            ("a\u{2062}b", "U+2062"),
            ("a\u{2063}b", "U+2063"),
            ("a\u{2064}b", "U+2064"),
            ("a\u{061C}b", "U+061C"),
            ("a\u{FFF9}b", "U+FFF9"),
            ("a\u{FFFA}b", "U+FFFA"),
            ("a\u{FFFB}b", "U+FFFB"),
            ("a\u{E0001}b", "U+E0001"),
            ("a\u{E0020}b", "U+E0020"),
            ("a\u{E007F}b", "U+E007F"),
        ] {
            let d = failure(text);
            assert_eq!(d.code, "E-PARSE");
            assert!(
                d.message
                    .starts_with(&format!("unexpected character {shown}")),
                "{text:?}: {}",
                d.message
            );
            assert!(!d.message.contains('`'), "{text:?}: {}", d.message);
        }
        assert!(failure("a\u{00A0}b").notes[0].contains("plain space"));
        assert!(failure("a\u{2061}b").notes[0].contains("delete it"));
        assert!(failure("a\u{061C}b").notes[0].contains("text-direction control"));
        assert_eq!(failure("a λ b").message, "unexpected character `λ`");
        assert_eq!(failure("a # b").message, "unexpected character `#`");
    }

    #[test]
    fn error_spans_point_at_the_problem() {
        // A comment in a `${…}` runs to the end of the line and takes the `}`,
        // so the comment is the problem, not the `${`.
        let text = "\"\"\"\n  ${x -- }\n  \"\"\"";
        let d = failure(text);
        assert_eq!(
            d.message,
            "a comment in a `${…}` runs to the end of the line, so it takes the `}`"
        );
        let span = d.primary_span().expect("a label");
        assert_eq!((span.start, span.end), (10, 14));
        assert_eq!(&text[span.start as usize..span.end as usize], "-- }");
        assert_eq!(d.labels[0].message, d.message);

        // A `${…}` that really does reach the newline spans from `${` to it.
        let text = "\"\"\"\n  ${f\n  x}\n  \"\"\"";
        let d = failure(text);
        assert_eq!(d.message, "a `${…}` in a `\"\"\"` text stays on one line");
        let span = d.primary_span().expect("a label");
        assert_eq!((span.start, span.end), (6, 9));
        assert_eq!(&text[span.start as usize..span.end as usize], "${f");

        // An invisible character's span is exactly the character.
        for ch in [
            '\u{2061}',
            '\u{2064}',
            '\u{034F}',
            '\u{180E}',
            '\u{061C}',
            '\u{FFF9}',
            '\u{FFFB}',
            '\u{E0001}',
            '\u{E0020}',
            '\u{E007F}',
        ] {
            let text = format!("a{ch}b");
            let d = failure(&text);
            let span = d.primary_span().expect("a label");
            assert_eq!(span.start, 1, "{ch:?}");
            assert_eq!(span.end, 1 + ch.len_utf8() as u32, "{ch:?}");
        }
    }

    #[test]
    fn text_block_keeps_later_columns_and_lines_right() {
        let mut sources = SourceMap::new();
        let text = "a \"\"\"\n  x\n  \"\"\" b\n  c";
        let file = sources.add("test.sw", text);
        let ts = lex(file, text).unwrap();
        let columns: Vec<u32> = ts.iter().map(|t| t.column).collect();
        assert_eq!(columns, vec![0, 2, 6, 2]);
        let fresh: Vec<bool> = ts.iter().map(|t| t.line_start).collect();
        assert_eq!(fresh, vec![true, false, false, true]);
    }

    fn trivia(text: &str) -> Lexed {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        lex_with_trivia(file, text).expect("lexes")
    }

    fn texts(comments: &[Comment]) -> Vec<&str> {
        comments.iter().map(|c| c.text.as_str()).collect()
    }

    #[test]
    fn trivia_comment_above_a_declaration() {
        let l = trivia("-- doc\ndef x := 1\n");
        assert_eq!(texts(&l.trivia[0].leading), vec!["-- doc"]);
        assert_eq!(l.trivia[0].leading[0].blank_lines_before, 0);
        assert_eq!(l.trivia[0].blank_lines_before, 0);
        assert!(l.trivia[1..].iter().all(|t| t == &Trivia::default()));
        assert_eq!(l.eof, Trivia::default());
        assert_eq!(l.trivia.len(), l.tokens.len());
    }

    #[test]
    fn trivia_blank_line_between_comment_and_code() {
        let l = trivia("-- a\n\n\ndef x := 1\n");
        assert_eq!(texts(&l.trivia[0].leading), vec!["-- a"]);
        assert_eq!(l.trivia[0].leading[0].blank_lines_before, 0);
        assert_eq!(l.trivia[0].blank_lines_before, 2);
    }

    #[test]
    fn trivia_trailing_comment_attaches_to_last_token_of_the_line() {
        let l = trivia("def x := 1 -- one\ndef y := 2\n");
        let one = l.trivia.iter().position(|t| t.trailing.is_some()).unwrap();
        assert_eq!(l.tokens[one].tok, Tok::Num(1u32.into()));
        let c = l.trivia[one].trailing.as_ref().unwrap();
        assert_eq!(c.text, "-- one");
        assert_eq!(c.column, 11);
        assert_eq!(l.trivia.iter().filter(|t| t.trailing.is_some()).count(), 1);
        // The next line's first token has no leading comment.
        assert!(l.trivia[one + 1].leading.is_empty());
    }

    #[test]
    fn trivia_several_comments_in_a_row() {
        let l = trivia("x\n-- a\n-- b\n\n-- c\n  -- d\n\ny\n");
        let y = &l.trivia[1];
        assert_eq!(texts(&y.leading), vec!["-- a", "-- b", "-- c", "-- d"]);
        let blanks: Vec<u32> = y.leading.iter().map(|c| c.blank_lines_before).collect();
        assert_eq!(blanks, vec![0, 0, 1, 0]);
        assert_eq!(y.leading[3].column, 2);
        assert_eq!(y.blank_lines_before, 1);
    }

    #[test]
    fn trivia_at_end_of_file() {
        let l = trivia("x -- t\n\n-- a\n-- b\n\n");
        assert_eq!(l.trivia[0].trailing.as_ref().unwrap().text, "-- t");
        assert_eq!(texts(&l.eof.leading), vec!["-- a", "-- b"]);
        assert_eq!(l.eof.leading[0].blank_lines_before, 1);
        assert_eq!(l.eof.blank_lines_before, 1);
        assert_eq!(l.eof.trailing, None);
        // Only blank lines, and no final newline.
        let l = trivia("x\n\n\n");
        assert_eq!(l.eof.blank_lines_before, 2);
        let l = trivia("x\n-- last");
        assert_eq!(texts(&l.eof.leading), vec!["-- last"]);
        // A file of only comments.
        let l = trivia("\n-- only\n");
        assert!(l.tokens.is_empty());
        assert_eq!(l.eof.leading[0].blank_lines_before, 1);
    }

    #[test]
    fn trivia_dashes_in_literals_are_not_comments() {
        let l =
            trivia("\"a -- b\" 'x'\n\"\"\"\n  -- not a comment\n\n  also\n\"\"\"\n\"p${x}--q\"\n");
        assert!(l.trivia.iter().all(|t| t == &Trivia::default()));
        assert_eq!(l.eof, Trivia::default());
        assert!(matches!(&l.tokens[0].tok, Tok::Str(s) if s == "a -- b"));
        // Blank lines inside a text block aren't counted for the next token.
        assert_eq!(l.trivia[2].blank_lines_before, 0);
    }

    #[test]
    fn trivia_arrows_near_dashes() {
        let l = trivia("a -> b --> c\n-> d --\ne-->f\n");
        let toks: Vec<Tok> = l.tokens.iter().map(|t| t.tok.clone()).collect();
        assert_eq!(
            toks,
            vec![
                Tok::Lower("a".into()),
                Tok::Arrow,
                Tok::Lower("b".into()),
                Tok::Arrow,
                Tok::Lower("d".into()),
                Tok::Lower("e".into()),
            ]
        );
        assert_eq!(l.trivia[2].trailing.as_ref().unwrap().text, "--> c");
        assert_eq!(l.trivia[4].trailing.as_ref().unwrap().text, "--");
        assert_eq!(l.trivia[5].trailing.as_ref().unwrap().text, "-->f");
    }

    #[test]
    fn trivia_counts_blank_lines_with_spaces_and_crlf() {
        let l = trivia("x\r\n  \r\n\r\n-- c\r\ny\r\n");
        assert_eq!(l.trivia[1].leading[0].text, "-- c");
        assert_eq!(l.trivia[1].leading[0].blank_lines_before, 2);
        assert_eq!(l.trivia[1].blank_lines_before, 0);
        // Blank lines between tokens with no comment.
        let l = trivia("x\n\n\ny z\n\nw");
        assert_eq!(
            l.trivia
                .iter()
                .map(|t| t.blank_lines_before)
                .collect::<Vec<_>>(),
            vec![0, 2, 0, 1]
        );
    }
}
