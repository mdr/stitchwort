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
    /// The text before `${` in an interpolated string: `"a${x}"`.
    StrStart(String),
    /// The text between a `}` and the next `${` in an interpolated string.
    StrMid(String),
    /// The text after the last `}` in an interpolated string.
    StrEnd(String),
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
    KwIf,
    KwThen,
    KwElse,
    /// `ability Name params where`, then its operations.
    KwAbility,
    KwWhere,
    /// `handle e with | clause …`
    KwHandle,
    KwWith,
    /// `match e with | p -> …`
    KwMatch,
    /// `return x -> …`, a handler's clause for the result.
    KwReturn,
    /// `let x = e`, binding `x` for the following lines of a block.
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
    /// `split` or `split in t`: a proof by automatic case splitting
    /// (docs/proposals/simp.md §5).
    KwSplit,
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
    /// `=>`, in a handler clause: `get () => k -> …`.
    FatArrow,
    Underscore,
    /// `?`: an open goal, a part of a proof or program still to write
    /// (docs/proposals/lsp-goal-holes.md).
    Question,
    /// `.`, in field access: `p.name`.
    Dot,
    /// `..`, the rest of a record pattern: `{ name, .. }`.
    DotDot,
    /// `@`, always followed by `[`: `@[js.name "X"]` writes attributes
    /// (docs/syntax.md, Attributes). The `[` is an ordinary [`Tok::LBracket`].
    At,
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
}

/// The tokens of `text`, without comments.
pub fn lex(file: FileId, text: &str) -> Result<Vec<Token>, Diagnostic> {
    lex_keeping(file, text, false).map(|lexed| lexed.tokens)
}

/// The tokens of `text` with the comments and blank lines around each. A
/// `--` inside a string or text literal is part of the literal, not a comment.
pub fn lex_with_trivia(file: FileId, text: &str) -> Result<Lexed, Diagnostic> {
    lex_keeping(file, text, true)
}

/// Lexes `text`, recording the trivia only if `keep_trivia` (otherwise
/// `trivia` and `eof` are empty). Only the formatter needs it, and it takes
/// more memory than the tokens, so checking doesn't record it.
fn lex_keeping(file: FileId, text: &str, keep_trivia: bool) -> Result<Lexed, Diagnostic> {
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
    let mut i = 0;
    let mut line_start = 0;
    let mut fresh_line = true;
    let mut interps: Vec<Interp> = Vec::new();

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
                    ..
                }) = interps.last()
                {
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
                if !keep_trivia {
                    continue;
                }
                let end = if bytes[start..i].ends_with(b"\r") {
                    i - 1
                } else {
                    i
                };
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
                    "type" => Tok::KwType,
                    "theorem" => Tok::KwTheorem,
                    "def" => Tok::KwDef,
                    "export" => Tok::KwExport,
                    "test" => Tok::KwTest,
                    "interface" => Tok::KwInterface,
                    "instance" => Tok::KwInstance,
                    "if" => Tok::KwIf,
                    "then" => Tok::KwThen,
                    "else" => Tok::KwElse,
                    "ability" => Tok::KwAbility,
                    "where" => Tok::KwWhere,
                    "handle" => Tok::KwHandle,
                    "with" => Tok::KwWith,
                    "match" => Tok::KwMatch,
                    "return" => Tok::KwReturn,
                    "let" => Tok::KwLet,
                    "import" => Tok::KwImport,
                    "include" => Tok::KwInclude,
                    "namespace" => Tok::KwNamespace,
                    "calc" => Tok::KwCalc,
                    "rewrite" => Tok::KwRewrite,
                    "omega" => Tok::KwOmega,
                    "ring" => Tok::KwRing,
                    // After a `.`, a field or a dot call: `line.split ','`.
                    "split" if !(start > 0 && bytes[start - 1] == b'.') => Tok::KwSplit,
                    "decreasing" => Tok::KwDecreasing,
                    "opaque" => Tok::KwOpaque,
                    "unfolding" => Tok::KwUnfolding,
                    "in" => Tok::KwIn,
                    // After a `.`, a field or a dot call: `x.exists p`.
                    "exists" if !(start > 0 && bytes[start - 1] == b'.') => Tok::KwExists,
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
            let (chars, stop, interpolation, rest) = if block {
                let mut segs = scan_block(file, text, i)?;
                let (chars, stop, interpolation) = segs.pop_front().expect("a block has a piece");
                (chars, stop, interpolation, Some(segs))
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
                interps.push(Interp {
                    depth: 0,
                    start,
                    block: rest,
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
                let text_start = i;
                let (chars, stop, interpolation) = match &mut interp.block {
                    Some(pieces) => pieces.pop_front().expect("a block's last piece closes it"),
                    None => scan_string(file, text, i, interp.start)?,
                };
                let close_len = if interp.block.is_some() { 3 } else { 1 };
                let tok = if interpolation {
                    i = stop + 2;
                    Tok::StrMid(chars)
                } else {
                    i = stop + close_len;
                    Tok::StrEnd(chars)
                };
                tokens.push(Token {
                    tok,
                    span: Span::new(file, text_start as u32, i as u32),
                    column,
                    line_start: fresh_line,
                });
                if let Some(newline) = text[text_start..stop].rfind('\n') {
                    line_start = text_start + newline + 1;
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
                        format!("unexpected character `{}`", c as char),
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
    Ok(Lexed {
        tokens,
        trivia,
        eof: Trivia {
            leading: pending,
            blank_lines_before: blank_run,
            trailing: None,
        },
    })
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
}

/// A piece of a literal's text: the text, the position of the `${` or the
/// closing `"""` after it, and whether it was a `${`.
type Piece = (String, usize, bool);

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
                let dollar = i;
                i += 2;
                let mut depth = 0;
                loop {
                    match bytes.get(i) {
                        None => return Err(unclosed()),
                        Some(b'\n') => {
                            return Err(error(
                                file,
                                dollar,
                                i,
                                "a `${…}` in a `\"\"\"` text stays on one line",
                            ));
                        }
                        Some(b'{') => depth += 1,
                        Some(b'}') if depth == 0 => break,
                        Some(b'}') => depth -= 1,
                        Some(&quote @ (b'"' | b'\''))
                            if quote == b'"'
                                || !(bytes[i - 1].is_ascii_alphanumeric()
                                    || bytes[i - 1] == b'_'
                                    || bytes[i - 1] == b'\'') =>
                        {
                            // A one-line text or character literal: skip to
                            // its end, since it may hold a `}`.
                            i += 1;
                            while let Some(&b) = bytes.get(i) {
                                if b == quote || b == b'\n' {
                                    break;
                                }
                                i += if b == b'\\' { 2 } else { 1 };
                            }
                            if bytes.get(i) != Some(&quote) {
                                continue;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
                interps.push((dollar, i));
                i += 1;
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
                    pieces.push_back((std::mem::take(&mut chars), j, true));
                    j = interps[next_interp].1 + 1;
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
    pieces.push_back((chars, close, false));
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
        _ => return None,
    })
}

/// Symbols from logic and mathematics that aren't aliases, with what to
/// write instead (D1208).
const UNSUPPORTED: &[(char, &str)] = &[
    ('∀', "\"for all\" is a function type: write `(x: T) -> P`"),
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
    let d = error(file, start, end, format!("unexpected character `{ch}`"));
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
        assert_eq!(tokens("a ∀ b"), Err("E-PARSE"));
        assert_eq!(tokens("a ⊆ b"), Err("E-PARSE"));
        assert_eq!(tokens("a ; b"), Err("E-PARSE"));
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
        let ascii = tokens("x in xs y !in ys p <-> q exists a -> b && c || !d <= e >= f != g");
        let unicode = tokens("x ∈ xs y ∉ ys p ↔ q ∃ a → b ∧ c ∨ ¬d ≤ e ≥ f ≠ g");
        assert_eq!(ascii, unicode);
        let toks = ascii.unwrap();
        for tok in [Tok::KwIn, Tok::NotIn, Tok::Iff, Tok::KwExists] {
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
    fn exists_after_a_dot_is_a_name() {
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
    }

    #[test]
    fn other_logic_symbols_say_what_to_write() {
        let note = |text: &str| {
            let mut sources = SourceMap::new();
            let file = sources.add("test.sw", text);
            let d = lex(file, text).expect_err("an error");
            d.notes.join(" ")
        };
        assert!(note("∀").contains("(x: T) -> P"));
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
                Tok::Lower("x".into()),
                Tok::StrEnd("b".into()),
            ])
        );
        assert_eq!(
            tokens("\"a${x}b${y}c\""),
            Ok(vec![
                Tok::StrStart("a".into()),
                Tok::Lower("x".into()),
                Tok::StrMid("b".into()),
                Tok::Lower("y".into()),
                Tok::StrEnd("c".into()),
            ])
        );
        assert_eq!(
            tokens("\"${ {value = 1} }\""),
            Ok(vec![
                Tok::StrStart(String::new()),
                Tok::LBrace,
                Tok::Lower("value".into()),
                Tok::Equals,
                Tok::Num(1u32.into()),
                Tok::RBrace,
                Tok::StrEnd(String::new()),
            ])
        );
        assert_eq!(
            tokens("\"${f \"x\"}\""),
            Ok(vec![
                Tok::StrStart(String::new()),
                Tok::Lower("f".into()),
                Tok::Str("x".into()),
                Tok::StrEnd(String::new()),
            ])
        );
        assert_eq!(tokens("\"\\${x}\""), Ok(vec![Tok::Str("${x}".into())]));
        assert_eq!(tokens("\"${x\""), Err("E-PARSE"));
        assert_eq!(tokens("\"${x\ny}\""), Err("E-PARSE"));
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
                Tok::Lower("x".into()),
                Tok::StrMid(" b\n  c ".into()),
                Tok::Lower("f".into()),
                Tok::Str("}".into()),
                Tok::Char('}'),
                Tok::LBrace,
                Tok::RBrace,
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
