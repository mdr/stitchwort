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
    /// A string literal, used for test names: `"reverse twice"`.
    Str(String),
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
    Backslash,
    Pipe,
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
    LBrace,
    RBrace,
    /// `=>`, in a handler clause: `get () => k -> …`.
    FatArrow,
    Underscore,
    /// `.`, in field access: `p.name`.
    Dot,
    /// `..`, the rest of a record pattern: `{ name, .. }`.
    DotDot,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
    /// Byte offset from the start of the line. Declarations start at column 0.
    pub column: u32,
    /// Whether this is the first token on its line. Blocks use this to find
    /// where each line starts.
    pub line_start: bool,
}

pub fn lex(file: FileId, text: &str) -> Result<Vec<Token>, Diagnostic> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    let mut line_start = 0;
    let mut fresh_line = true;

    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b'\n' => {
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
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
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
            let n = text[start..i]
                .parse()
                .expect("a run of ASCII digits is a valid number");
            Tok::Num(n)
        } else if c == b'"' || c == b'\'' {
            let quote = c;
            i += 1;
            let mut chars = String::new();
            loop {
                match bytes.get(i) {
                    None | Some(b'\n') => {
                        let what = if quote == b'"' { "string" } else { "character" };
                        let q = quote as char;
                        return Err(error(
                            file,
                            start,
                            i,
                            format!("this {what} isn't closed with `{q}`"),
                        ));
                    }
                    Some(&b) if b == quote => {
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
            if quote == b'"' {
                Tok::Str(chars)
            } else {
                let mut it = chars.chars();
                match (it.next(), it.next()) {
                    (Some(ch), None) => Tok::Char(ch),
                    _ => {
                        return Err(error(
                            file,
                            start,
                            i,
                            "a character literal holds exactly one character",
                        ));
                    }
                }
            }
        } else if !c.is_ascii() {
            let ch = text[start..].chars().next().expect("non-empty");
            let end = start + ch.len_utf8();
            return Err(error(
                file,
                start,
                end,
                format!("unexpected character `{ch}`"),
            ));
        } else {
            i += 1;
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
                b'\\' => Tok::Backslash,
                b'|' => Tok::Pipe,
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
                b'<' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::Le
                }
                b'<' => Tok::Lt,
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
    Ok(tokens)
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
            "unknown escape: use `\\n`, `\\t`, `\\r`, `\\\\`, `\\\"`, `\\'` or `\\u{…}`",
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
                "type Type x Xs _ _y x' := : = -> [ ] ( ) , | + \\ 42 - * / % != < <= if then else"
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
                Tok::Backslash,
                Tok::Num(42u32.into()),
                Tok::Minus,
                Tok::Star,
                Tok::Slash,
                Tok::Percent,
                Tok::NotEq,
                Tok::Lt,
                Tok::Le,
                Tok::KwIf,
                Tok::KwThen,
                Tok::KwElse,
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
        assert_eq!(tokens("a ∧ b"), Err("E-PARSE"));
        assert_eq!(tokens("a ; b"), Err("E-PARSE"));
        assert_eq!(tokens("a ! b"), Err("E-PARSE"));
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
}
