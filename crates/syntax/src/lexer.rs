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
    /// `type`, which starts a data type declaration.
    KwType,
    KwTheorem,
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
    Minus,
    Star,
    Slash,
    Percent,
    /// `!=`
    NotEq,
    Lt,
    /// `<=`
    Le,
    KwIf,
    KwThen,
    KwElse,
    Underscore,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
    /// Byte offset from the start of the line. Declarations start at column 0.
    pub column: u32,
}

pub fn lex(file: FileId, text: &str) -> Result<Vec<Token>, Diagnostic> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    let mut line_start = 0;

    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b'\n' => {
                i += 1;
                line_start = i;
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
            let word = &text[start..i];
            match word {
                "_" => Tok::Underscore,
                "type" => Tok::KwType,
                "theorem" => Tok::KwTheorem,
                "export" => Tok::KwExport,
                "test" => Tok::KwTest,
                "if" => Tok::KwIf,
                "then" => Tok::KwThen,
                "else" => Tok::KwElse,
                "Type" => Tok::TypeU,
                "Prop" => Tok::Prop,
                _ if c.is_ascii_uppercase() => Tok::Upper(word.to_string()),
                _ => Tok::Lower(word.to_string()),
            }
        } else if c.is_ascii_digit() {
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let n = text[start..i]
                .parse()
                .expect("a run of ASCII digits is a valid number");
            Tok::Num(n)
        } else if c == b'"' {
            i += 1;
            let mut text = String::new();
            loop {
                match bytes.get(i) {
                    None | Some(b'\n') => {
                        return Err(error(file, start, i, "this string isn't closed with `\"`"));
                    }
                    Some(b'"') => {
                        i += 1;
                        break;
                    }
                    Some(b'\\') if matches!(bytes.get(i + 1), Some(b'"' | b'\\')) => {
                        text.push(bytes[i + 1] as char);
                        i += 2;
                    }
                    Some(_) => {
                        let ch = std::str::from_utf8(&bytes[i..])
                            .ok()
                            .and_then(|s| s.chars().next());
                        let ch = ch.unwrap_or('\u{fffd}');
                        text.push(ch);
                        i += ch.len_utf8();
                    }
                }
            }
            Tok::Str(text)
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
                b']' => Tok::RBracket,
                b',' => Tok::Comma,
                b':' if bytes.get(i) == Some(&b'=') => {
                    i += 1;
                    Tok::ColonEq
                }
                b':' => Tok::Colon,
                b'=' => Tok::Equals,
                b'\\' => Tok::Backslash,
                b'|' => Tok::Pipe,
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
        });
    }
    Ok(tokens)
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
    fn numbers_can_be_any_size() {
        let huge = "99999999999999999999999999999999999999";
        assert_eq!(tokens(huge), Ok(vec![Tok::Num(huge.parse().unwrap())]));
    }
}
