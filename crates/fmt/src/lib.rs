//! The Stitchwort formatter (docs/proposals/formatter-style.md).
//!
//! [`format`] prints a file from its lossless syntax tree, choosing every
//! line break itself, in 120 columns ([`printer`]). It refuses a file with
//! any lexical or syntax error (D1021). It checks each declaration it
//! prints, and the whole file: the same tokens (up to the deliberate
//! rewrites), the same comments on the same tokens, the same syntax tree. A
//! declaration that fails stays as written and is counted in [`Stats`]; a
//! file that fails is [`Error::Internal`] and the caller keeps it as it was.

#[cfg(test)]
use stitchwort_test_alloc as _;

mod check;
pub mod printer;
mod spacing;

use stitchwort_syntax::{Diagnostic, FileId, SourceMap, Tok, Token};

/// Why a file wasn't formatted.
#[derive(Debug)]
pub enum Error {
    /// The file has a lexical or syntax error: these are the diagnostics.
    Refused(Vec<Diagnostic>),
    /// A formatter bug: the output wasn't the same program, so the file is
    /// left unchanged. The message names the first difference.
    Internal(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Refused(diagnostics) => {
                let messages: Vec<&str> = diagnostics.iter().map(|d| d.message.as_str()).collect();
                write!(f, "not formatted: {}", messages.join("; "))
            }
            Error::Internal(message) => {
                write!(
                    f,
                    "formatter bug: output differs, file left unchanged: {message}"
                )
            }
        }
    }
}

impl std::error::Error for Error {}

/// How much of a file the rules didn't cover.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Declarations in the file.
    pub decls: usize,
    /// Declarations left exactly as written, because their formatted text
    /// failed a check (the rest of the file is formatted).
    pub verbatim_decls: usize,
    /// Syntax nodes printed as written because no rule covers their kind.
    pub unruled_nodes: usize,
}

/// A formatted file and what its formatting didn't cover.
#[derive(Clone, Debug)]
pub struct Formatted {
    pub text: String,
    pub stats: Stats,
}

/// Formats a whole file.
pub fn format(text: &str) -> Result<String, Error> {
    format_with_stats(text).map(|formatted| formatted.text)
}

/// Like [`format`], with the counts of what the rules didn't cover.
pub fn format_with_stats(text: &str) -> Result<Formatted, Error> {
    let file = SourceMap::new().add("input.sw", text);
    format_in(file, text)
}

/// Like [`format_with_stats`], with `file` in the diagnostics of a refused
/// file.
pub fn format_in(file: FileId, text: &str) -> Result<Formatted, Error> {
    let printed = printer::format_tree_in(file, text)?;
    Ok(Formatted {
        text: printed.text,
        stats: Stats {
            decls: printed.stats.decls,
            verbatim_decls: printed.stats.verbatim_decls(),
            unruled_nodes: printed.stats.unruled.values().sum(),
        },
    })
}

/// D3472: a theorem with explicit parameters says `∀` before them,
/// `theorem leTrans ∀ (a b c: Nat) (h: a ≤ b): …`. It is cosmetic (the
/// parser reads the same tree either way), so the formatter writes it, and
/// leaves it off a header whose parameters are all implicit, which says
/// nothing is quantified over by name. Returns the text with it added, or
/// `None` if nothing needed it.
pub(crate) fn insert_theorem_foralls(text: &str, tokens: &[Token]) -> Option<String> {
    let mut insertions: Vec<(usize, &str)> = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        if token.tok != Tok::KwTheorem {
            continue;
        }
        // The name is one token, qualified or not.
        let Some(first) = tokens.get(i + 2) else {
            continue;
        };
        if first.tok == Tok::KwForall {
            continue;
        }
        let mut depth = 0i32;
        let mut explicit = false;
        let mut has_colon = false;
        for t in &tokens[i + 2..] {
            match t.tok {
                Tok::LParen => {
                    explicit |= depth == 0;
                    depth += 1;
                }
                Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Colon if depth == 0 => {
                    has_colon = true;
                    break;
                }
                Tok::ColonEq | Tok::Pipe if depth == 0 => break,
                _ => {}
            }
        }
        if !(explicit && has_colon) {
            continue;
        }
        // Before the first parameter when it is on the name's line, else
        // at the end of the name's line.
        let name = &tokens[i + 1];
        if first.line_start {
            insertions.push((name.span.end as usize, " ∀"));
        } else {
            insertions.push((first.span.start as usize, "∀ "));
        }
    }
    if insertions.is_empty() {
        return None;
    }
    let mut out = text.to_string();
    for (at, piece) in insertions.into_iter().rev() {
        out.insert_str(at, piece);
    }
    Some(out)
}
