//! The Stitchwort formatter (docs/proposals/formatter.md).
//!
//! [`format`] rewrites a file's layout (indentation, spacing, blank lines)
//! and keeps every token, every comment and every line break the author
//! chose. It refuses a file with any lexical or syntax error (D1021). Before
//! returning, it lexes and parses its own output and checks that the result
//! is the same program (§4.1); if not, it returns [`Error::Internal`] and the
//! caller keeps the file as it was.
//!
//! Every construct has a rule (stage F2): lines are indented from the line
//! they continue, brackets that span lines get the D1012 layout, and spacing
//! follows R3 to R6. [`Stats`] counts what a rule still doesn't decide.

mod check;
pub mod doc;
mod layout;
mod spacing;

use stitchwort_syntax::{
    DEFAULT_STACK, Diagnostic, FileId, SourceMap, decl_ranges, equivalence, lex_with_trivia,
    parse_module_within,
};

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

/// How much of a file the rules didn't cover yet.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Lines whose indentation no rule decided: each kept its distance from
    /// the line above it that it continues. Always 0 since F2.
    pub copied_lines: usize,
    /// Gaps between two tokens on a line whose spacing no rule decided:
    /// copied from the source (several spaces becoming one).
    pub copied_gaps: usize,
    /// Declarations whose brackets were not converted to D1012, because the
    /// converted text failed the checks (the rest of the declaration is
    /// formatted).
    pub unconverted_decls: usize,
    /// Declarations copied exactly as written, because their formatted text
    /// failed the checks.
    pub verbatim_decls: usize,
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
    let lexed = lex_with_trivia(file, text).map_err(|d| Error::Refused(vec![d]))?;
    let module = parse_module_within(file, text, DEFAULT_STACK).map_err(Error::Refused)?;
    let mut decls = decl_ranges(&lexed.tokens).map_err(|d| Error::Refused(vec![d]))?;
    // Tokens before the first split (a file that starts with `:=` at column
    // 0, which the parser skips) belong to no range: they form one of their
    // own, so none is dropped.
    let first = decls
        .first()
        .map_or(lexed.tokens.len(), |range| range.start);
    if first > 0 {
        decls.insert(0, 0..first);
    }
    let mut layout = layout::Layout::new(text, &lexed);
    let output = layout.file(&decls);
    let stats = layout.stats;

    // §4.1, on the whole file.
    let check = || -> Result<(), String> {
        let lexed_after = lex_with_trivia(file, &output)
            .map_err(|d| format!("the output doesn't lex: {}", d.message))?;
        check::same_tokens(text, &lexed, &output, &lexed_after)?;
        check::same_comments(&lexed, &lexed_after)?;
        let after = parse_module_within(file, &output, DEFAULT_STACK).map_err(|errors| {
            let first = errors.first().map_or("", |d| d.message.as_str());
            format!("the output doesn't parse: {first}")
        })?;
        if equivalence::shape(&module) != equivalence::shape(&after) {
            return Err("the output parses to a different syntax tree".into());
        }
        Ok(())
    };
    check().map_err(Error::Internal)?;
    Ok(Formatted {
        text: output,
        stats,
    })
}
