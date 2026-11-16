//! The Stitchwort formatter (docs/proposals/formatter-style.md).
//!
//! [`format`] prints a file from its lossless syntax tree, choosing every
//! line break itself, in 120 columns ([`printer`]). It refuses a file with
//! any lexical or syntax error (D1021). It checks the whole file it prints:
//! the same tokens (the tidy passes' rewrites aside), the same comments on
//! the same tokens, the same syntax tree. A file that fails is
//! [`Error::Internal`] and the caller keeps it as it was.

#[cfg(test)]
use stitchwort_test_alloc as _;

mod check;
mod merge;
mod parens;
pub mod passes;
pub mod printer;
mod spacing;
pub mod tidy;

use stitchwort_syntax::{Diagnostic, FileId, SourceMap};

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

/// Paths (prefixes, or whole files) the formatter leaves alone, relative to
/// the repository root: the Stitchwort repository deliberately keeps these
/// as written, and their exact text and error positions are tested (D1019).
/// `stitchwort fmt DIR` skips them, and `crates/cli/tests/tools/fmt_repo.rs`
/// uses the same list, so the two can't drift apart.
pub const DELIBERATELY_UNFORMATTED: [&str; 10] = [
    // D1019: files that exist to be rejected.
    "examples/reject/",
    "examples/soundness/",
    "examples/projects/reject/",
    // Repros of spellings the parser rejects (SW-1599).
    "dev/repros/sw-1599/spelled-iff.sw",
    "dev/repros/sw-1599/spelled-iff2.sw",
    // Bug repros kept exactly as found (fuzz cases may not even parse).
    "docs/repros/",
    "docs/reviews/repros/",
    "dev/fuzz-findings/",
    // Formatter test data.
    "crates/fmt/tests/it/golden/",
    // Exercises layouts the formatter normalises.
    "examples/accept/list-literal-layout.sw",
];

/// Formats a whole file.
pub fn format(text: &str) -> Result<String, Error> {
    let file = SourceMap::new().add("input.sw", text);
    format_in(file, text)
}

/// Like [`format`], with `file` in the diagnostics of a refused file.
pub fn format_in(file: FileId, text: &str) -> Result<String, Error> {
    printer::format_tree_in(file, text).map(|printed| printed.text)
}
