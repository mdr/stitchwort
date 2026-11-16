//! The tree printer: the formatter that chooses every line break, from the
//! lossless syntax tree (docs/proposals/formatter-architecture.md, stage 2;
//! the house style is docs/proposals/formatter-style.md). [`crate::format`]
//! is this printer; `stitchwort dev fmt-tree` reports on it over a tree of
//! files.
//!
//! Each declaration is turned into a layout document by the rule for each
//! construct ([`rules`]) and printed in 120 columns ([`engine`]). The whole
//! printed file must have the tokens of the file after the tidy passes
//! ([`crate::passes`], which include D2307's dropped brackets and D3565's
//! merged parameters) with its comments attached to the same tokens, the
//! original file's comments, and parse to the original's tree up to the
//! passes' changes ([`crate::same_program`]); a file that doesn't is
//! [`Error::Internal`] and the caller keeps it as it was, so a bug in the
//! rules is never a wrong program on disk. [`gate`] runs the same checks and
//! also that formatting twice changes nothing.

pub mod engine;
mod rules;

use stitchwort_syntax::tree::NodeKind;
use stitchwort_syntax::{
    DEFAULT_STACK, Diagnostic, FileId, Lexed, SourceMap, Tok, lex_with_trivia, parse_module_within,
};

use crate::{Error, check};

/// The width lines are fitted to (D1014).
pub const WIDTH: usize = 120;

/// What the tree printer did with a file.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TreeStats {
    pub decls: usize,
    /// Parameter groups made by merging parameters of one type (D3565).
    pub merged_groups: usize,
}

impl TreeStats {
    pub fn add(&mut self, other: &TreeStats) {
        self.decls += other.decls;
        self.merged_groups += other.merged_groups;
    }
}

/// A file printed by the tree printer.
#[derive(Clone, Debug)]
pub struct TreeFormatted {
    pub text: String,
    pub stats: TreeStats,
}

/// Formats a whole file with the tree printer, checking the result as
/// [`gate`] does; a result that fails is [`Error::Internal`].
pub fn format_tree(text: &str) -> Result<TreeFormatted, Error> {
    let file = SourceMap::new().add("input.sw", text);
    format_tree_in(file, text)
}

/// Like [`format_tree`], with `file` in the diagnostics of a refused file.
pub fn format_tree_in(file: FileId, text: &str) -> Result<TreeFormatted, Error> {
    format_with_passes(file, text, &crate::passes::PASSES)
}

/// Like [`format_tree_in`], with `passes` for the tidy passes: tests give
/// it a wrong pass to see the checks refuse what it does.
fn format_with_passes(
    file: FileId,
    text: &str,
    passes: &[crate::passes::Pass],
) -> Result<TreeFormatted, Error> {
    let printed = print_file(file, text, passes)?;
    check_file(file, text, &printed.input, &printed.text).map_err(Error::Internal)?;
    Ok(TreeFormatted {
        text: printed.text,
        stats: printed.stats,
    })
}

/// A file's gate results (formatter-architecture.md §6, stage 2).
#[derive(Clone, Debug)]
pub struct Gate {
    pub stats: TreeStats,
    /// The first difference in tokens, comments or tree, if any.
    pub check: Result<(), String>,
    /// Formatting the output again gives the output.
    pub idempotent: bool,
    /// Code lines over [`WIDTH`] characters, before and after.
    pub long_lines: (usize, usize),
    pub text: String,
}

/// Formats a file and checks the result: the same tokens up to the
/// deliberate rewrites, the same comments on the same tokens, the same
/// syntax tree, and the same text when formatted again.
pub fn gate(text: &str) -> Result<Gate, Error> {
    let file = SourceMap::new().add("input.sw", text);
    let printed = print_file(file, text, &crate::passes::PASSES)?;
    let check = check_file(file, text, &printed.input, &printed.text);
    let idempotent = match print_file(file, &printed.text, &crate::passes::PASSES) {
        Ok(again) => again.text == printed.text,
        Err(_) => false,
    };
    let long = |text: &str| {
        text.lines()
            .filter(|line| line.chars().count() > WIDTH && !line.trim_start().starts_with("--"))
            .count()
    };
    Ok(Gate {
        stats: printed.stats,
        check,
        idempotent,
        long_lines: (long(text), long(&printed.text)),
        text: printed.text,
    })
}

struct PrintedFile {
    /// The input after the tidy passes: what the output's tokens are
    /// compared with.
    input: String,
    text: String,
    stats: TreeStats,
}

fn print_file(
    file: FileId,
    text: &str,
    passes: &[crate::passes::Pass],
) -> Result<PrintedFile, Error> {
    lex_with_trivia(file, text).map_err(|d| Error::Refused(vec![d]))?;
    parse_module_within(file, text, DEFAULT_STACK).map_err(Error::Refused)?;
    let tidied = crate::passes::run(file, text, passes);
    let merged_groups = passes
        .iter()
        .position(|pass| {
            std::ptr::fn_addr_eq(
                *pass,
                crate::passes::merge_parameters as crate::passes::Pass,
            )
        })
        .map_or(0, |at| tidied.edits[at]);
    let input = tidied.text;
    let tree = tidied.tree;
    let (trivia, eof) = crate::tidy::place_comments(tree.tokens(), tree.trivia(), tree.eof());
    let mut printer = rules::Rules::new(&tree, &trivia, &input);
    let mut stats = TreeStats {
        merged_groups,
        ..TreeStats::default()
    };
    let mut out = String::new();
    let item = |out: &mut String, blank_lines: u32, text: &str| {
        if !out.is_empty() {
            out.push('\n');
            if blank_lines > 0 {
                out.push('\n');
            }
        }
        out.push_str(text);
    };
    for decl in tree.decls() {
        stats.decls += 1;
        // The parser accepts a file whose tokens before the first
        // declaration start with `:=` and drops them (they are in no
        // declaration, `decl_ranges`), so the tree holds them as an `Error`
        // node. Nothing reads them, so the file is refused as a syntax
        // error would be.
        let first_token = &tree.tokens()[decl.token_range().start];
        if decl.kind() == NodeKind::Error || first_token.tok == Tok::ColonEq {
            let message = "`:=` can't start a declaration";
            return Err(Error::Refused(vec![
                Diagnostic::error("E-PARSE", message).with_label(first_token.span, message),
            ]));
        }
        // Every declaration lexed: the file did, above.
        if decl.raw_text_range().is_some() {
            return Err(Error::Internal(
                "a declaration of a lexed file has no tokens".into(),
            ));
        }
        let range = decl.token_range();
        let first = &trivia[range.start];
        for comment in &first.leading {
            item(&mut out, comment.blank_lines_before, &comment.text);
        }
        let doc = printer.node(decl);
        if let Some(problem) = printer.take_unexpected() {
            return Err(Error::Internal(problem));
        }
        item(
            &mut out,
            first.blank_lines_before,
            &engine::print(&doc, WIDTH).text,
        );
    }
    for comment in &eof.leading {
        item(&mut out, comment.blank_lines_before, &comment.text);
    }
    if !out.is_empty() {
        out.push('\n');
    }
    Ok(PrintedFile {
        input,
        text: out,
        stats,
    })
}

/// Every comment with the token it belongs to, read by rule N
/// ([`crate::tidy`]): an own-line comment's token is the one after it, a
/// trailing one's the one it follows.
fn comment_anchors(lexed: &Lexed) -> Vec<(String, bool, usize)> {
    let tokens = &lexed.tokens;
    let (trivia, eof) = crate::tidy::place_comments(tokens, &lexed.trivia, &lexed.eof);
    let mut out = Vec::new();
    let mut n = 0;
    for trivia in trivia {
        for comment in trivia.leading {
            out.push((comment.text, false, n));
        }
        if let Some(comment) = trivia.trailing {
            out.push((comment.text, true, n));
        }
        n += 1;
    }
    for comment in eof.leading {
        out.push((comment.text, false, n));
    }
    out
}

/// The three checks on two texts of the same code: the first that fails.
fn compare(
    file: FileId,
    before: &str,
    after: &str,
    shapes: impl FnOnce() -> Result<Option<String>, String>,
) -> Result<(), (&'static str, String)> {
    let (Ok(a), Ok(b)) = (lex_with_trivia(file, before), lex_with_trivia(file, after)) else {
        return Err(("doesn't lex", String::new()));
    };
    check::same_tokens(before, &a, after, &b).map_err(|e| ("tokens", e))?;
    let (x, y) = (comment_anchors(&a), comment_anchors(&b));
    if x != y {
        let at = x
            .iter()
            .zip(&y)
            .position(|(p, q)| p != q)
            .unwrap_or(x.len().min(y.len()));
        let what = x.get(at).or(y.get(at)).map_or("", |c| c.0.as_str());
        return Err(("comments", format!("the comment `{what}` moved")));
    }
    match shapes() {
        Ok(None) => Ok(()),
        Ok(Some(difference)) => Err(("tree", difference)),
        Err(e) => Err(("doesn't parse", e)),
    }
}

/// The checks on `after`, the printed `original`, whose tidied text is
/// `before`. Tokens and comment anchors are compared with `before`, since
/// the passes rewrite tokens; the comments as written and the tree are
/// compared with `original` ([`check::same_comments`],
/// [`crate::same_program`]), so a wrong pass can't hide behind its own
/// result.
fn check_file(file: FileId, original: &str, before: &str, after: &str) -> Result<(), String> {
    if let (Ok(a), Ok(b)) = (
        lex_with_trivia(file, original),
        lex_with_trivia(file, after),
    ) {
        check::same_comments(&a, &b).map_err(|e| format!("comments: {e}"))?;
    }
    compare(file, before, after, || {
        let a = parse_module_within(file, original, DEFAULT_STACK)
            .map_err(|_| "the input doesn't parse".to_string())?;
        let b = parse_module_within(file, after, DEFAULT_STACK).map_err(|errors| {
            errors.first().map_or(String::new(), |d| {
                format!("the output doesn't parse: {}", d.message)
            })
        })?;
        crate::same_program::difference(&a, &b)
    })
    .map_err(|(reason, detail)| format!("{reason}: {detail}"))
}

#[cfg(test)]
mod tests;

/// The source bytes a token was read from: since SW-3171 every token's span
/// is exactly its text, interpolated text included.
pub(crate) fn token_text_range(token: &stitchwort_syntax::Token) -> std::ops::Range<usize> {
    token.span.start as usize..token.span.end as usize
}
