//! The tree printer: the formatter that chooses every line break, from the
//! lossless syntax tree (docs/proposals/formatter-architecture.md, stage 2;
//! the house style is docs/proposals/formatter-style.md). [`crate::format`]
//! is this printer; `stitchwort dev fmt-tree` reports on it over a tree of
//! files.
//!
//! Each declaration is turned into a layout document by the rule for each
//! construct ([`rules`]) and printed in 120 columns ([`engine`]). The
//! printed declaration must have the input's tokens (up to the deliberate
//! rewrites: D1012's commas, D3472's `∀` and D3565's merged parameters,
//! [`merge`], checked on their own), its comments attached to the
//! same tokens, and parse to the same tree; one that doesn't is left as
//! written and counted, so a gap in the rules costs an unformatted
//! declaration, never a wrong program. [`gate`] runs the same checks on a
//! whole file, and that formatting twice changes nothing.

pub mod engine;
mod merge;
mod parens;
mod rules;

use std::collections::BTreeMap;

use stitchwort_syntax::tree::{NodeKind, SyntaxFile};
use stitchwort_syntax::{
    DEFAULT_STACK, FileId, Lexed, SourceMap, Tok, equivalence, lex_with_trivia,
    parse_module_within, parse_tree,
};

use crate::{Error, check};

/// The width lines are fitted to (D1014).
pub const WIDTH: usize = 120;

/// What the tree printer did with a file.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TreeStats {
    pub decls: usize,
    /// Declarations left as written because their printed text failed a
    /// check, by the first check failed.
    pub verbatim: BTreeMap<&'static str, usize>,
    /// Where each of those is: its first line (from 1) and the check.
    pub verbatim_at: Vec<(usize, &'static str)>,
    /// Nodes printed as written because no rule covers their kind yet.
    pub unruled: BTreeMap<NodeKind, usize>,
    /// Parameter groups made by merging parameters of one type (D3565).
    pub merged_groups: usize,
}

impl TreeStats {
    pub fn verbatim_decls(&self) -> usize {
        self.verbatim.values().sum()
    }

    pub fn add(&mut self, other: &TreeStats) {
        self.decls += other.decls;
        self.merged_groups += other.merged_groups;
        for (reason, n) in &other.verbatim {
            *self.verbatim.entry(reason).or_default() += n;
        }
        for (kind, n) in &other.unruled {
            *self.unruled.entry(*kind).or_default() += n;
        }
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
    let printed = print_file(file, text)?;
    printed.merges.clone().map_err(Error::Internal)?;
    check_file(file, &printed.input, &printed.text).map_err(Error::Internal)?;
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
    let printed = print_file(file, text)?;
    let check = printed
        .merges
        .clone()
        .and_then(|()| check_file(file, &printed.input, &printed.text));
    let idempotent = match print_file(file, &printed.text) {
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
    /// The input with D3472's `∀`s added and D3565's parameters merged:
    /// what the output is compared with.
    input: String,
    /// How the merge of parameters checked; a failed one isn't made.
    merges: Result<(), String>,
    text: String,
    stats: TreeStats,
}

fn print_file(file: FileId, text: &str) -> Result<PrintedFile, Error> {
    let lexed = lex_with_trivia(file, text).map_err(|d| Error::Refused(vec![d]))?;
    parse_module_within(file, text, DEFAULT_STACK).map_err(Error::Refused)?;
    let mut input =
        crate::insert_theorem_foralls(text, &lexed.tokens).unwrap_or_else(|| text.to_string());
    let mut merges = Ok(());
    let mut merged_groups = 0;
    if let Some((dropped, _)) = parens::drop_parens(&input)
        && merge::check(&input, &dropped).is_ok()
    {
        input = dropped;
    }
    if let Some((merged, groups)) = merge::merge(&input) {
        merges = merge::check(&input, &merged);
        if merges.is_ok() {
            input = merged;
            merged_groups = groups;
        }
    }
    let tree = parse_tree(file, &input, DEFAULT_STACK).map_err(|d| Error::Refused(vec![d]))?;
    let mut printer = rules::Rules::new(&tree, &input);
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
        let range = decl.token_range();
        let trivia = &tree.trivia()[range.start];
        for comment in &trivia.leading {
            item(
                &mut out,
                comment.blank_lines_before,
                comment.text.trim_end_matches(' '),
            );
        }
        let before = decl_source(&tree, &input, range.start, range.end);
        let first_line = input[..token_text_range(&tree.tokens()[range.start]).start]
            .matches('\n')
            .count()
            + 1;
        let text =
            if decl.kind() == NodeKind::Error || tree.tokens()[range.start].tok == Tok::ColonEq {
                before.to_string()
            } else {
                let doc = printer.node(decl);
                let printed = engine::print(&doc, WIDTH);
                let verdict = if printed.forced_comment_lines > 0 {
                    Err("comment no rule places")
                } else if printed.stranded_comments > 0 {
                    Err("comment before a text block")
                } else {
                    same_decl(before, &printed.text)
                };
                match verdict {
                    Ok(()) => {
                        rules::unruled(decl, &mut stats.unruled);
                        printed.text
                    }
                    Err(reason) => {
                        if std::env::var_os("STITCHWORT_FMT_TREE_DEBUG").is_some() {
                            let error = equivalence::parse_shape(&printed.text).err();
                            eprintln!(
                                "--- line {first_line}: {reason} {}\n{}",
                                error.unwrap_or_default(),
                                printed.text
                            );
                        }
                        *stats.verbatim.entry(reason).or_default() += 1;
                        stats.verbatim_at.push((first_line, reason));
                        before.to_string()
                    }
                }
            };
        item(&mut out, trivia.blank_lines_before, &text);
    }
    for comment in &tree.eof().leading {
        item(
            &mut out,
            comment.blank_lines_before,
            comment.text.trim_end_matches(' '),
        );
    }
    if !out.is_empty() {
        out.push('\n');
    }
    Ok(PrintedFile {
        input,
        text: out,
        stats,
        merges,
    })
}

/// A declaration's source, from the start of its first line to the end of
/// its last (with any trailing comment).
fn decl_source<'t>(tree: &SyntaxFile, text: &'t str, first: usize, end: usize) -> &'t str {
    let tokens = tree.tokens();
    let start = token_text_range(&tokens[first]).start;
    let start = text[..start].rfind('\n').map_or(0, |k| k + 1);
    let last_end = token_text_range(&tokens[end - 1]).end;
    let line_end = text[last_end..]
        .find('\n')
        .map_or(text.len(), |k| last_end + k);
    text[start..line_end].trim_end_matches('\r')
}

/// Every comment with the token it is attached to: an own-line comment to
/// the token after it, a trailing one to the token it follows, skipping
/// commas and closing brackets, which move freely around a line's end.
/// Tokens are counted without commas, which D1012 adds and drops.
fn comment_anchors(lexed: &Lexed) -> Vec<(&str, bool, usize)> {
    let tokens = &lexed.tokens;
    let mut index = Vec::with_capacity(tokens.len());
    let mut n = 0;
    for token in tokens {
        index.push(n);
        if token.tok != Tok::Comma {
            n += 1;
        }
    }
    let mut out = Vec::new();
    for (i, trivia) in lexed.trivia.iter().enumerate() {
        for comment in &trivia.leading {
            out.push((comment.text.trim_end_matches(' '), false, index[i]));
        }
        if let Some(comment) = &trivia.trailing {
            let mut j = i;
            while j > 0
                && matches!(
                    tokens[j].tok,
                    Tok::Comma | Tok::RParen | Tok::RBracket | Tok::RBrace
                )
            {
                j -= 1;
            }
            out.push((comment.text.trim_end_matches(' '), true, index[j]));
        }
    }
    for comment in &lexed.eof.leading {
        out.push((comment.text.trim_end_matches(' '), false, n));
    }
    out
}

/// The three checks on two texts of the same code: the first that fails.
fn compare(
    file: FileId,
    before: &str,
    after: &str,
    shapes: impl FnOnce() -> Result<bool, String>,
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
        let what = x.get(at).or(y.get(at)).map_or("", |c| c.0);
        return Err(("comments", format!("the comment `{what}` moved")));
    }
    match shapes() {
        Ok(true) => Ok(()),
        Ok(false) => Err(("tree", "the output parses to a different tree".into())),
        Err(e) => Err(("doesn't parse", e)),
    }
}

fn same_decl(before: &str, after: &str) -> Result<(), &'static str> {
    if before == after {
        return Ok(());
    }
    let file = SourceMap::new().add("decl.sw", "");
    compare(file, before, after, || {
        let after = equivalence::parse_shape(after)?;
        Ok(equivalence::parse_shape(before).is_ok_and(|b| b == after))
    })
    .map_err(|(reason, _)| reason)
}

fn check_file(file: FileId, before: &str, after: &str) -> Result<(), String> {
    compare(file, before, after, || {
        let a = parse_module_within(file, before, DEFAULT_STACK)
            .map_err(|_| "the input doesn't parse".to_string())?;
        let b = parse_module_within(file, after, DEFAULT_STACK).map_err(|errors| {
            errors.first().map_or(String::new(), |d| {
                format!("the output doesn't parse: {}", d.message)
            })
        })?;
        Ok(equivalence::shape(&a) == equivalence::shape(&b))
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
