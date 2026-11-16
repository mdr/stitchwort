//! The tree printer: the formatter that chooses every line break, from the
//! lossless syntax tree (docs/proposals/formatter-architecture.md, stage 2;
//! the house style is docs/proposals/formatter-style.md). [`crate::format`]
//! is this printer; `stitchwort dev fmt-tree` reports on it over a tree of
//! files.
//!
//! Each declaration is turned into a layout document by the rule for each
//! construct ([`rules`]) and printed in 120 columns ([`engine`]). The
//! printed declaration must have the input's tokens (the input being the
//! file after the tidy passes, [`crate::passes`], which include D2307's
//! dropped brackets and D3565's merged parameters), its comments attached to
//! the same tokens, and parse to the same tree; one that doesn't is left as
//! written and counted, so a gap in the rules costs an unformatted
//! declaration, never a wrong program. [`gate`] runs the same checks on a
//! whole file, and that formatting twice changes nothing.

pub mod engine;
mod rules;

use std::collections::BTreeMap;

use stitchwort_syntax::tree::{NodeKind, SyntaxFile};
use stitchwort_syntax::{
    DEFAULT_STACK, FileId, Lexed, SourceMap, Tok, equivalence, lex_with_trivia, parse_module_within,
};

use crate::{Error, check};

/// An environment variable naming a declaration to treat as failing its
/// checks: no input fails them (every comment has a place, S40), so the
/// tests of how a declaration left as written is reported use this.
pub const REFUSE_FOR_TEST: &str = "STITCHWORT_FMT_REFUSE_FOR_TEST";

/// The width lines are fitted to (D1014).
pub const WIDTH: usize = 120;

/// A declaration left exactly as written, and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerbatimDecl {
    /// Its first line in the file, from 1.
    pub line: usize,
    /// Its name, or its first token when no name can be read.
    pub name: String,
    /// The check it failed.
    pub reason: &'static str,
}

/// What the tree printer did with a file.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TreeStats {
    pub decls: usize,
    /// Declarations left as written because their printed text failed a
    /// check, by the first check failed.
    pub verbatim: BTreeMap<&'static str, usize>,
    /// Where each of those is, and which declaration.
    pub verbatim_at: Vec<VerbatimDecl>,
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
    let check = check_file(file, &printed.input, &printed.text);
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
    /// The input after the tidy passes: what the output is compared with.
    input: String,
    text: String,
    stats: TreeStats,
}

fn print_file(file: FileId, text: &str) -> Result<PrintedFile, Error> {
    lex_with_trivia(file, text).map_err(|d| Error::Refused(vec![d]))?;
    parse_module_within(file, text, DEFAULT_STACK).map_err(Error::Refused)?;
    let tidied = crate::passes::run(file, text, &crate::passes::PASSES);
    let merge_at = crate::passes::PASSES
        .iter()
        .position(|pass| {
            std::ptr::fn_addr_eq(
                *pass,
                crate::passes::merge_parameters as crate::passes::Pass,
            )
        })
        .expect("P4 is in PASSES");
    let merged_groups = tidied.edits[merge_at];
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
        // A declaration that didn't lex, which only a file refused above
        // has: as written.
        if let Some(raw) = decl.raw_text_range() {
            item(&mut out, 0, input[raw].trim_end());
            continue;
        }
        let range = decl.token_range();
        let first = &trivia[range.start];
        for comment in &first.leading {
            item(&mut out, comment.blank_lines_before, &comment.text);
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
                let refused = || {
                    std::env::var(REFUSE_FOR_TEST)
                        .is_ok_and(|name| name == decl_name(&tree, &input, range.clone()))
                };
                let verdict = same_decl(before, &printed.text).and_then(|()| {
                    if refused() {
                        Err("refused for a test")
                    } else {
                        Ok(())
                    }
                });
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
                        stats.verbatim_at.push(VerbatimDecl {
                            line: first_line,
                            name: decl_name(&tree, &input, range.clone()),
                            reason,
                        });
                        before.to_string()
                    }
                }
            };
        item(&mut out, first.blank_lines_before, &text);
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
        let what = x.get(at).or(y.get(at)).map_or("", |c| c.0.as_str());
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

/// The name of the declaration in `range`, for a report: the name token after
/// its keyword (a definition's, theorem's, type's or test's), or its first
/// token when there is none.
fn decl_name(tree: &SyntaxFile, text: &str, range: std::ops::Range<usize>) -> String {
    let tokens = &tree.tokens()[range];
    let keyword = tokens.iter().position(|token| {
        matches!(
            token.tok,
            Tok::KwDef
                | Tok::KwTheorem
                | Tok::KwType
                | Tok::KwInterface
                | Tok::KwInstance
                | Tok::KwTest
                | Tok::KwAbility
        )
    });
    keyword
        .and_then(|at| {
            tokens[at + 1..].iter().find_map(|token| match &token.tok {
                Tok::Lower(name) | Tok::Upper(name) | Tok::Str(name) => Some(name.clone()),
                _ => None,
            })
        })
        .or_else(|| {
            tokens
                .first()
                .map(|token| text[token_text_range(token)].to_string())
        })
        .unwrap_or_default()
}
