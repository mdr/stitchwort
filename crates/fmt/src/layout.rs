//! Building the layout of a file from its tokens (docs/proposals/formatter.md
//! §2.3): the author's line breaks are kept (D1013), each line gets its
//! indentation from the construct it belongs to, and the spacing on a line
//! comes from [`crate::spacing`]. Every token prints its own source text.
//!
//! **Indentation.** Layout depends only on how the columns of line starts
//! compare (`crates/syntax/src/parser.rs`: a block's lines share a column, a
//! line further right continues the one above, a line at or left of a block's
//! column ends it). So lines are put in a tree: a line's *parent* is the
//! nearest line above it that starts further left. A line's new indentation
//! is its parent's plus an offset, and lines with the same parent and old
//! column (the lines of one block, or the arms of one definition) share it.
//! The offset is 2 (R1, R2: arms, body lines, and D1040: every continuation
//! line, such as further application arguments, `|>` and `calc` steps), or
//! 4 for a header's continuation lines (R1, D1038: `decreasing` too). If a
//! parent's groups of children would get the same offset, each deeper group
//! gets 2 more than the one before, which keeps their order. Lines at column
//! 0 stay there: they start or continue declarations (R21: a bare `:=`).
//! A `|>` line at its expression's own column is moved to its child
//! (R13), as it continues the line above either way.
//!
//! **Brackets.** A bracket with commas that spans lines is converted to the
//! D1012 layout (D1017): the opener ends a line (a line that began with the
//! opener joins the line above when that is safe), each element has a line
//! of its own with a comma at its end (none after the last), and the closer
//! has a line of its own at the opening line's indentation. The lines of
//! the new layout get *synthetic* columns for the tree above: an element's
//! line a column between its opening line and anything inside the bracket,
//! and a closer the opening line's column.
//!
//! Each declaration is checked on its own as it is built (the same checks as
//! §4.1). One that fails is formatted again without converting brackets
//! ([`Stats::unconverted_decls`]), and one that still fails is copied
//! unchanged ([`Stats::verbatim_decls`]), so a gap in the rules costs one
//! declaration's formatting rather than the file's.

// The formatter doesn't depend on the core, whose maps hash the same on
// every run (`stitchwort_core::collections`), and isn't benchmarked.
#![allow(clippy::disallowed_types)]

use std::collections::HashMap;
use std::ops::Range;

use stitchwort_syntax::{Comment, Lexed, Tok, Token, equivalence, lex_with_trivia};

use crate::doc::{Doc, print};
use crate::spacing::{Gap, Pair, Role, gap};
use crate::{Stats, check};

/// The indentation unit (R1).
const INDENT: usize = 2;
/// A definition's header continuation lines (R1).
const HEADER_INDENT: usize = 4;
/// What the synthetic columns of lines inside a converted bracket are
/// shifted by, per level of nesting: more than any real column.
const SHIFT: usize = 100_000;

/// One line of the new layout: tokens that start a line, or a bracket's
/// element or closer.
#[derive(Debug)]
struct VLine<'a> {
    /// The kept tokens, in order (the commas converted away are not here).
    toks: Vec<usize>,
    /// The column that decides the line's place in the tree.
    tcol: usize,
    /// The column of the line's first token in the source, shifted like
    /// `tcol` for brackets that were converted.
    col0: usize,
    /// The line starts with `|>`.
    pipe: bool,
    /// The column of the line's first token in the source.
    src_col: usize,
    /// A converted bracket's closer: the index of the line the bracket
    /// opened on, whose indentation it takes.
    closer_of: Option<usize>,
    /// A comma goes at the end of the line (before any comment).
    comma_after: bool,
    /// The comment that ended the comma converted away, if the line has no
    /// comment of its own.
    extra_trailing: Option<&'a Comment>,
    /// Own-line comments before the line, with whether a blank line is
    /// before each.
    lead: Vec<(&'a str, bool)>,
    /// A blank line between the comments (or the line above) and this line.
    blank: bool,
}

impl VLine<'_> {
    fn first(&self) -> usize {
        self.toks[0]
    }

    fn last(&self) -> usize {
        *self.toks.last().expect("a line has a token")
    }
}

/// A bracket with commas that spans lines, to be converted to D1012.
#[derive(Debug)]
struct Conv {
    open: usize,
    close: usize,
    /// The commas between elements, and a trailing comma.
    seps: Vec<usize>,
}

/// Which part of a declaration a child of a column-0 line is in: the header
/// is never compared with the body for layout, so lines in each are grouped
/// separately.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Part {
    Header,
    Main,
}

pub(crate) struct Layout<'a> {
    text: &'a str,
    lexed: &'a Lexed,
    roles: Vec<Role>,
    pub(crate) stats: Stats,
}

/// Whether a token can end an operand, so that a `-` after it is infix.
fn ends_operand(tok: &Tok) -> bool {
    use Tok::*;
    matches!(
        tok,
        Lower(_)
            | Upper(_)
            | Num(_)
            | Float(_)
            | Str(_)
            | StrEnd(_)
            | Char(_)
            | RParen
            | RBracket
            | RBrace
            | Underscore
            | TypeU
            | Prop
            | KwOmega
            | KwRing
    )
}

/// The role of each token (see [`Role`]).
fn roles(lexed: &Lexed) -> Vec<Role> {
    let tokens = &lexed.tokens;
    let mut roles = vec![Role::Plain; tokens.len()];
    let mut braces: Vec<bool> = Vec::new();
    // The column of the first token of the line before the current one.
    let (mut line_col, mut prev_line_col) = (0u32, 0u32);
    for (k, t) in tokens.iter().enumerate() {
        if t.line_start {
            prev_line_col = line_col;
            line_col = t.column;
        }
        match t.tok {
            Tok::LBrace => {
                // Only a function's result type has a row, and it follows
                // the `:` or `->` before it (`result_type` in the parser).
                let row = k > 0 && matches!(tokens[k - 1].tok, Tok::Colon | Tok::Arrow);
                if row {
                    roles[k] = Role::Row;
                }
                braces.push(row);
            }
            Tok::RBrace => {
                if braces.pop().unwrap_or(false) {
                    roles[k] = Role::Row;
                }
            }
            Tok::Minus => {
                let before = k.checked_sub(1).map(|j| &tokens[j]);
                roles[k] = if before.is_some_and(|b| {
                    b.tok == Tok::Lt && b.span.end == t.span.start && !t.line_start
                }) {
                    Role::RewriteArrow
                } else {
                    let operand = before.is_some_and(|b| ends_operand(&b.tok));
                    // A line starting with `-` at or left of the line above
                    // starts a statement, so the `-` is a prefix.
                    let continues = !t.line_start || t.column > prev_line_col;
                    if operand && continues {
                        Role::Binary
                    } else {
                        Role::Unary
                    }
                };
            }
            _ => {}
        }
    }
    roles
}

impl<'a> Layout<'a> {
    pub(crate) fn new(text: &'a str, lexed: &'a Lexed) -> Self {
        Layout {
            text,
            lexed,
            roles: roles(lexed),
            stats: Stats::default(),
        }
    }

    fn tokens(&self) -> &'a [Token] {
        &self.lexed.tokens
    }

    fn source(&self, k: usize) -> &'a str {
        let span = self.tokens()[k].span;
        &self.text[span.start as usize..span.end as usize]
    }

    /// The whole file, from its declarations' token ranges.
    pub(crate) fn file(&mut self, decls: &[Range<usize>]) -> String {
        let mut out = String::new();
        // R17: at most one blank line between items, none at the start of
        // the file.
        let item = |out: &mut String, blank_lines: u32, text: &str| {
            if !out.is_empty() {
                out.push('\n');
                if blank_lines > 0 {
                    out.push('\n');
                }
            }
            out.push_str(text);
        };
        for range in decls {
            let trivia = &self.lexed.trivia[range.start];
            for comment in &trivia.leading {
                item(&mut out, comment.blank_lines_before, comment_text(comment));
            }
            // Tokens before the first declaration (it starts with `:=`, which
            // the parser skips) aren't a declaration: they stay as written.
            let text = if self.tokens()[range.start].tok == Tok::ColonEq {
                self.decl_source(range).to_string()
            } else {
                self.decl(range.clone())
            };
            item(&mut out, trivia.blank_lines_before, &text);
        }
        for comment in &self.lexed.eof.leading {
            item(&mut out, comment.blank_lines_before, comment_text(comment));
        }
        // R18: one newline at the end.
        if !out.is_empty() {
            out.push('\n');
        }
        out
    }

    /// One declaration, without the comments and blank lines above it: its
    /// formatted text if that passes the checks, then its text without
    /// converting brackets if that does, otherwise its source.
    fn decl(&mut self, range: Range<usize>) -> String {
        let before = self.decl_source(&range);
        let saved = self.stats;
        for convert in [true, false] {
            self.stats = saved;
            let doc = self.decl_doc(range.clone(), convert);
            let after = print(&doc, None);
            if after == before || same_decl(before, &after) {
                if !convert {
                    self.stats.unconverted_decls += 1;
                }
                return after;
            }
        }
        self.stats = saved;
        self.stats.verbatim_decls += 1;
        before.to_string()
    }

    /// The source of a declaration, from the start of its first line to the
    /// end of its last (with any trailing comment).
    fn decl_source(&self, range: &Range<usize>) -> &'a str {
        let tokens = self.tokens();
        let first = &tokens[range.start];
        let start = first.span.start as usize - first.column as usize;
        let last_end = tokens[range.end - 1].span.end as usize;
        let end = self.text[last_end..]
            .find('\n')
            .map_or(self.text.len(), |k| last_end + k);
        self.text[start..end].trim_end_matches('\r')
    }

    /// The brackets of a declaration to convert to D1012: those with commas
    /// between their elements that span lines. A bracket that holds a
    /// `match`, `rewrite`, `handle` or `calc`, or an arm, is left alone: its
    /// commas may separate patterns or rules, not elements.
    fn find_convs(&self, range: &Range<usize>) -> Vec<Conv> {
        struct Open {
            at: usize,
            seps: Vec<usize>,
            blocked: bool,
        }
        let (tokens, trivia) = (self.tokens(), &self.lexed.trivia);
        let mut stack: Vec<Open> = Vec::new();
        let mut convs = Vec::new();
        for k in range.clone() {
            let t = &tokens[k];
            match t.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => stack.push(Open {
                    at: k,
                    seps: Vec::new(),
                    blocked: false,
                }),
                Tok::Comma => {
                    if let Some(top) = stack.last_mut() {
                        top.seps.push(k);
                    }
                }
                Tok::KwMatch | Tok::KwRewrite | Tok::KwHandle | Tok::KwCalc => {
                    if let Some(top) = stack.last_mut() {
                        top.blocked = true;
                    }
                }
                Tok::Pipe if t.line_start => {
                    if let Some(top) = stack.last_mut() {
                        top.blocked = true;
                    }
                }
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    let Some(top) = stack.pop() else { continue };
                    let spans_lines = (top.at + 1..=k).any(|j| tokens[j].line_start);
                    // A comma that ends a line with a comment cannot move to
                    // the end of an element that has a comment of its own.
                    let comments_fit = top
                        .seps
                        .iter()
                        .all(|&s| trivia[s - 1].trailing.is_none() || trivia[s].trailing.is_none());
                    if !top.seps.is_empty() && spans_lines && !top.blocked && comments_fit {
                        convs.push(Conv {
                            open: top.at,
                            close: k,
                            seps: top.seps,
                        });
                    }
                }
                _ => {}
            }
        }
        convs.sort_by_key(|c| c.open);
        convs
    }

    /// The lines of a declaration in the new layout.
    fn vlines(&self, range: &Range<usize>, convert: bool) -> Vec<VLine<'a>> {
        let (tokens, trivia) = (self.tokens(), &self.lexed.trivia);
        let n = range.len();
        let at = |k: usize| k - range.start;

        // The lines of the source, and their tree, for deciding which
        // openers may join the line above.
        let mut old: Vec<(usize, usize)> = Vec::new();
        for k in range.clone() {
            if k == range.start || tokens[k].line_start {
                old.push((k, tokens[k].column as usize));
            }
        }
        let mut old_index = vec![usize::MAX; n];
        let mut old_parent: Vec<Option<usize>> = Vec::with_capacity(old.len());
        let mut stack: Vec<usize> = Vec::new();
        for (i, &(first, column)) in old.iter().enumerate() {
            while stack.last().is_some_and(|&j| old[j].1 >= column) {
                stack.pop();
            }
            old_parent.push(stack.last().copied());
            stack.push(i);
            old_index[at(first)] = i;
        }
        // What each token is in a converted bracket.
        let convs = if convert {
            self.find_convs(range)
        } else {
            Vec::new()
        };
        let mut opens: Vec<Option<usize>> = vec![None; n];
        let mut closes: Vec<Option<usize>> = vec![None; n];
        let mut dropped = vec![false; n];
        let mut elem_first = vec![false; n];
        let mut trailing_sep = vec![false; n];
        for (id, conv) in convs.iter().enumerate() {
            opens[at(conv.open)] = Some(id);
            closes[at(conv.close)] = Some(id);
            elem_first[at(conv.open + 1)] = true;
            for &s in &conv.seps {
                dropped[at(s)] = true;
                if s + 1 == conv.close {
                    trailing_sep[at(s)] = true;
                } else {
                    elem_first[at(s + 1)] = true;
                }
            }
        }
        // A trailing comma on one line is dropped too (D1012).
        for k in range.start + 1..range.end {
            if tokens[k].tok == Tok::Comma
                && !tokens[k].line_start
                && !dropped[at(k)]
                && tokens.get(k + 1).is_some_and(|t| {
                    k + 1 < range.end && matches!(t.tok, Tok::RParen | Tok::RBracket | Tok::RBrace)
                })
                && (trivia[k - 1].trailing.is_none() || trivia[k].trailing.is_none())
            {
                dropped[at(k)] = true;
                trailing_sep[at(k)] = true;
            }
        }
        let mut group_size: HashMap<(Option<usize>, usize), usize> = HashMap::new();
        for (i, &(first, column)) in old.iter().enumerate() {
            // Lines that start with a comma or closer converted away aren't
            // statements of the block.
            if dropped[at(first)] || closes[at(first)].is_some() {
                continue;
            }
            *group_size.entry((old_parent[i], column)).or_default() += 1;
        }

        // Openers that join the line above: the first token of a line that
        // only continues the line above it, with nothing between them.
        let may_join = |o: usize| -> bool {
            let i = old_index[at(o)];
            o > range.start
                && i != usize::MAX
                && i > 0
                && (old_parent[i] == Some(i - 1)
                    || matches!(
                        tokens[o - 1].tok,
                        Tok::ColonEq | Tok::Equals | Tok::FatArrow
                    ))
                && group_size[&(old_parent[i], old[i].1)] == 1
                && !elem_first[at(o)]
                && trivia[o].leading.is_empty()
                && trivia[o].blank_lines_before == 0
                && trivia[o - 1].trailing.is_none()
        };

        let mut lines: Vec<VLine<'a>> = Vec::new();
        let mut open_line: Vec<usize> = vec![0; convs.len()];
        let mut enclosing: Vec<usize> = Vec::new();
        // Trivia of a comma converted away, for the token after it.
        let mut carry: Option<usize> = None;
        for k in range.clone() {
            let t = &tokens[k];
            if dropped[at(k)] {
                if let Some(last) = lines.last_mut() {
                    if !trailing_sep[at(k)] {
                        last.comma_after = true;
                    }
                    if trivia[last.last()].trailing.is_none() {
                        last.extra_trailing = trivia[k].trailing.as_ref();
                    }
                }
                if t.line_start {
                    carry = Some(k);
                }
                continue;
            }
            let closer = closes[at(k)];
            let joins = opens[at(k)].is_some()
                && may_join(k)
                && lines.last().is_some_and(|l| l.closer_of.is_none());
            let new_line = k == range.start
                || closer.is_some()
                || elem_first[at(k)]
                || (t.line_start && !joins);
            if new_line {
                let depth = enclosing.len();
                let col0 = t.column as usize + SHIFT * depth;
                let (tcol, closer_of) = if let Some(id) = closer {
                    (lines[open_line[id]].tcol, Some(open_line[id]))
                } else if elem_first[at(k)] {
                    (SHIFT * depth - 1, None)
                } else {
                    let mut column = t.column as usize;
                    column += SHIFT * depth;
                    // R13: a `|>` right under a line of the same column
                    // continues it, so it goes at +2.
                    let under_same = lines
                        .last()
                        .is_some_and(|l| l.col0 == column && (!l.pipe || l.tcol == column + 1));
                    let tcol = if t.tok == Tok::PipeGt && under_same {
                        column + 1
                    } else {
                        column
                    };
                    (tcol, None)
                };
                let mut lead: Vec<(&'a str, bool)> = Vec::new();
                let mut blank = trivia[k].blank_lines_before > 0;
                if let Some(c) = carry.take() {
                    for comment in &trivia[c].leading {
                        lead.push((comment_text(comment), comment.blank_lines_before > 0));
                    }
                    if trivia[c].blank_lines_before > 0 {
                        blank = true;
                    }
                }
                for comment in &trivia[k].leading {
                    lead.push((comment_text(comment), comment.blank_lines_before > 0));
                }
                lines.push(VLine {
                    toks: vec![k],
                    tcol,
                    col0,
                    pipe: t.tok == Tok::PipeGt,
                    src_col: t.column as usize,
                    closer_of,
                    comma_after: false,
                    extra_trailing: None,
                    lead,
                    blank,
                });
            } else if let Some(last) = lines.last_mut() {
                last.toks.push(k);
            }
            if let Some(id) = opens[at(k)] {
                open_line[id] = lines.len() - 1;
                enclosing.push(id);
            }
            if closer.is_some() {
                enclosing.pop();
            }
        }
        lines
    }

    fn decl_doc(&mut self, range: Range<usize>, convert: bool) -> Doc {
        let lines = self.vlines(&range, convert);
        let header = self.header_end(range.clone());
        let indents = self.indents(&lines, header);
        let mut docs = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            let mut parts = Vec::new();
            if i > 0 {
                // R17: no blank line at the start of a body.
                let opens = self.ends_with_opener(&lines[i - 1]);
                for (c, &(text, blank)) in line.lead.iter().enumerate() {
                    parts.push(Doc::HardLine);
                    if blank && !(c == 0 && opens) {
                        parts.push(Doc::HardLine);
                    }
                    // R16: an own-line comment is indented like the code
                    // line after it.
                    parts.push(Doc::text(text));
                }
                parts.push(Doc::HardLine);
                if line.blank && !(line.lead.is_empty() && opens) {
                    parts.push(Doc::HardLine);
                }
            }
            let shift = indents[i] as i64 - line.src_col as i64;
            parts.push(self.line_doc(line, shift));
            docs.push(Doc::nest(indents[i], Doc::Concat(parts)));
        }
        Doc::Concat(docs)
    }

    /// The token ending a declaration's header, after which its lines are
    /// its body: the first `:=` (or arm) of a definition, the `=` of a data
    /// type or interface, an ability's `where`. `None` for declarations
    /// without a header (imports, the namespace line).
    fn header_end(&self, range: Range<usize>) -> Option<(usize, usize)> {
        let tokens = self.tokens();
        let mut k = range.start;
        // Attributes, then `export`.
        while k < range.end && tokens[k].tok == Tok::At {
            let mut depth = 0i32;
            k += 1;
            while k < range.end {
                match tokens[k].tok {
                    Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                    Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                    _ => {}
                }
                k += 1;
                if depth <= 0 {
                    break;
                }
            }
        }
        if k < range.end && tokens[k].tok == Tok::KwExport {
            k += 1;
        }
        let keyword = tokens.get(k).filter(|_| k < range.end)?;
        let ends: fn(&Token) -> bool = match keyword.tok {
            Tok::KwDef | Tok::KwTheorem | Tok::KwInstance | Tok::KwTest => {
                |t| t.tok == Tok::ColonEq || (t.tok == Tok::Pipe && t.line_start)
            }
            Tok::KwType | Tok::KwInterface => |t| {
                matches!(t.tok, Tok::Equals | Tok::ColonEq) || (t.tok == Tok::Pipe && t.line_start)
            },
            Tok::KwAbility => |t| t.tok == Tok::KwWhere,
            _ => return None,
        };
        let mut depth = 0i32;
        for (j, t) in tokens.iter().enumerate().take(range.end).skip(k + 1) {
            if depth == 0 && ends(t) {
                return Some((k, j));
            }
            match t.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                _ => {}
            }
        }
        None
    }

    /// Whether a line ends with a token after which the next, deeper line
    /// starts a body (R2): `:=`, `=>`, `where`, `with`; for blank lines
    /// (R17) also `=` and an opening bracket.
    fn ends_with_opener(&self, line: &VLine) -> bool {
        matches!(
            self.tokens()[line.last()].tok,
            Tok::ColonEq
                | Tok::FatArrow
                | Tok::KwWhere
                | Tok::KwWith
                | Tok::Equals
                | Tok::LParen
                | Tok::LBracket
                | Tok::LBrace
        )
    }

    /// The new indentation of each line of a declaration (see the module
    /// documentation).
    fn indents(&mut self, lines: &[VLine], header: Option<(usize, usize)>) -> Vec<usize> {
        let tokens = self.tokens();
        // The parent of each line, by a stack of lines with rising columns.
        let mut tcol: Vec<usize> = lines.iter().map(|l| l.tcol).collect();
        let mut parent: Vec<Option<usize>> = Vec::with_capacity(lines.len());
        let mut stack: Vec<usize> = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            let mut sibling = None;
            while stack.last().is_some_and(|&j| tcol[j] >= tcol[i]) {
                sibling = stack.pop().filter(|&j| tcol[j] == tcol[i]);
            }
            // The sibling an `else` belongs to, if the author lined it up.
            let after_if = sibling
                .is_some_and(|j| matches!(tokens[lines[j].first()].tok, Tok::KwIf | Tok::KwElse));
            // R12: a `then` or `else` that starts a line below the line of
            // its `if` lines up with it.
            if let Some(&p) = stack.last()
                && matches!(tokens[line.first()].tok, Tok::KwThen | Tok::KwElse)
                && !after_if
                && line.closer_of.is_none()
                && matches!(
                    tokens[lines[p].first()].tok,
                    Tok::KwIf | Tok::KwThen | Tok::KwElse
                )
            {
                tcol[i] = tcol[p];
                while stack.last().is_some_and(|&j| tcol[j] >= tcol[i]) {
                    stack.pop();
                }
            }
            parent.push(stack.last().copied());
            stack.push(i);
        }
        let part = |i: usize| -> Part {
            let line = &lines[i];
            let under_top = parent[i].is_some_and(|p| tcol[p] == 0);
            // The header runs from the declaration's keyword (not its
            // attributes) to the `:=` or `=` or the first arm.
            let in_header = header.is_some_and(|(start, h)| {
                (line.first() >= start && line.first() < h)
                    || (line.first() == h && tokens[h].tok != Tok::Pipe && line.src_col > 0)
            });
            if under_top && in_header {
                Part::Header
            } else {
                Part::Main
            }
        };
        // The offset each group of lines (same parent, part and column)
        // asks for.
        type Key = (usize, Part, usize);
        let mut groups: Vec<(Key, usize)> = Vec::new();
        let mut index: HashMap<Key, usize> = HashMap::new();
        let mut group_of: Vec<Option<usize>> = vec![None; lines.len()];
        for (i, line) in lines.iter().enumerate() {
            let Some(p) = parent[i] else { continue };
            if line.closer_of.is_some() {
                continue;
            }
            let key = (p, part(i), tcol[i]);
            if let Some(&g) = index.get(&key) {
                group_of[i] = Some(g);
                continue;
            }
            index.insert(key, groups.len());
            let top = tcol[p] == 0;
            let wanted = if top && tokens[line.first()].tok == Tok::Pipe {
                // R1: arms (and constructors) at +2.
                INDENT
            } else if key.1 == Part::Header {
                // R1, D1038: header continuation lines at +4.
                HEADER_INDENT
            } else {
                // R2, D1040: body lines and continuation lines at +2.
                INDENT
            };
            group_of[i] = Some(groups.len());
            groups.push((key, wanted));
        }
        // Groups of one parent keep their order: each is deeper than the
        // one before it.
        let mut siblings: HashMap<(usize, Part), Vec<(usize, usize)>> = HashMap::new();
        for (g, ((p, part, column), _)) in groups.iter().enumerate() {
            siblings.entry((*p, *part)).or_default().push((*column, g));
        }
        for (_, mut members) in siblings {
            members.sort_unstable();
            let mut before: Option<usize> = None;
            for (_, g) in members {
                let wanted = groups[g].1;
                let offset = match before {
                    Some(b) if wanted <= b => b + INDENT,
                    _ => wanted,
                };
                groups[g].1 = offset;
                before = Some(offset);
            }
        }
        let mut indents = vec![0usize; lines.len()];
        for (i, line) in lines.iter().enumerate() {
            if let Some(open) = line.closer_of {
                // D1012: the closer lines up with the line the bracket
                // opened on.
                indents[i] = indents[open];
                continue;
            }
            let (Some(p), Some(g)) = (parent[i], group_of[i]) else {
                continue;
            };
            indents[i] = indents[p] + groups[g].1;
        }
        indents
    }

    /// A line's tokens with their spacing, and its trailing comment. A
    /// `"""` text block moves with the line: its later lines move by `shift`
    /// columns, or as near as their indentation allows (which leaves the
    /// text's value unchanged, since its common indentation is removed).
    fn line_doc(&mut self, line: &VLine, shift: i64) -> Doc {
        let tokens = self.tokens();
        let mut out = String::new();
        for (n, &k) in line.toks.iter().enumerate() {
            if n > 0 {
                let (left, right) = (&tokens[line.toks[n - 1]], &tokens[k]);
                let spaced = left.span.end != right.span.start;
                let pair = Pair {
                    left: &left.tok,
                    left_role: self.roles[line.toks[n - 1]],
                    right: &right.tok,
                    right_role: self.roles[k],
                    after: tokens.get(k + 1).map(|t| &t.tok),
                    spaced,
                };
                match gap(&pair) {
                    Gap::Source => {
                        out.push_str(&self.text[left.span.end as usize..right.span.start as usize])
                    }
                    Gap::Copied(space) => {
                        self.stats.copied_gaps += 1;
                        if space {
                            out.push(' ');
                        }
                    }
                    Gap::Rule(space) | Gap::Kept(space) => {
                        if space {
                            out.push(' ');
                        }
                    }
                }
            }
            if self.source(k).contains('\n') {
                // A text block: copy the rest of the line, moved.
                let start = tokens[k].span.start as usize;
                let end = tokens[line.last()].span.end as usize;
                out.push_str(&shift_lines(&self.text[start..end], shift));
                break;
            }
            out.push_str(self.source(k));
        }
        if line.comma_after {
            out.push(',');
        }
        let trailing = self.lexed.trivia[line.last()]
            .trailing
            .as_ref()
            .or(line.extra_trailing);
        if let Some(comment) = trailing {
            // R16: one space before a trailing comment.
            out.push(' ');
            out.push_str(comment_text(comment));
        }
        if out.contains('\n') {
            Doc::Raw(out)
        } else {
            Doc::Text(out)
        }
    }
}

/// `text` with every line after the first moved right by `shift` columns
/// (left if negative), as far as the least indented allows. Lines of only
/// spaces stay as they are.
fn shift_lines(text: &str, shift: i64) -> String {
    let blank = |line: &str| line.trim_matches([' ', '\r']).is_empty();
    let lead = |line: &str| line.len() - line.trim_start_matches(' ').len();
    let least = text
        .split('\n')
        .skip(1)
        .filter(|line| !blank(line))
        .map(lead)
        .min()
        .unwrap_or(0);
    let shift = shift.max(-(least as i64));
    let mut out = String::with_capacity(text.len());
    for (k, line) in text.split('\n').enumerate() {
        if k > 0 {
            out.push('\n');
            if !blank(line) {
                if shift >= 0 {
                    out.extend(std::iter::repeat_n(' ', shift as usize));
                } else {
                    out.push_str(&line[(-shift) as usize..]);
                    continue;
                }
            }
        }
        out.push_str(line);
    }
    out
}

/// Whether two texts of one declaration have the same tokens, comments and
/// tree (§4.1, on one declaration).
fn same_decl(before: &str, after: &str) -> bool {
    let file = stitchwort_syntax::SourceMap::new().add("decl.sw", "");
    let (Ok(a), Ok(b)) = (lex_with_trivia(file, before), lex_with_trivia(file, after)) else {
        return false;
    };
    if check::same_tokens(before, &a, after, &b).is_err() || check::same_comments(&a, &b).is_err() {
        return false;
    }
    match equivalence::parse_shape(after) {
        Ok(shape) => equivalence::parse_shape(before).is_ok_and(|old| old == shape),
        Err(_) => false,
    }
}

/// A comment's text without spaces at the end of its line (R18). The rest
/// is never changed (R16).
fn comment_text(comment: &Comment) -> &str {
    comment.text.trim_end_matches(' ')
}

#[cfg(test)]
mod tests {
    use super::shift_lines;

    #[test]
    fn text_block_lines_move_together_as_far_as_they_can() {
        let block = "\"\"\"\n    a\n      b\n\n    \"\"\"";
        assert_eq!(
            shift_lines(block, 2),
            "\"\"\"\n      a\n        b\n\n      \"\"\""
        );
        assert_eq!(shift_lines(block, -2), "\"\"\"\n  a\n    b\n\n  \"\"\"");
        // At most 4 to the left: `a` reaches column 0.
        assert_eq!(shift_lines(block, -9), "\"\"\"\na\n  b\n\n\"\"\"");
        // A line of only spaces stays as it is.
        assert_eq!(shift_lines("x\n   \ny", 2), "x\n   \n  y");
    }
}
