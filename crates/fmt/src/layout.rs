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
//! A style rule picks the offset (R1, R2); where none applies, the line keeps
//! its old distance from its parent, moving with it (the copy path, counted
//! in [`Stats::copied_lines`]). If the rules would reorder or merge the
//! columns of a parent's children, all of them keep their old distances.
//! Lines at column 0 stay there: they start or continue declarations.
//!
//! Each declaration is checked on its own as it is built (the same checks as
//! §4.1), and one that fails is copied unchanged and counted in
//! [`Stats::verbatim_decls`], so a gap in the rules costs one declaration's
//! formatting rather than the file's.

use std::collections::HashMap;
use std::ops::Range;

use stitchwort_syntax::{Comment, Lexed, Tok, Token, equivalence, lex_with_trivia};

use crate::doc::{Doc, print};
use crate::spacing::{Gap, gap};
use crate::{Stats, check};

/// The indentation unit (R1).
const INDENT: usize = 2;
/// A definition's header continuation lines (R1).
const HEADER_INDENT: usize = 4;

/// One line of code: the tokens from one that starts a line up to the next
/// (a `"""` text block keeps its tokens in the line it starts on).
#[derive(Clone, Copy, Debug)]
struct Line {
    first: usize,
    end: usize,
    column: usize,
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
    pub(crate) stats: Stats,
}

impl<'a> Layout<'a> {
    pub(crate) fn new(text: &'a str, lexed: &'a Lexed) -> Self {
        Layout {
            text,
            lexed,
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
            let text = self.decl(range.clone());
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
    /// formatted text if that passes the checks, otherwise its source.
    fn decl(&mut self, range: Range<usize>) -> String {
        let before = self.decl_source(&range);
        let saved = self.stats;
        let doc = self.decl_doc(range.clone());
        let after = print(&doc, None);
        if after == before || same_decl(before, &after) {
            return after;
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

    fn decl_doc(&mut self, range: Range<usize>) -> Doc {
        let tokens = self.tokens();
        let mut lines: Vec<Line> = Vec::new();
        for k in range.clone() {
            if k == range.start || tokens[k].line_start {
                lines.push(Line {
                    first: k,
                    end: k + 1,
                    column: tokens[k].column as usize,
                });
            } else if let Some(line) = lines.last_mut() {
                line.end = k + 1;
            }
        }
        let header_end = self.header_end(range.clone());
        let indents = self.indents(&lines, header_end);
        let mut docs = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            let mut parts = Vec::new();
            if i > 0 {
                let trivia = &self.lexed.trivia[line.first];
                // R17: no blank line at the start of a body.
                let opens = self.ends_with_opener(&lines[i - 1]);
                for (c, comment) in trivia.leading.iter().enumerate() {
                    parts.push(Doc::HardLine);
                    if comment.blank_lines_before > 0 && !(c == 0 && opens) {
                        parts.push(Doc::HardLine);
                    }
                    // R16: an own-line comment is indented like the code
                    // line after it.
                    parts.push(Doc::text(comment_text(comment)));
                }
                parts.push(Doc::HardLine);
                if trivia.blank_lines_before > 0 && !(trivia.leading.is_empty() && opens) {
                    parts.push(Doc::HardLine);
                }
            }
            let shift = indents[i] as i64 - line.column as i64;
            parts.push(self.line_doc(line, shift));
            docs.push(Doc::nest(indents[i], Doc::Concat(parts)));
        }
        Doc::Concat(docs)
    }

    /// The token ending a declaration's header, after which its lines are
    /// its body: the first `:=` (or arm) of a definition, the `=` of a data
    /// type or interface, an ability's `where`. `None` for declarations
    /// without a header (imports, the namespace line).
    fn header_end(&self, range: Range<usize>) -> Option<usize> {
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
                return Some(j);
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
    fn ends_with_opener(&self, line: &Line) -> bool {
        matches!(
            self.tokens()[line.end - 1].tok,
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
    fn indents(&mut self, lines: &[Line], header_end: Option<usize>) -> Vec<usize> {
        let tokens = self.tokens();
        // The parent of each line, by a stack of lines with rising columns.
        let mut parent: Vec<Option<usize>> = Vec::with_capacity(lines.len());
        let mut stack: Vec<usize> = Vec::new();
        for (i, line) in lines.iter().enumerate() {
            while stack
                .last()
                .is_some_and(|&j| lines[j].column >= line.column)
            {
                stack.pop();
            }
            parent.push(stack.last().copied());
            stack.push(i);
        }
        let part = |i: usize| -> Part {
            let line = &lines[i];
            let under_top = parent[i].is_some_and(|p| lines[p].column == 0);
            let in_header = header_end.is_some_and(|h| {
                line.first < h || (line.first == h && tokens[h].tok != Tok::Pipe && line.column > 0)
            });
            if under_top && in_header {
                Part::Header
            } else {
                Part::Main
            }
        };
        // The offset each group of lines (same parent, part and old column)
        // asks for: `Some` from a rule, `None` to keep its distance.
        type Key = (usize, Part, usize);
        let mut groups: Vec<(Key, Option<usize>)> = Vec::new();
        let mut index: HashMap<Key, usize> = HashMap::new();
        let mut group_of: Vec<Option<usize>> = vec![None; lines.len()];
        for (i, line) in lines.iter().enumerate() {
            let Some(p) = parent[i] else { continue };
            let key = (p, part(i), line.column);
            if let Some(&g) = index.get(&key) {
                group_of[i] = Some(g);
                continue;
            }
            index.insert(key, groups.len());
            let top = lines[p].column == 0;
            let wanted = if top && tokens[line.first].tok == Tok::Pipe {
                // R1: arms (and constructors) at +2.
                Some(INDENT)
            } else if key.1 == Part::Header {
                // R1: header continuation lines at +4.
                Some(HEADER_INDENT)
            } else if p + 1 == i
                && matches!(
                    tokens[lines[p].end - 1].tok,
                    Tok::ColonEq | Tok::FatArrow | Tok::KwWhere | Tok::KwWith
                )
            {
                // R2: a body on the next line after `:=` or `=>` (or an
                // ability's `where`, a `match`'s `with`) at +2.
                Some(INDENT)
            } else if top && header_end.is_some_and(|h| line.first > h) {
                // R2: the lines of a declaration's body at +2.
                Some(INDENT)
            } else {
                None
            };
            group_of[i] = Some(groups.len());
            groups.push((key, wanted));
        }
        // The rules must keep the order of each parent's children's columns.
        let mut siblings: HashMap<(usize, Part), Vec<(usize, usize)>> = HashMap::new();
        for (g, ((p, part, column), _)) in groups.iter().enumerate() {
            siblings.entry((*p, *part)).or_default().push((*column, g));
        }
        for ((p, _), mut members) in siblings {
            members.sort_unstable();
            let offset = |g: usize| {
                let ((_, _, column), wanted) = groups[g];
                wanted.unwrap_or(column - lines[p].column)
            };
            let ordered = members.windows(2).all(|w| offset(w[0].1) < offset(w[1].1));
            if !ordered {
                for (_, g) in members {
                    groups[g].1 = None;
                }
            }
        }
        let mut indents = vec![0usize; lines.len()];
        for (i, line) in lines.iter().enumerate() {
            let (Some(p), Some(g)) = (parent[i], group_of[i]) else {
                continue;
            };
            let ((_, _, column), wanted) = groups[g];
            indents[i] = indents[p]
                + match wanted {
                    Some(offset) => offset,
                    None => {
                        self.stats.copied_lines += 1;
                        column - lines[p].column
                    }
                };
            debug_assert_eq!(column, line.column);
        }
        indents
    }

    /// A line's tokens with their spacing, and its trailing comment. A
    /// `"""` text block moves with the line: its later lines move by `shift`
    /// columns, or as near as their indentation allows (which leaves the
    /// text's value unchanged, since its common indentation is removed).
    fn line_doc(&mut self, line: &Line, shift: i64) -> Doc {
        let tokens = self.tokens();
        let mut out = String::new();
        for k in line.first..line.end {
            if k > line.first {
                let (left, right) = (&tokens[k - 1], &tokens[k]);
                let spaced = left.span.end != right.span.start;
                match gap(&left.tok, &right.tok, spaced) {
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
                let end = tokens[line.end - 1].span.end as usize;
                out.push_str(&shift_lines(&self.text[start..end], shift));
                break;
            }
            out.push_str(self.source(k));
        }
        if let Some(comment) = &self.lexed.trivia[line.end - 1].trailing {
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
        // A line of only spaces is left alone.
        assert_eq!(shift_lines("x\n   \ny", 2), "x\n   \n  y");
    }
}
