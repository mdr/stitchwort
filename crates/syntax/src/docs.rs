//! The doc of a declaration, read from the comments around it
//! (docs/proposals/documentation.md §4, §5.1).
//!
//! Docs are not part of elaboration: a consumer that shows one (search, the
//! index, hover) calls [`docs`] on the file's text, which lexes it with
//! trivia, and looks the declaration up by the byte offset of its name.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::{Decl, Import, Module};
use crate::lexer::{Comment, Tok, Trivia, lex_recovering_with_trivia};
use crate::parser::{DEFAULT_STACK, decl_ranges, parse_module_recovering, parse_namespace_line};
use crate::{FileId, Span};

/// The marker of a doc line (D2134). Only `--|` lines make a doc; since
/// SW-1044 a plain `--` comment is a note, never a doc (D2142's fallback is
/// gone). The JSON's `docMarker` is always this.
pub const DOC_MARKER: &str = "--|";

/// A declaration's doc.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Doc {
    /// The doc with its markers removed, lines joined with `\n`.
    pub text: String,
    /// The first sentence of the first paragraph ([`summary`]).
    pub summary: String,
    /// The links in the doc (§7), in the order [`link_ranges`] finds them in
    /// `text`.
    pub links: Vec<DocLink>,
    /// From the first doc line to the end of the last, for diagnostics and
    /// links.
    pub span: Span,
}

impl Doc {
    fn new(lines: &[String], links: Vec<DocLink>, span: Span) -> Doc {
        let text = lines.join("\n");
        Doc {
            summary: summary(&text),
            text,
            links,
            span,
        }
    }
}

/// A link in a doc: ``[`Name`]``, where `Name` is name-shaped (§7, D2149).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DocLink {
    /// The name between the backticks.
    pub name: String,
    /// The whole link, in the source.
    pub span: Span,
}

/// Whether `name` is name-shaped: letters, digits, `_`, `'` and `.`,
/// starting with a letter or `_`.
fn name_shaped(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && name
            .chars()
            .all(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.'))
}

/// The links in one line of doc text, as `(start, end, name)`: byte ranges
/// of the whole ``[`Name`]``.
pub fn link_ranges(line: &str) -> Vec<(usize, usize, &str)> {
    let mut found = Vec::new();
    let mut from = 0;
    while let Some(open) = line[from..].find("[`") {
        let start = from + open;
        let name_at = start + 2;
        let Some(close) = line[name_at..].find("`]") else {
            break;
        };
        let name = &line[name_at..name_at + close];
        if name_shaped(name) {
            let end = name_at + close + 2;
            found.push((start, end, name));
            from = end;
        } else {
            from = name_at;
        }
    }
    found
}

/// The links of one `--|` comment (its text from `--|` to the end of the
/// line, at `span`).
fn comment_links(comment: &str, span: Span) -> Vec<DocLink> {
    link_ranges(comment)
        .into_iter()
        .map(|(start, end, name)| DocLink {
            name: name.to_string(),
            span: Span::new(
                span.file,
                span.start + start as u32,
                span.start + end as u32,
            ),
        })
        .collect()
}

/// The links in the `--|` comments at `bars` (as the lexer records them) of
/// `text`: what a file's namespace checks after it is checked (§7).
pub fn bar_links(text: &str, bars: &[Span]) -> Vec<DocLink> {
    bars.iter()
        .flat_map(|s| comment_links(&text[s.start as usize..s.end as usize], *s))
        .collect()
}

/// The names a doc link `name` may mean, in the order they are tried after
/// the file's own resolution (D2153): a full name, then a library name
/// without `Std.`, then (in a namespace) one of its own: `namespace` is the
/// namespace of the file, if it has one.
pub fn link_candidates(name: &str, namespace: Option<&str>) -> Vec<String> {
    let mut out = Vec::new();
    if let Some(ns) = namespace {
        out.push(format!("{ns}.{name}"));
    }
    out.push(name.to_string());
    if !name.starts_with("Std.") {
        out.push(format!("Std.{name}"));
    }
    out
}

/// What a doc link `name` may mean through the file's `imports` (SW-1045),
/// in addition to [`link_candidates`]: `import N (x)` makes `x` (and `x.y`)
/// mean `N.x` (`N.x.y`); `import N (x as z)`, `z`; `import N (..)`, every
/// name of `N`. The namespace `N` is tried as written, under the file's
/// `namespace` and under `Std.`, as `link_candidates` does. The caller keeps
/// the candidates that exist. This is the syntax of imports only, with no
/// elaboration: the file's imports are read by [`file_imports`].
pub fn link_candidates_with_imports(
    name: &str,
    namespace: Option<&str>,
    imports: &[Import],
) -> Vec<String> {
    let mut out = link_candidates(name, namespace);
    let (first, rest) = match name.split_once('.') {
        Some((first, rest)) => (first, Some(rest)),
        None => (name, None),
    };
    for import in imports {
        for base in link_candidates(&import.path.text, namespace) {
            for item in &import.items {
                if item.local().text == first {
                    let key = format!("{base}.{}", item.name.text);
                    out.push(rest.map_or(key.clone(), |r| format!("{key}.{r}")));
                }
            }
            if import.everything.is_some() {
                out.push(format!("{base}.{name}"));
            }
        }
    }
    out.dedup();
    out
}

/// The `import` lines of a file, parsed without elaborating (a file that
/// doesn't parse gives those before the error).
pub fn file_imports(file: FileId, text: &str) -> Vec<Import> {
    parse_module_recovering(file, text, DEFAULT_STACK).0.imports
}

/// The docs of a file's declarations, by the byte offset of the declaration's
/// name (of the `test` keyword for a test, which has none): top-level
/// declarations, and the constructors, fields and operations that have a line
/// to themselves. A declaration that doesn't lex or doesn't parse is left
/// out; the rest of the file is still read.
pub fn docs(file: FileId, text: &str) -> BTreeMap<u32, Doc> {
    let mut found = BTreeMap::new();
    let (lexed, _) = lex_recovering_with_trivia(file, text);
    let Ok(groups) = decl_ranges(&lexed.tokens) else {
        return found;
    };
    let (module, _) = parse_module_recovering(file, text, DEFAULT_STACK);
    let tokens = &lexed.tokens;
    let (tops, members) = names(&module);

    // A top-level declaration's doc is above the first token of its group,
    // so above its attributes. A group has one declaration (a signature's
    // equations have no name of their own here).
    let mut done: BTreeSet<usize> = BTreeSet::new();
    for offset in tops {
        let group = groups.partition_point(|g| tokens[g.start].span.start <= offset);
        let Some(group) = group.checked_sub(1) else {
            continue;
        };
        if !done.insert(group) {
            continue;
        }
        if let Some(doc) = attached_doc(&lexed.trivia, groups[group].start) {
            found.insert(offset, doc);
        }
    }

    // A member's doc is above its line, if it is the only member there and
    // starts it (after the `|` or `,` that introduces it), and the line isn't
    // the declaration's own.
    let mut lines: BTreeMap<usize, Vec<u32>> = BTreeMap::new();
    for offset in members {
        let Ok(i) = tokens.binary_search_by_key(&offset, |t| t.span.start) else {
            continue;
        };
        let mut first = i;
        while !tokens[first].line_start && first > 0 {
            first -= 1;
        }
        let introduced = matches!(
            tokens[first].tok,
            Tok::Pipe | Tok::Comma | Tok::LBrace | Tok::LParen | Tok::At
        );
        if tokens[first].column != 0 && (first == i || introduced) {
            lines.entry(first).or_default().push(offset);
        }
    }
    for (first, offsets) in lines {
        if let [offset] = offsets[..]
            && let Some(doc) = attached_doc(&lexed.trivia, first)
        {
            found.insert(offset, doc);
        }
    }
    found
}

/// The doc of a file as a whole (§4): the comment runs before its first
/// declaration, other than the run that is that declaration's own, joined as
/// paragraphs. A `namespace` or `import` line is not a declaration here, so
/// every run above one is the file's. Only `--|` lines count.
pub fn file_doc(file: FileId, text: &str) -> Option<Doc> {
    let (lexed, _) = lex_recovering_with_trivia(file, text);
    let groups = decl_ranges(&lexed.tokens).ok()?;
    let (comments, own) = match groups.first() {
        Some(group) => {
            let trivia = lexed.trivia.get(group.start)?;
            let header = matches!(
                lexed.tokens[group.start].tok,
                Tok::KwNamespace | Tok::KwImport
            );
            let own = if header { 0 } else { attached(trivia).len() };
            (&trivia.leading[..], own)
        }
        None => (&lexed.eof.leading[..], 0),
    };
    let comments = &comments[..comments.len() - own];
    let mut lines: Vec<String> = Vec::new();
    let mut links = Vec::new();
    let mut span: Option<Span> = None;
    for (n, comment) in comments.iter().enumerate() {
        // A new run starts after a blank line: a paragraph break.
        if n > 0
            && comment.blank_lines_before > 0
            && lines.last().is_some_and(|l| !l.is_empty())
            && body(comment).is_some()
        {
            lines.push(String::new());
        }
        if let Some(line) = body(comment) {
            lines.push(line);
            span = Some(span.map_or(comment.span, |s| s.to(comment.span)));
            links.extend(comment_links(&comment.text, comment.span));
        }
    }
    finish(lines, links, span?)
}

/// The namespace a file's doc belongs to (§4). A library file's doc belongs
/// to its folder's namespace (`List/Toolkit.sw` to `Std.List`), and a file
/// of the core (`core/…`) to none, since its names are in many; a
/// program's file's belongs to its `namespace` line's namespace, if it has
/// one. `std_path` is a library file's path under `std/`.
pub fn file_doc_namespace(file: FileId, text: &str, std_path: Option<&str>) -> Option<String> {
    match std_path {
        Some(path) => {
            let (folder, _) = path.split_once('/')?;
            (folder != "core").then(|| format!("Std.{folder}"))
        }
        None => {
            let line = parse_namespace_line(file, text).ok()??;
            Some(line.path.text)
        }
    }
}

/// The offsets of a module's declarations' names: top-level ones (a test's is
/// its start), and members.
fn names(module: &Module) -> (Vec<u32>, Vec<u32>) {
    let mut tops = Vec::new();
    let mut members = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::Signature { name, .. } => tops.push(name.span.start),
            Decl::Data {
                name,
                ctors,
                record,
                ..
            } => {
                tops.push(name.span.start);
                for ctor in ctors {
                    if *record {
                        let fields = ctor.fields.iter().flat_map(|binder| &binder.names);
                        members.extend(fields.map(|field| field.span.start));
                    } else {
                        members.push(ctor.name.span.start);
                    }
                }
            }
            Decl::Ability { name, ops, .. } => {
                tops.push(name.span.start);
                members.extend(ops.iter().map(|(op, _)| op.span.start));
            }
            Decl::Test { span, .. } => tops.push(span.start),
            Decl::Equation { .. } => {}
        }
    }
    (tops, members)
}

/// The comment run directly above a token: the last group of its leading
/// comments with no blank line inside it or before the token.
fn attached(trivia: &Trivia) -> &[Comment] {
    let leading = &trivia.leading;
    if leading.is_empty() || trivia.blank_lines_before != 0 {
        return &[];
    }
    let mut start = leading.len() - 1;
    while start > 0 && leading[start].blank_lines_before == 0 {
        start -= 1;
    }
    &leading[start..]
}

/// The doc of the declaration or member whose first token is `tokens[at]`.
fn attached_doc(trivia: &[Trivia], at: usize) -> Option<Doc> {
    let run = attached(trivia.get(at)?);
    let mut lines = Vec::new();
    let mut links = Vec::new();
    let mut span: Option<Span> = None;
    for comment in run {
        if let Some(line) = body(comment) {
            lines.push(line);
            span = Some(span.map_or(comment.span, |s| s.to(comment.span)));
            links.extend(comment_links(&comment.text, comment.span));
        }
    }
    finish(lines, links, span?)
}

/// A comment's line of the doc: the text after `--|` (and one space) of a
/// `--|` comment, and nothing for any other.
fn body(comment: &Comment) -> Option<String> {
    let rest = comment.text.strip_prefix("--|")?;
    let rest = rest.strip_prefix(' ').unwrap_or(rest);
    Some(rest.trim_end().to_string())
}

/// A doc from its lines, with the blank lines at its ends dropped; none if
/// nothing is left.
fn finish(mut lines: Vec<String>, links: Vec<DocLink>, span: Span) -> Option<Doc> {
    while lines.last().is_some_and(|l| l.is_empty()) {
        lines.pop();
    }
    let skip = lines.iter().take_while(|l| l.is_empty()).count();
    lines.drain(..skip);
    (!lines.is_empty()).then(|| Doc::new(&lines, links, span))
}

/// The longest a summary is, in characters.
const SUMMARY_LIMIT: usize = 160;

/// The first sentence of the first paragraph of `text`, its lines joined by
/// single spaces: up to the first `.` outside backticks that is followed by
/// whitespace or the end, other than the ones in `e.g.` and `i.e.`. One of
/// more than 160 characters is cut at the last space before the 160th that
/// is outside backticks, and ends in `…`.
pub fn summary(text: &str) -> String {
    let paragraph: Vec<&str> = text
        .lines()
        .map(str::trim)
        .skip_while(|l| l.is_empty())
        .take_while(|l| !l.is_empty())
        .collect();
    let joined: Vec<char> = paragraph.join(" ").chars().collect();
    let mut quoted = false;
    let mut end = joined.len();
    for (i, &c) in joined.iter().enumerate() {
        match c {
            '`' => quoted = !quoted,
            '.' if !quoted && joined.get(i + 1).is_none_or(|n| n.is_whitespace()) => {
                // `e.g.` and `i.e.`: the `.` after a lone letter that follows
                // `x.` at a word's start.
                let abbreviated = i >= 3
                    && matches!(joined[i - 3..i], ['e', '.', 'g'] | ['i', '.', 'e'])
                    && (i == 3 || !joined[i - 4].is_alphanumeric());
                if !abbreviated {
                    end = i + 1;
                    break;
                }
            }
            _ => {}
        }
    }
    let sentence = &joined[..end];
    if sentence.len() <= SUMMARY_LIMIT {
        return sentence.iter().collect();
    }
    let mut quoted = false;
    let mut cut = None;
    for (i, &c) in sentence.iter().enumerate().take(SUMMARY_LIMIT) {
        match c {
            '`' => quoted = !quoted,
            ' ' if !quoted => cut = Some(i),
            _ => {}
        }
    }
    match cut {
        Some(i) => {
            let mut cut: String = sentence[..i].iter().collect();
            cut.push('…');
            cut
        }
        None => sentence.iter().collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SourceMap;

    fn file() -> FileId {
        SourceMap::new().add("input.sw", "")
    }

    /// The doc text of `text`, by the offset of `needle` plus `skip` (the
    /// name's start).
    fn doc_at(text: &str, needle: &str, skip: usize) -> Option<String> {
        let offset = text.find(needle).expect("the needle is in the text") + skip;
        docs(file(), text).remove(&(offset as u32)).map(|d| d.text)
    }

    fn bar(text: &str) -> Option<String> {
        Some(text.to_string())
    }

    #[test]
    fn a_bar_run_above_a_definition_is_its_doc() {
        let text = "--| Adds one.\n--| Twice.\ndef inc (n: Nat): Nat := n + 1\n";
        assert_eq!(doc_at(text, "inc", 0), bar("Adds one.\nTwice."));
    }

    #[test]
    fn a_plain_run_above_a_declaration_is_not_a_doc() {
        let text = "-- Adds one.\n--   indented\ndef inc (n: Nat): Nat := n + 1\n";
        assert_eq!(doc_at(text, "inc", 0), None);
        assert!(docs(file(), text).is_empty());
        // Nor above an attribute, a type or a member.
        let more =
            "-- Note.\n@[noReceiver]\ndef h: Nat := 1\n\n-- Note.\ntype T =\n  -- Note.\n  | A\n";
        assert!(docs(file(), more).is_empty());
    }

    #[test]
    fn plain_lines_beside_marked_ones_are_maintainer_notes() {
        let text = "-- note above\n--| Adds one.\n-- note between\n--|\n--| More.\n-- note below\ndef inc: Nat := 1\n";
        assert_eq!(doc_at(text, "inc", 0), bar("Adds one.\n\nMore."));
    }

    #[test]
    fn a_blank_line_ends_the_run() {
        let text = "--| Above.\n\ndef a: Nat := 1\n\n--| Far.\n\n--| Near.\ndef b: Nat := 2\n";
        assert_eq!(doc_at(text, "a:", 0), None);
        assert_eq!(doc_at(text, "b:", 0), bar("Near."));
    }

    #[test]
    fn a_blank_line_inside_a_run_keeps_only_the_last_group() {
        let text = "--| First.\n--| Still first.\n\n--| Second.\ndef a: Nat := 1\n";
        assert_eq!(doc_at(text, "a:", 0), bar("Second."));
    }

    #[test]
    fn a_bare_marker_line_is_a_paragraph_break() {
        let text = "--| One.\n--|\n--| Two.\ndef a: Nat := 1\n";
        assert_eq!(doc_at(text, "a:", 0), bar("One.\n\nTwo."));
    }

    #[test]
    fn the_doc_goes_above_the_attributes() {
        let text = "--| Not for receivers.\n@[noReceiver]\ndef helper: Nat := 1\n";
        assert_eq!(doc_at(text, "helper", 0), bar("Not for receivers."));
        let split = "--| Above.\n@[noReceiver]\n@[js.name \"h\"]\ndef helper: Nat := 1\n";
        assert_eq!(doc_at(split, "helper", 0), bar("Above."));
    }

    #[test]
    fn a_comment_between_an_attribute_and_its_definition_is_no_doc() {
        let text = "@[noReceiver]\n--| Between.\ndef helper: Nat := 1\n";
        assert_eq!(doc_at(text, "helper", 0), None);
        // The run above the attribute is still the doc.
        let both = "--| Above.\n@[noReceiver]\n--| Between.\ndef helper: Nat := 1\n";
        assert_eq!(doc_at(both, "helper", 0), bar("Above."));
    }

    #[test]
    fn a_trailing_comment_is_never_a_doc() {
        let text = "def a: Nat := 1 --| trailing\ndef b: Nat := 2 -- trailing\n";
        assert_eq!(doc_at(text, "a:", 0), None);
        assert_eq!(doc_at(text, "b:", 0), None);
        // Nor does one on the previous declaration's line reach the next.
        let next = "def a: Nat := 1 -- trailing\ndef b: Nat := 2\n";
        assert_eq!(doc_at(next, "b:", 0), None);
    }

    #[test]
    fn equations_have_no_doc_of_their_own() {
        let text = "--| Length.\ndef len: List a → Nat\n  -- the empty list\n  | Nil => 0\n  | Cons x xs => 1\n";
        assert_eq!(doc_at(text, "len", 0), bar("Length."));
        assert_eq!(doc_at(text, "Nil =>", 0), None);
    }

    #[test]
    fn constructors_with_a_line_each_have_docs() {
        let text = "\
--| A shape.
type Shape =
  --| A point.
  | Dot
  -- A circle.
  | Circle (radius: Nat)
  | Square (side: Nat)
";
        assert_eq!(doc_at(text, "Shape", 0), bar("A shape."));
        assert_eq!(doc_at(text, "Dot", 0), bar("A point."));
        assert_eq!(doc_at(text, "Circle", 0), None);
        assert_eq!(doc_at(text, "Square", 0), None);
    }

    #[test]
    fn fields_and_operations_have_docs() {
        let text = "\
type Sized (a: Type) =
  --| The items.
  { items: List a
  --| How many.
  , size: Nat
  }

ability State (s: Type) where
  --| The current state.
  get : () -> {State s} s
  put : s -> {State s} ()
";
        assert_eq!(doc_at(text, "items:", 0), bar("The items."));
        assert_eq!(doc_at(text, "size", 0), bar("How many."));
        assert_eq!(doc_at(text, "get", 0), bar("The current state."));
        assert_eq!(doc_at(text, "put", 0), None);
    }

    #[test]
    fn a_member_sharing_a_line_has_no_doc() {
        // On the declaration's own line, and beside another member.
        let text = "\
--| A pair.
type Pair = { first: Nat, second: Nat }

type Two =
  --| Shared.
  | A | B

type Own = | One
  --| Not first.
  | Two
";
        assert_eq!(doc_at(text, "Pair", 0), bar("A pair."));
        assert_eq!(doc_at(text, "first", 0), None);
        assert_eq!(doc_at(text, "second", 0), None);
        assert_eq!(doc_at(text, "| A", 2), None);
        assert_eq!(doc_at(text, "| B", 2), None);
        assert_eq!(doc_at(text, "One", 0), None);
        assert_eq!(doc_at(text, "| Two", 2), bar("Not first."));
    }

    #[test]
    fn a_comment_after_a_member_on_its_line_is_no_doc() {
        let text = "type T =\n  | A -- first\n  | B\n";
        assert_eq!(doc_at(text, "| B", 2), None);
        assert_eq!(doc_at(text, "| A", 2), None);
    }

    #[test]
    fn a_test_has_a_doc_keyed_by_its_keyword() {
        let text = "--| Checks it.\ntest \"a\" := True\n";
        assert_eq!(doc_at(text, "test", 0), bar("Checks it."));
    }

    #[test]
    fn a_declaration_after_a_failed_one_still_has_its_doc() {
        let text = "--| Broken.\ndef a: := \n\n--| Fine.\ndef b: Nat := 1\n";
        assert_eq!(doc_at(text, "b:", 0), bar("Fine."));
    }

    #[test]
    fn the_span_covers_the_doc_lines() {
        let text = "-- note\n--| Doc.\ndef a: Nat := 1\n";
        let doc = docs(file(), text).into_values().next().expect("a doc");
        assert_eq!(&text[doc.span.range()], "--| Doc.");
    }

    fn file_doc_of(text: &str) -> Option<String> {
        file_doc(file(), text).map(|d| d.text)
    }

    #[test]
    fn a_file_doc_is_the_runs_before_the_first_declaration_but_its_own() {
        let text = "--| One.\n\n--| Two.\n--| Three.\n\n--| Of `a`.\ndef a: Nat := 1\n";
        assert_eq!(file_doc_of(text), bar("One.\n\nTwo.\nThree."));
        // With a blank line before the declaration, no run is its own.
        let apart = "--| One.\n\ndef a: Nat := 1\n";
        assert_eq!(file_doc_of(apart), bar("One."));
        let own = "--| Of `a`.\ndef a: Nat := 1\n";
        assert_eq!(file_doc_of(own), None);
    }

    #[test]
    fn a_file_doc_may_sit_above_the_namespace_line() {
        let text = "--| Grids.\n--|\n--| More.\n\nnamespace Aoc.Common\nimport Std (List)\n\n--| Of `a`.\ndef a: Nat := 1\n";
        assert_eq!(file_doc_of(text), bar("Grids.\n\nMore."));
        // Even with no blank line: a `namespace` line has no doc of its own.
        let close = "--| Grids.\nnamespace Aoc.Common\n\ndef a: Nat := 1\n";
        assert_eq!(file_doc_of(close), bar("Grids."));
    }

    #[test]
    fn plain_runs_beside_marked_ones_are_not_in_a_file_doc() {
        let text = "-- Maintainer note.\n\n--| For users.\n\n--| More.\n\ndef a: Nat := 1\n";
        assert_eq!(file_doc_of(text), bar("For users.\n\nMore."));
    }

    #[test]
    fn a_file_of_only_plain_comments_has_no_file_doc() {
        assert_eq!(
            file_doc_of("-- Notes.\n\n-- More.\n\ndef a: Nat := 1\n"),
            None
        );
        assert_eq!(
            file_doc_of("-- Notes.\nnamespace N\n\ndef a: Nat := 1\n"),
            None
        );
        assert_eq!(file_doc_of("-- Only notes here.\n"), None);
    }

    #[test]
    fn a_file_with_only_comments_has_a_doc() {
        assert_eq!(file_doc_of("--| Nothing here.\n"), bar("Nothing here."));
        assert_eq!(file_doc_of("def a: Nat := 1\n"), None);
    }

    #[test]
    fn a_file_doc_belongs_to_a_namespace() {
        let f = file();
        let std = |path| file_doc_namespace(f, "", Some(path));
        assert_eq!(std("List/Toolkit.sw").as_deref(), Some("Std.List"));
        assert_eq!(std("Text/Text.sw").as_deref(), Some("Std.Text"));
        assert_eq!(std("core/Data.sw"), None);
        let project = "-- Doc.\nnamespace Aoc.Common\n";
        assert_eq!(
            file_doc_namespace(f, project, None).as_deref(),
            Some("Aoc.Common")
        );
        assert_eq!(file_doc_namespace(f, "def a: Nat := 1\n", None), None);
    }

    #[test]
    fn a_summary_is_the_first_sentence_with_its_lines_joined() {
        assert_eq!(
            summary("Keeps the `Some` results, in order. `f` may perform\nabilities."),
            "Keeps the `Some` results, in order."
        );
        assert_eq!(
            summary("One\nsentence over\nlines.\n\nNext paragraph. Two."),
            "One sentence over lines."
        );
        assert_eq!(summary("No full stop"), "No full stop");
        assert_eq!(summary("Ends at the end."), "Ends at the end.");
    }

    #[test]
    fn a_sentence_ends_at_any_whitespace_after_a_stop() {
        assert_eq!(summary("Ends.\tHere."), "Ends.");
        assert_eq!(summary("Ends.\nHere."), "Ends.");
        // Not at a stop inside a name, a number or backticks.
        assert_eq!(
            summary("`List.map` is 1.5 times Std.List.map."),
            "`List.map` is 1.5 times Std.List.map."
        );
        assert_eq!(summary("Uses `a. b` here. Then."), "Uses `a. b` here.");
    }

    #[test]
    fn a_summary_skips_e_g_and_i_e() {
        assert_eq!(
            summary("Takes a unit, e.g. `Nat`, or i.e. a number. Then."),
            "Takes a unit, e.g. `Nat`, or i.e. a number."
        );
        // A word that merely ends like one.
        assert_eq!(summary("Is the pie.g. Then."), "Is the pie.g.");
    }

    #[test]
    fn a_long_summary_is_cut_at_a_space_outside_backticks() {
        // `Text.padLeft`'s doc in std: its first sentence is 162 characters.
        let sentence = "`Text.padLeft text n char` is enough copies of `char` followed by `text` to make it n characters long (it is `text` itself when that is already n long or longer).";
        assert_eq!(sentence.chars().count(), 162);
        assert_eq!(
            summary(sentence),
            "`Text.padLeft text n char` is enough copies of `char` followed by `text` to make it n characters long (it is `text` itself when that is already n long or…"
        );
        // A space inside backticks is not a place to cut.
        let long = format!("{} `a b c`.", "word ".repeat(40));
        let cut = summary(&long);
        assert!(cut.ends_with("word…"), "{cut}");
        let inside = format!("{}`{}`.", "w ".repeat(78), "x y ".repeat(10));
        let cut = summary(&inside);
        assert_eq!(cut.matches('`').count() % 2, 0, "{cut}");
    }

    fn names(line: &str) -> Vec<&str> {
        link_ranges(line).into_iter().map(|(_, _, n)| n).collect()
    }

    #[test]
    fn only_a_backticked_name_shaped_name_in_brackets_is_a_link() {
        assert_eq!(
            names("See [`List.filterMap`] and [`_x'1`], [`Std.Nat`]."),
            ["List.filterMap", "_x'1", "Std.Nat"]
        );
        // Bare brackets, and anything that isn't a name (D2149).
        assert!(names("[x] [List.map] [`not a name`] [``] [`1x`] [`a-b`]").is_empty());
        // The prose that looked like links in the aoc docs.
        assert!(names("every `[` has its `]`; its `[` is; its `]`").is_empty());
        assert!(names("`ESC [` then bytes, and an unclosed [`").is_empty());
        // A failed candidate doesn't hide the link after it.
        assert_eq!(names("`[` [`a`]"), ["a"]);
    }

    #[test]
    fn a_link_has_its_span_in_the_source() {
        let text = "def a: Nat := 1\n--| Uses [`a`] and\n--| [`b`].\ndef b: Nat := 2\n";
        let (_, doc) = docs(file(), text).into_iter().next_back().unwrap();
        let shown: Vec<(&str, &str)> = doc
            .links
            .iter()
            .map(|l| {
                (
                    l.name.as_str(),
                    &text[l.span.start as usize..l.span.end as usize],
                )
            })
            .collect();
        assert_eq!(shown, [("a", "[`a`]"), ("b", "[`b`]")]);
    }

    #[test]
    fn plain_notes_and_trailing_comments_have_no_links() {
        let text = "-- [`a`]\ndef a: Nat := 1 --| [`a`]\n--| [`a`]\n-- [`b`]\ndef b: Nat := 2\n";
        let docs = docs(file(), text);
        // `a`'s own-line `--` note is no doc; `b` has one `--|` line.
        assert_eq!(docs.len(), 1);
        let only = docs.values().next().unwrap();
        assert_eq!(only.links.len(), 1);
    }

    #[test]
    fn a_module_has_the_links_of_its_bar_comments_only() {
        let text = "\
--| File doc, [`a`].
-- note [`no`]
namespace N

--| Above [`b`].
def a: Nat := 1 --| trailing [`no`]
def s := \"--| [`no`]\"
";
        let mut sources = SourceMap::new();
        let id = sources.add("input.sw", text);
        let (module, _) = crate::parse_module_recovering(id, text, crate::DEFAULT_STACK);
        let links: Vec<&str> = module.doc_links.iter().map(|l| l.name.as_str()).collect();
        assert_eq!(links, ["a", "b"]);
    }
}
