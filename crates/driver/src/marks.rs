//! What an editor draws over the text from what checking recorded
//! (docs/proposals/editor-and-playground-roadmap.md, step 2): the types of
//! `let` variables, and the colour of each resolved name.
//!
//! Like the answers in [`crate::at`] they are functions over the last
//! published [`FileAnswers`] and the editor's text, with plain results; a
//! range that no longer matches the text after an edit just finds nothing.

use stitchwort_syntax::{SourceMap, Tok, lex_recovering};

use crate::live::{FileAnswers, Place};
use crate::nav::Range;

/// Where each line of a text starts, to turn byte offsets into positions
/// (lines and UTF-16 columns) without counting from the top each time.
struct Lines<'a> {
    text: &'a str,
    starts: Vec<usize>,
}

impl<'a> Lines<'a> {
    fn new(text: &'a str) -> Self {
        let mut starts = vec![0];
        starts.extend(text.match_indices('\n').map(|(i, _)| i + 1));
        Lines { text, starts }
    }

    fn position(&self, offset: usize) -> (u32, u32) {
        let line = self.starts.partition_point(|&s| s <= offset) - 1;
        let column = self.text[self.starts[line]..offset]
            .chars()
            .map(|c| c.len_utf16() as u32)
            .sum();
        (line as u32, column)
    }
}

// ---- inlay hints --------------------------------------------------------

/// The longest type shown, in characters.
const LONGEST_HINT: usize = 60;

/// A `let` variable's type, to show after its name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetHint {
    pub line: u32,
    /// Just after the name.
    pub character: u32,
    /// `: Nat`.
    pub label: String,
}

/// The type of each `let x := e` (without a written type) that starts in
/// `within`, if given, and whose variable has a type among the published
/// references: only a variable something uses has one.
pub fn let_hints(
    file: &FileAnswers,
    place: &Place,
    text: &str,
    within: Option<Range>,
) -> Vec<LetHint> {
    let mut sources = SourceMap::new();
    let id = sources.add("hints", "");
    let tokens = lex_recovering(id, text).tokens;
    let lines = Lines::new(text);
    let mut hints = Vec::new();
    for window in tokens.windows(3) {
        let (Tok::KwLet, Tok::Lower(name), Tok::ColonEq) =
            (&window[0].tok, &window[1].tok, &window[2].tok)
        else {
            continue;
        };
        if name.starts_with('_') {
            continue;
        }
        let (start, end) = (window[1].span.start as usize, window[1].span.end as usize);
        let ((l1, c1), (l2, c2)) = (lines.position(start), lines.position(end));
        if let Some(w) = within
            && ((l2, c2) < (w[0], w[1]) || (w[2], w[3]) < (l1, c1))
        {
            continue;
        }
        let Some(ty) = file
            .binder_exactly(place, [l1, c1, l2, c2])
            .and_then(|b| b.ty)
        else {
            continue;
        };
        let shown: String = if ty.chars().count() > LONGEST_HINT {
            ty.chars().take(LONGEST_HINT - 1).chain(['…']).collect()
        } else {
            ty
        };
        hints.push(LetHint {
            line: l2,
            character: c2,
            label: format!(": {shown}"),
        });
    }
    hints
}

// ---- semantic tokens ----------------------------------------------------

/// The token types, in the order the language server's legend lists them.
pub const TOKEN_TYPES: &[&str] = &[
    "type",
    "interface",
    "enumMember",
    "property",
    "function",
    "variable",
    "theorem",
    "ability",
];

/// The token modifiers, as bits in this order.
pub const TOKEN_MODIFIERS: &[&str] = &["declaration", "defaultLibrary"];
const DECLARATION: u32 = 1;
const DEFAULT_LIBRARY: u32 = 2;

/// A name to colour: on one line, `length` UTF-16 units long.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mark {
    pub line: u32,
    pub start: u32,
    pub length: u32,
    /// An index in [`TOKEN_TYPES`].
    pub token_type: u32,
    /// Bits of [`TOKEN_MODIFIERS`].
    pub modifiers: u32,
}

/// The legend type of a name by what it resolved to (`kind` as the
/// references and the outline have it), or `None` for what isn't coloured.
fn token_type(kind: &str, signature: bool) -> Option<u32> {
    let name = match kind {
        "type" | "data" | "record" => "type",
        "interface" => "interface",
        "ctor" => "enumMember",
        "field" => "property",
        "def" if signature => "function",
        "def" | "instance" | "local" => "variable",
        "op" => "function",
        "theorem" => "theorem",
        "ability" => "ability",
        _ => return None,
    };
    TOKEN_TYPES
        .iter()
        .position(|t| *t == name)
        .map(|i| i as u32)
}

/// Every name in the file that resolved to something, and every
/// declaration, in text order. A name the file's references hold is
/// coloured by what it refers to; a declaration's own name carries the
/// `declaration` modifier, a library name `defaultLibrary`.
pub fn semantic_marks(file: &FileAnswers, place: &Place) -> Vec<Mark> {
    let mut marks = Vec::new();
    let mut push = |range: Range, ty: Option<u32>, modifiers: u32| {
        if let Some(token_type) = ty
            && range[0] == range[2]
            && range[3] > range[1]
        {
            marks.push(Mark {
                line: range[0],
                start: range[1],
                length: range[3] - range[1],
                token_type,
                modifiers,
            });
        }
    };
    for r in &file.refs {
        let library = if matches!(r.target.place, Place::Library(_)) {
            DEFAULT_LIBRARY
        } else {
            0
        };
        push(r.range, token_type(r.kind, r.signature.is_some()), library);
        // A local variable's binder is a declaration of this file.
        if r.kind == "local" && r.target.place == *place {
            push(r.target.range, token_type(r.kind, false), DECLARATION);
        }
    }
    for item in &file.outline {
        push(
            item.range,
            token_type(
                item.kind,
                item.ty.as_deref().is_some_and(|t| t.contains("->")),
            ),
            DECLARATION,
        );
    }
    marks.sort_by_key(|m| (m.line, m.start, std::cmp::Reverse(m.modifiers)));
    // The same name twice (a use and the declaration it is on), and
    // overlapping ranges, which the protocol forbids: the first stays.
    let mut kept: Vec<Mark> = Vec::with_capacity(marks.len());
    for m in marks {
        if kept
            .last()
            .is_some_and(|k| k.line == m.line && m.start < k.start + k.length)
        {
            continue;
        }
        kept.push(m);
    }
    kept
}

// ---- lexical colours ----------------------------------------------------

/// What a token looks like, before anything is resolved: for the colouring
/// of text that isn't checked (the REPL's line editor). The names a
/// resolved file gets ([`semantic_marks`]) refine these: a capitalised name
/// is `type`, or `enumMember` once it resolves to a constructor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lexical {
    Keyword,
    Number,
    /// A text or character literal, or a piece of an interpolated one.
    Text,
    /// A capitalised name, `Type` or `Prop`: a type or a constructor.
    Name,
    Operator,
    Comment,
}

impl Lexical {
    /// The legend entry ([`TOKEN_TYPES`]) the class corresponds to, if the
    /// legend has one.
    pub fn token_type(self) -> Option<&'static str> {
        match self {
            Lexical::Name => Some("type"),
            _ => None,
        }
    }
}

/// The byte ranges of `text` worth colouring, in text order. Text that
/// doesn't lex still gets what does: a declaration with a lexical error
/// loses its tokens, but its comments are found.
pub fn lexical_marks(text: &str) -> Vec<(std::ops::Range<usize>, Lexical)> {
    let mut sources = SourceMap::new();
    let id = sources.add("colour", "");
    let tokens = lex_recovering(id, text).tokens;
    let mut marks = Vec::new();
    let mut covered = 0;
    for token in &tokens {
        let range = token.span.start as usize..token.span.end as usize;
        comments_in(text, covered..range.start, &mut marks);
        covered = range.end;
        let class = match &token.tok {
            Tok::Num(_) | Tok::Float(_) => Lexical::Number,
            Tok::Str(_) | Tok::StrStart(_) | Tok::StrMid(_) | Tok::StrEnd(_) | Tok::Char(_) => {
                Lexical::Text
            }
            Tok::Upper(_) | Tok::TypeU | Tok::Prop => Lexical::Name,
            Tok::Lower(_) | Tok::Underscore | Tok::Question => continue,
            tok if tok.keyword().is_some() => Lexical::Keyword,
            Tok::LParen
            | Tok::RParen
            | Tok::LBracket
            | Tok::RBracket
            | Tok::LBrace
            | Tok::RBrace
            | Tok::InterpOpen
            | Tok::InterpClose
            | Tok::Comma
            | Tok::Semi
            | Tok::Dot
            | Tok::At => continue,
            _ => Lexical::Operator,
        };
        marks.push((range, class));
    }
    comments_in(text, covered..text.len(), &mut marks);
    marks
}

/// The comments in the stretch of `text` that no token covers: from a `--`
/// to the end of its line.
fn comments_in(
    text: &str,
    gap: std::ops::Range<usize>,
    marks: &mut Vec<(std::ops::Range<usize>, Lexical)>,
) {
    let mut at = gap.start;
    while let Some(i) = text[at..gap.end].find("--") {
        let start = at + i;
        let end = text[start..].find('\n').map_or(text.len(), |n| start + n);
        marks.push((start..end, Lexical::Comment));
        at = end;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_count_utf16_columns() {
        let lines = Lines::new("ab\n\u{1F600}x\n");
        assert_eq!(lines.position(1), (0, 1));
        assert_eq!(lines.position(3), (1, 0));
        assert_eq!(lines.position(3 + 4), (1, 2));
    }

    #[test]
    fn lexical_marks_classify_tokens_and_comments() {
        let text = "if x then Some 1 else \"a\" ++ y -- done";
        let classes: Vec<(&str, Lexical)> = lexical_marks(text)
            .into_iter()
            .map(|(r, c)| (&text[r], c))
            .collect();
        assert_eq!(
            classes,
            [
                ("if", Lexical::Keyword),
                ("then", Lexical::Keyword),
                ("Some", Lexical::Name),
                ("1", Lexical::Number),
                ("else", Lexical::Keyword),
                ("\"a\"", Lexical::Text),
                ("++", Lexical::Operator),
                ("-- done", Lexical::Comment),
            ]
        );
    }
}
