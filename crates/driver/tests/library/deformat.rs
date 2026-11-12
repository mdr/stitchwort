//! A small, deterministic de-formatter for the formatter's hash oracle
//! (`fmt_hashes.rs`): it writes a file's text badly on purpose, so that
//! formatting has something to change even though the repository is kept
//! formatted.
//!
//! Every transformation is applied only if the result still parses to the
//! same syntax tree as the original (`equivalence::shape`), so the program
//! is unchanged by construction; one that fails on a file is dropped for
//! that file and reported. Choices are drawn from a generator seeded by the
//! file's path and the transformation's name, so a run is repeatable and
//! dropping one transformation doesn't change the others.
//!
//! Layout transformations, which the formatter should undo (completely for
//! the first three; the indentation ones are only partly undone, because it
//! copies the indentation of some lines):
//! - extra spaces between tokens, and spaces removed or added just inside
//!   brackets and around commas;
//! - one or two more blank lines wherever there is one (the formatter makes
//!   a run one, and adds none);
//! - the lines of a declaration after its first indented by 1 to 3 more
//!   spaces, and lines inside brackets by 1 to 4 more, each its own amount;
//! - trailing spaces on lines (outside `"""` texts).
//!
//! Line-break transformations, which the formatter keeps (it keeps the
//! author's line breaks), so only the hashes are comparable:
//! - a break after two thirds of the commas inside brackets;
//! - a break before two thirds of the `|>`s.
//!
//! Text inside string literals is never touched, and no line break goes
//! inside a `${…}`, which must stay on one line.

use std::ops::Range;

use stitchwort_syntax::{
    DEFAULT_STACK, SourceMap, Tok, Token, decl_ranges, equivalence, lex_with_trivia,
    parse_module_within,
};

/// A de-formatted file.
pub struct Deformed {
    /// Spacing, blank lines and trailing spaces only: nothing the formatter
    /// can't put back exactly.
    pub flat: String,
    /// All the layout transformations, indentation too. The formatter copies
    /// the indentation of some lines (SW-3026 findings), so this doesn't
    /// always format back to the original.
    pub layout: String,
    /// The layout transformations after the line-break ones.
    pub broken: String,
    /// The names of the transformations that kept the program (line-break
    /// ones first).
    pub applied: Vec<&'static str>,
    /// The names of those dropped because they changed the syntax tree or
    /// stopped it parsing.
    pub dropped: Vec<&'static str>,
}

type Edit = (usize, usize, String);

struct Transform {
    name: &'static str,
    run: fn(&Source, &mut Rng) -> Vec<Edit>,
}

const BREAKS: [Transform; 2] = [
    Transform {
        name: "break after comma",
        run: break_after_commas,
    },
    Transform {
        name: "break before pipe",
        run: break_before_pipes,
    },
];

const FLAT: [Transform; 3] = [
    Transform {
        name: "spacing",
        run: spacing,
    },
    Transform {
        name: "blank lines",
        run: blank_lines,
    },
    Transform {
        name: "trailing spaces",
        run: trailing_spaces,
    },
];

const LAYOUT: [Transform; 5] = [
    Transform {
        name: "spacing",
        run: spacing,
    },
    Transform {
        name: "blank lines",
        run: blank_lines,
    },
    Transform {
        name: "declaration indent",
        run: declaration_indent,
    },
    Transform {
        name: "bracket indent",
        run: bracket_indent,
    },
    Transform {
        name: "trailing spaces",
        run: trailing_spaces,
    },
];

/// De-formats `text`, the file at `path`; `None` if it doesn't parse.
pub fn deformat(path: &str, text: &str) -> Option<Deformed> {
    let want = shape(text)?;
    let mut applied = Vec::new();
    let mut dropped = Vec::new();
    let mut run = |from: &str, transforms: &[Transform]| {
        let mut note = |names: Vec<&'static str>, lost: Vec<&'static str>| {
            for name in names {
                if !applied.contains(&name) {
                    applied.push(name);
                }
            }
            for name in lost {
                if !dropped.contains(&name) {
                    dropped.push(name);
                }
            }
        };
        // All the steps, checked once at the end; only if that fails, one by
        // one (parsing is most of the cost).
        let mut current = from.to_string();
        let mut changed = Vec::new();
        for t in transforms {
            if let Some(next) = step(path, &current, t) {
                if next != current {
                    changed.push(t.name);
                }
                current = next;
            }
        }
        if shape(&current).as_ref() == Some(&want) {
            note(changed, Vec::new());
            return current;
        }
        let (mut current, mut changed, mut lost) = (from.to_string(), Vec::new(), Vec::new());
        for t in transforms {
            match step(path, &current, t) {
                Some(next) if shape(&next).as_ref() == Some(&want) => {
                    if next != current {
                        changed.push(t.name);
                    }
                    current = next;
                }
                _ => lost.push(t.name),
            }
        }
        note(changed, lost);
        current
    };
    let flat = run(text, &FLAT);
    let layout = run(text, &LAYOUT);
    let with_breaks = run(text, &BREAKS);
    let broken = run(&with_breaks, &LAYOUT);
    Some(Deformed {
        flat,
        layout,
        broken,
        applied,
        dropped,
    })
}

/// `text` with one transformation applied.
fn step(path: &str, text: &str, t: &Transform) -> Option<String> {
    let source = Source::new(text)?;
    let edits = (t.run)(&source, &mut Rng::new(path, t.name));
    Some(apply(text, edits))
}

fn shape(text: &str) -> Option<String> {
    let file = SourceMap::new().add("input.sw", text);
    parse_module_within(file, text, DEFAULT_STACK)
        .ok()
        .map(|module| equivalence::shape(&module))
}

/// SplitMix64, seeded from a path and a name.
struct Rng(u64);

impl Rng {
    fn new(path: &str, name: &str) -> Rng {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for b in path.bytes().chain([0]).chain(name.bytes()) {
            h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
        Rng(h)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number in `0..n`.
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// A number in `from..=to`.
    fn between(&mut self, from: usize, to: usize) -> usize {
        from + self.below(to - from + 1)
    }

    fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

fn apply(text: &str, mut edits: Vec<Edit>) -> String {
    edits.sort_by_key(|e| (e.0, e.1));
    let mut out = String::with_capacity(text.len() + edits.len() * 2);
    let mut at = 0;
    for (start, end, insert) in edits {
        assert!(start >= at, "overlapping edits");
        out.push_str(&text[at..start]);
        out.push_str(&insert);
        at = end;
    }
    out.push_str(&text[at..]);
    out
}

/// A file's tokens and what the transformations need to know about them.
struct Source<'a> {
    text: &'a str,
    tokens: Vec<Token>,
    decls: Vec<Range<usize>>,
    /// Byte ranges of string literal pieces: text inside them is data.
    strings: Vec<(usize, usize)>,
    /// `depth[i]`: open brackets after token `i`.
    depth: Vec<usize>,
    /// `in_interpolation[i]`: whether token `i` is followed, up to the end
    /// of the string, by more of a `${…}`, so a line break after it would
    /// break a `${…}` across lines.
    in_interpolation: Vec<bool>,
}

fn is_string_piece(tok: &Tok) -> bool {
    matches!(
        tok,
        Tok::Str(_) | Tok::StrStart(_) | Tok::StrMid(_) | Tok::StrEnd(_)
    )
}

impl<'a> Source<'a> {
    fn new(text: &'a str) -> Option<Source<'a>> {
        let file = SourceMap::new().add("input.sw", text);
        let lexed = lex_with_trivia(file, text).ok()?;
        let tokens = lexed.tokens;
        let decls = decl_ranges(&tokens).ok()?;
        let mut strings = Vec::new();
        let mut depth = Vec::with_capacity(tokens.len());
        let mut in_interpolation = Vec::with_capacity(tokens.len());
        let (mut open, mut interpolations) = (0usize, 0usize);
        for t in &tokens {
            match t.tok {
                Tok::LParen | Tok::LBracket | Tok::LBrace => open += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => open = open.saturating_sub(1),
                Tok::StrStart(_) => interpolations += 1,
                Tok::StrEnd(_) => interpolations = interpolations.saturating_sub(1),
                _ => {}
            }
            if is_string_piece(&t.tok) {
                strings.push((t.span.start as usize, t.span.end as usize));
            }
            depth.push(open);
            in_interpolation.push(interpolations > 0);
        }
        Some(Source {
            text,
            tokens,
            decls,
            strings,
            depth,
            in_interpolation,
        })
    }

    fn start(&self, i: usize) -> usize {
        self.tokens[i].span.start as usize
    }

    fn end(&self, i: usize) -> usize {
        self.tokens[i].span.end as usize
    }

    /// Whether `at` is strictly inside a string literal's text.
    fn in_string(&self, at: usize) -> bool {
        let i = self.strings.partition_point(|&(start, _)| start < at);
        i > 0 && at < self.strings[i - 1].1
    }

    /// The lines that start outside strings: (start offset, text without
    /// the line break, whether a line break ends it).
    fn lines(&self) -> Vec<(usize, &'a str, bool)> {
        let mut out = Vec::new();
        let mut at = 0;
        for line in self.text.split_inclusive('\n') {
            let body = line.strip_suffix('\n').unwrap_or(line);
            if !self.in_string(at) {
                out.push((at, body, line.ends_with('\n')));
            }
            at += line.len();
        }
        out
    }

    /// The declaration whose first line is before `at` and last token ends
    /// after it, if any (so a line there isn't the declaration's first).
    fn inside_declaration(&self, at: usize) -> Option<usize> {
        let i = self
            .decls
            .partition_point(|d| self.start(d.start) < at)
            .checked_sub(1)?;
        let d = &self.decls[i];
        (!d.is_empty() && at < self.end(d.end - 1)).then_some(i)
    }

    /// Open brackets before byte `at`.
    fn depth_at(&self, at: usize) -> usize {
        match self
            .tokens
            .partition_point(|t| (t.span.start as usize) < at)
        {
            0 => 0,
            n => self.depth[n - 1],
        }
    }

    /// Whether the gap after token `i` is just spaces and the tokens either
    /// side aren't joined by an interpolation's `${` or `}`.
    fn plain_gap(&self, i: usize) -> Option<Range<usize>> {
        let (left, right) = (&self.tokens[i].tok, &self.tokens.get(i + 1)?.tok);
        if matches!(left, Tok::StrStart(_) | Tok::StrMid(_))
            || matches!(right, Tok::StrMid(_) | Tok::StrEnd(_))
        {
            return None;
        }
        let gap = self.end(i)..self.start(i + 1);
        (gap.start <= gap.end && self.text[gap.clone()].bytes().all(|b| b == b' ')).then_some(gap)
    }
}

const DECLARATION_KEYWORDS: [&str; 7] = [
    "def ",
    "type ",
    "theorem ",
    "export ",
    "test ",
    "interface ",
    "instance ",
];

fn spaces(n: usize) -> String {
    " ".repeat(n)
}

/// Extra spaces between tokens; spaces removed or added just inside
/// brackets and around commas.
fn spacing(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    let mut edits = Vec::new();
    for i in 0..src.tokens.len().saturating_sub(1) {
        let Some(gap) = src.plain_gap(i) else {
            continue;
        };
        // The formatter copies the spacing of a line that ends a `"""` text
        // as it is (SW-3026 finding).
        let line = src.text[..gap.start].rfind('\n').map_or(0, |n| n + 1);
        if src.in_string(line) {
            continue;
        }
        let (left, right) = (&src.tokens[i].tok, &src.tokens[i + 1].tok);
        // A dot's neighbours: `f .x` and `f.x` differ, and `@[` is one unit.
        if matches!(left, Tok::Dot | Tok::At) || matches!(right, Tok::Dot) {
            continue;
        }
        let empty_pair = matches!(
            (left, right),
            (Tok::LParen, Tok::RParen)
                | (Tok::LBracket, Tok::RBracket)
                | (Tok::LBrace, Tok::RBrace)
                | (Tok::RParen, Tok::LParen)
        );
        if empty_pair {
            continue;
        }
        let inner = matches!(left, Tok::Comma | Tok::LParen | Tok::LBracket)
            || matches!(right, Tok::RParen | Tok::RBracket | Tok::Comma);
        let spaced = !gap.is_empty();
        let replacement = match (spaced, inner, rng.coin()) {
            (_, _, false) => continue,
            (true, true, true) => String::new(),
            (true, false, true) => spaces(rng.between(2, 3)),
            (false, true, true) => " ".to_string(),
            (false, false, true) => continue,
        };
        edits.push((gap.start, gap.end, replacement));
    }
    edits
}

/// One or two more blank lines wherever there is already one: the
/// formatter turns a run into one, but never adds any (D1020).
fn blank_lines(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    if src.text.contains('\r') {
        return Vec::new();
    }
    src.lines()
        .into_iter()
        .filter(|&(at, body, newline)| {
            newline && body.trim().is_empty() && !src.in_string(at + body.len())
        })
        .filter_map(|(at, _, _)| {
            let more = rng.below(3);
            (more > 0).then(|| (at, at, "\n".repeat(more)))
        })
        .collect()
}

/// The lines after each declaration's first, indented further by the same
/// 1 to 3 spaces: their layout relative to each other is kept.
fn declaration_indent(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    let by: Vec<usize> = src.decls.iter().map(|_| rng.between(1, 3)).collect();
    src.lines()
        .into_iter()
        .filter(|(_, body, _)| !body.trim().is_empty())
        .filter_map(|(at, body, _)| {
            // The formatter leaves a declaration keyword on the line after an
            // attribute where it is (SW-3026 finding), so it isn't moved.
            if DECLARATION_KEYWORDS
                .iter()
                .any(|k| body.trim_start().starts_with(k))
            {
                return None;
            }
            let d = src.inside_declaration(at)?;
            Some((at, at, spaces(by[d])))
        })
        .collect()
}

/// Lines that start inside brackets, each indented further by 1 to 4 spaces
/// of its own: inside brackets, layout ends nothing.
fn bracket_indent(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    src.lines()
        .into_iter()
        .filter(|(_, body, _)| !body.trim().is_empty())
        .filter(|&(at, _, _)| src.inside_declaration(at).is_some() && src.depth_at(at) > 0)
        .map(|(at, _, _)| (at, at, spaces(rng.between(1, 4))))
        .collect()
}

/// 1 to 3 spaces at the end of lines, blank ones too.
fn trailing_spaces(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    if src.text.contains('\r') {
        return Vec::new();
    }
    src.lines()
        .into_iter()
        .filter(|&(at, body, newline)| newline && !src.in_string(at + body.len()))
        .filter_map(|(at, body, _)| {
            if rng.below(3) == 0 {
                return None;
            }
            let end = at + body.len();
            Some((end, end, spaces(rng.between(1, 3))))
        })
        .collect()
}

/// The indentation of the line holding byte `at`.
fn line_indent(text: &str, at: usize) -> usize {
    let line = text[..at].rfind('\n').map_or(0, |i| i + 1);
    text[line..].bytes().take_while(|&b| b == b' ').count()
}

/// A line break in the gap after token `i` (when it is on the line of the
/// next token and outside any `${…}`), the next line indented 2 more than
/// the line it was on.
fn break_gap(src: &Source, i: usize) -> Option<Edit> {
    let right = src.tokens.get(i + 1)?;
    if right.line_start || src.in_interpolation[i] {
        return None;
    }
    let gap = src.plain_gap(i)?;
    let indent = line_indent(src.text, src.start(i));
    Some((gap.start, gap.end, format!("\n{}", spaces(indent + 2))))
}

fn break_after_commas(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    (0..src.tokens.len())
        .filter(|&i| src.tokens[i].tok == Tok::Comma && src.depth[i] > 0)
        .filter(|_| rng.below(3) != 0)
        .filter_map(|i| break_gap(src, i))
        .collect()
}

fn break_before_pipes(src: &Source, rng: &mut Rng) -> Vec<Edit> {
    (1..src.tokens.len())
        .filter(|&i| src.tokens[i].tok == Tok::PipeGt)
        .filter(|_| rng.below(3) != 0)
        .filter_map(|i| break_gap(src, i - 1))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = "\
def f (xs: List Nat) : Nat := xs |> .length |> .add 1 |> .add 2 |> .add 3

def g (n: Nat) : List Nat :=
  [n, n + 1, n + 2, n + 3, n + 4, n + 5]
    |> .map (x => x * 2)
    |> .filter (x => x > 2)

--- A text.
def t : String :=
  \"\"\"
    a  b
      c   \"\"\"

def u (x: Nat) : String := \"n=${x + 1}, ${x}\"
";

    #[test]
    fn deformatting_keeps_the_syntax_tree_and_changes_the_text() {
        let d = deformat("sample.sw", SAMPLE).expect("the sample parses");
        assert_eq!(shape(&d.flat), shape(SAMPLE));
        assert_eq!(shape(&d.layout), shape(SAMPLE));
        assert_eq!(shape(&d.broken), shape(SAMPLE));
        assert_ne!(d.layout, SAMPLE);
        assert_ne!(d.broken, d.layout);
        assert!(d.dropped.is_empty(), "dropped {:?}", d.dropped);
        assert_eq!(
            d.applied.len(),
            LAYOUT.len() + BREAKS.len(),
            "{:?}",
            d.applied
        );
    }

    #[test]
    fn it_is_repeatable_and_depends_on_the_path() {
        let a = deformat("a.sw", SAMPLE).unwrap();
        assert_eq!(a.layout, deformat("a.sw", SAMPLE).unwrap().layout);
        assert_ne!(a.layout, deformat("b.sw", SAMPLE).unwrap().layout);
    }

    #[test]
    fn text_literals_are_untouched() {
        let d = deformat("sample.sw", SAMPLE).unwrap();
        for text in [&d.layout, &d.broken] {
            assert!(text.contains("    a  b\n      c   \"\"\""), "{text}");
            assert!(text.contains("\"n=${") && text.contains("}, ${"), "{text}");
        }
    }

    #[test]
    fn a_file_that_does_not_parse_is_refused() {
        assert!(deformat("bad.sw", "def f :=\n  (").is_none());
    }
}
