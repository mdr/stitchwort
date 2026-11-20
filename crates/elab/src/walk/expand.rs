//! What a walk wrote, for `check --expand-walk`: the pieces of its chain, the
//! trace of the lemmas used, and their rendering as text.

use super::*;

/// A piece of a walk's expansion.
#[derive(Clone, Debug)]
pub enum Piece {
    Text(String),
    /// The user's own text, as written there.
    Source(Span),
    /// What a place the walk went on from wrote.
    Child(u32),
}

/// One check of a written walk, for `check --expand-walk`: where it is, the
/// chain it stands for and the lemma used at each call.
#[derive(Clone, Debug)]
pub struct WalkExpansion {
    pub span: Span,
    pub pieces: Vec<Piece>,
    pub trace: Vec<Vec<Piece>>,
}

impl Walks {
    /// The paths the splits reached from `node`'s text add, and `extra`'s.
    pub(super) fn splits(&self, node: u32, extra: u32) -> usize {
        let mut seen = vec![node];
        let mut todo = vec![node];
        let mut total = 0;
        while let Some(n) = todo.pop() {
            let Some(info) = self.nodes.get(n as usize) else {
                continue;
            };
            total += info.split;
            for piece in info.text.iter().flatten() {
                if let Piece::Child(k) = piece
                    && !seen.contains(k)
                {
                    seen.push(*k);
                    todo.push(*k);
                }
            }
        }
        if !seen.contains(&extra) {
            total += self.nodes[extra as usize].split;
        }
        total
    }

    /// The expansion of call `c`, with its children's pieces in place.
    pub(super) fn expansion(&self, c: usize) -> Option<WalkExpansion> {
        let call = &self.calls[c];
        let mut out = Vec::new();
        let mut trace = Vec::new();
        self.flatten(call.root, &mut out, &mut trace)?;
        Some(WalkExpansion {
            span: call.span,
            pieces: out,
            trace,
        })
    }

    /// The pieces and trace of the places the final chain goes through:
    /// a place tried and given up (a call first tried unweakened) isn't
    /// reached from the root's text.
    pub(super) fn flatten(
        &self,
        node: u32,
        out: &mut Vec<Piece>,
        trace: &mut Vec<Vec<Piece>>,
    ) -> Option<()> {
        let info = self.nodes.get(node as usize)?;
        trace.extend(info.trace.iter().cloned());
        let Some(text) = info.text.as_ref() else {
            // Where the walk stopped: left open.
            out.push(Piece::Text("?".into()));
            return Some(());
        };
        let mut skip_close = false;
        for (i, piece) in text.iter().enumerate() {
            match piece {
                Piece::Child(k) => {
                    let mut child = Vec::new();
                    self.flatten(*k, &mut child, trace)?;
                    // `f (x)` is written `f x`.
                    let opened = matches!(out.last(), Some(Piece::Text(t)) if t.ends_with('('));
                    let closed =
                        matches!(text.get(i + 1), Some(Piece::Text(t)) if t.starts_with(')'));
                    if opened && closed && atomic(&child) {
                        if let Some(Piece::Text(t)) = out.last_mut() {
                            t.pop();
                        }
                        skip_close = true;
                    }
                    out.extend(child);
                }
                Piece::Text(t) if skip_close => {
                    skip_close = false;
                    out.push(Piece::Text(t[1..].to_string()));
                }
                other => out.push(other.clone()),
            }
        }
        Some(())
    }
}

/// The characters of `s` outside string literals, with their byte offsets,
/// the quotes themselves left out: a bracket in a string (`"("`) isn't one.
fn outside_strings(s: &str) -> impl Iterator<Item = (usize, char)> + '_ {
    let mut quoted = false;
    let mut escaped = false;
    s.char_indices().filter(move |&(_, c)| {
        if escaped {
            escaped = false;
            false
        } else if quoted && c == '\\' {
            escaped = true;
            false
        } else if c == '"' {
            quoted = !quoted;
            false
        } else {
            !quoted
        }
    })
}

/// Whether `text` is one string literal, `"…"`: its first quote closes at
/// the end.
fn is_string_literal(text: &str) -> bool {
    let mut chars = text.char_indices();
    if chars.next().map(|(_, c)| c) != Some('"') {
        return false;
    }
    let mut escaped = false;
    for (i, c) in chars {
        match c {
            _ if escaped => escaped = false,
            '\\' => escaped = true,
            '"' => return i + 1 == text.len(),
            _ => {}
        }
    }
    false
}

/// Whether written pieces are one word, or one bracketed whole, needing no
/// brackets as an argument.
pub(super) fn atomic(pieces: &[Piece]) -> bool {
    let mut text = String::new();
    for p in pieces {
        match p {
            Piece::Text(t) => text.push_str(t),
            _ => return false,
        }
    }
    if text.is_empty() {
        return false;
    }
    if is_string_literal(&text) {
        return true;
    }
    if !text.contains([' ', '\n']) {
        return true;
    }
    let (Some(open), Some(close)) = (text.chars().next(), text.chars().last()) else {
        return false;
    };
    if !matches!((open, close), ('(', ')') | ('[', ']')) {
        return false;
    }
    // The first bracket closes at the end, not before.
    let mut depth = 0usize;
    for (i, c) in outside_strings(&text) {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => {
                depth -= 1;
                if depth == 0 {
                    return i + c.len_utf8() == text.len();
                }
            }
            _ => {}
        }
    }
    false
}

impl Elaborator {
    /// What each walk checked so far wrote: for a walk checked more than
    /// once, the last (`check --expand-walk`).
    pub fn take_walk_expansions(&self) -> Vec<WalkExpansion> {
        let walks = self.session.walks.borrow();
        let mut out: Vec<WalkExpansion> = Vec::new();
        for c in 0..walks.calls.len() {
            if let Some(e) = walks.expansion(c) {
                match out.iter_mut().find(|o| o.span == e.span) {
                    Some(o) => *o = e,
                    None => out.push(e),
                }
            }
        }
        out
    }
}

/// A line of a walk's trace ([`WalkExpansion::trace`]) as text, from the
/// text of the file it is in.
pub fn trace_line(text: &str, line: &[Piece]) -> String {
    line.iter()
        .map(|p| match p {
            Piece::Text(t) => t.as_str(),
            Piece::Source(span) => text.get(span.range()).unwrap_or("?"),
            Piece::Child(_) => "…",
        })
        .collect()
}

/// A file's text with each walk replaced by the chain it stands for, from
/// the expansions recorded for it (those of other files ignored), indented
/// where the walk was. How many were expanded.
pub fn expand_file(
    text: &str,
    file: stitchwort_syntax::FileId,
    expansions: &[WalkExpansion],
) -> (String, usize) {
    let mut mine: Vec<&WalkExpansion> = expansions.iter().filter(|e| e.span.file == file).collect();
    mine.sort_by_key(|e| e.span.range().start);
    let mut out = String::new();
    let mut at = 0;
    let mut done = 0;
    for e in mine {
        let range = e.span.range();
        if range.start < at {
            continue;
        }
        let line_start = text[..range.start].rfind('\n').map_or(0, |i| i + 1);
        let indent: String = text[line_start..range.start]
            .chars()
            .take_while(|c| c.is_whitespace())
            .collect();
        out.push_str(&text[at..range.start]);
        out.push_str(&render(text, &e.pieces, &indent));
        // Over the closing brackets the walk's span leaves out, as quoted.
        at = range.start + quoted(text, e.span).len();
        done += 1;
    }
    out.push_str(&text[at..]);
    (out, done)
}

/// Starts a line that continues the one before (an argument of a call on
/// the line above), in [`render`].
pub(super) const MORE: char = '\u{1}';

/// The source at `span`, with the closing brackets after it that its own
/// opening ones need: an application's span ends at its last argument's,
/// inside that argument's brackets (`f x (() => y)` is quoted without its
/// last `)`).
fn quoted(text: &str, span: Span) -> String {
    let Some(mut out) = text.get(span.range()).map(str::to_string) else {
        return "?".into();
    };
    let count = |s: &str, c: char| outside_strings(s).filter(|&(_, x)| x == c).count();
    let mut rest = text.get(span.range().end..).unwrap_or("").chars();
    while count(&out, '(') > count(&out, ')') && rest.next() == Some(')') {
        out.push(')');
    }
    out
}

/// The pieces as text, each line after the first indented by `indent` and
/// by the depth of the brackets open before it.
pub(super) fn render(text: &str, pieces: &[Piece], indent: &str) -> String {
    let mut raw = String::new();
    for p in pieces {
        match p {
            Piece::Text(t) => raw.push_str(t),
            Piece::Source(span) => raw.push_str(&quoted(text, *span)),
            Piece::Child(_) => {}
        }
    }
    let mut out = String::new();
    let mut depth: usize = 0;
    for (i, line) in raw.split('\n').enumerate() {
        let mut line = line;
        if i > 0 {
            out.push('\n');
            out.push_str(indent);
            for _ in 0..depth {
                out.push_str("  ");
            }
            // A line that goes on the one before: one level further in.
            if let Some(rest) = line.strip_prefix(MORE) {
                out.push_str("  ");
                line = rest;
            }
        }
        out.push_str(line);
        for (_, c) in outside_strings(line) {
            match c {
                '(' | '[' => depth += 1,
                ')' | ']' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(s: &str) -> Vec<Piece> {
        vec![Piece::Text(s.to_string())]
    }

    #[test]
    fn quoted_ignores_brackets_in_strings() {
        // The span ends inside the last argument's brackets; the `)` in the
        // string isn't the one it needs.
        let source = r#"f (g ")" x) y"#;
        let start = source.find("f (g").expect("start");
        let end = source.find(" x").expect("end") + 2;
        let span = Span::new(Span::NOWHERE.file, start as u32, end as u32);
        assert_eq!(quoted(source, span), r#"f (g ")" x)"#);
    }

    #[test]
    fn strings_are_atomic() {
        assert!(atomic(&text(r#""no (such) thing""#)));
        assert!(atomic(&text(r#""say \"hi\" ]""#)));
        assert!(!atomic(&text(r#""a" "b""#)));
        assert!(!atomic(&text(r#""unclosed \""#)));
        // Brackets in a string don't close a bracketed whole.
        assert!(atomic(&text(r#"(f ")" x)"#)));
        assert!(!atomic(&text(r#"(f ")") x"#)));
    }
}
