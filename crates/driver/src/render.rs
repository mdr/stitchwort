//! Renders [`Diagnostic`]s with source excerpts.

use crate::palette::{self, Role};
use ariadne::{Config, IndexType, Label, Report, ReportKind};
use stitchwort_syntax::{Diagnostic, Severity, SourceMap};

/// When to colour the report on the command line (`--color`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum ColorChoice {
    /// Colour when the report goes to a terminal and `NO_COLOR` isn't set.
    #[default]
    Auto,
    Always,
    Never,
}

impl ColorChoice {
    /// Whether to colour. `no_color` is the value of the `NO_COLOR`
    /// environment variable: any non-empty value turns `Auto` off, an empty
    /// one is ignored (<https://no-color.org>). An explicit
    /// `--color=always` or `never` wins over it.
    pub fn enabled(self, is_terminal: bool, no_color: Option<&str>) -> bool {
        match self {
            ColorChoice::Always => true,
            ColorChoice::Never => false,
            ColorChoice::Auto => is_terminal && no_color.is_none_or(str::is_empty),
        }
    }
}

/// `text` in the terminal style `code` (an SGR parameter list, `1;32`).
fn styled(code: &str, text: &str) -> String {
    format!("\u{1b}[{code}m{text}\u{1b}[0m")
}

/// Colours the part where the rows of a type mismatch's note differ
/// (`expected: …\n   found: …`, as the checker writes them): from the first
/// to the last character that isn't shared, widened to whole tokens (up to a space or bracket). The
/// text is unchanged, so the colourless form says the same.
fn highlight_rows(note: &str) -> String {
    let Some((expected, found)) = note
        .strip_prefix("expected: ")
        .and_then(|rest| rest.split_once("\n   found: "))
    else {
        return note.to_string();
    };
    let e: Vec<char> = expected.chars().collect();
    let f: Vec<char> = found.chars().collect();
    let word = |c: char| !c.is_whitespace() && !"()[]{},".contains(c);
    let mut start = e.iter().zip(&f).take_while(|(a, b)| a == b).count();
    let mut shared = e[start..]
        .iter()
        .rev()
        .zip(f[start..].iter().rev())
        .take_while(|(a, b)| a == b)
        .count();
    // Widen to whole tokens on both sides.
    while start > 0 && word(e[start - 1]) && e.get(start).is_some_and(|&c| word(c)) {
        start -= 1;
    }
    while shared > 0 && word(e[e.len() - shared]) && word(e[e.len() - shared - 1]) {
        shared -= 1;
    }
    let paint = |chars: &[char], code: &str| {
        let end = chars.len() - shared;
        let part: String = chars[start.min(end)..end].iter().collect();
        if part.is_empty() || part == "…" {
            return chars.iter().collect::<String>();
        }
        format!(
            "{}{}{}",
            chars[..start].iter().collect::<String>(),
            styled(code, &part),
            chars[end..].iter().collect::<String>()
        )
    };
    format!(
        "expected: {}\n   found: {}",
        paint(&e, &palette::current().sgr(Role::Fix, "1;4")),
        paint(&f, &palette::current().sgr(Role::Error, "1;4"))
    )
}

/// `diagnostic` with each generic note ([`Diagnostic::with_generic_note`])
/// that `seen` already holds replaced by a short pointer back to its first
/// printing; the others are added to `seen`. For the command line's text
/// output, once per run: the index and the editor keep every note.
pub fn with_repeated_generic_notes_cut(
    diagnostic: &Diagnostic,
    seen: &mut stitchwort_core::collections::HashSet<String>,
) -> Diagnostic {
    let mut d = diagnostic.clone();
    for note in &mut d.notes {
        if !diagnostic.is_generic_note(note) || seen.insert(note.clone()) {
            continue;
        }
        let words = note.split_whitespace().count();
        let tag: Vec<&str> = note.split_whitespace().take(4).collect();
        let more = if tag.len() < words { "…" } else { "" };
        *note = format!("(see the note above: \"{}{more}\")", tag.join(" "));
    }
    d
}

/// Renders `diagnostic` as text. Pass `color: false` for snapshots and pipes.
pub fn render(sources: &SourceMap, diagnostic: &Diagnostic, color: bool) -> String {
    let palette = palette::current();
    let kind = match diagnostic.severity {
        Severity::Error if color => ReportKind::Custom("Error", palette.ariadne(Role::Error)),
        Severity::Warning if color => ReportKind::Custom("Warning", palette.ariadne(Role::Warning)),
        Severity::Error => ReportKind::Error,
        Severity::Warning => ReportKind::Warning,
        Severity::Goal => ReportKind::Custom("Goal", palette.ariadne(Role::Goal)),
    };

    let Some(primary) = diagnostic.primary_span() else {
        let mut out = format!("[{}] {kind}: {}\n", diagnostic.code, diagnostic.message);
        for note in &diagnostic.notes {
            out.push_str(&format!("  note: {note}\n"));
        }
        return out;
    };

    // Characters, not bytes: ariadne's byte mode passes a character offset on as a
    // byte offset for the labels of a file other than the report's own.
    let config = Config::default()
        .with_color(color)
        .with_index_type(IndexType::Char);

    let mut report = Report::build(kind, place(sources, primary))
        .with_config(config)
        .with_code(diagnostic.code)
        .with_message(&diagnostic.message);
    // ariadne starts a new excerpt whenever a label comes before the previous one
    // in the file, so pass labels in source order, with the primary label's file
    // first (ariadne reports the error's position in the first file).
    let mut labels: Vec<_> = diagnostic.labels.iter().collect();
    labels.sort_by_key(|label| {
        (
            label.span.file != primary.file,
            sources.get(label.span.file).name.as_str(),
            label.span.start,
        )
    });
    for label in labels {
        let mut shown = Label::new(place(sources, label.span)).with_message(&label.message);
        if color {
            // The primary label in the report's own colour, the others in
            // a calm one; the `─┬─` and `╰──` marks carry the same
            // information without it.
            shown = shown.with_color(if std::ptr::eq(label, &diagnostic.labels[0]) {
                palette.ariadne(match diagnostic.severity {
                    Severity::Error => Role::Error,
                    Severity::Warning => Role::Warning,
                    Severity::Goal => Role::Goal,
                })
            } else {
                palette.ariadne(Role::Secondary)
            });
        }
        report = report.with_label(shown);
    }
    for note in &diagnostic.notes {
        report = report.with_note(if color {
            highlight_rows(note)
        } else {
            note.clone()
        });
    }

    let cache = ariadne::sources(
        sources
            .iter()
            .map(|(_, file)| (shown_name(&file.name, &file.text), file.text.clone()))
            .chain({
                let mut start = 0;
                let std = stitchwort_elab::std_text();
                std.core_layout.iter().map(move |(path, len)| {
                    let text = std.prelude[start..start + len].to_owned();
                    start += len;
                    (std.shown_path(path), text)
                })
            }),
    );
    let mut out = Vec::new();
    report
        .finish()
        .write(cache, &mut out)
        .expect("writing to a Vec cannot fail");
    let mut out = String::from_utf8(out).expect("ariadne writes UTF-8");
    if diagnostic.code == "GOAL" {
        // ariadne colours a report kind of its own whatever the setting.
        if !color {
            out = without_colour(&out);
        }
        for label in &diagnostic.labels {
            out = indent_continuations(&out, &label.message);
        }
    }
    // After the excerpt: ariadne's report is a box with room for notes
    // only. One line for each fix that can be applied as it stands.
    for fix in crate::fixes::fixes_of(sources, diagnostic) {
        if fix.applicability == crate::fixes::Applicability::Certain {
            let line = fix.try_line();
            match line.strip_prefix("try:").filter(|_| color) {
                Some(rest) => out.push_str(&format!(
                    "{}{rest}",
                    styled(&palette.sgr(Role::Fix, "1"), "try:")
                )),
                None => out.push_str(&line),
            }
            out.push('\n');
        }
    }
    out
}

/// `diagnostic` for a one-line input (the REPL's), without ariadne's box:
/// carets under the part of the line it points at, then the message. The
/// line itself isn't repeated: it is on the screen just above, after the
/// prompt, which `margin` columns wide the carets are indented by. `None` if
/// the diagnostic isn't about that one line alone (it has labels in other
/// files or on other lines, or is a goal), so [`render`] shows it in full.
pub fn render_compact(
    sources: &SourceMap,
    diagnostic: &Diagnostic,
    color: bool,
    margin: usize,
) -> Option<String> {
    let primary = diagnostic.primary_span()?;
    let text = sources.get(primary.file).text.as_str();
    let line = text.trim_end();
    let single_line = |span: stitchwort_syntax::Span| {
        span.file == primary.file
            && (span.end as usize) <= text.len()
            && !text[span.start as usize..span.end as usize].contains('\n')
    };
    if diagnostic.code == "GOAL"
        || line.contains('\n')
        || !diagnostic
            .labels
            .iter()
            .all(|label| single_line(label.span))
    {
        return None;
    }
    // Column of a byte offset, counting characters: the line is shown as typed.
    let column = |offset: u32| text[..(offset as usize).min(text.len())].chars().count();
    let start = column(primary.start);
    let width = column(primary.end).saturating_sub(start).max(1);
    let palette = palette::current();
    let (kind, role) = match diagnostic.severity {
        Severity::Error => ("error", Role::Error),
        Severity::Warning => ("warning", Role::Warning),
        Severity::Goal => ("goal", Role::Goal),
    };
    let colour = palette.sgr(role, "1");
    let paint = |code: &str, text: &str| {
        if color {
            styled(code, text)
        } else {
            text.to_string()
        }
    };
    let carets = "^".repeat(width);
    let labels = diagnostic
        .labels
        .iter()
        .filter(|label| !label.message.is_empty())
        .collect::<Vec<_>>();
    // The first label, which is the primary one, goes beside the carets; the
    // message is the line below.
    let beside = labels
        .first()
        .filter(|label| label.span == primary)
        .map_or("", |label| label.message.as_str());
    let mut out = format!(
        "{}{}\n",
        " ".repeat(margin + start),
        paint(&colour, format!("{carets} {beside}").trim_end())
    );
    out.push_str(&paint(
        &colour,
        &format!("{kind}[{}]: {}", diagnostic.code, diagnostic.message),
    ));
    out.push('\n');
    for label in labels.iter().skip(usize::from(!beside.is_empty())) {
        out.push_str(&format!(
            "  at column {}: {}\n",
            column(label.span.start) + 1,
            label.message
        ));
    }
    for note in &diagnostic.notes {
        let note = if color {
            highlight_rows(note)
        } else {
            note.clone()
        };
        out.push_str(&format!("{}note: {note}\n", " ".repeat(margin)));
    }
    for fix in crate::fixes::fixes_of(sources, diagnostic) {
        if fix.applicability == crate::fixes::Applicability::Certain {
            out.push_str(&format!("{}{}\n", " ".repeat(margin), fix.try_line()));
        }
    }
    Some(out)
}

/// The longest a line of a goal (a hypothesis, or the target) is shown in
/// full on the command line: a longer one keeps its first and last
/// [`GOAL_LINE_LIMIT`]` / 2` characters, and says how many it leaves out
/// (`--full-goals` shows them all; the index always has them). A goal is
/// a few lines; one line of thousands of characters is a term the reader
/// will search, not read, and six of them were 30 KB of output
/// (docs/research/agentic-proving.md §5 B).
pub const GOAL_LINE_LIMIT: usize = 400;

/// `diagnostic`, if it's a goal, with each line of its label longer than
/// `limit` characters cut in the middle ([`GOAL_LINE_LIMIT`]).
pub fn with_long_goal_lines_cut(diagnostic: &Diagnostic, limit: usize) -> Diagnostic {
    let mut d = diagnostic.clone();
    if d.code != "GOAL" {
        return d;
    }
    for label in &mut d.labels {
        let lines: Vec<String> = label
            .message
            .lines()
            .map(|line| cut_middle(line, limit))
            .collect();
        label.message = lines.join("\n");
    }
    d
}

/// `line` if it has no more than `limit` characters; else its first and
/// last `limit / 2`, and how many are left out between.
fn cut_middle(line: &str, limit: usize) -> String {
    let count = line.chars().count();
    if count <= limit {
        return line.to_string();
    }
    let keep = limit / 2;
    let head: String = line.chars().take(keep).collect();
    let tail: String = line.chars().skip(count - keep).collect();
    format!(
        "{} …[{} characters left out; --full-goals shows them]… {}",
        head.trim_end(),
        count - 2 * keep,
        tail.trim_start()
    )
}

/// `text` without its terminal colour codes.
fn without_colour(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' {
            // `ESC [ … m`
            for c in chars.by_ref() {
                if c == 'm' {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

/// ariadne writes the lines of a label after its first at the start of the
/// line: indents them under the first, inside the excerpt's margin. A goal's
/// label is its context and goal, a line each
/// (docs/proposals/lsp-goal-holes.md §3.2).
fn indent_continuations(out: &str, message: &str) -> String {
    let mut message_lines = message.lines();
    let (Some(first), rest) = (message_lines.next(), message_lines.collect::<Vec<_>>()) else {
        return out.to_string();
    };
    if rest.is_empty() {
        return out.to_string();
    }
    let lines: Vec<&str> = out.lines().collect();
    let Some(at) = lines
        .iter()
        .position(|l| without_colour(l).ends_with(&format!("── {first}")))
    else {
        return out.to_string();
    };
    let plain = without_colour(lines[at]);
    let prefix = &plain[..plain.len() - first.len()];
    // The margin, up to and including its `│`, then spaces to the text.
    let Some(bar) = prefix.find('│') else {
        return out.to_string();
    };
    let margin = &prefix[..bar + '│'.len_utf8()];
    let pad = " ".repeat(prefix[margin.len()..].chars().count());
    let mut result: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
    for (i, line) in rest.iter().enumerate() {
        if result.get(at + 1 + i).map(String::as_str) == Some(*line) {
            result[at + 1 + i] = format!("{margin}{pad}{line}");
        }
    }
    let mut joined = result.join("\n");
    if out.ends_with('\n') {
        joined.push('\n');
    }
    joined
}

/// [`place_bytes`] with the range in characters of the file's text, as ariadne is
/// configured to take it.
fn place(sources: &SourceMap, span: stitchwort_syntax::Span) -> (String, std::ops::Range<usize>) {
    let (name, bytes) = place_bytes(sources, span);
    let file = sources.get(span.file);
    let std = stitchwort_elab::std_text();
    let core = file.name == "<prelude>"
        && file.text.starts_with(std.prelude)
        && (span.end as usize) <= std.prelude.len();
    let text = if core {
        &std.prelude[span.start as usize - bytes.start..]
    } else {
        file.text.as_str()
    };
    let chars = |offset: usize| text.char_indices().take_while(|(i, _)| *i < offset).count();
    (name, chars(bytes.start)..chars(bytes.end))
}

/// Where `span` is shown: the file's name and range in bytes, but for a span in the
/// core, the name of the file of the core it is in, and the range within it.
fn place_bytes(
    sources: &SourceMap,
    span: stitchwort_syntax::Span,
) -> (String, std::ops::Range<usize>) {
    let file = sources.get(span.file);
    let std = stitchwort_elab::std_text();
    // The core is a prefix of the prelude file: tests append to it.
    if file.name == "<prelude>"
        && file.text.starts_with(std.prelude)
        && (span.end as usize) <= std.prelude.len()
    {
        let (path, start, _) = stitchwort_elab::core_file_at(span.start as usize);
        return (
            std.shown_path(path),
            (span.start as usize - start)..(span.end as usize - start),
        );
    }
    (shown_name(&file.name, &file.text), span.range())
}

/// Where `span` starts, as shown: the file's name and the line (from 1),
/// but for a span in the core, the core's file it is in and the line in it.
pub fn location(sources: &SourceMap, span: stitchwort_syntax::Span) -> (String, usize) {
    let (name, range) = place_bytes(sources, span);
    let file = sources.get(span.file);
    let line = |offset: usize| {
        file.text[..offset.min(file.text.len())]
            .matches('\n')
            .count()
    };
    // `place` moved the range into the core's file: count from its start.
    let base = (span.start as usize).saturating_sub(range.start);
    (name, line(span.start as usize) - line(base) + 1)
}

/// The name a source file is shown by: a library file's (`std/List/Sort.sw`
/// in the session) is its path on disk when the library is read from a
/// directory (`STITCHWORT_STD_DIR`), so an editor can jump to it.
fn shown_name(name: &str, text: &str) -> String {
    let std = stitchwort_elab::std_text();
    if std.dir.is_some()
        && let Some(path) = name.strip_prefix("std/")
        && std.library.iter().any(|(p, t)| *p == path && *t == text)
    {
        return std.shown_path(path);
    }
    name.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_syntax::Span;

    #[test]
    fn repeated_generic_notes_point_back_and_the_original_keeps_them() {
        let explain = "a call is in tail position when its result is the function's result";
        let make = || {
            Diagnostic::error("E-TAIL", "not a tail call")
                .with_generic_note(explain)
                .with_note("`f` isn't in tail position")
        };
        let mut seen = stitchwort_core::collections::HashSet::default();
        let first = with_repeated_generic_notes_cut(&make(), &mut seen);
        assert_eq!(first.notes, make().notes);
        let original = make();
        let second = with_repeated_generic_notes_cut(&original, &mut seen);
        assert_eq!(
            second.notes,
            [
                "(see the note above: \"a call is in…\")".to_string(),
                "`f` isn't in tail position".to_string()
            ]
        );
        // What the index and the editor read is the diagnostic itself.
        assert_eq!(original.notes[0], explain);
    }

    #[test]
    fn renders_labels_and_notes() {
        let mut sources = SourceMap::new();
        let file = sources.add("example.sw", "def innocent (n : Nat) : Nat := spin n + 1\n");
        let diagnostic = Diagnostic::error("E-ABILITY", "`innocent` uses the Partial ability")
            .with_label(Span::new(file, 32, 36), "`spin` might not terminate")
            .with_label(
                Span::new(file, 25, 28),
                "but this type doesn't allow Partial",
            )
            .with_note("write `Nat -> {Partial} Nat` to allow it");

        insta::assert_snapshot!(render(&sources, &diagnostic, false));
    }

    /// ariadne mixes byte and char offsets for a file other than the report's
    /// own: a non-ASCII character before a label in the second file panicked.
    #[test]
    fn labels_after_non_ascii_text_in_a_second_file_render() {
        let mut sources = SourceMap::new();
        let first = sources.add("a.sw", "x\n");
        let second = sources.add("b.sw", "→→→→\nlength : Nat\n");
        let diagnostic = Diagnostic::error("E-DUPLICATE", "`length` is already defined")
            .with_label(Span::new(first, 0, 1), "here")
            .with_label(Span::new(second, 13, 19), "and here");
        let out = render(&sources, &diagnostic, false);
        assert!(out.contains("b.sw:2:1"), "{out}");
        assert!(out.contains("length : Nat"), "{out}");
    }

    #[test]
    fn reports_the_position_in_the_primary_file() {
        let mut sources = SourceMap::new();
        let first = sources.add("a.sw", "length : Nat\n");
        let second = sources.add("b.sw", "x\nlength : Nat\n");
        let diagnostic = Diagnostic::error("E-DUPLICATE", "`length` is already defined")
            .with_label(Span::new(second, 2, 8), "defined again here")
            .with_label(Span::new(first, 0, 6), "first defined here");
        insta::assert_snapshot!(render(&sources, &diagnostic, false));
    }

    fn mismatch() -> (SourceMap, Diagnostic) {
        let mut sources = SourceMap::new();
        let file = sources.add("example.sw", "def innocent (n : Nat) : Nat := spin n + 1\n");
        let diagnostic = Diagnostic::error("E-TYPE-MISMATCH", "mismatch")
            .with_label(Span::new(file, 32, 36), "primary")
            .with_label(Span::new(file, 25, 28), "secondary")
            .with_note("expected: f (n <= height) …\n   found: f (n < height) …");
        (sources, diagnostic)
    }

    #[test]
    fn colour_marks_labels_and_the_first_difference() {
        let (sources, diagnostic) = mismatch();
        let out = render(&sources, &diagnostic, true);
        // Escape codes are on the labels (Mocha red primary, lavender secondary).
        assert!(out.contains("\u{1b}[38;2;243;139;168m"), "{out:?}");
        assert!(out.contains("\u{1b}[38;2;180;190;254m"), "{out:?}");
        // The differing words are bold and underlined, one in each row.
        assert!(
            out.contains("\u{1b}[1;4;38;2;166;227;161m<=\u{1b}[0m"),
            "{out:?}"
        );
        assert!(
            out.contains("\u{1b}[1;4;38;2;243;139;168m<\u{1b}[0m"),
            "{out:?}"
        );
        // Colour only adds codes: without them it is the plain form.
        assert_eq!(without_colour(&out), render(&sources, &diagnostic, false));
    }

    #[test]
    fn warnings_are_mochas_yellow() {
        let mut sources = SourceMap::new();
        let file = sources.add("example.sw", "def x := 1\n");
        let diagnostic =
            Diagnostic::warning("W-X", "careful").with_label(Span::new(file, 4, 5), "here");
        assert!(render(&sources, &diagnostic, true).contains("\u{1b}[38;2;249;226;175m"));
    }

    #[test]
    fn plain_form_has_no_escapes() {
        let (sources, diagnostic) = mismatch();
        assert!(!render(&sources, &diagnostic, false).contains('\u{1b}'));
    }

    #[test]
    fn colour_choice_follows_flag_and_no_color() {
        use ColorChoice::*;
        assert!(Auto.enabled(true, None));
        assert!(!Auto.enabled(false, None));
        // Any non-empty NO_COLOR turns it off; an empty one is ignored.
        assert!(!Auto.enabled(true, Some("1")));
        assert!(Auto.enabled(true, Some("")));
        assert!(Always.enabled(false, Some("1")));
        assert!(!Never.enabled(true, None));
    }

    #[test]
    fn renders_diagnostics_without_a_location() {
        let sources = SourceMap::new();
        let diagnostic =
            Diagnostic::error("E-NO-INPUT", "no input files").with_note("pass a .sw file");

        insta::assert_snapshot!(render(&sources, &diagnostic, false));
    }
}
