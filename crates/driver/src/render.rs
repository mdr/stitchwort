//! Renders [`Diagnostic`]s with source excerpts.

use ariadne::{Config, IndexType, Label, Report, ReportKind};
use stitchwort_syntax::{Diagnostic, Severity, SourceMap};

/// Renders `diagnostic` as text. Pass `color: false` for snapshots and pipes.
pub fn render(sources: &SourceMap, diagnostic: &Diagnostic, color: bool) -> String {
    let kind = match diagnostic.severity {
        Severity::Error => ReportKind::Error,
        Severity::Warning => ReportKind::Warning,
        Severity::Goal => ReportKind::Custom("Goal", ariadne::Color::Cyan),
    };

    let Some(primary) = diagnostic.primary_span() else {
        let mut out = format!("[{}] {kind}: {}\n", diagnostic.code, diagnostic.message);
        for note in &diagnostic.notes {
            out.push_str(&format!("  note: {note}\n"));
        }
        return out;
    };

    let config = Config::default()
        .with_color(color)
        .with_index_type(IndexType::Byte);

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
        report =
            report.with_label(Label::new(place(sources, label.span)).with_message(&label.message));
    }
    for note in &diagnostic.notes {
        report = report.with_note(note);
    }

    let cache = ariadne::sources(
        sources
            .iter()
            .map(|(_, file)| (file.name.clone(), file.text.clone()))
            .chain({
                let mut start = 0;
                stitchwort_elab::CORE_LAYOUT.iter().map(move |(path, len)| {
                    let text = stitchwort_elab::PRELUDE[start..start + len].to_owned();
                    start += len;
                    (format!("std/{path}"), text)
                })
            }),
    );
    let mut out = Vec::new();
    report
        .finish()
        .write(cache, &mut out)
        .expect("writing to a Vec cannot fail");
    let mut out = String::from_utf8(out).expect("ariadne writes UTF-8");
    if diagnostic.severity == Severity::Goal {
        // ariadne colours a report kind of its own whatever the setting.
        if !color {
            out = without_colour(&out);
        }
        for label in &diagnostic.labels {
            out = indent_continuations(&out, &label.message);
        }
    }
    out
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

/// Where `span` is shown: the file's name and range, but for a span in the
/// core, the name of the file of the core it is in, and the range within it.
fn place(sources: &SourceMap, span: stitchwort_syntax::Span) -> (String, std::ops::Range<usize>) {
    let file = sources.get(span.file);
    // The core is a prefix of the prelude file: tests append to it.
    if file.name == "<prelude>"
        && file.text.starts_with(stitchwort_elab::PRELUDE)
        && (span.end as usize) <= stitchwort_elab::PRELUDE.len()
    {
        let (path, start, _) = stitchwort_elab::core_file_at(span.start as usize);
        return (
            format!("std/{path}"),
            (span.start as usize - start)..(span.end as usize - start),
        );
    }
    (file.name.clone(), span.range())
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_syntax::Span;

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

    #[test]
    fn renders_diagnostics_without_a_location() {
        let sources = SourceMap::new();
        let diagnostic =
            Diagnostic::error("E-NO-INPUT", "no input files").with_note("pass a .sw file");

        insta::assert_snapshot!(render(&sources, &diagnostic, false));
    }
}
