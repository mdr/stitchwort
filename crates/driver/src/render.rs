//! Renders [`Diagnostic`]s with source excerpts.

use ariadne::{Config, IndexType, Label, Report, ReportKind};
use stitchwort_syntax::{Diagnostic, Severity, SourceMap};

/// Renders `diagnostic` as text. Pass `color: false` for snapshots and pipes.
pub fn render(sources: &SourceMap, diagnostic: &Diagnostic, color: bool) -> String {
    let kind = match diagnostic.severity {
        Severity::Error => ReportKind::Error,
        Severity::Warning => ReportKind::Warning,
    };

    let Some(primary) = diagnostic.primary_span() else {
        let mut out = format!("[{}] {kind}: {}\n", diagnostic.code, diagnostic.message);
        for note in &diagnostic.notes {
            out.push_str(&format!("  note: {note}\n"));
        }
        return out;
    };

    let name = |span: stitchwort_syntax::Span| sources.get(span.file).name.clone();
    let config = Config::default()
        .with_color(color)
        .with_index_type(IndexType::Byte);

    let mut report = Report::build(kind, (name(primary), primary.range()))
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
        report = report.with_label(
            Label::new((name(label.span), label.span.range())).with_message(&label.message),
        );
    }
    for note in &diagnostic.notes {
        report = report.with_note(note);
    }

    let cache = ariadne::sources(
        sources
            .iter()
            .map(|(_, file)| (file.name.clone(), file.text.clone())),
    );
    let mut out = Vec::new();
    report
        .finish()
        .write(cache, &mut out)
        .expect("writing to a Vec cannot fail");
    String::from_utf8(out).expect("ariadne writes UTF-8")
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
