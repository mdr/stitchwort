//! The formatter's interface: refusing files that don't lex or parse
//! (D1021), and the counts of what the rules didn't cover.

use stitchwort_fmt::{Error, Stats, format, format_with_stats};

fn refused(text: &str) -> Vec<String> {
    match format(text) {
        Err(Error::Refused(diagnostics)) => diagnostics.into_iter().map(|d| d.message).collect(),
        other => panic!("expected a refusal, got {other:?}"),
    }
}

#[test]
fn a_file_that_does_not_lex_is_refused() {
    let messages = refused("def x: Nat :=\n\t1\n");
    assert!(messages[0].contains("tabs"), "{messages:?}");
}

#[test]
fn a_file_with_any_syntax_error_is_refused_whole() {
    // The first declaration parses, but the file is still refused.
    let messages = refused("def a: Nat :=   1\n\ndef b: Nat := )\n");
    assert_eq!(messages.len(), 1, "{messages:?}");
    refused("  def indented: Nat := 1\n");
}

#[test]
fn empty_and_comment_only_files() {
    assert_eq!(format("").unwrap(), "");
    assert_eq!(format("\n\n").unwrap(), "");
    assert_eq!(
        format("\n-- only   a comment  \n\n\n").unwrap(),
        "-- only   a comment\n"
    );
}

#[test]
fn errors_say_what_happened() {
    let refusal = format("def x := )").unwrap_err().to_string();
    assert!(refusal.starts_with("not formatted: "), "{refusal}");
    let internal = Error::Internal("the token `a` became `b`".into()).to_string();
    assert_eq!(
        internal,
        "formatter bug: output differs, file left unchanged: the token `a` became `b`"
    );
}

#[test]
fn lines_and_gaps_no_rule_covers_are_counted() {
    let covered = "def f (x: Nat): Nat :=\n    let y := x\n    y\n";
    assert_eq!(format_with_stats(covered).unwrap().stats, Stats::default());

    // `(h x)` and `x` continue the line above: their indentation is copied.
    // So is the missing space in `g(x)`.
    let copied = "def f (x: Nat): Nat :=\n  g(x)\n     (h x)\n       x\n";
    let result = format_with_stats(copied).unwrap();
    assert_eq!(result.text, copied);
    assert_eq!(
        result.stats,
        Stats {
            copied_lines: 2,
            copied_gaps: 1,
            verbatim_decls: 0,
        }
    );
}
