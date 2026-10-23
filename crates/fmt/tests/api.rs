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
fn every_line_and_gap_has_a_rule() {
    // F2: continuation lines are at +2 (D1040) and `g(x)` is `g (x)`
    // (D1039), so nothing is left on the copy path.
    let text = "def f (x: Nat): Nat :=\n    let y := x\n    g(y)\n         (h x)\n           x\n";
    let result = format_with_stats(text).unwrap();
    assert_eq!(
        result.text,
        "def f (x: Nat): Nat :=\n  let y := x\n  g (y)\n    (h x)\n      x\n"
    );
    assert_eq!(result.stats, Stats::default());
}

#[test]
fn a_space_before_a_parenthesis_does_not_change_the_tree() {
    // D1039: `f(x)` and `f (x)` parse alike wherever the formatter adds the
    // space; `f()` against `f ()` is the one pair that differs, so it stays.
    use stitchwort_syntax::equivalence::parse_shape;
    for (tight, spaced) in [
        ("def a: Nat := f(x)", "def a: Nat := f (x)"),
        (
            "def a: Nat := f(x, y) + g(1)",
            "def a: Nat := f (x, y) + g (1)",
        ),
        ("def a: Nat := g f(x)", "def a: Nat := g f (x)"),
        ("def a: Nat := f(x).y", "def a: Nat := f (x).y"),
        ("def a: Nat := p.get(1) z", "def a: Nat := p.get (1) z"),
        ("def a: Nat := Some(x)", "def a: Nat := Some (x)"),
        ("def a: Nat := f(g(x))", "def a: Nat := f (g (x))"),
        (
            "def a: Nat -> Nat\n  | Some(x) => x\n  | None => 0",
            "def a: Nat -> Nat\n  | Some (x) => x\n  | None => 0",
        ),
    ] {
        assert_eq!(parse_shape(tight), parse_shape(spaced), "{tight}");
        assert_eq!(format(tight).unwrap(), format!("{spaced}\n"));
    }
    assert_ne!(
        parse_shape("def a: Nat := g f()"),
        parse_shape("def a: Nat := g f ()")
    );
    assert_eq!(
        format("def a: Nat := g f()").unwrap(),
        "def a: Nat := g f()\n"
    );
}
