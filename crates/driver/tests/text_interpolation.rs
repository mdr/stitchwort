//! Errors in a text with interpolations point at the whole literal.

use stitchwort_driver::driver::Session;

/// The source text each error label of loading `source` points at.
fn labelled(source: &str) -> Vec<String> {
    let mut session = Session::new();
    let errors = session.load("test.sw", source).unwrap_err();
    errors
        .iter()
        .flat_map(|d| &d.labels)
        .map(|label| source[label.span.start as usize..label.span.end as usize].to_string())
        .collect()
}

#[test]
fn a_mismatch_points_at_the_whole_literal() {
    for literal in [
        "\"${n}\"",
        "\"${n} and ${n}\"",
        "\"n is ${n}\"",
        "\"${n} is n\"",
    ] {
        let source = format!("def f (n: Nat): Nat := {literal}\n");
        assert_eq!(labelled(&source), [literal], "{source}");
    }
}
