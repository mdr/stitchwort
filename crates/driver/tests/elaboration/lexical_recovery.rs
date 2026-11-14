//! A lexical error loses only the declaration that holds it: the rest of the
//! file still checks, so its errors are reported and its names resolve.

use stitchwort_driver::driver::Session;

/// The `(code, text the first label points at)` of each error in `source`.
fn errors(source: &str) -> Vec<(&'static str, String)> {
    let mut session = Session::new();
    let errors = session.load("test.sw", source).unwrap_err();
    errors
        .iter()
        .map(|d| {
            let span = d.primary_span().expect("a span");
            (
                d.code,
                source[span.start as usize..span.end as usize].to_string(),
            )
        })
        .collect()
}

#[test]
fn an_unclosed_string_leaves_the_other_declarations_checked() {
    let source = "\
def broken: Text := \"never closed
  more text
def twice (n: Nat): Nat := n + n
def unrelated: Nat := \"text\"
def usesBroken: Text := broken
";
    let found = errors(source);
    // The lexical error is as before, and the type error after the broken
    // declaration is found, with no `E-UNKNOWN-NAME` for `broken`.
    assert_eq!(found.len(), 2, "{found:?}");
    assert_eq!(found[0].0, "E-PARSE");
    assert!(found[0].1.starts_with("\"never closed"), "{found:?}");
    assert_eq!(found[1], ("E-TYPE-MISMATCH", "\"text\"".to_string()));
}

#[test]
fn a_stray_character_loses_only_its_own_declaration() {
    let source = "\
def first: Nat := 1 # 2
def second: Nat := \"text\"
def third: Nat := \t3
";
    let found = errors(source);
    let codes: Vec<_> = found.iter().map(|(code, _)| *code).collect();
    assert_eq!(
        codes,
        ["E-PARSE", "E-TYPE-MISMATCH", "E-PARSE"],
        "{found:?}"
    );
}
