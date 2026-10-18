//! Unit tests of the snippet and HTML entry points.

use stitchwort_convert::{convert_html, convert_snippet};

#[test]
fn module_snippet() {
    let converted = convert_snippet("double : Nat -> Nat\ndouble n = n + n\n").expect("converts");
    assert_eq!(converted.text, "def double (n : Nat) : Nat := n + n\n");
    assert_eq!(converted.report.assign_form, 1);
    assert_eq!(converted.report.arm_form, 0);
}

#[test]
fn module_snippet_with_arms() {
    let converted =
        convert_snippet("len : List Nat -> Nat\nlen Nil = 0\nlen (Cons x xs) = 1 + len xs\n")
            .expect("converts");
    assert_eq!(
        converted.text,
        "def len : List Nat -> Nat\n  | Nil => 0\n  | Cons x xs => 1 + len xs\n"
    );
    assert_eq!(converted.report.arm_form, 1);
}

#[test]
fn expression_snippet() {
    let converted = convert_snippet(
        "match xs with\n  | Nil -> 0\n  | Cons x _ -> List.map (\\y z -> y + z) x\n",
    )
    .expect("converts as an expression");
    assert_eq!(
        converted.text,
        "match xs with\n  | Nil => 0\n  | Cons x _ => List.map (\\y z => y + z) x\n"
    );
    assert_eq!(converted.report.declarations(), 0);
}

#[test]
fn unconvertible_snippet_is_an_error() {
    // Neither a module nor an expression: a dangling operator.
    let err = convert_snippet("f n = n +\n").expect_err("cannot convert");
    assert!(err.contains("expected an expression"), "{err}");
}

#[test]
fn html_blocks() {
    let page = "<html>\n<body>\n\
<script type=\"text/plain\" id=\"one\">\n\
inc : Nat -> Nat\n\
inc n = n + 1\n\
</script>\n\
<p>between</p>\n\
<script type=\"text/plain\" id=\"two\">\n\
broken n = n\n\
</script>\n\
</body>\n</html>\n";
    let (out, blocks) = convert_html(page);
    assert_eq!(blocks.len(), 2);
    assert_eq!(blocks[0].id, "one");
    assert_eq!(blocks[0].first_line, 3);
    assert!(blocks[0].elaborated);
    assert!(blocks[0].outcome.is_ok());
    assert_eq!(blocks[1].id, "two");
    assert_eq!(blocks[1].first_line, 8);
    assert!(blocks[1].outcome.is_err());
    // The first block is rewritten, the second left as it was.
    assert!(
        out.contains("def inc (n : Nat) : Nat := n + 1\n</script>"),
        "{out}"
    );
    assert!(out.contains("<p>between</p>"));
    assert!(out.contains("id=\"two\">\nbroken n = n\n</script>"));
    assert!(out.starts_with("<html>\n<body>\n"));
    assert!(out.ends_with("</body>\n</html>\n"));
}
