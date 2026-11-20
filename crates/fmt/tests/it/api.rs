//! The formatter's interface: refusing files that don't lex or parse
//! (D1021), and failing a file whose output isn't the same program.

use stitchwort_fmt::{Error, format};

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
fn a_leading_colon_eq_is_refused() {
    // The parser drops tokens before the first declaration when they start
    // with `:=`, so the formatter, which can't print what nothing reads,
    // refuses the file.
    let messages = refused("-- c\n:=\n  if a\n  then b\n");
    assert!(messages[0].contains("`:=`"), "{messages:?}");
    refused(":=\n  List.sum 1\nimport Std (List)\n\ndef stored: Nat := 1\n");
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
fn a_call_chain_formats_on_one_line() {
    // `g(x)` is `g (x)` (D1039), and a call that fits is on one line.
    let text = "def f (x: Nat): Nat :=\n    let y := x\n    g(y)\n         (h x)\n           x\n";
    assert_eq!(
        format(text).unwrap(),
        "def f (x: Nat): Nat :=\n  let y := x\n  g (y) (h x) x\n"
    );
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

#[test]
fn glued_call_elements_get_a_space() {
    // SW-4459: the self-hosted formatter prints a space between adjacent
    // call elements; Rust copied the source's gap.
    use stitchwort_syntax::equivalence::parse_shape;
    for (glued, spaced) in [
        ("def a: Nat := f[x]", "def a: Nat := f [x]"),
        ("def a: Nat := f (x)[y]", "def a: Nat := f (x) [y]"),
        ("def a: Nat := f [x]y", "def a: Nat := f [x] y"),
        ("def a: Nat := f 2a", "def a: Nat := f 2 a"),
        ("def a: Nat := f [x][y]", "def a: Nat := f [x] [y]"),
        ("def a: Nat := byWalking[x]", "def a: Nat := byWalking [x]"),
    ] {
        assert_eq!(parse_shape(glued), parse_shape(spaced), "{glued}");
        assert_eq!(format(glued).unwrap(), format!("{spaced}\n"));
    }
}

#[test]
fn a_theorem_with_explicit_parameters_gets_forall() {
    // D3472: written before the first parameter, after the name when the
    // parameters start on the next line, and not at all where only implicit
    // parameters are (or a `def`, or none).
    let text = "theorem a (n: Nat): n = n := byComputing\n\n\
                theorem b [x: Bool] (n: Nat): n = n := byComputing\n\n\
                theorem c\n  (n: Nat): n = n := byComputing\n\n\
                theorem d [x: Bool]: x = x := byComputing\n\n\
                theorem e: True := trivial\n\n\
                theorem f ∀ (n: Nat): n = n := byComputing\n\n\
                def g (n: Nat): Nat := n\n";
    let want = "theorem a ∀ (n: Nat): n = n := byComputing\n\n\
                theorem b ∀ [x: Bool] (n: Nat): n = n := byComputing\n\n\
                theorem c ∀ (n: Nat): n = n := byComputing\n\n\
                theorem d [x: Bool]: x = x := byComputing\n\n\
                theorem e: True := trivial\n\n\
                theorem f ∀ (n: Nat): n = n := byComputing\n\n\
                def g (n: Nat): Nat := n\n";
    let once = format(text).unwrap();
    assert_eq!(once, want);
    assert_eq!(format(&once).unwrap(), want);
}

#[test]
fn a_trailing_comma_does_not_change_the_tree() {
    // SW-3229: `[(0 ..< n),]` once lowered differently from `[(0 ..< n)]`, so
    // the tree check refused the declaration and left it as written.
    use stitchwort_syntax::equivalence::parse_shape;
    for (comma, plain) in [
        ("[(0 ..< n),]", "[(0 ..< n)]"),
        ("[(0 ..= n),]", "[(0 ..= n)]"),
        ("[0 ..< n,]", "[0 ..< n]"),
        ("[(a, b),]", "[(a, b)]"),
        ("[(x),]", "[(x)]"),
        ("[(f x),]", "[(f x)]"),
        ("[a, (0 ..< n),]", "[a, (0 ..< n)]"),
        ("f (a, b,)", "f (a, b)"),
        ("{ x = 1, y = 2, }", "{ x = 1, y = 2 }"),
    ] {
        let comma = format!("def a: Nat := {comma}");
        let plain = format!("def a: Nat := {plain}");
        assert_eq!(parse_shape(&comma), parse_shape(&plain), "{comma}");
    }
    assert_eq!(
        format("def a: Nat := [(0 ..< n),]").unwrap(),
        "def a: Nat := [(0 ..< n)]\n"
    );
}

#[test]
fn shapes_the_rules_do_not_expect_are_syntax_errors() {
    // The rules treat these node shapes as internal errors (a bug if the
    // parser builds one); each is a syntax error the file is refused for.
    for text in [
        "def a: Nat := [1,,2]\n",
        "def a: Nat := { r | , }\n",
        "def a: Nat := rewrite a,, b then x\n",
        "def a: Nat := if c then a\n",
        "def a: Nat := if c then a else\n",
        "type T = | A | | B\n",
        "type T = | A\n  x\n",
        "@[a,,b]\ndef a: Nat := 1\n",
    ] {
        refused(text);
    }
}
