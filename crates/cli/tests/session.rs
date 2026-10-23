//! The REPL path: elaborating, evaluating and printing standalone expressions.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::parse_expression;

/// Evaluates `source` and prints `value : type`, or returns the error code.
fn eval(session: &mut Session, source: &str) -> Result<String, &'static str> {
    let expr = session
        .parse_expression("<test>", source)
        .map_err(|d| d.code)?;
    let (term, ty) = session.elab.infer_expr(&expr).map_err(|d| d.code)?;
    let value = session.elab.eval(&term).unwrap();
    Ok(format!(
        "{} : {}",
        session.elab.show(&value),
        session.elab.show(&ty)
    ))
}

/// A `match` typed in is lifted to a helper, as in a definition; each
/// input's helpers are separate.
#[test]
fn a_nested_match_is_lifted() {
    let mut session = Session::new();
    let source = "(match 2 with | 0 => 1 | Succ m => m) + 1";
    assert_eq!(eval(&mut session, source).as_deref(), Ok("2 : Nat"));
    assert_eq!(eval(&mut session, source).as_deref(), Ok("2 : Nat"));
    assert_eq!(
        eval(&mut session, "(match 0 with | 0 => 7 | Succ m => m) + 1").as_deref(),
        Ok("8 : Nat")
    );
}

#[test]
fn evaluates_and_prints_expressions() {
    let mut session = Session::new();
    let cases = [
        ("2 + 3", "5 : Nat"),
        ("[1, 2, 3].length", "3 : Nat"),
        ("Std.List.append [1] [2, 3]", "[1, 2, 3] : List Nat"),
        ("[[1], []]", "[[1], []] : List (List Nat)"),
        ("Succ", "n => Succ n : Nat -> Nat"),
        ("7 / 2", "3 : Nat"),
        ("Std.Nat.div 7 2", "3 : Nat"),
    ];
    for (source, expected) in cases {
        assert_eq!(
            eval(&mut session, source).as_deref(),
            Ok(expected),
            "{source}"
        );
    }
}

#[test]
fn shows_polymorphic_types_with_their_implicit_parameters() {
    let mut session = Session::new();
    let file = session.sources.add("<test>", "Std.List.append");
    let expr = parse_expression(file, "Std.List.append").unwrap();
    let (_, ty) = session.elab.infer_expr(&expr).unwrap();
    assert_eq!(
        session.elab.show(&ty),
        "[a: Type] -> List a -> List a -> List a"
    );
}

#[test]
fn reports_errors_in_expressions() {
    let mut session = Session::new();
    assert_eq!(eval(&mut session, "Nil"), Err("E-UNSOLVED"));
    assert_eq!(
        eval(&mut session, "Std.List.length 3"),
        Err("E-TYPE-MISMATCH")
    );
    assert_eq!(eval(&mut session, "nope"), Err("E-UNKNOWN-NAME"));
    assert_eq!(eval(&mut session, "(1"), Err("E-PARSE"));
}

#[test]
fn files_build_on_the_prelude_and_earlier_files() {
    let mut session = Session::new();
    session
        .load("a.sw", "def double (n : Nat) : Nat := n + n\n")
        .expect("first file checks");
    assert_eq!(eval(&mut session, "double 4").as_deref(), Ok("8 : Nat"));
    let errors = session
        .load("b.sw", "def double : Nat := 1\n")
        .expect_err("redefinition");
    assert_eq!(errors[0].code, "E-DUPLICATE");
}

#[test]
fn imports_typed_in_accumulate() {
    let mut session = Session::new();
    // Without an import, `List.` isn't a prefix yet.
    assert_eq!(
        eval(&mut session, "List.map (n => n + 1) [1, 2]"),
        Err("E-UNKNOWN-NAME")
    );
    assert!(
        session
            .add_imports("<input>", "import Std (List)")
            .is_empty()
    );
    assert_eq!(
        eval(&mut session, "List.map (n => n + 1) [1, 2]").as_deref(),
        Ok("[2, 3] : List Nat")
    );
    // A second import keeps the first.
    assert!(
        session
            .add_imports("<input>", "import Std.Nat (add)")
            .is_empty()
    );
    assert_eq!(eval(&mut session, "add 1 2").as_deref(), Ok("3 : Nat"));
    assert_eq!(
        eval(&mut session, "List.length [1]").as_deref(),
        Ok("1 : Nat")
    );
    // Importing twice is the usual warning; unknown names and namespaces
    // are the usual errors.
    let again = session.add_imports("<input>", "import Std (List)");
    assert_eq!(again[0].code, "W-IMPORT-TWICE");
    let unknown = session.add_imports("<input>", "import Std (Nope)");
    assert_eq!(unknown[0].code, "E-IMPORT-UNKNOWN");
    let namespace = session.add_imports("<input>", "import Nope (x)");
    assert_eq!(namespace[0].code, "E-IMPORT-UNKNOWN");
    // Declarations aren't imports.
    let decl = session.add_imports("<input>", "def x : Nat := 1");
    assert_eq!(decl[0].code, "E-PARSE");
}
