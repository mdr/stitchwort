//! The REPL path: elaborating, evaluating and printing standalone expressions.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::parse_expression;

/// Evaluates `source` and prints `value : type`, or returns the error code.
fn eval(session: &mut Session, source: &str) -> Result<String, &'static str> {
    let file = session.sources.add("<test>", source);
    let expr = parse_expression(file, source).map_err(|d| d.code)?;
    let (term, ty) = session.elab.infer_expr(&expr).map_err(|d| d.code)?;
    let value = session.elab.eval(&term).unwrap();
    Ok(format!(
        "{} : {}",
        session.elab.show(&value),
        session.elab.show(&ty)
    ))
}

#[test]
fn evaluates_and_prints_expressions() {
    let mut session = Session::new();
    let cases = [
        ("2 + 3", "5 : Nat"),
        ("List.length [1, 2, 3]", "3 : Nat"),
        ("List.append [1] [2, 3]", "[1, 2, 3] : List Nat"),
        ("[[1], []]", "[[1], []] : List (List Nat)"),
        ("Succ", "\\n => Succ n : Nat -> Nat"),
        ("7 / 2", "3 : Nat"),
        ("Nat.div 7 2", "3 : Nat"),
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
    let file = session.sources.add("<test>", "List.append");
    let expr = parse_expression(file, "List.append").unwrap();
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
    assert_eq!(eval(&mut session, "List.length 3"), Err("E-TYPE-MISMATCH"));
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
