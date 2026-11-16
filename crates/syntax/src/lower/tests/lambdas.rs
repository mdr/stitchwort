use super::*;

#[test]
fn lambda_parameters_may_be_annotated() {
    // (name, type, body) of a typed lambda.
    fn typed(e: &Expr) -> (String, String, Expr) {
        match e {
            Expr::TypedLam(name, Mode::Explicit, ty, body, _) => {
                (name.text.clone(), pshape(ty), body.as_ref().clone())
            }
            other => panic!("expected a typed lambda, got {other:?}"),
        }
    }
    let (name, ty, body) = typed(&rhs("def f : Nat := (x: Nat) => x\n"));
    assert_eq!((name.as_str(), ty.as_str()), ("x", "Nat"));
    assert!(matches!(body, Expr::Var(_)));
    // With a space before the colon, too.
    typed(&rhs("def f : Nat := (x : Nat) => x\n"));
    // Several parameters nest, in order; a group shares one type.
    let (name, _, body) = typed(&rhs("def f : Nat := (x y: Nat) => x\n"));
    assert_eq!(name, "x");
    let (name, ty, _) = typed(&body);
    assert_eq!((name.as_str(), ty.as_str()), ("y", "Nat"));
    let (_, _, body) = typed(&rhs("def f : Nat := (x: Nat) (y: Bool) => x\n"));
    assert!(matches!(body, Expr::TypedLam(..)));
    // Mixed with plain parameters: `x (y: Nat)` is a `Lam` around a
    // `TypedLam`.
    match &rhs("def f : Nat := x (y: Nat) => x\n") {
        Expr::Lam(names, body, _) => {
            assert_eq!(names.len(), 1);
            assert!(matches!(**body, Expr::TypedLam(..)));
        }
        other => panic!("expected a lambda, got {other:?}"),
    }
    let (_, _, body) = typed(&rhs("def f : Nat := (x: Nat) y z => x\n"));
    assert!(matches!(&body, Expr::Lam(names, _, _) if names.len() == 2));
    // A parenthesised name alone is still a plain parameter.
    assert!(matches!(rhs("def f : Nat := (x) => x\n"), Expr::Lam(..)));
    // A missing type or closing bracket is an error.
    assert!(rhs_of("def f : Nat := (x:) => x\n").is_err());
    assert!(rhs_of("def f : Nat := (x: Nat => x\n").is_err());
}

/// docs/proposals/lambda-syntax.md §5.1, layout rule: the run and its
/// `=>` follow the parser's existing continuation rule.
#[test]
fn a_lambdas_run_follows_the_layout_rule() {
    let lam_names = |e: &Expr| match e {
        Expr::Lam(names, _, _) => names.len(),
        other => panic!("expected a lambda, got {other:?}"),
    };
    // The body on the next line, indented.
    let e = rhs("def f : Nat :=\n  x y =>\n    x\n");
    assert_eq!(lam_names(&e), 2);
    // A second parameter on a continuation line.
    let e = rhs("def f : Nat :=\n  x\n    y =>\n      x\n");
    assert_eq!(lam_names(&e), 2);
    // `=>` at the block's column is a stop: `x y` is a statement.
    let text = "def f : Nat :=\n  x y\n  => x\n";
    assert!(error_text(text).contains("=>"), "{}", error_text(text));
    // A second line at the block's column starts a new statement.
    let e = rhs("def f : Nat :=\n  f x\n  y => y\n");
    assert_eq!(lines(&e), ["_", "result"]);
    let Expr::Seq(_, last) = &e else { panic!() };
    assert_eq!(lam_names(last), 1);
}

#[test]
fn lambda_positions() {
    let is_lam = |e: &Expr| matches!(e, Expr::Lam(..) | Expr::TypedLam(..));
    // `_` as a parameter, and a lambda returning a lambda.
    assert!(is_lam(&rhs("def f : Nat := _ => 0\n")));
    assert!(is_lam(&rhs("def f : Nat := x => y => x\n")));
    // Arguments need brackets, and with them the application is ordinary.
    assert!(matches!(
        rhs("def f : Nat := List.map (x => x) xs\n"),
        Expr::App(..)
    ));
    // Both branches of an `if`, and a record field.
    let e = rhs("def f : Nat := if c then x => a else y => b\n");
    let Expr::If {
        then, otherwise, ..
    } = &e
    else {
        panic!("expected an if")
    };
    assert!(is_lam(then) && is_lam(otherwise));
    assert!(matches!(
        rhs("def f : Nat := { f = x => x + 1 }\n"),
        Expr::Record { .. }
    ));
    // In an arm's result, and after `|>`.
    let e = rhs("def f : Nat := match n with | Zero => x => x | Succ k => g k\n");
    assert!(matches!(e, Expr::Match { .. }));
    assert!(matches!(
        rhs("def f : Nat := xs |> ys => ys\n"),
        Expr::Pipe(..)
    ));
    // `f x => e` is a lambda with parameters `f` and `x`.
    let e = rhs("def f : Nat := map x => x + 1\n");
    let Expr::Lam(names, _, _) = &e else {
        panic!("expected a lambda")
    };
    assert_eq!(names.len(), 2);
}

#[test]
fn what_is_not_a_lambda() {
    // A bare constructor or number isn't a parameter: use brackets.
    assert!(rhs_of("def f : Nat := Trivial => 1\n").is_err());
    assert!(rhs_of("def f : Nat := 0 => 1\n").is_err());
    assert!(matches!(
        rhs("def f : Nat := (Trivial) => 1\n"),
        Expr::Lam(..)
    ));
    // A qualified name or dot access can't be a parameter, so a forgotten
    // bracket is an error with a note.
    for text in [
        "def f : Nat := List.map x => x + 1\n",
        "def f : Nat := xs.map x => x + 1\n",
        "def f : Nat := Some x => x\n",
    ] {
        let message = error_text(text);
        assert!(message.contains("put it in brackets"), "{text}: {message}");
    }
    // After an operator the operand isn't a lambda position.
    assert!(rhs_of("def f : Nat := a + x => e\n").is_err());
    // An unclosed bracket isn't skipped over.
    assert!(rhs_of("def f : Nat := (a, b => e\n").is_err());
}

#[test]
fn a_lambda_takes_no_result_type() {
    for text in [
        "def f : Nat := (x: Nat): Nat => x\n",
        "def f : Nat := a (x: Nat): List (Nat) => x\n",
        "def f : Nat :=\n  let g := (x: Nat): Nat => x\n  g 1\n",
    ] {
        let message = error_text(text);
        assert!(
            message.contains("doesn't take a result type"),
            "{text}: {message}"
        );
    }
    // An annotated body is still a lambda.
    assert!(matches!(
        rhs("def f : Nat := (x: Nat) => (x: Nat)\n"),
        Expr::TypedLam(..)
    ));
}

#[test]
fn the_backslash_is_gone() {
    assert!(rhs_of("def f : Nat := \\x => x\n").is_err());
    let mut sources = SourceMap::new();
    let file = sources.add("t.sw", "\\");
    assert!(crate::lex(file, "\\").is_err());
}

/// docs/proposals/lambda-syntax.md §4.3 (D91): implicit and auto
/// parameters are written as in a header, and each gets its mode.
#[test]
fn lambdas_bind_implicit_and_auto_parameters() {
    // (name, mode, type, body) of a typed lambda.
    fn typed(e: &Expr) -> (String, Mode, String, Expr) {
        match e {
            Expr::TypedLam(name, mode, ty, body, _) => {
                (name.text.clone(), *mode, pshape(ty), body.as_ref().clone())
            }
            other => panic!("expected a typed lambda, got {other:?}"),
        }
    }
    let (name, mode, ty, body) = typed(&rhs("def f : Nat := [a: Kind] (x: a) => x\n"));
    assert_eq!(
        (name.as_str(), mode, ty.as_str()),
        ("a", Mode::Implicit, "Kind")
    );
    let (name, mode, _, body) = typed(&body);
    assert_eq!((name.as_str(), mode), ("x", Mode::Explicit));
    assert!(matches!(body, Expr::Var(_)));
    // On its own, and as a group sharing one type.
    let (_, mode, _, body) = typed(&rhs("def f : Nat := [a b: Kind] => a\n"));
    assert_eq!(mode, Mode::Implicit);
    let (name, mode, _, _) = typed(&body);
    assert_eq!((name.as_str(), mode), ("b", Mode::Implicit));
    // `auto`, with a name and without one.
    let (name, mode, ty, _) = typed(&rhs("def f : Nat := [auto h: Ord a] => h\n"));
    assert_eq!(
        (name.as_str(), mode, ty.as_str()),
        ("h", Mode::Auto, "(Ord a)")
    );
    let (name, mode, _, _) = typed(&rhs("def f : Nat := [auto Ord a] => 0\n"));
    assert_eq!((name.as_str(), mode), (crate::ast::NAMELESS, Mode::Auto));
    // Mixed with plain parameters, in any order.
    match &rhs("def f : Nat := x [a: Kind] y => x\n") {
        Expr::Lam(names, body, _) => {
            assert_eq!(names.len(), 1);
            let (_, mode, _, body) = typed(body);
            assert_eq!(mode, Mode::Implicit);
            assert!(matches!(&body, Expr::Lam(names, _, _) if names.len() == 1));
        }
        other => panic!("expected a lambda, got {other:?}"),
    }
    // The function type with the same start is unaffected, and so is a
    // list.
    assert!(matches!(
        rhs("def f : Nat := [a: Type] -> a -> a\n"),
        Expr::Pi { implicit: true, .. }
    ));
    assert!(matches!(rhs("def f : Nat := [a, b]\n"), Expr::List(..)));
    // A missing type is the header's error.
    let message = error_text("def f : Nat := [a] => a\n");
    assert!(message.contains("needs a type"), "{message}");
}

#[test]
fn rejects_bad_pattern_bindings() {
    assert!(rhs_of("def f (e : Nat) : Nat :=\n  let (a, b) := e\n").is_err());
    assert!(rhs_of("def f (e : Nat) : Nat :=\n  let (a, b)\n  e\n").is_err());
}

#[test]
fn a_lambda_on_the_right_takes_the_rest_of_the_pipeline() {
    let cases = [
        ("x |> y => f y", "(|> x (\\y (f y)))"),
        ("x |> y => f y |> g", "(|> x (\\y (|> (f y) g)))"),
        ("x |> f |> y => y + 1", "(|> (|> x f) (\\y (Add y 1)))"),
        (
            "x |> List.map (y => y |> f)",
            "(|> x (List.map (\\y (|> y f))))",
        ),
    ];
    for (text, want) in cases {
        assert_eq!(pipe_shape(text), want, "{text}");
    }
}

#[test]
fn a_method_section_is_a_lambda_over_a_dot_call() {
    let cases = [
        (".name", "(\\%section %section.name)"),
        // The head section takes its arguments.
        (".drop 1", "(\\%section (%section.drop 1))"),
        (".fold a b", "(\\%section ((%section.fold a) b))"),
        // Chains.
        (".name.length", "(\\%section %section.name.length)"),
        // As an argument it takes none, unless it's in brackets.
        (
            "List.map .name ps",
            "((List.map (\\%section %section.name)) ps)",
        ),
        (
            "ps.map (.greet h)",
            "(ps.map (\\%section (%section.greet h)))",
        ),
        ("(.split c)", "(\\%section (%section.split c))"),
        // A space before the dot makes it a section; none, a field.
        ("f p .name", "((f p) (\\%section %section.name))"),
        ("f p.name", "(f p.name)"),
    ];
    for (text, want) in cases {
        assert_eq!(section_shape(text), want, "{text}");
    }
}

#[test]
fn a_section_in_a_pipe_is_a_plain_dot_call() {
    // No lambda and no `Pipe`: the same tree as writing the calls out.
    let cases = [
        ("xs |> .drop 1", "(xs.drop 1)"),
        ("xs |> .name", "xs.name"),
        ("xs |> .drop 1 |> .sum", "(xs.drop 1).sum"),
        ("xs |> .name.length", "xs.name.length"),
        ("xs |> .drop 1 |> f", "(|> (xs.drop 1) f)"),
    ];
    for (text, want) in cases {
        assert_eq!(section_shape(text), want, "{text}");
    }
    assert_eq!(section_shape("xs |> .drop 1"), section_shape("xs.drop 1"));
    assert_eq!(
        section_shape("xs |> .drop 1 |> .sum"),
        section_shape("(xs.drop 1).sum")
    );
}

#[test]
fn a_pipe_line_may_start_with_a_section() {
    let want = "(x.map f).sum";
    assert_eq!(pipe_body("  x\n    |> .map f\n    |> .sum"), want);
    assert_eq!(pipe_body("  x\n  |> .map f\n  |> .sum"), want);
    assert_eq!(pipe_body("  x |> .map f\n    |> .sum"), want);
}

#[test]
fn a_line_cant_start_with_a_section_as_an_argument() {
    let err = parse_error("def g (x : Nat) : Nat :=\n  foo x\n    .map f\n");
    assert!(
        err.message
            .contains("a line can't start with a method section"),
        "{}",
        err.message
    );
}

#[test]
fn a_section_at_the_start_of_an_expression_takes_the_whole_expression() {
    let cases = [
        ("(.id == id)", "(\\%section (EqEq %section.id id))"),
        ("(.a + 1 * 2)", "(\\%section (Add %section.a (Mul 1 2)))"),
        (
            "(.drop 1 == xs)",
            "(\\%section (EqEq (%section.drop 1) xs))",
        ),
        (
            "(.items |> List.sum)",
            "(\\%section (|> %section.items List.sum))",
        ),
        ("(.a <-> b)", "(\\%section ((Std.Iff %section.a) b))"),
        // A section alone, or as an argument, is as it was.
        ("(.id)", "(\\%section %section.id)"),
        ("f .a == b", "(EqEq (f (\\%section %section.a)) b)"),
        // Only the first section is the function's argument.
        (
            "(.a && .b)",
            "(\\%section (And %section.a (\\%section %section.b)))",
        ),
        // After `|>` the section is the call it stands for, and a
        // comparison after it compares the result.
        ("xs |> .sum == 6", "(EqEq xs.sum 6)"),
        ("a && xs |> .length == 4", "(And a (EqEq xs.length 4))"),
        ("xs |> .show ++ y", "(Append xs.show y)"),
    ];
    for (text, want) in cases {
        assert_eq!(section_shape(text), want, "{text}");
    }
    assert_eq!(
        section_shape("xs |> .drop 1 |> .sum"),
        section_shape("(xs.drop 1).sum")
    );
    let membership = section_shape("(.a !in xs)");
    assert!(
        membership.starts_with("(\\%section (Std.Bool.not (In("),
        "{membership}"
    );
}

#[test]
fn an_operator_section_is_a_lambda_with_the_operand_missing() {
    let cases = [
        ("(== s)", "(\\%section (EqEq %section s))"),
        ("(!= s)", "(\\%section (Ne %section s))"),
        ("(> 3)", "(\\%section (Lt 3 %section))"),
        ("(<= 3)", "(\\%section (Le %section 3))"),
        ("(+ 1)", "(\\%section (Add %section 1))"),
        ("(* 2 )", "(\\%section (Mul %section 2))"),
        ("(++ ys)", "(\\%section (Append %section ys))"),
        ("(|| a && b)", "(\\%section (Or %section (And a b)))"),
        ("(&& a == b)", "(\\%section (And %section (EqEq a b)))"),
        ("(<-> q)", "(\\%section ((Std.Iff %section) q))"),
        ("(k +)", "(\\%section (Add k %section))"),
        ("(k ++)", "(\\%section (Append k %section))"),
        ("(n * 2 ==)", "(\\%section (EqEq (Mul n 2) %section))"),
        ("(a * b +)", "(\\%section (Add (Mul a b) %section))"),
        ("(p &&)", "(\\%section (And p %section))"),
    ];
    for (text, want) in cases {
        assert_eq!(section_shape(text), want, "{text}");
    }
    assert!(section_shape("(in xs)").starts_with("(\\%section (In("));
    assert!(section_shape("(!in xs)").starts_with("(\\%section (Std.Bool.not (In("));
    assert!(section_shape("(k in)").starts_with("(\\%section (In("));
}

#[test]
fn a_bare_operator_is_a_function_of_two_arguments() {
    let cases = [
        ("(&&)", "(\\%left %right (And %left %right))"),
        ("(+)", "(\\%left %right (Add %left %right))"),
        ("(-)", "(\\%left %right (Sub %left %right))"),
        ("(==)", "(\\%left %right (EqEq %left %right))"),
        ("(>)", "(\\%left %right (Lt %right %left))"),
    ];
    for (text, want) in cases {
        assert_eq!(section_shape(text), want, "{text}");
    }
}

#[test]
fn minus_is_not_an_operator_section() {
    assert!(matches!(expression("(- 1)").unwrap(), Expr::Neg(..)));
    assert!(matches!(expression("(-1)").unwrap(), Expr::Neg(..)));
    for bad in ["(k -)", "(+ 1 + 2)", "(a + b *)", "(k + 1 +)", "(== == 1)"] {
        assert!(expression(bad).is_err(), "{bad}");
    }
}

#[test]
fn a_section_needs_a_lowercase_name_right_after_the_dot() {
    for bad in [". name", ".Name", ".1", "(. name)", "f .Name"] {
        assert!(expression(bad).is_err(), "{bad}");
    }
}

#[test]
fn a_line_starting_with_a_pipe_continues_the_expression() {
    let want = "(|> (|> x f) g)";
    // Deeper than the expression, and at the block's own column.
    assert_eq!(pipe_body("  x\n    |> f\n    |> g"), want);
    assert_eq!(pipe_body("  x\n  |> f\n  |> g"), want);
    assert_eq!(pipe_body("  x |> f\n    |> g"), want);
    assert_eq!(pipe_body("  x |> f\n  |> g"), want);
    assert_eq!(pipe_body("  x\n    |> f\n  |> g"), want);
    // Inside a `let` block, the rest of the block is the body.
    assert_eq!(
        pipe_body("  let y := x\n  y\n  |> f\n  |> g"),
        "(let y x (|> (|> y f) g))"
    );
    assert_eq!(
        pipe_body("  let y := x\n    |> f\n  y |> g"),
        "(let y (|> x f) (|> y g))"
    );
    assert_eq!(pipe_body("  x + 1\n  |> f"), "(|> (Add x 1) f)");
    // A comparison on the last line compares the pipeline's result.
    assert_eq!(
        pipe_body("  x\n    |> f\n    |> g == y"),
        "(EqEq (|> (|> x f) g) y)"
    );
    assert_eq!(
        pipe_body("  x\n    |> .map f\n    |> .sum = y"),
        "(Eq (x.map f).sum y)"
    );
}

#[test]
fn a_line_starting_with_an_infix_operator_continues_the_statement() {
    let want = "(And a (And b c))";
    // Deeper than the block, and at the block's own column.
    assert_eq!(pipe_body("  a\n    && b\n    && c"), want);
    assert_eq!(pipe_body("  a\n  && b\n  && c"), want);
    assert_eq!(pipe_body("  a && b\n  ∧ c"), want);
    assert_eq!(pipe_body("  a\n  ∧ b\n    ∧ c"), want);
    assert_eq!(pipe_body("  a\n  + b\n  * c"), "(Add a (Mul b c))");
    assert_eq!(pipe_body("  a\n  = b"), "(Eq a b)");
    // A `let` value stays on its line; the next line is the body.
    assert_eq!(pipe_body("  let y := a\n  y\n  ∨ b"), "(let y a (Or y b))");
}

#[test]
fn a_line_starting_with_an_ambiguous_operator_is_a_new_statement() {
    // `-` and `!` can start an expression, so at the block's column they
    // begin a statement (negation), as they always did.
    for line in ["-b", "!b"] {
        let body = rhs_of(&format!("def g (x : Nat) : Nat :=\n  a\n  {line}\n")).unwrap();
        assert!(matches!(body, Expr::Seq(..)), "{line}");
    }
    // Left of the block's column an operator is still an error.
    assert!(rhs_of("def g (x : Nat) : Nat :=\n   a\n  ∧ b\n").is_err());
}

#[test]
fn a_pipe_is_not_a_bar() {
    // `|` still separates the arms of a definition and a `match`.
    let module = parse("def f : Nat -> Nat\n  | 0 => 1 |> g\n  | n => n |> h\n");
    let arms: Vec<String> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Equation { rhs: Some(rhs), .. } => Some(pshape(rhs)),
            _ => None,
        })
        .collect();
    assert_eq!(arms, ["(|> 1 g)", "(|> n h)"]);
    assert_eq!(
        pipe_body("  match x with\n    | 0 => a |> f\n    | n => n |> g"),
        "(match x | (|> a f) | (|> n g))"
    );
    // `||` is still `Or`, and a row's `|` still has its tail after it.
    assert_eq!(pipe_shape("a || b"), "(Or a b)");
    let module = parse("def f (h : Nat -> {IO | e} Nat) : Nat := 1\n");
    assert!(matches!(module.decls.last(), Some(Decl::Equation { .. })));
    let module = parse("def f (h : Nat -> {IO | e} Nat) : Nat :=\n  1\n  |> g\n");
    assert!(matches!(module.decls.last(), Some(Decl::Equation { .. })));
}

#[test]
fn list_spreads_are_items_anywhere_in_a_list_expression() {
    let list = rhs("def f : Nat := [a, ..xs, b, ..f ys]\n");
    let Expr::List(items, _) = &list else {
        panic!("a list")
    };
    let shape: Vec<bool> = items
        .iter()
        .map(|i| matches!(i, Expr::Spread(..)))
        .collect();
    assert_eq!(shape, [false, true, false, true]);
    assert!(matches!(rhs("def f : Nat := [..xs]\n"), Expr::List(..)));
    let message = parse_error("def f : Nat := [a, ..]\n").message;
    assert!(message.contains("a list after `..`"), "{message}");
    let message = parse_error("def f : Nat := arithmetic [h, ..xs]\n").message;
    assert!(message.contains("list of facts"), "{message}");
}
