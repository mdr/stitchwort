use super::*;

#[test]
fn field_access_binds_tighter_than_application() {
    // `f p.name q` is `f (p.name) q`.
    let e = expression("f p.name q").unwrap();
    let Expr::App(f, q) = &e else {
        panic!("expected an application");
    };
    assert!(matches!(**q, Expr::Var(_)));
    let Expr::App(_, arg) = &**f else {
        panic!("expected `f (p.name)`");
    };
    assert!(
        matches!(&**arg, Expr::Field(e, n, _) if n.text == "name" && matches!(**e, Expr::Var(_)))
    );
    // Chains, and parenthesised expressions.
    let e = expression("t.lead.name").unwrap();
    assert!(matches!(&e, Expr::Field(inner, _, _) if matches!(**inner, Expr::Field(..))));
    assert!(matches!(expression("(f x).age").unwrap(), Expr::Field(..)));
    // No spaces around the dot, and a field name after it.
    for bad in ["p. name", "p.1", "p.Foo.Bar"] {
        assert!(expression(bad).is_err(), "{bad}");
    }
    // A capitalised field names a function of the value's type, as in
    // `xs.Distinct` for `List.Distinct xs`.
    let e = expression("xs.Distinct").unwrap();
    assert!(
        matches!(&e, Expr::Field(r, n, _) if n.text == "Distinct" && matches!(**r, Expr::Var(_)))
    );
    let e = expression("on.Subsequence bank").unwrap();
    let Expr::App(_, arg) = &e else {
        panic!("{e:?}")
    };
    assert!(matches!(&**arg, Expr::Var(n) if n.text == "bank"));
    let Expr::App(f, _) = &e else { panic!("{e:?}") };
    assert!(matches!(&**f, Expr::Field(_, n, _) if n.text == "Subsequence"));
}

#[test]
fn equality_binds_looser_than_addition_and_tighter_than_arrows() {
    let module = parse("def p : (n : Nat) -> n + 0 = n -> Nat\n");
    let Decl::Signature { ty, .. } = &module.decls[0] else {
        panic!("expected a signature");
    };
    let Expr::Pi { cod, .. } = ty else {
        panic!("expected a dependent function type, got {ty:?}");
    };
    let Expr::Arrow(lhs, _) = cod.as_ref() else {
        panic!("expected an arrow, got {cod:?}");
    };
    let Expr::Binary(BinOp::Eq, sum, _) = lhs.as_ref() else {
        panic!("expected an equation, got {lhs:?}");
    };
    assert!(matches!(sum.as_ref(), Expr::Binary(BinOp::Add, ..)));
}

#[test]
fn or_binds_looser_than_and() {
    let Expr::Binary(BinOp::Or, a, rhs) = &expr("a || b && c") else {
        panic!("expected an or");
    };
    assert!(matches!(a.as_ref(), Expr::Var(..)));
    assert!(matches!(rhs.as_ref(), Expr::Binary(BinOp::And, ..)));
}

#[test]
fn and_associates_right() {
    let Expr::Binary(BinOp::And, a, rhs) = &expr("a && b && c") else {
        panic!("expected an and");
    };
    assert!(matches!(a.as_ref(), Expr::Var(..)));
    assert!(matches!(rhs.as_ref(), Expr::Binary(BinOp::And, ..)));
}

#[test]
fn and_then_or_groups_the_and_first() {
    let Expr::Binary(BinOp::Or, lhs, c) = &expr("a && b || c") else {
        panic!("expected an or");
    };
    assert!(matches!(lhs.as_ref(), Expr::Binary(BinOp::And, ..)));
    assert!(matches!(c.as_ref(), Expr::Var(..)));
}

#[test]
fn comparisons_bind_tighter_than_and() {
    let Expr::Binary(BinOp::And, l, r) = &expr("x < y && y < z") else {
        panic!("expected an and");
    };
    assert!(matches!(l.as_ref(), Expr::Binary(BinOp::Lt, ..)));
    assert!(matches!(r.as_ref(), Expr::Binary(BinOp::Lt, ..)));
}

#[test]
fn and_binds_tighter_than_arrow() {
    let Expr::Arrow(lhs, _) = &expr("a && b -> c") else {
        panic!("expected an arrow");
    };
    assert!(matches!(lhs.as_ref(), Expr::Binary(BinOp::And, ..)));
}

#[test]
fn multiplication_binds_tighter_than_addition_and_both_associate_left() {
    let Expr::Binary(BinOp::Sub, lhs, rhs) = &expr("a + b * c - d") else {
        panic!("expected `(a + b * c) - d`");
    };
    assert!(matches!(**rhs, Expr::Var(_)));
    let Expr::Binary(BinOp::Add, _, product) = &**lhs else {
        panic!("expected `a + (b * c)`");
    };
    assert!(matches!(**product, Expr::Binary(BinOp::Mul, ..)));
    assert!(matches!(expr("a / b % c"), Expr::Binary(BinOp::Mod, ..)));
    assert!(matches!(expr("a <= b + 1"), Expr::Binary(BinOp::Le, ..)));
    assert!(matches!(expr("a != b"), Expr::Binary(BinOp::Ne(_), ..)));
    assert!(matches!(expr("a == b + 1"), Expr::Binary(BinOp::EqEq, ..)));
    assert!(matches!(expr("a < b"), Expr::Binary(BinOp::Lt, ..)));
}

/// SW-1339: `<`/`<=` chain, and `>`/`>=` chain, into `&&` of the links;
/// a middle that is not a name or a literal is bound once.
#[test]
fn comparisons_chain() {
    let cases = [
        ("a <= b < x", "(And (Le a b) (Lt b x))"),
        ("a >= b > x", "(And (Le b a) (Lt x b))"),
        ("0 <= a < 10", "(And (Le 0 a) (Lt a 10))"),
        ("a < b <= x < y", "(And (Lt a b) (And (Le b x) (Lt x y)))"),
        // The chain is one conjunct of a longer `&&`.
        ("a <= b <= x && y", "(And (And (Le a b) (Le b x)) y)"),
        ("y || a <= b <= x", "(Or y (And (Le a b) (Le b x)))"),
        // Arithmetic and pipelines bind tighter.
        ("a <= b + 1 <= x", "(And (Le a (Add b 1)) (Le (Add b 1) x))"),
    ];
    for (text, want) in cases {
        let got = shape_of(text);
        // A middle that is not an atom is bound.
        if text.contains('+') {
            assert!(got.starts_with("(let %chain"), "{text}: {got}");
            continue;
        }
        assert_eq!(got, want, "{text}");
    }
}

#[test]
fn a_chain_binds_a_call_in_the_middle_once() {
    let got = shape_of("a <= f x <= b");
    assert!(got.starts_with("(let %chain"), "{got}");
    assert_eq!(got.matches("(f x)").count(), 1, "{got}");
    // Both ends perform: the first is bound before the middle.
    let got = shape_of("f a <= f x <= f b");
    assert_eq!(got.matches("(let %chain").count(), 2, "{got}");
    assert!(got.find("(f a)") < got.find("(f x)"), "{got}");
    // The later operand is bound where it is only run if the first
    // link holds.
    let got = shape_of("a < f x < f y < b");
    let second = got.rfind("(let %chain").unwrap();
    assert!(got[second..].starts_with("(let %chain"), "{got}");
    assert!(got.find("(And (Lt a %chain").unwrap() < second, "{got}");
}

#[test]
fn refused_chains_say_what_to_write() {
    for (text, want) in [
        ("a < b > x", "one way"),
        ("a >= b < x", "one way"),
        ("a < b = x", "`=`"),
        ("a == b == x", "`==`"),
        ("a < b == x", "`==`"),
        ("a != b != x", "`!=`"),
        ("a < b != x", "`!=`"),
        ("a <= b in x", "`in`"),
        ("a <= b !in x", "`in`"),
        ("a = b < x", "`=`"),
        ("a != b <= x", "`!=`"),
        ("a == b < x", "`==`"),
        ("a == b > x", "`==`"),
    ] {
        let e = rhs_of(&format!("def g : Nat := {text}\n")).expect_err(text);
        assert_eq!(e.code, "E-COMPARISON-CHAIN", "{text}");
        assert!(e.message.contains(want), "{text}: {}", e.message);
        assert!(!e.notes.is_empty(), "{text}");
    }
}

#[test]
fn prefix_minus_precedence() {
    let cases = [
        ("-x.abs", "(- x.abs)"),
        ("(-x).abs", "(- x).abs"),
        ("-f x", "(- (f x))"),
        ("f -x", "(f (- x))"),
        ("-a * b", "(Mul (- a) b)"),
        ("a * -b", "(Mul a (- b))"),
        ("-18 % 100", "(Mod (- 18) 100)"),
        ("-(18 % 100)", "(- (Mod 18 100))"),
        ("a - -b", "(Sub a (- b))"),
        ("- -x", "(- (- x))"),
        ("a + -b * c", "(Add a (Mul (- b) c))"),
        ("f (-5)", "(f (- 5))"),
        ("f -5", "(f (- 5))"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
    // `--` starts a comment.
    assert_eq!(shape_of("a --b"), "a");
}

#[test]
fn an_argument_minus_negates_one_atom() {
    let cases = [
        ("f -x.abs", "(f (- x.abs))"),
        ("f -2 * 3", "(Mul (f (- 2)) 3)"),
        ("f -g x", "((f (- g)) x)"),
        ("f 1 -2", "((f 1) (- 2))"),
        ("f -(a * 2)", "(f (- (Mul a 2)))"),
        ("x-1", "(Sub x 1)"),
        ("x- 1", "(Sub x 1)"),
        ("x - 1", "(Sub x 1)"),
        ("x -  1", "(Sub x 1)"),
        ("x - -y", "(Sub x (- y))"),
        ("f \"a\" -1", "((f \"a\") (- 1))"),
        ("(f x) -1", "((f x) (- 1))"),
        ("xs.length -1", "(xs.length (- 1))"),
        ("f() -1", "((f ()) (- 1))"),
        ("f -()", "(f (- ()))"),
        ("f -g()", "(f (- (g ())))"),
        ("f -1 -2", "((f (- 1)) (- 2))"),
        // After `,` or an operator the `-` is prefix, as before.
        ("f x * -y", "(Mul (f x) (- y))"),
        // `--` starts a comment.
        ("f --x", "f"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
    let list = expression("[1, -2]").unwrap();
    assert!(matches!(
        &list,
        Expr::List(items, _) if matches!(&items[1], Expr::Neg(_, _, NegForm::Operand))
    ));
    // A `-` at the end of a line is binary, and needs its operand.
    assert!(rhs_of("def g : Nat := f -\n").is_err());
    // The form is recorded: `f -2` is an argument, `f (-2)` is not.
    let call = rhs_of("def g : Nat := f -2\n").unwrap();
    let Expr::App(_, arg) = &call else {
        panic!("an application")
    };
    assert!(matches!(**arg, Expr::Neg(_, _, NegForm::Argument)));
    let call = rhs_of("def g : Nat := f (-2)\n").unwrap();
    let Expr::App(_, arg) = &call else {
        panic!("an application")
    };
    assert!(matches!(
        &**arg,
        Expr::Neg(_, _, NegForm::Operand) | Expr::Bracketed(..)
    ));
    assert!(!format!("{arg:?}").contains("Argument"));
}

#[test]
fn negative_numerals_are_one_atom() {
    let cases = [
        ("-1.abs", "(- 1).abs"),
        ("f -1.abs", "(f (- 1).abs)"),
        ("x-1.abs", "(Sub x 1.abs)"),
        ("- 1.abs", "(- 1.abs)"),
        ("-x.abs", "(- x.abs)"),
        ("-1.5.abs", "(- 1.5).abs"),
        ("- -1.abs", "(- (- 1).abs)"),
        ("x - -1.abs", "(Sub x (- 1).abs)"),
        ("-3.sub 5", "((- 3).sub 5)"),
        ("-3 * 2", "(Mul (- 3) 2)"),
        ("(-0e-400).bits", "(- 0e-400).bits"),
        ("1e-5", "1e-5"),
        ("x --1", "x"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
}

#[test]
fn an_argument_minus_in_sections_pipes_and_texts() {
    let cases = [
        ("(.fst -1)", "(=> (%section.fst (- 1)))"),
        ("x |> f -1", "(|> x (f (- 1)))"),
        ("\"${x -1}\"", "${(Std.Show.toText (x (- 1)))}"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
    let e = shape_of("xs |> .drop -1");
    assert!(e.contains("(- 1)") && e.contains("drop"), "{e}");
    let e = format!(
        "{:?}",
        rhs_of("def g : Nat := (let z := f -1; z)\n").unwrap()
    );
    assert!(e.contains("Argument"), "{e}");
    let e = format!("{:?}", rhs_of("def g : Nat := (let z := 1; -z)\n").unwrap());
    assert!(e.contains("Operand") && !e.contains("Argument"), "{e}");
}

#[test]
fn a_block_line_starting_with_a_minus_is_a_new_statement() {
    let e = rhs_of("def g (x : Int) : Int :=\n  let y := x + 1\n  -y\n").unwrap();
    let text = format!("{e:?}");
    assert!(text.contains("Let") && text.contains("Operand"), "{text}");
    assert!(!text.contains("Argument"), "{text}");
    // An indented line continues the one above: an argument.
    let e = rhs_of("def g (f : Int -> Int) (x : Int) : Int :=\n  f\n    -x\n").unwrap();
    assert!(matches!(&e, Expr::App(_, a) if matches!(**a, Expr::Neg(_, _, NegForm::Argument))));
    // A line starting `- y` with a space is binary, as before.
    let e = rhs_of("def g (x : Int) (y : Int) : Int :=\n  x\n    - y\n").unwrap();
    assert!(matches!(e, Expr::Binary(BinOp::Sub, ..)), "{e:?}");
}

#[test]
fn a_block_line_starting_with_a_bang_is_a_new_statement() {
    let e = rhs_of("def g (c : Bool) (d : Bool) : Bool :=\n  let y := c\n  !d\n").unwrap();
    let Expr::Let { value, body, .. } = &e else {
        panic!("{e:?}")
    };
    assert_eq!(shape(value), "c");
    assert_eq!(shape(body), "(Std.Bool.not d)");
    // An indented line continues the one above: an argument.
    let e = rhs_of("def g (f : Bool -> Bool) (x : Bool) : Bool :=\n  f\n    !x\n").unwrap();
    assert_eq!(shape(&e), "(f (Std.Bool.not x))");
}

#[test]
fn x_not_in_xs_is_not_an_argument_bang() {
    let e = rhs_of("def g (x : Nat) (xs : List Nat) : Bool := x !in xs\n").unwrap();
    assert!(matches!(e, Expr::App(..)), "{e:?}");
    assert!(format!("{e:?}").contains("In("), "{e:?}");
    let e =
        rhs_of("def g (f : Nat -> Bool) (x : Nat) (xs : List Nat) : Bool := f x !in xs\n").unwrap();
    assert!(format!("{e:?}").contains("In("), "{e:?}");
    // `!` after an operand with a space on both sides, or none before it.
    assert!(rhs_of("def g (f : Bool -> Bool) (a : Bool) : Bool := f ! a\n").is_err());
    assert!(rhs_of("def g (f : Bool -> Bool) (a : Bool) : Bool := f!a\n").is_err());
}

#[test]
fn a_negative_argument_in_a_constructor_pattern() {
    let text =
        "def h (o : Option Int) : Int :=\n  match o with\n    | Some -1 => 0\n    | _ => 1\n";
    let module = parse_module_text(text).unwrap();
    let debug = format!("{module:?}");
    assert!(debug.contains("NegNum(1,"), "{debug}");
    let text =
        "def h (l : List Int) : Int :=\n  match l with\n    | Cons -1 rest => 0\n    | _ => 1\n";
    let debug = format!("{:?}", parse_module_text(text).unwrap());
    assert!(debug.contains("NegNum(1,"), "{debug}");
    // Numerals only, as `(-x)` is.
    let text =
        "def h (o : Option Int) : Int :=\n  match o with\n    | Some -x => 0\n    | _ => 1\n";
    assert!(parse_module_text(text).is_err());
}

#[test]
fn greater_than_is_less_than_flipped() {
    let cases = [
        ("a > b", "(Lt b a)"),
        ("a >= b", "(Le b a)"),
        ("a + 1 > b * 2", "(Lt (Mul b 2) (Add a 1))"),
        ("f x > y", "(Lt y (f x))"),
        ("a ++ b > y", "(Lt y (Append a b))"),
        ("a < b", "(Lt a b)"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
    // They chain, as `<` does.
    assert_eq!(shape_of("a > b > c"), "(And (Lt b a) (Lt c b))");
    // `>>` is not a token (yet).
    assert!(rhs_of("def g : Nat := a >> b\n").is_err());
}

/// An expression the parser writes with its parts out of order, or with
/// a function at an operator, still spans what was written.
#[test]
fn spans_of_expanded_operators_cover_what_was_written() {
    let cases = [
        "n * n > 20",
        "n * n >= f x y",
        "p <-> q",
        "f x <-> g y && z",
        "x !in xs",
        "f x !in g xs",
        "1 <= f x < 20",
        "1 <= f x < g y <= 30",
        "20 > f x > 3",
    ];
    for text in cases {
        let span = expr(text).span();
        assert_eq!(
            (span.start as usize, span.end as usize),
            (0, text.len()),
            "{text}"
        );
    }
}

#[test]
fn range_precedence() {
    let cases = [
        ("a ..< b + 1", "(Range a (Add b 1))"),
        ("0 ..< xs.length", "(Range 0 xs.length)"),
        ("a ..= b ++ c", "(RangeThrough a (Append b c))"),
        ("0 ..< n |> .map f", "((Range 0 n).map f)"),
        ("0 ..< 3 == n", "(EqEq (Range 0 3) n)"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
    for ok in ["[0, ..2 ..< n]", "[..0 ..< 3, 7]", "[0 ..< n]"] {
        assert!(rhs_of(&format!("def g : Nat := {ok}\n")).is_ok(), "{ok}");
    }
    assert!(shape_of("x in 0 ..< n").ends_with("x (Range 0 n))"));
    for bad in ["a ..< b ..< c", "a ..< b ..= c", "a .. b", "a..b", "[2..n]"] {
        assert!(rhs_of(&format!("def g : Nat := {bad}\n")).is_err(), "{bad}");
    }
    let err = rhs_of("def g : Nat := [2..n]\n").unwrap_err();
    assert!(format!("{err:?}").contains("[2, ..n]"));
}

#[test]
fn bang_precedence() {
    let n = "Std.Bool.not";
    let cases = [
        ("!a", format!("({n} a)")),
        ("!f x", format!("({n} (f x))")),
        ("!x.abs", format!("({n} x.abs)")),
        ("!!a", format!("({n} ({n} a))")),
        ("!a > b", format!("(Lt b ({n} a))")),
        ("!a = b", format!("(Eq ({n} a) b)")),
        ("f (!a)", format!("(f ({n} a))")),
        ("f !a", format!("(f ({n} a))")),
        // `¬` is the same token as `!`.
        ("f ¬x", format!("(f ({n} x))")),
        ("f !x.done", format!("(f ({n} x.done))")),
        ("f !g x", format!("((f ({n} g)) x)")),
        ("f !a !b", format!("((f ({n} a)) ({n} b))")),
        ("a != b", "(Ne a b)".to_string()),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
    let e = rhs_of("def g : Bool := !a && b\n").unwrap();
    assert!(matches!(e, Expr::Binary(BinOp::And, ..)), "{e:?}");
}

#[test]
fn arrows_and_pipes_still_parse_beside_greater_than() {
    assert!(rhs_of("def g : Nat := x |> f\n").is_ok());
    assert!(rhs_of("def g : Nat := (x => y) a\n").is_ok());
    assert!(rhs_of("def g : Type := a -> b\n").is_ok());
    assert!(rhs_of("def g : Bool := x |> f > y\n").is_ok());
}

#[test]
fn pipe_is_tighter_than_comparisons_and_looser_than_append() {
    let cases = [
        ("x |> f", "(|> x f)"),
        ("x |> f a b", "(|> x ((f a) b))"),
        ("a + b |> f", "(|> (Add a b) f)"),
        ("a ++ b |> f", "(|> (Append a b) f)"),
        ("x |> f ++ y", "(|> x (Append f y))"),
        ("a || b |> f", "(Or a (|> b f))"),
        ("a && b |> f", "(And a (|> b f))"),
        ("a = b |> f", "(Eq a (|> b f))"),
        ("a == b |> f", "(EqEq a (|> b f))"),
        ("(a == b) |> f", "(|> (EqEq a b) f)"),
        ("x |> f a == y", "(EqEq (|> x (f a)) y)"),
        ("xs |> List.sum == 6", "(EqEq (|> xs List.sum) 6)"),
        ("xs |> List.sum = 6", "(Eq (|> xs List.sum) 6)"),
        ("x |> f < y |> g", "(Lt (|> x f) (|> y g))"),
        ("x |> f || y", "(Or (|> x f) y)"),
        ("x |> f && y", "(And (|> x f) y)"),
        ("a && xs |> f == 4", "(And a (EqEq (|> xs f) 4))"),
        ("x |> f |> g", "(|> (|> x f) g)"),
        ("x |> f |> g |> h", "(|> (|> (|> x f) g) h)"),
        ("x |> f -> T", "(-> (|> x f) T)"),
        ("A -> x |> f", "(-> A (|> x f))"),
        ("x |> f <-> y", "((Std.Iff (|> x f)) y)"),
        ("(x |> f) = y", "(Eq (|> x f) y)"),
        ("x |> (f = y)", "(|> x (Eq f y))"),
        ("[a |> f, b]", "[(|> a f) b]"),
    ];
    for (text, want) in cases {
        assert_eq!(pipe_shape(text), want, "{text}");
    }
}

#[test]
fn membership_sits_with_the_comparisons() {
    // `x in xs && y !in ys`: no brackets needed.
    let Expr::Binary(BinOp::And, l, r) = &expr("x in xs && y !in ys") else {
        panic!("expected `&&`");
    };
    assert!(matches!(l.as_ref(), Expr::Binary(BinOp::In(_), ..)));
    // `!in` is `!(y in ys)`.
    let Expr::App(not, member) = r.as_ref() else {
        panic!("expected `!(…)`");
    };
    assert!(matches!(not.as_ref(), Expr::Var(n) if n.text == "Std.Bool.not"));
    assert!(matches!(member.as_ref(), Expr::Binary(BinOp::In(_), ..)));
    // Tighter than `++` loses: `x in xs ++ ys` is `x in (xs ++ ys)`.
    let Expr::Binary(BinOp::In(_), _, rhs) = &expr("x in xs ++ ys") else {
        panic!("expected `in`");
    };
    assert!(matches!(rhs.as_ref(), Expr::Binary(BinOp::Append, ..)));
    // Not associative.
    assert!(parse_module_text("def t: Bool := a in b in c\n").is_err());
    // `!x in xs` would be `(!x) in xs`: refused, with brackets allowed.
    let error = parse_errors("def t: Bool := !x in xs\n");
    assert!(error.contains("applies to the element"), "{error}");
    assert!(parse_errors("def t: Bool := ¬x ∈ xs\n").contains("applies to the element"));
    assert!(parse_module_text("def t: Bool := (!x) in xs\n").is_ok());
    assert!(parse_module_text("def t: Bool := !(x in xs)\n").is_ok());
}

#[test]
fn iff_sits_between_arrow_and_or() {
    let iff = |e: &Expr| -> Option<(Expr, Expr)> {
        let Expr::App(f, q) = e else { return None };
        let Expr::App(head, p) = f.as_ref() else {
            return None;
        };
        matches!(head.as_ref(), Expr::Var(n) if n.text == "Std.Iff")
            .then(|| (p.as_ref().clone(), q.as_ref().clone()))
    };
    // `p && q <-> r` is `(p && q) <-> r`.
    let (p, _) = iff(&expr("p && q <-> r || s")).expect("an iff");
    assert!(matches!(p, Expr::Binary(BinOp::And, ..)));
    // `p -> q <-> r` is `p -> (q <-> r)`, and `p <-> q -> r` is
    // `(p <-> q) -> r`.
    let Expr::Arrow(_, rhs) = &expr("p -> q <-> r") else {
        panic!("expected an arrow");
    };
    assert!(iff(rhs).is_some());
    let Expr::Arrow(lhs, _) = &expr("p <-> q -> r") else {
        panic!("expected an arrow");
    };
    assert!(iff(lhs).is_some());
    // Not associative.
    assert!(parse_errors("def t: Prop := p <-> q <-> r\n").contains("doesn't chain"));
    assert!(parse_module_text("def t: Prop := (p <-> q) <-> r\n").is_ok());
}

#[test]
fn ne_remembers_whether_it_was_written_ascii_or_unicode() {
    // The two spellings mean the same thing, but a message that quotes the
    // source tells them apart (SW-3125).
    assert!(matches!(
        expr("a != b"),
        Expr::Binary(BinOp::Ne(NeForm::Ascii), ..)
    ));
    assert!(matches!(
        expr("a ≠ b"),
        Expr::Binary(BinOp::Ne(NeForm::Unicode), ..)
    ));
}
