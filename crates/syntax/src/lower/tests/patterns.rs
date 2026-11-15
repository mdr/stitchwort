use super::*;

#[test]
fn record_patterns() {
    let module = parse(
        "def f : R -> R -> Nat\n  | { name, age = Succ n, .. }, { tag = (Cons x xs) } => 0\n",
    );
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!("expected an equation");
    };
    let Pattern::Record {
        fields, rest: true, ..
    } = &patterns[0]
    else {
        panic!("expected a record pattern with `..`");
    };
    assert!(matches!(&fields[0].1, Pattern::Var(n) if n.text == "name"));
    assert!(
        matches!(&fields[1].1, Pattern::Ctor(n, args, _) if n.text == "Succ" && args.len() == 1)
    );
    assert!(matches!(&patterns[1], Pattern::Record { rest: false, .. }));
}

/// Braces right after a constructor name its fields; a record pattern
/// as its argument is in brackets (docs/proposals/variant-fields.md §4).
#[test]
fn constructor_field_patterns() {
    let module = parse(
        "def f : S -> S -> S -> Nat\n  | C { id, text = Cons x _, .. }, (W ({ name, .. })), (D { }) => 0\n",
    );
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!("expected an equation");
    };
    let Pattern::CtorFields {
        ctor,
        fields,
        rest: true,
        ..
    } = &patterns[0]
    else {
        panic!("expected named fields: {:?}", patterns[0]);
    };
    assert_eq!(ctor.text, "C");
    assert!(matches!(&fields[0].1, Pattern::Var(n) if n.text == "id"));
    assert!(
        matches!(&fields[1].1, Pattern::Ctor(n, args, _) if n.text == "Cons" && args.len() == 2)
    );
    assert!(matches!(&patterns[1], Pattern::Ctor(n, args, _)
        if n.text == "W" && matches!(&args[..], [Pattern::Record { rest: true, .. }])));
    assert!(
        matches!(&patterns[2], Pattern::CtorFields { fields, rest: false, .. }
        if fields.is_empty())
    );
    // Parses in a `match` arm, a `let`, a tuple, a list and after a
    // field's `=` (`parse` panics on an error).
    parse(
        "def g (s: S): Nat :=\n  let C { id, .. } := s\n  match s with\n    | (C { id }, [D { .. }]) => 0\n    | W { p = C { id, .. }, .. } => 1\n",
    );
}

#[test]
fn braces_after_a_constructor_pattern_take_no_further_arguments() {
    let e = parse_error("def f : L -> Nat\n  | Cons { name, .. } rest => 0\n");
    assert!(e.message.contains("take no further arguments"), "{e:?}");
    assert!(e.notes[0].contains("Cons ({ … })"), "{e:?}");
    // After another argument, a record pattern is one more argument.
    let module = parse("def f : E -> Nat\n  | MkEntry r { name, .. } => 0\n");
    assert_eq!(module.decls.len(), 2);
    let e = parse_error("def f : E -> Nat\n  | Pair Filling { name, .. } => 0\n");
    assert!(e.message.contains("written in brackets"), "{e:?}");
}

#[test]
fn parses_text_patterns() {
    let e = rhs(
        "def f (t : Text) : Nat :=\n  match t with\n    | \"def\" | \"\\n\" => 1\n    | Some \"on\" => 2\n    | _ => 3\n",
    );
    let (_, alts) = match_parts(&e);
    assert!(matches!(
        or_alternatives(&alts[0].patterns[0]),
        [Pattern::Text(a, _), Pattern::Text(b, _)] if a == "def" && b == "\n"
    ));
    assert!(matches!(
        &alts[1].patterns[0],
        Pattern::Ctor(_, args, _) if matches!(args.as_slice(), [Pattern::Text(on, _)] if on == "on")
    ));
}

#[test]
fn refuses_interpolated_text_patterns() {
    let d =
        parse_error("def f (t : Text) : Nat := match t with\n  | \"a${t}b\" => 1\n  | _ => 2\n");
    assert_eq!(d.code, "E-TEXT-PATTERN");
    assert_eq!(d.message, "a text pattern can't interpolate");
}

#[test]
fn parses_or_patterns() {
    // On one line, one arm; a `|` that starts a line starts the next.
    let e = rhs(
        "def f (c : Char) : Nat :=\n  match c with\n    | 'k' | 'w' => 1\n    | Red | Green _ => 2\n    | _ => 3\n",
    );
    let (_, alts) = match_parts(&e);
    assert_eq!(alts.len(), 3);
    let first = or_alternatives(&alts[0].patterns[0]);
    assert!(matches!(
        first,
        [Pattern::Char('k', _), Pattern::Char('w', _)]
    ));
    assert!(matches!(
        or_alternatives(&alts[1].patterns[0]),
        [Pattern::Ctor(_, none, _), Pattern::Ctor(_, one, _)] if none.is_empty() && one.len() == 1
    ));
    assert!(matches!(alts[2].patterns[0], Pattern::Wildcard(_)));

    // `|` binds tighter than `,`.
    let e = rhs("def f (a : Nat) (b : Nat) : Nat := match a, b with | 0 | 1, Red | Green => 0\n");
    let (_, alts) = match_parts(&e);
    assert_eq!(alts.len(), 1);
    assert_eq!(or_alternatives(&alts[0].patterns[0]).len(), 2);
    assert_eq!(or_alternatives(&alts[0].patterns[1]).len(), 2);

    // Nested in brackets, a tuple and a list.
    let e = rhs(
        "def f (p : Nat) : Nat := match p with | Some ('a' | 'b') => 0 | (0 | 1, _) => 1 | [_, 'x' | 'y'] => 2\n",
    );
    let (_, alts) = match_parts(&e);
    let Pattern::Ctor(_, args, _) = &alts[0].patterns[0] else {
        panic!("{:?}", alts[0].patterns[0])
    };
    assert_eq!(or_alternatives(&args[0]).len(), 2);
    let Pattern::Tuple(a, _, _) = &alts[1].patterns[0] else {
        panic!("{:?}", alts[1].patterns[0])
    };
    assert_eq!(or_alternatives(a).len(), 2);
    let Pattern::Cons(_, rest, _) = &alts[2].patterns[0] else {
        panic!("{:?}", alts[2].patterns[0])
    };
    assert!(matches!(&**rest, Pattern::Cons(x, _, _) if or_alternatives(x).len() == 2));

    // In a definition's arms.
    let module = parse("def f: Colour -> Nat\n  | Red | Blue => 1\n  | _ => 2\n");
    let arms: Vec<&Pattern> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Equation { patterns, .. } => Some(&patterns[0]),
            _ => None,
        })
        .collect();
    assert_eq!(arms.len(), 2);
    assert_eq!(or_alternatives(arms[0]).len(), 2);
}

#[test]
fn rejects_binding_in_or_patterns() {
    for text in [
        "def f (o : Nat) : Nat := match o with | Some x | None => 0\n",
        "def f (o : Nat) : Nat := match o with | Some (x | 0) => 0\n",
        "def f (o : Nat) : Nat := match o with | { name } | _ => 0\n",
    ] {
        let error = rhs_of(text).unwrap_err();
        assert_eq!(error.code, "E-OR-PATTERN-BINDS", "{text}");
    }
    assert!(rhs_of("def f (o : Nat) : Nat := match o with | Some _ | None => 0\n").is_ok());
}

#[test]
fn negative_number_patterns() {
    let module = parse("def f : Int -> Nat -> Option Int -> Nat\n  | (-1), 0, (Some (-20)) => 1\n");
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(matches!(&patterns[0], Pattern::NegNum(n, _) if *n == 1u32.into()));
    assert!(matches!(&patterns[1], Pattern::Num(..)));
    let Pattern::Ctor(_, args, _) = &patterns[2] else {
        panic!()
    };
    assert!(matches!(&args[0], Pattern::NegNum(n, _) if *n == 20u32.into()));
    for bad in [
        "def f : Int -> Nat\n  | (-x) => 1\n",
        "def f : Int -> Nat\n  | (- - 1) => 1\n",
        "def f : Int -> Nat\n  | (-1 + 2) => 1\n",
    ] {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", bad);
        assert!(parse_module(file, bad).is_err(), "{bad}");
    }
}

#[test]
fn parses_list_patterns() {
    let module = parse(
        "def f : A -> B -> C -> D -> E -> Nat\n  | [], [a], [a, b], [Some x, (-1)], (xs, [y]) => a\n",
    );
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(matches!(patterns[0], Pattern::Nil(_)));
    assert!(matches!(&patterns[1], Pattern::Cons(_, t, _) if matches!(**t, Pattern::Nil(_))));
    let Pattern::Cons(_, rest, _) = &patterns[2] else {
        panic!()
    };
    assert!(matches!(&**rest, Pattern::Cons(_, t, _) if matches!(**t, Pattern::Nil(_))));
    let Pattern::Cons(head, _, _) = &patterns[3] else {
        panic!()
    };
    assert!(matches!(&**head, Pattern::Ctor(_, args, _) if args.len() == 1));
    assert!(matches!(&patterns[4], Pattern::Tuple(_, r, _) if matches!(**r, Pattern::Cons(..))));
}

#[test]
fn parses_tuple_patterns() {
    let module =
        parse("def f : A -> B -> C -> Nat\n  | (a, b, c), ((d, e) , _), (Cons (x, y) ys) => a\n");
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(matches!(&patterns[0], Pattern::Tuple(_, r, _) if matches!(**r, Pattern::Tuple(..))));
    assert!(matches!(&patterns[1], Pattern::Tuple(l, _, _) if matches!(**l, Pattern::Tuple(..))));
    assert!(matches!(&patterns[2], Pattern::Ctor(_, args, _)
        if matches!(args[0], Pattern::Tuple(..))));
}

#[test]
fn parses_a_constructor_as_a_tuples_first_component() {
    let module = parse("def f : A -> Nat\n  | (Some a, b) => a\n");
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(matches!(&patterns[0], Pattern::Tuple(l, _, _)
        if matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1)));

    let e = rhs("def f (p : Nat) : Nat :=\n  let (Some a, b) := p\n  a\n");
    let (_, p, _) = let_parts(&e);
    assert!(matches!(p, Pattern::Tuple(l, _, _)
        if matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1)));
}

#[test]
fn parses_constructors_with_arguments_in_later_tuple_components() {
    let module = parse("def f : A -> Nat\n  | (Some x, Some y, Some z) => x\n");
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    // (Some x, (Some y, Some z)): every component keeps its argument.
    let Pattern::Tuple(l, r, _) = &patterns[0] else {
        panic!()
    };
    assert!(matches!(&**l, Pattern::Ctor(_, args, _) if args.len() == 1));
    assert!(matches!(&**r, Pattern::Tuple(m, n, _)
        if matches!(&**m, Pattern::Ctor(_, a, _) if a.len() == 1)
            && matches!(&**n, Pattern::Ctor(_, a, _) if a.len() == 1)));
}

#[test]
fn parses_negative_numbers_in_tuple_patterns() {
    let text = "def f : A -> B -> C -> Nat\n  | (-1, 0), (0, -2), (-3) => a\n";
    let module = parse(text);
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(matches!(&patterns[0], Pattern::Tuple(l, _, _)
        if matches!(&**l, Pattern::NegNum(n, _) if *n == 1u32.into())));
    assert!(matches!(&patterns[1], Pattern::Tuple(_, r, _)
        if matches!(&**r, Pattern::NegNum(n, _) if *n == 2u32.into())));
    // `(-3)` still spans the whole bracketed pattern.
    let Pattern::NegNum(n, span) = &patterns[2] else {
        panic!()
    };
    assert!(*n == 3u32.into());
    let start = text.find("(-3)").unwrap() as u32;
    assert_eq!((span.start, span.end), (start, start + 4));
    let bad = "def f : A -> Nat\n  | (-x, 0) => a\n";
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", bad);
    assert!(parse_module(file, bad).is_err(), "{bad}");
}

#[test]
fn rejects_bad_tuples() {
    for bad in [
        "def f : Nat := (1,)\n",
        "def f : Nat := (a, b : T)\n",
        "def f : Nat := (a : T, b)\n",
        "def f : A -> Nat\n  | (a,) => a\n",
    ] {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", bad);
        assert!(parse_module(file, bad).is_err(), "{bad}");
    }
}

#[test]
fn parses_let_patterns() {
    let e = rhs("def f (e : Nat) : Nat :=\n  let (a, b) := e\n  a\n");
    let (s, p, body) = let_parts(&e);
    assert!(matches!(s, Expr::Var(_)));
    assert!(matches!(p, Pattern::Tuple(..)));
    assert!(matches!(body, Expr::Var(_)));

    let e = rhs("def f (p : Nat) : Nat :=\n  let MkPair a b := p\n  a\n");
    let (_, p, _) = let_parts(&e);
    assert!(matches!(p, Pattern::Ctor(_, args, _) if args.len() == 2));

    let e = rhs("def f (p : Nat) : Nat :=\n  let Pair.MkPair a b := p\n  a\n");
    let (_, p, _) = let_parts(&e);
    assert!(matches!(p, Pattern::Ctor(n, args, _) if args.len() == 2 && n.text == "Pair.MkPair"));

    let e = rhs("def f (r : Nat) : Nat :=\n  let { x, .. } := r\n  x\n");
    let (_, p, _) = let_parts(&e);
    assert!(matches!(p, Pattern::Record { rest: true, .. }));

    let e = rhs("def f (e : Nat) : Nat :=\n  let (a, b) : (Nat, Nat) := e\n  a\n");
    let (s, _, _) = let_parts(&e);
    assert!(matches!(s, Expr::Ann(..)));

    let e = rhs("def f (e : Nat) : Nat :=\n  let _ := e\n  0\n");
    let (_, p, _) = let_parts(&e);
    assert!(matches!(p, Pattern::Wildcard(_)));

    // Plain lets are unchanged.
    for text in [
        "def f (e : Nat) : Nat :=\n  let x := e\n  x\n",
        "def f (e : Nat) : Nat :=\n  let (x) := e\n  x\n",
    ] {
        assert!(matches!(rhs(text), Expr::Let { .. }), "{text}");
    }

    // Later lines nest inside the match.
    let e = rhs("def f (e : Nat) : Nat :=\n  let (a, b) := e\n  let c := a\n  c\n");
    let (_, _, body) = let_parts(&e);
    assert!(matches!(body, Expr::Let { .. }));
}

#[test]
fn parses_lambda_patterns() {
    let lam = |text: &str| match &rhs(text) {
        Expr::Lam(names, body, _) => (names.clone(), body.as_ref().clone()),
        other => panic!("expected a lambda, got {other:?}"),
    };
    let lambda_match = |body: &Expr| match body {
        Expr::Match {
            scrutinees,
            alts,
            kind: MatchKind::Lambda,
            ..
        } => (scrutinees.len(), alts[0].patterns.len()),
        other => panic!("expected a lambda match, got {other:?}"),
    };

    let (names, body) = lam("def f : Nat := (a, b) => a\n");
    assert_eq!(names[0].text, "%arg0");
    assert_eq!(lambda_match(&body), (1, 1));

    let (names, body) = lam("def f : Nat := acc (k, v) => acc\n");
    let texts: Vec<_> = names.iter().map(|n| n.text.as_str()).collect();
    assert_eq!(texts, ["acc", "%arg1"]);
    assert_eq!(lambda_match(&body), (1, 1));

    let (names, body) = lam("def f : Nat := { name, .. } => name\n");
    assert_eq!(names[0].text, "%arg0");
    assert_eq!(lambda_match(&body), (1, 1));

    let (_, body) = lam("def f : Nat := (MkPair a b) => a\n");
    assert_eq!(lambda_match(&body), (1, 1));

    let (names, body) = lam("def f : Nat := (a, b) (c, d) => a\n");
    assert_eq!(names.len(), 2);
    assert_eq!(lambda_match(&body), (2, 2));

    // Plain parameters are unchanged.
    let (names, body) = lam("def f : Nat := x y => x\n");
    assert_eq!(names.len(), 2);
    assert!(matches!(body, Expr::Var(_)));
    let (names, body) = lam("def f : Nat := (x) _ => x\n");
    assert_eq!(names.len(), 2);
    assert!(matches!(body, Expr::Var(_)));
}

#[test]
fn lambda_patterns_may_be_annotated() {
    let Expr::TypedLam(name, Mode::Explicit, ty, body, _) =
        &rhs("def f : Nat := ((a, b): (Nat, Nat)) => a\n")
    else {
        panic!("expected a typed lambda");
    };
    assert_eq!(name.text, "%arg0");
    assert!(matches!(**ty, Expr::Tuple(..)));
    assert!(matches!(
        **body,
        Expr::Match {
            kind: MatchKind::Lambda,
            ..
        }
    ));
    // Among plain parameters, with a record pattern.
    let Expr::Lam(names, body, _) = &rhs("def f : Nat := x ({ n, .. }: P) => x\n") else {
        panic!("expected a lambda");
    };
    assert_eq!(names[0].text, "x");
    assert!(matches!(**body, Expr::TypedLam(..)));
}
