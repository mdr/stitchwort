use super::*;

#[test]
fn record_literals_updates_and_puns() {
    let e = expression("{ b = f x, a }").unwrap();
    let Expr::Record {
        base: None, fields, ..
    } = &e
    else {
        panic!("expected a literal");
    };
    // In the order written; a pun is a variable.
    assert_eq!(fields[0].0.text, "b");
    assert!(matches!(&fields[0].1, Expr::App(..)));
    assert!(matches!(&fields[1].1, Expr::Var(n) if n.text == "a"));
    let e = expression("{ f p | age = 1 }").unwrap();
    let Expr::Record {
        base: Some(base),
        fields,
        ..
    } = &e
    else {
        panic!("expected an update");
    };
    assert!(matches!(**base, Expr::App(..)));
    assert_eq!(fields.len(), 1);
    let e = expression("{}").unwrap();
    assert!(matches!(&e, Expr::Record { base: None, fields, .. } if fields.is_empty()));
    // An update needs a field.
    assert!(expression("{ p | }").is_err());
}

#[test]
fn unit_call_is_one_atom() {
    let shape = |text: &str| match &expression(text).unwrap() {
        Expr::Field(r, n, _) => format!("{:?}.{}", matches!(**r, Expr::App(..)), n.text),
        Expr::App(f, _) => format!("app({})", matches!(**f, Expr::Field(..))),
        _ => "other".into(),
    };
    // `f().x` is `(f()).x`; `IO.readAll().lines` too.
    assert_eq!(shape("f().x"), "true.x");
    assert_eq!(shape("IO.readAll().lines"), "true.lines");
    // `f().g y` is `(f()).g y`: an application of a field of the call.
    let e = expression("f().g y").unwrap();
    let Expr::App(g, _) = &e else { panic!("{e:?}") };
    assert!(matches!(&**g, Expr::Field(r, n, _) if n.text == "g" && matches!(**r, Expr::App(..))));
    // Chains.
    let e = expression("f().x.y").unwrap();
    assert!(matches!(&e, Expr::Field(r, _, _) if matches!(**r, Expr::Field(..))));
    let e = expression("p.f().x").unwrap();
    assert!(matches!(&e, Expr::Field(r, _, _) if matches!(**r, Expr::App(..))));
    // A space keeps ordinary application: `f ().x` is `f (().x)`.
    assert_eq!(shape("f ().x"), "app(false)");
    // Without a following `.name`, `f()` is still one atom: `g f()` is
    // `g (f())`, while `g f ()` is `g f ()`.
    let e = expression("g f()").unwrap();
    assert!(matches!(&e, Expr::App(g, a)
        if matches!(**g, Expr::Var(_)) && matches!(**a, Expr::App(..))));
    let e = expression("g f ()").unwrap();
    assert!(matches!(&e, Expr::App(f, u)
        if matches!(**f, Expr::App(..)) && matches!(**u, Expr::Unit(..))));
    let e = expression("parseTurns IO.readAllLines()").unwrap();
    assert!(matches!(&e, Expr::App(_, a) if matches!(**a, Expr::App(..))));
    // `()` alone and `f ()` are unchanged.
    assert!(matches!(expression("()").unwrap(), Expr::Unit(..)));
    assert!(matches!(expression("f ()").unwrap(), Expr::App(..)));
}

/// Named construction (docs/proposals/variant-fields.md §4.5): braces
/// right after a constructor at the head of an application name its
/// fields; `C ({ … })` is a record argument.
#[test]
fn constructor_field_expressions() {
    let Expr::CtorFields { ctor, fields, .. } =
        &rhs("def f : S := Shape.Circle { id = \"a\", ref }\n")
    else {
        panic!("expected named construction");
    };
    assert_eq!(ctor.text, "Shape.Circle");
    assert_eq!(fields.len(), 2);
    assert!(matches!(&fields[1].1, Expr::Var(n) if n.text == "ref"));
    let Expr::App(head, arg) = &rhs("def f : S := W ({ name = n })\n") else {
        panic!("expected an application");
    };
    assert!(matches!(&**head, Expr::Var(n) if n.text == "W"));
    assert!(matches!(&**arg, Expr::Record { base: None, .. }));
    // After an operator, in brackets and lists, after a field's `=`, and
    // with a field access after the braces.
    assert!(matches!(
        &rhs("def f : Bool := x == C { }\n"),
        Expr::Binary(_, _, rhs) if matches!(&**rhs, Expr::CtorFields { .. })
    ));
    assert!(matches!(
        &rhs("def f : T := (C { a = 1 }).a\n"),
        Expr::Field(e, _, _) if matches!(&**e, Expr::CtorFields { .. })
    ));
    assert!(matches!(
        &rhs("def f : T := C { a = 1 }.a\n"),
        Expr::Field(e, _, _) if matches!(&**e, Expr::CtorFields { .. })
    ));
    parse("def f : T := [C { a = D { b } }, g (C { a })]\n");
    // A lower-case name keeps a record argument: `f { a = 1 }`.
    assert!(matches!(
        &rhs("def f : T := g { a = 1 }\n"),
        Expr::App(_, arg) if matches!(&**arg, Expr::Record { .. })
    ));
}

#[test]
fn braces_after_a_constructor_expression_are_left_to_the_elaborator() {
    // Whether they name the constructor's fields or are a record argument
    // depends on how it is declared, so the parser keeps a literal as is,
    // at the head and as an argument, with the arguments after it.
    let Expr::App(head, _) = &rhs("def f : L := Cons { head = 1 } rest\n") else {
        panic!("expected an application");
    };
    assert!(matches!(
        &**head,
        Expr::CtorFields {
            argument: false,
            ..
        }
    ));
    let Expr::App(_, arg) = &rhs("def f : L := g Cons { head = 1 }\n") else {
        panic!("expected an application");
    };
    assert!(matches!(&**arg, Expr::CtorFields { argument: true, .. }));
    // An update is never a construction: the constructor, then the record.
    let Expr::App(head, arg) = &rhs("def f : L := Some { r | a = 1 }\n") else {
        panic!("expected an application");
    };
    assert!(matches!(&**head, Expr::Var(n) if n.text == "Some"));
    assert!(matches!(&**arg, Expr::Record { base: Some(_), .. }));
}

/// `?` is a goal: an atom, so an argument too, and never a hole.
#[test]
fn a_question_mark_is_a_goal() {
    let module = parse("def x : Nat := f ? (?, _)\n");
    let Decl::Equation { rhs, .. } = &module.decls[1] else {
        panic!("expected an equation");
    };
    let Some(Expr::App(f, pair)) = rhs else {
        panic!("expected an application, got {rhs:?}");
    };
    let Expr::Tuple(first, second, _) = pair.as_ref() else {
        panic!("expected a tuple, got {pair:?}");
    };
    assert!(matches!(first.as_ref(), Expr::Goal(_)));
    assert!(matches!(second.as_ref(), Expr::Hole(_)));
    let Expr::App(_, goal) = f.as_ref() else {
        panic!("expected an application, got {f:?}");
    };
    assert!(matches!(goal.as_ref(), Expr::Goal(_)));
}

#[test]
fn square_brackets_are_implicit_binders_named_arguments_or_lists() {
    let module = parse("def f : [a : Type] -> List a -> Nat\ndef x : Nat := g [a := Nat] [1] _\n");
    let Decl::Signature { ty, .. } = &module.decls[0] else {
        panic!("expected a signature");
    };
    assert!(matches!(ty, Expr::Pi { implicit: true, .. }));
    let Decl::Equation { rhs, .. } = &module.decls[2] else {
        panic!("expected an equation");
    };
    let Some(Expr::App(f, hole)) = rhs else {
        panic!("expected an application, got {rhs:?}");
    };
    assert!(matches!(hole.as_ref(), Expr::Hole(_)));
    let Expr::App(f, list) = f.as_ref() else {
        panic!("expected an application, got {f:?}");
    };
    assert!(matches!(list.as_ref(), Expr::List(..)));
    let Expr::App(_, named) = f.as_ref() else {
        panic!("expected an application, got {f:?}");
    };
    assert!(matches!(named.as_ref(), Expr::NamedArg(..)));
}

#[test]
fn colon_spacing_does_not_change_the_parse() {
    let shape = |text| crate::equivalence::parse_shape(text).expect(text);
    assert_eq!(
        shape("def f (n : Nat) : Nat := n\n"),
        shape("def f (n: Nat): Nat := n\n")
    );
    assert_eq!(
        shape("def f (n : Nat) : Nat := n\n"),
        shape("def f (n:Nat):Nat := n\n")
    );
}

#[test]
fn parenthesised_names_without_an_arrow_are_annotations() {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", "(x : Nat)");
    assert!(matches!(
        parse_expression(file, "(x : Nat)"),
        Ok(Expr::Ann(..))
    ));
}

#[test]
fn parses_tuples() {
    // Components nest to the right; `()` and `(e)` are unchanged.
    let e = rhs("def f : Nat := (1, 2, 3)\n");
    let Expr::Tuple(a, rest, _) = &e else {
        panic!("{e:?}")
    };
    assert!(matches!(**a, Expr::Num(..)));
    assert!(matches!(**rest, Expr::Tuple(..)));
    let e = rhs("def f : Nat := ((1, 2), 3)\n");
    assert!(matches!(&e, Expr::Tuple(a, b, _)
        if matches!(**a, Expr::Tuple(..)) && matches!(**b, Expr::Num(..))));
    assert!(matches!(rhs("def f : Nat := ()\n"), Expr::Unit(_)));
    assert!(matches!(rhs("def f : Nat := (1)\n"), Expr::Num(..)));
    assert!(matches!(rhs("def f : Nat := (1 : Nat)\n"), Expr::Ann(..)));
    // A tuple is a function's domain, and `(x : A)` is still a binder.
    assert!(matches!(&rhs("def f : Nat := (A, B) -> C\n"),
        Expr::Arrow(d, _) if matches!(**d, Expr::Tuple(..))));
    assert!(matches!(
        rhs("def f : Nat := (x : A) -> B\n"),
        Expr::Pi { .. }
    ));
    // The tuple's span covers its brackets.
    let e = rhs("def f : Nat := (1, 2, 3)\n");
    assert_eq!((e.span().start, e.span().end), (15, 24));
}

#[test]
fn an_interpolated_text_spans_its_quotes() {
    for literal in [
        "\"${a}\"",
        "\"${a} and ${b}\"",
        "\"x ${a}\"",
        "\"${a} x\"",
        "\"x ${a} y\"",
        "\"${\"${a}\"}\"",
    ] {
        let source = format!("def f : Text := {literal}\n");
        let e = rhs(&source);
        assert!(matches!(e, Expr::Interpolated(..)), "{literal}: {e:?}");
        let span = e.span();
        assert_eq!(
            &source[span.start as usize..span.end as usize],
            literal,
            "{literal}"
        );
    }
}

/// A field access, with its id, is far from the largest expression, so the
/// id costs no memory (docs/proposals/syntax-node-ids.md §7). A change here
/// is a change to every expression's size.
#[test]
fn an_expression_is_112_bytes() {
    assert_eq!(std::mem::size_of::<Expr>(), 112);
}
