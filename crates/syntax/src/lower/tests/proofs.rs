use super::*;

#[test]
fn calc_steps_are_lines_starting_with_an_underscore() {
    let text = "def f (a: Nat): a = a :=\n  calc a\n    _ = a := byComputing\n    _ <= a\n    _ < a := Nat.f _\n";
    let expr = rhs(text);
    let Expr::Calc { steps, .. } = &expr else {
        panic!("expected a calc");
    };
    let shape: Vec<(BinOp, bool)> = steps.iter().map(|s| (s.rel, s.proof.is_some())).collect();
    assert_eq!(
        shape,
        vec![(BinOp::Eq, true), (BinOp::Le, false), (BinOp::Lt, true)]
    );
    // The `_` argument stays an argument when it isn't at the start of a line.
    assert!(matches!(&steps[2].proof, Some(Expr::App(..))));
}

#[test]
fn arithmetic_takes_an_optional_list_of_facts() {
    let expr = rhs("theorem t (a: Nat): a <= a := arithmetic\n");
    assert!(
        matches!(&expr, Expr::Omega { facts, .. } if facts.is_empty()),
        "{expr:?}"
    );
    let expr = rhs("theorem t (a: Nat): a <= a := arithmetic [h a, Nat.leRefl a]\n");
    let Expr::Omega { facts, .. } = &expr else {
        panic!("expected arithmetic, got {expr:?}");
    };
    assert_eq!(facts.len(), 2);
    assert!(facts.iter().all(|f| matches!(f, Expr::App(..))));
    // As an argument, and as a calc step's proof.
    let expr = rhs("theorem t (a: Nat): a <= a := f arithmetic x\n");
    assert!(matches!(&expr, Expr::App(..)));
    let expr = rhs("def f (a: Nat): a <= a :=\n  calc a\n    _ <= a := arithmetic\n");
    let Expr::Calc { steps, .. } = &expr else {
        panic!("expected a calc");
    };
    assert!(matches!(&steps[0].proof, Some(Expr::Omega { .. })));
}

#[test]
fn algebra_takes_an_optional_list_of_hypotheses() {
    let expr = rhs("theorem t (a: Nat): a + 1 = 1 + a := algebra\n");
    assert!(
        matches!(&expr, Expr::Ring { facts, .. } if facts.is_empty()),
        "{expr:?}"
    );
    let expr = rhs("theorem t (a: Nat): a = a := algebra [h a, g]\n");
    let Expr::Ring { facts, .. } = &expr else {
        panic!("expected algebra, got {expr:?}");
    };
    assert_eq!(facts.len(), 2);
    // As an argument, and as a calc step's proof.
    let expr = rhs("theorem t (a: Nat): a = a := f algebra x\n");
    assert!(matches!(&expr, Expr::App(..)));
    let expr = rhs("def f (a: Nat): a = a :=\n  calc a\n    _ = a := algebra\n");
    let Expr::Calc { steps, .. } = &expr else {
        panic!("expected a calc");
    };
    assert!(matches!(&steps[0].proof, Some(Expr::Ring { .. })));
}

#[test]
fn exists_takes_a_lambda() {
    let exists = |e: &Expr| -> Option<Expr> {
        let Expr::App(f, lam) = e else { return None };
        let Expr::App(head, _) = f.as_ref() else {
            return None;
        };
        matches!(head.as_ref(), Expr::Var(n) if n.text == "Std.Exists")
            .then(|| lam.as_ref().clone())
    };
    let lam = exists(&expr("exists (n: Nat) => n * n = 49")).expect("an exists");
    assert!(matches!(lam, Expr::TypedLam(..)));
    // Several parameters nest, the body's own lambda doesn't.
    let lam = exists(&expr("exists a b => f (x => x)")).expect("an exists");
    let Expr::Lam(names, body, _) = &lam else {
        panic!("expected a lambda");
    };
    assert_eq!(names.len(), 1);
    let inner = exists(body).expect("a second exists");
    let Expr::Lam(_, body, _) = &inner else {
        panic!("expected a lambda");
    };
    assert!(matches!(body.as_ref(), Expr::App(..)));
    // After `&&`, `||`, `<->` and `->` it takes the rest.
    assert!(matches!(
        expr("p && exists k => q k"),
        Expr::Binary(BinOp::And, ..)
    ));
    assert!(parse_module_text("def t: Prop := p <-> exists k => q k\n").is_ok());
    assert!(parse_module_text("def t: Prop := p -> ∃ (k: Nat) => q k\n").is_ok());
    assert!(parse_errors("def t: Prop := exists 3\n").contains("after `exists`"));
    // After a `.` it's a name: `x.exists` and `Foo.exists` still parse.
    assert!(parse_module_text("def t: Bool := (Some 3).exists (v => v > 2)\n").is_ok());
    assert!(parse_module_text("def t: Bool := Foo.exists (v => v > 2) (Some 3)\n").is_ok());
}

#[test]
fn forall_is_a_function_type() {
    // A group is a function type per name (D3679); the body takes the rest.
    let e = expr("forall (a b: Nat) [c: Nat] => a + b = c -> p");
    let Expr::Pi {
        implicit: false,
        cod,
        ..
    } = &e
    else {
        panic!("expected a function type");
    };
    let Expr::Pi {
        implicit: false,
        cod,
        ..
    } = cod.as_ref()
    else {
        panic!("expected a function type for the group's second name");
    };
    let Expr::Pi {
        implicit: true,
        cod,
        ..
    } = cod.as_ref()
    else {
        panic!("expected an implicit function type");
    };
    assert!(matches!(cod.as_ref(), Expr::Arrow(..)));
    // `∀` is the same token (three bytes, so the spaces keep the
    // spans the same), and a bare name's type is a hole.
    assert_eq!(
        format!("{:?}", expr("∀    (n: Nat) => n = n")),
        format!("{:?}", expr("forall (n: Nat) => n = n"))
    );
    let e = expr("∀ n => n = n");
    let Expr::Pi { dom, .. } = &e else {
        panic!("expected a function type");
    };
    assert!(matches!(dom.as_ref(), Expr::Hole(_)));
    assert!(matches!(
        expr("p && ∀ k => q k"),
        Expr::Binary(BinOp::And, ..)
    ));
    assert!(parse_module_text("def t: Prop := p <-> forall k => q k\n").is_ok());
    assert!(parse_module_text("def t: Prop := p -> ∀ (k: Nat) => q k\n").is_ok());
    // Lean's and Rocq's comma, a pattern, a missing parameter, a default.
    let comma = parse_errors("def t: Prop := ∀ x, x = x\n");
    assert!(comma.contains("not `,`"), "{comma}");
    assert!(parse_errors("def t: Prop := ∀ (a, b) => a = b\n").contains("a parameter after"));
    assert!(parse_errors("def t: Prop := ∀ (x: Nat) (a, b) => p\n").contains("`=>` after"));
    assert!(parse_errors("def t: Prop := forall => p\n").contains("a parameter after"));
    assert!(parse_errors("def t: Prop := ∀ (x: Nat := 1) => x = x\n").contains("default"));
    assert!(parse_module_text("def t: Bool := xs.forall (v => v > 2)\n").is_ok());
}

#[test]
fn membership_in_a_rewrite_rule_needs_brackets() {
    // A bare `in` still ends a rule, so it gets the old spelling's error.
    let error = parse_errors("def f (a: Nat): a = a :=\n  rewrite h x in xs then t\n");
    assert!(error.contains("write `then`"), "{error}");
    assert!(parse_module_text("def f (a: Nat): a = a :=\n  rewrite h (x in xs) then t\n").is_ok());
    // As the body, after `then`, a membership test needs no brackets.
    let e = rhs("def f (a: Nat): a = a :=\n  rewrite h then x in xs\n");
    let Expr::Rewrite { body, .. } = &e else {
        panic!("expected a rewrite");
    };
    assert!(matches!(
        body.as_deref(),
        Some(Expr::Binary(BinOp::In(_), ..))
    ));
}

#[test]
fn the_old_in_after_rewrite_and_cases_names_then() {
    for text in [
        "def f (a: Nat): a = a :=\n  rewrite h in t\n",
        "def f (a: Nat): a = a :=\n  rewrite h at k in t\n",
        "def f (a: Nat): a = a :=\n  rewrite h\n  in t\n",
        "def f (a: Nat): a = a :=\n  cases in t\n",
        "def f (a: Nat): a = a := g cases in t\n",
    ] {
        let error = parse_errors(text);
        assert!(error.contains("write `then`, not `in`"), "{text}: {error}");
    }
    let e = rhs("def f (a: Nat): a = a :=\n  cases then t\n");
    let Expr::Cases { body, .. } = &e else {
        panic!("expected cases");
    };
    assert!(body.is_some());
    let e = rhs("def f (a: Nat): a = a :=\n  rewrite h\n  then t\n");
    let Expr::Rewrite { body, .. } = &e else {
        panic!("expected a rewrite");
    };
    assert!(body.is_some());
}

#[test]
fn cases_takes_the_values_to_split_on_its_own_line() {
    let targets = |e: &Expr| match e {
        Expr::Cases { targets, body, .. } => (
            targets.iter().map(|t| t.text.clone()).collect::<Vec<_>>(),
            body.is_some(),
        ),
        other => panic!("expected cases, got {other:?}"),
    };
    let e = rhs("def f (a: Nat): a = a :=\n  cases x, y then t\n");
    assert_eq!(targets(&e), (vec!["x".to_string(), "y".to_string()], true));
    let e = rhs("def f (a: Nat): a = a := cases x\n");
    assert_eq!(targets(&e), (vec!["x".to_string()], false));
    let e = rhs("def f (a: Nat): a = a := (cases x then t)\n");
    assert_eq!(targets(&e), (vec!["x".to_string()], true));
    // As an argument, `cases` is still a whole term, and a name after it
    // the next argument.
    let e = rhs("def f (a: Nat): a = a := g cases none\n");
    let Expr::App(head, last) = &e else {
        panic!("expected a call, got {e:?}");
    };
    assert!(matches!(&**last, Expr::Var(..)), "{last:?}");
    assert!(matches!(&**head, Expr::App(_, c) if targets(c) == (vec![], false)));
    // A name followed by `=`, `=>` or `:` starts the next field or item.
    for text in [
        "def f: P := { left = a => cases a, right = b => cases b }\n",
        "def f: P := (a => cases a, b => cases b)\n",
    ] {
        assert!(
            parse_module_text(text).is_ok(),
            "{text}: {}",
            parse_errors(text)
        );
    }
    let e = rhs("def f (a: Nat): a = a :=\n  cases\n");
    assert_eq!(targets(&e), (vec![], false));
}

#[test]
fn arithmetic_and_algebra_are_keywords_and_the_old_words_are_names() {
    assert!(parse_module_text("def arithmetic: Nat := 1\n").is_err());
    assert!(parse_module_text("def algebra: Nat := 1\n").is_err());
    assert!(parse_module_text("def omega: Nat := 1\n").is_ok());
    assert!(parse_module_text("def ring: Nat := 1\n").is_ok());
}

#[test]
fn rewrite_takes_rules_left_to_right_and_an_optional_body() {
    let text = "def f (a: Nat): a = a :=\n  rewrite p, <- q x, r (y in ys) then Nat.f _\n";
    let expr = rhs(text);
    let Expr::Rewrite { rules, body, .. } = &expr else {
        panic!("expected a rewrite");
    };
    let shape: Vec<bool> = rules.iter().map(|r| r.reverse).collect();
    assert_eq!(shape, vec![false, true, false]);
    assert!(matches!(&rules[1].proof, Expr::App(..)));
    // A bracketed membership is an ordinary argument; the bare `in`
    // ended the rule.
    let Expr::App(_, arg) = &rules[2].proof else {
        panic!("expected an application");
    };
    assert!(matches!(&**arg, Expr::Binary(BinOp::In(_), ..)));
    assert!(matches!(body.as_deref(), Some(Expr::App(..))));
    // No `in`: the body is `byComputing`, left to the elaborator.
    let text = "def f (a: Nat): a = a :=\n  rewrite p x\n";
    let expr = rhs(text);
    let Expr::Rewrite { rules, body, .. } = &expr else {
        panic!("expected a rewrite");
    };
    assert_eq!(rules.len(), 1);
    assert!(body.is_none());
}

#[test]
fn rewrite_repeatedly_takes_a_bracketed_list_of_rules() {
    let text = "def f (a: Nat): a = a :=\n  rewrite repeatedly [p, <- q x,\n    r] then t\n";
    let Expr::Rewrite {
        rules,
        body,
        repeatedly,
        ..
    } = &rhs(text)
    else {
        panic!("expected a rewrite");
    };
    assert!(repeatedly.is_some());
    let shape: Vec<bool> = rules.iter().map(|r| r.reverse).collect();
    assert_eq!(shape, vec![false, true, false]);
    assert!(body.is_some());
    // Without a `[`, `repeatedly` is a rule like any other name.
    let Expr::Rewrite {
        rules, repeatedly, ..
    } = &rhs("def f (a: Nat): a = a :=\n  rewrite repeatedly then t\n")
    else {
        panic!("expected a rewrite");
    };
    assert!(repeatedly.is_none());
    assert_eq!(rules.len(), 1);
    assert!(!parse_errors("def f (a: Nat): a = a :=\n  rewrite repeatedly []\n").is_empty());
    // `at h` rewrites a hypothesis (SW-3642).
    assert!(matches!(
        rhs("def f (a: Nat): a = a :=\n  rewrite repeatedly [p] at h\n"),
        Expr::Rewrite {
            repeatedly: Some(_),
            ..
        }
    ));
}

#[test]
fn rewrite_in_can_start_its_own_line() {
    let body = |text: &str| {
        let expr = rhs(text);
        let Expr::Rewrite { rules, body, .. } = &expr else {
            panic!("expected a rewrite");
        };
        (rules.len(), body.clone())
    };
    for text in [
        "def f (a: Nat): a = a :=\n  rewrite p,\n    q x\n  then t\n",
        "def f (a: Nat): a = a :=\n  rewrite p, q x\n  then t\n",
        "def f (a: Nat): a = a :=\n  rewrite p, q x\n    then t\n",
        "def f (a: Nat): a = a :=\n  rewrite p at h\n  then t\n",
    ] {
        let (rules, body) = body(text);
        assert!(rules >= 1, "{text}");
        assert!(
            matches!(body.as_deref(), Some(Expr::Var(n)) if n.text == "t"),
            "{text}"
        );
    }
    // Left of the `rewrite`, an `in` isn't its.
    assert!(parse_module_text("def f (a: Nat): a = a :=\n  g\n    rewrite p\n  in t\n").is_err());
}

#[test]
fn rewrite_at_takes_a_target_before_the_body() {
    let parts = |text: &str| {
        let expr = rhs(text);
        let Expr::Rewrite {
            rules,
            target,
            body,
            ..
        } = &expr
        else {
            panic!("expected a rewrite");
        };
        (rules.clone(), target.clone(), body.clone())
    };
    // `at` ends the rules, `in` ends the target.
    let (rules, target, body) =
        parts("def f (a: Nat): a = a :=\n  rewrite p, <- q x at h y then t\n");
    assert_eq!(rules.len(), 2);
    assert!(matches!(&rules[1].proof, Expr::App(..)));
    assert!(matches!(target.as_deref(), Some(Expr::App(..))));
    assert!(matches!(body.as_deref(), Some(Expr::Var(n)) if n.text == "t"));
    // Without `in`, the rewritten target is the value.
    let (_, target, body) = parts("def f (a: Nat): a = a :=\n  rewrite p at h\n");
    assert!(matches!(target.as_deref(), Some(Expr::Var(n)) if n.text == "h"));
    assert!(body.is_none());
    // An `at` that starts a rule is a name, so is a bracketed one, and so
    // is a field `.at`.
    let (rules, target, body) =
        parts("def f (a: Nat): a = a :=\n  rewrite at b (at) r.at at at then at\n");
    let Expr::App(f, arg) = &rules[0].proof else {
        panic!("expected an application");
    };
    assert!(matches!(&**arg, Expr::Field(_, n, _) if n.text == "at"));
    assert!(matches!(&**f, Expr::App(_, a) if matches!(&**a, Expr::Var(n) if n.text == "at")));
    assert!(matches!(target.as_deref(), Some(Expr::Var(n)) if n.text == "at"));
    assert!(matches!(body.as_deref(), Some(Expr::Var(n)) if n.text == "at"));
    // `at` is an ordinary name elsewhere.
    assert!(parse_module_text("def f (at: Nat): Nat := at\n").is_ok());
    let (_, target, _) = parts("def f (a: Nat): a = a :=\n  rewrite p then at\n");
    assert!(target.is_none());
}

#[test]
fn rewrite_and_in_are_keywords() {
    assert!(parse_module_text("def rewrite: Nat := 1\n").is_err());
    // `in` is reserved since it became membership (D1201).
    assert!(parse_module_text("def f (in: Nat): Nat := in\n").is_err());
    // `<` then `-` apart is a comparison, not an arrow.
    assert!(
        parse_module_text("def f (a: Nat): a = a :=\n  rewrite < - p then byComputing\n").is_err()
    );
}

#[test]
fn calc_expressions_may_use_logic_operators() {
    let text = "def f (a: Bool) (b: Bool): a || b = b || a :=\n  calc a || b\n    _ = b || a := g a b\n    _ = b || a && a\n";
    let Expr::Calc { ref steps, .. } = rhs(text) else {
        panic!("expected a calc");
    };
    assert_eq!(steps.len(), 2);
}

#[test]
fn calc_expressions_may_use_pipes() {
    // `|>` binds tighter than the step's relation: `_ = (xs |> List.sum)`.
    let text = "def f (xs: List Nat): xs.sum = xs.sum :=\n  calc xs |> List.sum\n    _ = xs |> List.sum := h\n    _ = xs |> .sum\n";
    let Expr::Calc {
        ref first,
        ref steps,
        ..
    } = rhs(text)
    else {
        panic!("expected a calc");
    };
    assert!(matches!(**first, Expr::Pipe(..)));
    assert_eq!(steps.len(), 2);
    assert!(matches!(steps[0].rhs, Expr::Pipe(..)));
    assert!(steps[0].proof.is_some());
    assert!(matches!(steps[1].rhs, Expr::Field(..)));
}

#[test]
fn a_keyword_where_a_name_goes_is_called_a_keyword() {
    for text in [
        "def f (then: Nat): Nat := 0\n",
        "def f: Nat := (test => test) 0\n",
        "def f: Nat :=\n  let with := 0\n  0\n",
        "def f (n: Nat): Nat := match n with\n  | Succ return => 0\n  | Zero => 0\n",
    ] {
        let message = first_error(text);
        assert!(message.contains("found the keyword"), "{text}: {message}");
    }
    // `∈` is `in`, but isn't written as a word.
    let message = first_error("def f (∈: Nat): Nat := 0\n");
    assert!(!message.contains("keyword"), "{message}");
}

#[test]
fn calc_needs_steps_on_their_own_lines() {
    assert!(parse_module_text("def f (a: Nat): a = a := calc a = a := byComputing\n").is_err());
    assert!(parse_module_text("def f (a: Nat): a = a :=\n  calc a\n").is_err());
    assert!(
        parse_module_text("def f (a: Nat): a = a :=\n  calc a\n    _ = a\n   _ = a\n").is_err()
    );
}
