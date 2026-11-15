use super::*;

#[test]
fn match_induct_names_a_case_and_its_binders() {
    let text = "match induct (f k xs) with\n  | eq1 => a\n  | eq2Step x _ ih => b\n";
    let e = expression(text).unwrap();
    let Expr::Induct { call, alts, .. } = &e else {
        panic!("expected a `match induct`");
    };
    assert!(matches!(**call, Expr::App(..)));
    let shown: Vec<(String, Vec<String>)> = alts
        .iter()
        .map(|a| {
            let bound = a.binders.iter().map(|b| b.text.clone());
            (a.case.text.clone(), bound.collect())
        })
        .collect();
    assert_eq!(shown[0], ("eq1".to_string(), vec![]));
    assert_eq!(
        shown[1],
        (
            "eq2Step".to_string(),
            vec!["x".to_string(), "_".to_string(), "ih".to_string()]
        )
    );
}

#[test]
fn handler_and_reify_return_clauses_accept_a_wildcard() {
    let e = rhs(
        "def f (t : () -> {Fail} a) : P := match reify t with\n  | return _ => rfl\n  | Fail.stop msg, k => k\n",
    );
    let Expr::Reify { clauses, .. } = &e else {
        panic!("expected a `match reify`, got {e:?}")
    };
    assert!(
        matches!(&clauses[0], Clause::Return { var, .. } if var.text == "_"),
        "{clauses:?}"
    );

    let e = rhs(
        "def f (p : Nat) : Nat :=\n  handle p () with\n    | return _ => 0\n    | get (), k => k 0\n",
    );
    let Expr::Handle { clauses, .. } = &e else {
        panic!("expected a `handle`, got {e:?}")
    };
    assert!(
        matches!(&clauses[0], Clause::Return { var, .. } if var.text == "_"),
        "{clauses:?}"
    );
}

#[test]
fn induct_is_a_name_except_after_match() {
    let e = expression("match induct with\n  | x => x\n").unwrap();
    assert!(matches!(e, Expr::Match { .. }));
    let e = expression("induct x").unwrap();
    assert!(matches!(e, Expr::App(..)));
    assert!(expression("match induct x, y with\n  | eq1 => a\n").is_err());
}

#[test]
fn parses_match_expressions() {
    // Alternatives on their own lines.
    let e = rhs(
        "def f (xs : List Nat) : Nat :=\n  match xs with\n    | Nil => 0\n    | Cons x Nil => x\n    | _ => 2\n",
    );
    let (s, alts) = match_parts(&e);
    assert_eq!(s.len(), 1);
    assert!(s[0].name.is_none());
    assert_eq!(alts.len(), 3);
    assert!(matches!(&alts[1].patterns[0], Pattern::Ctor(_, args, _) if args.len() == 2));
    assert!(matches!(alts[2].patterns[0], Pattern::Wildcard(_)));

    // All on one line.
    let e = rhs("def f (xs : List Nat) : Nat := match xs with | Nil => 0 | Cons x _ => x\n");
    let (_, alts) = match_parts(&e);
    assert_eq!(alts.len(), 2);
    assert!(matches!(&alts[1].patterns[0], Pattern::Ctor(_, args, _) if args.len() == 2));

    // Two scrutinees.
    let e = rhs(
        "def f (a : Nat) (b : Nat) : Nat := match a, b with | Zero, _ => 0 | Succ m, Zero => m | _, _ => 1\n",
    );
    let (s, alts) = match_parts(&e);
    assert_eq!(s.len(), 2);
    assert!(alts.iter().all(|a| a.patterns.len() == 2));

    // A named equation.
    let e =
        rhs("def f (xs : List Nat) : Nat := match h : length xs with | Zero => 0 | Succ k => k\n");
    let (s, _) = match_parts(&e);
    assert_eq!(s[0].name.as_ref().unwrap().text, "h");
    assert!(matches!(s[0].expr, Expr::App(..)));

    // Other pattern forms.
    let e = rhs(
        "def f (p : Nat) : Nat := match p with | (a, b) => a | { name = n } => n | () => 0 | 0 => 1\n",
    );
    let (_, alts) = match_parts(&e);
    assert!(matches!(alts[0].patterns[0], Pattern::Tuple(..)));
    assert!(matches!(alts[1].patterns[0], Pattern::Record { .. }));
    assert!(matches!(alts[2].patterns[0], Pattern::Absurd(_)));
    assert!(matches!(alts[3].patterns[0], Pattern::Num(..)));
    assert!(alts.iter().all(|a| a.body.is_some()));

    // An absurd alternative: `()` and no body, as in an equation.
    let e = rhs(
        "def f (m : Move) (h : P m) : Nat :=\n  match m, h with\n    | Rock, _ => 0\n    | Paper, ()\n    | Scissors, () => 1\n",
    );
    let (_, alts) = match_parts(&e);
    assert!(alts[0].body.is_some());
    assert!(alts[1].body.is_none());
    assert!(matches!(alts[1].patterns[1], Pattern::Absurd(_)));
    assert!(alts[2].body.is_some());

    // As an operand.
    let e = rhs("def f (n : Nat) : Nat := 1 + match n with | Zero => 0 | Succ k => k\n");
    let Expr::Binary(_, _, r) = &e else {
        panic!("{e:?}")
    };
    assert_eq!(match_parts(r).1.len(), 2);
}

#[test]
fn nested_match_alternatives_line_up_by_column() {
    let e = rhs(
        "def f (a : Nat) (b : Nat) : Nat :=\n  match a with\n    | Zero =>\n      match b with\n        | Zero => 1\n        | Succ _ => 2\n    | Succ _ => 3\n",
    );
    let (_, outer) = match_parts(&e);
    assert_eq!(outer.len(), 2);
    assert_eq!(match_parts(outer[0].body.as_ref().unwrap()).1.len(), 2);
    assert!(is_num(outer[1].body.as_ref().unwrap(), 3));
}

#[test]
fn rejects_malformed_matches() {
    let fails = |text: &str| rhs_of(text).is_err();
    assert!(
        fails("def f (xs : List Nat) : Nat := match xs with\n"),
        "no alternatives"
    );
    assert!(
        fails("def f (xs : List Nat) : Nat := match xs with | Nil, _ => 0\n"),
        "too many patterns"
    );
    assert!(
        fails("def f (a : Nat) (b : Nat) : Nat := match a, b with | Nil => 0\n"),
        "too few patterns"
    );
    let message = rhs_of("def f (xs : List Nat) : Nat := match xs with | Nil, _ => 0\n")
        .unwrap_err()
        .message;
    assert!(
        message.contains("has 2 patterns, but the `match` has 1 scrutinee"),
        "{message}"
    );
}

#[test]
fn clause_lambdas_are_lambdas_over_a_match() {
    let e = bracketed_arg("match | A => 1 | B => 2");
    let (alts, kind) = clause_parts(&e);
    assert_eq!((alts.len(), kind), (2, MatchKind::Clause));

    // Two parameters: two patterns in each arm.
    let e = bracketed_arg("match | 0, y => y | x, _ => x");
    let Expr::Lam(names, ..) = &e else {
        panic!("{e:?}")
    };
    assert_eq!(names.len(), 2);

    // `some` and `matches` are keywords only before `|`.
    let e = bracketed_arg("match some | A x => x");
    let (alts, kind) = clause_parts(&e);
    assert_eq!((alts.len(), kind), (2, MatchKind::ClauseSome));
    let e = rhs("def f: T := match some with | 0 => 1 | _ => 2\n");
    assert_eq!(match_parts(&e).1.len(), 2);
    let e = bracketed_arg("matches | A | B");
    let (alts, kind) = clause_parts(&e);
    assert_eq!((alts.len(), kind), (2, MatchKind::ClauseMatches));
    assert_eq!(alts[0].patterns.len(), 1);
    assert!(matches!(alts[0].patterns[0], Pattern::Or(..)));
    assert!(matches!(rhs("def f: T := matches + 1\n"), Expr::Binary(..)));
}

#[test]
fn guards_follow_the_patterns_and_end_at_the_arrow() {
    // `flag => e` is not a lambda inside a guard.
    let e = bracketed_arg("match some | x if flag => x");
    let (alts, _) = clause_parts(&e);
    let guard = alts[0].guard.as_ref().expect("a guard");
    assert!(guard.binder.is_none());
    assert!(matches!(&guard.cond, Expr::Var(n) if n.text == "flag"));
    assert!(alts[1].guard.is_none());

    // A pipe, a comparison, a named fact.
    let e = bracketed_arg("match some | (a, b) if xs |> f => a");
    let (alts, _) = clause_parts(&e);
    assert!(matches!(
        alts[0].guard.as_ref().unwrap().cond,
        Expr::Pipe(..)
    ));
    let e = bracketed_arg("match some | (a, b) if h: a < b => a");
    let (alts, _) = clause_parts(&e);
    assert_eq!(
        alts[0]
            .guard
            .as_ref()
            .unwrap()
            .binder
            .as_ref()
            .unwrap()
            .text,
        "h"
    );

    // A lambda in brackets inside the guard is still a lambda.
    let e = bracketed_arg("match some | xs if xs.any (x => x > 0) => xs");
    let (alts, _) = clause_parts(&e);
    assert!(alts[0].guard.is_some());

    // One guard over an or-pattern; none on the `matches` result.
    let e = bracketed_arg("matches | 1 | 2 if strict");
    let (alts, kind) = clause_parts(&e);
    assert_eq!(kind, MatchKind::ClauseMatches);
    assert!(matches!(alts[0].patterns[0], Pattern::Or(..)));
    assert!(alts[0].guard.is_some());

    // A constructor's arguments stop at `if`, in a `match` on one line.
    let e = rhs("def f: T := match n with | Some x if x > 0 => x | _ => 0\n");
    let (_, alts) = match_parts(&e);
    assert!(alts[0].guard.is_some() && alts[1].guard.is_none());

    // A definition's arm.
    let module = parse("def f: Nat → Nat\n  | n if n > 2 => n\n  | _ => 0\n");
    let guards: Vec<bool> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Equation { guard, .. } => Some(guard.is_some()),
            _ => None,
        })
        .collect();
    assert_eq!(guards, [true, false]);
}

#[test]
fn a_definition_whose_body_is_a_clause_lambda_has_the_arms_form() {
    let module = parse("def f: Nat → Option Nat := match some | 0 => 1 | 1 => 2\n");
    let arms: Vec<_> = module
        .decls
        .iter()
        .filter(|d| matches!(d, Decl::Equation { .. }))
        .collect();
    // Two written arms, and the one for everything else.
    assert_eq!(arms.len(), 3);
    assert!(
        arms.iter()
            .all(|d| matches!(d, Decl::Equation { arm: Some(0), .. }))
    );
}

#[test]
fn clause_lambda_arms_have_the_same_number_of_patterns() {
    let message = rhs_of("def f: T := match | 0, y => y | x => x\n")
        .unwrap_err()
        .message;
    assert!(
        message.contains("has 1 pattern, but the first has 2"),
        "{message}"
    );
}

#[test]
fn a_pipe_after_a_match_pipes_the_whole_match_or_the_last_body() {
    // Left of the last alternative's body, at least at the `match` line:
    // the whole match.
    assert_eq!(
        pipe_body("  match x with\n    | 0 => a\n    | n => n\n  |> f"),
        "(|> (match x | a | n) f)"
    );
    // At the alternatives' own column it already belongs to the last body.
    assert_eq!(
        pipe_body("  match x with\n    | 0 => a\n    | n => n\n    |> f"),
        "(match x | a | (|> n f))"
    );
    // Under the last alternative's body: just that body.
    assert_eq!(
        pipe_body("  match x with\n    | 0 => a\n    | n => g n\n      |> f"),
        "(match x | a | (|> (g n) f))"
    );
    // The scrutinee can be piped.
    assert_eq!(
        pipe_body("  match x |> f with\n    | _ => a"),
        "(match (|> x f) | a)"
    );
}
