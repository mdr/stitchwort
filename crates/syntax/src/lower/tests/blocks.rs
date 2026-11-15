use super::*;

#[test]
fn a_block_is_lines_at_one_column() {
    let body = rhs("def f (u : Nat) : Nat :=\n  let n := get ()\n  put (n +\n    1)\n  n\n");
    assert_eq!(lines(&body), ["let n", "_", "result"]);
    // On one line, or with one line, it's just the expression.
    assert!(matches!(
        rhs("def f (u : Nat) : Nat := g u\n"),
        Expr::App(..)
    ));
    assert!(matches!(
        rhs("def f (u : Nat) : Nat :=\n  g\n    u\n"),
        Expr::App(..)
    ));
}

#[test]
fn a_line_ending_in_an_operator_continues() {
    let module = parse("def f : Nat ->\n  Nat ->\n  Nat\n");
    let Decl::Signature { ty, .. } = &module.decls[0] else {
        panic!()
    };
    let Expr::Arrow(_, rest) = ty else {
        panic!("{ty:?}")
    };
    assert!(matches!(rest.as_ref(), Expr::Arrow(..)), "{rest:?}");
}

#[test]
fn blocks_nest() {
    let body = rhs("def f (u : Nat) : Nat :=\n  let g := x =>\n    say x\n    x\n  g 1\n");
    assert_eq!(lines(&body), ["let g", "result"]);
    let Expr::Let { value, .. } = &body else {
        panic!()
    };
    let Expr::Lam(_, inner, _) = value.as_ref() else {
        panic!("{value:?}")
    };
    assert_eq!(lines(inner), ["_", "result"]);
}

#[test]
fn let_takes_a_type() {
    let body = rhs("def f (u : Nat) : Nat :=\n  let r : s -> {e} a := run\n  r\n");
    let Expr::Let { ty: Some(ty), .. } = &body else {
        panic!("{body:?}")
    };
    assert!(matches!(ty.as_ref(), Expr::Arrow(..)));
}

#[test]
fn rows_list_abilities_then_a_tail() {
    let row = |text: &str| {
        let module = parse(&format!("def f : Nat -> {text} Nat\n"));
        let Decl::Signature {
            ty: Expr::Arrow(_, cod),
            ..
        } = &module.decls[0]
        else {
            panic!()
        };
        let Expr::Effect(row, _) = cod.as_ref() else {
            panic!("{cod:?}")
        };
        (
            row.abilities.len(),
            row.tail.as_ref().map(|t| t.text.clone()),
        )
    };
    assert_eq!(row("{State s, Abort | e}"), (2, Some("e".into())));
    assert_eq!(row("{State s}"), (1, None));
    assert_eq!(row("{e}"), (0, Some("e".into())));
    assert_eq!(row("{| e}"), (0, Some("e".into())));
    assert_eq!(row("{}"), (0, None));
}

/// SW-1015: a statement (a result type) may start with a record literal
/// or update; the braces are a row only when a type follows them and
/// they hold no `=`.
#[test]
fn a_statement_may_start_with_a_record() {
    // The result type, under the parameters.
    let result = |text: &str| {
        let module = parse(text);
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("{:?}", module.decls[0])
        };
        let mut ty = ty;
        while let Expr::Pi { cod, .. } | Expr::Arrow(_, cod) = ty {
            ty = cod;
        }
        ty.clone()
    };
    for text in [
        "theorem t (p: P): { p | x = 3 }.x = 3 := rfl\n",
        "theorem t: { id = 2, x = 1 }.x = 1 := rfl\n",
        "theorem t: { id = 2, x = 1 } = p := rfl\n",
        "theorem t (p: P): { p | x }.x = x := rfl\n",
        "theorem t (r: R): {} = r := rfl\n",
        "def f: Nat -> { p | x = 3 }.x = 3 := rfl\n",
    ] {
        let ty = result(text);
        assert!(matches!(ty, Expr::Binary(BinOp::Eq, ..)), "{text}: {ty:?}");
    }
    // Rows: a type follows, or the braces start with an ability.
    for text in [
        "def f: {IO} Nat := 0\n",
        "def f: {e} Nat := 0\n",
        "def f: {} Nat := 0\n",
        "def f: {State s | e} (Nat, Nat) := 0\n",
    ] {
        assert!(matches!(result(text), Expr::Effect(..)), "{text}");
    }
    // A row missing its type is still reported as a row.
    let e = parse_error("def f: {IO} := 0\n");
    assert!(!e.message.contains("fields to update"), "{}", e.message);
}

/// SW-908: a parameter's type can't start with an ability row; the error
/// says what to write. A record literal there that isn't applied to a
/// type is left to the elaborator, as before.
#[test]
fn a_row_in_a_parameters_type_says_what_to_write() {
    for (text, note) in [
        ("def f (c: {} Nat): Nat := c\n", "`{} Nat` is `Nat`"),
        ("def f (c: {IO} Nat): Nat := 0\n", "`(c: () -> {IO} Nat)`"),
        (
            "def f [c: {Fail | e} a]: Nat := 0\n",
            "only as a result type",
        ),
        (
            "def f: Nat -> Nat := (c: {} Nat) => c\n",
            "`{} Nat` is `Nat`",
        ),
        ("def f: (c: {} Nat) -> Nat := c => c\n", "`{} Nat` is `Nat`"),
    ] {
        let e = parse_error(text);
        assert_eq!(
            e.message, "an ability row can't be written in a parameter's type",
            "{text}"
        );
        assert!(e.notes.iter().any(|n| n.contains(note)), "{text}: {e:?}");
    }
    parse("def f (c: {}): Nat := 0\n");
}

#[test]
fn parses_abilities_and_handlers() {
    let module = parse(
        "ability State (s : Type) where\n  get : () -> {State s} s\n  put : s -> {State s} ()\n",
    );
    let Decl::Ability { params, ops, .. } = &module.decls[0] else {
        panic!()
    };
    assert_eq!(params.len(), 1);
    let names: Vec<_> = ops.iter().map(|(n, _)| n.text.as_str()).collect();
    assert_eq!(names, ["get", "put"]);

    let body = rhs(
        "def f (p : Nat) : Nat :=\n  handle p () with\n    | return x => x\n    | get (), k => k 1\n    | put s, k =>\n      k ()\n",
    );
    let Expr::Handle { clauses, .. } = &body else {
        panic!("{body:?}")
    };
    assert!(matches!(clauses[0], Clause::Return { .. }));
    assert!(matches!(
        &clauses[1],
        Clause::Op {
            arg: Pattern::Absurd(_),
            ..
        }
    ));
    assert!(matches!(
        &clauses[2],
        Clause::Op {
            arg: Pattern::Var(_),
            ..
        }
    ));
}

#[test]
fn unit_is_a_value_and_a_pattern() {
    assert!(
        matches!(rhs("def f (u : Nat) : Nat := g ()\n"), Expr::App(_, ref a) if matches!(**a, Expr::Unit(_)))
    );
    let module = parse("def f : () -> Nat\n  | () => 1\n");
    let Decl::Equation { patterns, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(matches!(patterns[0], Pattern::Absurd(_)));
}

#[test]
fn rejects_malformed_blocks_and_handlers() {
    let fails = |text: &str| {
        let mut sources = SourceMap::new();
        let file = sources.add("test.sw", text);
        parse_module(file, text).is_err()
    };
    assert!(
        fails("def f (u : Nat) : Nat :=\n  let x := 1\n"),
        "a block ending in `let`"
    );
    assert!(
        fails("def f (p : Nat) : Nat := handle p with\n"),
        "a handler with no clauses"
    );
    assert!(
        fails("def f (p : Nat) : Nat := handle p with | get x, k -> k\n"),
        "a clause without `=>`"
    );
    assert!(fails("ability A where\n"), "an ability without operations");
    assert!(fails("def f : Nat -> {State s Nat\n"), "an unclosed row");
}

/// `(let x := e; body)` is the tree a block `let` makes (D1425, D1453).
#[test]
fn an_expression_let_is_a_block_let() {
    for text in [
        "def f (n : Nat) : Nat := (let x := n; let y := x; y)\n",
        "def f (n : Nat) : Nat := let x := n; let y := x; y\n",
        "def f (n : Nat) : Nat :=\n  (let x := n;\n    let y := x; y)\n",
        "def f (n : Nat) : Nat := if True then let x := n; let y := x; y else 0\n",
    ] {
        let e = rhs(text);
        let e = if let Expr::If { then, .. } = &e {
            then
        } else {
            &e
        };
        assert_eq!(lines(e), ["let x", "let y", "result"], "{text}");
    }
    // A pattern gives the one-alternative `match`, as in a block.
    let e = rhs("def f (p : Nat) : Nat := (let (a, b) := p; a)\n");
    assert!(matches!(
        &e,
        Expr::Match {
            kind: MatchKind::Let,
            ..
        }
    ));
    // `in` is membership, so it stays in the value.
    let e = rhs("def f (x : Nat) (xs : List Nat) : Bool := (let b := x in xs; b)\n");
    let Expr::Let { value, .. } = &e else {
        panic!("expected a `let`, got {e:?}");
    };
    assert!(!matches!(**value, Expr::Var(_)), "{value:?}");
}

#[test]
fn an_expression_let_needs_a_semicolon_and_a_body() {
    let message = |text: &str| rhs_of(text).unwrap_err().message;
    let m = message("def f (n : Nat) : Nat := (let x := n in x)\n");
    assert!(m.contains("expected `;` after the value of `let`"), "{m}");
    let m = message("def f (n : Nat) : Nat := (let x := n)\n");
    assert!(m.contains("expected `;` after the value of `let`"), "{m}");
    let m = message("def f (n : Nat) : Nat := (let x := n;)\n");
    assert!(m.contains("`let` needs a body after `;`"), "{m}");
}

/// `a; b` is the tree the block lines `a` and `b` make (SW-888, D1700).
#[test]
fn a_sequence_is_block_lines() {
    let block = rhs("def f (n : Nat) : Nat :=\n  a\n  let x := b\n  c\n  x\n");
    for text in [
        "def f (n : Nat) : Nat := (a; let x := b; c; x)\n",
        "def f (n : Nat) : Nat := a; let x := b; c; x\n",
        "def f (n : Nat) : Nat :=\n  a\n  let x := b; c; x\n",
        "def f (n : Nat) : Nat :=\n  a\n  let x := b\n  c; x\n",
        "def f (n : Nat) : Nat :=\n  (a;\n    let x := b; c; x)\n",
    ] {
        let e = rhs(text);
        let e = match &e {
            Expr::Bracketed(inner, _) => inner,
            e => e,
        };
        assert_eq!(lines(e), lines(&block), "{text}");
        assert_eq!(shape(e), shape(&block), "{text}");
    }
}

#[test]
fn sequence_precedence() {
    let cases = [
        // Looser than everything else, so it runs to the right.
        ("a; b; c", "(; a (; b c))"),
        ("f a; g b", "(; (f a) (g b))"),
        ("a |> f; b", "(; (|> a f) b)"),
        ("a; b |> f", "(; a (|> b f))"),
        ("x => a; b", "(=> (; a b))"),
        ("if a then b; x else y; f", "(if (; b x) (; y f))"),
        // It ends at a comma, as a `let`'s body does.
        ("(a; b, f)", "(, (; a b) f)"),
        // In a `let`, a `;` after the value starts the body.
        ("(let z := a; b; f)", "(let z a (; b f))"),
        ("(let z := x => a; b)", "(let z (=> a) b)"),
        ("(let z := if a then b else x; y)", "(let z (if b x) y)"),
        ("(let z := let w := a; w; z)", "(let z (let w a w) z)"),
        // Unless the `;` is in brackets inside the value.
        ("(let z := (a; b); z)", "(let z (; a b) z)"),
        ("(let z := f (a; b); z)", "(let z (f (; a b)) z)"),
        ("(a; let z := b; z)", "(; a (let z b z))"),
    ];
    for (text, want) in cases {
        assert_eq!(shape_of(text), want, "{text}");
    }
}

#[test]
fn a_sequence_needs_an_expression_after_the_semicolon() {
    for text in [
        "def f (n : Nat) : Nat := (a;)\n",
        "def f (n : Nat) : Nat := (a; b;)\n",
        "def f (n : Nat) : (Nat, Nat) := (a;, b)\n",
        "def f (n : Nat) : Nat := (let x := n; x;)\n",
        // A `;` ending a block's line: the next line is a new statement.
        "def f (n : Nat) : Nat :=\n  a;\n  b\n",
    ] {
        let m = rhs_of(text).unwrap_err().message;
        assert!(
            m.contains("`;` needs an expression after it"),
            "{text}: {m}"
        );
    }
}

#[test]
fn else_on_its_own_line_continues_the_if() {
    let e = rhs_of("def g (n : Nat) : Nat :=\n  if n == 0 then 1\n  else 2\n").unwrap();
    assert!(is_num(else_branch(&e), 2));
}

#[test]
fn then_and_else_chain_across_lines() {
    let text = "def g (n : Nat) : Nat :=\n  if a\n  then 1\n  else if b then 2\n  else if c then 3\n  else 4\n";
    let e = rhs_of(text).unwrap();
    assert!(is_num(else_branch(else_branch(else_branch(&e))), 4));
}

#[test]
fn a_proof_binder_and_a_let_value_can_span_lines() {
    let e = rhs_of("def g (n : Nat) : Nat :=\n  if h : n != 0 then 1\n  else 2\n").unwrap();
    assert!(matches!(
        e,
        Expr::If {
            binder: Some(_),
            ..
        }
    ));
    let e =
        rhs_of("def g (n : Nat) : Nat :=\n  let x := if n == 0 then 1\n  else 2\n  x\n").unwrap();
    assert!(matches!(e, Expr::Let { .. }));
}

#[test]
fn the_inner_if_takes_the_closest_else() {
    let e = rhs_of(
        "def g (a : Nat) (b : Nat) : Nat :=\n  if a then\n    if b then 1\n    else 2\n  else 3\n",
    )
    .unwrap();
    assert!(is_num(else_branch(&e), 3));
}

#[test]
fn an_else_left_of_its_if_is_explained() {
    let e =
        rhs_of("def g (a : Nat) : Nat :=\n  if a then\n    if a then 1\n  else 2\n").unwrap_err();
    assert!(
        e.message.contains("starts a new statement"),
        "{}",
        e.message
    );
}

#[test]
fn a_local_def_with_arms_then_the_result() {
    let body = rhs(
        "def sumTo (n : Nat) : Nat :=\n  let start := 0\n  def go : Nat -> Nat -> Nat\n    | Zero, acc => acc\n    | Succ k, acc => go k (acc + Succ k)\n  go n start\n",
    );
    assert_eq!(lines(&body), ["let start", "result"]);
    let Expr::Let { body, .. } = &body else {
        panic!()
    };
    let (names, rest) = local(body);
    assert_eq!(names, ["go"]);
    assert!(matches!(rest, Expr::App(..)), "{rest:?}");
    let Expr::LocalDefs { defs, .. } = body.as_ref() else {
        panic!()
    };
    assert_eq!(defs[0].equations.len(), 2);
}

#[test]
fn a_local_def_with_a_body_and_a_local_theorem() {
    let body = rhs(
        "def f (n : Nat) : Nat :=\n  def double (x : Nat) : Nat := x + x\n  theorem t : double 0 = 0 := refl\n  double n\n",
    );
    let (names, rest) = local(&body);
    assert_eq!(names, ["double", "t"]);
    assert!(matches!(rest, Expr::App(..)), "{rest:?}");
    let Expr::LocalDefs { defs, .. } = &body else {
        panic!()
    };
    assert!(matches!(
        defs[1].signature,
        Decl::Signature { theorem: true, .. }
    ));
    // A `:=` body on a further-indented block.
    let body =
        rhs("def f (n : Nat) : Nat :=\n  def g (x : Nat) : Nat :=\n    let y := x\n    y\n  g n\n");
    let (names, _) = local(&body);
    assert_eq!(names, ["g"]);
}

#[test]
fn interleaved_lets_and_defs_nest() {
    let body = rhs(
        "def f (n : Nat) : Nat :=\n  let a := 1\n  def g (x : Nat) : Nat := x\n  let b := 2\n  def h (x : Nat) : Nat := x\n  h b\n",
    );
    let Expr::Let { body, .. } = &body else {
        panic!("{body:?}")
    };
    let (names, rest) = local(body);
    assert_eq!(names, ["g"]);
    let Expr::Let { body, .. } = rest else {
        panic!("{rest:?}")
    };
    let (names, rest) = local(body);
    assert_eq!(names, ["h"]);
    assert!(matches!(rest, Expr::App(..)));
}

#[test]
fn local_defs_nest_in_blocks_arms_and_alternatives() {
    // In a nested block.
    let body =
        rhs("def f (n : Nat) : Nat :=\n  let r :=\n    def g (x : Nat) : Nat := x\n    g n\n  r\n");
    let Expr::Let { value, .. } = &body else {
        panic!("{body:?}")
    };
    assert_eq!(local(value).0, ["g"]);
    // In an arm body: the outer arms still parse.
    let module = parse(
        "def f : Nat -> Nat\n  | Zero =>\n    def g (x : Nat) : Nat := x\n    g 1\n  | Succ k =>\n    def h : Nat -> Nat\n      | Zero => 0\n      | Succ j => j\n    h k\n",
    );
    let arms: Vec<_> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Equation { rhs: Some(r), .. } => Some(r),
            _ => None,
        })
        .collect();
    assert_eq!(arms.len(), 2);
    assert_eq!(local(arms[0]).0, ["g"]);
    assert_eq!(local(arms[1]).0, ["h"]);
    // In a match alternative.
    let body = rhs(
        "def f (n : Nat) : Nat :=\n  match n with\n    | Zero =>\n      def g (x : Nat) : Nat := x\n      g 1\n    | Succ k => k\n",
    );
    let Expr::Match { alts, .. } = &body else {
        panic!("{body:?}")
    };
    assert_eq!(alts.len(), 2);
    assert_eq!(local(alts[0].body.as_ref().unwrap()).0, ["g"]);
}

#[test]
fn local_def_errors() {
    let e = parse_error("def f (n : Nat) : Nat :=\n  let a := 1\n  def g : Nat := a\n");
    assert!(e.message.contains("must end with an expression"), "{e:?}");
    assert!(e.message.contains("def"), "{e:?}");
    let e = parse_error("def f (n : Nat) : Nat :=\n  export def g : Nat := 1\n  g\n");
    assert!(e.message.contains("can't be exported"), "{e:?}");
    let e = parse_error("def f (n : Nat) : Nat :=\n  def g : Nat\n  n\n");
    assert!(e.message.contains("needs a body"), "{e:?}");
    let e = parse_error("def f (n : Nat) : Nat := g n\n  where\n    g : Nat\n");
    assert_eq!(e.code, "E-WHERE");
    assert!(e.message.contains("local `def`"), "{e:?}");
}
