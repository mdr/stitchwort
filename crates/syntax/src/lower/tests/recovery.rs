use super::*;

/// R1: an operand that runs out at the end of its line is missing, at
/// the end of the operator, and the lines after it are parsed as usual.
#[test]
fn an_operand_that_runs_out_is_missing_and_the_block_goes_on() {
    let text = "def f (n: Nat): Nat :=\n  let a := n +\n  let b := a * 2\n  b\n";
    let (module, errors, points) = recovered(text);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(points, [vec![RecoveryPoint::RanOut]]);
    assert!(module.decls.iter().any(|d| matches!(
        d,
        Decl::Signature { name, syntax_error: Some(_), .. } if name.text == "f"
    )));
    let Expr::Let { value, body, .. } = equation_rhs(&module, "f") else {
        panic!("{module:?}")
    };
    let Expr::Binary(BinOp::Add, _, missing) = &**value else {
        panic!("{value:?}")
    };
    let plus = text.find('+').unwrap() as u32;
    assert!(
        matches!(**missing, Expr::Missing(span) if span.start == plus + 1 && span.end == plus + 1),
        "{missing:?}"
    );
    assert!(matches!(**body, Expr::Let { .. }), "{body:?}");
}

/// `def f: Nat :=` with nothing after it is a definition whose body is
/// missing, not a primitive (a header with no body).
#[test]
fn a_body_that_runs_out_is_missing_not_a_primitive() {
    let (module, errors, points) = recovered("def f: Nat :=\n\ndef g: Nat := f\n");
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(points, [vec![RecoveryPoint::RanOut], vec![]]);
    assert!(matches!(equation_rhs(&module, "f"), Expr::Missing(_)));
}

/// A local definition whose result type runs out, at the end of the
/// input or before a line that ends the block, is one error at the gap
/// after its `:`. The empty type has no token to span, and at the end of
/// the input none follows it either (SW-3278).
#[test]
fn a_local_definition_whose_type_runs_out_is_one_error_at_the_gap() {
    for text in [
        "theorem t: Unit :=\n  def f (s: Nat):",
        "theorem t: Unit :=\n  def f (s: Nat):\n",
        "theorem t: Unit :=\n  def f:",
        "def g: Unit :=\n  def f [x: Nat]:",
        "def g: Unit :=\n  theorem h (n: Nat):\n",
        "def g: Unit :=\n  def f (s: Nat):\ndef h: Nat := 1\n",
    ] {
        let (_, errors, points) = recovered(text);
        assert_eq!(errors.len(), 1, "{text:?}: {errors:?}");
        assert_eq!(points[0], [RecoveryPoint::RanOut], "{text:?}");
        // The local header's line ends with its `:`.
        let local = text.find("\n  ").unwrap() + 1;
        let gap = text[local..].find('\n').map_or(text.len(), |i| local + i) as u32;
        let at = errors[0].primary_span().unwrap();
        assert_eq!((at.start, at.end), (gap, gap), "{text:?}");
    }
}

/// R6: an error nothing inside recovers from skips the rest of the body,
/// which is one missing expression over the skipped text; the
/// declarations after it are parsed as usual.
#[test]
fn a_body_that_breaks_is_skipped_to_the_end() {
    let text = "def f (n: Nat): Nat :=\n  let a := n + ) 1\n  a\n\ndef g: Nat := 1\n";
    let (module, errors, points) = recovered(text);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(points, [vec![RecoveryPoint::Body], vec![]]);
    let Expr::Missing(span) = equation_rhs(&module, "f") else {
        panic!("{module:?}")
    };
    let skipped = &text[text.find("let").unwrap()..text.find("\n\n").unwrap()];
    assert_eq!(&text[span.start as usize..span.end as usize], skipped);
    assert!(matches!(equation_rhs(&module, "g"), Expr::Num(..)));
}

/// Arms that break are one equation of the header's patterns whose body
/// is missing.
#[test]
fn arms_that_break_are_one_equation_with_a_missing_body() {
    let text = "def f: Nat -> Nat\n  | 0 => 1\n  | n => ) n\n";
    let (module, errors, points) = recovered(text);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(points, [vec![RecoveryPoint::Body]]);
    assert!(matches!(equation_rhs(&module, "f"), Expr::Missing(_)));
}

/// Outside a top-level definition's body nothing recovers: a header, a
/// data type, a test fail whole as before.
#[test]
fn headers_and_other_declarations_still_fail_whole() {
    for text in [
        "def f (n: Nat): Nat + := n\n",
        "type T =\n  | A (n: Nat +)\n",
        "test \"t\" := 1 +\n",
        "instance i: Foo := 1 +\n",
    ] {
        let (_, errors, points) = recovered(text);
        assert_eq!(errors.len(), 1, "{text}: {errors:?}");
        assert_eq!(points, [vec![]], "{text}");
    }
}

/// R1 inside a bracket left open in a `calc` step: the next step's `_`
/// is a stop, so the bracket's contents run out there. That is one
/// error at the `_`, the steps after it still parse, and no block is
/// opened on the `_` (one used to read it forever, SW-3285).
#[test]
fn a_bracket_left_open_in_a_calc_step_runs_out_at_the_next_step() {
    for text in [
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n(\n  _ ≤ m := h",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n[\n  _ ≤ m := h",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n {\n  _ ≤ m := h",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ f ((\n  _ ≤ m := h\n",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n := f (\n  _ ≤ m := h\n",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n := f (\n    _\n  _ ≤ m := h\n",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n := (calc 1\n    _ = 1 := (\n  _ ≤ m := h\n",
        "theorem z: 0 ≤ m := calc 0\n  _ ≤ n := match x with\n    | a => (\n  _ ≤ m := h\n",
    ] {
        let (_, errors, points) = recovered(text);
        assert_eq!(errors.len(), 1, "{text:?}: {errors:?}");
        assert_eq!(points, [vec![RecoveryPoint::RanOut]], "{text:?}");
        assert!(
            errors[0]
                .message
                .contains("the next `calc` step starts here"),
            "{text:?}: {errors:?}"
        );
        // At the first `_` after the line with the bracket left open.
        let open = text.rfind(['(', '[', '{']).unwrap();
        let after = open + text[open..].find('\n').unwrap();
        let step = (after + text[after..].find('_').unwrap()) as u32;
        let at = errors[0].primary_span().unwrap();
        assert_eq!((at.start, at.end), (step, step + 1), "{text:?}");
    }
}

/// A bracket left open at the end of a line, with another line at the
/// block's column or a guard's `=>` after it, is one error at the gap,
/// not a second one for the closer missing at the token that stopped
/// it: the call's `(` with a `let` after it, and a guard's `[` with the
/// arm's `=>` on the next line (SW-3289).
#[test]
fn a_bracket_left_open_at_a_line_end_is_one_error() {
    let call = "def f (x: Nat): Nat :=\n  g (\n  let y := 1\n  y\n";
    let guard = "def h (x: List Nat): Nat := match x with\n  | a if a == [\n    => 1\n  | _ => 2\n";
    let call_gap = call.find("(\n").unwrap() + 1;
    let arrow = guard.find("=>").unwrap();
    for (text, at) in [
        (call, (call_gap, call_gap)),
        (guard, (arrow, arrow + "=>".len())),
    ] {
        let (_, errors, points) = recovered(text);
        assert_eq!(errors.len(), 1, "{text:?}: {errors:?}");
        assert_eq!(points, [vec![RecoveryPoint::RanOut]], "{text:?}");
        let span = errors[0].primary_span().unwrap();
        assert_eq!(
            (span.start, span.end),
            (at.0 as u32, at.1 as u32),
            "{text:?}"
        );
        if text == guard {
            // The guard's own `=>`, not a lambda inside the guard: the
            // note asks about the unclosed bracket (SW-3308).
            assert!(
                errors[0].message.contains("the guard's `=>` starts here"),
                "{errors:?}"
            );
            assert!(
                errors[0]
                    .notes
                    .iter()
                    .any(|n| n.contains("bracket in the guard left open")),
                "{errors:?}"
            );
        }
    }
}

/// A guard that runs out at its own `=>` with no bracket open: the guard
/// message, but the bracket note is only for an unclosed bracket
/// (SW-3308).
#[test]
fn a_guard_that_runs_out_without_a_bracket_has_no_bracket_note() {
    let text = "def h (x: Nat): Nat := match x with\n  | a if a +\n    => 1\n  | _ => 2\n";
    let (_, errors, points) = recovered(text);
    assert_eq!(errors.len(), 1, "{text:?}: {errors:?}");
    assert_eq!(points, [vec![RecoveryPoint::RanOut]], "{text:?}");
    assert!(
        errors[0].message.contains("the guard's `=>` starts here"),
        "{errors:?}"
    );
    assert!(
        !errors[0].notes.iter().any(|n| n.contains("bracket")),
        "{errors:?}"
    );
    assert!(
        errors[0]
            .notes
            .iter()
            .any(|n| n.contains("condition is incomplete")),
        "{errors:?}"
    );
    let arrow = text.find("=>").unwrap();
    let span = errors[0].primary_span().unwrap();
    assert_eq!(
        (span.start, span.end),
        (arrow as u32, (arrow + 2) as u32),
        "{text:?}"
    );
}

#[test]
fn a_half_typed_minus_is_still_binary_in_recovery() {
    let text = "def a: Nat := 1\n\ndef b (n: Nat): Nat := n -\n\ndef d: Nat := 2\n";
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    let (module, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(module.decls.iter().any(|d| matches!(
        d,
        Decl::Signature { name, syntax_error: Some(_), .. } if name.text == "b"
    )));
}

/// The other brackets closed by [`Parser::close_bracket`]: a record's
/// braces, a named argument's `(x := e)` and an annotation's `(e : T)`.
/// Each left open at a line end is one error at the gap, not a second one
/// for the closer that isn't there (SW-3308).
#[test]
fn the_other_brackets_left_open_at_a_line_end_are_one_error() {
    let record = "def f (n: Nat): Nat :=\n  let r := {\n  let y := 1\n  y\n";
    let record_field = "def f (n: Nat): Nat :=\n  let r := { x =\n  let y := 1\n  y\n";
    let named = "def f (g: Nat -> Nat): Nat :=\n  g (x :=\n  let y := 1\n  y\n";
    let annotation = "def f (n: Nat): Nat :=\n  let m := (n :\n  let y := 1\n  y\n";
    for (text, gap) in [
        (record, record.find("{\n").unwrap() + 1),
        (
            record_field,
            record_field.find("x =\n").unwrap() + "x =".len(),
        ),
        (named, named.find("x :=\n").unwrap() + "x :=".len()),
        (
            annotation,
            annotation.find("(n :\n").unwrap() + "(n :".len(),
        ),
    ] {
        let (_, errors, points) = recovered(text);
        assert_eq!(errors.len(), 1, "{text:?}: {errors:?}");
        assert_eq!(points, [vec![RecoveryPoint::RanOut]], "{text:?}");
        let span = errors[0].primary_span().unwrap();
        assert_eq!((span.start, span.end), (gap as u32, gap as u32), "{text:?}");
    }
}
