//! The tree printer's rules, one small input each. Inputs are written the
//! way an author might; the expected text is the style sheet's
//! (docs/proposals/formatter-style.md, rule numbers in the test names'
//! comments).

use super::*;

/// The tree printer's output for `text`, which must pass every check and
/// print no declaration as written.
fn fmt(text: &str) -> String {
    let gate = gate(text).expect("it parses");
    assert_eq!(gate.check, Ok(()), "{}", gate.text);
    assert_eq!(gate.stats.verbatim, BTreeMap::new(), "{}", gate.text);
    assert!(gate.idempotent, "not idempotent:\n{}", gate.text);
    gate.text
}

/// `fmt` of `before` is `after`, and `after` is a fixed point.
fn check(before: &str, after: &str) {
    assert_eq!(fmt(before), after);
    assert_eq!(fmt(after), after);
}

/// A name `n` characters long, to push lines past 120.
fn long(n: usize) -> String {
    format!("l{}", "o".repeat(n - 1))
}

#[test]
fn a_body_that_fits_joins_its_header_and_one_that_does_not_goes_below() {
    // S12.
    check(
        "def f (n: Nat): Nat :=\n  n + 1\n",
        "def f (n: Nat): Nat := n + 1\n",
    );
    let name = long(100);
    check(
        &format!("def f (n: Nat): Nat := {name} n n\n"),
        &format!("def f (n: Nat): Nat :=\n  {name} n n\n"),
    );
}

#[test]
fn a_long_theorem_header_puts_variables_first_and_each_premise_on_its_own_line() {
    // S8, D3564 (c): the conclusion on its own line, the body below at 2.
    let before = "theorem shrinks ∀ (numbers: List Nat) (target: Nat) (start: Nat) \
                  (sums: numbers.sum = target) (front: List Nat) (count: Nat) \
                  (over: target < count): front ≠ numbers := same\n";
    let after = "\
theorem shrinks ∀ (numbers: List Nat) (target: Nat) (start: Nat)
    (sums: numbers.sum = target)
    (front: List Nat) (count: Nat)
    (over: target < count):
    front ≠ numbers :=
  same
";
    check(before, after);
}

#[test]
fn the_theorem_forall_is_added() {
    // D3472, as the line formatter does.
    check(
        "theorem t (a: Nat): a = a := rfl\n",
        "theorem t ∀ (a: Nat): a = a := rfl\n",
    );
}

#[test]
fn a_match_opens_on_the_header_line_and_two_arms_go_one_a_line() {
    // D3553, S20, D3566.
    check(
        "def f (n: Nat): Nat :=\n  match n with | Zero => 1 | Succ k => k\n",
        "def f (n: Nat): Nat := match n with\n  | Zero => 1\n  | Succ k => k\n",
    );
    // One arm may share the line.
    check(
        "def f (p: (Nat, Nat)): Nat := match p with\n  | (a, b) => a\n",
        "def f (p: (Nat, Nat)): Nat := match p with | (a, b) => a\n",
    );
}

#[test]
fn an_arm_body_too_long_for_its_line_goes_below() {
    // S21.
    let name = long(110);
    check(
        &format!("def f (n: Nat): Nat := match n with\n  | Zero => {name} 1\n  | k => k\n"),
        &format!("def f (n: Nat): Nat := match n with\n  | Zero =>\n    {name} 1\n  | k => k\n"),
    );
}

#[test]
fn constructors_fit_or_break_like_fields() {
    // S14, D3566 (b).
    check(
        "type Direction =\n  | Up\n  | Down\n",
        "type Direction = | Up | Down\n",
    );
    // A trailing comment keeps them one a line (S39).
    check(
        "type Key =\n  | Printable (char: Char) -- a character\n  | Enter\n",
        "type Key =\n  | Printable (char: Char) -- a character\n  | Enter\n",
    );
}

#[test]
fn a_call_that_does_not_fit_keeps_simple_arguments_and_gives_bracketed_ones_lines() {
    // S23, D3567 (c).
    let name = long(60);
    let before = format!("def x: Nat := f a b (g {name}) (h {name})\n");
    let after = format!("def x: Nat :=\n  f a b\n    (g {name})\n    (h {name})\n");
    check(&before, &after);
}

#[test]
fn a_last_lambda_hugs() {
    // S23: the call stays on its line and the lambda opens downwards.
    let name = long(100);
    check(
        &format!("def x: List Nat := xs.map (x => {name} x x)\n"),
        &format!("def x: List Nat := xs.map (x =>\n  {name} x x)\n"),
    );
}

#[test]
fn a_long_chain_breaks_before_each_operator_of_its_level() {
    // S27.
    let a = long(40);
    let before = format!("def x: Bool := {a} && {a} || c && {a} && {a}\n");
    let after = format!("def x: Bool :=\n  {a} && {a}\n    || c && {a} && {a}\n");
    check(&before, &after);
}

#[test]
fn a_pipeline_that_does_not_fit_has_one_stage_a_line() {
    // S29.
    let a = long(50);
    check(
        &format!("def x: Nat := xs |> .map {a} |> .filter {a} |> .sum\n"),
        &format!("def x: Nat :=\n  xs\n    |> .map {a}\n    |> .filter {a}\n    |> .sum\n"),
    );
}

#[test]
fn a_comma_bracket_breaks_one_item_a_line() {
    // S2, S31, D1012: the opener ends the line, the closer has its own.
    let a = long(50);
    check(
        &format!("import Std ({a}, {a}2, {a}3)\n"),
        &format!("import Std (\n  {a},\n  {a}2,\n  {a}3\n)\n"),
    );
    check(
        "type R = {\n  a: Nat,\n  b: Text\n}\n",
        "type R = { a: Nat, b: Text }\n",
    );
}

#[test]
fn an_if_breaks_one_clause_a_line() {
    // S19.
    let a = long(50);
    check(
        &format!("def x: Nat := if c then {a} else if d then {a} else {a}\n"),
        &format!("def x: Nat :=\n  if c then {a}\n  else if d then {a}\n  else {a}\n"),
    );
}

#[test]
fn blocks_keep_one_statement_a_line_and_their_blank_lines() {
    // S17, E4.
    check(
        "def f (n: Nat): Nat :=\n  let a := n\n\n\n  let b :=\n    a\n  b\n",
        "def f (n: Nat): Nat :=\n  let a := n\n\n  let b := a\n  b\n",
    );
}

#[test]
fn comments_stay_where_they_were() {
    // S38, S39: above the item they belong to, and at the end of the line.
    check(
        "\
-- About f.
def f (n: Nat): Nat :=
  -- first
  let a := n -- the same
  a

-- At the end.
",
        "\
-- About f.
def f (n: Nat): Nat :=
  -- first
  let a := n -- the same
  a

-- At the end.
",
    );
    // A comment inside a list keeps it open.
    check(
        "def h: List Nat := [1, 2, -- two\n  3]\n",
        "def h: List Nat := [\n  1,\n  2, -- two\n  3\n]\n",
    );
}

#[test]
fn a_comment_no_rule_places_leaves_its_declaration_as_written() {
    // S40: between a function and its first argument, joined to the line.
    let text = "def x: Nat := f\n  -- why\n  a\n";
    let gate = gate(text).unwrap();
    assert_eq!(gate.check, Ok(()));
    assert_eq!(gate.text, text);
    assert_eq!(gate.stats.verbatim_decls(), 1);
}

#[test]
fn decreasing_breaks_its_header() {
    // S11.
    check(
        "def f (n: Nat): Nat decreasing n := f n\n",
        "def f (n: Nat): Nat\n    decreasing n\n:=\n  f n\n",
    );
}

#[test]
fn calc_steps_go_one_a_line() {
    // S35.
    check(
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a\n    := rfl\n  _ = a := rfl\n",
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a := rfl\n  _ = a := rfl\n",
    );
}

#[test]
fn text_blocks_and_interpolations_stay_as_written() {
    // S32, S33.
    let text = "test \"grid\" := parsed \"\"\"\n  12\n  34\n  \"\"\" == Ok \"${a}\"\n";
    let gate = gate(text).unwrap();
    assert_eq!(gate.check, Ok(()));
    assert_eq!(gate.text, text);
    assert_eq!(gate.stats.unruled.get(&NodeKind::Interpolated), Some(&1));
}
