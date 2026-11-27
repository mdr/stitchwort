//! The tree printer's rules, one small input each. Inputs are written the
//! way an author might; the expected text is the style sheet's
//! (docs/proposals/formatter-style.md, rule numbers in the test names'
//! comments).

use super::*;

/// The tree printer's output for `text`, which must pass every check.
fn fmt(text: &str) -> String {
    let gate = gate(text).expect("it parses");
    assert_eq!(gate.check, Ok(()), "{}", gate.text);
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
    // D3565: parameters of one type merge.
    let before = "theorem shrinks ∀ (numbers: List Nat) (target: Nat) (start: Nat) \
                  (sums: numbers.sum = target) (front: List Nat) (count: Nat) \
                  (over: target < count) (other: front = numbers.drop start): front ≠ numbers := same\n";
    let after = "\
theorem shrinks ∀ (numbers: List Nat) (target start: Nat)
    (sums: numbers.sum = target)
    (front: List Nat) (count: Nat)
    (over: target < count)
    (other: front = numbers.drop start):
    front ≠ numbers :=
  same
";
    check(before, after);
}

#[test]
fn the_theorem_forall_is_added() {
    // D3472, as the line formatter does.
    check(
        "theorem t (a: Nat): a = a := byComputing\n",
        "theorem t ∀ (a: Nat): a = a := byComputing\n",
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
    // S23: the call stays on its line and the lambda opens downwards. D3571: only when the call would not fit on one line below.
    let name = long(108);
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
fn a_record_update_that_breaks_keeps_its_base_and_bar_together() {
    // S31, SW-3164: `{ position |` stays on the opening line and the fields
    // follow, also when the base has a trailing comment.
    let (a, b) = (long(60), long(60));
    check(
        &format!("def f (position: Position): Position := {{ position | x = {a}, y = {b} }}\n"),
        &format!(
            "def f (position: Position): Position := {{ position |\n  x = {a},\n  y = {b}\n}}\n"
        ),
    );
    check(
        "def f (position: Position): Position := { position -- here\n  | x = 1 }\n",
        "def f (position: Position): Position := { position | -- here\n  x = 1\n}\n",
    );
}

#[test]
fn an_attribute_list_that_fits_drops_its_trailing_comma() {
    // R15, S31, D1012: the same as the list without one.
    check(
        "@[js.tag \"kind\", js.other \"x\",]\ntype Message = | Note | Other\n",
        "@[js.tag \"kind\", js.other \"x\"]\ntype Message = | Note | Other\n",
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
fn a_comment_where_no_layout_breaks_gets_a_line_break() {
    // S40: between a function and its first argument, the comment starts
    // a line deeper than the call's, and so does the argument after it.
    check(
        "def x: Nat := f\n  -- why\n  a\n",
        "def x: Nat :=\n  f\n    -- why\n    a\n",
    );
    // After an operator, the operand goes below.
    check(
        "def x: Nat :=\n  a + -- why\n    b\n",
        "def x: Nat := a + -- why\n  b\n",
    );
}

#[test]
fn a_hugged_bracket_after_a_comment_lays_its_items_under_it() {
    // S23, S40: a comment above a hugged last argument, or after the
    // argument before it, puts the bracket on a line of its own; its items
    // go 2 in from it and its closer under it, as for any other node.
    check(
        "def x: List Nat := f\n  -- the pairs\n  (firstLongArgumentName, secondLongArgumentName, thirdLongArgumentName, fourthLongArgumentName)\n",
        "def x: List Nat := f\n  -- the pairs\n  (\n    firstLongArgumentName,\n    secondLongArgumentName,\n    thirdLongArgumentName,\n    fourthLongArgumentName\n  )\n",
    );
}

#[test]
fn comments_around_a_leading_comma_go_above_the_next_item() {
    let gate = gate("def x: List Nat :=\n  [ 1 -- a\n  -- b\n  , -- c\n    2\n  ]\n").unwrap();
    assert_eq!(gate.check, Ok(()));
    assert_eq!(
        gate.text,
        "def x: List Nat := [\n  1, -- a\n  -- b\n  -- c\n  2\n]\n"
    );
}

#[test]
fn a_closer_with_a_comment_after_code_with_one_keeps_its_line() {
    // Two comments can't share a line: the closer isn't hoisted onto the
    // first one's line (the fuzzer's SW-3497 case, which was printed as
    // `(1) -- c -- d`).
    check(
        "def a: Nat := f (1-- c\n)-- d\n x\n",
        "def a: Nat :=\n  f\n    (1 -- c\n    ) -- d\n    x\n",
    );
}

#[test]
fn a_field_after_a_closer_stays_after_it_when_a_comment_ends_the_line_before() {
    // `.total` can't start a line, so the closer can't move up in front of
    // the comment.
    check(
        "def a: Nat := (f 1-- c\n).total\n",
        "def a: Nat :=\n  (f 1 -- c\n  ).total\n",
    );
}

#[test]
fn a_comment_after_the_assign_puts_a_match_below_it_with_its_arms_deeper() {
    // The arms would otherwise line up with the `match` on its own line,
    // which starts a new statement.
    check(
        "def f (n: Nat): Nat :=-- c\n match n with\n  | Zero => 1\n  | Succ m => m\n",
        "def f (n: Nat): Nat := -- c\n  match n with\n    | Zero => 1\n    | Succ m => m\n",
    );
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
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a\n    := byComputing\n  _ = a := byComputing\n",
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a := byComputing\n  _ = a := byComputing\n",
    );
}

#[test]
fn text_blocks_and_interpolations_stay_as_written() {
    // S32, S33.
    let text = "test \"grid\" := parsed \"\"\"\n  12\n  34\n  \"\"\" == Ok \"${a}\"\n";
    let gate = gate(text).unwrap();
    assert_eq!(gate.check, Ok(()));
    assert_eq!(gate.text, text);
}

#[test]
fn an_arm_opens_a_comma_bracket_on_its_line() {
    // S21 with S31: the opener ends the arm's line.
    let a = long(40);
    check(
        &format!(
            "def f (n: Nat): R := match n with\n  | 0 => {{ x = {a}, y = {a}, z = {a} }}\n  | _ => r\n"
        ),
        &format!(
            "def f (n: Nat): R := match n with\n  | 0 => {{\n    x = {a},\n    y = {a},\n    z = {a}\n  }}\n  | _ => r\n"
        ),
    );
}

#[test]
fn some_arguments_never_start_a_line() {
    // `_` would read as a `calc` step, `.f` as a field of the line before.
    let a = long(50);
    check(
        &format!("def x: Nat := f ({a} 1) ({a} 2) _ .size\n"),
        &format!("def x: Nat :=\n  f\n    ({a} 1)\n    ({a} 2) _ .size\n"),
    );
}

#[test]
fn a_one_arm_match_inside_an_arm_breaks() {
    // On one line, the outer arms after it would read as its own.
    check(
        "def f (n: Nat) (m: Nat): Nat :=\n  match n with\n    | 0 =>\n      match m with\n        | k => k\n    | _ => 1\n",
        "def f (n m: Nat): Nat := match n with\n  | 0 =>\n    match m with\n      | k => k\n  | _ => 1\n",
    );
}

#[test]
fn a_block_inside_brackets_hugs() {
    check(
        "theorem t ∀ (n: Nat): n = n :=\n  ident (\n    let m := n\n    (byComputing: m = m))\n",
        "theorem t ∀ (n: Nat): n = n := ident (\n  let m := n\n  (byComputing: m = m))\n",
    );
}

#[test]
fn operators_after_a_match_stay_at_its_column() {
    check(
        "def d (n: Nat): Nat :=\n  match n with\n    | 0 => 1\n    | _ => n\n  |> k => k + 10\n",
        "def d (n: Nat): Nat :=\n  match n with\n    | 0 => 1\n    | _ => n\n  |> k => k + 10\n",
    );
}

#[test]
fn a_lambda_after_the_assign_stays_on_its_line() {
    // D3568: the body goes below at 2, not the whole lambda.
    let name = long(105);
    check(
        &format!("def f (n: Nat): Nat -> Nat :=\n  n =>\n    {name} n n\n"),
        &format!("def f (n: Nat): Nat -> Nat := n =>\n  {name} n n\n"),
    );
    check(
        &format!("def f (n: Nat): Nat :=\n  let g :=\n    k =>\n      {name} k k\n  g n\n"),
        &format!("def f (n: Nat): Nat :=\n  let g := k =>\n    {name} k k\n  g n\n"),
    );
}

#[test]
fn a_let_expression_and_a_sequence_break_after_each_semicolon() {
    // S18: the parts line up one column inside the bracket.
    let (a, b) = (long(60), long(60));
    check(
        &format!("def f (n: Nat): Nat := (let x := {a} n; {b} x)\n"),
        &format!("def f (n: Nat): Nat :=\n  (let x := {a} n;\n   {b} x)\n"),
    );
    check(
        &format!("def f (n: Nat): Nat := ({a} n; {b} n)\n"),
        &format!("def f (n: Nat): Nat :=\n  ({a} n;\n   {b} n)\n"),
    );
    check(
        "def f (n: Nat): Nat := (let x := n; x)\n",
        "def f (n: Nat): Nat := (let x := n; x)\n",
    );
}

#[test]
fn an_interpolation_is_never_broken() {
    // S32: however long, and as the author spaced it.
    let a = long(130);
    let text = format!("def f (n: Nat): Text :=\n  \"a ${{ {a} n }} b ${{n}} c\"\n");
    assert_eq!(fmt(&text), text);
}

#[test]
fn a_long_pattern_breaks_like_a_call() {
    // S22: the continuation is at +4 from the `|`, as a header's
    // parameters are, so it never lines up with a body at +2.
    let (a, b) = (long(50), long(50));
    check(
        &format!("def f (p: Nat): Nat := match p with\n  | Pair {a} (Pair {b} (Pair k k)) => 1\n"),
        &format!(
            "def f (p: Nat): Nat := match p with\n  | Pair {a}\n      (Pair {b} (Pair k k)) => 1\n"
        ),
    );
}

#[test]
fn a_long_exists_chain_continues_below() {
    // S28.
    let (a, b) = (long(60), long(60));
    check(
        &format!(
            "theorem t ∀ (n: Nat): ∃ ({a}: Nat) => ∃ ({b}: Nat) => ∃ (c: Nat) => n = c\n  := same\n"
        ),
        &format!(
            "theorem t ∀ (n: Nat):\n    ∃ ({a}: Nat) =>\n      ∃ ({b}: Nat) => ∃ (c: Nat) => n = c :=\n  same\n"
        ),
    );
}

#[test]
fn a_comment_above_the_assign_of_a_calc_step_keeps_its_line() {
    // S35, S40.
    check(
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a\n    -- why\n    := byComputing\n",
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a\n    -- why\n    := byComputing\n",
    );
}

#[test]
fn plain_arguments_that_do_not_fit_fill_lines_at_four() {
    // D3569.
    let names: Vec<String> = (0..8).map(|k| format!("{}{k}", long(20))).collect();
    let call = names.join(" ");
    let (first, second) = (names[..5].join(" "), names[5..].join(" "));
    check(
        &format!("def f (n: Nat): Nat :=\n  g {call}\n"),
        &format!("def f (n: Nat): Nat :=\n  g {first}\n      {second}\n"),
    );
}

#[test]
fn leading_plain_arguments_past_the_width_fill_lines_and_the_rest_follow_at_the_same_indent() {
    // D3569 for the plain arguments before a bracketed one (SW-3187).
    let names: Vec<String> = (0..8).map(|k| format!("{}{k}", long(20))).collect();
    let (first, second) = (names[..5].join(" "), names[5..].join(" "));
    check(
        &format!("def f (n: Nat): Nat :=\n  g {} (h n) n\n", names.join(" ")),
        &format!("def f (n: Nat): Nat :=\n  g {first}\n      {second}\n      (h n)\n      n\n"),
    );
    // A prefix that fits keeps the rest at 2.
    let name = long(115);
    check(
        &format!("def f (n: Nat): Nat :=\n  g {name} (h n) n\n"),
        &format!("def f (n: Nat): Nat :=\n  g {name}\n    (h n)\n    n\n"),
    );
}

#[test]
fn a_lambdas_parameters_that_do_not_fit_fill_lines_at_four() {
    // S22 (SW-3187): the body goes below at 2, the arrow stays after the
    // last parameter.
    let names: Vec<String> = (0..8).map(|k| format!("{}{k}", long(20))).collect();
    let (first, second) = (names[..5].join(" "), names[5..].join(" "));
    check(
        &format!("def f: Nat := {} => n + 1\n", names.join(" ")),
        &format!("def f: Nat :=\n  {first}\n      {second} =>\n    n + 1\n"),
    );
}

#[test]
fn a_match_joins_the_header_line_only_when_its_whole_head_fits() {
    // D3553, S12: a head that would wrap goes below at 2, arms at 4.
    check(
        "def f (n: Nat): Nat :=\n  match n with\n    | 0 => 1\n    | _ => 2\n",
        "def f (n: Nat): Nat := match n with\n  | 0 => 1\n  | _ => 2\n",
    );
    let name = long(90);
    let before =
        format!("def f (n: Nat): Nat :=\n  match {name} n n with\n    | 0 => 1\n    | _ => 2\n");
    check(&before, &before);
}

#[test]
fn an_empty_parameter_list_stays_attached_to_the_definition_name() {
    // D1039: `f()` is a call with no arguments, `f ()` is not.
    check(
        "def main(): {IO} () := IO.print \"hi\"\n",
        "def main(): {IO} () := IO.print \"hi\"\n",
    );
}

#[test]
fn a_bracketed_if_keeps_its_else_under_the_if() {
    // S19: clauses at the `if`'s column, not the bracket's.
    let (a, b) = (long(70), long(70));
    let want = format!("def f (n: Nat): Nat :=\n  (if {a} then 1\n   else {b})\n");
    let before = format!("def f (n: Nat): Nat := (if {a} then 1 else {b})\n");
    check(&before, &want);
}

#[test]
fn a_record_or_hugging_call_goes_below_when_it_fits_there_on_one_line() {
    // D3571: the hug is for a body that doesn't fit below.
    let (a, b) = (long(40), long(40));
    let record = format!("{{ row = {a}, column = {b} }}");
    check(
        &format!("def moved (position: Position): Position := {record}\n"),
        &format!("def moved (position: Position): Position :=\n  {record}\n"),
    );
    let call = format!("{a}.filter (value => {b} value)");
    check(
        &format!("def f (xs: List Nat): List Nat := {call}\n"),
        &format!("def f (xs: List Nat): List Nat :=\n  {call}\n"),
    );
    // Too long for one line below: the record opens on the `:=` line.
    let c = long(60);
    let wide = format!("{{ row = {a}, column = {b}, other = {c} }}");
    let after = format!(
        "def moved (position: Position): Position := {{\n  row = {a},\n  column = {b},\n  other = {c}\n}}\n"
    );
    check(
        &format!("def moved (position: Position): Position := {wide}\n"),
        &after,
    );
}

#[test]
fn a_list_of_plain_values_fills_its_lines_and_any_other_list_has_one_item_a_line() {
    // D3572.
    let items: Vec<String> = (0..16)
        .map(|k| format!("{}", 10_000_000_000u64 + k))
        .collect();
    let flat = format!("def xs: List Nat := [{}]\n", items.join(", "));
    let fill = format!(
        "def xs: List Nat := [{},\n  {}]\n",
        items[..7].join(", "),
        items[7..].join(", ")
    );
    check(&flat, &fill);
    // A call among the items: one a line.
    let (a, b) = (long(60), long(60));
    check(
        &format!("def xs: List Nat := [f {a}, {b}]\n"),
        &format!("def xs: List Nat := [\n  f {a},\n  {b}\n]\n"),
    );
}

#[test]
fn a_tuple_pattern_of_names_fills_its_lines_and_any_other_has_one_item_a_line() {
    // proof-tuples.md §5: names and `_` fill the line; a tuple with a
    // nested pattern is a comma bracket, one item a line.
    let names: Vec<String> = (0..12).map(|k| format!("part{k:x<9}")).collect();
    let flat = format!(
        "def f (x: Nat): Nat := match x with\n  | ({}, _, last) => 0\n",
        names.join(", ")
    );
    let fill = format!(
        "def f (x: Nat): Nat := match x with\n  | ({},\n      {}, _, last) => 0\n",
        names[..7].join(", "),
        names[7..].join(", ")
    );
    check(&flat, &fill);
    let nested = format!(
        "def f (x: Nat): Nat := match x with\n  | ({}, Some y, last) => 0\n",
        names.join(", ")
    );
    assert!(
        fmt(&nested).contains("(\n"),
        "one item a line: {}",
        fmt(&nested)
    );
}

#[test]
fn a_single_variable_after_a_premise_shares_the_premise_line() {
    // D3564, D3571: no variable stands alone on a line.
    let before = "theorem shrinks ∀ (numbers: List Nat) (target: Nat) (start: Nat) \
                  (sums: numbers.sum = target) (count: Nat) \
                  (over: target < count) (other: numbers = numbers.drop start): numbers ≠ numbers := same\n";
    let after = "\
theorem shrinks ∀ (numbers: List Nat) (target start: Nat)
    (sums: numbers.sum = target) (count: Nat)
    (over: target < count)
    (other: numbers = numbers.drop start):
    numbers ≠ numbers :=
  same
";
    check(before, after);
}

#[test]
fn a_run_of_variables_does_not_leave_its_last_variable_alone_on_a_line() {
    // SW-3193, D3564: greedy filling would put `(middle: Position)` by itself
    // on line 2; the variable before it comes down to keep it company.
    let before = "theorem isPathAppend ∀ (allowed: Position → Bool) (more: List Position) (to: Position) \
                  (from: Position) (steps: List Position) (middle: Position) \
                  (path: isPath allowed from steps middle = True): isPath allowed from steps to = True := same\n";
    let after = "\
theorem isPathAppend ∀ (allowed: Position → Bool) (more: List Position) (to from: Position)
    (steps: List Position) (middle: Position)
    (path: isPath allowed from steps middle = True):
    isPath allowed from steps to = True :=
  same
";
    check(before, after);
}

#[test]
fn a_comment_before_a_closing_bracket_moves_to_the_line_end_without_changing_the_layout() {
    // The comment trails the `)` after the first run, so the second must
    // choose the same layout (SW-3203).
    check(
        "type Shape =\n  | Circle (kind: Text) (radius: Nat --eld\n)\n",
        "type Shape = | Circle (kind: Text) (radius: Nat) --eld\n",
    );
    check(
        "type Shape =\n  | Circle (radius: Nat) --eld\n  | Square (side: Nat)\n",
        "type Shape =\n  | Circle (radius: Nat) --eld\n  | Square (side: Nat)\n",
    );
    // Under rule N a comment on the last item and one after the closer
    // are the same comment, so every spelling prints alike.
    for text in [
        "def f: Nat := g (a, b --c\n)\n",
        "def f: Nat := g (a, b) --c\n",
        "def f: Nat := g (\n  a,\n  b\n) --c\n",
        "def f: Nat := g (a\n  , b --c\n  )\n",
    ] {
        check(text, "def f: Nat := g (a, b) --c\n");
    }
    for text in [
        "def f: List Nat := [1, 2 --c\n]\n",
        "def f: List Nat := [1, 2, --c\n]\n",
        "def f: List Nat := [\n  1,\n  2\n] --c\n",
    ] {
        check(text, "def f: List Nat := [1, 2] --c\n");
    }
}

/// `type T = | A (x: Nat) | …` padded so the whole declaration line is `width` characters.
fn data_of_width(width: usize) -> String {
    let base = "type T = | A (x: Nat) | B (".len() + ": Nat)".len();
    format!(
        "type T = | A (x: Nat) | B ({}: Nat)\n",
        "n".repeat(width - base)
    )
}

#[test]
fn a_data_type_stays_on_one_line_up_to_80_characters_and_then_goes_one_constructor_a_line() {
    // S14, D3605: measured over the whole declaration line.
    for width in [79, 80] {
        let line = data_of_width(width);
        assert_eq!(line.trim_end().chars().count(), width);
        check(&line, &line);
    }
    let long = data_of_width(81);
    let name = &long["type T = | A (x: Nat) | B (".len()..long.len() - ": Nat)\n".len()];
    check(
        &long,
        &format!("type T =\n  | A (x: Nat)\n  | B ({name}: Nat)\n"),
    );
    // The same code written over several lines gets the same layout.
    check(
        &format!("type T =\n  | A (x: Nat)\n  | B ({name}: Nat)\n"),
        &format!("type T =\n  | A (x: Nat)\n  | B ({name}: Nat)\n"),
    );
}

#[test]
fn short_type_declarations_stay_on_one_line() {
    // S14, S15, D3605.
    for line in [
        "type Direction = | Up | Right | Down | Left\n",
        "type Person = { name: Text, age: Nat }\n",
        "type Result (a: Type) (e: Type): Type = | Ok (value: a) | Err (error: e)\n",
    ] {
        check(line, line);
    }
    check(
        "type Person = {\n  name: Text,\n  age: Nat\n}\n",
        "type Person = { name: Text, age: Nat }\n",
    );
}

#[test]
fn a_record_type_stays_on_one_line_up_to_80_characters_and_then_goes_one_field_a_line() {
    // S15, D3605.
    let record = |width: usize| {
        let base = "type R = { a: Nat, b: ".len() + " }".len();
        format!("type R = {{ a: Nat, b: {} }}\n", "T".repeat(width - base))
    };
    for width in [79, 80] {
        let line = record(width);
        assert_eq!(line.trim_end().chars().count(), width);
        check(&line, &line);
    }
    let long = record(81);
    let ty = &long["type R = { a: Nat, b: ".len()..long.len() - " }\n".len()];
    check(&long, &format!("type R = {{\n  a: Nat,\n  b: {ty}\n}}\n"));
    let interface = format!("interface I (f: Type) = {{ a: Nat, b: {ty} }}\n");
    check(
        &interface,
        &format!("interface I (f: Type) = {{\n  a: Nat,\n  b: {ty}\n}}\n"),
    );
}

#[test]
fn an_if_with_an_else_if_goes_one_clause_a_line_and_a_plain_if_still_fits() {
    // S19, D3605.
    check(
        "def f (n: Nat): Nat := if n = 0 then 1 else if n = 1 then 2 else 3\n",
        "def f (n: Nat): Nat :=\n  if n = 0 then 1\n  else if n = 1 then 2\n  else 3\n",
    );
    check(
        "def f (n: Nat): Nat :=\n  if n = 0 then 1\n  else 2\n",
        "def f (n: Nat): Nat := if n = 0 then 1 else 2\n",
    );
}

#[test]
fn a_semicolon_that_ends_a_line_before_a_comment_keeps_the_sequence() {
    // S18.
    check(
        "def three: Nat :=\n  let x := 1;\n-- c\n  x\n",
        "def three: Nat :=\n  let x := 1;\n  -- c\n  x\n",
    );
}

#[test]
fn a_line_ending_semicolon_is_followed_by_a_rest_that_goes_deeper_when_it_breaks() {
    // S18: a second line ending `;` would meet a line at its block's column,
    // which ends the block, so each later line of the rest steps in by 2.
    check(
        "def three: Nat :=\n  (let x := 1; 2;\n-- c\n   x)\n",
        "def three: Nat :=\n  (let x := 1;\n   2;\n     -- c\n     x)\n",
    );
    check(
        "def three: Nat :=\n  (2; 3; -- c\n   x)\n",
        "def three: Nat :=\n  (2;\n   3; -- c\n     x)\n",
    );
    let part = format!("f {}", long(50));
    check(
        &format!("def three: Nat :=\n  let x := 1; {part}; {part}; {part}\n"),
        &format!("def three: Nat :=\n  let x := 1;\n  {part};\n    {part}; {part}\n"),
    );
}

#[test]
fn a_sequence_that_starts_a_line_breaks_after_a_semicolon_two_columns_in() {
    // S18: a line at the sequence's own column would end its block.
    check(
        "def d: Nat :=\n  [a; -- c\n   b]\n",
        "def d: Nat := [\n  a; -- c\n    b\n]\n",
    );
    check(
        "def d: Nat :=\n  xs.map (x => a; -- c\n    b)\n",
        "def d: Nat := xs.map (x =>\n  a; -- c\n    b)\n",
    );
}

#[test]
fn a_comment_on_its_own_line_after_an_arrow_goes_before_it() {
    // SW-3524, SW-3533: an operand starting its own line would end the
    // type at the next arrow.
    check(
        "def combine (f: Nat ->\n-- c\n b -> c): List c := xs\n",
        "def combine\n    (f: Nat\n      -- c\n      -> b\n      -> c):\n    List c :=\n  xs\n",
    );
    check(
        "def pick: Option Bool →\n-- c\n Nat → Nat\n  | Some _, 0 => 1\n",
        "def pick: Option Bool\n      -- c\n      → Nat\n      → Nat\n  | Some _, 0 => 1\n",
    );
    check(
        "def f (x: Nat → -- c\n -- d\n  Nat → Nat): Nat := x\n",
        "def f\n    (x: Nat\n      -- c\n      -- d\n      → Nat\n      → Nat):\n    Nat :=\n  x\n",
    );
}

#[test]
fn a_comment_inside_the_header_puts_the_body_below_it() {
    // SW-3532: the `calc` steps are measured from the keyword's line.
    check(
        "theorem t (h: a =-- c\n 3): 3 = a :=\n  calc 3\n    _ = a := h\n",
        "theorem t ∀\n    (h: a = -- c\n      3):\n    3 = a :=\n  calc 3\n    _ = a := h\n",
    );
}

#[test]
fn a_comment_after_a_result_colon_starts_the_type_on_its_own_line() {
    // SW-3537: the type's continuation lines were left of its first line.
    check(
        "theorem t: -- c\n f 2 = Some\n-- c\n (R 2) := byComputing\n",
        "theorem t: -- c\n    f 2 = Some\n    -- c\n    (R 2) :=\n  byComputing\n",
    );
}

#[test]
fn an_else_may_line_up_with_an_if_whose_binder_a_comment_moved_down() {
    // SW-3538: the parser measured `else` against the binder's line.
    check(
        "def f (b: Bool): Nat := if\n-- c\n h: b then 1 else 0\n",
        "def f (b: Bool): Nat :=\n  if\n    -- c\n    h: b then\n    1\n  else 0\n",
    );
}

#[test]
fn a_type_a_comment_moved_to_its_own_line_continues_from_where_it_lands() {
    // SW-3570, SW-3573, SW-3575: the lines after a first line that a comment
    // displaced stay right of it, or they would end the block it opens.
    check(
        "type Stream: Type = | MkStream (head: Nat) (rest:-- c\n Nat →\n-- c\n Stream)\n",
        "type Stream: Type =\n  | MkStream\n      (head: Nat)\n      (rest: -- c\n        Nat\n          -- c\n          → Stream)\n",
    );
    check(
        "type Box = | MkBox (n:\n-- c\n match 1 with | 0 => Nat | Succ m => Nat)\n",
        "type Box =\n  | MkBox\n      (n:\n        -- c\n        match 1 with\n          | 0 => Nat\n          | Succ m => Nat)\n",
    );
    check(
        "def greenOuter: Outer := { thing =\n-- c\n { color = Green, name =-- c\n \"g\" }\n}\n",
        "def greenOuter: Outer := {\n  thing =\n    -- c\n    {\n      color = Green,\n      name = -- c\n        \"g\"\n    }\n}\n",
    );
}

#[test]
fn an_if_chain_after_a_trailing_comment_keeps_its_else_lines_with_it() {
    // SW-3572: the `if` is on a line of its own after the comment.
    check(
        "def collatzSteps (n: Nat): {Partial} --Nat :=\n  if n ≤ 1 then 0\n  else if n % 2 == 0 then 1 + collatzSteps (n / 2)\n  else 1 + collatzSteps (3 * n + 1)\n",
        "def collatzSteps (n: Nat):\n    {Partial} --Nat :=\n      if n ≤ 1 then 0\n      else if n % 2 == 0 then 1 + collatzSteps (n / 2)\n      else 1 + collatzSteps (3 * n + 1)\n",
    );
}

#[test]
fn a_comment_after_the_last_parameter_puts_the_body_below_the_header() {
    // SW-3571: the `:` can't join the comment's line, so the header's last
    // line is a continuation, and a `calc` on it would measure its steps
    // from there.
    check(
        "theorem andChain ∀ (a b: Bool)-- c\n  : (a ∧ b) = (a ∧ b) := calc a ∧ b\n    _ = a ∧-- c\n b\n",
        "theorem andChain ∀ (a b: Bool) -- c\n    : (a ∧ b) = (a ∧ b) :=\n  calc a ∧ b\n    _ = a ∧ -- c\n      b\n",
    );
    // The same after a word of the head.
    check(
        "theorem-- c\n bad (a: Nat) (h: a = a): a = a :=\n  calc a\n    _ = a := h\n",
        "theorem -- c\n    bad ∀ (a: Nat)\n    (h: a = a):\n    a = a :=\n  calc a\n    _ = a := h\n",
    );
}

#[test]
fn a_let_whose_value_breaks_over_a_comment_keeps_its_semicolon_after_it() {
    // SW-3574: a value starting its own line is a block, which the `;`
    // after it would end as a sequence's.
    check(
        "def inArm (o: Option Nat): Nat := match o with\n  | Some k => let j := k +\n-- c\n 1; j * 2\n",
        "def inArm (o: Option Nat): Nat := match o with\n  | Some k =>\n    let j := k\n      +\n        -- c\n        1;\n    j * 2\n",
    );
}

#[test]
fn a_comment_right_after_a_let_assign_keeps_the_sequence() {
    // SW-3750: a comment ending the `:=` line must not put the value below
    // it: a value starting its own line is a block, which the `;` after it
    // would end as a sequence's.
    check(
        "def value: Text :=\n (let x :=-- c\n 1; 2; x)\n",
        "def value: Text :=\n  (let x\n    -- c\n    := 1;\n   2; x)\n",
    );
    // A list's element is bracketed too.
    check(
        "def xs: List Nat :=\n [let x :=-- c\n 1; 2; x]\n",
        "def xs: List Nat := [\n  let x\n    -- c\n    := 1;\n  2; x\n]\n",
    );
}

#[test]
fn a_comment_after_an_arrow_goes_before_it_and_a_long_chain_stays_one_chain() {
    // SW-3570: the operand after `→ -- c` would start a line, a block that
    // the next arrow at the chain's column ends.
    check(
        "def many: Nat → Nat →-- c\n Nat → Nat → Nat → Nat\n",
        "def many: Nat\n      → Nat\n      -- c\n      → Nat\n      → Nat\n      → Nat\n      → Nat\n",
    );
    check(
        "def many: Nat → Nat\n  -- c\n  → Nat → Nat →-- c\n Nat → Nat\n",
        "def many: Nat\n      → Nat\n      -- c\n      → Nat\n      → Nat\n      -- c\n      → Nat\n      → Nat\n",
    );
}

#[test]
fn a_record_update_with_comments_after_its_base_and_after_the_bar_keeps_both() {
    // SW-3580: the base's comment follows the `|` and the bar's own has
    // nowhere else to go, so it starts the line below.
    check(
        "def bad (t: Timed Int): Timed Nat := { t -- a\n  | -- b\n  start = 1 }\n",
        "def bad (t: Timed Int): Timed Nat := { t | -- a\n  -- b\n  start = 1\n}\n",
    );
}

#[test]
fn a_result_colon_after_own_line_comments_stays_with_its_type() {
    // SW-3578: the `:` started its line and the type went below it.
    check(
        "def f (a: Nat)\n  -- c\n  : Nat := a\n",
        "def f (a: Nat)\n    -- c\n    : Nat :=\n  a\n",
    );
    check(
        "def f (a: Nat) -- c\n  : Nat := a\n",
        "def f (a: Nat) -- c\n    : Nat := a\n",
    );
}

/// A `match` in a header followed by the definition's arms keeps its
/// alternatives on lines of their own, deeper than the arms: sharing the
/// header's line, the arms after it would read as its own (SW-3582).
#[test]
fn a_match_in_a_header_with_arms_after_it_keeps_its_alternatives_below() {
    check(
        "def loop (n: Nat): Nat 1 + match Succ n with\n               | Zero   => 0\n      | Succ k => loop k\n",
        "def loop (n: Nat):\n    Nat 1\n      + match Succ n with\n        | Zero => 0\n  | Succ k => loop k\n",
    );
}

/// A result type written as a block of lines keeps its lines, starting
/// below the `:`: joined to it, `List` would take `Text` as an argument
/// (SW-3582).
#[test]
fn a_result_type_that_is_a_block_starts_below_its_colon() {
    check(
        "def names:\n List\n Text := x\n",
        "def names:\n    List\n    Text :=\n  x\n",
    );
}

/// Two closers that each end a line with a comment keep both comments
/// (SW-3606: the second overwrote the first, and the file was written).
#[test]
fn comments_after_two_closers_on_two_lines_are_both_kept() {
    let out = fmt("def a: Nat := (f (1) -- c1\n  ) -- c2\n");
    assert!(out.contains("-- c1") && out.contains("-- c2"), "{out}");
}

/// The comments check counts comments as written, so an output missing one
/// is refused even where rule N reads both texts' comments alike.
#[test]
fn an_output_missing_a_comment_is_refused() {
    let file = SourceMap::new().add("input.sw", "");
    let before = "def a: Nat := (f (1) -- c1\n  ) -- c2\n";
    let error = check_file(file, before, before, "def a: Nat := (f (1)) -- c2\n").unwrap_err();
    assert!(error.contains("-- c1"), "{error}");
}

/// A bracketed block that isn't a call's last argument opens below its
/// bracket at 2, as one that is does (S17): after `(let`, the block's next
/// line would be left of the `let` and end it (SW-3605).
#[test]
fn a_bracketed_block_before_more_arguments_opens_below_the_bracket() {
    check(
        "theorem t ∀ (n: Nat): n + 1 = n + 1 := ident (\n  let m := n + 1\n  (rfl: m = m))\n  ys.length\n",
        "theorem t ∀ (n: Nat): n + 1 = n + 1 :=\n  ident\n    (\n      let m := n + 1\n      (rfl: m = m))\n    ys.length\n",
    );
}

/// An `if` that a comment puts on the line after an `else` is that
/// `else`'s branch, with its own clauses below it: at the chain's column,
/// its `else` would end the block the `if` starts (SW-3605).
#[test]
fn an_if_a_comment_puts_below_its_else_is_the_else_branch() {
    check(
        "def clamp (x lo hi: Int): Int :=\n if x < lo then lo\n  else-- c\n if hi < x then hi\n  else x\n",
        "def clamp (x lo hi: Int): Int :=\n  if x < lo then lo\n  else -- c\n    if hi < x then hi else x\n",
    );
    check(
        "def f (a b c: Bool): Nat := if a then 1 else -- c\n  if b then 2 else if c then 3 else 4\n",
        "def f (a b c: Bool): Nat :=\n  if a then 1\n  else -- c\n    if b then 2\n    else if c then 3\n    else 4\n",
    );
}

/// A closing bracket that comments put on a line of its own goes left of
/// the lines inside it: at the indentation in force, `Nat`'s, it would be
/// a line of the block `Nat` starts. It lines up with its opener's line
/// instead (SW-3605).
#[test]
fn a_closer_after_comments_goes_left_of_the_lines_inside_its_brackets() {
    check(
        "theorem small: ∃ (n:-- c\n Nat\n-- c\n) => n >\n (7, rfl)\n",
        "theorem small: ∃ (n: -- c\n    Nat\n      -- c\n) =>\n      n > (7, rfl)\n",
    );
}

/// A closer that a comment after the code before it and one of its own
/// put on a line of its own goes left of the lines inside its brackets
/// too: in a declaration's type the contents and the closer would both be
/// at 4, and the closer would read as the next line of a block (SW-3962).
#[test]
fn a_closer_after_a_trailing_comment_goes_left_of_the_lines_inside_its_brackets() {
    check(
        "def d: ( -- t7\n    a -- t9\n  ) -- t10\n  := b\n",
        "def d: ( -- t7\n    a -- t9\n) -- t10\n  :=\n  b\n",
    );
}

/// A blank line before the first cell of a filled list is dropped: it
/// would write nothing in mid-line but still break the groups around it,
/// and the result would format to another text (SW-3963).
#[test]
fn a_blank_line_before_a_filled_lists_first_cell_is_dropped() {
    check("def d: A := g [\n\n  f, a]\n", "def d: A := g [f, a]\n");
}

/// The same for a filled tuple pattern (SW-3992 filled them).
#[test]
fn a_blank_line_before_a_filled_tuple_patterns_first_cell_is_dropped() {
    check(
        "def sum (pair: (Nat, Nat)): Nat := match pair with\n  | (\n\n    a, b) => a + b\n",
        "def sum (pair: (Nat, Nat)): Nat := match pair with | (a, b) => a + b\n",
    );
}

/// A last comma that starts its line, after a blank line, hands its
/// trailing comment to the closer's own-line comments with that blank line
/// (SW-3963: the Stitchwort formatter dropped it).
#[test]
fn a_last_commas_trailing_comment_keeps_the_commas_blank_line_above_it() {
    check(
        "def d: A := f [g -- t12\n  -- o13\n\n , -- t14\n]\n",
        "def d: A := f [g -- t12\n  -- o13\n\n  -- t14\n]\n",
    );
}

/// A last comma on a line of its own, between comments, is deleted as text
/// and leaves its line blank (SW-3963).
#[test]
fn a_last_comma_on_its_own_line_leaves_a_blank_line_between_the_comments_around_it() {
    check(
        "def d: A := f [g\n  -- o2\n  ,\n  -- o3\n]\n",
        "def d: A := f [g\n  -- o2\n\n  -- o3\n]\n",
    );
}

/// A lambda right before a `;` keeps its body after `=>`: below, the body
/// would be a block, which the `;` would end as a sequence of its own
/// (SW-3605, SW-3587: here after a comment broke the parameters).
#[test]
fn a_lambda_before_a_semicolon_keeps_its_body_after_the_arrow() {
    check(
        "def lambdaValue: Nat := (let f := (n: Nat\n-- c\n) => n + 1; f 2)\n",
        "def lambdaValue: Nat :=\n  (let f := (n: Nat\n     -- c\n   ) => n + 1;\n   f 2)\n",
    );
    let name = long(100);
    check(
        &format!("def lambdaValue: Nat := (let f := (n: Nat) => n + {name}; f 2)\n"),
        &format!("def lambdaValue: Nat :=\n  (let f := (n: Nat) => n\n     + {name};\n   f 2)\n"),
    );
}

/// Comments between a declaration's attributes and its keyword stay at
/// its column, and so does the keyword: as a continuation line it would be
/// indented past its arms (SW-3605).
#[test]
fn a_comment_after_attributes_keeps_the_definition_at_its_column() {
    check(
        "@[noReceiver\n]\n-- c\ndef Meter.sumOnto (acc: Nat): List Meter → Nat\n  | [] => acc\n",
        "@[noReceiver]\n-- c\ndef Meter.sumOnto (acc: Nat): List Meter → Nat\n  | [] => acc\n",
    );
    check(
        "@[noReceiver]\n-- c\n\n-- d\n\ndef f (acc: Nat): Nat := acc\n",
        "@[noReceiver]\n-- c\n\n-- d\n\ndef f (acc: Nat): Nat := acc\n",
    );
}

/// A tidy pass that swaps the arguments of `f a b`: the tokens of its
/// result are the output's, so only a check against the original file can
/// see it (SW-3610).
fn swap_arguments(
    _tree: &stitchwort_syntax::tree::SyntaxFile,
    text: &str,
) -> Vec<crate::passes::Edit> {
    text.find("f a b").map_or(Vec::new(), |at| {
        vec![crate::passes::Edit {
            range: at..at + 5,
            text: "f b a".into(),
        }]
    })
}

/// A tidy pass that drops the brackets of `f (g a)`, which matter.
fn drop_needed_brackets(
    _tree: &stitchwort_syntax::tree::SyntaxFile,
    text: &str,
) -> Vec<crate::passes::Edit> {
    text.find("f (g a)").map_or(Vec::new(), |at| {
        vec![crate::passes::Edit {
            range: at..at + 7,
            text: "f g a".into(),
        }]
    })
}

/// The tree check compares the output with the original file, not the
/// tidied text, so a tidy pass that changes the program is refused.
#[test]
fn a_tidy_pass_that_changes_the_program_is_refused() {
    let file = SourceMap::new().add("input.sw", "");
    for (pass, text) in [
        (
            swap_arguments as crate::passes::Pass,
            "def x: Nat := f a b\n",
        ),
        (drop_needed_brackets, "def x: Nat := f (g a)\n"),
    ] {
        match format_with_passes(file, text, &[pass]) {
            Err(Error::Internal(message)) => assert!(message.contains("tree"), "{message}"),
            other => panic!("{text}: {other:?}"),
        }
    }
}

/// A `|>` (or other operator) that starts a line left of a `match`'s arms
/// continues the whole match; the printed form must keep it out of the
/// last arm (SW-3680).
#[test]
fn an_operator_after_a_match_block_stays_outside_its_arms() {
    for text in [
        "def classify (n: Nat): Nat :=\n  match n with\n    | 0 => 1\n  |> k => k + 10\n",
        "def classify (n: Nat): Nat :=\n  match n with\n    | 0 => 1\n  + 10\n",
        "def classify (n: Nat): Nat :=\n  if n = 0 then 1 else 2\n  |> k => k + 10\n",
    ] {
        let gate = gate(text).expect("it parses");
        assert_eq!(gate.check, Ok(()), "{text}\n=> {}", gate.text);
        assert!(gate.idempotent, "not idempotent:\n{}", gate.text);
    }
}

/// A unary minus before a numeral that heads an application keeps its
/// space: `- 2 n` is `Neg (App 2 n)`, where `-2 n` would apply the negative
/// numeral (`App (Neg 2) n`) (SW-3716).
#[test]
fn a_minus_before_an_applied_numeral_keeps_its_space() {
    // The fuzzer's minimal case must format at all, and be a fixed point.
    let text = "def f: Ieft withEnt → Nat\n  | 0 => - 2 is alreas are left withE-NONEXHAUSTIVE\n";
    let gate = gate(text).expect("it parses");
    assert_eq!(gate.check, Ok(()), "{text}\n=> {}", gate.text);
    assert!(gate.idempotent, "not idempotent:\n{}", gate.text);
    // The space is what keeps the `Neg` outside the application, and it
    // survives an argument the source wrote on the next line.
    check(
        "def g (n: Nat): Int := - 2 n\n",
        "def g (n: Nat): Int := - 2 n\n",
    );
    check(
        "def h (n: Nat): Int :=\n  - 2\n    n\n",
        "def h (n: Nat): Int := - 2 n\n",
    );
}

/// Every combination of a spaced or glued unary minus, an operand that is a
/// numeral, a name or bracketed, and an argument that is a numeral, a
/// negative one, a name, bracketed or a negative name (SW-3771): each must
/// print to a program with the same tree, and to a fixed point. A spaced
/// minus before a numeral is the only one that turns into a negative numeral
/// when glued, which would make the operand the head of the application
/// instead of the argument (SW-3716).
#[test]
fn a_unary_minus_keeps_its_operand_apart_from_every_kind_of_argument() {
    for minus in ["- ", "-"] {
        for operand in ["1", "x", "(x)"] {
            for argument in ["2", "-2", "n", "(n)", "-x"] {
                let source = format!("def f (x n: Int): Int := {minus}{operand} {argument}\n");
                let gate = gate(&source).expect("it parses");
                assert_eq!(gate.check, Ok(()), "{source}=> {}", gate.text);
                assert!(gate.idempotent, "not idempotent:\n{}", gate.text);
            }
        }
    }
    // The fuzzer's minimal case: the argument is a negative literal, so the
    // space after the first `-` is what keeps the `Neg` outside the
    // application.
    check(
        "def decrement (xs: List Int): List Int := xs.map (- 1 -1)\n",
        "def decrement (xs: List Int): List Int := xs.map (- 1 -1)\n",
    );
}

#[test]
fn a_calc_proof_never_wraps_a_hole_to_the_start_of_a_line() {
    // S35: a line starting with `_` would read as the next step. SW-3683.
    for k in 100..112 {
        let text = format!(
            "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a :=\n    f {} {} _\n  _ = a := byComputing\n",
            long(k),
            long(10)
        );
        fmt(&text);
    }
}

#[test]
fn a_rewrite_without_then_breaks_one_rule_a_line_when_the_rules_do_not_fit() {
    // S36 without a body, D3668: the first rule stays on the `rewrite` line,
    // the others follow at 4.
    let a = long(60);
    check(
        &format!("theorem t ∀ (a: Nat): a = a :=\n  rewrite f {a} _, g {a} _,\n    h {a} _ _\n"),
        &format!(
            "theorem t ∀ (a: Nat): a = a :=\n  rewrite f {a} _,\n      g {a} _,\n      h {a} _ _\n"
        ),
    );
    // A list that fits stays on one line.
    check(
        "theorem t ∀ (a: Nat): a = a :=\n  rewrite f _,\n    g _\n",
        "theorem t ∀ (a: Nat): a = a := rewrite f _, g _\n",
    );
}

#[test]
fn a_rewrite_without_then_breaks_before_its_target_too() {
    let a = long(60);
    check(
        &format!("theorem t ∀ (a: Nat): a = a :=\n  rewrite f {a} _, g {a} _ at h\n"),
        &format!("theorem t ∀ (a: Nat): a = a :=\n  rewrite f {a} _,\n      g {a} _ at h\n"),
    );
    check(
        &format!("theorem t ∀ (a: Nat): a = a :=\n  rewrite <- f {a} _, <- g {a} _\n"),
        &format!("theorem t ∀ (a: Nat): a = a :=\n  rewrite <- f {a} _,\n      <- g {a} _\n"),
    );
}

#[test]
fn a_rewrite_without_then_in_a_calc_step_keeps_the_steps_lined_up() {
    let a = long(40);
    check(
        &format!(
            "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a :=\n    rewrite f {a} _, g {a} _,\n      h {a} _ _\n  _ = a := byComputing\n"
        ),
        &format!(
            "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a :=\n    rewrite f {a} _,\n        g {a} _,\n        h {a} _ _\n  _ = a := byComputing\n"
        ),
    );
}

#[test]
fn a_rule_list_that_fits_drops_its_trailing_comma() {
    // D1012, P2: a rule list is a comma bracket, so its trailing comma goes
    // like a list literal's (SW-3729).
    check(
        "rules appends := [List.appendAssoc, ]\n",
        "rules appends := [List.appendAssoc]\n",
    );
    check(
        "theorem t ∀ (a: Nat): a = a := rewrite repeatedly [f _, ]\n",
        "theorem t ∀ (a: Nat): a = a := rewrite repeatedly [f _]\n",
    );
}

#[test]
fn a_rule_list_that_breaks_drops_its_trailing_comma() {
    let a = long(60);
    let b = format!("{a}b");
    check(
        &format!("rules appends := [{a}, {b}, ]\n"),
        &format!("rules appends :=\n  [\n    {a},\n    {b}\n  ]\n"),
    );
    check(
        &format!("rules appends := [\n  {a},\n  {b},\n]\n"),
        &format!("rules appends :=\n  [\n    {a},\n    {b}\n  ]\n"),
    );
}

#[test]
fn a_comment_between_binder_names_keeps_a_commented_body_block_together() {
    // SW-3728: the comment after `=>` moved the body's first line in by the
    // call's own indent, while its next statement stayed at the block's, so
    // the parser read that statement as a binder group after the first.
    check(
        "theorem t (x: Nat): ∀ (a-- c\n b: Bool) =>-- c\n f a\n b = f b a := same\n",
        "theorem t ∀ (x: Nat):\n    ∀ (a -- c\n      b: Bool) => -- c\n        f a\n        b = f b a :=\n  same\n",
    );
}

/// A parameter's function type split by comments after its colon and around
/// its arrow must print so the arrow stays inside the parameter (SW-3770):
/// left of the type's first line it closed the parameter, and the output
/// didn't parse. The arrow's comment comes before the arrow, as rule N has
/// it, whether the source wrote it after the arrow or on the line below.
#[test]
fn comments_around_a_parameter_types_arrow_stay_inside_the_parameter() {
    let after = "\
def apply (xs: List Nat)
    (kif: -- c
      List Nat
        -- c
        → Nat):
    Nat :=
  k [0, 0, ..xs]
";
    check(
        "def apply (xs: List Nat) (kif:-- c\n List Nat →\n-- c\n Nat): Nat := k [0, 0, ..xs]\n",
        after,
    );
    check(
        "def apply (xs: List Nat) (kif:-- c\n List Nat → -- c\n Nat): Nat := k [0, 0, ..xs]\n",
        after,
    );
}

/// A comment line ending `\r\r\n` loses every `\r`, not only the last, so the
/// output reads back the same (SW-4054).
#[test]
fn a_comment_ending_in_two_carriage_returns_keeps_none() {
    for text in [
        "-- a\r\r\ndef d: A := b\n",
        "def d: A := b\n-- a\r\r\n",
        "def d: A := b -- a\r\r\n",
    ] {
        let gate = gate(text).expect("it parses");
        assert_eq!(gate.check, Ok(()), "{text:?}\n=> {:?}", gate.text);
        assert!(gate.idempotent, "not idempotent:\n{:?}", gate.text);
        assert!(!gate.text.contains('\r'), "{:?}", gate.text);
    }
}

/// A comment's trailing carriage returns and spaces go together, in any
/// order, so the output reads back the same (SW-4065).
#[test]
fn a_comment_ending_in_carriage_returns_and_spaces_keeps_none() {
    for text in [
        "-- a\r \ndef d: A := b\n",
        "-- a \r\ndef d: A := b\n",
        "-- a\r \r\ndef d: A := b\n",
        "def d: A := b\n-- a\r \r \n",
        "def d: A := b -- a \r \r\n",
    ] {
        let gate = gate(text).expect("it parses");
        assert_eq!(gate.check, Ok(()), "{text:?}\n=> {:?}", gate.text);
        assert!(gate.idempotent, "not idempotent:\n{:?}", gate.text);
        assert!(!gate.text.contains('\r'), "{:?}", gate.text);
    }
}

/// A carriage return or a tab that something follows is kept, and the
/// output is stable.
#[test]
fn a_comment_keeps_a_carriage_return_or_tab_that_text_follows() {
    for text in [
        "-- a\r\t\ndef d: A := b\n",
        "-- a\rb\ndef d: A := b\n",
        "def d: A := b -- a\rb \r\n",
    ] {
        let gate = gate(text).expect("it parses");
        assert_eq!(gate.check, Ok(()), "{text:?}\n=> {:?}", gate.text);
        assert!(gate.idempotent, "not idempotent:\n{:?}", gate.text);
    }
}
