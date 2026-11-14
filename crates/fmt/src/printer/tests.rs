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
fn a_comment_no_rule_places_leaves_its_declaration_as_written() {
    // S40: between a function and its first argument, joined to the line.
    let text = "def x: Nat := f\n  -- why\n  a\n";
    let gate = gate(text).unwrap();
    assert_eq!(gate.check, Ok(()));
    assert_eq!(gate.text, text);
    assert_eq!(gate.stats.verbatim_decls(), 1);
}

#[test]
fn comments_around_a_leading_comma_go_above_the_next_item() {
    let gate = gate("def x: List Nat :=\n  [ 1 -- a\n  -- b\n  , -- c\n    2\n  ]\n").unwrap();
    assert_eq!(gate.check, Ok(()));
    assert_eq!(gate.stats.verbatim_decls(), 0);
    assert_eq!(
        gate.text,
        "def x: List Nat := [\n  1, -- a\n  -- b\n  -- c\n  2\n]\n"
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
    assert!(gate.stats.unruled.is_empty());
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
        "theorem t ∀ (n: Nat): n = n :=\n  ident (\n    let m := n\n    (rfl: m = m))\n",
        "theorem t ∀ (n: Nat): n = n := ident (\n  let m := n\n  (rfl: m = m))\n",
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
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a\n    -- why\n    := rfl\n",
        "theorem t ∀ (a: Nat): a = a := calc a\n  _ = a\n    -- why\n    := rfl\n",
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
    check(
        "def f: Nat := g (a, b --c\n)\n",
        "def f: Nat := g (\n  a,\n  b --c\n)\n",
    );
    check(
        "def f: List Nat := [1, 2 --c\n]\n",
        "def f: List Nat := [\n  1,\n  2 --c\n]\n",
    );
}
