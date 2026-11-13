//! Answers at a position (`stitchwort_driver::at`): the goal, the hover, the
//! call being typed, and the context anywhere in an expression.

use stitchwort_driver::at;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::live::{FileAnswers, LiveFile, Place};

const STACK: usize = 64 * 1024 * 1024;

const SOURCE: &str = "namespace Demo

def clampTo (low: Nat) (high: Nat := 10) (x: Nat): Nat := if x < low then low else x

def sum (xs: List Nat) (start: Nat): Nat :=
  match xs with
    | [] => start
    | Cons y rest =>
      let next := start + y
      sum rest next

def double (n: Nat): Nat := n + n

theorem twice (n: Nat): double n = n + n := ?
";

fn answers(text: &str) -> FileAnswers {
    with_stack(STACK, || answers_here(text))
}

fn answers_here(text: &str) -> FileAnswers {
    let mut session = Session::navigable_for_stack(STACK);
    session.elab.enable_expression_types();
    let mut live = LiveFile::new(session, "demo.sw", text.to_string(), None);
    live.step().expect("not cancelled");
    live.answers()
        .remove(&Place::Program("demo.sw".into()))
        .expect("the file")
}

/// `(line, column)` of the first `needle` in the source, plus `shift`.
fn at_text(text: &str, needle: &str, shift: usize) -> (u32, u32) {
    let offset = text.find(needle).expect("in the source") + shift;
    at::position_at(text, offset)
}

#[test]
fn the_goal_at_a_question_mark_and_near_it() {
    let file = answers(SOURCE);
    let goals = at::goals_of(&file);
    assert_eq!(goals.len(), 1);
    let goal = &goals[0];
    assert_eq!(goal.owner, "`twice`");
    assert_eq!(goal.goal, "double n = n + n");
    assert_eq!(goal.context.len(), 1);
    assert_eq!(
        (goal.context[0].name.as_str(), goal.context[0].ty.as_str()),
        ("n", "Nat")
    );
    assert!(goal.text.contains('\u{22a2}'), "{}", goal.text);

    let (line, col) = at_text(SOURCE, "?", 0);
    assert_eq!(at::goal_at(&goals, Some(&file), line, col), Some(goal));
    // Elsewhere in the declaration: the nearest goal of it.
    let (line, col) = at_text(SOURCE, "theorem", 2);
    assert_eq!(at::goal_at(&goals, Some(&file), line, col), Some(goal));
    // Outside every declaration: none.
    assert_eq!(at::goal_at(&goals, Some(&file), 0, 3), None);
}

#[test]
fn hover_shows_the_type_and_what_a_name_is() {
    let file = answers(SOURCE);
    let place = Place::Program("demo.sw".into());
    let (line, col) = at_text(SOURCE, "sum rest", 1);
    let hover = at::hover_at(&file, &place, Some(SOURCE), line, col, None).expect("a hover");
    assert!(
        hover
            .markdown
            .contains("def Demo.sum (xs: List Nat) (start: Nat): Nat"),
        "{}",
        hover.markdown
    );
    assert!(hover.markdown.contains("List Nat"), "{}", hover.markdown);
    // A selection: the type of the expression around it.
    let (l, c) = at_text(SOURCE, "start + y", 0);
    let selection = [l, c, l, c + "start + y".len() as u32];
    let hover = at::hover_at(&file, &place, Some(SOURCE), l, c, Some(selection)).expect("a hover");
    assert_eq!(hover.range, selection);
    assert!(hover.markdown.contains("Nat"), "{}", hover.markdown);
}

/// A proof a test fact was built from (D3549a) says so on hover.
#[test]
fn hover_on_a_term_a_test_fact_was_built_from() {
    let source = "import Std (List, Nat)

theorem fromMember (x: Nat) (xs: List Nat) (m: x ∈ xs): xs.contains x := m

theorem notZero (n: Nat) (big: n > 3): Nat.equal n 0 = False := isZero => omega
";
    let file = answers(source);
    let place = Place::Program("demo.sw".into());
    let (line, col) = at_text(source, ":= m", 3);
    let hover = at::hover_at(&file, &place, Some(source), line, col, None).expect("a hover");
    assert!(
        hover.markdown.contains(
            "builds the test fact `xs.contains x` from a proof of `x ∈ xs` (by `List.memContains`)"
        ),
        "{}",
        hover.markdown
    );
    // A lambda built into a fact says so on its first binder.
    let (line, col) = at_text(source, "isZero =>", 0);
    let hover = at::hover_at(&file, &place, Some(source), line, col, None).expect("a hover");
    assert!(
        hover.markdown.contains("from a proof of `n ≠ 0`"),
        "{}",
        hover.markdown
    );
}

#[test]
fn the_parameters_of_a_call_being_typed() {
    let file = answers(SOURCE);
    let typed = format!("{SOURCE}\ndef use: Nat := clampTo (");
    let signature = at::signature_at(&file, &typed, typed.len()).expect("a call");
    assert_eq!(signature.function, "clampTo");
    let wanted: Vec<_> = signature.wanted().map(|p| p.name.as_str()).collect();
    assert_eq!(wanted, ["low", "high", "x"]);
    let typed = format!("{SOURCE}\ndef use: Nat := clampTo (low := 1) (");
    let signature = at::signature_at(&file, &typed, typed.len()).expect("a call");
    let wanted: Vec<_> = signature.wanted().map(|p| p.name.as_str()).collect();
    assert_eq!(wanted, ["high", "x"]);
}

fn context(text: &str, needle: &str, shift: usize) -> Option<at::Context> {
    let (line, col) = at_text(text, needle, shift);
    with_stack(STACK, || {
        Session::for_stack(STACK).context_at_text("demo.sw", text, line, col)
    })
}

#[test]
fn context_at_a_cursor_that_is_not_a_hole() {
    // On `y` in `start + y`: the type of that expression, and everything in
    // scope there, as a goal lists them (`xs` is gone: the `match` took it apart).
    let found = context(SOURCE, "start + y", 8).expect("a context");
    assert_eq!(found.ty, "Nat");
    let names: Vec<_> = found
        .locals
        .iter()
        .map(|l| (l.name.as_str(), l.ty.as_str()))
        .collect();
    assert_eq!(
        names,
        [("start", "Nat"), ("y", "Nat"), ("rest", "List Nat")]
    );
    let text_range = found.range;
    assert_eq!(text_range[0], text_range[2]);
}

#[test]
fn context_includes_lets_and_values() {
    // After `let next := start + y`, in the call that uses it.
    let found = context(SOURCE, "sum rest next", 9).expect("a context");
    let next = found
        .locals
        .iter()
        .find(|l| l.name == "next")
        .expect("next is in scope");
    assert_eq!(next.ty, "Nat");
    assert_eq!(next.value.as_deref(), Some("start + y"));
}

#[test]
fn context_at_a_goal_matches_the_goal() {
    let file = answers(SOURCE);
    let goal = at::goals_of(&file).remove(0);
    let found = context(SOURCE, "?", 0).expect("a context");
    assert_eq!(found.ty, goal.goal);
    assert!(found.checked, "a hole is checked against its type");
    assert_eq!(found.locals, goal.context);
}

#[test]
fn no_context_outside_expressions() {
    assert_eq!(context(SOURCE, "namespace", 2), None);
}

/// A declaration with an unclosed string loses only itself: hover still
/// answers elsewhere in the file, with the doc of what it names.
#[test]
fn hover_works_outside_a_declaration_with_a_lexical_error() {
    let source = "namespace Demo

--| Doubles a number.
def twice (n: Nat): Nat := n + n

def broken: Text := \"never closed

def useTwice: Nat := twice 2
";
    let file = answers(source);
    let place = Place::Program("demo.sw".into());
    let (line, col) = at_text(source, "twice 2", 1);
    let hover = at::hover_at(&file, &place, Some(source), line, col, None).expect("a hover");
    assert!(
        hover.markdown.contains("def Demo.twice (n: Nat): Nat"),
        "{}",
        hover.markdown
    );
    assert!(
        hover.markdown.contains("Doubles a number."),
        "{}",
        hover.markdown
    );
}
