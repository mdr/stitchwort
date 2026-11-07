//! `W-NO-EFFECT` (D1702, SW-889): a statement line, of a block or of a
//! sequence `a; b`, that performs no effects, so it does nothing; and the
//! lines that perform something, which don't warn.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::{Diagnostic, Severity};

const PARSERS: &str = "import Std (Nat, List, Parse)\n\
                       import Std.Parse (char, natDigits)\n\n\
                       def shortNumber(): {Parse} Nat := natDigits 1 3\n\n";

/// The `W-NO-EFFECT` warnings of `text` (after [`PARSERS`]), which must check.
fn warnings(text: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    let source = format!("{PARSERS}{text}");
    if let Err(errors) = session.load("test.sw", &source) {
        panic!("{errors:#?}");
    }
    session
        .warnings
        .into_iter()
        .filter(|w| w.code == "W-NO-EFFECT")
        .collect()
}

fn one(text: &str) -> Diagnostic {
    let mut found = warnings(text);
    assert_eq!(found.len(), 1, "{found:#?}");
    let w = found.remove(0);
    assert_eq!(w.severity, Severity::Warning);
    assert!(w.message.contains("this line does nothing"), "{w:?}");
    w
}

#[test]
fn a_parser_named_and_not_called_warns_with_its_call() {
    let w = one("def forgotten(): {Parse} Nat :=\n  char ','\n  shortNumber\n  shortNumber()\n");
    assert_eq!(w.notes, ["call it: `shortNumber()`"], "{w:?}");
}

#[test]
fn a_function_missing_its_argument_warns() {
    let w = one("def f(): {Parse} Nat :=\n  char\n  shortNumber()\n");
    assert!(
        w.notes[0].contains("`char` is a function missing its arguments"),
        "{w:?}"
    );
}

#[test]
fn the_first_part_of_a_sequence_warns_too() {
    let w = one("def f(): {Parse} Nat := (char; shortNumber())\n");
    assert!(w.notes[0].contains("`char`"), "{w:?}");
}

#[test]
fn arithmetic_on_its_own_line_warns() {
    let w = one("def f (x: Nat): {Parse} Nat :=\n  x + 1\n  shortNumber()\n");
    assert!(w.notes[0].contains("bind its value with `let`"), "{w:?}");
}

#[test]
fn a_map_with_a_pure_callback_warns_in_an_effectful_function() {
    one("def f (list: List Nat): {Parse} List Nat :=\n  list.map (x => x + 1)\n  list\n");
}

#[test]
fn a_map_with_a_pure_callback_warns_in_a_pure_function() {
    one("def f (list: List Nat): List Nat :=\n  list.map (x => x + 1)\n  list\n");
}

#[test]
fn an_effectful_call_whose_result_is_dropped_does_not_warn() {
    // Reading a number only to skip it is fine (D1713 is another question).
    assert!(
        warnings("def f(): {Parse} Nat :=\n  shortNumber()\n  char ','\n  shortNumber()\n")
            .is_empty()
    );
}

#[test]
fn a_map_with_an_effectful_callback_does_not_warn() {
    assert!(
        warnings(
            "def f (list: List Nat): {Parse} List Nat :=\n  list.map (x => shortNumber())\n  list\n"
        )
        .is_empty()
    );
}

#[test]
fn a_unit_line_does_not_warn() {
    assert!(warnings("def f(): {Parse} Nat :=\n  ()\n  shortNumber()\n").is_empty());
}

#[test]
fn a_call_of_a_parameter_whose_type_is_not_known_yet_does_not_warn() {
    assert!(warnings("def f(): Nat := (run => (run (); 1)) (u => 2)\n").is_empty());
}

#[test]
fn handler_code_does_not_warn() {
    // A handled body, and a clause that resumes and then gives a value.
    let text = "ability Tick where\n  tick: () -> {Tick} ()\n\n\
                def count (body: () -> {Tick} ()): Nat :=\n  \
                handle body() with\n    | return r => 0\n    | tick(), k =>\n      k ()\n      1\n\n\
                def twice(): {Tick} () :=\n  tick()\n  tick()\n\n\
                def pureAround(): Nat :=\n  handle twice() with\n    | return r => ()\n    | tick(), k => k ()\n  count twice\n";
    assert!(warnings(text).is_empty(), "{:#?}", warnings(text));
}

#[test]
fn proofs_do_not_warn() {
    let text = "theorem zeroAdd (n: Nat): 0 + n = n :=\n  let m := n\n  rfl\n\n\
                theorem viaRewrite (a b: Nat) (h: a = b): b = a :=\n  let k := h\n  rewrite k in rfl\n";
    assert!(warnings(text).is_empty(), "{:#?}", warnings(text));
}

#[test]
fn a_map_whose_callback_has_statement_lines_is_not_tried() {
    // Trying it would elaborate the callback's lines twice, each trying its
    // own lines, doubling the work with each level of nesting: the warning
    // is missed instead.
    assert!(
        warnings(
            "def f (list: List Nat): {Parse} List Nat :=\n  \
             list.map (x => (let y := x; y + 1))\n  list\n"
        )
        .is_empty()
    );
}

#[test]
fn deeply_nested_callbacks_with_statement_lines_check_quickly() {
    // Each level is a statement line whose callback has statement lines of
    // its own. With every line tried as plain calls, callbacks included, the
    // work doubled with each level: 14 levels took 4 s, 20 would take minutes.
    let mut inner = "(IO.print \"x\"; IO.print \"y\")".to_string();
    for d in 1..20 {
        inner = format!("([1, 2].forEach (x{d} => {inner}); IO.print \"y\")");
    }
    let text = format!(
        "import Std (IO, List)\n\n\
         def main(): {{IO}} () :=\n  [1, 2].forEach (x20 => {inner})\n  IO.print \"done\"\n"
    );
    let start = std::time::Instant::now();
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", &text) {
        panic!("{errors:#?}");
    }
    let took = start.elapsed();
    assert!(
        took < std::time::Duration::from_secs(10),
        "20 levels took {took:?}"
    );
}
