//! `W-LAMBDA-SHADOW` (docs/proposals/lambda-syntax.md §7.2, D97): a lambda
//! with two or more parameters whose first hides a function in scope, and the
//! note on errors inside such a lambda.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::{Diagnostic, Severity};

fn load(text: &str) -> (Session, Result<(), Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load("test.sw", text).map(|_| ());
    (session, result)
}

fn shadow_warnings(session: &Session) -> Vec<&Diagnostic> {
    session
        .warnings
        .iter()
        .filter(|w| w.code == "W-LAMBDA-SHADOW")
        .collect()
}

#[test]
fn a_first_parameter_that_hides_an_imported_function_warns() {
    let (session, result) = load(
        "import Std (List)\nimport List (map)\n\n\
         def f : (Nat -> Nat) -> List Nat -> List Nat := map xs => List.map map xs\n",
    );
    result.unwrap();
    let [w] = &shadow_warnings(&session)[..] else {
        panic!("{:#?}", session.warnings);
    };
    assert_eq!(w.severity, Severity::Warning);
    assert!(
        w.message.contains("`map` hides the function `map`"),
        "{w:?}"
    );
    assert!(w.notes[0].contains("map (xs => …)"), "{w:?}");
}

#[test]
fn the_usage_of_the_parameter_does_not_matter() {
    // `map x => map x`: the author meant the outer `map`.
    let (session, _) =
        load("import List (map)\n\ndef f : (Nat -> Nat) -> Nat -> Nat := map x => map x\n");
    assert_eq!(
        shadow_warnings(&session).len(),
        1,
        "{:#?}",
        session.warnings
    );
}

#[test]
fn a_top_level_function_of_the_same_file_counts() {
    let (session, result) = load(
        "def r (i: Nat): Nat := i\n\n\
         def f : Nat -> Nat -> Nat := r acc => r + acc\n",
    );
    result.unwrap();
    assert_eq!(
        shadow_warnings(&session).len(),
        1,
        "{:#?}",
        session.warnings
    );
}

#[test]
fn a_local_variable_of_function_type_counts() {
    let (session, result) = load("def g (apply: Nat -> Nat) : Nat -> Nat -> Nat := apply y => y\n");
    result.unwrap();
    assert_eq!(
        shadow_warnings(&session).len(),
        1,
        "{:#?}",
        session.warnings
    );
}

#[test]
fn no_warning_otherwise() {
    for source in [
        // A fresh name.
        "import List (map)\n\ndef f : Nat -> Nat -> Nat := acc x => acc + x\n",
        // One parameter only.
        "import List (map)\n\ndef f : Nat -> Nat := map => map\n",
        // `_` hides nothing.
        "def f : Nat -> Nat -> Nat := _ x => x\n",
        // A top-level value that isn't a function.
        "def r : Nat := 3\n\ndef f : Nat -> Nat -> Nat := r x => r + x\n",
        // A local variable that isn't a function.
        "def g (n: Nat) : Nat -> Nat -> Nat := n y => n + y\n",
        // A bracketed argument lambda, as the note advises.
        "import List (map)\n\ndef f : List Nat -> List Nat := xs => map (x => x + 1) xs\n",
    ] {
        let (session, result) = load(source);
        result.unwrap_or_else(|e| panic!("{source}: {e:#?}"));
        assert!(
            shadow_warnings(&session).is_empty(),
            "{source}: {:#?}",
            session.warnings
        );
    }
}

#[test]
fn an_error_inside_such_a_lambda_gets_the_note() {
    let (_, result) = load("import List (map)\n\ndef f : Nat := map x => x + 1\n");
    let errors = result.unwrap_err();
    let error = errors
        .iter()
        .find(|d| d.severity == Severity::Error)
        .expect("an error");
    assert!(
        error
            .notes
            .iter()
            .any(|n| n.contains("put it in brackets: `map (x => …)`")),
        "{error:#?}"
    );
}
