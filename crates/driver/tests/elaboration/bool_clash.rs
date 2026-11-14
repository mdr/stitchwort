//! `cases` and `auto` close a goal when the context holds `e = True` and
//! `e = False` for the same Bool `e`, in either orientation, without
//! reading `e` as a proposition.

use stitchwort_driver::driver::Session;

const HEADER: &str = "import Std (Bool, Nat, List)\n\n\
    def rem (a: Nat) (b: Nat) [auto ok: b ≠ 0]: Nat := a % b\n\n";

fn load(body: &str) -> Result<(), Vec<&'static str>> {
    let mut session = Session::new();
    session
        .load("test.sw", &format!("{HEADER}{body}\n"))
        .map(|_| ())
        .map_err(|errors| errors.iter().map(|d| d.code).collect())
}

#[test]
fn cases_closes_a_goal_from_both_values_of_a_test() {
    load("theorem t (xs: List Nat) (x: Nat) (y: Nat) (h1: xs.contains x = True) (h2: xs.contains x = False): y = 7 := cases")
        .unwrap();
}

#[test]
fn cases_closes_it_in_either_orientation() {
    for (a, b) in [
        ("True = xs.contains x", "xs.contains x = False"),
        ("xs.contains x = True", "False = xs.contains x"),
        ("True = xs.contains x", "False = xs.contains x"),
        ("xs.contains x = False", "xs.contains x = True"),
    ] {
        load(&format!(
            "theorem t (xs: List Nat) (x: Nat) (y: Nat) (h1: {a}) (h2: {b}): y = 7 := cases"
        ))
        .unwrap_or_else(|e| panic!("{a}, {b}: {e:?}"));
    }
}

#[test]
fn cases_leaves_two_different_tests_open() {
    let errors = load("theorem t (xs: List Nat) (x: Nat) (z: Nat) (y: Nat) (h1: xs.contains x = True) (h2: xs.contains z = False): y = 7 := cases")
        .unwrap_err();
    assert!(!errors.is_empty());
}

#[test]
fn auto_closes_a_goal_from_both_values_of_a_test() {
    load("def f (xs: List Nat) (x: Nat) (b: Nat) (h1: xs.contains x = True) (h2: xs.contains x = False): Nat := rem 1 b")
        .unwrap();
}

#[test]
fn auto_closes_it_with_the_constructor_on_the_left() {
    load("def f (xs: List Nat) (x: Nat) (b: Nat) (h1: True = xs.contains x) (h2: xs.contains x = False): Nat := rem 1 b")
        .unwrap();
}

#[test]
fn auto_leaves_two_different_tests_open() {
    let errors = load("def f (xs: List Nat) (x: Nat) (z: Nat) (b: Nat) (h1: xs.contains x = True) (h2: xs.contains z = False): Nat := rem 1 b")
        .unwrap_err();
    assert_eq!(errors, ["E-AUTO-STUCK"]);
}
