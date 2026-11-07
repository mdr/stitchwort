//! `decreasing`'s fallback when the plain form of `f.unfold` can't be
//! generated (D3100): the definition still checks, `f.unfold` is stated over
//! the step as before plain `if`s were shown, and a warning names the
//! failure as a compiler bug. No program is known to reach it, so a test
//! switch (`refuse_plain_view`) makes the generator fail once the twins of
//! the definition's `match`es are made.

use stitchwort_driver::driver::Session;

const SOURCE: &str = "\
import Std (Bool, Nat)

def countUp (bound: Nat) (i: Nat): Nat
    decreasing bound - i
:=
  if Nat.leq (i + 1) bound then countUp bound (i + 1) else i

-- A `match` whose twin is made before the failure, and goes with the rest.
def countDown (n: Nat) (k: Nat): Nat
    decreasing n - k
:=
  match n - k with
    | Zero => k
    | Succ j => if Nat.leq (k + 1) n then countDown n (k + 1) else k

test \"countUp\" := countUp 10 3 == 10
test \"countDown\" := countDown 4 0 == 4
";

fn names(session: &Session) -> Vec<String> {
    (session.elab.kernel.env.defs().iter())
        .map(|d| d.name().to_string())
        .collect()
}

#[test]
fn a_refused_plain_view_falls_back_to_the_step_with_a_warning() {
    let mut session = Session::new();
    session.elab.options.refuse_plain_view = Some("countDown".into());
    if let Err(errors) = session.load("test.sw", SOURCE) {
        panic!("doesn't check: {errors:#?}");
    }
    let names = names(&session);
    assert!(
        names.iter().any(|n| n.ends_with("countUp.%plain")),
        "{names:?}"
    );
    assert!(
        names.iter().any(|n| n.ends_with("countDown.unfold")),
        "{names:?}"
    );
    assert!(
        !(names.iter()).any(|n| n.contains("countDown.") && n.contains("%plain")),
        "the view and the twin are gone: {names:?}"
    );
    let warnings: Vec<_> = (session.warnings.iter())
        .filter(|w| w.code == "W-DECREASING-UNFOLD")
        .collect();
    assert_eq!(warnings.len(), 1, "one warning: {:#?}", session.warnings);
    assert!(
        warnings[0].message.contains("countDown.unfold"),
        "{:?}",
        warnings[0]
    );
    let notes = warnings[0].notes.join("\n");
    assert!(notes.contains("a bug in the compiler"), "{notes}");
}

/// Without the switch the same program has its plain views, and no warning.
#[test]
fn the_plain_view_is_made_without_the_switch() {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", SOURCE) {
        panic!("doesn't check: {errors:#?}");
    }
    assert!(
        !(session.warnings.iter()).any(|w| w.code == "W-DECREASING-UNFOLD"),
        "{:#?}",
        session.warnings
    );
    let names = names(&session);
    for view in ["countUp.%plain", "countDown.%plain", "%match1.%plain"] {
        assert!(names.iter().any(|n| n.ends_with(view)), "{view}: {names:?}");
    }
}
