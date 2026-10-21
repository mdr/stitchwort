//! The search for decision procedures (`auto`) remembers, per definition,
//! what its result type is (`auto::result_head`). These check that what it
//! remembers never hides a decision procedure added later in the same
//! session, as in the REPL or the playground, and that the "above the use"
//! rule still holds.

use stitchwort_driver::driver::Session;
use stitchwort_syntax::Diagnostic;

fn codes(errors: &[Diagnostic]) -> Vec<&'static str> {
    errors.iter().map(|d| d.code).collect()
}

const TOKEN: &str = "
type Token : Prop =
  | MkToken

def needsToken : [auto t : Token] -> Nat := 1
";

#[test]
fn a_decision_procedure_added_in_a_later_file_is_found() {
    let mut session = Session::new();
    session.load("token.sw", TOKEN).expect("loads");
    // Nothing decides `Token` yet; the search has now looked at (and
    // remembered) every definition so far.
    let errors = session
        .load("early.sw", "def early : Nat := needsToken")
        .expect_err("nothing decides `Token` yet");
    assert_eq!(codes(&errors), ["E-AUTO-NONE"]);
    session
        .load(
            "dec.sw",
            "instance decToken : Decidable Token := Yes MkToken",
        )
        .expect("loads");
    session
        .load("late.sw", "def late : Nat := needsToken")
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
}

#[test]
fn a_decision_procedure_below_the_use_is_still_not_used() {
    let mut session = Session::new();
    // `client` is checked after `decToken` (it doesn't depend on it), but
    // `decToken` is written below it.
    let source = format!(
        "{TOKEN}
def first : Nat := needsToken [t := Decidable.fromYes decToken Trivial]

def client : Nat := needsToken

instance decToken : Decidable Token := Yes MkToken

def after : Nat := needsToken
"
    );
    let errors = session
        .load("test.sw", &source)
        .expect_err("`client` fails");
    assert_eq!(codes(&errors), ["E-AUTO-NONE"]);
}
