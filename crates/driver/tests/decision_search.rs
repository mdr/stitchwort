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
def first : Nat := needsToken [t := Std.Decidable.fromYes decToken Trivial]

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

// The order the search tries procedures in, after the current module's own
// definitions, is remembered (`auto::DecisionOrder`, SW-913). These check
// that what it remembers never hides a procedure declared after it was
// worked out, or one declared again after a rewind.

const COIN: &str = "
type Coin : Prop =
  | MkCoin

def needsCoin : [auto c : Coin] -> Nat := 1

instance decCoin : Decidable Coin := Yes MkCoin
";

#[test]
fn a_decision_procedure_declared_after_a_search_in_the_same_file_is_found() {
    let mut session = Session::new();
    let source = format!(
        "{TOKEN}{COIN}
def warm : Nat := needsCoin

instance decToken : Decidable Token := Yes MkToken

def late : Nat := needsToken
"
    );
    session
        .load("test.sw", &source)
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
}

#[test]
fn a_decision_procedure_in_a_namespace_checked_after_a_search_is_found() {
    use stitchwort_driver::project::{MemoryFiles, Target};
    let base = format!("namespace Base\n{TOKEN}{COIN}");
    // `Early` searches (for `Coin`) before `A` is checked: `A` uses it.
    let early = "namespace Early\n\nimport Base (needsCoin)\n\ndef warm : Nat := needsCoin\n";
    let a = "namespace A

import Base (Token)
import Early (warm)

def used : Nat := warm

instance decToken : Decidable Token := Yes MkToken
";
    let day = "namespace Day\n\nimport Base (needsToken)\nimport A (decToken)\n\ndef late : Nat := needsToken\n";
    let files = MemoryFiles {
        files: [
            ("stitchwort.yaml", ""),
            ("src/base.sw", base.as_str()),
            ("src/early.sw", early),
            ("src/a.sw", a),
            ("src/day.sw", day),
        ]
        .iter()
        .map(|(p, t)| (p.to_string(), t.to_string()))
        .collect(),
        reversed: false,
    };
    let mut session = Session::new();
    session
        .load_project(&files, "proj", &Target::Everything)
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
}

/// Rewound, then a file declared again with as many definitions as before,
/// so everything the remembered order was worked out from is the same; but
/// now the procedure is marked `instance`. The search must see it.
#[test]
fn a_decision_procedure_declared_after_a_rewind_is_found() {
    let mut session = Session::new();
    session.load("token.sw", TOKEN).expect("loads");
    let mark = session.mark();
    session
        .load(
            "dec.sw",
            "def decToken : Decidable Token := Yes MkToken\n\ndef z : Nat := 0",
        )
        .expect("loads");
    let errors = session
        .load("use.sw", "def client : Nat := needsToken")
        .expect_err("`decToken` isn't marked `instance`");
    assert_eq!(codes(&errors), ["E-AUTO-NONE"]);
    let defs = session.elab.globals.defs.len();
    session.rewind(&mark);
    session
        .load(
            "dec.sw",
            "instance decToken : Decidable Token := Yes MkToken\n\ndef z : Nat := 0",
        )
        .expect("loads");
    session
        .load("use.sw", "def client : Nat := needsToken")
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
    // The same definitions as before the rewind, so only the rewind tells
    // the remembered order apart.
    assert_eq!(session.elab.globals.defs.len(), defs);
}

/// And the other way: a procedure that was found, rewound and declared
/// again without its mark, is no longer used.
#[test]
fn a_decision_procedure_unmarked_after_a_rewind_is_not_used() {
    let mut session = Session::new();
    session.load("token.sw", TOKEN).expect("loads");
    let mark = session.mark();
    session
        .load(
            "dec.sw",
            "instance decToken : Decidable Token := Yes MkToken\n\ndef z : Nat := 0",
        )
        .expect("loads");
    session
        .load("use.sw", "def client : Nat := needsToken")
        .unwrap_or_else(|errors| panic!("{errors:#?}"));
    session.rewind(&mark);
    session
        .load(
            "dec.sw",
            "def decToken : Decidable Token := Yes MkToken\n\ndef z : Nat := 0",
        )
        .expect("loads");
    let errors = session
        .load("use.sw", "def client : Nat := needsToken")
        .expect_err("`decToken` isn't marked `instance` now");
    assert_eq!(codes(&errors), ["E-AUTO-NONE"]);
}
