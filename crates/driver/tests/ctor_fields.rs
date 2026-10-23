//! `W-RECORD-ARGUMENT` (docs/proposals/variant-fields.md §12.3): braces after
//! a one-field constructor whose field holds a record name the constructor's
//! own field, which is easily meant as the record's when the names coincide.

use stitchwort_driver::driver::Session;
use stitchwort_syntax::{Diagnostic, Severity};

fn warnings(text: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    session.load("test.sw", text).expect("checks");
    session
        .warnings
        .iter()
        .filter(|w| w.code == "W-RECORD-ARGUMENT")
        .cloned()
        .collect()
}

const ITEM: &str = "import Std (Option)\n\ntype Item = { value: Nat, fits: Bool }\n\n";

#[test]
fn naming_a_field_the_record_has_too_warns() {
    let found = warnings(&format!(
        "{ITEM}def get: Option Item -> Nat\n  | Some {{ value = n, .. }} => n.value\n  | None => 0\n"
    ));
    let [w] = &found[..] else {
        panic!("{found:#?}");
    };
    assert_eq!(w.severity, Severity::Warning);
    assert!(w.message.contains("`Some`'s own field `value`"), "{w:?}");
    assert!(w.notes[0].contains("Some ({ … })"), "{w:?}");
}

#[test]
fn the_bracketed_record_argument_and_positional_patterns_dont_warn() {
    let found = warnings(&format!(
        "{ITEM}def get: Option Item -> Nat\n  | Some ({{ value = n, .. }}) => n\n  | None => 0\n\n\
         def get2: Option Item -> Nat\n  | Some i => i.value\n  | None => 0\n"
    ));
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn a_field_the_record_lacks_doesnt_warn() {
    let found = warnings(
        "type Person = { name: Text, age: Nat }\n\ntype Wrap = | W (person: Person)\n\n\
         def nameOf: Wrap -> Text\n  | W { person = { name, .. }, .. } => name\n",
    );
    assert!(found.is_empty(), "{found:#?}");
}
