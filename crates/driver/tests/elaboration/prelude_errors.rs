//! A prelude that doesn't check is reported like any other source error
//! (file, line, labels), not as a debug dump of byte offsets.

use stitchwort_driver::driver::Session;
use stitchwort_elab::prelude;

#[test]
fn a_duplicate_prelude_declaration_names_both_places() {
    let prelude = format!(
        "{}\ndef Nat.digitsOnto (fuel : Nat) (n : Nat) (acc : List Char) : List Char := acc\n",
        prelude()
    );
    let Err(report) = Session::try_with_prelude(&prelude) else {
        panic!("a duplicate declaration should not check");
    };
    // Line numbers are stable only relative to the prelude's length, so show
    // the first line and the message, not the excerpt.
    let summary: Vec<&str> = report
        .lines()
        .filter(|l| {
            l.contains("E-DUPLICATE")
                || l.contains("already defined")
                || l.contains("first defined")
        })
        .collect();
    insta::assert_debug_snapshot!(summary);
    assert!(report.contains("std/core/"), "{report}");
    assert!(!report.contains("start:"), "{report}");
}

/// A pinned declaration whose body changed refuses the prelude, naming it
/// and its new content hash (`stitchwort_core::pins`): otherwise the kernel
/// would compute `Nat.sub` natively to the old answers while proofs
/// unfolded the new body.
#[test]
fn a_changed_native_definition_refuses_the_prelude() {
    let (old, new) = (
        "  | Zero, Succ n => Zero\n",
        "  | Zero, Succ n => Succ Zero\n",
    );
    assert!(prelude().contains(old));
    let Err(report) = Session::try_with_prelude(&prelude().replacen(old, new, 1)) else {
        panic!("a prelude with a changed `Nat.sub` checks");
    };
    assert!(
        report.contains(
            "the library's `Nat.sub` isn't the declaration the kernel's natives were written for"
        ),
        "{report}"
    );
    assert!(report.contains("its content hash is now "), "{report}");
    assert!(report.contains("crates/core/src/pins.rs"), "{report}");
}
