//! `W-RECEIVER-NOT-FIRST` (docs/proposals/dot-receiver.md §6, D307): a
//! definition in `T`'s namespace that takes a `T`, but not as its first
//! explicit parameter, can't be called with `.` or `|>`. `@[noReceiver]`
//! opts a helper out (D309).

use stitchwort_cli::driver::Session;
use stitchwort_syntax::{Diagnostic, Severity};

const METER: &str = "type Meter = { v: Nat }\n\n";

fn warnings(text: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    let source = format!("{METER}{text}");
    if let Err(errors) = session.load("test.sw", &source) {
        panic!("{errors:#?}");
    }
    (session.warnings.iter())
        .filter(|w| w.code == "W-RECEIVER-NOT-FIRST")
        .cloned()
        .collect()
}

#[test]
fn a_receiver_after_another_parameter_warns() {
    let found = warnings("def Meter.scale (k: Nat) (m: Meter): Meter := { v = k * m.v }\n");
    let [w] = &found[..] else {
        panic!("{found:#?}");
    };
    assert_eq!(w.severity, Severity::Warning);
    assert_eq!(
        w.message,
        "`Meter.scale` takes a `Meter` but not as its first parameter, so `m.scale` and \
         `m |> Meter.scale` won't work"
    );
    assert!(
        w.notes[0].starts_with("put the main value first (`m`)"),
        "{w:?}"
    );
    assert!(w.notes[0].contains("`@[noReceiver]`"), "{w:?}");
}

#[test]
fn a_receiver_first_does_not_warn() {
    assert!(warnings("def Meter.scale (m: Meter) (k: Nat): Meter := { v = k * m.v }\n").is_empty());
}

#[test]
fn implicit_parameters_before_the_receiver_do_not_count() {
    assert!(warnings("def Meter.tag [a: Type] (m: Meter) (x: a): Meter := m\n").is_empty());
}

#[test]
fn no_parameter_of_the_type_does_not_warn() {
    assert!(warnings("def Meter.fromNat (n: Nat): Meter := { v = n }\n").is_empty());
}

#[test]
fn a_type_only_inside_another_does_not_count() {
    // `Option Meter`'s head is `Option`: `m.orZero` couldn't use it anyway.
    assert!(warnings("def Meter.orZero (k: Nat) (m: Option Meter): Nat := k\n").is_empty());
}

#[test]
fn the_attribute_opts_out() {
    assert!(
        warnings("@[noReceiver]\ndef Meter.scale (k: Nat) (m: Meter): Meter := { v = k * m.v }\n")
            .is_empty()
    );
}

#[test]
fn theorems_do_not_warn() {
    assert!(warnings("theorem Meter.same (n: Nat) (m: Meter): m = m := rfl\n").is_empty());
}
