//! `Float` (docs/proposals/float.md): the kernel's definitional agreement
//! gate (§3.4, D731), the bindings pinned by content hash, and the
//! contract plumbing (§3.3).

use stitchwort_core::Limits;
use stitchwort_core::float;
use stitchwort_driver::driver::Session;
use stitchwort_driver::float_gate::{self, Mode};

/// Every row of §3.4's table with natives on, and with the float natives
/// off (the number natives on): the `rfl` theorems check, `neg (neg x) = x`
/// is proved, and the normal forms are the same terms in both modes.
#[test]
fn the_float_natives_agree_with_their_definitions() {
    let checks = float_gate::run(&[Mode::NativesOn, Mode::FloatNativesOff], Limits::default());
    let failed: Vec<String> = checks
        .iter()
        .filter(|c| !c.passed)
        .map(|c| format!("[{}] {}: {}", c.mode.name(), c.name, c.detail))
        .collect();
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    // Per mode: the program, 4 natives, 6 pairs, 2 x 12 neutral witnesses;
    // then 13 + 24 normal forms compared across the modes.
    assert_eq!(checks.len(), 2 * (1 + 4 + 6 + 24) + 13 + 24, "{checks:#?}");
    // The cross-mode comparisons ran.
    assert!(
        checks
            .iter()
            .any(|c| c.mode == Mode::FloatNativesOff && c.name.contains("same term as"))
    );
}

/// With every native off (the `n0` mode), `Float` can't be checked at all:
/// its proofs compute with 64-bit patterns, and without the number natives
/// `Nat.leq` and `Nat.sub` count down one `Succ` at a time. The session runs
/// out of its work budget instead of looping (a small one, so this is
/// quick).
#[test]
fn with_every_native_off_float_runs_out_of_budget() {
    let limits = Limits {
        work: 2_000_000,
        ..Limits::default()
    };
    let checks = float_gate::run(&[Mode::AllNativesOff], limits);
    let loaded = &checks[0];
    assert!(!loaded.passed, "{loaded:?}");
    assert!(loaded.detail.contains("E-RESOURCE"), "{loaded:?}");
}

/// `Float` and the definitions with float natives are the declarations the
/// kernel's float support was written for. If this fails, the library
/// changed one: check the natives in crates/core/src/float.rs still compute
/// what the definitions do, then update the hashes there to these.
#[test]
fn the_float_bindings_are_the_pinned_declarations() {
    let mut session = Session::new();
    // A binding that doesn't match fails the load; its hash is printed below
    // all the same (fix `Float`'s first: the others depend on it).
    let loaded = session.load("uses.sw", "import Std (Float)\ndef zero: Float := 0.0\n");
    let bindings = float::bindings(&session.elab.globals);
    assert_eq!(bindings.len(), 1 + float::NATIVE_HASHES.len());
    let wrong: Vec<String> = bindings
        .iter()
        .filter(|(_, actual, pinned)| actual.as_deref() != Some(*pinned))
        .map(|(name, actual, _)| format!("{name}: {actual:?}"))
        .collect();
    assert!(wrong.is_empty(), "new hashes:\n{}", wrong.join("\n"));
    assert!(loaded.is_ok(), "{loaded:?}");
}
