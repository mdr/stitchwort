//! `STITCHWORT_SEAL_THEOREMS=1` makes every theorem opaque to what follows
//! it (SW-4657, docs/proposals/sealed-theorems.md, stage 0); off, nothing
//! changes.

use std::path::Path;
use std::process::{Command, Output, Stdio};

fn check_probe(seal: bool) -> Output {
    let probe = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../docs/proposals/sealed-theorems/switch.sw");
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command
        .args(["check", "--no-cache", &probe.display().to_string()])
        .stdin(Stdio::null());
    if seal {
        // The library's own `Decidable.symThenSelf` compares two proofs, so
        // it needs these two unsealed (docs/proposals/sealed-theorems.md,
        // "Stage 0 results").
        command
            .env("STITCHWORT_SEAL_THEOREMS", "1")
            .env("STITCHWORT_SEAL_EXCEPT", "Std.Eq.trans,Std.Eq.flipped");
    }
    command.output().expect("run stitchwort")
}

#[test]
fn the_probe_checks_with_the_switch_off() {
    let output = check_probe(false);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stderr:\n{stderr}");
}

/// A cast along a theorem's proof, computed with: stuck once the proof is
/// hidden. `useTrans` chains the sealed lemma inside a proof and still checks.
#[test]
fn the_switch_seals_the_proof_a_cast_computes_with() {
    let output = check_probe(true);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "stderr:\n{stderr}");
    assert!(stderr.contains("E-REFL"), "stderr:\n{stderr}");
    assert!(stderr.contains("castComputes"), "stderr:\n{stderr}");
    assert!(!stderr.contains("useTrans"), "stderr:\n{stderr}");
}
