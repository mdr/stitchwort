//! Every theorem is sealed (D3722; docs/core.md, "Opaque definitions"): no
//! later declaration sees its proof, so a cast along one doesn't compute,
//! while a proof that only uses lemmas' statements still checks.

use std::path::Path;
use std::process::{Command, Stdio};

/// A cast along a theorem's proof, computed with: stuck, as the proof is
/// hidden. `useTrans` chains the sealed lemma inside a proof and checks.
#[test]
fn a_cast_along_a_sealed_proof_does_not_compute() {
    let probe = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../docs/proposals/sealed-theorems/switch.sw");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache", &probe.display().to_string()])
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "stderr:\n{stderr}");
    assert!(stderr.contains("E-REFL"), "stderr:\n{stderr}");
    assert!(stderr.contains("castComputes"), "stderr:\n{stderr}");
    assert!(
        stderr.contains("`flippedT` is a theorem: its proof is sealed"),
        "stderr:\n{stderr}"
    );
    assert!(!stderr.contains("unfolding flippedT"), "stderr:\n{stderr}");
    assert!(!stderr.contains("useTrans"), "stderr:\n{stderr}");
}
