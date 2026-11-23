//! Every theorem is sealed (D3722; docs/core.md, "Opaque definitions"): no
//! later declaration sees its proof. A cast along one still computes when its
//! ends agree (rule K, SW-4673), which needs only the proof's statement.

use std::path::Path;
use std::process::{Command, Stdio};

/// A cast along a theorem's proof, computed with: it takes its base by rule
/// K, from the statement's ends, never the hidden proof. `useTrans` chains
/// the sealed lemma inside a proof.
#[test]
fn a_cast_along_a_sealed_proof_computes_from_its_statement() {
    let probe = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../docs/proposals/sealed-theorems/switch.sw");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache", &probe.display().to_string()])
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "stderr:\n{stderr}");
}
