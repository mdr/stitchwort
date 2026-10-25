//! `stitchwort dev opcode-census`
//! (docs/proposals/native-compilation.md, Appendix: N1 coverage census), end
//! to end with the built command, on the tail-call benchmark: its `spin` loop
//! is inside the N1 subset, and the entry's own glue (the `Delay` and the
//! `Nat` to text conversion for the print) is not.

use std::path::Path;
use std::process::{Command, Stdio};

#[test]
fn micro_tail_loop_fits_and_the_entry_glue_does_not() {
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../bench/native/micro_tail.sw");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["dev", "opcode-census"])
        .arg(&file)
        .arg("--no-cache")
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let out = String::from_utf8(output.stdout).unwrap();
    assert!(out.starts_with("island: BLOCKED "), "{out}");
    assert!(out.contains("Prim:Delay(Lift): 1, 1"), "{out}");
    assert!(out.contains("callee islands: FITS "), "{out}");
    assert!(out.contains("[fits] Main.spin: reachable=1"), "{out}");
}
