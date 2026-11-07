//! `stitchwort dev opcode-census`
//! (docs/proposals/native-compilation.md, Appendix: N1 coverage census), end
//! to end with the built command, on the tail-call benchmark: its `spin` loop
//! is inside the N1 subset, and so is the entry's own glue: native N4
//! compiles every reached body (effects and handlers included), so no
//! island is blocked any more.

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
    assert!(out.starts_with("island: FITS "), "{out}");
    assert!(out.contains("blocked_bodies=0"), "{out}");
    assert!(!out.contains("Prim:Delay"), "{out}");
    assert!(out.contains("callee islands: FITS "), "{out}");
    assert!(out.contains("[fits] Main.spin: reachable=1"), "{out}");
}
