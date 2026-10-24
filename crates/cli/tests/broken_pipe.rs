//! Output into a closed pipe (`stitchwort std-source … | head`) ends the
//! program quietly, with no panic message.

use std::process::{Command, Stdio};

#[cfg(unix)]
#[test]
fn printing_into_a_closed_pipe_does_not_panic() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["std-source", "List/Toolkit.sw"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawns");
    // The reader goes away before the program prints anything it can't buffer.
    drop(child.stdout.take());
    let output = child.wait_with_output().expect("finishes");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert!(!stderr.contains("Broken pipe"), "{stderr}");
}
