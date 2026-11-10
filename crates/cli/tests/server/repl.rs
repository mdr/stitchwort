//! The REPL's commands, end to end: what a line typed at the prompt prints.

use std::io::Write;
use std::process::{Command, Stdio};

/// Runs `stitchwort repl` with `input` at the prompt, and returns what it
/// printed.
fn repl(input: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("repl")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start stitchwort repl");
    child
        .stdin
        .take()
        .expect("the REPL's input")
        .write_all(input.as_bytes())
        .expect("write to the REPL");
    child.wait_with_output().expect("run stitchwort repl")
}

#[test]
fn type_only_prints_the_expression_and_its_type() {
    let output = repl(":t 1 + 2\n");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stderr, b"");
    let printed = String::from_utf8(output.stdout).expect("output is UTF-8");
    assert!(
        printed.lines().any(|line| line == "1 + 2: Nat"),
        "expected `1 + 2: Nat` in:\n{printed}"
    );
}
