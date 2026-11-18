//! A missing standard library is a setup error the command reports, not a
//! panic (SW-1142).

use std::path::Path;
use std::process::{Command, Output, Stdio};

/// Runs `stitchwort` with `STITCHWORT_STD_DIR` naming `dir`.
fn stitchwort_with_std_dir(dir: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .env("STITCHWORT_STD_DIR", dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// `STITCHWORT_STD_DIR` naming a directory that doesn't exist: one clear
/// error saying what was looked for and how to point at a copy, exit 2, and
/// no panic text or backtrace note.
#[test]
fn a_missing_std_dir_is_a_clean_error() {
    let missing = "/nonexistent/stitchwort-std-for-test";
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/abort.sw");
    let output = stitchwort_with_std_dir(
        missing,
        &["check", &example.display().to_string(), "--no-cache"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(
        stderr.contains("the standard library at"),
        "stderr:\n{stderr}"
    );
    assert!(stderr.contains(missing), "stderr:\n{stderr}");
    assert!(stderr.contains("--std-dir"), "stderr:\n{stderr}");
    assert!(stderr.contains("STITCHWORT_STD_DIR"), "stderr:\n{stderr}");
    assert!(!stderr.contains("panicked"), "stderr:\n{stderr}");
    assert!(!stderr.contains("RUST_BACKTRACE"), "stderr:\n{stderr}");
}

/// `test --std Nat/Iterate.sw` runs the tests declared in that file and no
/// others, and a target that names no library file fails.
#[test]
fn test_std_runs_one_library_namespace_s_tests() {
    let run = |args: &[&str]| {
        let mut all = vec!["test", "--std"];
        all.extend_from_slice(args);
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(all)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort")
    };
    let output = run(&["Nat/Iterate.sw"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "stdout:\n{stdout}");
    assert!(stdout.contains("Nat.iterate dot"), "stdout:\n{stdout}");
    assert!(stdout.contains("2 test(s): 2 passed"), "stdout:\n{stdout}");
    assert!(!stdout.contains("divSuccStep"), "stdout:\n{stdout}");

    let output = run(&["Nope"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stderr:\n{stderr}");
    assert!(stderr.contains("E-STD-TARGET"), "stderr:\n{stderr}");
}
