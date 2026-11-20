//! `check --expand-walk` end to end: the expansion it writes for every
//! walk of `examples/accept/walk.sw` and `walk-two-run.sw` checks again,
//! as the walk did (docs/syntax.md, "byWalking").

use std::path::Path;
use std::process::{Command, Output, Stdio};

use crate::common;

fn output(mut command: Command, dir: &Path) -> Output {
    command
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("start stitchwort")
}

#[test]
fn walk_expansions_check_again() {
    for (file, name) in [
        ("walk.sw", "walk_expand"),
        ("walk-two-run.sw", "walk_two_run_expand"),
    ] {
        expansion_checks_again(file, name);
    }
}

/// Expands the walks of `examples/accept/<file>`, snapshots the trace and
/// the text as `<name>_trace` and `<name>_text`, and checks the text.
fn expansion_checks_again(file: &str, name: &str) {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept")
        .join(file);
    std::fs::copy(&source, dir.join(file)).expect("copy the example");

    let expand = output(common::cli_with("check", &["--expand-walk", file]), &dir);
    let stderr = String::from_utf8_lossy(&expand.stderr);
    assert!(expand.status.success(), "--expand-walk failed:\n{stderr}");
    let trace = String::from_utf8_lossy(&expand.stdout).into_owned();
    let expanded = std::fs::read_to_string(dir.join(file)).expect("read the expansion");
    let left = (expanded.lines())
        .filter(|l| !l.trim_start().starts_with("--") && l.contains("byWalking"))
        .count();
    assert_eq!(left, 0, "a walk was left unexpanded:\n{expanded}");
    insta::assert_snapshot!(format!("{name}_trace"), trace);
    insta::assert_snapshot!(format!("{name}_text"), expanded);

    let check = output(common::cli_with("check", &["--no-cache", file]), &dir);
    assert!(
        check.status.success(),
        "the expansion of {file} doesn't check:\n{}{}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );
}

#[test]
fn walk_expand_stdout_leaves_the_file_alone() {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("walk-expand-stdout");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/walk.sw");
    std::fs::copy(&source, dir.join("in-place.sw")).expect("copy the example");
    std::fs::copy(&source, dir.join("stdout.sw")).expect("copy the example");
    let original = std::fs::read(dir.join("stdout.sw")).expect("read the copy");

    let in_place = output(
        common::cli_with("check", &["--expand-walk", "in-place.sw"]),
        &dir,
    );
    assert!(
        in_place.status.success(),
        "--expand-walk failed:\n{}",
        String::from_utf8_lossy(&in_place.stderr)
    );
    let written = std::fs::read(dir.join("in-place.sw")).expect("read the expansion");

    let printed = output(
        common::cli_with("check", &["--expand-walk", "--stdout", "stdout.sw"]),
        &dir,
    );
    assert!(
        printed.status.success(),
        "--expand-walk --stdout failed:\n{}",
        String::from_utf8_lossy(&printed.stderr)
    );
    let unchanged = std::fs::read(dir.join("stdout.sw")).expect("read the copy again");
    assert_eq!(
        original, unchanged,
        "--expand-walk --stdout changed the file"
    );
    assert_eq!(
        written, printed.stdout,
        "--expand-walk --stdout printed something other than the in-place expansion"
    );
    let trace = String::from_utf8_lossy(&printed.stderr);
    assert!(
        trace.contains("stdout.sw:") && trace.contains(": walk"),
        "the trace isn't on standard error:\n{trace}"
    );
}
