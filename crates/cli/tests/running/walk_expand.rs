//! `check --expand-walk` end to end: the expansion it writes for every
//! walk of `examples/accept/walk.sw` checks again, as the walk did
//! (docs/syntax.md, "byWalking").

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
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("walk-expand");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/walk.sw");
    std::fs::copy(&source, dir.join("walk.sw")).expect("copy the example");

    let expand = output(
        common::cli_with("check", &["--expand-walk", "walk.sw"]),
        &dir,
    );
    let stderr = String::from_utf8_lossy(&expand.stderr);
    assert!(expand.status.success(), "--expand-walk failed:\n{stderr}");
    let trace = String::from_utf8_lossy(&expand.stdout).into_owned();
    let expanded = std::fs::read_to_string(dir.join("walk.sw")).expect("read the expansion");
    let left = (expanded.lines())
        .filter(|l| !l.trim_start().starts_with("--") && l.contains("byWalking"))
        .count();
    assert_eq!(left, 0, "a walk was left unexpanded:\n{expanded}");
    insta::assert_snapshot!("walk_expand_trace", trace);
    insta::assert_snapshot!("walk_expand_text", expanded);

    let check = output(common::cli_with("check", &["--no-cache", "walk.sw"]), &dir);
    assert!(
        check.status.success(),
        "the expansion doesn't check:\n{}{}",
        String::from_utf8_lossy(&check.stdout),
        String::from_utf8_lossy(&check.stderr)
    );
}
