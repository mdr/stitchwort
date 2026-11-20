//! `stitchwort dev tree`: its exit status is the thing the self-hosted
//! formatter's tree stage compares (`dev/fmt-twin tree`), so a declaration
//! that doesn't parse must fail the dump even when the tree still reads back.

use std::process::{Command, Stdio};

fn dev_tree(name: &str, source: &str) -> std::process::Output {
    let dir =
        std::env::temp_dir().join(format!("stitchwort-dev-tree-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("make a folder");
    let file = dir.join("input.sw");
    std::fs::write(&file, source).expect("write the input");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["dev", "tree", "--print"])
        .arg(&file)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    std::fs::remove_dir_all(&dir).ok();
    output
}

#[test]
fn a_declaration_that_does_not_parse_exits_one() {
    // The error is inside the declaration's body, so the declaration's root
    // is still a `Def` and the tree reads back: only the parse error says it
    // failed.
    let output = dev_tree(
        "parse-error",
        "def twice (n: Nat): Nat :=\n  let with := n + n\n  with\n",
    );
    assert_eq!(output.status.code(), Some(1));
    let out = String::from_utf8(output.stdout).unwrap();
    assert!(out.contains("\n    Error\n"), "{out}");
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn a_file_that_parses_exits_zero() {
    let output = dev_tree("parses", "def x: Nat := 1\n");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let out = String::from_utf8(output.stdout).unwrap();
    assert!(out.contains("Def\n  def\n  x\n"), "{out}");
    assert!(out.contains("1 files (0 not read back)"), "{out}");
}
