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

/// A project file's imports of the project's other namespaces resolve, and
/// the file's own names are in scope.
#[test]
fn a_project_file_is_loaded_with_its_project() {
    let dir = std::env::temp_dir().join(format!("sw-repl-project-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("make the project folder");
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").expect("write the config");
    std::fs::write(
        dir.join("src/Base.sw"),
        "namespace Demo.Base\n\ndef one: Nat := 1\n",
    )
    .expect("write Base.sw");
    std::fs::write(
        dir.join("src/Top.sw"),
        "namespace Demo.Top\nimport Demo.Base (one)\n\ndef two: Nat := one + one\n",
    )
    .expect("write Top.sw");
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(args)
            .current_dir(&dir)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort")
    };
    let evaluated = run(&["eval", "src/Top.sw", "two"]);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        evaluated.status.success(),
        "{}",
        String::from_utf8_lossy(&evaluated.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&evaluated.stdout).trim(), "2: Nat");
}
