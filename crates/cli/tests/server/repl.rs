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

/// A project that allows open goals prints one line for them when a file
/// loads, not a box for each; errors in the project still print in full.
#[test]
fn open_goals_allowed_by_the_project_print_one_line() {
    let dir = std::env::temp_dir().join(format!("sw-repl-goals-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("make the project folder");
    std::fs::write(
        dir.join("stitchwort.yaml"),
        "sources: [src]\ncheck:\n  open-goals: warn\n",
    )
    .expect("write the config");
    std::fs::write(
        dir.join("src/Ex.sw"),
        "namespace Demo.Ex\n\ndef one: Nat := 1\n\ndef a: Nat := ?\n\ndef b: Nat := ?\n",
    )
    .expect("write Ex.sw");
    let evaluated = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["eval", "src/Ex.sw", "one"])
        .current_dir(&dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    let _ = std::fs::remove_dir_all(&dir);
    let stderr = String::from_utf8_lossy(&evaluated.stderr);
    assert!(evaluated.status.success(), "{stderr}");
    assert_eq!(String::from_utf8_lossy(&evaluated.stdout).trim(), "1: Nat");
    assert_eq!(
        stderr.trim(),
        "2 goals open, allowed by `check: open-goals: warn`; `stitchwort goal` lists them"
    );
}

/// `:t` on a declaration whose body is still `?` prints its type (the
/// header is checked); evaluating it is refused.
#[test]
fn type_only_works_on_a_declaration_with_an_open_goal() {
    let dir = std::env::temp_dir().join(format!("sw-repl-type-open-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("make the project folder");
    std::fs::write(
        dir.join("stitchwort.yaml"),
        "sources: [src]\ncheck:\n  open-goals: warn\n",
    )
    .expect("write the config");
    std::fs::write(
        dir.join("src/Ex.sw"),
        "namespace Demo.Ex\n\ndef a (n: Nat): Nat := ?\n",
    )
    .expect("write Ex.sw");
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["repl", "src/Ex.sw"])
        .current_dir(&dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start stitchwort repl");
    child
        .stdin
        .take()
        .expect("the REPL's input")
        .write_all(b":t a\na 1\n")
        .expect("write to the REPL");
    let output = child.wait_with_output().expect("run stitchwort repl");
    let _ = std::fs::remove_dir_all(&dir);
    let printed = String::from_utf8_lossy(&output.stdout);
    let errors = String::from_utf8_lossy(&output.stderr);
    assert!(
        printed.lines().any(|l| l == "a: Nat → Nat"),
        "expected `a: Nat → Nat` in:\n{printed}\n{errors}"
    );
    assert!(errors.contains("E-UNFINISHED"), "{errors}");
}
