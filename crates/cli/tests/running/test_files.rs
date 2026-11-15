//! `stitchwort test FILE` for a file of a project: the file is tested in its
//! project, and only the tests it declares run (SW-3390).

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// A fresh folder for one test.
fn work_dir(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("test-files")
        .join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    dir
}

/// A project with a library, and two files of one namespace each declaring
/// a test: the file named on the command line imports the library, so it
/// can only be tested in the project.
fn project(name: &str) -> PathBuf {
    let dir = work_dir(name).join("proj");
    std::fs::create_dir_all(dir.join("src/Tests")).expect("make the project");
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").expect("write");
    std::fs::write(
        dir.join("src/Lib.sw"),
        "namespace Lib\n\ndef answer: Nat := 42\n",
    )
    .expect("write");
    std::fs::write(
        dir.join("src/Tests/First.sw"),
        "namespace Tests\n\nimport Lib (answer)\n\ntest \"first\" := answer == 42\n",
    )
    .expect("write");
    std::fs::write(
        dir.join("src/Tests/Second.sw"),
        "namespace Tests\n\ntest \"second\" := True\n",
    )
    .expect("write");
    dir
}

/// Runs `stitchwort test --no-cache ARGS` in `cwd` and gives its output.
fn test(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["test", "--no-cache"])
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort test")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

#[test]
fn a_project_files_tests_run_in_the_project() {
    let dir = project("file-in-project");
    let output = test(&dir, &["src/Tests/First.sw"]);
    let stderr = text(&output.stderr);
    let stdout = text(&output.stdout);
    assert!(output.status.success(), "{stderr}");
    assert!(stdout.contains("first"), "{stdout}");
    assert!(
        !stdout.contains("second"),
        "only the tests of the file named run:\n{stdout}"
    );
}

#[test]
fn a_project_files_tests_run_with_the_project_flag() {
    let dir = project("file-with-project");
    let output = test(
        dir.parent().unwrap(),
        &["--project", "proj", "proj/src/Tests/First.sw"],
    );
    let stderr = text(&output.stderr);
    let stdout = text(&output.stdout);
    assert!(output.status.success(), "{stderr}");
    assert!(stdout.contains("first"), "{stdout}");
    assert!(
        !stdout.contains("second"),
        "only the tests of the file named run:\n{stdout}"
    );
}

#[test]
fn a_file_outside_a_project_stays_file_mode() {
    let dir = work_dir("file-alone");
    let path = dir.join("alone.sw");
    std::fs::write(&path, "namespace Alone\n\ntest \"alone\" := True\n").expect("write");
    let output = test(&dir, &["alone.sw"]);
    let stderr = text(&output.stderr);
    let stdout = text(&output.stdout);
    assert!(output.status.success(), "{stderr}");
    assert!(stdout.contains("alone"), "{stdout}");
}
