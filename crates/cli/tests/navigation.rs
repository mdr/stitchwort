//! `stitchwort check --index` and `std-source`, end to end with the built
//! command (docs/proposals/code-navigation.md).

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn project(test: &str, files: &[(&str, &str)]) -> PathBuf {
    let base = std::env::temp_dir().join(format!("stitchwort-nav-{}-{test}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("proj");
    std::fs::create_dir_all(&dir).unwrap();
    for (path, text) in files {
        let full = dir.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    }
    dir
}

fn stitchwort(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

fn out(output: &Output) -> &str {
    std::str::from_utf8(&output.stdout).unwrap()
}

const FILES: &[(&str, &str)] = &[
    ("stitchwort.yaml", "sources: [src]\n"),
    (
        "src/Lib/Lib.sw",
        "namespace Lib\n\ntype Range = { lo: Nat, hi: Nat }\n\ndef Range.size (r: Range): Nat := r.hi + r.lo\n",
    ),
    (
        "src/Day/Day.sw",
        "namespace Day\n\nimport Lib (Range)\n\ndef width (r: Range): Nat := r.hi\n\ndef total (xs: List Nat): Nat := Lib.Range.size { lo = 0, hi = xs.length }\n",
    ),
];

#[test]
fn a_project_to_standard_output() {
    let dir = project("stdout", FILES);
    let output = stitchwort(&dir, &["check", "--index", "-"]);
    assert!(output.status.success());
    let json = out(&output);
    assert!(json.starts_with(r#"{"version":2,"errors":false,"files":["#));
    // Paths are within the project.
    assert!(json.contains(r#"{"path":"src/Day/Day.sw"}"#), "{json}");
    assert!(json.contains(r#"{"path":"src/Lib/Lib.sw"}"#), "{json}");
    // The import, a qualified name, a field and a library function.
    assert!(json.contains(r#""name":"Lib.Range","kind":"record","file":"#));
    assert!(json.contains(r#""name":"Lib.Range.size","kind":"def""#));
    assert!(json.contains(r#""name":"Lib.Range.hi","kind":"field""#));
    assert!(json.contains(r#""name":"Std.List.length","kind":"def""#));
    assert!(json.contains(r#""std":"core.sw""#));
}

#[test]
fn a_file_to_a_file() {
    let dir = project(
        "file",
        &[("one.sw", "def f (xs: List Nat): Nat := xs.length\n")],
    );
    let output = stitchwort(&dir, &["check", "--index", "out.json", "one.sw"]);
    assert!(output.status.success());
    assert!(out(&output).is_empty());
    let json = std::fs::read_to_string(dir.join("out.json")).unwrap();
    assert!(json.contains(r#"{"path":"one.sw"}"#), "{json}");
    assert!(json.contains(r#""binder":{"name":"xs","file":0,"range":[0,7,0,9]}"#));
}

#[test]
fn errors_still_write_the_index_and_fail() {
    let files = [
        ("stitchwort.yaml", "sources: [src]\n"),
        (
            "src/Day/Day.sw",
            "namespace Day\n\ndef ok (xs: List Nat): Nat := xs.length\n\ndef bad: Nat := missing\n",
        ),
    ];
    let dir = project("errors", &files);
    let output = stitchwort(&dir, &["check", "--index", "-"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(out(&output).starts_with(r#"{"version":2,"errors":true,"#));
    assert!(
        out(&output).contains(r#""diagnostics":[{"severity":"error","code":"E-UNKNOWN-NAME""#),
        "{}",
        out(&output)
    );
    assert!(out(&output).contains(r#""name":"Std.List.length""#));
}

#[test]
fn std_source_prints_embedded_files() {
    let dir = project("std", &[]);
    let output = stitchwort(&dir, &["std-source", "core.sw"]);
    assert!(output.status.success());
    assert!(out(&output).contains("type List"));
    let output = stitchwort(&dir, &["std-source", "List/Toolkit.sw"]);
    assert!(output.status.success());
    assert!(out(&output).contains("def List.map"));
    let output = stitchwort(&dir, &["std-source", "nope.sw"]);
    assert_eq!(output.status.code(), Some(1));
}
