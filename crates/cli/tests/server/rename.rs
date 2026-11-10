//! `stitchwort rename` end to end (SW-2630, docs/proposals/refactoring.md):
//! the exit status, the files written and the JSON.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

const SHOP: &str = "\
namespace Shop

def limit: Nat := 100

def cap (n: Nat): Nat := n + limit

def step (count: Nat): Nat :=
  let next := count + 1
  next * 2

def size (xs: List Nat): Nat := xs.length
";

const REPORT: &str = "\
namespace Shop.Report

import Shop (cap, step)

def report: Nat := cap (step 3)

test \"report\" := report == 108
";

fn project(test: &str) -> PathBuf {
    let base =
        std::env::temp_dir().join(format!("stitchwort-rename-{}-{test}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("proj");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/shop.sw"), SHOP).unwrap();
    std::fs::write(dir.join("src/report.sw"), REPORT).unwrap();
    dir
}

fn rename(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("rename")
        .args(args)
        .arg("--no-cache")
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

fn out(output: &Output) -> &str {
    std::str::from_utf8(&output.stdout).unwrap()
}

fn read(dir: &Path, file: &str) -> String {
    std::fs::read_to_string(dir.join(file)).unwrap()
}

#[test]
fn a_function_used_in_two_files_is_renamed() {
    let dir = project("clean");
    let output = rename(&dir, &["Shop.step", "advance"]);
    assert_eq!(output.status.code(), Some(0), "{}", out(&output));
    assert!(out(&output).contains("renamed `step` to `advance`: 3 places in 2 files"));
    assert!(read(&dir, "src/shop.sw").contains("def advance (count: Nat)"));
    let report = read(&dir, "src/report.sw");
    assert!(report.contains("import Shop (cap, advance)"), "{report}");
    assert!(report.contains("cap (advance 3)"), "{report}");
}

/// `n` in `cap`, renamed to the global `limit`, would turn `n + limit` into
/// `limit + limit`.
const CAPTURE: &str = "src/shop.sw:5:10";

#[test]
fn a_rename_that_captures_a_global_is_refused_with_the_declaration() {
    let dir = project("capture");
    let output = rename(&dir, &[CAPTURE, "limit"]);
    assert_eq!(output.status.code(), Some(1), "{}", out(&output));
    assert!(
        out(&output).contains("would change what `cap` means"),
        "{}",
        out(&output)
    );
    assert!(out(&output).contains("nothing was written"));
    assert_eq!(read(&dir, "src/shop.sw"), SHOP);
}

#[test]
fn anyway_applies_it_and_reports_what_is_left() {
    let dir = project("anyway");
    let output = rename(&dir, &[CAPTURE, "limit", "--anyway"]);
    assert_eq!(output.status.code(), Some(3), "{}", out(&output));
    assert!(out(&output).contains("would change what `cap` means"));
    assert!(read(&dir, "src/shop.sw").contains("def cap (limit: Nat): Nat := limit + limit"));
}

#[test]
fn a_standard_library_name_is_refused_even_with_anyway() {
    let dir = project("std");
    let output = rename(&dir, &["Std.List.length", "count", "--anyway"]);
    assert_eq!(output.status.code(), Some(2));
    let err = String::from_utf8_lossy(&output.stderr);
    assert!(err.contains("standard library"), "{err}");
    assert_eq!(read(&dir, "src/shop.sw"), SHOP);
}

#[test]
fn a_type_or_a_bad_name_is_refused() {
    let dir = project("bad");
    let output = rename(&dir, &["Shop.step", "def"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("keyword"));
}

#[test]
fn json_lists_the_edits_and_the_problems() {
    let dir = project("json");
    let output = rename(&dir, &[CAPTURE, "limit", "--json"]);
    assert_eq!(output.status.code(), Some(1));
    let json: serde_json::Value = serde_json::from_str(out(&output)).unwrap();
    assert_eq!(json["status"], "not-applied");
    assert_eq!(json["applied"], false);
    assert_eq!(json["edits"].as_array().unwrap().len(), 2);
    assert_eq!(json["edits"][0]["file"], "src/shop.sw");
    assert_eq!(json["edits"][0]["line"], 5);
    let problem = &json["problems"][0];
    assert_eq!(problem["kind"], "changed-meaning");
    assert_eq!(problem["declaration"], "cap");
    assert_eq!(problem["file"], "src/shop.sw");
    assert_eq!(problem["line"], 5);
    assert_eq!(json["refusals"].as_array().unwrap().len(), 0);

    let output = rename(&dir, &["Std.List.length", "count", "--json"]);
    assert_eq!(output.status.code(), Some(2));
    let json: serde_json::Value = serde_json::from_str(out(&output)).unwrap();
    assert_eq!(json["status"], "refused");
    assert!(
        json["refusals"][0]["message"]
            .as_str()
            .unwrap()
            .contains("standard library")
    );
}

#[test]
fn dry_run_writes_nothing() {
    let dir = project("dry");
    let output = rename(&dir, &["Shop.step", "advance", "--dry-run"]);
    assert_eq!(output.status.code(), Some(0), "{}", out(&output));
    assert!(out(&output).contains("would rename `step` to `advance`"));
    assert!(
        out(&output).contains("src/report.sw:3:19"),
        "{}",
        out(&output)
    );
    assert_eq!(read(&dir, "src/shop.sw"), SHOP);
    assert_eq!(read(&dir, "src/report.sw"), REPORT);
}
