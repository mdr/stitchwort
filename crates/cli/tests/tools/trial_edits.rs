//! `stitchwort trial-edits` and `stitchwort hash` (SW-2648, SW-2647): the
//! trial check for arbitrary edits, and for an edited copy of the library.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use serde_json::Value;

fn stitchwort(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

fn json(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|e| {
        panic!(
            "not JSON ({e}): {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-trial-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

const BEFORE: &str = "\
namespace Laws

import Std (Nat)

theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero

def limit: Nat := 100
";

/// The same theorem moved to the header: another proof term. The edits are
/// the whole file.
const AFTER: &str = "\
namespace Laws

import Std (Nat)

theorem addZ (n: Nat): n + 0 = n := Nat.addZero n

def limit: Nat := 100
";

fn names(value: &Value, key: &str) -> Vec<String> {
    value[key]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| c["name"].as_str().unwrap().to_string())
        .collect()
}

#[test]
fn trial_edits_reports_by_promise_and_applies_only_when_asked() {
    let dir = scratch("project");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/laws.sw"), BEFORE).unwrap();
    let edits = serde_json::json!([{ "file": "src/laws.sw", "text": AFTER }]);
    std::fs::write(dir.join("edits.json"), edits.to_string()).unwrap();

    // The same meaning: the proof term moved, so the hash did.
    let output = stitchwort(&dir, &["trial-edits", "edits.json", "--json"]);
    assert_eq!(output.status.code(), Some(1));
    let result = json(&output);
    assert_eq!(result["version"], 1);
    assert_eq!(result["status"], "problems");
    assert_eq!(result["promise"], "same-meaning");
    assert_eq!(result["applied"], false);
    assert_eq!(names(&result, "changed"), ["addZ"]);

    // The same statement: accepted, and still not written.
    let args = ["trial-edits", "edits.json", "--same-statement", "--json"];
    let output = stitchwort(&dir, &args);
    assert_eq!(output.status.code(), Some(0));
    let result = json(&output);
    assert_eq!(result["status"], "clean");
    assert_eq!(result["proofsChanged"], serde_json::json!(["Laws.addZ"]));
    assert_eq!(
        std::fs::read_to_string(dir.join("src/laws.sw")).unwrap(),
        BEFORE
    );

    // Written on request; the hashes then are those the trial checked.
    let args = [
        "trial-edits",
        "edits.json",
        "--same-statement",
        "--apply",
        "--json",
    ];
    let result = json(&stitchwort(&dir, &args));
    assert_eq!(result["applied"], true);
    assert_eq!(
        std::fs::read_to_string(dir.join("src/laws.sw")).unwrap(),
        AFTER
    );
    let hashes = json(&stitchwort(&dir, &["hash", "--json", "Laws.addZ"]));
    let decl = &hashes["declarations"][0];
    assert_eq!(decl["kind"], "theorem");
    assert_eq!(decl["hash"].as_str().unwrap().len(), 64);
    assert_eq!(decl["typeHash"].as_str().unwrap().len(), 64);

    // A definition's body is not allowed to change under either promise.
    let body = AFTER.replace("Nat := 100", "Nat := 101");
    let edits = serde_json::json!([{ "file": "src/laws.sw", "text": body }]);
    std::fs::write(dir.join("edits.json"), edits.to_string()).unwrap();
    for flags in [&["--json"][..], &["--same-statement", "--json"][..]] {
        let mut args = vec!["trial-edits", "edits.json"];
        args.extend(flags);
        let output = stitchwort(&dir, &args);
        assert_eq!(output.status.code(), Some(1));
        assert_eq!(names(&json(&output), "changed"), ["limit"]);
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// An edited copy of the library: one theorem given another proof of the
/// same statement. The original is the library this run reads.
#[test]
fn trial_edits_compares_an_edited_library_with_the_original() {
    let std = Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std");
    let copy = scratch("std");
    copy_dir(&std, &copy);
    let file = copy.join("Bool/ToNat.sw");
    let text = std::fs::read_to_string(&file).unwrap();
    let before = "theorem Bool.toNatOdd (b: Bool): (b.toNat % 2 == 1) = b :=\n  match b with\n    | False => rfl";
    let after = "theorem Bool.toNatOdd (b: Bool): (b.toNat % 2 == 1) = b :=\n  match b with\n    | False => Eq.sym rfl";
    assert!(text.contains(before));
    std::fs::write(&file, text.replace(before, after)).unwrap();

    let copy_arg = copy.display().to_string();
    let cwd = scratch("std-cwd");
    let output = stitchwort(&cwd, &["--std-dir", &copy_arg, "trial-edits", "--json"]);
    assert_eq!(output.status.code(), Some(1));
    let result = json(&output);
    assert_eq!(result["mode"], "std");
    assert_eq!(names(&result, "changed"), ["Std.Bool.toNatOdd"]);
    assert_eq!(result["changed"][0]["kind"], "theorem");

    let args = [
        "--std-dir",
        &copy_arg,
        "trial-edits",
        "--same-statement",
        "--json",
    ];
    let output = stitchwort(&cwd, &args);
    assert_eq!(output.status.code(), Some(0));
    let result = json(&output);
    assert_eq!(result["status"], "clean");
    assert_eq!(
        result["proofsChanged"],
        serde_json::json!(["Std.Bool.toNatOdd"])
    );
    let _ = std::fs::remove_dir_all(&copy);
    let _ = std::fs::remove_dir_all(&cwd);
}

fn copy_dir(from: &Path, to: &Path) {
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            std::fs::create_dir_all(&target).unwrap();
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), target).unwrap();
        }
    }
}
