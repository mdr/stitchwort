//! `stitchwort sweep theorem-binders` (SW-2655): theorems' `∀` variables
//! moved before the colon, written only where the trial check keeps every
//! statement.

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
    let dir = std::env::temp_dir().join(format!("stitchwort-sweep-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn names(file: &Value, key: &str) -> Vec<String> {
    file[key]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| c["name"].as_str().unwrap().to_string())
        .collect()
}

/// `leAntisym` keeps its hash; `addZ` gains an argument, a new proof term,
/// which `limit` depends on, so it is refused; `memOf` has a `∀` after a
/// premise and is skipped.
const BEFORE: &str = "\
namespace Laws

import Std (Nat, Void, Bool, Eq)

theorem leAntisym: ∀ (a b: Nat) => a ≤ b → b ≤ a → a = b
  | Zero, Zero, h1, h2 => rfl
  | Zero, Succ b, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, h1, h2 => Eq.cong Succ (leAntisym a b h1 h2)

theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero

def checked (n: Nat) (same: n + 0 = n): Nat := n

def limit: Nat := checked 100 (addZ 100)

theorem memOf: ∀ (n: Nat) => 0 < n → ∀ (k: Nat) => k ≤ k + n := n h k => Nat.leAddRight k n
";

const AFTER: &str = "\
namespace Laws

import Std (Nat, Void, Bool, Eq)

theorem leAntisym (a b: Nat) (h1: a ≤ b) (h2: b ≤ a): a = b :=
  match a, b with
    | Zero, Zero => rfl
    | Zero, Succ b => Void.exfalso (Bool.falseNotTrue h2)
    | Succ a, Zero => Void.exfalso (Bool.falseNotTrue h1)
    | Succ a, Succ b => Eq.cong Succ (leAntisym a b h1 h2)

theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero
";

#[test]
fn sweep_theorem_binders_writes_only_what_keeps_its_statement() {
    let dir = scratch("project");
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(dir.join("src/laws.sw"), BEFORE).unwrap();

    let args = ["sweep", "theorem-binders", "src", "--dry-run", "--json"];
    let output = stitchwort(&dir, &args);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = json(&output);
    assert_eq!(result["version"], 1);
    assert_eq!(result["status"], "clean");
    assert_eq!(result["written"], false);
    let file = &result["files"][0];
    assert_eq!(file["file"], "src/laws.sw");
    assert_eq!(names(file, "converted"), ["leAntisym"]);
    assert_eq!(names(file, "refused"), ["addZ"]);
    assert!(
        file["refused"][0]["reason"]
            .as_str()
            .unwrap()
            .contains("limit"),
        "{file}"
    );
    assert_eq!(names(file, "skipped"), ["memOf"]);
    assert_eq!(file["skipped"][0]["reason"], "forall-after-premise");
    assert_eq!(
        std::fs::read_to_string(dir.join("src/laws.sw")).unwrap(),
        BEFORE
    );

    // Written, and formatted.
    let output = stitchwort(&dir, &["sweep", "theorem-binders", "src"]);
    assert_eq!(output.status.code(), Some(0));
    let text = std::fs::read_to_string(dir.join("src/laws.sw")).unwrap();
    assert!(text.starts_with(AFTER), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--files`: a single file outside any project is checked on its own.
#[test]
fn sweep_theorem_binders_files_checks_a_single_file_on_its_own() {
    const SINGLE_BEFORE: &str = "\
namespace Laws

import Std (Nat, Void, Bool, Eq)

theorem ident: ∀ (n: Nat) => n = n := n => rfl

theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero

def checked (n: Nat) (same: n + 0 = n): Nat := n

def limit: Nat := checked 100 (addZ 100)

theorem memOf: ∀ (n: Nat) => 0 < n → ∀ (k: Nat) => k ≤ k + n := n h k => Nat.leAddRight k n
";
    const SINGLE_AFTER: &str = "theorem ident (n: Nat): n = n := rfl";
    let dir = scratch("files");
    std::fs::write(dir.join("laws.sw"), SINGLE_BEFORE).unwrap();

    let args = [
        "sweep",
        "theorem-binders",
        "--files",
        "laws.sw",
        "--dry-run",
        "--json",
    ];
    let output = stitchwort(&dir, &args);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = json(&output);
    assert_eq!(result["mode"], "file");
    assert_eq!(result["status"], "clean");
    assert_eq!(result["written"], false);
    let file = &result["files"][0];
    assert_eq!(file["file"], "laws.sw");
    assert_eq!(names(file, "converted"), ["ident"]);
    assert_eq!(names(file, "refused"), ["addZ"]);
    assert_eq!(names(file, "skipped"), ["memOf"]);
    assert_eq!(
        std::fs::read_to_string(dir.join("laws.sw")).unwrap(),
        SINGLE_BEFORE
    );

    // Written, and formatted.
    let output = stitchwort(&dir, &["sweep", "theorem-binders", "--files", "laws.sw"]);
    assert_eq!(output.status.code(), Some(0));
    let text = std::fs::read_to_string(dir.join("laws.sw")).unwrap();
    assert!(text.contains(SINGLE_AFTER), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}
