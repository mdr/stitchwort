//! `stitchwort oracle readings|builds` (SW-3111): each `.read` deleted, and
//! each build helper replaced by its proof, in turn, and what the check
//! makes of it.

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
    let dir = std::env::temp_dir().join(format!("stitchwort-oracle-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    dir
}

/// A `.read` that is needed (nothing else turns the test fact into `a = b`)
/// and one that is redundant (the fact is already the proposition); a
/// helper that is removable (the proof is accepted where the test fact is
/// expected) and one that is needed (the equation is an argument of
/// `Eq.sym`, where nothing says what to build).
const FIXTURE: &str = "\
namespace Laws

import Std (Nat, Bool, Eq)

theorem needed (a b: Nat) (same: (a == b) = True): a = b := same.read

theorem redundant (a b: Nat) (h: Nat.leq a b = True): Nat.leq a b = True := h.read

theorem removable (x: Bool) (h: x ≠ True): x = False := Bool.falseOfNotTrue x h

theorem helperNeeded (x: Bool) (h: x ≠ True): False = x := Eq.sym (Bool.falseOfNotTrue x h)
";

fn verdicts(result: &Value) -> Vec<(u64, String)> {
    result["sites"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| {
            (
                s["line"].as_u64().unwrap(),
                s["verdict"].as_str().unwrap().to_string(),
            )
        })
        .collect()
}

#[test]
fn oracle_readings_tells_a_needed_read_from_a_redundant_one() {
    let dir = scratch("readings");
    std::fs::write(dir.join("src/laws.sw"), FIXTURE).unwrap();
    let output = stitchwort(&dir, &["oracle", "readings", "src", "--json"]);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = json(&output);
    assert_eq!(result["half"], "readings");
    assert_eq!(result["status"], "clean");
    assert_eq!(
        verdicts(&result),
        [(5, "needed".to_string()), (7, "redundant".to_string())]
    );
    assert_eq!(result["summary"]["needed"], 1);
    assert_eq!(result["summary"]["removable"], 1);
    assert_eq!(result["summary"]["changed"], 0);
    // Nothing is written.
    assert_eq!(
        std::fs::read_to_string(dir.join("src/laws.sw")).unwrap(),
        FIXTURE
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn oracle_builds_lists_the_removable_helper_and_counts_the_needed_one() {
    let dir = scratch("builds");
    std::fs::write(dir.join("src/laws.sw"), FIXTURE).unwrap();
    let output = stitchwort(&dir, &["oracle", "builds", "src", "--json"]);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = json(&output);
    assert_eq!(
        verdicts(&result),
        [(9, "removable".to_string()), (11, "needed".to_string())]
    );
    let removable = result["removable"].as_array().unwrap();
    assert_eq!(removable.len(), 1);
    assert_eq!(removable[0]["file"], "src/laws.sw");
    assert_eq!(removable[0]["helper"], "Bool.falseOfNotTrue");
    assert_eq!(removable[0]["replacement"], "h");
    let helper = &result["summary"]["byHelper"]["Bool.falseOfNotTrue"];
    assert_eq!(
        (helper["needed"].as_u64(), helper["removable"].as_u64()),
        (Some(1), Some(1))
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--files` checks one file on its own and gives the same verdicts; a
/// `--limit` stops after that many sites.
#[test]
fn oracle_files_mode_and_limit() {
    let dir = scratch("files");
    std::fs::write(dir.join("laws.sw"), FIXTURE).unwrap();
    let output = stitchwort(&dir, &["oracle", "builds", "--files", "laws.sw", "--json"]);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = json(&output);
    assert_eq!(result["mode"], "file");
    assert_eq!(
        verdicts(&result),
        [(9, "removable".to_string()), (11, "needed".to_string())]
    );
    let output = stitchwort(
        &dir,
        &[
            "oracle", "builds", "--files", "laws.sw", "--json", "--limit", "1",
        ],
    );
    assert_eq!(verdicts(&json(&output)).len(), 1);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A project that doesn't check already is refused: a declaration that
/// fails before and after the edit would look redundant.
#[test]
fn oracle_refuses_a_project_that_does_not_check() {
    let dir = scratch("broken");
    let broken = format!("{FIXTURE}\ntheorem bad (n: Nat): n = 0 := rfl\n");
    std::fs::write(dir.join("src/laws.sw"), broken).unwrap();
    let output = stitchwort(&dir, &["oracle", "readings", "src", "--json"]);
    assert_eq!(output.status.code(), Some(2));
    assert_eq!(json(&output)["status"], "refused");
    let _ = std::fs::remove_dir_all(&dir);
}
