//! `doc` and `search` for generated equations (SW-1067,
//! docs/proposals/function-equations.md §3.4, stage 1c): the Equations
//! section with its stuck marks and skipped reasons, the Theorems groups
//! without them, and `search`'s `generated` flag.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

/// Runs `stitchwort COMMAND ARGS` in `cwd`: (exit code, stdout, stderr).
fn run(command: &str, cwd: &Path, args: &[&str]) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg(command)
        .args(args)
        .arg("--cache-dir")
        .arg(Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-cache"))
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn folder(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-eqdoc-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

const FILE: &str = "\
import Std (Nat, Option)

def kind: Nat → Nat
  | 3 => 1
  | 7 => 2
  | n => 0

type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def explode (depth: Nat): Number → Option Nat
  | Regular _ => None
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then Some (a + b) else None
  | Pair left right =>
    match explode (depth + 1) left with
      | Some n => Some n
      | None => explode (depth + 1) right

theorem kindOfThree: kind 3 = 1 := rfl
";

fn theorem_names(report: &Value) -> Vec<&str> {
    (report["theorems"]["shown"].as_array().unwrap().iter())
        .map(|t| t["name"].as_str().unwrap())
        .collect()
}

/// `doc` lists a definition's generated equations in their own section, the
/// stuck ones marked, with what wasn't generated and why; the Theorems
/// section has only the written theorem.
#[test]
fn doc_lists_generated_equations_in_their_own_section() {
    let dir = folder("section");
    std::fs::write(dir.join("a.sw"), FILE).unwrap();
    let (code, out, err) = run("doc", &dir, &["kind", "a.sw"]);
    assert_eq!(code, 0, "{out}\n{err}");
    assert!(out.contains("Equations: 3 generated equations\n"), "{out}");
    assert!(out.contains("kind.eq1  kind 3 = 1   (a.sw:4)"), "{out}");
    assert!(out.contains("kind.eq2  kind 7 = 2   (a.sw:5)"), "{out}");
    assert!(
        out.contains("kind.eq3  n ≠ 3 → n ≠ 7 → kind n = 0  [stuck]   (a.sw:6)"),
        "{out}"
    );
    let theorems = out.split("Theorems:").nth(1).expect("a Theorems section");
    assert!(theorems.contains("Main.kindOfThree"), "{out}");
    assert!(!theorems.contains("kind.eq"), "{out}");

    let (code, out, err) = run("doc", &dir, &["kind", "a.sw", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let equations = &report["equations"];
    assert_eq!(equations["total"], 3);
    let shown = equations["shown"].as_array().unwrap();
    let names: Vec<&str> = shown.iter().map(|e| e["name"].as_str().unwrap()).collect();
    assert_eq!(names, ["Main.kind.eq1", "Main.kind.eq2", "Main.kind.eq3"]);
    let stuck: Vec<bool> = shown
        .iter()
        .map(|e| e["stuck"].as_bool().unwrap())
        .collect();
    assert_eq!(stuck, [false, false, true]);
    assert_eq!(shown[2]["line"], 6);
    assert_eq!(theorem_names(&report), ["Main.kindOfThree"]);
    let _ = std::fs::remove_dir_all(&dir);
}

/// An arm that couldn't be stated is listed with its reason, and so is an
/// `f.induct` that wasn't made (here because `eq3` is read per leaf,
/// SW-1071).
#[test]
fn doc_says_which_equations_were_not_generated_and_why() {
    let dir = folder("skipped");
    std::fs::write(dir.join("a.sw"), FILE).unwrap();
    let (code, out, err) = run("doc", &dir, &["explode", "a.sw", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let skipped = report["equations"]["skipped"].as_array().unwrap();
    let names: Vec<&str> = (skipped.iter())
        .map(|s| s["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        names,
        ["Main.explode.eq3", "Main.explode.induct"],
        "{report}"
    );
    assert!(
        skipped
            .iter()
            .all(|s| s["reason"].as_str().unwrap().len() > 20)
    );
    assert!(report["equations"]["induct"].is_null(), "{report}");
    let (_, out, _) = run("doc", &dir, &["explode", "a.sw"]);
    assert!(
        out.contains("Not generated:\n  Main.explode.eq3  "),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A library definition's equations are made on demand and listed: the
/// second arm of `filter` has no hypothesis, so it isn't stuck. Its
/// `f.induct` is listed first but isn't counted as an equation (SW-1073).
#[test]
fn a_library_definition_lists_its_equations() {
    let dir = folder("library");
    let (code, out, err) = run("doc", &dir, &["List.filter", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let equations = &report["equations"];
    assert_eq!(equations["total"], 2, "{report}");
    assert_eq!(equations["shown"].as_array().unwrap().len(), 2, "{report}");
    assert_eq!(equations["shown"][1]["name"], "List.filter.eq2");
    assert_eq!(equations["shown"][1]["stuck"], false);
    assert_eq!(equations["shown"][1]["file"], "std/List/Toolkit.sw");
    assert_eq!(
        equations["induct"]["name"], "List.filter.induct",
        "{report}"
    );
    assert!(theorem_names(&report).iter().all(|n| !n.contains(".eq")));
    let (code, out, err) = run("doc", &dir, &["List.filter"]);
    assert_eq!(code, 0, "{out}\n{err}");
    assert!(
        out.contains("Equations: 2 generated equations and f.induct\n  List.filter.induct  "),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `search` flags a generated equation, in JSON and in the text, and ranks
/// it after the written theorem about the same call.
#[test]
fn search_flags_generated_equations() {
    let dir = folder("search");
    std::fs::write(dir.join("a.sw"), FILE).unwrap();
    let (code, out, err) = run("search", &dir, &["kind", "a.sw", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let results = report["results"].as_array().unwrap();
    let find = |name: &str| results.iter().position(|r| r["name"] == name);
    let written = find("Main.kindOfThree").expect("the written theorem");
    let generated = find("Main.kind.eq1").expect("the equation");
    assert!(written < generated, "{report}");
    assert!(results[written].get("generated").is_none());
    assert_eq!(results[generated]["generated"], true);
    let (_, text, _) = run("search", &dir, &["kind", "a.sw"]);
    assert!(
        text.contains("Main.kind.eq1  theorem · generated"),
        "{text}"
    );
    assert!(
        !text.contains("Main.kindOfThree  theorem · generated"),
        "{text}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
