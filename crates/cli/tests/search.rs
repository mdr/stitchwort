//! `stitchwort search` (SW-915, docs/proposals/search.md draft 3 §4, §8
//! S1b; docs/syntax.md, "Lemma search"), end to end with the built command:
//! a project's lemmas and the library's, theorems and definitions marked by
//! kind (D2089), hidden helpers, the file scope, rewrite mode with `Iff` and
//! conditional equations, exit codes and the JSON contract, version 1.
//!
//! The library loads through one check cache the tests share (the first
//! fills it; writes are atomic), so each search after that takes well under
//! a second.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

/// Runs `stitchwort search ARGS` in `cwd`: (exit code, stdout, stderr).
fn search(cwd: &Path, args: &[&str]) -> (i32, String, String) {
    let cache = Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-cache");
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("search")
        .args(args)
        .arg("--cache-dir")
        .arg(&cache)
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

/// [`search`] with `--json`: (exit code, the report).
fn json(cwd: &Path, args: &[&str]) -> (i32, Value) {
    let mut all = args.to_vec();
    all.push("--json");
    let (code, out, err) = search(cwd, &all);
    let report = serde_json::from_str(&out).unwrap_or_else(|e| panic!("{e}: {out}\n{err}"));
    (code, report)
}

/// A fresh folder for one test.
fn folder(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-search-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// A project with one namespace, `Shapes`.
fn project(name: &str) -> PathBuf {
    let dir = folder(name);
    std::fs::write(dir.join("stitchwort.yaml"), "# for the search tests\n").unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("src/shapes.sw"),
        "namespace Shapes\n\n\
         type Shape = | Circle (r: Nat) | Square (side: Nat)\n\n\
         @[noReceiver]\n\
         def Shape.scale: Nat → Shape → Shape\n  \
         | k, Circle r => Circle (k * r)\n  \
         | k, Square a => Square (k * a)\n\n\
         theorem Shape.scaleOne: (s: Shape) → Shape.scale 1 s = s\n  \
         | Circle r => rfl\n  \
         | Square a => rfl\n",
    )
    .unwrap();
    dir
}

/// The results' names, and a field of each.
fn names(report: &Value) -> Vec<&str> {
    (report["results"].as_array().unwrap().iter())
        .map(|r| r["name"].as_str().unwrap())
        .collect()
}

fn result<'a>(report: &'a Value, name: &str) -> &'a Value {
    (report["results"].as_array().unwrap().iter())
        .find(|r| r["name"] == name)
        .unwrap_or_else(|| panic!("no {name} in {report}"))
}

#[test]
fn a_project_search_finds_its_own_lemmas_and_the_librarys() {
    let dir = project("own");
    // The project's names are in scope as `import Shapes (..)` brings them,
    // and each result says what to import.
    let (code, report) = json(&dir, &["Shape.scale _ _ = _"]);
    assert_eq!(code, 0, "{report}");
    let own = result(&report, "Shapes.Shape.scaleOne");
    assert_eq!(own["kind"], "theorem");
    assert_eq!(own["relation"], "instance");
    assert_eq!(own["place"], "conclusion");
    assert_eq!(own["import"], "import Shapes (Shape)");
    assert_eq!(
        own["file"],
        format!(
            "{}/src/shapes.sw",
            dir.file_name().unwrap().to_str().unwrap()
        )
    );
    assert_eq!(own["line"], 10);
    // The library, from the project's folder.
    let (code, report) = json(&dir, &["Nat.min _ _ ≤ _"]);
    assert_eq!(code, 0, "{report}");
    assert_eq!(names(&report)[0], "Std.Nat.minLeLeft");
    assert_eq!(report["results"][0]["import"], "import Std (Nat)");
    // From elsewhere, with --project.
    let (code, report) = json(
        Path::new("/"),
        &["Shape.scale _ _ = _", "--project", dir.to_str().unwrap()],
    );
    assert_eq!(code, 0, "{report}");
    assert_eq!(names(&report), ["Shapes.Shape.scaleOne"]);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn theorems_definitions_and_constructors_are_searched_and_marked() {
    let dir = project("kinds");
    let (code, report) = json(&dir, &["Nat → Shape → Shape"]);
    assert_eq!(code, 0, "{report}");
    let scale = result(&report, "Shapes.Shape.scale");
    assert_eq!(scale["kind"], "definition");
    assert_eq!(scale["place"], "whole");
    let (_, report) = json(&dir, &["Nat → Shape"]);
    assert_eq!(
        result(&report, "Shapes.Shape.Circle")["kind"],
        "constructor"
    );
    // Narrowed to theorems: no theorem has that type, and what the relaxed
    // pass finds is theorems with a premise of it (`f: Nat → a → b`).
    let (_, report) = json(&dir, &["Nat → Shape → Shape", "--theorems"]);
    assert_eq!(report["query"]["kinds"], serde_json::json!(["theorem"]));
    assert_eq!(report["searchTier"], "relaxed");
    for r in report["results"].as_array().unwrap() {
        assert_eq!(
            (&r["kind"], &r["place"]),
            (&"theorem".into(), &"premise".into()),
            "{r}"
        );
    }
    // An interface's law (a field whose type is a proposition) is a theorem.
    let (_, report) = json(&dir, &["Ord.compare ?x ?x = _", "--limit", "50"]);
    assert_eq!(result(&report, "Std.Ord.flip")["kind"], "theorem");
    // The human output names the kind too.
    let (code, out, _) = search(&dir, &["Nat → Shape → Shape", "--definitions"]);
    assert_eq!(code, 0);
    assert!(
        out.starts_with(" 1. Shapes.Shape.scale  definition · instance · whole\n"),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn hidden_helpers_are_searched_only_with_all() {
    let dir = folder("hidden");
    let (code, report) = json(&dir, &[r#""%""#]);
    assert_eq!(code, 1, "{report}");
    let (code, report) = json(&dir, &[r#""%""#, "--all", "--limit", "1"]);
    assert_eq!(code, 0, "{report}");
    assert!(report["total"].as_u64().unwrap() > 100, "{report}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn rewrite_mode_takes_iff_sides_and_conditional_equations() {
    let dir = folder("rewrite");
    let (code, report) = json(&dir, &["_ ∈ List.distinct _", "--rewrite"]);
    assert_eq!(code, 0, "{report}");
    let distinct = result(&report, "Std.List.memDistinct");
    assert_eq!(distinct["place"], "left");
    assert_eq!(distinct["equation"], "iff");
    // `Nat.minLeft: m ≤ n → Nat.min m n = m`: its premise is left open,
    // and counted.
    let (_, report) = json(&dir, &["Nat.min ?a ?b", "--rewrite"]);
    let min = result(&report, "Std.Nat.minLeft");
    assert_eq!(min["equation"], "eq");
    assert_eq!(min["premises"], 1);
    let _ = std::fs::remove_dir_all(&dir);
}

const FILE: &str = "\
import Std (List)

def twice (xs: List Nat): List Nat := List.append xs xs

theorem twiceLength (xs: List Nat): List.length (twice xs) = List.length xs + List.length xs :=
  List.lengthAppend xs xs

theorem broken (n: Nat): n = n + 1 := rfl
";

#[test]
fn a_file_is_searched_with_its_own_names_even_if_it_doesnt_check() {
    let dir = folder("file");
    std::fs::write(dir.join("a.sw"), FILE).unwrap();
    let (code, out, err) = search(&dir, &["List.length (twice _) = _", "a.sw"]);
    assert_eq!(code, 0, "{out}{err}");
    assert!(err.contains("E-REFL"), "{err}");
    assert!(
        err.contains("warning: the file doesn't check: only what checked is searched"),
        "{err}"
    );
    assert_eq!(
        out,
        " 1. Main.twiceLength  theorem · instance · conclusion\n    \
         (xs: List Nat) → List.length (twice xs) = List.length xs + List.length xs\n    \
         a.sw:5\n\
         1 result, filtered pass\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn exit_codes_say_found_none_or_refused() {
    let dir = folder("exit");
    let (code, report) = json(&dir, &["Nat.min _ _ ≤ _"]);
    assert_eq!(code, 0, "{report}");
    let (code, report) = json(&dir, &[r#""noSuchNameAnywhere""#]);
    assert_eq!(code, 1, "{report}");
    assert_eq!(report["total"], 0);
    // A pattern that doesn't elaborate, or is a hole on its own.
    let (code, report) = json(&dir, &["List.nope _"]);
    assert_eq!(code, 2, "{report}");
    assert_eq!(report["error"]["code"], "E-UNKNOWN-NAME");
    let (code, report) = json(&dir, &["_"]);
    assert_eq!(code, 2, "{report}");
    assert_eq!(report["error"]["code"], "E-SEARCH-PATTERN");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The query log (S1d): with `--log FILE` each search appends one line of
/// JSON, an error too; the overloaded `++` is searched as lists and texts
/// (SW-927), and the log has both readings.
#[test]
fn the_query_log_gets_a_line_per_search() {
    let dir = folder("log");
    let log = dir.join("searches.jsonl");
    let log_arg = log.display().to_string();
    let (code, _, err) = search(&dir, &["_ ++ _ = _", "--limit", "3", "--log", &log_arg]);
    assert_eq!(code, 0, "{err}");
    let (code, _, _) = search(&dir, &["List.nope _", "--log", &log_arg]);
    assert_eq!(code, 2);
    let text = std::fs::read_to_string(&log).unwrap();
    let lines: Vec<Value> = text
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    assert_eq!(lines.len(), 2, "{text}");
    let first = &lines[0];
    assert_eq!(first["log"], 1);
    assert_eq!(first["event"], "search");
    assert_eq!(first["query"], "_ ++ _ = _");
    assert_eq!(
        first["elaborated"],
        serde_json::json!(["List.append ?1 ?2 = ?3", "Text.append ?0 ?1 = ?2"])
    );
    let results = first["results"].as_array().unwrap();
    assert_eq!(results.len(), 3, "{first}");
    assert_eq!(results[0]["rank"], 1);
    assert!(results[0]["name"].is_string() && first["ms"].is_u64());
    assert_eq!(lines[1]["error"]["code"], "E-UNKNOWN-NAME");
    let _ = std::fs::remove_dir_all(&dir);
}

/// The JSON contract, version 1 (draft 3 §4.1): a search of a file's own
/// lemma, in full but for the library's size.
#[test]
fn the_json_contract() {
    let dir = folder("json");
    std::fs::write(dir.join("a.sw"), FILE).unwrap();
    let (code, out, _) = search(&dir, &["List.length (twice _) = _", "a.sw", "--json"]);
    assert_eq!(code, 0, "{out}");
    let mut report: Value = serde_json::from_str(&out).unwrap();
    assert!(
        report["budget"]["candidates"].as_u64().unwrap() > 3000,
        "{report}"
    );
    report["budget"]["candidates"] = "(the library's size)".into();
    insta::assert_snapshot!(serde_json::to_string_pretty(&report).unwrap());
    // The instance double search: found both ways, listed once.
    let (_, report) = json(&dir, &["Ord.compare (?x: Nat) ?x = _", "--limit", "100"]);
    let generic = result(&report, "Std.Ord.compareSelf");
    assert_eq!(generic["via"], serde_json::json!(["generic"]));
    assert_eq!(
        result(&report, "Std.Nat.compareSelf")["via"],
        serde_json::json!(["resolved"])
    );
    let _ = std::fs::remove_dir_all(&dir);
}

const GOALS: &str = "\
import Std (Nat)

theorem swap (m: Nat) (n: Nat): m + n = n + m := ?

theorem chain (a: Nat) (b: Nat) (c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c := ?

theorem wrong (m: Nat): m + 1 = m := ?
";

/// `search --at` (stage 2): a goal by line or by index, exit codes, and the
/// JSON contract's snapshot.
#[test]
fn what_closes_a_goal() {
    let dir = folder("at");
    std::fs::write(dir.join("goals.sw"), GOALS).unwrap();
    let (code, out, err) = search(&dir, &["--at", "goals.sw:3", "--limit", "2"]);
    assert_eq!(code, 0, "{out}{err}");
    assert!(out.contains(" 1. Nat.addComm m n  [exact]"), "{out}");
    let (code, report) = json(&dir, &["--at", "goals.sw", "--goal", "2", "--limit", "1"]);
    assert_eq!(code, 0, "{report}");
    assert_eq!(report["goal"]["line"], 5);
    assert_eq!(report["results"][0]["proof"], "Nat.leTrans a b c h1 h2");
    let mut report = report;
    report["budget"]["candidates"] = "(the library's size)".into();
    report["budget"]["checks"] = "(varies)".into();
    insta::assert_snapshot!(serde_json::to_string_pretty(&report).unwrap());
    // Nothing closes a false goal: 1. No goal there, or a query too: 2.
    let (code, report) = json(&dir, &["--at", "goals.sw:7"]);
    assert_eq!(code, 1, "{report}");
    assert_eq!(report["total"]["closing"], 0);
    let (code, report) = json(&dir, &["--at", "goals.sw:4"]);
    assert_eq!(code, 2, "{report}");
    assert_eq!(report["error"]["code"], "E-SEARCH-AT");
    let (code, _, _) = search(&dir, &["_ = _", "--at", "goals.sw:3"]);
    assert_eq!(code, 2);
    let _ = std::fs::remove_dir_all(&dir);
}
