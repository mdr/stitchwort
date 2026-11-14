//! `stitchwort doc NAME` (SW-1019, docs/proposals/documentation.md §5.3 to
//! §5.5, stage 1b), end to end with the built command: name resolution, the
//! header as written, the doc, examples by name (D2144), theorems about the
//! name with their groups and cap, the scope of a project name (D2146),
//! `--theorems 0` without a check (D2152), namespaces and every kind of
//! declaration.
//!
//! The library loads through the check cache the search tests share (the
//! first fills it; writes are atomic), so each `doc` after that takes well
//! under a second.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

/// Runs `stitchwort doc ARGS` in `cwd`: (exit code, stdout, stderr).
fn doc_in(cwd: &Path, cache: &Path, args: &[&str]) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("doc")
        .args(args)
        .arg("--cache-dir")
        .arg(cache)
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

fn shared_cache() -> PathBuf {
    Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-cache")
}

/// [`doc_in`] from a folder with no project, with the shared cache.
fn doc(args: &[&str]) -> (i32, String, String) {
    let cwd = folder("neutral");
    let out = doc_in(&cwd, &shared_cache(), args);
    let _ = std::fs::remove_dir_all(&cwd);
    out
}

/// [`doc`] with `--json`: (exit code, the report).
fn json(args: &[&str]) -> (i32, Value) {
    let mut all = args.to_vec();
    all.push("--json");
    let (code, out, err) = doc(&all);
    let report = serde_json::from_str(&out).unwrap_or_else(|e| panic!("{e}: {out}\n{err}"));
    (code, report)
}

/// A fresh folder for one test.
fn folder(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-doc-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// How many cached results there are under `dir`, which may not exist (its
/// `header` file only says which version wrote it).
fn files_under(dir: &Path) -> usize {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return 0;
    };
    entries
        .flatten()
        .map(|e| {
            if e.path().is_dir() {
                files_under(&e.path())
            } else {
                usize::from(e.file_name() != "header")
            }
        })
        .sum()
}

/// The names of the theorems shown, with their groups.
fn shown(report: &Value) -> Vec<(&str, &str)> {
    (report["theorems"]["shown"].as_array().unwrap().iter())
        .map(|t| (t["name"].as_str().unwrap(), t["group"].as_str().unwrap()))
        .collect()
}

/// The line `declaration` is on in the standard library file `file` (under
/// `std/`), for the source locations the report shows. Found by name, so a
/// sweep moving the library's text doesn't fail the test.
fn std_line(file: &str, declaration: &str) -> u64 {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../elab/src/std")
        .join(file);
    let text = std::fs::read_to_string(&path).unwrap();
    let at = text
        .find(declaration)
        .unwrap_or_else(|| panic!("{file} has no `{declaration}`"));
    text[..at].lines().count() as u64 + 1
}

#[test]
fn a_library_name_shows_header_doc_location_and_theorems() {
    let (code, out, err) = doc(&["List.filterMap"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let lines: Vec<&str> = out.lines().collect();
    // The header as written, with the parameter names the type drops.
    assert_eq!(lines[0], "Std.List.filterMap  definition");
    assert_eq!(
        lines[1],
        "  def List.filterMap: (xs: List a) → (f: a → {e} Option b) → {e} List b"
    );
    let line = std_line("List/Toolkit.sw", "def List.filterMap");
    assert_eq!(
        lines[2],
        format!("  std/List/Toolkit.sw:{line}  (import Std (List))")
    );
    assert!(
        out.contains("\n  Keeps the `Some` results, in order."),
        "{out}"
    );
    assert!(out.contains("\nExamples: none"), "{out}");
    // Eight theorems of the total, and the command that lists all.
    let heading = lines
        .iter()
        .find(|l| l.starts_with("Theorems: "))
        .expect("a theorems section");
    assert!(heading.ends_with(" mention it; 8 shown"), "{heading}");
    let at = lines.iter().position(|l| l == heading).unwrap();
    assert!(
        lines[at + 1].starts_with("  List.filterMapSome  "),
        "{}",
        lines[at + 1]
    );
    // The parameters only later ones use are left out of a statement.
    assert!(
        lines[at + 1].ends_with("xs.filterMap (x => Some (f x)) = xs.map f"),
        "{}",
        lines[at + 1]
    );
    assert!(lines[at + 9].starts_with("  all "), "{}", lines[at + 9]);
    assert!(
        lines[at + 9].contains(": stitchwort search 'List.filterMap' --theorems --limit "),
        "{}",
        lines[at + 9]
    );
    // The full name finds the same.
    let (code, full, _) = doc(&["Std.List.filterMap"]);
    assert_eq!(code, 0);
    assert_eq!(full, out);
}

#[test]
fn the_json_contract() {
    let (code, report) = json(&["List.filterMap"]);
    assert_eq!(code, 0, "{report}");
    assert_eq!(report["version"], 1);
    assert_eq!(report["name"], "Std.List.filterMap");
    assert_eq!(report["kind"], "definition");
    assert_eq!(report["file"], "std/List/Toolkit.sw");
    assert_eq!(
        report["line"],
        std_line("List/Toolkit.sw", "def List.filterMap")
    );
    assert_eq!(report["import"], "import Std (List)");
    assert_eq!(report["summary"], "Keeps the `Some` results, in order.");
    assert_eq!(report["docMarker"], "--|");
    assert!(report["type"].as_str().unwrap().starts_with("[a: Type] → "));
    assert_eq!(report["examples"].as_array().unwrap().len(), 0);
    let theorems = &report["theorems"];
    let total = theorems["total"].as_u64().unwrap();
    assert!(total > 8);
    assert_eq!(theorems["shown"].as_array().unwrap().len(), 8);
    assert!(
        (theorems["command"].as_str().unwrap())
            .starts_with("stitchwort search 'List.filterMap' --theorems --limit ")
    );
    let first = &theorems["shown"][0];
    assert_eq!(first["name"], "Std.List.filterMapSome");
    assert_eq!(first["file"], "std/List/Lemmas.sw");
    assert_eq!(first["group"], "rewrite");
    // The JSON keeps the whole type.
    assert!(
        first["type"]
            .as_str()
            .unwrap()
            .starts_with("∀ [a b: Type] ")
    );
    // `--theorems N` caps the list, and the total stays.
    let (_, three) = json(&["List.filterMap", "--theorems", "3"]);
    assert_eq!(three["theorems"]["shown"].as_array().unwrap().len(), 3);
    assert_eq!(three["theorems"]["total"].as_u64().unwrap(), total);
}

/// SW-1146: a built-in name has no declaration of its own, and is documented
/// by `core/Builtins.sw`. SW-1148: being always in scope, it has no import.
#[test]
fn a_built_in_name_is_documented_by_builtins_sw() {
    let cwd = folder("builtin");
    let cache = cwd.join("fresh-cache");
    for (name, header) in [
        (
            "Quot",
            "def Quot: (a: Type) \u{2192} (r: a \u{2192} a \u{2192} Prop) \u{2192} Type",
        ),
        (
            "Quot.mk",
            "def Quot.mk: [a: Type] \u{2192} [r: a \u{2192} a \u{2192} Prop] \u{2192} (x: a) \u{2192} Quot a r",
        ),
        ("rfl", "def rfl: [a: Type] \u{2192} [x: a] \u{2192} x = x"),
    ] {
        let (code, out, err) = doc_in(&cwd, &cache, &[name, "--theorems", "0", "--json"]);
        assert_eq!(code, 0, "{out}\n{err}");
        let report: Value = serde_json::from_str(&out).unwrap();
        assert_eq!(report["header"], header, "{report}");
        assert!(
            report["file"]
                .as_str()
                .is_some_and(|f| f.ends_with("core/Builtins.sw")),
            "{report}"
        );
        assert!(!report["doc"].as_str().unwrap_or("").is_empty(), "{report}");
        assert!(
            report["import"].is_null(),
            "a built-in needs no import: {report}"
        );
        let (code, out, err) = doc_in(&cwd, &cache, &[name, "--theorems", "0"]);
        assert_eq!(code, 0, "{out}\n{err}");
        assert!(
            !out.contains("(import "),
            "a built-in needs no import: {out}"
        );
    }
    let _ = std::fs::remove_dir_all(&cwd);
}

/// D2152: with `--theorems 0` nothing is checked, so there is no type, and no
/// cache is written (a check of the library would write one).
#[test]
fn without_theorems_nothing_is_checked() {
    let cwd = folder("parse-only");
    let cache = cwd.join("fresh-cache");
    let (code, out, err) = doc_in(&cwd, &cache, &["Text.padLeft", "--theorems", "0", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(report["name"], "Std.Text.padLeft");
    assert!(report.get("type").is_none(), "{report}");
    assert!(report["theorems"].is_null(), "{report}");
    assert_eq!(
        report["header"],
        "def Text.padLeft (text: Text) (width: Nat) (char: Char): Text"
    );
    assert_eq!(report["examples"][0]["name"], "Std.Text.padLeftExample");
    assert_eq!(files_under(&cache), 0, "a check ran and wrote its cache");
    // The text has no theorems section.
    let (code, out, _) = doc_in(&cwd, &cache, &["Text.padLeft", "--theorems", "0"]);
    assert_eq!(code, 0);
    assert!(!out.contains("Theorems"), "{out}");
    assert!(
        out.contains("Examples:\n  theorem Text.padLeftExample: "),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(&cwd);
}

/// §5.5: the ranking on the three names the proposal names. The groups are
/// `rewrite` (named after it, an equation headed by it), `named`, `other`;
/// within a group, search's own order.
#[test]
fn theorems_are_ranked_for_filter_map_map_and_add() {
    let (_, report) = json(&["List.filterMap", "--theorems", "30"]);
    let theorems = shown(&report);
    // 8 rewrites named after it, in search's order, then the other
    // theorems named after it, then the rest (the digit lemma).
    let rewrites: Vec<&str> = theorems
        .iter()
        .filter(|(_, g)| *g == "rewrite")
        .map(|(n, _)| *n)
        .collect();
    assert_eq!(
        rewrites,
        [
            "Std.List.filterMapSome",
            "Std.List.filterMapMap",
            "Std.List.filterMapAppend",
            "Std.List.filterMapAll",
            "Std.List.filterMapCong",
            "Std.List.filterMapCongMem",
            "Std.List.filterMapMapSelf",
            "Std.List.filterMapSomeMem",
        ]
    );
    let group_of = |name: &str| theorems.iter().find(|(n, _)| *n == name).map(|(_, g)| *g);
    assert_eq!(group_of("Std.List.memFilterMapElim"), Some("named"));
    assert_eq!(group_of("Std.Char.toTextDigits"), Some("other"));
    // Groups come in order.
    let order: Vec<&str> = theorems.iter().map(|(_, g)| *g).collect();
    let mut sorted = order.clone();
    sorted.sort_by_key(|g| ["rewrite", "named", "other"].iter().position(|x| x == g));
    assert_eq!(order, sorted);

    // `List.map`: 66 of its theorems are named after it, so the cap matters.
    let (_, report) = json(&["List.map", "--theorems", "12"]);
    let theorems = shown(&report);
    assert!(theorems.len() == 12 && report["theorems"]["total"].as_u64().unwrap() > 100);
    assert!(theorems.iter().all(|(_, g)| *g == "rewrite"));
    let names: Vec<&str> = theorems.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        names[..3],
        ["Std.List.mapId", "Std.List.mapGetOr", "Std.List.mapReverse"]
    );
    assert!(names.contains(&"Std.List.mapMap"), "{names:?}");
    assert!(names.contains(&"Std.List.mapAppend"), "{names:?}");

    // `Nat.add`: `+` is it, so statements written with `+` count.
    let (_, report) = json(&["Nat.add", "--theorems", "12"]);
    let theorems = shown(&report);
    assert!(report["theorems"]["total"].as_u64().unwrap() > 250);
    assert!(theorems.iter().all(|(_, g)| *g == "rewrite"));
    let names: Vec<&str> = theorems.iter().map(|(n, _)| *n).collect();
    assert_eq!(
        names[..3],
        ["Std.Nat.addZero", "Std.Nat.zeroAdd", "Std.Nat.addOne"]
    );
    assert!(names.contains(&"Std.Nat.addComm"), "{names:?}");
    assert!(names.contains(&"Std.Nat.addAssoc"), "{names:?}");
}

/// A project of three namespaces: `Shapes`, `Shapes.Tests` (which uses it)
/// and `Elsewhere` (which doesn't, and doesn't even check).
fn shop(name: &str) -> PathBuf {
    let dir = folder(name);
    std::fs::write(dir.join("stitchwort.yaml"), "# for the doc tests\n").unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("src/shapes.sw"),
        "\
--| The shapes of the shop.

namespace Shapes

--| A shape: a circle or a square.
type Shape =
  | Circle (r: Nat)
  --| The side of the square.
  | Square (side: Nat)

def Shape.size: Shape → Nat
  | Circle r => r
  | Square a => a

--| Scales a shape.
--|
--| Every side is multiplied by the first argument.
@[noReceiver]
def Shape.scale: Nat → Shape → Shape
  | k, Circle r => Circle (k * r)
  | k, Square a => Square (k * a)

theorem Shape.scaleOne: (s: Shape) → Shape.scale 1 s = s
  | Circle r => rfl
  | Square a => rfl

theorem Shape.scaleExample: Shape.scale 2 (Circle 3) = Circle 6 := rfl

test \"Shape.scale\" := Shape.size (Shape.scale 2 (Circle 3)) == 6
",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/tests.sw"),
        "\
namespace Shapes.Tests
import Shapes (..)

test \"Shape.scale of a square\" := Shape.size (Shape.scale 3 (Square 2)) == 6

theorem scaleTwice: (s: Shape) → Shape.scale 1 (Shape.scale 1 s) = s
  | Circle r => rfl
  | Square a => rfl
",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/elsewhere.sw"),
        "\
namespace Elsewhere

test \"Shape.scale\" := True

def Nat.add: Nat → Nat → Nat
  | a, b => a

def broken: Nat := True
",
    )
    .unwrap();
    dir
}

/// D2146: a project name's examples and theorems come from its namespace and
/// those that use it. `Elsewhere` doesn't use `Shapes`, and doesn't check:
/// it is neither looked in nor loaded.
#[test]
fn a_project_name_looks_in_its_namespace_and_those_that_use_it() {
    let dir = shop("scope");
    let (code, out, err) = doc_in(&dir, &shared_cache(), &["Shape.scale", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    assert_eq!(err, "", "nothing about a namespace that doesn't check");
    let report: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(report["name"], "Shapes.Shape.scale");
    assert_eq!(report["header"], "def Shape.scale: Nat → Shape → Shape");
    assert_eq!(report["import"], "import Shapes (Shape)");
    assert_eq!(report["type"], "Nat → Shapes.Shape → Shapes.Shape");
    // The doc is the `--|` lines, with a paragraph break.
    assert_eq!(report["docMarker"], "--|");
    assert_eq!(report["summary"], "Scales a shape.");
    assert_eq!(
        report["doc"],
        "Scales a shape.\n\nEvery side is multiplied by the first argument."
    );
    // Examples: the test and the `…Example` theorem of the namespace, and
    // the test of `Shapes.Tests`; not `Elsewhere`'s.
    let examples: Vec<(&str, &str)> = (report["examples"].as_array().unwrap().iter())
        .map(|e| (e["kind"].as_str().unwrap(), e["name"].as_str().unwrap()))
        .collect();
    assert_eq!(
        examples,
        [
            ("theorem", "Shapes.Shape.scaleExample"),
            ("test", "Shape.scale"),
            ("test", "Shape.scale of a square"),
        ]
    );
    assert_eq!(report["examples"][0]["line"], 27);
    assert_eq!(
        report["examples"][0]["source"],
        "theorem Shape.scaleExample: Shape.scale 2 (Circle 3) = Circle 6 := rfl"
    );
    // Theorems: the namespace's and `Shapes.Tests`'; the `…Example` theorem
    // is an example, not listed.
    // `Shape.scale`'s generated equations have a section of their own
    // (docs/proposals/function-equations.md, stage 1c).
    assert_eq!(
        shown(&report),
        [
            ("Shapes.Shape.scaleOne", "rewrite"),
            ("Shapes.Tests.scaleTwice", "rewrite"),
        ]
    );
    assert_eq!(report["equations"]["total"], 2);
    let command = report["theorems"]["command"].as_str().unwrap();
    assert!(
        command.contains(" --in Shapes --in Shapes.Tests"),
        "{command}"
    );
    assert!(!command.contains("Elsewhere"), "{command}");
    // The text.
    let (code, out, _) = doc_in(&dir, &shared_cache(), &["Shape.scale"]);
    assert_eq!(code, 0);
    assert!(out.contains("Theorems: 2 mention it\n"), "{out}");
    assert!(out.contains("Equations: 2 generated equations\n"), "{out}");
    assert!(
        out.contains("  test \"Shape.scale of a square\" := "),
        "{out}"
    );
    // From another folder, with --project.
    let (code, out, _) = doc_in(
        Path::new("/"),
        &shared_cache(),
        &[
            "Shape.scale",
            "--theorems",
            "0",
            "--project",
            dir.to_str().unwrap(),
        ],
    );
    assert_eq!(code, 0, "{out}");
    assert!(out.starts_with("Shapes.Shape.scale  definition\n"), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_project_namespace_and_its_members() {
    let dir = shop("namespace");
    let (code, out, _) = doc_in(&dir, &shared_cache(), &["Shapes", "--json"]);
    assert_eq!(code, 0, "{out}");
    let report: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(report["namespace"], "Shapes");
    assert_eq!(report["fileDocs"][0]["doc"], "The shapes of the shop.");
    let members: Vec<(&str, &str, Option<&str>)> = (report["members"].as_array().unwrap().iter())
        .map(|m| {
            (
                m["name"].as_str().unwrap(),
                m["kind"].as_str().unwrap(),
                m["summary"].as_str(),
            )
        })
        .collect();
    assert_eq!(
        members,
        [
            (
                "Shapes.Shape",
                "type",
                Some("A shape: a circle or a square.")
            ),
            ("Shapes.Shape.size", "definition", None),
            ("Shapes.Shape.scale", "definition", Some("Scales a shape.")),
        ]
    );
    // The text lists them under their file.
    let (code, out, _) = doc_in(&dir, &shared_cache(), &["Shapes"]);
    assert_eq!(code, 0);
    assert!(out.starts_with("namespace Shapes\n"), "{out}");
    assert!(out.contains("  The shapes of the shop.\n"), "{out}");
    assert!(
        out.contains("Shapes.Shape.scale  definition  Scales a shape.\n"),
        "{out}"
    );
    // The type and its constructors, one with a doc.
    let (code, out, _) = doc_in(&dir, &shared_cache(), &["Shapes.Shape", "--theorems", "0"]);
    assert_eq!(code, 0);
    assert!(
        out.contains(
            "Members:\n  Circle (r: Nat)\n  Square (side: Nat)\n      The side of the square.\n"
        ),
        "{out}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn several_names_and_none() {
    let dir = shop("names");
    // `Nat.add` is the library's and `Elsewhere`'s: write one in full.
    let (code, out, _) = doc_in(
        &dir,
        &shared_cache(),
        &["Nat.add", "--theorems", "0", "--json"],
    );
    assert_eq!(code, 2, "{out}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let names: Vec<&str> = (report["matches"].as_array().unwrap().iter())
        .map(|m| m["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["Std.Nat.add", "Elsewhere.Nat.add"]);
    let (code, out, _) = doc_in(
        &dir,
        &shared_cache(),
        &["Elsewhere.Nat.add", "--theorems", "0"],
    );
    assert_eq!(code, 0, "{out}");
    let (code, out, _) = doc_in(&dir, &shared_cache(), &["Std.Nat.add", "--theorems", "0"]);
    assert_eq!(code, 0, "{out}");
    // None: the closest names, and exit 1.
    let (code, out, err) = doc(&["List.filterMa", "--theorems", "0"]);
    assert_eq!(code, 1, "{out}\n{err}");
    assert!(
        out.contains("no declaration or namespace named `List.filterMa`"),
        "{out}"
    );
    assert!(out.contains("\n  List.filterMap  "), "{out}");
    let (code, report) = json(&["List.filterMa", "--theorems", "0"]);
    assert_eq!(code, 1);
    assert_eq!(report["matches"].as_array().unwrap().len(), 0);
    assert_eq!(report["closest"][0]["name"], "Std.List.filterMap");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn every_kind_of_declaration() {
    let kinds = [
        ("Nat.addComm", "theorem"),
        ("List.decMem", "instance"),
        ("List", "type"),
        ("Ord", "interface"),
        ("Fail", "ability"),
        ("List.Cons", "constructor"),
        ("Ord.compare", "field"),
        ("Fail.stop", "operation"),
    ];
    for (name, kind) in kinds {
        let (code, report) = json(&[name, "--theorems", "0"]);
        assert_eq!(code, 0, "{name}: {report}");
        assert_eq!(report["kind"], kind, "{name}");
    }
    // A theorem has a statement and no theorem list.
    let (_, report) = json(&["Nat.addComm"]);
    assert_eq!(
        report["header"],
        "theorem Nat.addComm ∀ (m n: Nat): m + n = n + m"
    );
    assert!(report["theorems"].is_null());
    assert!(report["type"].as_str().unwrap().contains("m + n = n + m"));
    // A constructor on a line of its own shows its type.
    let (_, report) = json(&["Effect.Comp.Call", "--theorems", "0"]);
    assert_eq!(report["container"], "Std.Effect.Comp");
    assert_eq!(
        report["header"],
        "Call (o: op) (rest: res o → Comp op res a)"
    );
    // An instance has tests named after it.
    let (_, report) = json(&["List.decMem", "--theorems", "0"]);
    let examples = report["examples"].as_array().unwrap();
    assert_eq!(examples.len(), 2);
    assert_eq!(examples[0]["kind"], "test");
    assert_eq!(examples[1]["name"], "List.decMem on a variable");
    // A type's members, and a type that is a namespace too: the type first,
    // then the namespace's listing.
    let (_, report) = json(&["List", "--theorems", "0"]);
    let members: Vec<&str> = (report["members"].as_array().unwrap().iter())
        .map(|m| m["name"].as_str().unwrap())
        .collect();
    assert_eq!(members, ["Std.List.Nil", "Std.List.Cons"]);
    assert_eq!(report["namespace"]["namespace"], "Std.List");
    let listed: Vec<&str> = (report["namespace"]["members"].as_array().unwrap().iter())
        .map(|m| m["name"].as_str().unwrap())
        .collect();
    assert!(listed.contains(&"Std.List.filterMap"));
    assert!(
        !listed.contains(&"Std.List.Cons"),
        "constructors aren't listed"
    );
    assert!(
        !listed.iter().any(|n| n.contains("Example")),
        "theorems aren't listed"
    );
    let (code, out, _) = doc(&["List", "--theorems", "0"]);
    assert_eq!(code, 0);
    let type_at = out.find("Std.List  type").unwrap();
    let namespace_at = out.find("namespace Std.List\n").unwrap();
    assert!(type_at < namespace_at, "{out}");
    // A namespace on its own lists its docs, then its declarations.
    let (code, out, _) = doc(&["Std.Fail", "--theorems", "0"]);
    assert_eq!(code, 0);
    assert!(out.contains("Fail.toResult  definition"), "{out}");
}

#[test]
fn a_file_is_documented_with_the_library() {
    let dir = folder("file");
    std::fs::write(
        dir.join("a.sw"),
        "\
--| Twice `n`.
def doubleIt (n: Nat): Nat := n + n

theorem doubleItZero: doubleIt 0 = 0 := rfl

test \"doubleIt\" := doubleIt 2 == 4
",
    )
    .unwrap();
    let (code, out, err) = doc_in(&dir, &shared_cache(), &["doubleIt", "a.sw", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(report["name"], "Main.doubleIt");
    assert_eq!(report["header"], "def doubleIt (n: Nat): Nat");
    assert_eq!(report["summary"], "Twice `n`.");
    assert_eq!(report["examples"][0]["name"], "doubleIt");
    assert_eq!(shown(&report), [("Main.doubleItZero", "rewrite")]);
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- `doc --coverage` (SW-1025, §6.2, D2138, D2148) -------------------------

/// A project of two namespaces with every case the report tells apart.
fn coverage_project(name: &str) -> PathBuf {
    let dir = folder(name);
    std::fs::write(dir.join("stitchwort.yaml"), "# for the coverage tests\n").unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("src/lib.sw"),
        "\
namespace Lib

--| Adds one to a number, never fails.
def good (n: Nat): Nat := n + 1

-- Adds two to a number, never fails.
def plainDoc (n: Nat): Nat := n + 2

def noDoc (n: Nat): Nat := n

--| Adds two.
def short (n: Nat): Nat := n

--| fill the whole bag
def fillTheWholeBag (n: Nat): Nat := n

--| A box holding one number.
type Box = | Box (n: Nat)

--| Shows that one is not zero, by `rfl`.
theorem goodIsOne: good 0 = 1 := rfl

theorem noDocLemma: good 1 = 2 := rfl

theorem goodExample: good 2 = 3 := rfl

theorem ghostExample: good 3 = 4 := rfl

test \"noDoc\" := noDoc 1 == 1
",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/other.sw"),
        "\
namespace Other

--| Doubles a number by adding it to itself.
def double (n: Nat): Nat := n + n
",
    )
    .unwrap();
    dir
}

#[test]
fn coverage_counts_a_project_namespace() {
    let dir = coverage_project("coverage-text");
    let (code, out, err) = doc_in(&dir, &shared_cache(), &["--coverage", "Lib"]);
    assert_eq!(code, 0, "{out}\n{err}");
    // 6 declarations; `good` and `Box` count; `plainDoc` (a plain `--` note
    // is no doc), `noDoc`, `short` and `fillTheWholeBag` (it repeats its
    // name) don't. A project is no target (SW-1100): plain counts, no
    // percentages, no list of defects.
    assert!(out.contains("with a doc: 2 of 6 declarations\n"), "{out}");
    assert!(!out.contains('%') && !out.contains("undocumented"), "{out}");
    assert!(!out.contains("Lib.noDoc"), "{out}");
    // Examples by name: the test for `noDoc`, the theorem for `good`.
    assert!(
        out.contains("with an example: 2 of 6 declarations"),
        "{out}"
    );
    // Theorems apart: one of four has a doc.
    assert!(
        out.contains("theorems with a doc (counted apart): 1 of 4"),
        "{out}"
    );
    // The unattached `…Example` theorem, and not the attached one.
    assert!(out.contains("Lib.ghostExample  "), "{out}");
    assert!(!out.contains("Lib.goodExample  "), "{out}");
    // `--list` names the declarations without a doc that counts.
    let (code, out, err) = doc_in(&dir, &shared_cache(), &["--coverage", "--list", "Lib"]);
    assert_eq!(code, 0, "{out}\n{err}");
    assert!(out.contains("without a doc that counts (4):"), "{out}");
    assert!(out.contains("Lib.plainDoc  definition  "), "{out}");
    assert!(out.contains("Lib.noDoc  definition  "), "{out}");
    assert!(out.contains("(no doc)"), "{out}");
    assert!(out.contains("(too short)"), "{out}");
    assert!(out.contains("(repeats the name)"), "{out}");
    assert!(!out.contains("Lib.good  "), "{out}");
    assert!(!out.contains('%'), "{out}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn coverage_json_and_the_default_scope() {
    let dir = coverage_project("coverage-json");
    // Inside a project and with no namespace: the project's namespaces.
    let (code, out, err) = doc_in(&dir, &shared_cache(), &["--coverage", "--json"]);
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    assert_eq!(report["version"], 1);
    let names: Vec<&str> = (report["namespaces"].as_array().unwrap().iter())
        .map(|n| n["namespace"].as_str().unwrap())
        .collect();
    assert_eq!(names, ["Lib", "Other"]);
    let lib = &report["namespaces"][0];
    // A project has no target, but the JSON keeps the lists.
    assert_eq!(lib["target"], false);
    assert_eq!(report["total"]["target"], false);
    assert_eq!(lib["declarations"]["total"], 6);
    assert_eq!(lib["declarations"]["documented"], 2);
    assert!(lib["declarations"].get("plain").is_none(), "{lib}");
    assert!(lib.get("plainDocs").is_none(), "{lib}");
    assert_eq!(lib["declarations"]["withExample"], 2);
    assert_eq!(lib["theorems"]["total"], 4);
    assert_eq!(lib["theorems"]["documented"], 1);
    assert!(lib["theorems"].get("withExample").is_none(), "{lib}");
    let reasons: Vec<(&str, &str)> = (lib["undocumented"].as_array().unwrap().iter())
        .map(|m| (m["name"].as_str().unwrap(), m["reason"].as_str().unwrap()))
        .collect();
    assert_eq!(
        reasons,
        [
            ("Lib.plainDoc", "no doc"),
            ("Lib.noDoc", "no doc"),
            ("Lib.short", "too short"),
            ("Lib.fillTheWholeBag", "repeats the name"),
        ]
    );
    assert_eq!(lib["undocumentedTheorems"][0]["name"], "Lib.noDocLemma");
    assert_eq!(lib["unattachedExamples"][0]["name"], "Lib.ghostExample");
    assert_eq!(report["namespaces"][1]["declarations"]["documented"], 1);
    // The total counts each declaration once.
    assert_eq!(report["total"]["declarations"]["total"], 7);
    assert_eq!(report["total"]["declarations"]["documented"], 3);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn coverage_reports_and_never_fails_but_a_bad_name_is_an_error() {
    let dir = coverage_project("coverage-errors");
    let (code, _, err) = doc_in(&dir, &shared_cache(), &["--coverage", "Lib.Nowhere"]);
    assert_eq!(code, 2, "{err}");
    assert!(err.contains("is not a namespace"), "{err}");
    // A name that is a declaration, not a namespace, is the same error.
    let (code, ..) = doc_in(&dir, &shared_cache(), &["--coverage", "Lib.good"]);
    assert_eq!(code, 2);
    // Poor coverage is exit 0.
    let (code, ..) = doc_in(&dir, &shared_cache(), &["--coverage", "Lib", "Other"]);
    assert_eq!(code, 0);
    // Without `--coverage` a name is still required.
    let (code, ..) = doc_in(&dir, &shared_cache(), &[]);
    assert_eq!(code, 2);
    let _ = std::fs::remove_dir_all(&dir);
}

/// The library, by shape: std will change, so no figure is pinned.
#[test]
fn coverage_of_a_library_namespace_has_the_shape() {
    let (code, report) = json(&["--coverage", "List"]);
    assert_eq!(code, 0);
    let ns = &report["namespaces"][0];
    assert_eq!(ns["namespace"], "Std.List");
    assert_eq!(ns["target"], true);
    let n = |v: &Value| v.as_u64().unwrap();
    let d = &ns["declarations"];
    assert!(n(&d["total"]) > 50, "{d}");
    assert!(n(&d["documented"]) > 0 && n(&d["documented"]) <= n(&d["total"]));
    assert!(n(&d["withExample"]) > 0 && n(&d["withExample"]) <= n(&d["total"]));
    let t = &ns["theorems"];
    assert!(
        n(&t["total"]) > n(&d["total"]),
        "theorems are counted apart"
    );
    assert!(n(&t["documented"]) <= n(&t["total"]));
    assert_eq!(
        ns["undocumented"].as_array().unwrap().len() as u64,
        n(&d["total"]) - n(&d["documented"])
    );
    assert_eq!(
        ns["undocumentedTheorems"].as_array().unwrap().len() as u64,
        n(&t["total"]) - n(&t["documented"])
    );
    // No namespace: the library, in pieces, with a total.
    let (code, all) = json(&["--coverage"]);
    assert_eq!(code, 0);
    let names: Vec<&str> = (all["namespaces"].as_array().unwrap().iter())
        .map(|n| n["namespace"].as_str().unwrap())
        .collect();
    assert!(
        names.contains(&"Std.List") && names.contains(&"Std.Vec"),
        "{names:?}"
    );
    assert!(n(&all["total"]["declarations"]["total"]) > n(&d["total"]));
    let (code, text, _) = doc(&["--coverage", "Std.Vec"]);
    assert_eq!(code, 0);
    assert!(text.starts_with("Std.Vec\n  documented: "), "{text}");
}

// ---- Checked links (SW-1042, §7, D2149, D2153) ------------------------------

/// A project of two namespaces whose docs link: some well, some not.
fn links_project(name: &str) -> PathBuf {
    let dir = folder(name);
    std::fs::write(dir.join("stitchwort.yaml"), "# for the link tests\n").unwrap();
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(
        dir.join("src/lib.sw"),
        "\
namespace Lib

--| Adds one. Like [`later`] (below), [`Lib.later`], [`Other.double`], [`List.map`],
--| [`Std.List.filter`], [`Lib`] and the type [`Box`]; but not [`Lib.lateer`] or
--| [`nothere`], and [x] and the pair \"its `[` is; its `]`\" are no links.
def good (n: Nat): Nat := n + 1

-- A note: [`nothere`] is not checked.
def later (n: Nat): Nat := n

type Box = | Box (n: Nat)
",
    )
    .unwrap();
    std::fs::write(
        dir.join("src/other.sw"),
        "\
namespace Other

--| Doubles. Compare [`Lib.good`].
def double (n: Nat): Nat := n + n
",
    )
    .unwrap();
    dir
}

fn check_in(dir: &Path, args: &[&str]) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("check")
        .args(args)
        .arg("--cache-dir")
        .arg(dir.join("cache"))
        .current_dir(dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort");
    (
        output.status.code().unwrap_or(-1),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn check_warns_of_a_link_that_names_nothing_and_suggests_the_nearest() {
    let dir = links_project("links-check");
    // Twice: the second run replays the namespaces from the cache, with
    // the warnings they had.
    for _ in 0..2 {
        let (code, out, err) = check_in(&dir, &[]);
        assert_eq!(code, 0, "{out}\n{err}");
        let text = format!("{out}{err}");
        assert_eq!(text.matches("[W-DOC-LINK]").count(), 2, "{text}");
        assert!(
            text.contains("the doc link `Lib.lateer` names nothing"),
            "{text}"
        );
        assert!(text.contains("did you mean `Lib.later`?"), "{text}");
        assert!(
            text.contains("the doc link `nothere` names nothing"),
            "{text}"
        );
        // The plain note, the bare `[x]` and the prose are not links.
        assert!(!text.contains("`x`"), "{text}");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn doc_json_has_links_and_the_text_marks_the_unresolved() {
    let dir = links_project("links-doc");
    let (code, out, err) = doc_in(
        &dir,
        &shared_cache(),
        &["Lib.good", "--theorems", "0", "--json"],
    );
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let links: Vec<(&str, Option<&str>)> = (report["links"].as_array().unwrap().iter())
        .map(|l| (l["text"].as_str().unwrap(), l["target"].as_str()))
        .collect();
    assert_eq!(
        links,
        [
            ("later", Some("Lib.later")),
            ("Lib.later", Some("Lib.later")),
            ("Other.double", Some("Other.double")),
            ("List.map", Some("Std.List.map")),
            ("Std.List.filter", Some("Std.List.filter")),
            ("Lib", Some("Lib")),
            ("Box", Some("Lib.Box")),
            ("Lib.lateer", None),
            ("nothere", None),
        ]
    );
    let first = &report["links"][0];
    assert_eq!(first["status"], "resolved");
    assert!(
        first["file"].as_str().unwrap().ends_with("src/lib.sw"),
        "{first}"
    );
    assert_eq!(first["line"], 9);
    assert_eq!(report["links"][7]["status"], "unresolved");
    assert!(report["links"][7]["file"].is_null());
    let (code, text, _) = doc_in(&dir, &shared_cache(), &["Lib.good", "--theorems", "0"]);
    assert_eq!(code, 0);
    assert!(text.contains("Like `later` (below), `Lib.later`"), "{text}");
    assert!(text.contains("`Lib.lateer` (unresolved link)"), "{text}");
    assert!(text.contains("`nothere` (unresolved link)"), "{text}");
    assert!(!text.contains("`Lib.later` (unresolved"), "{text}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn the_index_has_links_per_doc() {
    let dir = links_project("links-index");
    let (code, out, err) = check_in(&dir, &["--index", "-"]);
    assert_eq!(code, 0, "{err}");
    let start = out.find("{\"version\"").expect("the index");
    let index: Value = serde_json::from_str(&out[start..]).unwrap();
    let symbols = index["symbols"].as_array().unwrap();
    let good = symbols
        .iter()
        .find(|s| s["name"] == "Lib.good")
        .expect("Lib.good");
    let links = good["links"].as_array().unwrap();
    assert_eq!(links.len(), 9);
    assert_eq!(links[0]["text"], "later");
    assert_eq!(links[0]["target"], "Lib.later");
    assert_eq!(links[3]["target"], "Std.List.map");
    assert_eq!(links[7]["text"], "Lib.lateer");
    assert!(links[7]["target"].is_null());
    // Its comment is a `--` note: no doc, so no links.
    let later = symbols
        .iter()
        .find(|s| s["name"] == "Lib.later")
        .expect("Lib.later");
    assert!(
        later.get("doc").is_none() && later.get("links").is_none(),
        "{later}"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- Links through the file's imports (SW-1045) -----------------------------

#[test]
fn a_link_an_import_makes_resolve_resolves_in_doc_and_the_index() {
    let dir = links_project("links-imports");
    std::fs::write(
        dir.join("src/third.sw"),
        "\
namespace Third

import Lib (good as better)
import Other (..)

--| Calls [`better`] and [`double`] (both by an import), not [`good`], which this
--| file renamed, nor [`Lib.later`], which needs no import.
def use (n: Nat): Nat := double (better n)
",
    )
    .unwrap();
    // `check` accepts them all but the one that names nothing here.
    let (code, out, err) = check_in(&dir, &[]);
    assert_eq!(code, 0, "{out}\n{err}");
    let text = format!("{out}{err}");
    assert!(!text.contains("the doc link `better`"), "{text}");
    assert!(!text.contains("the doc link `double`"), "{text}");
    assert_eq!(text.matches("[W-DOC-LINK]").count(), 3, "{text}");
    assert!(text.contains("the doc link `good` names nothing"), "{text}");
    let want = [
        ("better", Some("Lib.good")),
        ("double", Some("Other.double")),
        ("good", None),
        ("Lib.later", Some("Lib.later")),
    ];
    // `doc` agrees with `check`, with no elaboration.
    let (code, out, err) = doc_in(
        &dir,
        &shared_cache(),
        &["Third.use", "--theorems", "0", "--json"],
    );
    assert_eq!(code, 0, "{out}\n{err}");
    let report: Value = serde_json::from_str(&out).unwrap();
    let links: Vec<(&str, Option<&str>)> = (report["links"].as_array().unwrap().iter())
        .map(|l| (l["text"].as_str().unwrap(), l["target"].as_str()))
        .collect();
    assert_eq!(links, want);
    // So does the index.
    let (code, out, err) = check_in(&dir, &["--index", "-"]);
    assert_eq!(code, 0, "{err}");
    let index: Value = serde_json::from_str(&out[out.find("{\"version\"").unwrap()..]).unwrap();
    let symbol = (index["symbols"].as_array().unwrap().iter())
        .find(|s| s["name"] == "Third.use")
        .expect("Third.use");
    let links: Vec<(&str, Option<&str>)> = (symbol["links"].as_array().unwrap().iter())
        .map(|l| (l["text"].as_str().unwrap(), l["target"].as_str()))
        .collect();
    assert_eq!(links, want);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_cached_link_warning_follows_the_namespace_it_points_into() {
    let dir = links_project("links-stale");
    let lib = "namespace Lib\n\n--| Calls [`Third.helper`] (another namespace).\ndef caller (n: Nat): Nat := n\n";
    let third = |name: &str| format!("namespace Third\n\ndef {name} (n: Nat): Nat := n\n");
    std::fs::write(dir.join("src/lib.sw"), lib).unwrap();
    std::fs::write(dir.join("src/third.sw"), third("other")).unwrap();
    let warned = |run: &str| {
        let (code, out, err) = check_in(&dir, &[]);
        assert_eq!(code, 0, "{run}: {out}\n{err}");
        format!("{out}{err}").contains("the doc link `Third.helper` names nothing")
    };
    assert!(warned("first"), "the link names nothing");
    // Only `Third` changes (`Lib` does not use it, so its cache key is the
    // same): the link now resolves, and the warning must go.
    std::fs::write(dir.join("src/third.sw"), third("helper")).unwrap();
    assert!(!warned("after Third gained helper"), "a stale warning");
    // And back: the warning comes back.
    std::fs::write(dir.join("src/third.sw"), third("other")).unwrap();
    assert!(warned("after Third lost helper"), "a missing warning");
    let _ = std::fs::remove_dir_all(&dir);
}
