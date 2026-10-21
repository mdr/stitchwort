//! Checking a project: namespaces in canonical order, each with its
//! dependencies in scope (docs/proposals/multi-file.md §4, §12). Sources are
//! in memory.

use std::collections::BTreeMap;

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_driver::project::{Loaded, MemoryFiles, Target, parse_config, project_sources};
use stitchwort_syntax::{Diagnostic, Severity};

fn owned(files: &[(&str, &str)]) -> Vec<(String, String)> {
    files
        .iter()
        .map(|(path, text)| (path.to_string(), text.to_string()))
        .collect()
}

fn load_target(
    files: &[(&str, &str)],
    target: &Target,
) -> (Session, Result<Loaded, Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load_project_sources("proj", owned(files), target);
    (session, result)
}

fn load(files: &[(&str, &str)]) -> Session {
    let (session, result) = load_target(files, &Target::Everything);
    if let Err(errors) = result {
        panic!("{errors:#?}");
    }
    session
}

fn errors(files: &[(&str, &str)]) -> Vec<Diagnostic> {
    let (_, result) = load_target(files, &Target::Everything);
    result
        .err()
        .expect("should be refused")
        .into_iter()
        .filter(|d| d.severity == Severity::Error)
        .collect()
}

fn codes(ds: &[Diagnostic]) -> Vec<&'static str> {
    ds.iter().map(|d| d.code).collect()
}

fn passes(session: &Session) {
    let results = session.run_tests(&Cache::disabled());
    assert!(!results.is_empty());
    for result in &results {
        assert_eq!(result.outcome, Outcome::Passed, "{}", result.name);
    }
}

fn def_hash_of(session: &Session, path: &str) -> ContentHash {
    let g = &session.elab.globals;
    let id = g
        .defs
        .iter()
        .position(|d| &*d.path == path)
        .unwrap_or_else(|| panic!("no definition `{path}`"));
    def_hash(g, DefId(id)).unwrap().expect("checked")
}

fn data_hash_of(session: &Session, path: &str) -> ContentHash {
    let g = &session.elab.globals;
    let id = (0..g.datas.len())
        .map(DataId)
        .find(|d| &*g.data(*d).path == path)
        .unwrap_or_else(|| panic!("no type `{path}`"));
    data_hash(g, id).unwrap().expect("checked")
}

const LIB: &str = "namespace Lib

type Range = { lo: Nat, hi: Nat }

def Range.size (r: Range): Nat := r.hi + r.lo

def Range.parse (n: Nat): Range := { lo = 0, hi = n }

test \"size\" := Range.size (Range.parse 3) == 3
";

#[test]
fn two_namespaces() {
    let day = "namespace Day

import Lib (Range)

def width (r: Range): Nat := r.size

def parsed: Range := Range.parse 4

def qualified (r: Lib.Range): Nat := Lib.Range.size r

test \"width\" := width parsed == 4
test \"qualified\" := qualified parsed == 4
";
    // Whatever order the files are given in.
    let (session, loaded) = load_target(&[("day.sw", day), ("lib.sw", LIB)], &Target::Everything);
    let loaded = loaded.unwrap_or_else(|e| panic!("{e:#?}"));
    assert_eq!(loaded.checked, ["Lib", "Day"]);
    passes(&session);
    let tests: Vec<(&str, &str)> = session
        .elab
        .tests
        .iter()
        .map(|t| (t.namespace.as_str(), t.name.as_str()))
        .collect();
    assert_eq!(
        tests,
        [("Lib", "size"), ("Day", "width"), ("Day", "qualified")]
    );
}

#[test]
fn qualified_use_without_import() {
    let day = "namespace Day\n\ntest \"f\" := Lib.f 1 == 2\n";
    let lib = "namespace Lib\n\ndef f (n: Nat): Nat := n + 1\n";
    passes(&load(&[("day.sw", day), ("lib.sw", lib)]));
}

#[test]
fn dot_notation_through_a_synonym_and_a_record_field() {
    let mid = "namespace Mid

type R = Lib.Range

type Holder = { r: Lib.Range }

def mk (n: Nat): R := Lib.Range.parse n

def holder (n: Nat): Holder := { r = Lib.Range.parse n }
";
    let day = "namespace Day

import Mid (mk, holder)

test \"synonym\" := (mk 2).size == 2
test \"field\" := (holder 3).r.size == 3
";
    passes(&load(&[("day.sw", day), ("lib.sw", LIB), ("mid.sw", mid)]));
}

#[test]
fn foreign_namespace() {
    let day = |body: &str| format!("namespace Day\n\nimport Lib (Range)\n\n{body}\n");
    // A qualifier that is another namespace's type.
    let found = errors(&[
        ("lib.sw", LIB),
        ("day.sw", &day("def Range.extra (r: Range): Nat := 1")),
    ]);
    assert_eq!(codes(&found), ["E-FOREIGN-NAMESPACE"]);
    assert!(
        found[0].message.contains("belongs to namespace Lib"),
        "{found:#?}"
    );
    // A qualifier that is a namespace of the project.
    let aoc = "namespace Aoc\n\ndef x: Nat := 1\n";
    let found = errors(&[
        ("aoc.sw", aoc),
        ("day.sw", "namespace Day\n\ndef Aoc.f (n: Nat): Nat := n\n"),
    ]);
    assert_eq!(codes(&found), ["E-FOREIGN-NAMESPACE"]);
    assert!(found[0].message.contains("is a namespace of the project"));
    // Its own namespace's name.
    let found = errors(&[("day.sw", "namespace Day\n\ndef Day.f (n: Nat): Nat := n\n")]);
    assert_eq!(codes(&found), ["E-FOREIGN-NAMESPACE"]);
}

#[test]
fn a_failed_namespace_stops_its_dependents_only() {
    let lib = "namespace Lib\n\ndef f: Nat := True\n";
    let day = "namespace Day\n\nimport Lib (f)\n\ndef g: Nat := f\n";
    let other = "namespace Other\n\ndef h: Nat := 1\n\ntest \"h\" := h == 1\n";
    let files = [("lib.sw", lib), ("day.sw", day), ("other.sw", other)];
    let found = errors(&files);
    let found_codes = codes(&found);
    assert!(
        found_codes.contains(&"E-NAMESPACE-FAILED"),
        "{found_codes:?}"
    );
    assert_eq!(found_codes.len(), 2, "{found:#?}");
    let failed = found
        .iter()
        .find(|d| d.code == "E-NAMESPACE-FAILED")
        .unwrap();
    assert_eq!(
        failed.message,
        "namespace Lib has errors, so Day isn't checked"
    );
    // The independent namespace can be checked alone.
    let (session, result) = load_target(&files, &Target::Namespaces(vec!["Other".into()]));
    result.unwrap_or_else(|e| panic!("{e:#?}"));
    passes(&session);
    // Its own error is reported too.
    let broken = "namespace Other\n\ndef h: Nat := False\n";
    let found = errors(&[("lib.sw", lib), ("day.sw", day), ("other.sw", broken)]);
    assert_eq!(found.len(), 3, "{found:#?}");
}

#[test]
fn identical_types_in_two_namespaces_hash_differently() {
    let ty = |ns: &str| format!("namespace {ns}\n\ntype T: Type =\n  | MkT (n: Nat)\n");
    let session = load(&[("a.sw", &ty("A")), ("b.sw", &ty("B"))]);
    assert_ne!(data_hash_of(&session, "A.T"), data_hash_of(&session, "B.T"));
}

const BASE: &str = "namespace Base

type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] -> Nat := 1
";

#[test]
fn auto_uses_a_dependency_not_an_unrelated_namespace() {
    let a = "namespace A\n\nimport Base (Token)\n\ninstance decA: Decidable Token := Yes MkToken\n";
    let another = "namespace Another\n\nimport Base (Token)\n\ninstance decU: Decidable Token := Yes MkToken\n";
    let day = "namespace Day

import Base (needsToken)
import A (decA)

def client: Nat := needsToken

test \"client\" := client == 1
";
    let session = load(&[
        ("base.sw", BASE),
        ("a.sw", a),
        ("another.sw", another),
        ("day.sw", day),
    ]);
    passes(&session);
    // Without `A`'s procedure, `Another`'s isn't looked at, and the error
    // says so.
    let a_without = "namespace A\n\ndef other: Nat := 1\n";
    let day_without = day.replace("import A (decA)", "import A (other)");
    let found = errors(&[
        ("base.sw", BASE),
        ("a.sw", a_without),
        ("another.sw", another),
        ("day.sw", &day_without),
    ]);
    assert_eq!(codes(&found), ["E-AUTO-NONE"]);
    assert!(
        found[0]
            .notes
            .iter()
            .any(|n| n == "`decU` is in `Another`, which `Day` doesn't use"),
        "{:#?}",
        found[0].notes
    );
}

#[test]
fn auto_choice_doesnt_depend_on_file_order() {
    let procedure = |ns: &str, name: &str| {
        format!(
            "namespace {ns}\n\nimport Base (Token)\n\ninstance {name}: Decidable Token := Yes MkToken\n"
        )
    };
    let (a, b) = (procedure("A", "decA"), procedure("B", "decB"));
    let day = "namespace Day

import Base (needsToken)
import A (decA)
import B (decB)

def client: Nat := needsToken
";
    let hash = |files: &[(&str, &str)]| def_hash_of(&load(files), "Day.client");
    let reference = hash(&[
        ("base.sw", BASE),
        ("a.sw", &a),
        ("b.sw", &b),
        ("day.sw", day),
    ]);
    assert_eq!(
        hash(&[
            ("day.sw", day),
            ("b.sw", &b),
            ("a.sw", &a),
            ("base.sw", BASE)
        ]),
        reference
    );
    assert_eq!(
        hash(&[("1.sw", BASE), ("2.sw", &b), ("3.sw", &a), ("4.sw", day)]),
        reference
    );
    // `B`'s procedure is the one chosen: it's last in canonical order. So
    // the same use, where `A` has none, has the same hash.
    let a_without = "namespace A\n\ndef other: Nat := 1\n";
    let day_without = "namespace Day

import Base (needsToken)
import A (other)
import B (decB)

def client: Nat := needsToken
";
    assert_eq!(
        hash(&[
            ("base.sw", BASE),
            ("a.sw", a_without),
            ("b.sw", &b),
            ("day.sw", day_without)
        ]),
        reference
    );
}

#[test]
fn abilities_from_two_namespaces_hash_the_same_in_any_order() {
    let x = "namespace X\n\nability Log where\n  say : Nat -> {Log} ()\n";
    let y = "namespace Y\n\nability Ask where\n  ask : () -> {Ask} Nat\n";
    let day = "namespace Day

import X (Log)
import Y (Ask)

def both(): {Ask, Log} Nat :=
  say 1
  ask()
";
    let hash = |files: &[(&str, &str)]| def_hash_of(&load(files), "Day.both");
    let reference = hash(&[("x.sw", x), ("y.sw", y), ("day.sw", day)]);
    assert_eq!(
        hash(&[("day.sw", day), ("y.sw", y), ("x.sw", x)]),
        reference
    );
    assert_eq!(hash(&[("1.sw", y), ("2.sw", x), ("3.sw", day)]), reference);
    // Written the other way round in the row, the same type.
    let flipped = day.replace("{Ask, Log}", "{Log, Ask}");
    assert_eq!(
        hash(&[("x.sw", x), ("y.sw", y), ("day.sw", &flipped)]),
        reference
    );
}

#[test]
fn tests_in_two_namespaces_with_the_same_name() {
    let file = |ns: &str| {
        format!(
            "namespace {ns}\n\n\
             test \"example\" :=\n  def double (n: Nat): Nat := n + n\n  match double 1 with\n    | Zero => False\n    | Succ k => True\n"
        )
    };
    let session = load(&[("a.sw", &file("A")), ("b.sw", &file("B"))]);
    let tests: Vec<(&str, &str)> = session
        .elab
        .tests
        .iter()
        .map(|t| (t.namespace.as_str(), t.name.as_str()))
        .collect();
    assert_eq!(tests, [("A", "example"), ("B", "example")]);
    passes(&session);
    // In a file, a repeated test name in one session is still refused.
    let mut session = Session::new();
    session.load("a.sw", "test \"example\" := True\n").unwrap();
    assert!(session.load("b.sw", "test \"example\" := True\n").is_err());
}

#[test]
fn a_project_file_alone_means_the_same_in_file_mode() {
    let solo = "namespace Solo

type Shape: Type =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

def Shape.area: Shape -> Nat
  | Square s => s * s
  | Rect w h => w * h

test \"area\" := (Rect 2 3).area == 6 && Square 2 == Square 2
";
    let hashes = |session: &Session| -> BTreeMap<String, ContentHash> {
        let g = &session.elab.globals;
        let mut out = BTreeMap::new();
        for (i, d) in g.defs.iter().enumerate() {
            if d.path.starts_with("Solo.") {
                out.insert(d.path.to_string(), def_hash(g, DefId(i)).unwrap().unwrap());
            }
        }
        for (i, d) in g.datas.iter().enumerate() {
            if d.path.starts_with("Solo.") {
                out.insert(
                    d.path.to_string(),
                    data_hash(g, DataId(i)).unwrap().unwrap(),
                );
            }
        }
        out
    };
    let mut file_mode = Session::new();
    file_mode.load("solo.sw", solo).unwrap();
    let project = load(&[("solo.sw", solo), ("lib.sw", LIB)]);
    let (a, b) = (hashes(&file_mode), hashes(&project));
    assert!(a.len() > 5, "{a:?}");
    assert_eq!(a, b);
}

#[test]
fn a_siblings_declaration_changes_the_meaning() {
    let a = "namespace N\n\ndef f (b: Bool): Bool := not b\n";
    let b = "namespace N\n\ndef not (b: Bool): Bool := b\n";
    let project = load(&[("a.sw", a), ("b.sw", b)]);
    let alone = load(&[("a.sw", a)]);
    assert_ne!(def_hash_of(&project, "N.f"), def_hash_of(&alone, "N.f"));
}

#[test]
fn eval_after_a_project_load_needs_full_names() {
    let lib = "namespace Day\n\ndef x: Nat := 1\n";
    let mut session = load(&[("day.sw", lib)]);
    let full = session.parse_expression("<eval>", "Day.x").unwrap();
    session.elab.infer_expr(&full).unwrap();
    let short = session.parse_expression("<eval>", "x").unwrap();
    assert_eq!(
        session.elab.infer_expr(&short).unwrap_err().code,
        "E-UNKNOWN-NAME"
    );
}

fn config(text: &str) -> Result<Vec<String>, Diagnostic> {
    let mut sources = stitchwort_syntax::SourceMap::new();
    let id = sources.add("proj/stitchwort.yaml", text);
    parse_config(id, "proj/stitchwort.yaml", text).map(|c| c.sources)
}

#[test]
fn config_defaults_and_folders() {
    assert_eq!(config("").unwrap(), ["src"]);
    assert_eq!(config("# nothing here\n\n").unwrap(), ["src"]);
    assert_eq!(config("sources: null\n").unwrap(), ["src"]);
    assert_eq!(config("sources: [lib, src]\n").unwrap(), ["lib", "src"]);
    assert_eq!(
        config("sources:\n  - ./lib/\n  - .\n  - lib\n").unwrap(),
        ["lib", ""]
    );
}

/// `no` isn't read as `false`: it's a folder's name.
#[test]
fn config_booleans_and_numbers_are_text() {
    assert_eq!(config("sources: [no]\n").unwrap(), ["no"]);
    let d = config("sources: [2025]\n").unwrap_err();
    assert_eq!(d.code, "E-PROJECT-CONFIG");
    assert!(d.message.contains("must be quoted"), "{}", d.message);
    assert_eq!(d.labels.len(), 1);
}

#[test]
fn config_errors_say_what_is_wrong() {
    let d = config("sources: [a]\nsources: [b]\n").unwrap_err();
    assert!(
        d.message.ends_with("`sources` is written twice"),
        "{}",
        d.message
    );
    let d = config("source: [a]\n").unwrap_err();
    assert!(d.message.ends_with("unknown key `source`"), "{}", d.message);
    assert_eq!(d.notes, ["the known key is `sources`"]);
    let d = config("sources: 5\n").unwrap_err();
    assert!(d.message.ends_with("expected a list"), "{}", d.message);
    let d = config("sources: []\n").unwrap_err();
    assert!(d.message.ends_with("`sources` lists no folders"));
    for outside in ["sources: [..]\n", "sources: [a/../..]\n", "sources: [/x]\n"] {
        let d = config(outside).unwrap_err();
        assert!(
            d.message.contains("outside the project folder"),
            "{}",
            d.message
        );
    }
}

fn memory(files: &[(&str, &str)], reversed: bool) -> MemoryFiles {
    MemoryFiles {
        files: files
            .iter()
            .map(|(p, t)| (p.to_string(), t.to_string()))
            .collect(),
        reversed,
    }
}

#[test]
fn reading_a_project_finds_every_sw_file_once() {
    let files = memory(
        &[
            ("stitchwort.yaml", "sources: [., src]\n"),
            ("a.sw", "namespace A\n"),
            ("src/b.sw", "namespace B\n"),
            ("src/deep/c.sw", "namespace C\n"),
            (".hidden/d.sw", "namespace D\n"),
            ("notes.txt", "not a source"),
        ],
        false,
    );
    let mut sources = stitchwort_syntax::SourceMap::new();
    let found = project_sources(&files, "proj", &mut sources).unwrap();
    let paths: Vec<&str> = found.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(paths, ["a.sw", "src/b.sw", "src/deep/c.sw"]);
}

#[test]
fn reading_a_project_reports_missing_and_nested_folders() {
    let mut sources = stitchwort_syntax::SourceMap::new();
    let files = memory(&[("stitchwort.yaml", "sources: [lib]\n")], false);
    let d = project_sources(&files, "proj", &mut sources).unwrap_err();
    assert!(
        d[0].message
            .contains("the source folder `lib` doesn't exist")
    );
    let files = memory(
        &[
            ("stitchwort.yaml", ""),
            ("src/a.sw", "namespace A\n"),
            ("src/inner/stitchwort.yaml", ""),
            ("src/inner/b.sw", "namespace B\n"),
        ],
        false,
    );
    let d = project_sources(&files, "proj", &mut sources).unwrap_err();
    assert!(
        d[0].message
            .contains("`src/inner/` is a project inside the project proj/"),
        "{}",
        d[0].message
    );
}

/// The order a directory is listed in never reaches hashes or test order.
#[test]
fn directory_order_doesnt_matter() {
    let project = [
        ("stitchwort.yaml", ""),
        ("src/a.sw", "namespace A\n\ntest \"a\" := True\n"),
        ("src/b.sw", "namespace B\n\ntest \"b\" := A.f == 1\n"),
        ("src/c.sw", "namespace A\n\ndef f: Nat := 1\n"),
    ];
    let run = |reversed: bool| {
        let mut session = Session::new();
        let loaded = session
            .load_project(&memory(&project, reversed), "proj", &Target::Everything)
            .unwrap_or_else(|e| panic!("{e:#?}"));
        let tests: Vec<String> = session.elab.tests.iter().map(|t| t.name.clone()).collect();
        (loaded.checked, tests, def_hash_of(&session, "A.f"))
    };
    assert_eq!(run(false), run(true));
}

/// Renaming and moving files, with the same text, changes nothing: every
/// test result is a cache hit (docs/proposals/multi-file.md §8).
#[test]
fn moving_files_keeps_every_cache_hit() {
    let a = "namespace A\n\ndef f: Nat := 1\n\ntest \"f\" := f == 1\n";
    let b = "namespace B\n\ntest \"g\" := A.f + 1 == 2\n";
    let first = memory(
        &[("stitchwort.yaml", ""), ("src/a.sw", a), ("src/b.sw", b)],
        false,
    );
    let mut session = Session::new();
    session
        .load_project(&first, "proj", &Target::Everything)
        .unwrap();
    let cache = Cache::memory([]);
    let results = session.run_tests(&cache);
    assert!(results.iter().all(|r| !r.cached));
    let moved = memory(
        &[
            ("stitchwort.yaml", ""),
            ("src/alpha.sw", a),
            ("src/deeper/b-file.sw", b),
        ],
        false,
    );
    let mut again = Session::new();
    again
        .load_project(&moved, "proj", &Target::Everything)
        .unwrap();
    let results = again.run_tests(&Cache::memory(cache.added()));
    assert_eq!(results.len(), 2);
    assert!(results.iter().all(|r| r.cached));
}

#[test]
fn an_unknown_target_is_named() {
    let (_, result) = load_target(&[("lib.sw", LIB)], &Target::Namespaces(vec!["Lbi".into()]));
    let found = result.err().unwrap();
    assert_eq!(found[0].code, "E-NAMESPACE-UNKNOWN");
    assert_eq!(found[0].notes, ["did you mean `Lib`?"]);
}

/// An import's path is found without the file's other imports, so the order
/// of two import lines never changes what they mean, and the pre-pass sees
/// the same project namespace that checking does.
#[test]
fn import_order_doesnt_matter() {
    let a = "namespace A\n\ntype Cat = | MkA\n\ndef Cat.f: Nat := 7\n";
    let cat = "namespace Cat\n\ndef f: Nat := 1\n";
    for bay in [
        "namespace Bay\n\nimport A (Cat)\nimport Cat (f)\n\ndef g: Nat := f\n\ntest \"which\" := g == 1\n",
        "namespace Bay\n\nimport Cat (f)\nimport A (Cat)\n\ndef g: Nat := f\n\ntest \"which\" := g == 1\n",
    ] {
        let files = [("a.sw", a), ("cat.sw", cat), ("bay.sw", bay)];
        let session = load(&files);
        passes(&session);
        let mut analysing = Session::new();
        let analysis = stitchwort_driver::project::analyse(&mut analysing, "proj", owned(&files));
        let targets: Vec<&str> = analysis
            .namespace("Bay")
            .expect("Bay")
            .edges
            .iter()
            .map(|e| e.target.as_str())
            .collect();
        assert_eq!(targets, ["A", "Cat"]);
    }
}

#[test]
fn auto_uses_a_namespace_only_wildcard_imported() {
    let zed = "namespace Zed

type Token: Prop =
  | MkToken

def needsToken: [auto t: Token] -> Nat := 1

instance decZ: Decidable Token := Yes MkToken
";
    let alpha = "namespace Alpha

import Zed (..)

def client: Nat := needsToken

test \"client\" := client == 1
";
    passes(&load(&[("zed.sw", zed), ("alpha.sw", alpha)]));
    let (session, loaded) = load_target(
        &[("zed.sw", zed), ("alpha.sw", alpha)],
        &Target::Namespaces(vec!["Alpha".to_string()]),
    );
    let loaded = loaded.unwrap_or_else(|e| panic!("{e:#?}"));
    assert_eq!(loaded.checked, ["Zed", "Alpha"]);
    passes(&session);
}

const LIB_WITH_IMPORT: &str = "namespace Lib

import Base (helper)

type Range = { lo: Nat, hi: Nat }

def Range.size (r: Range): Nat := r.hi + r.lo

def libThing: Nat := helper
";
const BASE_HELPER: &str = "namespace Base\n\ndef helper: Nat := 1\n";

#[test]
fn a_wildcard_doesnt_bring_the_namespaces_imports() {
    let day = |body: &str| format!("namespace Day\n\nimport Lib (..)\n\n{body}\n");
    let files = |body: &str| {
        [
            ("base.sw", BASE_HELPER.to_string()),
            ("lib.sw", LIB_WITH_IMPORT.to_string()),
            ("day.sw", day(body)),
        ]
    };
    let run = |body: &str| {
        let owned = files(body);
        let refs: Vec<(&str, &str)> = owned.iter().map(|(p, t)| (*p, t.as_str())).collect();
        errors(&refs)
    };
    // `helper` is `Lib`'s own import, not `Lib`'s.
    assert_eq!(codes(&run("def a: Nat := helper")), ["E-UNKNOWN-NAME"]);
    // `Range.size` is inside `Range`.
    assert_eq!(
        codes(&run("def b (r: Range): Nat := size r")),
        ["E-UNKNOWN-NAME"]
    );
    // `Range` and `libThing` are.
    let owned =
        files("def c (r: Range): Nat := Range.size r + libThing\n\ntest \"c\" := libThing == 1");
    let refs: Vec<(&str, &str)> = owned.iter().map(|(p, t)| (*p, t.as_str())).collect();
    passes(&load(&refs));
}

#[test]
fn a_wildcard_isnt_shared_with_sibling_files() {
    let found = errors(&[
        ("lib.sw", "namespace Lib\n\ndef f: Nat := 1\n"),
        (
            "day1.sw",
            "namespace Day\n\nimport Lib (..)\n\ndef a: Nat := f\n",
        ),
        ("day2.sw", "namespace Day\n\ndef b: Nat := f\n"),
    ]);
    assert_eq!(codes(&found), ["E-UNKNOWN-NAME"]);
    assert!(found[0].message.contains("`f`"));
}

#[test]
fn a_wildcard_brings_every_file_of_the_namespace() {
    let session = load(&[
        ("lib1.sw", "namespace Lib\n\ndef one: Nat := 1\n"),
        ("lib2.sw", "namespace Lib\n\ndef two: Nat := 2\n"),
        (
            "day.sw",
            "namespace Day\n\nimport Lib (..)\n\ntest \"both\" := one + two == 3\n",
        ),
    ]);
    passes(&session);
}

#[test]
fn adding_through_a_wildcard_is_foreign() {
    let found = errors(&[
        ("lib.sw", LIB),
        (
            "day.sw",
            "namespace Day\n\nimport Lib (..)\n\ndef Range.extra (r: Range): Nat := 1\n",
        ),
    ]);
    assert_eq!(codes(&found), ["E-FOREIGN-NAMESPACE"]);
    assert!(
        found[0].message.contains("belongs to namespace Lib"),
        "{found:#?}"
    );
}

#[test]
fn wildcard_refusals_in_a_project() {
    let day = |import: &str| format!("namespace Day\n\n{import}\n\ndef x: Nat := 1\n");
    // Part of a namespace.
    let found = errors(&[("lib.sw", LIB), ("day.sw", &day("import Lib.Range (..)"))]);
    assert_eq!(codes(&found), ["E-IMPORT-WILDCARD"]);
    assert!(found[0].message.contains("is part of namespace Lib"));
    // Only the start of namespace names.
    let found = errors(&[
        ("d5.sw", "namespace Aoc.Day05\n\ndef y: Nat := 1\n"),
        ("day.sw", &day("import Aoc (..)")),
    ]);
    assert!(
        ["E-IMPORT-WILDCARD", "E-IMPORT-UNKNOWN"].contains(&found[0].code),
        "{found:#?}"
    );
    // Its own namespace.
    let found = errors(&[("day.sw", &day("import Day (..)"))]);
    assert_eq!(codes(&found), ["E-IMPORT-WILDCARD"]);
    assert!(found[0].message.contains("is this file's own namespace"));
}

#[test]
fn wildcard_project_file_order_doesnt_change_hashes() {
    let project = [
        ("stitchwort.yaml", ""),
        ("src/a.sw", "namespace A\n\ndef f: Nat := 1\n"),
        (
            "src/b.sw",
            "namespace B\n\nimport A (..)\n\ndef g: Nat := f + 1\n\ntest \"g\" := g == 2\n",
        ),
        ("src/c.sw", "namespace A\n\ndef h: Nat := 5\n"),
    ];
    let run = |reversed: bool| {
        let mut session = Session::new();
        let loaded = session
            .load_project(&memory(&project, reversed), "proj", &Target::Everything)
            .unwrap_or_else(|e| panic!("{e:#?}"));
        (
            loaded.checked,
            def_hash_of(&session, "A.f"),
            def_hash_of(&session, "B.g"),
        )
    };
    assert_eq!(run(false), run(true));
}

/// The pre-pass's table of a namespace's direct names is the set of
/// single-component keys of the checked scope, for every accepted project
/// (generated `%` names aside).
#[test]
fn the_names_table_matches_the_scope() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept");
    let mut dirs: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    for dir in dirs {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let mut session = Session::new();
        let files = stitchwort_driver::project::DiskFiles { root: dir };
        let loaded = session
            .load_project(&files, &name, &Target::Everything)
            .unwrap_or_else(|e| panic!("{name}: {e:#?}"));
        for namespace in &loaded.checked {
            let table = session
                .elab
                .project_names(namespace)
                .unwrap_or_else(|| panic!("{name}: no names for {namespace}"));
            assert_eq!(
                table,
                &session.elab.direct_keys(namespace),
                "{name}: {namespace}"
            );
        }
    }
}

/// Own > named import > `(..)` import > default, across namespaces (the
/// `wildcard-precedence` example project, in memory).
#[test]
fn wildcard_precedence_across_namespaces() {
    macro_rules! source {
        ($name:literal) => {
            include_str!(concat!(
                "../../../examples/projects/accept/wildcard-precedence/src/",
                $name
            ))
        };
    }
    let session = load(&[
        ("lib.sw", source!("lib.sw")),
        ("lib-more.sw", source!("lib-more.sw")),
        ("other.sw", source!("other.sw")),
        ("twin.sw", source!("twin.sw")),
        ("day.sw", source!("day.sw")),
    ]);
    passes(&session);
}

/// Checks `files` as a project, then walks the checked types and bodies of
/// every namespace and asserts that each reaches only itself, the namespaces
/// of its closure in the pre-pass, or the library: what name resolution found
/// agrees with what the pre-pass planned (docs/proposals/multi-file.md §4.6).
fn assert_reaches_only_planned(label: &str, files: Vec<(String, String)>) {
    use stitchwort_core::Term;
    use stitchwort_driver::project::{analyse, closure};
    let analysis = analyse(&mut Session::new(), "proj", files.clone());
    let mut session = Session::new();
    let loaded = session
        .load_project_sources("proj", files, &Target::Everything)
        .unwrap_or_else(|e| panic!("{label}: {e:#?}"));
    let g = &session.elab.globals;
    let ranges: Vec<(String, std::ops::Range<usize>)> = loaded
        .checked
        .iter()
        .map(|n| (n.clone(), session.elab.namespace_def_range(n)))
        .collect();
    // Definitions in `Std` are the library's, wherever they loaded.
    let def_namespace = |id: DefId| {
        if g.def(id).path.starts_with("Std.") {
            return Some(None);
        }
        ranges
            .iter()
            .find(|(_, r)| r.contains(&id.0))
            .map(|(n, _)| Some(n.as_str()))
    };
    let data_namespace = |d: DataId| {
        let path = &*g.data(d).path;
        loaded
            .checked
            .iter()
            .filter(|n| path.starts_with(&format!("{n}.")))
            .max_by_key(|n| n.len())
            .map(String::as_str)
    };
    for (namespace, range) in &ranges {
        let mut terms: Vec<&Term> = Vec::new();
        for def in &g.defs[range.clone()] {
            terms.push(&def.ty);
            terms.extend(def.body().map(|b| &**b));
        }
        for d in (0..g.datas.len()).map(DataId) {
            if data_namespace(d) == Some(namespace.as_str()) {
                let data = g.data(d);
                terms.extend(data.params.iter().map(|(_, t)| t));
                terms.extend(
                    data.ctors
                        .iter()
                        .flat_map(|c| c.fields.iter().map(|(_, t)| t)),
                );
            }
        }
        let allowed = closure(&analysis, std::slice::from_ref(namespace));
        for term in terms {
            for (t, _) in term.subterms() {
                let reached = match t {
                    Term::Def(id) => def_namespace(*id)
                        .unwrap_or_else(|| panic!("{label}: {namespace} reaches stray def {id:?}")),
                    Term::Data(d, _) | Term::Ctor(d, ..) => data_namespace(*d),
                    _ => continue,
                };
                if let Some(reached) = reached {
                    assert!(
                        allowed.iter().any(|a| a == reached),
                        "{label}: {namespace} reaches {reached}, which the pre-pass didn't plan (closure: {allowed:?})"
                    );
                }
            }
        }
    }
}

#[test]
fn checked_terms_only_reach_planned_namespaces() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept");
    let mut dirs: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    for dir in dirs {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let files = stitchwort_driver::project::DiskFiles { root: dir };
        let mut sources = stitchwort_syntax::SourceMap::new();
        let found = project_sources(&files, &name, &mut sources)
            .unwrap_or_else(|e| panic!("{name}: {e:#?}"));
        assert_reaches_only_planned(&name, found);
    }
    assert_reaches_only_planned("shadowing", owned(&SHADOWING));
    // In memory: wildcards of several namespaces over several files.
    assert_reaches_only_planned(
        "in memory",
        owned(&[
            ("lib1.sw", "namespace Lib\n\ndef one: Nat := 1\n"),
            ("lib2.sw", "namespace Lib\n\ndef two: Nat := 2\n"),
            (
                "day.sw",
                "namespace Day\n\nimport Lib (..)\n\ntest \"both\" := one + two == 3\n",
            ),
        ]),
    );
}

/// `Lib`'s type `Range` comes in through `(..)`, so `Range.make` in `Zday` is
/// `Lib.Range.make` (7), not the project namespace `Range`'s (99), which
/// sorts, and is checked, first.
const SHADOWING: [(&str, &str); 3] = [
    (
        "lib.sw",
        "namespace Lib\n\ntype Range =\n  | R (n: Nat)\n\ndef Range.make: Nat := 7\n",
    ),
    ("range.sw", "namespace Range\n\ndef make: Nat := 99\n"),
    (
        "zday.sw",
        "namespace Zday\n\nimport Lib (..)\n\ntest \"t\" := Range.make == 7\n",
    ),
];

#[test]
fn a_wildcard_name_shadows_a_project_namespace() {
    passes(&load(&SHADOWING));
}

/// Two types with the same name make their constructors ambiguous, not
/// unknown, whether they come in by name or with `(..)`.
#[test]
fn constructors_of_two_same_named_types_are_ambiguous() {
    let lib = "namespace Lib\n\ntype Range =\n  | R\n";
    let twin = "namespace Twin\n\ntype Range =\n  | R\n";
    for imports in [
        "import Lib (Range)\nimport Twin (Range)",
        "import Lib (..)\nimport Twin (..)",
    ] {
        let day = format!("namespace Day\n\n{imports}\n\ntest \"u\" := R == R\n");
        let found = errors(&[("lib.sw", lib), ("twin.sw", twin), ("day.sw", &day)]);
        assert_eq!(codes(&found), ["E-AMBIGUOUS"], "{imports}");
        assert!(
            found[0].message.contains("`Lib.Range.R`")
                && found[0].message.contains("`Twin.Range.R`"),
            "{found:#?}"
        );
        assert!(
            found[0].notes.iter().all(|n| !n.contains("library has")),
            "{found:#?}"
        );
    }
}
