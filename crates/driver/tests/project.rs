//! Checking a project: namespaces in canonical order, each with its
//! dependencies in scope (docs/proposals/multi-file.md §4, §12). Sources are
//! in memory.

use std::collections::BTreeMap;

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_driver::project::{Loaded, Target};
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
    let a = "namespace A\n\nimport Base (Token)\n\ndef decA: Decidable Token := Yes MkToken\n";
    let another =
        "namespace Another\n\nimport Base (Token)\n\ndef decU: Decidable Token := Yes MkToken\n";
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
            "namespace {ns}\n\nimport Base (Token)\n\ndef {name}: Decidable Token := Yes MkToken\n"
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

#[test]
fn an_unknown_target_is_named() {
    let (_, result) = load_target(&[("lib.sw", LIB)], &Target::Namespaces(vec!["Lbi".into()]));
    let found = result.err().unwrap();
    assert_eq!(found[0].code, "E-NAMESPACE-UNKNOWN");
    assert_eq!(found[0].notes, ["did you mean `Lib`?"]);
}
