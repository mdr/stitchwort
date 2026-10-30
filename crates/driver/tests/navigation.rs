//! The code navigation index (docs/proposals/code-navigation.md): which
//! declaration or binder each written name refers to. Sources are in memory;
//! the snapshots list each reference as `line:col text -> target`.

use stitchwort_driver::driver::Session;
use stitchwort_driver::nav::{index_json, index_of};
use stitchwort_elab::{NavIndex, NavTarget};
use stitchwort_syntax::Span;

const NAV: &str = "namespace Nav

import Lib (Range)

type Shape =
  | Circle (r: Nat)
  | Square (side: Nat)

def area (s: Shape): Nat :=
  match s with
    | Circle r => r * r * 3
    | Square side => side * side

def total (xs: List Nat): Nat :=
  def go (acc: Nat) (ys: List Nat): Nat :=
    match ys with
      | [] => acc
      | Cons y rest => go (acc + y) rest
  let start := 0
  go start xs

def doubled (xs: List Nat): List Nat := xs.map (n => n + n)

def piped (xs: List Nat): List Nat := xs |> .map (n => n + 1)

def width (r: Range): Nat := r.hi

def qualified (r: Lib.Range): Nat := Lib.Range.size r

def build: Range := { lo = 1, hi = 2 }
";

const LIB: &str = "namespace Lib

type Range = { lo: Nat, hi: Nat }

def Range.size (r: Range): Nat := r.hi + r.lo
";

fn project() -> Session {
    let mut session = Session::navigable();
    let files = vec![
        ("proj/src/Nav/Nav.sw".to_string(), NAV.to_string()),
        ("proj/src/Lib/Lib.sw".to_string(), LIB.to_string()),
    ];
    let target = stitchwort_driver::project::Target::Everything;
    session
        .load_project_sources("proj", files, &target)
        .expect("checks");
    session
}

/// `text` of `span`, `line:col` of its start (both from 1).
fn place(session: &Session, span: Span) -> (String, String) {
    let file = session.sources.get(span.file);
    let before = &file.text[..span.start as usize];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().unwrap().chars().count() + 1;
    (
        file.text[span.range()].to_string(),
        format!("{}:{line}:{col}", file.name.rsplit('/').next().unwrap()),
    )
}

fn lines(session: &Session, index: &NavIndex, only: &str) -> String {
    let mut out = String::new();
    for r in &index.refs {
        let (text, at) = place(session, r.span);
        if !at.starts_with(only) {
            continue;
        }
        let text = r.dot.as_ref().map_or(text, |d| d.clone());
        let target = match &r.target {
            NavTarget::Symbol(i) => {
                let s = &index.symbols[*i];
                let (_, at) = place(session, s.span);
                format!("{} [{}] {at}", s.name, s.kind)
            }
            NavTarget::Binder { name, span } => {
                let (_, at) = place(session, *span);
                format!("local {name} {at}")
            }
        };
        let ty = r.ty.as_deref().unwrap_or("");
        out.push_str(&format!("{at} {text} -> {target} : {ty}\n"));
    }
    out
}

#[test]
fn references_of_a_project() {
    let session = project();
    let index = index_of(&session);
    insta::assert_snapshot!("nav-project", lines(&session, &index, "Nav.sw"));
}

/// The specific entries the language server and the editor depend on.
#[test]
fn the_entries_of_each_kind() {
    let session = project();
    let index = index_of(&session);
    let all = lines(&session, &index, "Nav.sw");
    for expected in [
        // an import
        "Nav.sw:3:13 Range -> Lib.Range [record] Lib.sw:3:6",
        // a qualified name
        "Nav.sw:28:38 Lib.Range.size -> Lib.Range.size [def] Lib.sw:5:5",
        // dot notation on a List, chosen by the type of `xs`
        "Nav.sw:22:44 map -> Std.List.map [def]",
        // a pipe
        "Nav.sw:24:46 map -> Std.List.map [def]",
        // a constructor in a pattern
        "Nav.sw:11:7 Circle -> Nav.Shape.Circle [ctor] Nav.sw:6:5",
        "Nav.sw:18:9 Cons -> Std.List.Cons [ctor]",
        // a record field: projection and literal
        "Nav.sw:26:32 hi -> Lib.Range.hi [field] Lib.sw:3:25",
        "Nav.sw:30:23 lo -> Lib.Range.lo [field] Lib.sw:3:16",
        // a local def, and a let variable
        "Nav.sw:20:3 go -> local go Nav.sw:15:7",
        "Nav.sw:20:6 start -> local start Nav.sw:19:7 : Nat",
        // a pattern variable, and a lambda variable
        "Nav.sw:18:34 y -> local y Nav.sw:18:14 : Nat",
        "Nav.sw:22:58 n -> local n Nav.sw:22:49 : Nat",
    ] {
        assert!(all.contains(expected), "missing `{expected}` in\n{all}");
    }
}

/// With recording off, nothing is kept.
#[test]
fn off_by_default() {
    let mut session = Session::new();
    let files = vec![("proj/src/Lib/Lib.sw".to_string(), LIB.to_string())];
    let target = stitchwort_driver::project::Target::Everything;
    session
        .load_project_sources("proj", files, &target)
        .expect("checks");
    let index = session.elab.navigation_index(&|_, _| true);
    assert!(index.refs.is_empty() && index.symbols.is_empty());
}

/// What was elaborated is still indexed when a later declaration fails.
#[test]
fn partial_when_checking_fails() {
    let mut session = Session::navigable();
    let source = "def ok (xs: List Nat): Nat := xs.length\n\ndef bad (xs: List Nat): Nat := xs.map (n => n)\n";
    assert!(session.load("one.sw", source).is_err());
    let json = index_json(&session, true, Some(false), "", &[]);
    assert!(json.starts_with(r#"{"version":3,"errors":true,"ok":false,"files":["#));
    assert!(json.contains(r#""name":"Std.List.length""#), "{json}");
    assert!(json.contains(r#""name":"Main.ok","kind":"def""#), "{json}");
}

/// Columns count UTF-16 code units, and lines and columns start at 0.
#[test]
fn columns_are_utf16() {
    let mut session = Session::navigable();
    let source = "def f (t: Text): Text := \"😀\" ++ t\n";
    session.load("one.sw", source).expect("checks");
    let json = index_json(&session, false, None, "", &[]);
    // `t` in the body: `def f (t: Text): Text := "😀" ++ t`; the emoji is
    // one character, two UTF-16 units, so the column is one more than the
    // number of characters before it.
    let chars_before = source[..source.rfind('t').unwrap()].chars().count();
    let expected = format!(
        r#""range":[0,{},0,{}],"binder":{{"name":"t","file":0,"range":[0,7,0,8]}}"#,
        chars_before + 1,
        chars_before + 2
    );
    assert!(json.contains(&expected), "{expected}\n{json}");
}

/// A library target is marked, with the path under `std/` to read it from.
#[test]
fn library_targets_are_marked() {
    let mut session = Session::navigable();
    session
        .load("one.sw", "def f (xs: List Nat): Nat := xs.length\n")
        .expect("checks");
    let json = index_json(&session, false, None, "", &[]);
    assert!(json.contains(r#"{"path":"crates/elab/src/std/core/Data.sw","std":"core/Data.sw"}"#));
    let text = stitchwort_driver::nav::std_source("core/Data.sw", session.elab.limits.stack)
        .expect("embedded");
    assert!(text.contains("List"));
    assert!(stitchwort_driver::nav::std_source("nope.sw", session.elab.limits.stack).is_none());
}

/// Diagnostics come with the index: where, what, the other labels and notes.
#[test]
fn diagnostics_are_in_the_index() {
    let mut session = Session::navigable();
    let source = "def f: Nat := \"a\"\n";
    let errors = session.load("one.sw", source).expect_err("fails");
    let json = index_json(&session, true, None, "", &errors);
    assert!(
        json.contains(
            r#""diagnostics":[{"severity":"error","code":"E-TYPE-MISMATCH","message":"type mismatch","file":0,"range":[0,14,0,17],"labels":[{"file":0,"range":[0,14,0,17],"message":"expected `Nat`, but this has type `Text`"}],"notes":[]}]"#
        ),
        "{json}"
    );
}

/// A name's own declaration refers to it; a single file's names are
/// qualified with `Main.` as a project's are with the namespace; a symbol's
/// range is its last name component; `container` is always there.
#[test]
fn declarations_refer_to_themselves() {
    let mut session = Session::navigable();
    let source = "type Bag = { n: Nat }\n\ndef Bag.size (b: Bag): Nat := b.n\n\ndef use (b: Bag): Nat := b.size\n";
    session.load("one.sw", source).expect("checks");
    let json = index_json(&session, false, None, "", &[]);
    assert!(
        json.contains(
            r#"{"name":"Main.Bag.size","kind":"def","file":0,"range":[2,8,2,12],"fullRange":[2,0,2,33],"container":null,"#
        ),
        "{json}"
    );
    // the declaration's own name, then the use by dot notation: one symbol
    assert!(
        json.contains(r#"{"file":0,"range":[2,8,2,12],"symbol":2,"#),
        "{json}"
    );
    assert!(
        json.contains(r#"{"file":0,"range":[4,27,4,31],"symbol":2,"#),
        "{json}"
    );
    assert!(!json.contains(r#""name":"Bag.size""#), "{json}");
    assert_eq!(
        json.matches(r#""name":"Main.Bag.size""#).count(),
        1,
        "{json}"
    );
}

/// Names inside the library's files are references too, so that navigation
/// continues there.
#[test]
fn library_files_have_references() {
    let mut session = Session::navigable();
    session
        .load("one.sw", "def f (xs: List Nat): Nat := xs.length\n")
        .expect("checks");
    let index = index_of(&session);
    let std_files = session.elab.std_file_count();
    assert!(
        index.refs.iter().any(|r| r.span.file.index() < std_files),
        "no references in library files"
    );
}

/// The core's own names are references too (it is the first file of the
/// index, `core/Data.sw` among its files): a user of the playground or editor who jumps into it
/// can go on from there. This needs recording from the start of the session,
/// since the core is loaded when the session is made.
#[test]
fn the_core_has_references() {
    let mut session = Session::navigable();
    session
        .load("one.sw", "def f (xs: List Nat): Nat := xs.length\n")
        .expect("checks");
    let index = index_of(&session);
    let in_core = index
        .refs
        .iter()
        .filter(|r| r.span.file.index() == 0)
        .count();
    assert!(in_core > 100, "only {in_core} references in the core");
    // A name used in the core refers to its declaration there.
    let json = index_json(&session, false, None, "", &[]);
    assert!(json.contains(r#"{"path":"crates/elab/src/std/core/Data.sw","std":"core/Data.sw"}"#));
}

/// A library declaration that something refers to has a reference at its own
/// name too, so that hover, definition and references work there when the
/// library file is open.
#[test]
fn library_declarations_refer_to_themselves() {
    let mut session = Session::navigable();
    session
        .load("one.sw", "def f (xs: List Nat): Nat := xs.length\n")
        .expect("checks");
    let index = index_of(&session);
    let at = index
        .symbols
        .iter()
        .position(|s| s.name == "Std.List.length")
        .expect("the symbol");
    let span = index.symbols[at].span;
    assert!(
        index.refs.iter().any(|r| r.span.file == span.file
            && r.span.end == span.end
            && matches!(r.target, NavTarget::Symbol(s) if s == at)),
        "no reference at the declaration of List.length"
    );
}

/// Names inside the `${…}` of a `"""` text, and after it, are placed by their
/// own line and UTF-16 column, though the literal spans several lines.
#[test]
fn positions_inside_and_after_a_multi_line_text() {
    let mut session = Session::navigable();
    let source = "def f (t: Text): Text := \"\"\"\n  😀 ${t}\n  é ${t}\n  \"\"\" ++ t\n";
    session.load("one.sw", source).expect("checks");
    let json = index_json(&session, false, None, "", &[]);
    for range in ["[1,7,1,8]", "[2,6,2,7]", "[3,9,3,10]"] {
        let expected =
            format!(r#""range":{range},"binder":{{"name":"t","file":0,"range":[0,7,0,8]}}"#);
        assert!(json.contains(&expected), "{expected}\n{json}");
    }
}

/// A local's type noted inside an attempt that is then undone (a pipe into a
/// dot section tries the receiver first) is dropped with the attempt's
/// metavariables, not printed after later ones have reused their numbers
/// (that panicked: "applying a data type"). The retry notes it again.
#[test]
fn a_local_noted_in_an_undone_attempt() {
    let mut session = Session::navigable();
    let body = "  xs.filterMap (c => o.flatMap (b => g b c)) |> .head\n";
    let source = format!(
        "def g (b: Nat) (c: Nat): Option Nat := Option.Some (b + c)\n\n\
         def f (xs: List Nat) (o: Option Nat): Option Nat :=\n{body}"
    );
    session.load("one.sw", &source).expect("checks");
    let index = index_of(&session);
    let col = body.find("g b").unwrap() + 3;
    let b = index
        .refs
        .iter()
        .find(|r| place(&session, r.span) == ("b".to_string(), format!("one.sw:4:{col}")))
        .expect("a reference at `b`");
    assert_eq!(b.ty.as_deref(), Some("Nat"));
}

/// The index doesn't depend on a hash map's order (each session's maps are
/// seeded differently): the same source gives the same JSON every time, and
/// the library's `Ord.equal` is named and typed as the field a user writes,
/// not as its generated `%equal` member (SW-244).
#[test]
fn the_index_is_the_same_every_time() {
    let source = "def same: Nat -> Nat -> Bool\n  | a, b => a == b\n\n\
                  def less: Nat -> Nat -> Bool\n  | a, b => a < b\n\n\
                  def both: Nat -> Nat -> Bool\n  | a, b => a == b && a <= b\n";
    let build = || {
        let mut session = Session::navigable();
        session.load("one.sw", source).expect("checks");
        stitchwort_driver::nav::index_json(&session, false, None, "", &[])
    };
    let first = build();
    for _ in 0..10 {
        assert_eq!(build(), first);
    }
    assert!(first.contains("\"name\":\"Std.Ord.equal\""), "{first}");
    assert!(!first.contains("\"name\":\"Std.Ord.%"), "{first}");
}

/// A constructor's field named in a pattern, `C { f = … }`, refers to the
/// field's binder in the constructor's declaration, and shows the field's
/// type (docs/proposals/variant-fields.md §4.3).
#[test]
fn constructor_fields_in_patterns() {
    let source = "type Shape =\n  | Dot (id: Text)\n  | Circle (id: Text) (count: Nat)\n\n\
                  def label: Shape -> Text\n  | Circle { count = 0, .. } => \"none\"\n  \
                  | Circle { id, .. } => id\n  | Dot { id } => id\n";
    let mut session = Session::navigable();
    session.load("one.sw", source).expect("checks");
    let index = index_of(&session);
    let all = lines(&session, &index, "one.sw");
    for expected in [
        "one.sw:6:14 count -> Main.Shape.Circle.count [field] one.sw:3:24 : Nat",
        "one.sw:7:14 id -> Main.Shape.Circle.id [field] one.sw:3:13 : Text",
        "one.sw:8:11 id -> Main.Shape.Dot.id [field] one.sw:2:10 : Text",
        "one.sw:6:5 Circle -> Main.Shape.Circle [ctor] one.sw:3:5",
    ] {
        assert!(all.contains(expected), "missing `{expected}` in\n{all}");
    }
}

/// A shared field's accessor (docs/proposals/variant-fields.md §9.3), by dot
/// notation, as a section and written in full, refers to the field's binder
/// in the first constructor, and shows the accessor's type.
#[test]
fn shared_fields() {
    let source = "type Shape =\n  | Dot (id: Text)\n  | Circle (count: Nat) (id: Text)\n\n\
                  def name (s: Shape): Text := s.id\n\n\
                  def names (xs: List Shape): List Text := xs.map .id\n\n\
                  def full (s: Shape): Text := Shape.id s\n";
    let mut session = Session::navigable();
    session.load("one.sw", source).expect("checks");
    let index = index_of(&session);
    let all = lines(&session, &index, "one.sw");
    for expected in [
        "one.sw:5:32 id -> Main.Shape.id [field] one.sw:2:10 : Shape → Text",
        "one.sw:7:50 id -> Main.Shape.id [field] one.sw:2:10 : Shape → Text",
        "one.sw:9:30 Shape.id -> Main.Shape.id [field] one.sw:2:10 : Shape → Text",
    ] {
        assert!(all.contains(expected), "missing `{expected}` in\n{all}");
    }
}

#[test]
fn update_lemmas() {
    let source = "type Shape =\n  | Dot (id: Text)\n  | Circle (count: Nat) (id: Text)\n\n\
                  theorem renamed (s: Shape): ({ s | id = \"a\" }).id = \"a\" :=\n  \
                    rewrite Shape.id.update.id in rfl\n";
    let mut session = Session::navigable();
    session.load("one.sw", source).expect("checks");
    let index = index_of(&session);
    let all = lines(&session, &index, "one.sw");
    let found = all
        .lines()
        .find(|l| l.contains("-> Main.Shape.id.update.id [theorem]"))
        .unwrap_or_else(|| panic!("no hover on the lemma in\n{all}"));
    assert!(
        found.contains(": (x: Shape) → (id: Text) → ")
            && found.ends_with("{ x | id = id }.id = id"),
        "{found}"
    );
}
