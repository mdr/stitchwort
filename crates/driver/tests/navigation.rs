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
    let mut session = Session::new();
    session.elab.enable_navigation();
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
    let mut session = Session::new();
    session.elab.enable_navigation();
    let source = "def ok (xs: List Nat): Nat := xs.length\n\ndef bad (xs: List Nat): Nat := xs.map (n => n)\n";
    assert!(session.load("one.sw", source).is_err());
    let json = index_json(&session, true, Some(false), "");
    assert!(json.starts_with(r#"{"version":1,"errors":true,"ok":false,"files":["#));
    assert!(json.contains(r#""name":"Std.List.length""#), "{json}");
    assert!(json.contains(r#""name":"ok","kind":"def""#), "{json}");
}

/// Columns count UTF-16 code units, and lines and columns start at 0.
#[test]
fn columns_are_utf16() {
    let mut session = Session::new();
    session.elab.enable_navigation();
    let source = "def f (t: Text): Text := \"😀\" ++ t\n";
    session.load("one.sw", source).expect("checks");
    let json = index_json(&session, false, None, "");
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
    let mut session = Session::new();
    session.elab.enable_navigation();
    session
        .load("one.sw", "def f (xs: List Nat): Nat := xs.length\n")
        .expect("checks");
    let json = index_json(&session, false, None, "");
    assert!(json.contains(r#"{"path":"crates/elab/src/std/core.sw","std":"core.sw"}"#));
    let text =
        stitchwort_driver::nav::std_source("core.sw", session.elab.limits.stack).expect("embedded");
    assert!(text.contains("List"));
    assert!(stitchwort_driver::nav::std_source("nope.sw", session.elab.limits.stack).is_none());
}
