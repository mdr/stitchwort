//! The references a rename can trust (docs/proposals/refactoring.md §1.2):
//! each case that would make a rename built on the references wrong has
//! its references checked with their exact ranges.

use stitchwort_driver::driver::Session;
use stitchwort_driver::nav::{Index, Ref, RefTarget, index_data};

const LIB: &str = "namespace Lib

def map (x: Nat): Nat := x + 1

def size (x: Nat): Nat := x
";

fn load(files: &[(&str, &str)]) -> (Session, Index) {
    let mut session = Session::navigable();
    let files = files
        .iter()
        .map(|(name, text)| (format!("proj/src/{name}"), text.to_string()))
        .collect();
    let target = stitchwort_driver::project::Target::Everything;
    session
        .load_project_sources("proj", files, &target)
        .expect("checks");
    let index = index_data(&session, "proj", &[]);
    (session, index)
}

/// The text of `range` in `text`.
fn written(text: &str, range: [u32; 4]) -> String {
    let line = text.lines().nth(range[0] as usize).expect("a line");
    let chars: Vec<char> = line.chars().collect();
    chars[range[1] as usize..range[3] as usize].iter().collect()
}

/// One line per reference in `file`: `line:column text -> target`, with
/// `[name text]` where the part a rename edits is less than all of it,
/// and `pun` or `alias` where those hold. Lines are from 1.
fn describe(index: &Index, file: &str, text: &str) -> Vec<String> {
    let mut out = Vec::new();
    for r in &index.refs {
        if !index.files[r.file].path.ends_with(file) {
            continue;
        }
        out.push(line_of(index, r, text));
    }
    out
}

fn line_of(index: &Index, r: &Ref, text: &str) -> String {
    let target = match &r.target {
        RefTarget::Symbol(s) => {
            let s = &index.symbols[*s];
            format!(
                "{} [{}] {}:{}",
                s.name,
                s.kind,
                s.range[0] + 1,
                s.range[1] + 1
            )
        }
        RefTarget::Binder { name, range, .. } => {
            format!("local {name} {}:{}", range[0] + 1, range[1] + 1)
        }
    };
    let mut line = format!(
        "{}:{} {} -> {target}",
        r.range[0] + 1,
        r.range[1] + 1,
        written(text, r.range)
    );
    if r.name_range != r.range {
        line.push_str(&format!(" [name {}]", written(text, r.name_range)));
    }
    if r.pun {
        line.push_str(" pun");
    }
    if r.alias {
        line.push_str(" alias");
    }
    line
}

#[track_caller]
fn expect(all: &[String], wanted: &[&str]) {
    for w in wanted {
        assert!(
            all.iter().any(|l| l == w),
            "missing `{w}` in\n{}",
            all.join("\n")
        );
    }
}

/// The records, parameters and indexed family the cases below are written in.
const SOURCE: &str = "namespace Refs

type Item = { name: Text, price: Nat }

def label (name: Text) (price: Nat): Item := { name, price }

def nameOf: Item -> Text
  | { name, .. } => name

def base: Nat := 0

def span (start: Nat) (stop: Nat := start + base): Nat := stop

def tally (n: Nat) (step: Nat): Nat
    decreasing n + base
:=
  if n < 10 then step else tally (n / 10) step

def gap: Nat := span 1 (stop := 5)

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

def length: Vec a n -> Nat
  | VNil => 0
  | VCons [n := k] _ _ => Succ k

def cons (x: a) (xs: Vec a n): Vec a (Succ n) := VCons [n := n] x xs
";

fn refs_file() -> Vec<String> {
    let (_, index) = load(&[("Refs/Refs.sw", SOURCE)]);
    describe(&index, "Refs.sw", SOURCE)
}

/// A punned field `{ name }` is two references at one range, the field and
/// the variable, each saying so, in a literal and in a pattern. (The
/// declaration of a constructor's field is not a pun.)
#[test]
fn punned_fields() {
    let all = refs_file();
    expect(
        &all,
        &[
            "5:48 name -> Refs.Item.name [field] 3:15 pun",
            "5:48 name -> local name 5:12 pun",
            "5:54 price -> Refs.Item.price [field] 3:27 pun",
            "5:54 price -> local price 5:25 pun",
            "8:7 name -> Refs.Item.name [field] 3:15 pun",
            "8:7 name -> local name 8:7 pun",
            // the body's use of the pattern's variable is not
            "8:21 name -> local name 8:7",
            // a field written out is neither
            "23:12 n -> Refs.Vec.VCons.n [field] 23:12",
        ],
    );
}

/// A use of an import's alias is marked, and a qualified name's part that a
/// rename edits is the last component.
#[test]
fn aliases_and_qualified_names() {
    const USE: &str = "namespace Use

import Lib (map as each, size)

def a: Nat := each 1

def b: Nat := Lib.map 2

def c: Nat := Lib.size 3 + size 4
";
    let (_, index) = load(&[("Use/Use.sw", USE), ("Lib/Lib.sw", LIB)]);
    let all = describe(&index, "Use.sw", USE);
    expect(
        &all,
        &[
            "3:13 map -> Lib.map [def] 3:5",
            "3:20 each -> Lib.map [def] 3:5 alias",
            "5:15 each -> Lib.map [def] 3:5 alias",
            "7:15 Lib.map -> Lib.map [def] 3:5 [name map]",
            "9:15 Lib.size -> Lib.size [def] 5:5 [name size]",
            "9:28 size -> Lib.size [def] 5:5",
        ],
    );
}

/// The names in a parameter's default and in a `decreasing` measure are
/// references, to the parameters before it, and to globals.
#[test]
fn defaults_and_measures() {
    let all = refs_file();
    expect(
        &all,
        &[
            "12:37 start -> local start 12:11",
            "12:45 base -> Refs.base [def] 10:5",
            "15:16 n -> local n 14:12",
            "15:20 base -> Refs.base [def] 10:5",
        ],
    );
}

/// The name in a named argument is a use of the callee's parameter, and in
/// a call or a pattern of a constructor, of its field.
#[test]
fn named_arguments() {
    let all = refs_file();
    expect(
        &all,
        &[
            "19:25 stop -> local stop 12:24",
            "27:12 n -> Refs.Vec.VCons.n [field] 23:12",
            "29:57 n -> Refs.Vec.VCons.n [field] 23:12",
        ],
    );
    // Not also a variable of its own.
    assert!(
        !all.iter()
            .any(|l| l.starts_with("19:25 stop -> local stop 19"))
    );
    assert_eq!(all.iter().filter(|l| l.starts_with("19:25 ")).count(), 1);
    assert_eq!(all.iter().filter(|l| l.starts_with("27:12 ")).count(), 1);
}

/// The name in a doc link is a reference to the declaration it names (to
/// the last component of a qualified one).
#[test]
fn doc_links() {
    const USE: &str = "namespace Use

import Lib (size)

--| The same as [`Lib.size`], or [`size`] with the import.
def a: Nat := size 1

--| Calls [`a`].
def b: Nat := a
";
    let (_, index) = load(&[("Use/Use.sw", USE), ("Lib/Lib.sw", LIB)]);
    let all = describe(&index, "Use.sw", USE);
    expect(
        &all,
        &[
            "5:19 Lib.size -> Lib.size [def] 5:5 [name size]",
            "5:36 size -> Lib.size [def] 5:5",
            "8:13 a -> Use.a [def] 6:5",
        ],
    );
}

/// What the language server's answers carry for a rename to read.
#[test]
fn live_references_carry_the_flags() {
    use stitchwort_driver::live::{Place, answers_from};
    let (_, index) = load(&[("Refs/Refs.sw", SOURCE)]);
    let wanted = std::iter::once("proj/src/Refs/Refs.sw".to_string())
        .chain(index.files.iter().map(|f| f.path.clone()))
        .collect();
    let answers = answers_from(&index, &wanted, "");
    let file = answers
        .iter()
        .find(|(place, _)| matches!(place, Place::Program(p) if p.ends_with("Refs.sw")))
        .map(|(_, a)| a)
        .expect("the file");
    let puns: Vec<_> = file.refs.iter().filter(|r| r.pun).collect();
    // `{ name, price }` in the literal, `{ name, .. }` in the pattern: a
    // field and a variable each.
    assert_eq!(puns.len(), 6, "{puns:#?}");
    assert!(puns.iter().all(|r| !r.alias && r.name_range == r.range));
}
