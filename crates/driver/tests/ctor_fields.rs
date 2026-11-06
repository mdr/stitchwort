//! `W-RECORD-ARGUMENT` (docs/proposals/variant-fields.md §12.3): braces after
//! a one-field constructor whose field holds a record name the constructor's
//! own field, which is easily meant as the record's when the names coincide.
//! Named construction, `C { f = e, … }` in an expression (§4.5): the same
//! hash as the positional form, and its errors.

use stitchwort_driver::driver::Session;
use stitchwort_syntax::{Diagnostic, Severity};

fn warnings(text: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    session.load("test.sw", text).expect("checks");
    session
        .warnings
        .iter()
        .filter(|w| w.code == "W-RECORD-ARGUMENT")
        .cloned()
        .collect()
}

const ITEM: &str = "import Std (Option)\n\ntype Item = { value: Nat, fits: Bool }\n\ntype Box = | Held { item: Item }\n\n";

#[test]
fn naming_a_field_the_record_has_too_warns() {
    let found = warnings(&format!(
        "{ITEM}def get: Box -> Item\n  | Held {{ item = i, .. }} => i\n"
    ));
    assert!(found.is_empty(), "{found:#?}");
    let found = warnings(&format!(
        "type Item = {{ item: Nat, fits: Bool }}\n\ntype Box = | Held {{ item: Item }}\n\n\
         def get: Box -> Nat\n  | Held {{ item = n, .. }} => n.item\n"
    ));
    let [w] = &found[..] else {
        panic!("{found:#?}");
    };
    assert_eq!(w.severity, Severity::Warning);
    assert!(w.message.contains("`Held`'s own field `item`"), "{w:?}");
    assert!(w.notes[0].contains("Held ({ … })"), "{w:?}");
}

#[test]
fn the_bracketed_record_argument_and_positional_patterns_dont_warn() {
    let found = warnings(&format!(
        "{ITEM}def get: Box -> Nat\n  | Held ({{ value = n, .. }}) => n\n\n\
         def get2: Box -> Nat\n  | Held i => i.value\n\n\
         def get3: Option Item -> Nat\n  | Some {{ value = n, .. }} => n\n  | None => 0\n"
    ));
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn a_field_the_record_lacks_doesnt_warn() {
    let found = warnings(
        "type Person = { name: Text, age: Nat }\n\ntype Wrap = | W { person: Person }\n\n\
         def nameOf: Wrap -> Text\n  | W { person = { name, .. }, .. } => name\n",
    );
    assert!(found.is_empty(), "{found:#?}");
}

// Named construction, `C { f = e, … }` in an expression
// (docs/proposals/variant-fields.md §4.5): the positional application, so
// switching between the two forms never moves a hash.

const TYPES: &str = "import Std (Option)\n\n\
type Shape =\n  | Dot { ref: Nat, id: Text }\n  | Circle { ref: Nat, id: Text, text: Text }\n\n\
type Vec (a: Type): Nat -> Type =\n  | VNil: Vec a 0\n  | VCons { x: a, xs: Vec a n }: Vec a (Succ n)\n\n\
type Pos = | MkPos { n: Nat, ok: n > 0 }\n\n\
type Item = { name: Text, price: Nat }\n\n";

/// The definitions the hash test compares.
const NAMES: &[&str] = &["a", "b", "v", "p", "o", "r"];

/// The hash of each of [`NAMES`], defined by `text` after [`TYPES`].
fn hashes(text: &str) -> Vec<(String, String)> {
    use stitchwort_core::DefId;
    use stitchwort_core::hash::def_hash;
    let mut session = Session::new();
    let first = session.elab.kernel.env.defs().len();
    session
        .load("test.sw", &format!("{TYPES}{text}"))
        .unwrap_or_else(|e| panic!("{e:#?}"));
    let g = &session.elab.ev();
    (first..g.env.defs().len())
        .filter(|&i| {
            let path = g.env.defs()[i].path().to_string();
            NAMES.iter().any(|n| path == format!("Main.{n}"))
        })
        .map(|i| {
            let h = def_hash(g, DefId(i)).unwrap().expect("a hash").hex();
            (g.env.defs()[i].path().to_string(), h)
        })
        .collect()
}

#[test]
fn named_construction_hashes_as_the_positional_form() {
    let positional = hashes(
        "def a: Shape := Circle 1 \"a\" \"t\"\n\n\
         def b (id: Text): Shape := Dot 2 id\n\n\
         def v: Vec Nat 2 := VCons 1 (VCons 2 VNil)\n\n\
         def p: Pos := MkPos 3 omega\n\n\
         def o: Option Shape := Some (Circle 1 \"a\" \"t\")\n\n\
         def r: Option Item := Some ({ name = \"tea\", price = 3 })\n",
    );
    let named = hashes(
        "def a: Shape := Circle { text = \"t\", ref = 1, id = \"a\" }\n\n\
         def b (id: Text): Shape := Dot { id, ref = 2 }\n\n\
         def v: Vec Nat 2 := VCons { xs = VCons { x = 2, xs = VNil }, x = 1 }\n\n\
         def p: Pos := MkPos { ok = omega, n = 3 }\n\n\
         def o: Option Shape := Some (value := Circle { ref = 1, id = \"a\", text = \"t\" })\n\n\
         def r: Option Item := Some { name = \"tea\", price = 3 }\n",
    );
    assert_eq!(positional.len(), 6, "{positional:?}");
    assert_eq!(positional, named);
}

fn errors(text: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    match session.load("test.sw", &format!("{TYPES}{text}")) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

#[test]
fn named_construction_is_refused_like_a_record_literal() {
    let cases = [
        (
            "def c: Shape := Circle { ref = 1, id = \"a\", colour = \"t\" }\n",
            "E-UNKNOWN-FIELD",
            "`Circle` has no field `colour`",
        ),
        (
            "def c: Shape := Circle { ref = 1, id = \"a\" }\n",
            "E-RECORD-FIELD",
            "this `Circle` is missing `text`",
        ),
        (
            "def c: Shape := Dot { ref = 1, id = \"a\", ref = 2 }\n",
            "E-RECORD-FIELD",
            "field `ref` is given twice",
        ),
        (
            "def c: Vec Nat 1 := VCons { n = 0, x = 1, xs = VNil }\n",
            "E-UNKNOWN-FIELD",
            "`n` is an implicit field of `VCons`",
        ),
        (
            "def c: Item := Item { name = \"tea\", price = 3 }\n",
            "E-NOT-A-CONSTRUCTOR",
            "`Item` isn't a constructor",
        ),
        (
            "def c: Shape := Circle { ref = 1, id = \"a\" } \"t\"\n",
            "E-PARSE",
            "take no further arguments",
        ),
        (
            "def c: List Shape := List.map (s => s) Dot { ref = 1, id = \"a\" }\n",
            "E-PARSE",
            "as an argument need brackets",
        ),
    ];
    for (text, code, message) in cases {
        let found = errors(text);
        assert!(
            found
                .iter()
                .any(|e| e.code == code && e.message.contains(message)),
            "{text}: {found:#?}"
        );
    }
}

// Braces after a constructor declared with brackets are a record argument,
// as after a function (docs/proposals/brace-syntax-review.md §5): the same
// term as the bracketed form.
#[test]
fn braces_after_a_bracket_declared_constructor_hash_as_the_bracketed_form() {
    let bracketed = hashes(
        "def a: Option Item := Some ({ name = \"tea\", price = 3 })\n\n\
         def b (i: Item): Option Item := Some ({ i | price = 4 })\n\n\
         def o: Result Item Text := Ok ({ name = \"tea\", price = 3 })\n",
    );
    let braces = hashes(
        "def a: Option Item := Some { name = \"tea\", price = 3 }\n\n\
         def b (i: Item): Option Item := Some { i | price = 4 }\n\n\
         def o: Result Item Text := Ok { name = \"tea\", price = 3 }\n",
    );
    assert_eq!(bracketed.len(), 3, "{bracketed:?}");
    assert_eq!(bracketed, braces);
}

#[test]
fn a_bracket_declared_constructors_braces_take_a_record_pattern_and_more_arguments() {
    let found = errors(
        "type Tagged = | Tag (item: Item) (tag: Text)\n\n\
         def hot: Tagged := Tag { name = \"tea\", price = 3 } \"hot\"\n\n\
         def name: Option Item -> Text\n  | Some { name, .. } => name\n  | None => \"\"\n\n\
         def pick (t: Tagged) (i: Item): Text := i.name\n\n\
         def p: Text := pick hot { name = \"x\", price = 1 }\n",
    );
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn named_arguments_on_a_constructor_fill_the_defaults() {
    let found = errors(
        "type Marked = | Mark (id: Text) (size: Nat := 3)\n\n\
         def a: Marked := Mark (id := \"a\")\n\n\
         theorem same: Mark (id := \"a\") = Mark \"a\" 3 := rfl\n",
    );
    assert!(found.is_empty(), "{found:#?}");
}
