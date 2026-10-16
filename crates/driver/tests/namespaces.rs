//! Namespaces and imports (docs/proposals/namespaces.md, stage 1): what the
//! examples can't show on their own (`examples/accept/namespaces.sw` and the
//! `reject/` examples show the rest).

use stitchwort_core::hash::data_hash;
use stitchwort_core::registry::Builtin;
use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_syntax::Severity;

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

fn codes(source: &str) -> Vec<&'static str> {
    let mut session = Session::new();
    match session.load("test.sw", source) {
        Ok(_) => session.warnings.iter().map(|d| d.code).collect(),
        Err(errors) => errors
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .map(|d| d.code)
            .collect(),
    }
}

fn passes(session: &Session) {
    let results = session.run_tests(&Cache::disabled());
    assert!(!results.is_empty());
    for result in &results {
        assert_eq!(result.outcome, Outcome::Passed, "{}", result.name);
    }
}

/// A type's hash includes its full logical name (§7.4): a program's own
/// `List`, declared exactly like the library's, is a different type with a
/// different hash, and so are two same-shaped types in different
/// namespaces.
#[test]
fn types_are_hashed_with_their_full_names() {
    let session = load(
        "type List (a : Type) : Type =\n  | Nil\n  | Cons (head : a) (tail : List a)\n\n\
         type Geometry.Shape : Type =\n  | Square (side : Nat)\n\n\
         type UI.Shape : Type =\n  | Square (side : Nat)\n",
    );
    let g = &session.elab.globals;
    let _op = g.budget.operation(stitchwort_core::Limits::default());
    let library = g.registry.data(Builtin::List).unwrap();
    let find = |path: &str| {
        (0..g.datas.len())
            .map(stitchwort_core::DataId)
            .find(|d| &*g.data(*d).path == path)
            .unwrap_or_else(|| panic!("no `{path}`"))
    };
    assert_eq!(&*g.data(library).path, "Std.List");
    let own = find("Main.List");
    assert_ne!(own, library);
    let hash = |d| data_hash(g, d).unwrap().unwrap();
    assert_ne!(hash(own), hash(library));
    assert_ne!(
        hash(find("Main.Geometry.Shape")),
        hash(find("Main.UI.Shape"))
    );
}

/// Two candidates at one level are only an error where the name is used.
#[test]
fn ambiguity_is_reported_only_where_used() {
    passes(&load(
        "import List (length)\nimport Text (length)\n\n\
         test \"full names\" = List.length [1] == Text.length \"a\"\n",
    ));
    assert_eq!(
        codes("import List (length)\nimport Text (length)\n\nn : Nat\nn = length [1]\n"),
        ["E-AMBIGUOUS"]
    );
}

/// The same thing reached twice isn't ambiguous: an import of a default
/// name, or `not` both as the alias and imported from `Bool`.
#[test]
fn the_same_thing_twice_is_not_ambiguous() {
    passes(&load(
        "import Bool (not)\nimport Std (List)\n\ntest \"not\" = not False\n\
         test \"list\" = List.length (Cons 1 Nil) == 1\n",
    ));
}

/// Importing the same name twice is a warning.
#[test]
fn importing_twice_is_a_warning() {
    assert_eq!(
        codes("import List (length, length)\n\nn : Nat\nn = length [1]\n"),
        ["W-IMPORT-TWICE"]
    );
}

/// A type brings its constructors with it, through an import as through
/// the default set.
#[test]
fn constructors_come_with_an_imported_type() {
    passes(&load(
        "import Effect (Comp)\n\n\
         one : Comp Builtin.UnitType (\\o -> Builtin.UnitType) Nat\none = Done 1\n\n\
         test \"done\" = List.length [one, Call () (\\u -> one)] == 2\n",
    ));
}

/// The extension check is on what the qualifier means, not its spelling:
/// an imported library type can't be added to either, nor can a library
/// namespace that isn't a type.
#[test]
fn library_namespaces_are_closed_however_they_are_reached() {
    for source in [
        "import Effect (Comp)\n\nComp.size : Nat\nComp.size = 0\n",
        "Text.size : Nat\nText.size = 0\n",
        "Effect.size : Nat\nEffect.size = 0\n",
        "Std.size : Nat\nStd.size = 0\n",
    ] {
        assert_eq!(codes(source), ["E-STD-NAMESPACE"], "{source}");
    }
}

/// Qualified names work in every position: expressions, types, patterns,
/// rows and handler clauses.
#[test]
fn qualified_names_work_everywhere() {
    passes(&load(
        "ability Console.Log where\n  log : Text -> {Console.Log} ()\n\n\
         collect : (() -> {Console.Log} Nat) -> Std.List Text\n\
         collect f =\n  handle f () with\n    | return x -> []\n    \
         | Console.Log.log t => k -> Cons t (k ())\n\n\
         twice : () -> {Console.Log} Nat\ntwice u =\n  Console.Log.log \"a\"\n  Console.Log.log \"b\"\n  2\n\n\
         isEmpty : Std.List Nat -> Bool\nisEmpty Std.List.Nil = True\nisEmpty (Std.List.Cons x xs) = False\n\n\
         test \"rows and clauses\" = List.length (collect twice) == 2\n\
         test \"patterns\" = isEmpty Std.List.Nil\n",
    ));
}

/// An operation is visible by its short name only where its ability is:
/// `Console.Log`'s `log` isn't, since `Console.Log` isn't at the root.
#[test]
fn operations_follow_their_ability() {
    let ability = "ability Console.Log where\n  log : Text -> {Console.Log} ()\n\n";
    assert_eq!(
        codes(&format!(
            "{ability}f : () -> {{Console.Log}} ()\nf u = log \"a\"\n"
        )),
        ["E-UNKNOWN-NAME"]
    );
    load(&format!(
        "import Console.Log (log)\n\n{ability}f : () -> {{Console.Log}} ()\nf u = log \"a\"\n"
    ));
}

/// A lowercase name in a type that's imported means the import, with a
/// warning, as for the module's own names (§4.11).
#[test]
fn an_imported_name_in_a_type_is_not_a_type_variable() {
    assert!(
        codes("import List (length)\n\nf : length -> Nat\nf x = 0\n")
            .iter()
            .any(|c| *c == "W-MODULE-NAME" || c.starts_with("E-"))
    );
}
