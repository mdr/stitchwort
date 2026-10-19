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
        "import List (length)\n\
         import Text (length)\n\n\
         test \"full names\" := List.length [1] == Text.length \"a\"\n",
    ));
    assert_eq!(
        codes("import List (length)\nimport Text (length)\n\ndef n : Nat := length [1]\n"),
        ["E-AMBIGUOUS"]
    );
}

/// The same thing reached twice isn't ambiguous: an import of a default
/// name, or `not` both as the alias and imported from `Bool`.
#[test]
fn the_same_thing_twice_is_not_ambiguous() {
    passes(&load(
        "import Bool (not)\n\
         import Std (List)\n\n\
         test \"not\" := not False\n\
         test \"list\" := List.length (Cons 1 Nil) == 1\n",
    ));
}

/// Importing the same name twice is a warning.
#[test]
fn importing_twice_is_a_warning() {
    assert_eq!(
        codes("import List (length, length)\n\ndef n : Nat := length [1]\n"),
        ["W-IMPORT-TWICE"]
    );
}

/// A type brings its constructors with it, through an import as through
/// the default set.
#[test]
fn constructors_come_with_an_imported_type() {
    passes(&load(
        "import Effect (Comp)\n\n\
         def one : Comp Builtin.UnitType (\\o => Builtin.UnitType) Nat := Done 1\n\n\
         test \"done\" := List.length [one, Call () (\\u => one)] == 2\n",
    ));
}

/// The extension check is on what the qualifier means, not its spelling:
/// an imported library type can't be added to either, nor can a library
/// namespace that isn't a type.
#[test]
fn library_namespaces_are_closed_however_they_are_reached() {
    for source in [
        "import Effect (Comp)\n\ndef Comp.size : Nat := 0\n",
        "def Text.size : Nat := 0\n",
        "def Effect.size : Nat := 0\n",
        "def Std.size : Nat := 0\n",
    ] {
        assert_eq!(codes(source), ["E-STD-NAMESPACE"], "{source}");
    }
}

/// Qualified names work in every position: expressions, types, patterns,
/// rows and handler clauses.
#[test]
fn qualified_names_work_everywhere() {
    passes(&load(
        "ability Console.Log where\n  \
         log : Text -> {Console.Log} ()\n\n\
         def collect (f : () -> {Console.Log} Nat) : Std.List Text :=\n  \
         handle f () with\n    \
         | return x => []\n    \
         | Console.Log.log t, k => Cons t (k ())\n\n\
         def twice () : {Console.Log} Nat :=\n  \
         Console.Log.log \"a\"\n  \
         Console.Log.log \"b\"\n  \
         2\n\n\
         def isEmpty : Std.List Nat -> Bool\n  \
         | Std.List.Nil => True\n  \
         | Std.List.Cons x xs => False\n\n\
         test \"rows and clauses\" := List.length (collect twice) == 2\n\
         test \"patterns\" := isEmpty Std.List.Nil\n",
    ));
}

/// An operation is visible by its short name only where its ability is:
/// `Console.Log`'s `log` isn't, since `Console.Log` isn't at the root.
#[test]
fn operations_follow_their_ability() {
    let ability = "ability Console.Log where\n  log : Text -> {Console.Log} ()\n\n";
    assert_eq!(
        codes(&format!(
            "{ability}def f () : {{Console.Log}} () := log \"a\"\n"
        )),
        ["E-UNKNOWN-NAME"]
    );
    load(&format!(
        "import Console.Log (log)\n\n{ability}def f () : {{Console.Log}} () := log \"a\"\n"
    ));
}

/// A lowercase name in a type that's imported means the import, with a
/// warning, as for the module's own names (§4.11).
#[test]
fn an_imported_name_in_a_type_is_not_a_type_variable() {
    assert!(
        codes("import List (length)\n\ndef f (x : length) : Nat := 0\n")
            .iter()
            .any(|c| *c == "W-MODULE-NAME" || c.starts_with("E-"))
    );
}

fn path_hash(session: &Session, path: &str) -> stitchwort_core::hash::ContentHash {
    let g = &session.elab.globals;
    let id = g
        .defs
        .iter()
        .position(|d| &*d.path == path)
        .unwrap_or_else(|| panic!("no definition `{path}`"));
    stitchwort_core::hash::def_hash(g, stitchwort_core::DefId(id))
        .unwrap()
        .expect("checked")
}

fn data_path_hash(session: &Session, path: &str) -> stitchwort_core::hash::ContentHash {
    let g = &session.elab.globals;
    let id = (0..g.datas.len())
        .map(stitchwort_core::DataId)
        .find(|d| &*g.data(*d).path == path)
        .unwrap_or_else(|| panic!("no type `{path}`"));
    data_hash(g, id).unwrap().unwrap()
}

/// A namespace line puts a file's types in the namespace, and their hashes
/// with it (docs/proposals/multi-file.md §4.3, §8.1).
#[test]
fn a_namespace_line_puts_types_in_it() {
    let ty = "type T: Type =\n  | MkT (n: Nat)\n";
    let none = load(ty);
    let demo = load(&format!("namespace Demo\n\n{ty}"));
    let other = load(&format!("namespace Other\n\n{ty}"));
    let none_hash = data_path_hash(&none, "Main.T");
    let demo_hash = data_path_hash(&demo, "Demo.T");
    let other_hash = data_path_hash(&other, "Other.T");
    assert_ne!(none_hash, demo_hash);
    assert_ne!(demo_hash, other_hash);
}

/// A definition that mentions no type of the file doesn't know whether the
/// file has a namespace line.
#[test]
fn definitions_hash_the_same_with_or_without_a_namespace_line() {
    let def = "def double (n: Nat): Nat := n + n\n";
    let none = load(def);
    let demo = load(&format!("namespace Demo\n\n{def}"));
    assert_eq!(
        path_hash(&none, "Main.double"),
        path_hash(&demo, "Demo.double")
    );
}

/// `main` is the namespace's own.
#[test]
fn a_namespaced_file_runs_its_main() {
    let mut session = load("namespace Demo\n\ndef main(): {IO} () := print \"hello\"\n");
    assert_eq!(session.simulate(&[]).unwrap(), ["hello"]);
}

/// Tests' internal names carry the namespace, so two files' tests, and the
/// helpers lifted out of them, don't collide.
#[test]
fn two_namespaced_files_in_one_session_have_separate_tests() {
    let file = |ns: &str, name: &str| {
        format!(
            "namespace {ns}\n\n\
             test \"{name}\" := match 1 with\n  | 0 => False\n  | Succ k => True\n"
        )
    };
    let mut session = Session::new();
    session.load("a.sw", &file("A", "first")).unwrap();
    session.load("b.sw", &file("B", "second")).unwrap();
    passes(&session);
}
