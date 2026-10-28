//! The standard library split into a core and library files that load on
//! demand (docs/proposals/std-library.md, stage 1): the name index, the
//! loader, and the invariant that lazy loading changes nothing a program can
//! see (§4.0).

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::registry::{Builtin, Home, Kind};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{
    Cache, Outcome, Session, full_tier, par_map, par_map_with, tier_sample,
};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::render::render;
use stitchwort_elab::{EMBEDDED_LIBRARY_FILES, LibraryIndex, library_files, prelude};
use stitchwort_syntax::Diagnostic;

/// Examples run with this much stack, as from the command line.
const STACK: usize = 16 * 1024 * 1024;

fn codes(diagnostics: &[Diagnostic]) -> Vec<&'static str> {
    diagnostics.iter().map(|d| d.code).collect()
}

fn messages(diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|d| format!("{}: {}\n", d.code, d.message))
        .collect()
}

// ---------------------------------------------------------------- the table

/// Every `.sw` file under `crates/elab/src/std`, by path under it.
fn files_on_disk() -> Vec<String> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(&path, root, out);
            } else if path.extension().is_some_and(|e| e == "sw") {
                let rel = path.strip_prefix(root).unwrap();
                out.push(rel.to_string_lossy().replace('\\', "/"));
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std");
    let mut out = Vec::new();
    walk(&root, &root, &mut out);
    out.sort();
    out
}

/// The core's files (`std/core/`), `prelude()`, are not library files.
fn is_core(path: &str) -> bool {
    path.starts_with("core/")
}

/// Which copy of the library this run uses (`STITCHWORT_STD_DIR`), said
/// once in the test output.
fn say_mode() {
    static SAID: std::sync::Once = std::sync::Once::new();
    SAID.call_once(|| eprintln!("std_library: {}", stitchwort_elab::std_text().mode()));
}

/// Every `.sw` file under `std/core/` is in `EMBEDDED_CORE_LAYOUT`, and each
/// file's text, read back by path, is what the layout this run uses says:
/// they join to `prelude()`.
#[test]
fn the_core_layout_lists_every_core_file() {
    say_mode();
    let on_disk: Vec<String> = files_on_disk().into_iter().filter(|p| is_core(p)).collect();
    let mut listed: Vec<String> = stitchwort_elab::EMBEDDED_CORE_LAYOUT
        .iter()
        .map(|(p, _)| p.to_string())
        .collect();
    listed.sort();
    assert_eq!(listed, on_disk);
    let mut joined = String::new();
    for (path, len) in stitchwort_elab::core_layout() {
        let text = stitchwort_driver::nav::std_source(path, STACK).expect("a core file");
        assert_eq!(text.len(), *len, "{path}");
        joined.push_str(&text);
    }
    assert_eq!(joined, prelude());
}

/// The embedded table lists every library file in the checkout, in order,
/// with its text. The text is compared only when this run uses the embedded
/// copy: with `STITCHWORT_STD_DIR` set, the files on disk may be ahead of the
/// build, which is the point.
#[test]
fn the_table_lists_every_library_file_in_order() {
    say_mode();
    let listed: Vec<String> = EMBEDDED_LIBRARY_FILES
        .iter()
        .map(|(p, _)| p.to_string())
        .collect();
    assert_eq!(
        listed,
        files_on_disk()
            .into_iter()
            .filter(|p| !is_core(p))
            .collect::<Vec<_>>(),
        "EMBEDDED_LIBRARY_FILES in crates/elab/src/library.rs"
    );
    if stitchwort_elab::std_text().dir.is_some() {
        eprintln!("the embedded files' text isn't compared: std is read from disk");
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std");
    for (path, text) in EMBEDDED_LIBRARY_FILES {
        assert_eq!(&std::fs::read_to_string(root.join(path)).unwrap(), text);
    }
}

// ----------------------------------------------------------------- the index

fn standard_index() -> std::sync::Arc<LibraryIndex> {
    say_mode();
    LibraryIndex::standard(STACK).expect("the standard library's index")
}

#[test]
fn library_files_do_not_form_a_cycle() {
    let index = standard_index();
    let all: BTreeSet<usize> = (1..index.files.len()).collect();
    if let Err(cycle) = index.load_order(&all, &|f| f == 0) {
        panic!("{}", index.cycle_message(&cycle));
    }
}

#[test]
fn the_index_holds_exactly_the_names_an_eager_load_makes() {
    let session = Session::eager();
    let index = standard_index();
    assert!(
        session.elab.pending_keys().is_empty(),
        "names still pending after every file loaded: {:?}",
        session.elab.pending_keys()
    );
    // Every name the index promises exists, and every name the library
    // declares (not the compiler's `%` names, nor a definition's local
    // helpers `f.go`) is promised. A candidate shared-field accessor is
    // declared only if its field is shared (docs/proposals/variant-fields.md
    // §12.1): `Exists.value` isn't (data out of a proof).
    let keys: BTreeSet<String> = session.elab.scope_keys().into_iter().collect();
    let promised: BTreeSet<String> = index.names().map(|(k, _)| k.to_string()).collect();
    let candidates: BTreeSet<&str> = index.candidates().collect();
    assert!(candidates.contains("Std.Exists.value"), "{candidates:?}");
    let missing: Vec<&String> = promised
        .difference(&keys)
        .filter(|k| !candidates.contains(k.as_str()))
        .collect();
    assert!(missing.is_empty(), "promised but not declared: {missing:?}");
    let unpromised: Vec<&String> = keys.difference(&promised).collect();
    assert!(
        unpromised.is_empty(),
        "declared but not in the index: {unpromised:?}"
    );
}

#[test]
fn a_name_declared_twice_is_refused() {
    let build = |files: &[(&str, &str)]| LibraryIndex::build(prelude(), files, STACK).err();
    // Library against library.
    let error = build(&[
        ("A.sw", "def Nat.libTwice (n: Nat): Nat := n + n\n"),
        ("B.sw", "def Nat.libTwice (n: Nat): Nat := n + n + 0\n"),
    ])
    .expect("a duplicate is refused");
    assert!(error.contains("Std.Nat.libTwice"), "{error}");
    assert!(error.contains("A.sw") && error.contains("B.sw"), "{error}");
    // Library against the core.
    let error = build(&[("A.sw", "def Nat.add (a: Nat) (b: Nat): Nat := a\n")])
        .expect("a core name is refused");
    assert!(error.contains("Std.Nat.add"), "{error}");
    assert!(error.contains("core") && error.contains("A.sw"), "{error}");
    // A generated name (a constructor) against a definition.
    let error = build(&[
        ("A.sw", "type Lib = | Mk\n"),
        ("B.sw", "def Lib.Mk: Nat := 0\n"),
    ])
    .expect("a constructor's name is taken");
    assert!(error.contains("Std.Lib.Mk"), "{error}");
    // A generated name (a record's field) against a definition.
    let error = build(&[
        ("A.sw", "type Libr = { size: Nat }\n"),
        ("B.sw", "def Libr.size: Nat := 0\n"),
    ])
    .expect("a field's name is taken");
    assert!(error.contains("Std.Libr.size"), "{error}");
    // An ability's operation against a definition.
    let error = build(&[
        ("A.sw", "ability Libab where\n  go: Nat -> {Libab} Nat\n"),
        ("B.sw", "def Libab.go: Nat := 0\n"),
    ])
    .expect("an operation's name is taken");
    assert!(error.contains("Std.Libab.go"), "{error}");
    // Even in files no program loads, and the same file twice over.
    let error = build(&[(
        "A.sw",
        "def Nat.libOne: Nat := 1\ndef Nat.libOne: Nat := 2\n",
    )])
    .expect("a name twice in a file is refused");
    assert!(error.contains("Std.Nat.libOne"), "{error}");
    // Independent files are fine.
    assert!(
        build(&[
            ("A.sw", "def Nat.libTwice (n: Nat): Nat := n + n\n"),
            ("B.sw", "def Nat.libThrice (n: Nat): Nat := n + n + n\n"),
        ])
        .is_none()
    );
}

// ------------------------------------------------------------------ loading

const A: &str = "def Nat.libTwice (n: Nat): Nat := n + n\n\
                 test \"libTwice\" := Nat.libTwice 2 == 4\n";
const B: &str = "def Nat.libFour (n: Nat): Nat := Nat.libTwice (Nat.libTwice n)\n";
const C: &str = "def Nat.libEight (n: Nat): Nat := Nat.libTwice (Nat.libFour n)\n";
/// Needs nothing, and is reached by dot notation.
const D: &str = "def List.libDouble (xs: List Nat): Nat := List.length xs + List.length xs\n";
const FILES: &[(&str, &str)] = &[("A.sw", A), ("B.sw", B), ("C.sw", C), ("D.sw", D)];

fn lazy() -> Session {
    Session::with_library_files(FILES, false, false).unwrap()
}

fn loaded_by(program: &str) -> Vec<String> {
    let mut session = lazy();
    session
        .load("t.sw", program)
        .unwrap_or_else(|e| panic!("{}", messages(&e)));
    session.elab.loaded_library_files()
}

#[test]
fn an_empty_program_loads_no_library_file() {
    assert_eq!(loaded_by("def x : Nat := 1\n"), Vec::<String>::new());
    let mut session = Session::new();
    session.load("t.sw", "def x : Nat := 1\n").unwrap();
    assert!(session.elab.loaded_library_files().is_empty());
}

#[test]
fn a_file_loads_after_the_files_it_needs() {
    assert_eq!(
        loaded_by("import Std (Nat)\ndef x : Nat := Nat.libFour 1\n"),
        ["A.sw", "B.sw"]
    );
    assert_eq!(
        loaded_by("import Std (Nat)\ndef x : Nat := Nat.libTwice 1\n"),
        ["A.sw"]
    );
}

#[test]
fn the_order_never_depends_on_how_the_program_mentions_things() {
    let one = "import Std (Nat)\ndef x : Nat := Nat.libEight 1\ndef y : Nat := Nat.libTwice 1\n";
    let other = "import Std (Nat)\ndef y : Nat := Nat.libTwice 1\ndef x : Nat := Nat.libEight 1\n";
    assert_eq!(loaded_by(one), ["A.sw", "B.sw", "C.sw"]);
    assert_eq!(loaded_by(other), ["A.sw", "B.sw", "C.sw"]);
    // Independent files: by path.
    let both = "import Std (List, Nat)\ndef x : Nat := Nat.libTwice 1\ndef y (xs: List Nat) : Nat := List.libDouble xs\n";
    assert_eq!(loaded_by(both), ["A.sw", "D.sw"]);
}

#[test]
fn every_way_of_naming_a_library_declaration_loads_its_file() {
    // Qualified, with the namespace imported, and with `Std.`.
    assert_eq!(
        loaded_by("import Std (Nat)\ndef x : Nat := Nat.libTwice 1\n"),
        ["A.sw"]
    );
    assert_eq!(loaded_by("def x : Nat := Std.Nat.libTwice 1\n"), ["A.sw"]);
    // By an import, qualified or by name.
    assert_eq!(
        loaded_by("import Nat (libTwice)\ndef x : Nat := libTwice 1\n"),
        ["A.sw"]
    );
    assert_eq!(
        loaded_by("import Std.Nat (libTwice)\ndef x : Nat := libTwice 1\n"),
        ["A.sw"]
    );
    // By a `(..)` import.
    assert_eq!(
        loaded_by("import Nat (..)\ndef x : Nat := libTwice 1\n"),
        ["A.sw"]
    );
    // By dot notation, whose target depends on the receiver's type.
    assert_eq!(
        loaded_by("def x (xs: List Nat) : Nat := xs.libDouble\n"),
        ["D.sw"]
    );
    // By a method section.
    assert_eq!(
        loaded_by("def x : List Nat -> Nat := .libDouble\n"),
        ["D.sw"]
    );
}

#[test]
fn diagnostics_and_suggestions_never_load_anything() {
    let mut session = lazy();
    // An unknown short name: the library's declarations of it are suggested.
    let errors = session
        .load("t.sw", "def x : Nat := libTwice 1\n")
        .unwrap_err();
    assert_eq!(codes(&errors), ["E-UNKNOWN-NAME"]);
    let text = errors[0].notes.join(" ");
    assert!(text.contains("Nat.libTwice"), "{text}");
    // A misspelt import item: a near miss.
    let errors = session
        .load("u.sw", "import Nat (libTwic)\ndef y : Nat := 1\n")
        .unwrap_err();
    assert_eq!(codes(&errors), ["E-IMPORT-UNKNOWN"]);
    assert!(errors[0].notes.join(" ").contains("libTwice"));
    // A misspelt qualified name.
    let errors = session
        .load("v.sw", "def z : Nat := Nat.libTwic 1\n")
        .unwrap_err();
    assert!(!errors.is_empty());
    assert!(session.elab.loaded_library_files().is_empty());
}

#[test]
fn ambiguity_doesnt_depend_on_what_is_loaded() {
    // `libTwice` from two imports is ambiguous, whether or not either file
    // has loaded.
    let two = [
        ("A.sw", "def Nat.libTwice (n: Nat): Nat := n + n\n"),
        ("B.sw", "def List.libTwice (n: List Nat): Nat := 0\n"),
    ];
    let program = "import Nat (libTwice)\nimport List (libTwice)\ndef x : Nat := libTwice 1\n";
    let mut lazy = Session::with_library_files(&two, false, false).unwrap();
    let mut eager = Session::with_library_files(&two, true, false).unwrap();
    let a = lazy.load("t.sw", program).unwrap_err();
    let b = eager.load("t.sw", program).unwrap_err();
    assert_eq!(codes(&a), codes(&b));
    assert!(codes(&a).contains(&"E-AMBIGUOUS"), "{}", messages(&a));
    assert_eq!(messages(&a), messages(&b));
}

#[test]
fn library_tests_run_only_under_the_library_target() {
    // A program that loads a file with a test doesn't run it.
    let mut session = lazy();
    session
        .load(
            "t.sw",
            "import Std (Nat)\ndef x : Nat := Nat.libTwice 1\ntest \"mine\" := x == 2\n",
        )
        .unwrap();
    let results = session.run_tests(&Cache::disabled());
    let names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
    assert_eq!(names, ["mine"]);
    assert!(session.run_library_tests(&Cache::disabled()).is_empty());
    // The library target checks them, and runs only them.
    let session = Session::with_library_files(FILES, true, true).unwrap();
    let results = session.run_library_tests(&Cache::disabled());
    let names: Vec<&str> = results.iter().map(|r| r.name.as_str()).collect();
    assert_eq!(names, ["libTwice"]);
    assert!(results.iter().all(|r| r.outcome == Outcome::Passed));
    assert!(session.run_tests(&Cache::disabled()).is_empty());
}

#[test]
fn the_standard_library_passes_its_own_tests() {
    let session = Session::with_library_tests();
    let results = session.run_library_tests(&Cache::disabled());
    for r in &results {
        assert_eq!(r.outcome, Outcome::Passed, "library test `{}`", r.name);
    }
    // And nothing it declares is the program's.
    assert!(session.run_tests(&Cache::disabled()).is_empty());
}

// ----------------------------------------------------------------- the cycles

#[test]
fn a_cycle_between_files_is_an_internal_error_naming_both() {
    let files = [
        ("A.sw", "def Nat.cycA (n: Nat): Nat := Nat.cycB n\n"),
        ("B.sw", "def Nat.cycB (n: Nat): Nat := Nat.cycA n\n"),
    ];
    let mut session = Session::with_library_files(&files, false, false).unwrap();
    let errors = session
        .load("t.sw", "import Std (Nat)\ndef x : Nat := Nat.cycA 1\n")
        .unwrap_err();
    assert_eq!(codes(&errors), ["E-INTERNAL"]);
    let text = messages(&errors);
    assert!(
        text.contains("std/A.sw") && text.contains("std/B.sw"),
        "{text}"
    );
    assert!(text.contains("need each other"), "{text}");
    // Loading every file reports it too, rather than hanging.
    let Err(report) = Session::with_library_files(&files, true, false) else {
        panic!("a cycle should not load");
    };
    assert!(
        report.contains("std/A.sw") && report.contains("std/B.sw"),
        "{report}"
    );
}

#[test]
fn a_cycle_through_dot_notation_is_an_internal_error_naming_both() {
    // `A.sw` reaches `B.sw` only through `.dotB`, whose target depends on
    // the receiver's type; `B.sw` names `A.sw` outright.
    let files = [
        ("A.sw", "def List.dotA (xs: List Nat): Nat := xs.dotB\n"),
        (
            "B.sw",
            "def List.dotB (xs: List Nat): Nat := List.dotA xs\n",
        ),
    ];
    let mut session = Session::with_library_files(&files, false, false).unwrap();
    let errors = session
        .load("t.sw", "import Std (List)\ndef x : Nat := List.dotA Nil\n")
        .unwrap_err();
    assert!(codes(&errors).iter().all(|c| *c == "E-INTERNAL"));
    let text = messages(&errors);
    assert!(
        text.contains("std/A.sw") && text.contains("std/B.sw"),
        "{text}"
    );
}

#[test]
fn a_dot_call_does_not_load_a_same_named_function_that_needs_the_caller() {
    // SW-254: `xs.spanX` in `A.sw` is `List.spanX`, but the index can't tell
    // the receiver's type, so `Nat.spanX` in `B.sw` (which needs `A.sw`) is a
    // target too, and would make a cycle. `A.sw` can't use it, so no edge.
    let files = [
        (
            "A.sw",
            "def List.spanX (xs: List Nat) (n: Nat): List Nat := xs\n\
             def List.spanA (xs: List Nat): Nat := List.length (xs.spanX 1)\n",
        ),
        (
            "B.sw",
            "def Nat.spanX (a: Nat) (b: Nat): Nat := List.length (List.spanX Nil b)\n",
        ),
    ];
    let mut session = Session::with_library_files(&files, false, false).unwrap();
    session
        .load("t.sw", "import Std (List)\ndef x : Nat := List.spanA Nil\n")
        .unwrap();
}

#[test]
fn a_library_file_may_use_dot_notation_on_a_loaded_file() {
    // SW-189: `.dotB` notes every file with a function of that name, and
    // `B.sw` is loaded before `A.sw` is checked; that's no error.
    let files = [
        ("A.sw", "def List.dotA (xs: List Nat): Nat := xs.dotB\n"),
        (
            "B.sw",
            "def List.dotB (xs: List Nat): Nat := List.length xs\n",
        ),
    ];
    let mut session = Session::with_library_files(&files, false, false).unwrap();
    session
        .load("t.sw", "import Std (List)\ndef x : Nat := List.dotA Nil\n")
        .unwrap();
}

/// Library files for dot notation by namespace (SW-234): `Clock` is a type
/// declared in one file, with functions in it and in another.
const DOT_FILES: &[(&str, &str)] = &[
    (
        "Clock.sw",
        "type Clock = { hand: Nat }\n\
         def Clock.size (c: Clock): Nat := c.hand\n",
    ),
    // A function in `Clock`'s namespace, away from `Clock`'s file.
    (
        "ClockMore.sw",
        "def Clock.tick (c: Clock): Clock := { hand = c.hand + 1 }\n",
    ),
    // `.size` and `.tick` on `List`, whose type is in the core.
    (
        "ListMore.sw",
        "def List.size (xs: List Nat): Nat := List.length xs\n",
    ),
    // A file whose functions return a `Clock`: it needs `Clock.sw`.
    (
        "Start.sw",
        "def Nat.clock (n: Nat): Clock := { hand = n }\n",
    ),
    // A file that calls `.tick` on a `Clock` it gets from `Start.sw`, so it
    // needs `ClockMore.sw` though it never names `Clock`.
    (
        "Uses.sw",
        "def Nat.later (n: Nat): Nat := (Nat.clock n).tick.hand\n",
    ),
];

fn loaded_by_dot(program: &str) -> Vec<String> {
    let mut session = Session::with_library_files(DOT_FILES, false, false).unwrap();
    session
        .load("t.sw", program)
        .unwrap_or_else(|e| panic!("{}", messages(&e)));
    session.elab.loaded_library_files()
}

#[test]
fn dot_notation_loads_a_file_only_when_the_receivers_type_can_be_loaded() {
    // `xs.size` can't mean `Clock.size`: nothing makes a `Clock`.
    assert_eq!(
        loaded_by_dot("def x (xs: List Nat) : Nat := xs.size\n"),
        ["ListMore.sw"]
    );
    // With `Clock` named, it might, and `.tick` might mean `Clock.tick`.
    assert_eq!(
        loaded_by_dot("import Std (Clock)\ndef x (c: Clock) : Nat := c.tick.size\n"),
        ["Clock.sw", "ClockMore.sw", "ListMore.sw"]
    );
    // A `Clock` from a function in another file: `Clock.sw` loads with it.
    assert_eq!(
        loaded_by_dot("import Std (Nat)\ndef x : Nat := (Nat.clock 1).tick.hand\n"),
        ["Clock.sw", "ClockMore.sw", "Start.sw"]
    );
    // A library file's own dot calls, the same way: `Uses.sw` needs
    // `ClockMore.sw` because it needs `Start.sw`, which needs `Clock.sw`.
    assert_eq!(
        loaded_by_dot("import Std (Nat)\ndef x : Nat := Nat.later 1\n"),
        ["Clock.sw", "ClockMore.sw", "Start.sw", "Uses.sw"]
    );
    // Eager and lazy agree on all of these (§4.0).
    let mut eager = Session::with_library_files(DOT_FILES, true, false).unwrap();
    eager
        .load("t.sw", "import Std (Nat)\ndef x : Nat := Nat.later 1\n")
        .unwrap();
}

/// The library files a program loads, with the standard library.
fn std_loaded_by(program: &str) -> Vec<String> {
    let mut session = Session::new();
    session
        .load("t.sw", program)
        .unwrap_or_else(|e| panic!("{}", messages(&e)));
    session.elab.loaded_library_files()
}

#[test]
fn small_programs_load_only_the_library_files_they_can_use() {
    // SW-234: `Mod.add`, `Mod.size`, `Mod.value` and the rest are reached
    // by dot notation only on a `Mod`, so programs that make none don't
    // load `Mod/Mod.sw` (nor `Map`, `Set` or `Vec`).
    // `Result` is a core type, so the toolkit's dot calls (`.map`, `.flatMap`,
    // ...) may mean its functions too, and `Result/Result.sw` loads with it.
    // The toolkit's lemmas are in `List/Lemmas.sw` and the `Option` helpers'
    // in `Option/Lemmas.sw`, so neither loads, nor what only they use
    // (`Decidable/Decidable.sw`, `Logic/Logic.sw`). `Nat/Arith.sw` is for
    // the bounds facts that `List.chunksOf` and the congruence lemmas use.
    let toolkit = [
        "Bool/Bool.sw",
        "Nat/Arith.sw",
        "Option/Option.sw",
        "Ord/Ord.sw",
        "Result/Result.sw",
        "List/Toolkit.sw",
    ];
    assert_eq!(
        std_loaded_by("import Std (List)\ntest \"r\" := List.range 3 == [0, 1, 2]\n"),
        toolkit
    );
    assert_eq!(
        std_loaded_by("def t (xs: List Nat): Nat := xs.foldLeft 0 (a b => a + b)\n"),
        toolkit
    );
    // The sort's lemmas are in `List/SortLemmas.sw`, so neither they nor
    // `ring` (`Std.Ring` and the `Int` files under it) load. The congruence
    // lemmas of `List.sumBy` and `List.count` are in the toolkit, so the
    // toolkit's other lemmas don't load either.
    let sort = [
        "Bool/Bool.sw",
        "Nat/Arith.sw",
        "Option/Option.sw",
        "Ord/Ord.sw",
        "Result/Result.sw",
        "List/Toolkit.sw",
        "List/Sort.sw",
    ];
    assert_eq!(
        std_loaded_by("def s (xs: List Nat): List Nat := xs.sort\n"),
        sort
    );
    // `d.size` and `n.toInt` on types of the program's own and `Nat`.
    let own = "type Dial = { position: Nat }\n\
               def Dial.size (d: Dial): Nat := d.position\n\
               def x (d: Dial): Int := d.size.toInt\n";
    let loaded = std_loaded_by(own);
    assert!(!loaded.iter().any(|f| f.starts_with("Mod/")), "{loaded:?}");
    // SW-250: the list grid helpers don't load `Vec`, and plain list
    // programs don't load them.
    let grid =
        std_loaded_by("def g (rows: List (List Nat)): List (List Nat) := rows.transposeFill 0\n");
    assert!(grid.contains(&"List/Grid.sw".to_string()), "{grid:?}");
    assert!(!grid.iter().any(|f| f.starts_with("Vec/")), "{grid:?}");
    // A program using `Mod` loads it, of course.
    let modular = "import Std (Mod)\ndef x : Mod 10 := Mod.ofNat 3 + Mod.ofNat 9\n";
    assert!(std_loaded_by(modular).contains(&"Mod/Mod.sw".to_string()));
}

#[test]
fn a_dot_call_on_a_variable_of_a_written_data_type_loads_only_that_types_function() {
    let text = ["Text/Basics.sw".to_string(), "Text/Text.sw".to_string()];
    // `xs.length` with `(xs: List Nat)` is the core's `List.length`, not
    // `Text.length`: nothing loads.
    assert!(std_loaded_by("def n (xs: List Nat): Nat := xs.length\n").is_empty());
    assert!(
        std_loaded_by("def n: (xs: List Nat) → xs.length = xs.length := xs => rfl\n").is_empty()
    );
    assert!(
        std_loaded_by("def n (xs: List Nat): Nat :=\n  let ys: List Nat := xs\n  ys.length\n")
            .is_empty()
    );
    // A list-only program: the toolkit, whose `List.padRight` calls
    // `xs.length`, without `Text`.
    let padded = std_loaded_by("def p (xs: List Nat): List Nat := xs.padRight 5 0\n");
    assert!(
        padded.contains(&"List/Toolkit.sw".to_string()),
        "{padded:?}"
    );
    assert!(!padded.iter().any(|f| text.contains(f)), "{padded:?}");
    // `t.length` with `(t: Text)` loads the file declaring `Text.length`.
    let written = std_loaded_by("def n (t: Text): Nat := t.length\n");
    assert!(written.contains(&text[0]), "{written:?}");
    // Where the receiver's type isn't written, every `length` it could
    // mean loads.
    let unwritten = std_loaded_by("def n (ts: List Text): List Nat := ts.map (t => t.length)\n");
    assert!(unwritten.contains(&text[0]), "{unwritten:?}");
    // Nor where the written type is a definition, which dot calls unfold.
    let nickname = std_loaded_by("def Line: Type := Text\ndef n (l: Line): Nat := l.length\n");
    assert!(nickname.contains(&text[0]), "{nickname:?}");
}

#[test]
fn int_only_programs_dont_load_the_list_toolkit() {
    // SW-322: the `List.sumBy` lemmas about `Int` are in `Int/Sums.sw`, so
    // `Int/Int.sw` doesn't pull in `List/Toolkit.sw`.
    let loaded = std_loaded_by(
        "import Std (Int)\ntheorem t (a: Int) (b: Int): a * b = b * a := Int.mulComm a b\n",
    );
    eprintln!("INT-ONLY LOADED: {loaded:?}");
    assert!(loaded.contains(&"Int/Int.sw".to_string()), "{loaded:?}");
    assert!(
        !loaded.contains(&"List/Toolkit.sw".to_string()),
        "{loaded:?}"
    );
    assert!(!loaded.contains(&"Int/Sums.sw".to_string()), "{loaded:?}");
    // A program using the lemmas loads the file.
    let sums = std_loaded_by(
        "import Std (Int, List)\ntheorem t (xs: List Nat): (List.sumBy xs (n => n)).toInt = List.sumBy xs (n => n.toInt) :=\n  Int.toIntSumBy (n => n) xs\n",
    );
    assert!(sums.contains(&"Int/Sums.sw".to_string()), "{sums:?}");
}

#[test]
fn a_longer_cycle_names_each_file() {
    let files = [
        ("A.sw", "def Nat.cycA (n: Nat): Nat := Nat.cycB n\n"),
        ("B.sw", "def Nat.cycB (n: Nat): Nat := Nat.cycC n\n"),
        ("C.sw", "def Nat.cycC (n: Nat): Nat := Nat.cycA n\n"),
    ];
    let mut session = Session::with_library_files(&files, false, false).unwrap();
    let errors = session
        .load("t.sw", "import Std (Nat)\ndef x : Nat := Nat.cycB 1\n")
        .unwrap_err();
    let text = messages(&errors);
    for f in ["std/A.sw", "std/B.sw", "std/C.sw"] {
        assert!(text.contains(f), "{text}");
    }
}

#[test]
fn a_library_file_that_doesnt_check_is_reported_as_internal() {
    let files = [("A.sw", "def Nat.bad (n: Nat): Nat := True\n")];
    let mut session = Session::with_library_files(&files, false, false).unwrap();
    let errors = session
        .load("t.sw", "import Std (Nat)\ndef x : Nat := Nat.bad 1\n")
        .unwrap_err();
    assert_eq!(errors[0].code, "E-INTERNAL");
    assert!(errors[0].message.contains("std/A.sw"));
    assert!(errors.len() > 1);
}

// --------------------------------------------------------------------- D58

#[test]
fn no_library_file_declares_a_decision_procedure() {
    let session = Session::eager();
    // Except `Float`'s equality (docs/proposals/float.md, "As built"): it
    // decides only equations between `Float`s, which no program can write
    // without loading std/Float/Float.sw, so `auto` still can't depend on
    // what else is loaded. It is a definition of its own because the kernel
    // binds a native to it. The same holds for `Map`'s and `Set`'s equality
    // (docs/proposals/map-equality.md §8.3): an equation between maps or sets
    // needs their file loaded. So does `List.decMem` (D1201), which decides
    // `List.Mem`, declared beside it in std/List/Toolkit.sw. And `Float.decLessEq` and
    // `Float.decLessThan`, which decide `Float.LessEq` and `Float.LessThan`,
    // what `x <= y` and `x < y` on `Float` are, declared beside them. And
    // `Nat.decPowSuccNotZero`, which decides `Nat.pow (Succ b) e ≠ 0`: only a
    // goal that is or unfolds to a `Nat.pow` matches it, and `Nat.pow` is
    // declared beside it in std/Nat/Arith.sw.
    assert_eq!(
        session.elab.library_decision_procedures(),
        [
            "Std.Nat.decPowSuccNotZero",
            "Std.List.decMem",
            "Std.Float.decEqFrom",
            "Std.Float.decEq",
            "Std.Float.decLessEq",
            "Std.Float.decLessThan",
            "Std.Map.decEq",
            "Std.Map.decEq.%match1",
            "Std.Set.decEq",
            "Std.Set.decEq.%match1"
        ],
        "every `Decidable` procedure stays in the core (D58), so `auto` never \
         depends on what is loaded"
    );
    // The check does find one.
    let files = [(
        "A.sw",
        "def Nat.libDec (n: Nat): Decidable (n = n) := Nat.decEq n n\n",
    )];
    let session = Session::with_library_files(&files, true, false).unwrap();
    assert_eq!(
        session.elab.library_decision_procedures(),
        ["Std.Nat.libDec"]
    );
}

// ------------------------------------------------------------------ natives

#[test]
fn every_builtin_is_bound_once_every_file_has_loaded() {
    let session = Session::eager();
    session
        .elab
        .check_registry_complete()
        .expect("the registry is complete");
}

#[test]
fn a_builtins_home_says_which_file_declares_it() {
    let index = standard_index();
    for b in Builtin::ALL {
        let name = match b.kind() {
            Kind::Ctor(parent) => parent.name(),
            _ => b.name(),
        };
        let owner = index
            .owner(&format!("Std.{name}"))
            .unwrap_or_else(|| panic!("`{name}` isn't declared"));
        match b.home() {
            Home::Core => assert_eq!(owner, 0, "`{name}` is a core built-in"),
            Home::Library => assert_ne!(owner, 0, "`{name}` is a library built-in"),
        }
    }
}

// ------------------------------------------------------------ the core alone

/// What loading a source does in a session: whether it was accepted, the
/// errors rendered, and the hash of every declaration it made.
struct Run {
    accepted: bool,
    errors: String,
    hashes: BTreeMap<String, String>,
}

fn hashes(session: &Session) -> BTreeMap<String, String> {
    let g = &session.elab.globals;
    let show =
        |h: stitchwort_core::budget::Result<Option<stitchwort_core::hash::ContentHash>>| match h {
            Ok(Some(h)) => h.hex(),
            _ => "<none>".to_string(),
        };
    let mut out = BTreeMap::new();
    for i in 0..g.datas.len() {
        out.insert(
            format!("data {}", g.datas[i].path),
            show(data_hash(g, DataId(i))),
        );
    }
    for i in 0..g.defs.len() {
        out.insert(g.defs[i].path.to_string(), show(def_hash(g, DefId(i))));
    }
    out
}

enum Source {
    File(String, String),
    Project(String, PathBuf),
}

fn run(session: &mut Session, source: &Source) -> Run {
    let result = match source {
        Source::File(name, text) => session.load(name, text).map(|_| ()),
        Source::Project(name, path) => {
            let files = DiskFiles { root: path.clone() };
            session
                .load_project(&files, name, &Target::Everything)
                .map(|_| ())
        }
    };
    let errors = match &result {
        Ok(()) => String::new(),
        Err(ds) => ds
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect(),
    };
    Run {
        accepted: result.is_ok(),
        errors,
        hashes: hashes(session),
    }
}

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

fn example_files(dir: &str) -> Vec<Source> {
    let Ok(entries) = std::fs::read_dir(examples_dir().join(dir)) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|p| {
            Source::File(
                format!("{dir}/{}", p.file_name().unwrap().to_string_lossy()),
                std::fs::read_to_string(&p).unwrap(),
            )
        })
        .collect()
}

fn example_projects(dir: &str) -> Vec<Source> {
    let root = examples_dir().join("projects").join(dir);
    let Ok(entries) = std::fs::read_dir(&root) else {
        return Vec::new();
    };
    let mut dirs: Vec<PathBuf> = entries
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    dirs.into_iter()
        .map(|p| Source::Project(p.file_name().unwrap().to_string_lossy().to_string(), p))
        .collect()
}

fn aoc() -> Vec<Source> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    assert!(
        root.join("stitchwort.yaml").exists(),
        "aoc/ must be in the build's sources (flake.nix)"
    );
    vec![Source::Project("aoc".to_string(), root)]
}

fn name(source: &Source) -> &str {
    match source {
        Source::File(n, _) | Source::Project(n, _) => n,
    }
}

/// Loads each source in a lazy session and an eager one, and checks they
/// agree: accepted or rejected, the same errors, and the same hash for every
/// declaration the program made and every library declaration that
/// was loaded (§4.0).
///
/// A corpus sweep: every eighth source in the daily tier (a fixed sample),
/// all of them in the full tier ([`tier_sample`]); the AoC project only in
/// the full tier.
fn assert_lazy_is_eager(sources: Vec<Source>) {
    let sources = tier_sample(sources, 8);
    // Each worker keeps one eager session (loading the whole library takes a
    // second or two) and rewinds it before each source: the rewind tests
    // check that this is exactly a fresh eager session.
    let eager_worker = || {
        let eager = Session::eager_for_stack(STACK);
        let mark = eager.mark();
        (eager, mark)
    };
    let loaded = par_map_with(STACK, &sources, eager_worker, |(eager, mark), source| {
        let mut lazy = Session::for_stack(STACK);
        eager.rewind(mark);
        let a = run(&mut lazy, source);
        let b = run(eager, source);
        let n = name(source);
        assert_eq!(
            a.accepted, b.accepted,
            "{n}: accepted lazily and not eagerly"
        );
        assert_eq!(a.errors, b.errors, "{n}: its errors differ");
        // Everything the lazy session made, the eager one made the same.
        for (decl, hash) in &a.hashes {
            assert_eq!(
                b.hashes.get(decl),
                Some(hash),
                "{n}: `{decl}` differs between a lazy and an eager session"
            );
        }
        // And what the program made is all that the eager one has beyond
        // the library.
        let user = |m: &BTreeMap<String, String>| -> BTreeSet<String> {
            m.keys().filter(|k| !k.contains("Std.")).cloned().collect()
        };
        assert_eq!(user(&a.hashes), user(&b.hashes), "{n}");
        lazy.elab.loaded_library_files()
    });
    let library_loaded: BTreeSet<_> = loaded.into_iter().flatten().collect();
    eprintln!("library files some program loaded: {library_loaded:?}");
}

#[test]
fn lazy_loading_changes_nothing_for_the_accepted_examples() {
    let mut sources = example_files("accept");
    sources.extend(example_files("extract"));
    assert!(!sources.is_empty());
    assert_lazy_is_eager(sources);
}

#[test]
fn lazy_loading_changes_nothing_for_the_rejected_examples() {
    let mut sources = example_files("reject");
    sources.extend(example_files("soundness"));
    assert!(!sources.is_empty());
    assert_lazy_is_eager(sources);
}

#[test]
fn lazy_loading_changes_nothing_for_the_example_projects() {
    let mut sources = example_projects("accept");
    sources.extend(example_projects("reject"));
    assert!(!sources.is_empty());
    assert_lazy_is_eager(sources);
}

#[test]
fn lazy_loading_changes_nothing_for_the_aoc_project() {
    if !full_tier("lazy_loading_changes_nothing_for_the_aoc_project") {
        return;
    }
    assert_lazy_is_eager(aoc());
}

/// The core stands on its own: everything an example does that doesn't use a
/// library name works with the core alone. (A program that does use one is
/// refused as an unknown name.)
#[test]
fn the_core_alone_runs_every_example_that_uses_no_library_name() {
    let mut sources = example_files("accept");
    sources.extend(example_files("extract"));
    // Whether each source used no library name (and so the core alone ran it).
    let ran_alone = par_map(STACK, &sources, |source| {
        let mut core = Session::core_alone();
        core.elab.limits = stitchwort_core::Limits::for_stack(STACK);
        let mut full = Session::for_stack(STACK);
        let a = run(&mut core, source);
        let b = run(&mut full, source);
        let n = name(source);
        if full.elab.loaded_library_files().is_empty() {
            // It uses no library file: the core alone does the same.
            assert_eq!(a.accepted, b.accepted, "{n}");
            assert_eq!(a.errors, b.errors, "{n}");
            assert_eq!(a.hashes, b.hashes, "{n}");
            true
        } else {
            // It uses a library name, which the core alone doesn't have.
            assert!(b.accepted, "{n}: {}", b.errors);
            false
        }
    });
    let ran = ran_alone.iter().filter(|r| **r).count();
    let used_the_library = ran_alone.len() - ran;
    eprintln!("core alone ran {ran}; {used_the_library} use a library name");
    assert!(ran > 50);
}

/// Every compiler path that names a declaration, in a session whose library
/// is absent: records, `deriving`-style `==`, `calc`, `auto`, abilities,
/// `if`, text, `++`.
#[test]
fn the_core_alone_handles_what_the_compiler_names() {
    let program = "\
type Point = { x: Nat, y: Nat }

def origin: Point := { x = 0, y = 0 }

type Colour = | Red | Green

test \"derived equality\" := origin == { x = 0, y = 0 }

test \"derived equality on data\" := not (Red == Green)

test \"auto proves the divisor isn't zero\" := 7 / 2 == 3

theorem chain (a: Nat) (b: Nat) (h: a <= b): a <= b :=
  calc a
    _ = a := rfl
    _ <= b := h

ability Counter where
  tick: () -> {Counter} Nat

def runCounter (prog: () -> {Counter | e} a): {e} a :=
  handle prog() with
    | return x    => x
    | tick u, k   => k 7

def label (n: Nat) : Text := if n == 0 then \"zero\" else \"many\" ++ \"!\"

test \"text\" := label 0 == \"zero\"
";
    let mut session = Session::core_alone();
    if let Err(errors) = session.load("t.sw", program) {
        panic!("{}", render_all(&session, &errors));
    }
    for r in session.run_tests(&Cache::disabled()) {
        assert_eq!(r.outcome, Outcome::Passed, "{}", r.name);
    }
}

fn render_all(session: &Session, errors: &[Diagnostic]) -> String {
    errors
        .iter()
        .map(|d| render(&session.sources, d, false))
        .collect()
}

/// A report, not a check: what building the index costs (stage 1 measures it,
/// §4.3). `cargo test --release -p stitchwort-driver --test std_library
/// index_cost -- --ignored --nocapture`.
#[test]
#[ignore = "a report, not a check"]
fn index_cost() {
    for _ in 0..3 {
        let started = std::time::Instant::now();
        let index = LibraryIndex::build(prelude(), library_files(), STACK).unwrap();
        let names: usize = index.files.iter().map(|f| f.names.len()).sum();
        eprintln!("index build: {:?} ({names} names)", started.elapsed());
    }
    let started = std::time::Instant::now();
    let _ = LibraryIndex::standard(STACK).unwrap();
    eprintln!("standard index (first use): {:?}", started.elapsed());
    let started = std::time::Instant::now();
    let _ = Session::core_alone();
    eprintln!("a session, core alone: {:?}", started.elapsed());
    let started = std::time::Instant::now();
    let _ = Session::new();
    eprintln!(
        "a session with the library's names: {:?}",
        started.elapsed()
    );
}
