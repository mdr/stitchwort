//! Reading a project's files: namespaces, what they use, the order to
//! check them in (docs/proposals/multi-file.md §4.5-4.7, §12).

use std::collections::BTreeSet;

use stitchwort_driver::driver::Session;
use stitchwort_driver::project::{Analysis, analyse, canonical_order, closure, cycle_diagnostic};

fn read(files: &[(&str, &str)]) -> Analysis {
    let mut session = Session::new();
    analyse(
        &mut session,
        "proj",
        files
            .iter()
            .map(|(path, text)| (path.to_string(), text.to_string()))
            .collect(),
    )
}

fn edges(analysis: &Analysis, name: &str) -> Vec<String> {
    analysis
        .namespace(name)
        .unwrap_or_else(|| panic!("no namespace {name}"))
        .edges
        .iter()
        .map(|e| e.target.clone())
        .collect()
}

fn all(analysis: &Analysis) -> BTreeSet<String> {
    analysis.namespaces.iter().map(|n| n.name.clone()).collect()
}

fn codes(analysis: &Analysis) -> Vec<&'static str> {
    analysis.diagnostics.iter().map(|d| d.code).collect()
}

#[test]
fn qualified_names_and_imports_make_edges() {
    let analysis = read(&[
        ("lib.sw", "namespace Lib\n\ndef f(): Nat := 1\n"),
        ("other.sw", "namespace Other\n\ndef g(): Nat := 1\n"),
        (
            "day.sw",
            "namespace Day\n\nimport Other (g)\n\ndef x(): Nat := Lib.f() + g()\n",
        ),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert_eq!(edges(&analysis, "Day"), ["Lib", "Other"]);
    assert!(edges(&analysis, "Lib").is_empty());
    assert!(edges(&analysis, "Other").is_empty());
}

/// A type named like a namespace of the project, used qualified, is the
/// type: no edge, and no false cycle.
#[test]
fn a_local_type_named_like_a_namespace_makes_no_edge() {
    let analysis = read(&[
        (
            "n.sw",
            "namespace N\n\ntype Aoc: Type =\n  | MkAoc\n\ndef x(): Aoc := Aoc.MkAoc\n",
        ),
        (
            "aoc.sw",
            "namespace Aoc\n\nimport N (Aoc)\n\ndef y(): Nat := 1\n",
        ),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert!(edges(&analysis, "N").is_empty());
    assert_eq!(edges(&analysis, "Aoc"), ["N"]);
    assert_eq!(
        canonical_order(&analysis, &all(&analysis)),
        Ok(vec!["N".to_string(), "Aoc".to_string()])
    );
}

#[test]
fn an_imported_name_used_as_qualifier() {
    let analysis = read(&[
        (
            "lib.sw",
            "namespace Lib\n\ntype Range: Type =\n  | MkRange (n: Nat)\n\ndef Range.parse(n: Nat): Range := MkRange n\n",
        ),
        (
            "day.sw",
            "namespace Day\n\nimport Lib (Range)\n\ndef r(): Range := Range.parse 1\n",
        ),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert_eq!(edges(&analysis, "Day"), ["Lib"]);
}

#[test]
fn the_longest_namespace_wins() {
    let analysis = read(&[
        ("aoc.sw", "namespace Aoc\n\ndef y(): Nat := 1\n"),
        ("grid.sw", "namespace Aoc.Grid\n\ndef z(): Nat := 1\n"),
        (
            "day.sw",
            "namespace Day\n\ndef v(): Nat := Aoc.Grid.Cell.x\n",
        ),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert_eq!(edges(&analysis, "Day"), ["Aoc.Grid"]);
}

#[test]
fn canonical_order_breaks_ties_by_name() {
    let independent = read(&[
        ("b.sw", "namespace B\n\ndef x(): Nat := 1\n"),
        ("a.sw", "namespace A\n\ndef x(): Nat := 1\n"),
        ("c.sw", "namespace C\n\ndef x(): Nat := 1\n"),
    ]);
    assert_eq!(
        canonical_order(&independent, &all(&independent)),
        Ok(vec!["A".to_string(), "B".to_string(), "C".to_string()])
    );
    let a_uses_c = read(&[
        ("b.sw", "namespace B\n\ndef x(): Nat := 1\n"),
        ("a.sw", "namespace A\n\ndef x(): Nat := C.x\n"),
        ("c.sw", "namespace C\n\ndef x(): Nat := 1\n"),
    ]);
    assert_eq!(
        canonical_order(&a_uses_c, &all(&a_uses_c)),
        Ok(vec!["B".to_string(), "C".to_string(), "A".to_string()])
    );
    assert_eq!(
        closure(&a_uses_c, &["A".to_string()]),
        ["A".to_string(), "C".to_string()]
    );
}

#[test]
fn a_three_namespace_cycle() {
    let analysis = read(&[
        ("a.sw", "namespace A\n\ndef x(): Nat := B.x\n"),
        ("b.sw", "namespace B\n\ndef x(): Nat := C.x\n"),
        ("c.sw", "namespace C\n\ndef x(): Nat := A.x\n"),
        ("d.sw", "namespace D\n\ndef x(): Nat := A.x\n"),
    ]);
    let cycles = canonical_order(&analysis, &all(&analysis)).unwrap_err();
    assert_eq!(
        cycles,
        [["A".to_string(), "B".to_string(), "C".to_string()]]
    );
    let d = cycle_diagnostic(&analysis, &cycles[0]);
    assert_eq!(d.code, "E-NAMESPACE-CYCLE");
    assert!(d.message.ends_with("A → B → C → A"), "{}", d.message);
    assert_eq!(d.labels.len(), 3);
}

#[test]
fn files_without_a_namespace_line() {
    let analysis = read(&[
        ("day05-merge.sw", "def x(): Nat := 1\n"),
        ("9.sw", "def x(): Nat := 1\n"),
    ]);
    assert_eq!(codes(&analysis), ["E-NO-NAMESPACE", "E-NO-NAMESPACE"]);
    assert!(analysis.diagnostics[0].message.contains("proj/9.sw"));
    assert!(analysis.diagnostics[0].notes[0].contains("namespace Name"));
    assert!(analysis.diagnostics[1].notes[0].contains("`namespace Day05`"));
}

#[test]
fn reserved_namespace_names() {
    let analysis = read(&[
        ("a.sw", "namespace Std.Extra\n\ndef x(): Nat := 1\n"),
        ("b.sw", "namespace List\n\ndef x(): Nat := 1\n"),
        ("c.sw", "namespace Fine\n\ndef x(): Nat := 1\n"),
    ]);
    assert_eq!(
        codes(&analysis),
        ["E-STD-NAMESPACE", "E-NAMESPACE-RESERVED"]
    );
    assert_eq!(all(&analysis), BTreeSet::from(["Fine".to_string()]));
}

#[test]
fn a_type_and_a_namespace_clash() {
    let analysis = read(&[
        (
            "aoc.sw",
            "namespace Aoc\n\ntype Grid: Type =\n  | MkGrid\n\ndef Grid.f(n: Nat): Nat := n\n",
        ),
        ("grid.sw", "namespace Aoc.Grid\n\ndef x(): Nat := 1\n"),
    ]);
    assert_eq!(codes(&analysis), ["E-NAMESPACE-CLASH", "E-NAMESPACE-CLASH"]);
    assert!(
        analysis.diagnostics[0]
            .message
            .contains("is both the type `Grid` in namespace Aoc and a namespace of its own"),
        "{}",
        analysis.diagnostics[0].message
    );
    assert!(
        analysis.diagnostics[1]
            .message
            .contains("is both a namespace inside Aoc (from `Grid.f`)"),
        "{}",
        analysis.diagnostics[1].message
    );
}

#[test]
fn read_order_doesnt_matter() {
    let files = [
        ("a.sw", "namespace A\n\ndef x(): Nat := C.x\n"),
        ("b.sw", "namespace B\n\ndef x(): Nat := A.x + C.x\n"),
        ("c.sw", "namespace C\n\ndef x(): Nat := 1\n"),
    ];
    let forward = read(&files);
    let mut reversed_files = files;
    reversed_files.reverse();
    let reversed = read(&reversed_files);
    for name in ["A", "B", "C"] {
        assert_eq!(edges(&forward, name), edges(&reversed, name));
    }
    assert_eq!(
        canonical_order(&forward, &all(&forward)),
        canonical_order(&reversed, &all(&reversed))
    );
}

/// An import's namespace is never found through another import: `Cat` in
/// `import Cat (f)` is the project namespace, not the type `A.Cat`.
#[test]
fn an_import_path_isnt_read_through_an_import() {
    let analysis = read(&[
        (
            "a.sw",
            "namespace A\n\ntype Cat = | MkA\n\ndef Cat.f: Nat := 7\n",
        ),
        ("cat.sw", "namespace Cat\n\ndef f: Nat := 1\n"),
        (
            "day.sw",
            "namespace Day\n\nimport A (Cat)\nimport Cat (f)\n\ndef g: Nat := f\n",
        ),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert_eq!(edges(&analysis, "Day"), ["A", "Cat"]);
}

#[test]
fn a_wildcard_import_makes_an_edge() {
    let analysis = read(&[
        ("lib.sw", "namespace Lib\n\ndef f(): Nat := 1\n"),
        (
            "day.sw",
            "namespace Day\n\nimport Lib (..)\n\ndef x(): Nat := 1\n",
        ),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert_eq!(edges(&analysis, "Day"), ["Lib"]);
}

const LIB_WITH_OTHER: &str = "namespace Lib\n\ntype Other = | MkO\n\ndef Other.v: Nat := 1\n";
const OTHER: &str = "namespace Other\n\ndef v: Nat := 2\n";

/// A name `import Lib (..)` brings is a short name, so as a qualifier it's
/// that, not the project namespace of the same name: no edge to it.
#[test]
fn a_wildcard_name_used_as_a_qualifier_makes_no_edge() {
    let day = "namespace Day\n\nimport Lib (..)\n\ndef x: Nat := Other.v\n";
    let analysis = read(&[
        ("lib.sw", LIB_WITH_OTHER),
        ("other.sw", OTHER),
        ("day.sw", day),
    ]);
    assert!(
        analysis.diagnostics.is_empty(),
        "{:#?}",
        analysis.diagnostics
    );
    assert_eq!(edges(&analysis, "Day"), ["Lib"]);
    // Mirror: if `Lib` doesn't declare `Other`, it is the namespace.
    let analysis = read(&[
        ("lib.sw", "namespace Lib\n\ndef f(): Nat := 1\n"),
        ("other.sw", OTHER),
        ("day.sw", day),
    ]);
    assert_eq!(edges(&analysis, "Day"), ["Lib", "Other"]);
}

#[test]
fn a_wildcard_in_one_file_doesnt_change_a_siblings_edges() {
    let analysis = read(&[
        ("lib.sw", LIB_WITH_OTHER),
        ("other.sw", OTHER),
        (
            "day1.sw",
            "namespace Day\n\nimport Lib (..)\n\ndef x(): Nat := 1\n",
        ),
        ("day2.sw", "namespace Day\n\ndef y: Nat := Other.v\n"),
    ]);
    assert_eq!(edges(&analysis, "Day"), ["Lib", "Other"]);
}

#[test]
fn wildcard_read_order_doesnt_matter() {
    let files = [
        ("a.sw", "namespace A\n\nimport C (..)\n\ndef x: Nat := y\n"),
        (
            "b.sw",
            "namespace B\n\nimport A (..)\nimport C (..)\n\ndef z: Nat := x + y\n",
        ),
        ("c.sw", "namespace C\n\ndef y: Nat := 1\n"),
    ];
    let forward = read(&files);
    let mut reversed_files = files;
    reversed_files.reverse();
    let reversed = read(&reversed_files);
    for name in ["A", "B", "C"] {
        assert_eq!(edges(&forward, name), edges(&reversed, name));
    }
    assert_eq!(edges(&forward, "B"), ["A", "C"]);
    assert_eq!(
        canonical_order(&forward, &all(&forward)),
        canonical_order(&reversed, &all(&reversed))
    );
}

/// `Lib` doesn't parse, so what its wildcard brings is unknown: `Day` makes
/// its import edge but no qualified-name edges, and no cycle appears.
#[test]
fn a_wildcard_of_a_broken_namespace_invents_no_cycle() {
    let analysis = read(&[
        ("lib.sw", "namespace Lib\n\ndef := \n"),
        (
            "day.sw",
            "namespace Day\n\nimport Lib (..)\n\ndef x: Nat := Other.v\n",
        ),
        (
            "other.sw",
            "namespace Other\n\nimport Day (..)\n\ndef v: Nat := 2\n",
        ),
    ]);
    assert_eq!(edges(&analysis, "Day"), ["Lib"]);
    assert_eq!(edges(&analysis, "Other"), ["Day"]);
    assert!(canonical_order(&analysis, &all(&analysis)).is_ok());
}

/// A refused wildcard adds no names: the file's qualifiers are read as if
/// the import weren't there. Its edges are those of an explicit import.
#[test]
fn refused_wildcards_add_no_names() {
    let aoc =
        "namespace Aoc\n\ntype Range = | MkR\n\ntype Other = | MkO\n\ndef Other.v: Nat := 1\n";
    let day = "namespace Day\n\nimport Aoc.Range (..)\nimport Day (..)\n\ndef x: Nat := Other.v\n";
    let analysis = read(&[("aoc.sw", aoc), ("other.sw", OTHER), ("day.sw", day)]);
    assert_eq!(edges(&analysis, "Day"), ["Aoc", "Other"]);
}

// ---- the scan cache (SW-4813) -------------------------------------------

mod scan_cache {
    use std::cell::{Cell, RefCell};
    use std::collections::BTreeMap;
    use std::rc::Rc;

    use stitchwort_driver::driver::Session;
    use stitchwort_driver::project::{Analysis, Scan, Target, analyse, analyse_scan};
    use stitchwort_elab::cache::{Key, Store};

    /// A store in memory that counts its writes.
    #[derive(Default)]
    struct Memory {
        entries: RefCell<BTreeMap<(String, Key), Vec<u8>>>,
        writes: Cell<usize>,
    }

    impl Store for Memory {
        fn compiler(&self) -> &str {
            "scan-cache-test"
        }
        fn salt(&self) -> [u8; 16] {
            [7; 16]
        }
        fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
            self.entries
                .borrow()
                .get(&(unit.to_string(), *key))
                .cloned()
        }
        fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
            self.writes.set(self.writes.get() + 1);
            self.entries
                .borrow_mut()
                .insert((unit.to_string(), *key), entry.to_vec());
        }
    }

    const STACK: usize = 16 * 1024 * 1024;

    fn owned(files: &[(&str, &str)]) -> Vec<(String, String)> {
        files
            .iter()
            .map(|(p, t)| (p.to_string(), t.to_string()))
            .collect()
    }

    /// Everything a reader of an analysis can see, as text: the namespaces,
    /// their files, what each uses and where, their syntax, the errors, and
    /// what `import N (..)` brings.
    fn describe(session: &Session, analysis: &Analysis) -> String {
        let mut out = String::new();
        for d in &analysis.diagnostics {
            out += &format!(
                "diagnostic {} {} {:?}\n",
                d.code,
                d.message,
                d.primary_span()
            );
        }
        for ns in &analysis.namespaces {
            out += &format!("namespace {} files {:?}\n", ns.name, ns.files);
            for e in &ns.edges {
                out += &format!("  uses {} at {:?}\n", e.target, e.span);
            }
            for d in &ns.parse_errors {
                out += &format!("  error {} {} {:?}\n", d.code, d.message, d.primary_span());
            }
            for m in ns.modules() {
                out += &format!("  module {m:?}\n");
            }
            out += &format!("  names {:?}\n", session.elab.project_names(&ns.name));
        }
        out
    }

    fn fresh(files: &[(&str, &str)]) -> String {
        let mut session = Session::new();
        let analysis = analyse(&mut session, "proj", owned(files));
        describe(&session, &analysis)
    }

    fn scanned(files: &[(&str, &str)], store: &Memory) -> String {
        let mut session = Session::new();
        let scan = Scan::new(owned(files), STACK, "proj", Some(store));
        let analysis = analyse_scan(&mut session, "proj", &scan);
        describe(&session, &analysis)
    }

    const LIB: &str = "namespace Lib\n\ndef f(): Nat := 1\n";
    const OTHER: &str = "namespace Other\n\ndef g(): Nat := 1\n";
    const DAY: &str = "namespace Day\n\nimport Other (g)\n\ndef x(): Nat := Lib.f() + g()\n";

    /// Each edit changes what the analysis reads of one file; after each,
    /// the cached scan describes the project as a fresh analysis does, and
    /// a second run on the same files reads the entry without writing it.
    #[test]
    fn a_scan_of_edited_files_reads_like_a_fresh_analysis() {
        let store = Memory::default();
        let versions: Vec<Vec<(&str, &str)>> = vec![
            vec![("lib.sw", LIB), ("other.sw", OTHER), ("day.sw", DAY)],
            // The namespace line of a file.
            vec![
                ("lib.sw", "namespace Library\n\ndef f(): Nat := 1\n"),
                ("other.sw", OTHER),
                ("day.sw", DAY),
            ],
            // An import, and a declaration another file refers to.
            vec![
                ("lib.sw", LIB),
                (
                    "other.sw",
                    "namespace Other\n\ndef g(): Nat := 1\ndef h(): Nat := 2\n",
                ),
                (
                    "day.sw",
                    "namespace Day\n\nimport Other (g, h)\n\ndef x(): Nat := Lib.f() + g() + h()\n",
                ),
            ],
            // A file that is a namespace of its own inside another's.
            vec![
                ("lib.sw", LIB),
                ("lib_f.sw", "namespace Lib.f\n\ndef y(): Nat := 1\n"),
            ],
            // No namespace line.
            vec![("lib.sw", LIB), ("bare.sw", "def x(): Nat := 1\n")],
            // A file added, a file removed.
            vec![
                ("lib.sw", LIB),
                ("day.sw", DAY),
                ("extra.sw", "namespace Extra\n"),
            ],
        ];
        for files in &versions {
            let expected = fresh(files);
            assert_eq!(scanned(files, &store), expected, "first run on {files:?}");
            let writes = store.writes.get();
            assert_eq!(scanned(files, &store), expected, "second run on {files:?}");
            assert_eq!(store.writes.get(), writes, "a hit wrote the entry again");
        }
    }

    /// A file with a syntax error is reported as it always was, in another
    /// namespace's way too, whether the rest of the project came from the
    /// cache or not.
    #[test]
    fn a_syntax_error_is_reported_as_before_cached_or_not() {
        let store = Memory::default();
        let good = [("lib.sw", LIB), ("other.sw", OTHER), ("day.sw", DAY)];
        scanned(&good, &store);
        let broken: Vec<(&str, &str)> = vec![
            ("lib.sw", LIB),
            ("other.sw", "namespace Other\n\ndef g(: Nat := 1\n"),
            ("day.sw", DAY),
        ];
        let expected = fresh(&broken);
        assert!(
            expected.contains("error "),
            "no syntax error in\n{expected}"
        );
        assert_eq!(scanned(&broken, &store), expected, "with a warm entry");
        assert_eq!(scanned(&broken, &store), expected, "again");
        assert_eq!(
            scanned(&broken, &Memory::default()),
            expected,
            "with no entry"
        );
        // The error's file isn't in the entry, and the others are.
        scanned(&good, &store);
        let writes = store.writes.get();
        assert_eq!(scanned(&good, &store), fresh(&good));
        assert_eq!(store.writes.get(), writes);
    }

    /// An entry written for another stack limit, or that is not an entry,
    /// is ignored.
    #[test]
    fn an_entry_that_does_not_fit_is_ignored() {
        let store = Memory::default();
        let files = [("lib.sw", LIB), ("day.sw", DAY)];
        let expected = fresh(&files);
        scanned(&files, &store);
        let mut session = Session::new();
        let scan = Scan::new(owned(&files), STACK / 2, "proj", Some(&store));
        let analysis = analyse_scan(&mut session, "proj", &scan);
        assert_eq!(describe(&session, &analysis), expected);
        for entry in store.entries.borrow_mut().values_mut() {
            entry.truncate(entry.len() / 2);
        }
        assert_eq!(scanned(&files, &store), expected, "a truncated entry");
        for entry in store.entries.borrow_mut().values_mut() {
            *entry = vec![0; 5];
        }
        assert_eq!(scanned(&files, &store), expected, "junk");
    }

    /// Checking a project whose scan comes from the cache gives the check
    /// cache the keys a fresh analysis does: the second run replays every
    /// namespace from the first's entries.
    #[test]
    fn a_cached_scan_gives_the_check_cache_the_same_keys() {
        stitchwort_driver::driver::with_stack(STACK, || {
            let files = [("lib.sw", LIB), ("other.sw", OTHER), ("day.sw", DAY)];
            let store = Rc::new(Memory::default());
            let run = |store: &Rc<Memory>| {
                let mut session = Session::for_stack(STACK);
                session.elab.set_check_cache(store.clone());
                let loaded = session
                    .load_project_sources("proj", owned(&files), &Target::Everything)
                    .expect("checks");
                (loaded.checked, session.elab.check_cache_stats())
            };
            let (_, cold) = run(&store);
            assert_eq!(cold.namespace_hits, 0);
            assert!(cold.namespace_written > 0, "nothing written: {cold:?}");
            let (_, warm) = run(&store);
            assert_eq!(warm.namespace_hits, cold.namespace_written, "{warm:?}");
            // An edit to a file's text makes that namespace and its users miss.
            let mut edited = owned(&files);
            edited[1].1 = "namespace Other\n\ndef g(): Nat := 3\n".to_string();
            let mut session = Session::for_stack(STACK);
            session.elab.set_check_cache(store.clone());
            session
                .load_project_sources("proj", edited, &Target::Everything)
                .expect("checks");
            let stats = session.elab.check_cache_stats();
            assert!(stats.namespace_misses >= 2, "{stats:?}");
            assert!(stats.namespace_hits >= 1, "{stats:?}");
        });
    }
}
