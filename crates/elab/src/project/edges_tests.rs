//! The namespace edges, and the longest-namespace lookup under them, against
//! the straightforward versions they replaced (SW-4829): the edges feed
//! check-cache keys, so any difference matters.

use std::collections::BTreeMap;

use stitchwort_syntax::{FileId, parse_module_recovering};

use stitchwort_syntax::Span;

use super::{Edge, FileSketch};
use crate::Elaborator;

/// The first version of `longest_namespace`: every namespace is tried.
fn longest_namespace_reference(e: &Elaborator, path: &str, equal: bool) -> Option<String> {
    e.session
        .project_namespaces
        .iter()
        .filter(|q| (equal && q.as_str() == path) || path.starts_with(&format!("{q}.")))
        .max_by_key(|q| q.len())
        .cloned()
}

/// A project: each namespace's files, as texts.
fn project() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("Aoc", vec!["namespace Aoc\n\ndef y(): Nat := 1\n"]),
        (
            "Aoc.Grid",
            vec!["namespace Aoc.Grid\n\ndef z(): Nat := 1\n"],
        ),
        (
            "Aoc.Grid.Cell",
            vec!["namespace Aoc.Grid.Cell\n\ndef c(): Nat := 1\n"],
        ),
        (
            "Lib",
            vec![
                "namespace Lib\n\ntype Range: Type =\n  | MkRange (n: Nat)\n\ndef Range.parse(n: Nat): Range := MkRange n\n",
            ],
        ),
        ("Lib.Sub", vec!["namespace Lib.Sub\n\ndef s(): Nat := 1\n"]),
        (
            "Lib.Sub.Deep",
            vec!["namespace Lib.Sub.Deep\n\ndef d(): Nat := 1\n"],
        ),
        (
            "Wild",
            vec![
                "namespace Wild\n\ndef w1(): Nat := 1\n",
                "namespace Wild\n\ndef w2(): Nat := Lib.Sub.s()\n",
            ],
        ),
        // Qualified references, nested, and through the longest namespace.
        (
            "Qualified",
            vec![
                "namespace Qualified\n\ndef a(): Nat := Aoc.Grid.Cell.c() + Aoc.y() + Aoc.Grid.Missing.x\n",
                "namespace Qualified\n\ndef b(): Nat := Lib.Sub.Deep.d() + Lib.Range.parse 1 |> .n\n",
            ],
        ),
        // `import N (..)`, and the names it brings.
        (
            "Wildcard",
            vec![
                "namespace Wildcard\n\nimport Wild (..)\n\ndef u(): Nat := w1() + w2()\n",
                "namespace Wildcard\n\nimport Lib.Sub (..)\n\ndef v(): Nat := s()\n",
            ],
        ),
        // A namespace imported as a qualifier, renamed or not.
        (
            "Qualifiers",
            vec![
                "namespace Qualifiers\n\nimport Lib (Sub)\nimport Aoc (Grid as G)\n\ndef p(): Nat := Sub.s() + G.z() + Sub.Deep.d() + G.Cell.c()\n",
                "namespace Qualifiers\n\nimport Lib.Sub (Deep as D, s as t)\n\ndef q(): Nat := D.d() + t()\n",
            ],
        ),
        // A declared name that hides a namespace's name, and a type used
        // qualified: no edge.
        (
            "Hidden",
            vec![
                "namespace Hidden\n\ndef Lib.x(): Nat := 1\n\ndef h(): Nat := Lib.x()\n",
                "namespace Hidden\n\nimport Lib (Range)\n\ndef r(): Range := Range.parse 1\n",
            ],
        ),
        // Nothing but itself.
        (
            "Own",
            vec!["namespace Own\n\ndef Own.k(): Nat := 1\n\ndef o(): Nat := Own.k()\n"],
        ),
    ]
}

fn sketches(files: &[&str]) -> Vec<FileSketch> {
    files
        .iter()
        .map(|text| {
            let (module, errors) = parse_module_recovering(FileId::SCRATCH, text, 8 << 20);
            assert!(errors.is_empty(), "{text}\n{errors:#?}");
            FileSketch::of(&module)
        })
        .collect()
}

fn edges(e: &Elaborator, name: &str, files: &[FileSketch], new: bool) -> Vec<Edge> {
    let files: Vec<&FileSketch> = files.iter().collect();
    if new {
        e.namespace_edges_of(name, &files)
    } else {
        e.namespace_edges_with(name, &files, longest_namespace_reference)
    }
}

#[test]
fn edges_equal_the_reference_on_a_project() {
    let project = project();
    let mut e = Elaborator::new();
    e.set_project_namespaces(project.iter().map(|(n, _)| n.to_string()));
    let sketched: BTreeMap<&str, Vec<FileSketch>> = project
        .iter()
        .map(|(name, files)| (*name, sketches(files)))
        .collect();
    e.set_project_names(
        sketched
            .iter()
            .map(|(name, files)| {
                let names = files.iter().flat_map(FileSketch::direct_names);
                (name.to_string(), names.map(str::to_string).collect())
            })
            .collect(),
    );
    let mut total = 0;
    for (name, files) in &sketched {
        let new = edges(&e, name, files, true);
        let old = edges(&e, name, files, false);
        let show = |v: &[Edge]| -> Vec<(String, Span)> {
            v.iter().map(|x| (x.target.clone(), x.span)).collect()
        };
        assert_eq!(show(&new), show(&old), "edges of {name}");
        total += new.len();
    }
    // The project is built to have edges of every kind.
    assert!(total >= 12, "only {total} edges");
}

#[test]
fn longest_namespace_equals_the_reference() {
    let mut e = Elaborator::new();
    e.set_project_namespaces(["A", "A.B", "A.B.C", "AB", "D.E", "F"].map(str::to_string));
    let paths = [
        "A", "A.B", "A.B.C", "A.B.C.D", "A.B.X", "A.X", "A.", "AB", "AB.C", "B", "D", "D.E",
        "D.E.F.G", "F.F", "F.", "", ".", ".A", "A..B", "X.A.B",
    ];
    for path in paths {
        for equal in [false, true] {
            assert_eq!(
                e.longest_namespace(path, equal),
                longest_namespace_reference(&e, path, equal),
                "{path:?} {equal}"
            );
        }
    }
}
