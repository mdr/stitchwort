//! Pins the elaborator's bare reads of `Def::body()`. Rule 6 (docs/core.md,
//! "Opaque definitions"): no declaration sees another theorem's proof. A read
//! of another definition's body goes through `Def::computing_body()`, which
//! hides a theorem's; a bare `.body()` is for the declaration being
//! elaborated, the check cache, and reports no cache entry replays. Adding
//! one fails this test: use `computing_body()`, or justify the read and
//! raise its count here (docs/reviews/SW-4732-body-read-audit.md).

use std::collections::BTreeMap;
use std::path::Path;

fn count_reads(dir: &Path, root: &Path, counts: &mut BTreeMap<String, usize>) {
    // Built in pieces so that this file doesn't count itself.
    let needle = format!(".{}{}", "body", "()");
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            count_reads(&path, root, counts);
        } else if path.extension().is_some_and(|e| e == "rs") {
            let text = std::fs::read_to_string(&path).unwrap();
            let n = text
                .lines()
                .filter(|l| !l.trim_start().starts_with("//"))
                .map(|l| l.matches(&needle).count())
                .sum::<usize>();
            if n > 0 {
                let rel = path.strip_prefix(root).unwrap().display().to_string();
                counts.insert(rel, n);
            }
        }
    }
}

#[test]
fn bare_body_reads_are_pinned() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut counts = BTreeMap::new();
    count_reads(&root, &root, &mut counts);
    let expected: BTreeMap<String, usize> = [
        // The declaration's own helpers and group, or a stated reason in place.
        ("decreasing.rs", 2),
        ("decreasing/plain.rs", 2),
        ("equations.rs", 2),
        ("equations/induct.rs", 3),
        ("carry.rs", 1),
        // Guarded by `theorem()` or `opaque()`.
        ("opaque.rs", 2),
        ("rewrite/repeatedly.rs", 2),
        // Reports and the cache, which see every proof by design.
        ("equation_notes.rs", 1),
        ("assume.rs", 1),
        ("timings.rs", 1),
        ("cache/dump.rs", 1),
        ("cache/mod.rs", 3),
    ]
    .into_iter()
    .map(|(f, n)| (f.to_string(), n))
    .collect();
    assert_eq!(counts, expected, "bare Def::body() reads changed");
}
