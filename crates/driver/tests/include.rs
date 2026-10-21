//! `include "file"` (docs/proposals/multi-file.md §10): a file's text, hashed
//! by its contents. Sources are in memory.

use std::collections::BTreeMap;

use stitchwort_driver::driver::{Cache, Session};
use stitchwort_driver::project::{MemoryFiles, Target};

fn memory(files: &[(&str, &str)]) -> MemoryFiles {
    MemoryFiles {
        files: files
            .iter()
            .map(|(p, t)| (p.to_string(), t.to_string()))
            .collect::<BTreeMap<_, _>>(),
        reversed: false,
    }
}

const DAY: &str = "namespace Day\n\n\
    def input: Text := include \"../inputs/day.txt\"\n\
    def other: Text := include \"../inputs/other.txt\"\n\n\
    test \"uses the input\" := input.lines == [\"a\", \"b\"]\n\
    test \"uses the other input\" := other == \"x\"\n\
    test \"uses neither\" := 1 + 1 == 2\n";

fn load(day: &str, files: &[(&str, &str)]) -> Result<Session, Vec<String>> {
    let mut all = vec![("stitchwort.yaml", "sources: [src]\n"), ("src/Day.sw", day)];
    all.extend_from_slice(files);
    let mut session = Session::new();
    session
        .load_project(&memory(&all), "proj", &Target::Everything)
        .map_err(|ds| {
            ds.into_iter()
                .map(|d| d.code.to_string())
                .collect::<Vec<_>>()
        })?;
    Ok(session)
}

fn codes(day: &str, files: &[(&str, &str)]) -> Vec<String> {
    load(day, files).err().expect("should be rejected")
}

/// Editing an included file reruns exactly the tests that use it; moving it
/// (so long as the text is the same) reruns nothing.
#[test]
fn editing_an_input_reruns_only_its_tests() {
    let inputs = [("inputs/day.txt", "a\nb\n"), ("inputs/other.txt", "x")];
    let session = load(DAY, &inputs).unwrap();
    let cache = Cache::memory([]);
    let results = session.run_tests(&cache);
    assert_eq!(results.len(), 3);
    assert!(results.iter().all(|r| !r.cached));

    // The same contents: everything is cached.
    let again = load(DAY, &inputs).unwrap();
    let results = again.run_tests(&Cache::memory(cache.added()));
    assert!(results.iter().all(|r| r.cached), "unchanged inputs hit");

    // Edit the first input: its test reruns (and now fails); the others hit.
    let edited = [("inputs/day.txt", "a\nb\nc\n"), ("inputs/other.txt", "x")];
    let session = load(DAY, &edited).unwrap();
    let results = session.run_tests(&Cache::memory(cache.added()));
    let cached = |name: &str| results.iter().find(|r| r.name == name).unwrap().cached;
    assert!(!cached("uses the input"));
    assert!(cached("uses the other input"));
    assert!(cached("uses neither"));
}

#[test]
fn moving_an_input_changes_no_hash() {
    let first = load(
        DAY,
        &[("inputs/day.txt", "a\nb\n"), ("inputs/other.txt", "x")],
    )
    .unwrap();
    let cache = Cache::memory([]);
    first.run_tests(&cache);
    let moved = DAY
        .replace("../inputs/day.txt", "../data/renamed.txt")
        .replace("../inputs/other.txt", "../data/also.txt");
    let session = load(
        &moved,
        &[("data/renamed.txt", "a\nb\n"), ("data/also.txt", "x")],
    )
    .unwrap();
    let results = session.run_tests(&Cache::memory(cache.added()));
    assert!(results.iter().all(|r| r.cached));
}

#[test]
fn a_missing_file_is_missing() {
    assert_eq!(
        codes(DAY, &[("inputs/day.txt", "a\nb\n")]),
        ["E-INCLUDE-MISSING"]
    );
}

#[test]
fn a_path_above_the_project_is_outside() {
    let day = DAY.replace("../inputs/day.txt", "../../elsewhere.txt");
    assert_eq!(
        codes(&day, &[("inputs/other.txt", "x")]),
        ["E-INCLUDE-OUTSIDE"]
    );
    let day = DAY.replace("../inputs/day.txt", "/etc/passwd");
    assert_eq!(
        codes(&day, &[("inputs/other.txt", "x")]),
        ["E-INCLUDE-OUTSIDE"]
    );
}

/// A symlink inside the project that points outside it is refused; one that
/// stays inside is followed (SW-186).
#[cfg(unix)]
#[test]
fn a_symlink_out_of_the_project_is_outside() {
    use stitchwort_driver::project::DiskFiles;
    let base = std::env::temp_dir().join(format!("sw-include-symlink-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let root = base.join("proj");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::create_dir_all(root.join("inputs")).unwrap();
    std::fs::write(base.join("secret.txt"), "secret").unwrap();
    std::fs::write(root.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::write(root.join("inputs/real.txt"), "x").unwrap();
    std::os::unix::fs::symlink(base.join("secret.txt"), root.join("inputs/out.txt")).unwrap();
    std::os::unix::fs::symlink("real.txt", root.join("inputs/in.txt")).unwrap();
    let attempt = |name: &str| {
        let day = format!(
            "namespace Day\n\ndef input: Text := include \"../inputs/{name}\"\n\ntest \"t\" := input == \"x\"\n"
        );
        std::fs::write(root.join("src/Day.sw"), day).unwrap();
        Session::new()
            .load_project(
                &DiskFiles { root: root.clone() },
                "proj",
                &Target::Everything,
            )
            .map(|_| ())
            .map_err(|ds| ds.into_iter().map(|d| d.code).collect::<Vec<_>>())
    };
    let outside = attempt("out.txt");
    let inside = attempt("in.txt");
    let _ = std::fs::remove_dir_all(&base);
    assert_eq!(outside, Err(vec!["E-INCLUDE-OUTSIDE"]));
    assert_eq!(inside, Ok(()));
}

#[test]
fn without_files_include_is_unavailable() {
    let mut session = Session::new();
    let found = session
        .load("t.sw", "def x: Text := include \"a.txt\"\n")
        .err()
        .unwrap();
    assert_eq!(found[0].code, "E-INCLUDE-UNAVAILABLE");
}

/// A 20 KB input checks and hashes quickly: it is one compact text literal.
#[test]
fn a_large_input_is_cheap() {
    let line = "7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24\n";
    let big: String = line.repeat(400);
    assert!(big.len() > 20_000);
    let day = "namespace Day\n\n\
        def input: Text := include \"../inputs/day.txt\"\n\n\
        test \"lines\" := input.lines.length == 400\n";
    let session = load(day, &[("inputs/day.txt", &big)]).unwrap();
    let results = session.run_tests(&Cache::memory([]));
    assert!(
        results
            .iter()
            .all(|r| r.outcome == stitchwort_driver::driver::Outcome::Passed)
    );
}
