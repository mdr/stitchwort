//! The test cache's key has no standard-library text (SW-1329): a library
//! edit that a test doesn't reach keeps its cached result, and one it
//! reaches runs it again, because the test's content hash covers what it
//! uses. `Cache::verifying` compares fresh runs with the cache.

use stitchwort_driver::driver::{Cache, Outcome, Session, TestResult};

const PROGRAM: &str = "import Nat (libTwice)\n\
    test \"uses\" := libTwice 2 == 4\n\
    test \"apart\" := 1 + 1 == 2\n";

fn run(library: &[(&str, &str)], cache: &Cache) -> Vec<TestResult> {
    let mut session = Session::with_library_files(library, false, false).expect("library");
    session.load("t.sw", PROGRAM).expect("checks");
    session.run_tests_fast(cache)
}

fn cached(results: &[TestResult]) -> Vec<(&str, bool)> {
    results
        .iter()
        .map(|r| (r.name.as_str(), r.cached))
        .collect()
}

fn scratch(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("sw-tck-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    dir
}

#[test]
fn a_library_edit_keeps_tests_that_dont_reach_it_cached() {
    let dir = scratch("edit");
    let cache = Cache::at(&dir);
    let base = [
        ("A.sw", "def Nat.libTwice (n: Nat): Nat := n + n\n"),
        ("B.sw", "def Nat.libUnused (n: Nat): Nat := n\n"),
    ];
    assert_eq!(
        cached(&run(&base, &cache)),
        [("uses", false), ("apart", false)]
    );
    assert_eq!(
        cached(&run(&base, &cache)),
        [("uses", true), ("apart", true)]
    );

    // Text the tests don't reach: a new definition, a changed comment, an
    // edited unused definition. Everything stays cached.
    let unrelated = [
        (
            "A.sw",
            "-- twice\ndef Nat.libTwice (n: Nat): Nat := n + n\n",
        ),
        (
            "B.sw",
            "def Nat.libUnused (n: Nat): Nat := n + 1\ndef Nat.libNew: Nat := 7\n",
        ),
    ];
    assert_eq!(
        cached(&run(&unrelated, &cache)),
        [("uses", true), ("apart", true)]
    );

    // A definition the test reaches: it runs again; the other stays cached.
    let reached = [
        ("A.sw", "def Nat.libTwice (n: Nat): Nat := 2 * n\n"),
        ("B.sw", "def Nat.libUnused (n: Nat): Nat := n\n"),
    ];
    assert_eq!(
        cached(&run(&reached, &cache)),
        [("uses", false), ("apart", true)]
    );

    // An edit that makes the test fail is seen, not hidden by the cache.
    let broken = [("A.sw", "def Nat.libTwice (n: Nat): Nat := n + 1\n")];
    let results = run(&broken, &cache);
    assert_eq!(cached(&results), [("uses", false), ("apart", true)]);
    assert_eq!(results[0].outcome, Outcome::Failed);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn verifying_compares_fresh_runs_with_the_cache() {
    let dir = scratch("verify");
    let lib = [("A.sw", "def Nat.libTwice (n: Nat): Nat := n + n\n")];
    // Nothing cached yet: nothing to compare.
    let empty = Cache::at(&dir).verifying();
    let results = run(&lib, &empty);
    assert!(results.iter().all(|r| !r.cached));
    {
        let v = empty.verification().unwrap();
        assert_eq!((v.compared, v.missing, v.disagreements.len()), (0, 2, 0));
    }
    assert!(!dir.join("tests").exists(), "verifying writes nothing");

    run(&lib, &Cache::at(&dir));
    let verify = Cache::at(&dir).verifying();
    let results = run(&lib, &verify);
    assert!(results.iter().all(|r| !r.cached), "every test runs afresh");
    {
        let v = verify.verification().unwrap();
        assert_eq!((v.compared, v.missing, v.disagreements.len()), (2, 0, 0));
    }

    // Plant a wrong result under "apart"'s key: it is reported, with the
    // test's name, and left in place.
    let apart = results.iter().find(|r| r.name == "apart").unwrap();
    let modes = "n1c1m";
    let path = Cache::at(&dir)
        .path(&Cache::unit("", "apart"), &apart.hash.unwrap(), modes)
        .unwrap();
    assert!(path.exists(), "{path:?}");
    std::fs::write(&path, "failed").unwrap();
    let verify = Cache::at(&dir).verifying();
    run(&lib, &verify);
    let v = verify.verification().unwrap();
    assert_eq!(v.disagreements.len(), 1, "{v:?}");
    let d = &v.disagreements[0];
    assert_eq!(
        (d.name.as_str(), d.cached, d.fresh),
        ("apart", Outcome::Failed, Outcome::Passed)
    );
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "failed");
    let _ = std::fs::remove_dir_all(&dir);
}
