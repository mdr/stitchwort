//! Content hashes and the test cache (DESIGN.md §11).

use stitchwort_cli::driver::{Cache, Outcome, Session, TestResult};
use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

fn hash_of(session: &Session, name: &str) -> ContentHash {
    let g = &session.elab.globals;
    if let Some(i) = g.defs.iter().position(|d| &*d.name == name) {
        return def_hash(g, DefId(i)).unwrap().expect("checked");
    }
    let d = g
        .datas
        .iter()
        .position(|d| &*d.name == name)
        .expect("declared");
    data_hash(g, DataId(d)).unwrap().expect("checked")
}

#[test]
fn hashes_ignore_names_layout_and_comments() {
    let a = load("double : Nat -> Nat\ndouble n = n + n\n\nuse : Nat\nuse = double 2\n");
    let b = load(
        "-- the same, written differently\ntwice : Nat -> Nat\ntwice   m =   m + m\n\nuse : Nat\nuse = twice 2\n",
    );
    assert_eq!(hash_of(&a, "double"), hash_of(&b, "twice"));
    // `use` refers to its dependency by hash, not by name.
    assert_eq!(hash_of(&a, "use"), hash_of(&b, "use"));
}

#[test]
fn hashes_change_with_anything_a_definition_depends_on() {
    let a = load("double : Nat -> Nat\ndouble n = n + n\n\nuse : Nat\nuse = double 2\n");
    let b = load("double : Nat -> Nat\ndouble n = 2 * n\n\nuse : Nat\nuse = double 2\n");
    assert_ne!(hash_of(&a, "double"), hash_of(&b, "double"));
    assert_ne!(
        hash_of(&a, "use"),
        hash_of(&b, "use"),
        "a dependency changed"
    );
    let c = load("double : Nat -> Nat\ndouble n = n + n\n\nuse : Nat\nuse = double 3\n");
    assert_eq!(hash_of(&a, "double"), hash_of(&c, "double"));
    assert_ne!(hash_of(&a, "use"), hash_of(&c, "use"));
}

#[test]
fn data_types_are_nominal() {
    let a = load("type Celsius : Type =\n  | C (degrees : Nat)\n");
    let b = load("type Fahrenheit : Type =\n  | C (degrees : Nat)\n");
    assert_ne!(hash_of(&a, "Celsius"), hash_of(&b, "Fahrenheit"));
    let c = load("type Celsius : Type =\n  | C (value : Nat)\n");
    assert_eq!(
        hash_of(&a, "Celsius"),
        hash_of(&c, "Celsius"),
        "field names are just binder names"
    );
}

fn outcomes(results: &[TestResult]) -> Vec<(&str, Outcome, bool)> {
    results
        .iter()
        .map(|r| (r.name.as_str(), r.outcome, r.cached))
        .collect()
}

#[test]
fn test_results_are_reused_until_a_dependency_changes() {
    let dir = std::env::temp_dir().join(format!("stitchwort-cache-test-{}", std::process::id()));
    let cache = Cache::at(&dir);
    let program = |double: &str, triple_name: &str| {
        format!(
            "double : Nat -> Nat\ndouble n = {double}\n\n{t} : Nat -> Nat\n{t} n = n + n + n\n\n\
             test \"double\" = leq (double 3) 6\ntest \"triple\" = leq ({t} 2) 6\ntest \"wrong\" = leq 2 1\n",
            t = triple_name
        )
    };
    let run = |source: String| load(&source).run_tests(&cache);

    let first = run(program("n + n", "triple"));
    assert_eq!(
        outcomes(&first),
        vec![
            ("double", Outcome::Passed, false),
            ("triple", Outcome::Passed, false),
            ("wrong", Outcome::Failed, false),
        ]
    );
    let second = run(program("n + n", "triple"));
    assert!(second.iter().all(|r| r.cached), "nothing changed");
    assert_eq!(
        second[2].outcome,
        Outcome::Failed,
        "failures are cached too"
    );

    let changed = run(program("2 * n", "triple"));
    assert_eq!(
        outcomes(&changed),
        vec![
            ("double", Outcome::Passed, false),
            ("triple", Outcome::Passed, true),
            ("wrong", Outcome::Failed, true),
        ]
    );
    let renamed = run(program("2 * n", "thrice"));
    assert!(
        renamed.iter().all(|r| r.cached),
        "renaming changes no hashes"
    );

    let uncached = load(&program("2 * n", "thrice")).run_tests(&Cache::disabled());
    assert!(uncached.iter().all(|r| !r.cached));
    let _ = std::fs::remove_dir_all(&dir);
}
