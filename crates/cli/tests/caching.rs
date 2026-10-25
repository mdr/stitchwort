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
    let a = load("def double (n : Nat) : Nat := n + n\n\ndef use : Nat := double 2\n");
    let b = load(
        "-- the same, written differently\ndef twice (m : Nat) : Nat :=   m + m\n\ndef use : Nat := twice 2\n",
    );
    assert_eq!(hash_of(&a, "double"), hash_of(&b, "twice"));
    // `use` refers to its dependency by hash, not by name.
    assert_eq!(hash_of(&a, "use"), hash_of(&b, "use"));
}

#[test]
fn hashes_change_with_anything_a_definition_depends_on() {
    let a = load("def double (n : Nat) : Nat := n + n\n\ndef use : Nat := double 2\n");
    let b = load("def double (n : Nat) : Nat := 2 * n\n\ndef use : Nat := double 2\n");
    assert_ne!(hash_of(&a, "double"), hash_of(&b, "double"));
    assert_ne!(
        hash_of(&a, "use"),
        hash_of(&b, "use"),
        "a dependency changed"
    );
    let c = load("def double (n : Nat) : Nat := n + n\n\ndef use : Nat := double 3\n");
    assert_eq!(hash_of(&a, "double"), hash_of(&c, "double"));
    assert_ne!(hash_of(&a, "use"), hash_of(&c, "use"));
}

#[test]
fn data_types_are_nominal() {
    let a = load("type Celsius : Type =\n  | C (degrees : Nat)\n");
    let b = load("type Fahrenheit : Type =\n  | C (degrees : Nat)\n");
    assert_ne!(hash_of(&a, "Celsius"), hash_of(&b, "Fahrenheit"));
    // Field names are hashed: they're the keys of the type's JS objects, so
    // renaming one changes the generated code (docs/proposals/records.md
    // §12).
    let c = load("type Celsius : Type =\n  | C (value : Nat)\n");
    assert_ne!(hash_of(&a, "Celsius"), hash_of(&c, "Celsius"));
}

/// A record's hash covers its field names, and that it's a record (which
/// changes its JS form), but not how its declaration is laid out.
#[test]
fn record_hashes_cover_field_names_and_the_record_flag() {
    let a = load("type Person = { name : Text, age : Nat }\n");
    let renamed = load("type Person = { name : Text, years : Nat }\n");
    assert_ne!(hash_of(&a, "Person"), hash_of(&renamed, "Person"));
    let reordered = load("type Person = { age : Nat, name : Text }\n");
    assert_ne!(hash_of(&a, "Person"), hash_of(&reordered, "Person"));
    let laid_out = load("type Person =\n  { name : Text\n  , age : Nat\n  }\n");
    assert_eq!(hash_of(&a, "Person"), hash_of(&laid_out, "Person"));
    // What uses a record changes with it.
    let uses = "\n\ndef ageOf (p : Person) : Nat := p.age\n";
    let b = load(&format!("type Person = {{ name : Text, age : Nat }}{uses}"));
    let c = load(&format!(
        "type Person = {{ fullName : Text, age : Nat }}{uses}"
    ));
    assert_ne!(hash_of(&b, "ageOf"), hash_of(&c, "ageOf"));
}

/// Data types defined together are hashed as a unit
/// (docs/proposals/mutual-recursion.md §8.4): changing one constructor of
/// one changes the hashes of both, and of what uses either; the order
/// they're written in doesn't matter.
#[test]
fn data_types_defined_together_are_hashed_together() {
    let tree = "type Tree : Type =\n  | Node (label : Nat) (kids : Forest)\n\n";
    let forest = "type Forest : Type =\n  | FNil\n  | FCons (first : Tree) (rest : Forest)\n\n";
    let leaf = "def leaf : Tree := Node 0 FNil\n";
    let a = load(&format!("{tree}{forest}{leaf}"));
    let b = load(&format!("{forest}{tree}{leaf}"));
    for name in ["Tree", "Forest", "leaf"] {
        assert_eq!(hash_of(&a, name), hash_of(&b, name), "{name}");
    }
    assert_ne!(hash_of(&a, "Tree"), hash_of(&a, "Forest"));
    // A constructor of `Forest` changes: `Tree`'s hash changes too, and so
    // does `leaf`'s, which uses only `Node` and `FNil`.
    let other = "type Forest : Type =\n  | FNil\n  | FCons (rest : Forest) (first : Tree)\n\n";
    let c = load(&format!("{tree}{other}{leaf}"));
    for name in ["Tree", "Forest", "leaf"] {
        assert_ne!(hash_of(&a, name), hash_of(&c, name), "{name}");
    }
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
            "import Std (Nat)\n\ndef double (n : Nat) : Nat := {double}\n\n\
             def {t} (n : Nat) : Nat := n + n + n\n\n\
             test \"double\" := Nat.leq (double 3) 6\n\
             test \"triple\" := Nat.leq ({t} 2) 6\n\
             test \"wrong\" := Nat.leq 2 1\n",
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

/// A result is only reused by the same build of the compiler, evaluating the
/// same way: the key has the build fingerprint and the effective modes, so a
/// run with natives switched off doesn't reuse a result found with them on
/// (docs/proposals/compact-text.md, "Hashing and caches").
#[test]
fn test_results_are_only_reused_by_the_same_build_and_modes() {
    use stitchwort_cli::driver::{build_fingerprint, modes};
    let dir = std::env::temp_dir().join(format!("stitchwort-modes-test-{}", std::process::id()));
    let cache = Cache::at(&dir);
    let program = "import Std (Nat, Text)\ntest \"big\" := Nat.leq 1000 (1000 * 1000)\ntest \"text\" := Text.length \"abc\" == 3\n";
    let run = |natives: bool, compact: bool| {
        let mut session = Session::new();
        session.elab.globals.builtins.disable_natives = !natives;
        session.elab.globals.builtins.disable_compact_text = !compact;
        session.load("test.sw", program).expect("checks");
        let results = session.run_tests(&cache);
        assert!(results.iter().all(|r| r.outcome == Outcome::Passed));
        let path = cache
            .path(
                &Cache::unit("", &results[0].name),
                &results[0].hash.unwrap(),
                &modes(&session.elab.globals),
            )
            .unwrap();
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        (results.iter().map(|r| r.cached).collect::<Vec<_>>(), name)
    };
    let (cached, name) = run(true, true);
    assert_eq!(cached, [false, false]);
    assert!(
        name.contains(build_fingerprint()) && name.contains("-n1c1-"),
        "{name}"
    );
    assert!(
        build_fingerprint().len() == 24
            && build_fingerprint().chars().all(|c| c.is_ascii_hexdigit())
    );
    assert_eq!(run(true, true).0, [true, true]);
    // Natives off: nothing is reused, though the tests' hashes are the same.
    let (cached, name) = run(false, true);
    assert_eq!(cached, [false, false]);
    assert!(name.contains("-n0c1-"), "{name}");
    assert_eq!(run(false, true).0, [true, true]);
    // Compact text off: the literal's test has a new hash anyway, but the
    // other's result isn't reused either.
    let (cached, name) = run(true, false);
    assert_eq!(cached, [false, false]);
    assert!(name.contains("-n1c0-"), "{name}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// Eviction (docs/proposals/check-cache.md §6, D283): writing a result
/// deletes the same test's older results, and the first write of a run
/// deletes other builds' results more than a day old.
#[test]
fn old_test_results_are_deleted() {
    let dir = std::env::temp_dir().join(format!("stitchwort-evict-test-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let program = |n: u32| {
        format!("import Std (Nat)\ntest \"t\" := Nat.leq {n} 6\ntest \"u\" := Nat.leq 1 2\n")
    };
    let files = || -> Vec<String> {
        let mut names: Vec<String> = std::fs::read_dir(dir.join("tests"))
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    };
    load(&program(1)).run_tests(&Cache::at(&dir));
    let first = files();
    assert_eq!(first.len(), 2, "{first:?}");
    // `t` changes: its new result replaces its old one; `u`'s stays.
    let results = load(&program(2)).run_tests(&Cache::at(&dir));
    assert_eq!(
        results.iter().map(|r| r.cached).collect::<Vec<_>>(),
        [false, true]
    );
    let second = files();
    assert_eq!(second.len(), 2, "{second:?}");
    assert_eq!(
        first.iter().filter(|f| second.contains(f)).count(),
        1,
        "only `u`'s result is the same file"
    );
    // Another build's results: an old one goes, a recent one stays.
    let old = dir.join("tests").join("stitchwort-0.0.0-000000-n1c1-0-00");
    let recent = dir.join("tests").join("stitchwort-0.0.0-000000-n1c1-1-00");
    std::fs::write(&old, "passed").unwrap();
    std::fs::write(&recent, "passed").unwrap();
    let two_days_ago = std::time::SystemTime::now() - std::time::Duration::from_secs(2 * 86_400);
    std::fs::File::options()
        .write(true)
        .open(&old)
        .unwrap()
        .set_modified(two_days_ago)
        .unwrap();
    load(&program(3)).run_tests(&Cache::at(&dir));
    assert!(!old.exists(), "another build's old result is deleted");
    assert!(recent.exists(), "another build's recent result is kept");
    assert_eq!(files().len(), 3);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn ability_order_in_rows_doesnt_depend_on_declaration_order() {
    let ask = "ability Ask where
  ask : () -> {Ask} Nat
";
    let log = "ability Log where
  say : Nat -> {Log} ()
";
    let both = "def both(): {Log, Ask} Nat :=
  say 1
  ask()
";
    let a = load(&format!("{ask}{log}{both}"));
    let b = load(&format!("{log}{ask}{both}"));
    assert_eq!(hash_of(&a, "both"), hash_of(&b, "both"));
}

#[test]
fn same_shaped_recursive_members_hash_by_name_not_order() {
    let ping = "def ping (n: Nat): Nat := match n with
  | Zero => Zero
  | Succ k => pong k
";
    let pong = "def pong (n: Nat): Nat := match n with
  | Zero => Zero
  | Succ k => ping k
";
    let a = load(&format!("{ping}{pong}"));
    let b = load(&format!("{pong}{ping}"));
    assert_eq!(hash_of(&a, "ping"), hash_of(&b, "ping"));
    assert_eq!(hash_of(&a, "pong"), hash_of(&b, "pong"));
    assert_ne!(hash_of(&a, "ping"), hash_of(&a, "pong"));
}
