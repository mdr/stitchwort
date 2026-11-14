//! Pins the content hash of every declaration in the prelude and in each
//! `examples/accept` and `examples/extract` file that loads in a fresh
//! session, so a change to the elaborator can be shown to leave every
//! existing declaration's hash unchanged. One snapshot per source, one line
//! per declaration (`data` types first, then definitions), in declaration
//! order. For examples only the declarations the file added are listed.
//!
//! Files that fail to load in a fresh session are skipped (computed, not
//! hard-coded). The broad and all tiers check every file and project; the
//! quick tier and the lanes check a fixed quarter of them (`tier_sample`),
//! and `EXAMPLES` keeps exactly the names matching its comma-separated
//! substrings. A part that matches no example or project is an error, so a
//! typo can't pass by sweeping nothing.

use std::path::Path;

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{
    Session, Tier, par_map, par_map_with_at_most, tier, tier_sample, with_session,
};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::rewind::Mark;

/// Stack for the worker threads that load examples.
const STACK: usize = 16 * 1024 * 1024;

fn show(h: stitchwort_core::budget::Result<Option<ContentHash>>) -> String {
    match h {
        Ok(Some(h)) => h.hex(),
        _ => "<none>".to_string(),
    }
}

/// Whether `name` matches `filter`: unset or empty means every one, otherwise
/// only those whose name contains one of its comma-separated substrings.
fn matches(filter: &str, name: &str) -> bool {
    filter.is_empty()
        || filter
            .split(',')
            .map(str::trim)
            .any(|part| !part.is_empty() && name.contains(part))
}

/// Whether the example called `name` should run: `EXAMPLES` unset or empty
/// means every example, otherwise only those whose name contains one of its
/// comma-separated substrings.
fn wanted(name: &str) -> bool {
    std::env::var("EXAMPLES").map_or(true, |filter| matches(&filter, name))
}

#[test]
fn examples_filter_takes_a_comma_separated_list() {
    assert!(matches("parse", "parse-basics.sw"));
    assert!(!matches("parse", "safe-fields.sw"));
    assert!(matches("parse,safe-fields", "safe-fields.sw"));
    assert!(matches("safe-fields, parse", "parse-basics.sw"));
    assert!(!matches("other,none", "parse-basics.sw"));
    assert!(
        matches("", "anything.sw"),
        "an empty filter keeps everything"
    );
}

/// A part that matches nothing fails, and a part that matches still counts
/// beside one that needs no match.
#[test]
fn a_filter_part_that_matches_nothing_is_an_error() {
    let names = vec!["ranges.sw".to_string(), "safe-fields.sw".to_string()];
    assert!(filter_error("ranges,safe-fields", &names).is_none());
    assert!(filter_error("", &names).is_none());
    let message = filter_error("examples", &names).unwrap();
    assert!(
        message.contains("EXAMPLES=examples matches no example (did you mean"),
        "{message}"
    );
    assert!(
        message.contains("EXAMPLES filters by example file name"),
        "{message}"
    );
    let message = filter_error("ranges,examples", &names).unwrap();
    assert!(
        message.contains("part that matches no example: `examples`"),
        "{message}"
    );
}

/// How many workers a sweep uses. Each has a whole library loaded, which
/// costs seconds of CPU where it's checked from source, for a few
/// milliseconds of examples, so in the quick tier and the lanes, with their
/// quarter sample and every core already busy, two repeat the load least; the
/// broad and all tiers check everything and use them all.
fn workers() -> usize {
    match tier() {
        Tier::Quick | Tier::Lane => 2,
        _ => usize::MAX,
    }
}

/// A worker's eager session (every library file loaded), marked so that each
/// example can be checked in it and then rewound: as a fresh eager session,
/// without loading the library again for every example. The rewind tests
/// check that rewinding gives exactly what a fresh session does.
///
/// Except in the all tier the library is replayed from the test std cache:
/// `prelude` checks it from source in the same run and holds every hash of it
/// to its snapshot, and an example's hashes come out the same only if the
/// library it uses does. The all tier checks it from source in every worker,
/// as a second guard.
fn eager_worker() -> (Session, Mark) {
    let mut session = match tier() {
        Tier::All => Session::eager_from_source_for_stack(STACK),
        _ => Session::eager_for_stack(STACK),
    };
    let mark = session.mark();
    (session, mark)
}

/// Whether `EXAMPLES` is filtering the examples.
fn filtering() -> bool {
    std::env::var("EXAMPLES").is_ok_and(|filter| !filter.is_empty())
}

/// Every name `EXAMPLES` can match: the `.sw` files in every folder under
/// `examples/` (except `examples/projects`), and every project folder under
/// `examples/projects/*/`.
///
/// Every test binary checks the same set, so a part that only names an
/// example another binary sweeps still counts, and only a part naming nothing
/// anywhere is an error.
fn all_names() -> Vec<String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut names = Vec::new();
    sw_files(&root, &mut names);
    let Ok(kinds) = std::fs::read_dir(root.join("projects")) else {
        return names;
    };
    for kind in kinds {
        let kind = kind.expect("readable directory entry").path();
        let Ok(projects) = std::fs::read_dir(kind) else {
            continue;
        };
        names.extend(
            projects
                .map(|entry| entry.expect("readable directory entry").path())
                .filter(|path| path.is_dir())
                .map(|path| path.file_name().unwrap().to_string_lossy().into_owned()),
        );
    }
    names
}

/// Adds the `.sw` file names under `dir` to `names`, recursively, skipping
/// `examples/projects` (projects match by folder name instead).
fn sw_files(dir: &Path, names: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries {
        let path = entry.expect("readable directory entry").path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "projects") {
                continue;
            }
            sw_files(&path, names);
        } else if path.extension().is_some_and(|ext| ext == "sw") {
            names.push(path.file_name().unwrap().to_string_lossy().into_owned());
        }
    }
}

/// Fails when `EXAMPLES` is set and a part matches none of the names this
/// binary checks: such a part runs no examples, silently, and a snapshot
/// run writes nothing.
fn check_examples_filter() {
    let Ok(filter) = std::env::var("EXAMPLES") else {
        return;
    };
    if let Some(message) = filter_error(&filter, &all_names()) {
        panic!("{message}");
    }
}

/// The message to fail with when an `EXAMPLES` part matches none of `names`,
/// or `None` when every non-empty part matches at least one.
fn filter_error(filter: &str, names: &[String]) -> Option<String> {
    let missing: Vec<&str> = filter
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .filter(|part| !names.iter().any(|name| name.contains(part)))
        .collect();
    if missing.is_empty() {
        return None;
    }
    let suggestion = |part: &str| {
        let nearest = nearest_names(part, names);
        if nearest.is_empty() {
            String::new()
        } else {
            format!(" (did you mean {}?)", quoted(&nearest))
        }
    };
    let what = match missing.as_slice() {
        [part] if filter.trim() == *part => {
            format!("EXAMPLES={filter} matches no example{}", suggestion(part))
        }
        [part] => format!(
            "EXAMPLES={filter} has a part that matches no example: `{part}`{}",
            suggestion(part)
        ),
        parts => {
            let clauses: Vec<String> = parts
                .iter()
                .map(|part| format!("`{part}`{}", suggestion(part)))
                .collect();
            format!(
                "EXAMPLES={filter} has parts that match no example: {}",
                clauses.join(", ")
            )
        }
    };
    Some(format!(
        "{what}; EXAMPLES filters by example file name (or project folder name)"
    ))
}

/// The `names` closest to `part`, nearest first.
fn nearest_names<'a>(part: &str, names: &'a [String]) -> Vec<&'a str> {
    let mut ranked: Vec<(&str, usize)> = names
        .iter()
        .map(|name| (name.as_str(), distance(part, name)))
        .collect();
    ranked.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(b.0)));
    ranked.into_iter().map(|(name, _)| name).take(3).collect()
}

/// The edit distance between `a` and `b`, in characters.
fn distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut previous: Vec<usize> = (0..=b.len()).collect();
    let mut current = vec![0; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        current[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let substitution = previous[j] + usize::from(ca != cb);
            current[j + 1] = (previous[j + 1] + 1).min(current[j] + 1).min(substitution);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[b.len()]
}

/// `` `a`, `b` or `c` ``, for a message.
fn quoted(names: &[&str]) -> String {
    match names {
        [] => String::new(),
        [only] => format!("`{only}`"),
        [first, second] => format!("`{first}` or `{second}`"),
        _ => {
            let (last, rest) = names.split_last().unwrap();
            let rest: Vec<String> = rest.iter().map(|name| format!("`{name}`")).collect();
            format!("{} or `{last}`", rest.join(", "))
        }
    }
}

/// A sweep's share of the examples or projects in this tier: all of them when
/// `EXAMPLES` picks some by name, otherwise `tier_sample`'s fixed sample
/// (every one in the broad and all tiers, every fourth in quick and lane).
fn share<T>(items: Vec<T>) -> Vec<T> {
    if filtering() {
        items
    } else {
        tier_sample(items, 1)
    }
}

fn lines(session: &Session, first_data: usize, first_def: usize) -> String {
    let g = &session.elab.ev();
    let mut out = String::new();
    for i in first_data..g.env.datas().len() {
        let h = show(data_hash(g, DataId(i)));
        out += &format!("data {} {h}\n", g.env.datas()[i].path());
    }
    for i in first_def..g.env.defs().len() {
        let h = show(def_hash(g, DefId(i)));
        out += &format!("{} {h}\n", g.env.defs()[i].path());
    }
    out
}

/// The core and every library file, with every declaration's hash, sorted by
/// name (the library's files load after the core, so declaration order is no
/// longer the prelude's source order). Moving a declaration between files
/// leaves this unchanged (docs/proposals/std-library.md §4.8).
#[test]
fn prelude() {
    // The snapshot is of the library this run reads (`STITCHWORT_STD_DIR`).
    eprintln!("hash_stability: {}", stitchwort_elab::std_text().mode());
    let text = with_session(STACK, Session::eager_from_source_for_stack, |session| {
        lines(session, 0, 0)
    });
    let mut sorted: Vec<&str> = text.lines().collect();
    sorted.sort_by_key(|l| {
        (
            !l.starts_with("data "),
            l.strip_prefix("data ").unwrap_or(l).to_string(),
        )
    });
    insta::assert_snapshot!("prelude", sorted.join("\n") + "\n");
}

#[test]
fn examples() {
    check_examples_filter();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut files: Vec<(&str, std::path::PathBuf)> = Vec::new();
    for dir in ["accept", "extract"] {
        let mut found: Vec<_> = std::fs::read_dir(root.join(dir))
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .filter(|p| wanted(&p.file_name().unwrap().to_string_lossy()))
            .collect();
        found.sort();
        files.extend(found.into_iter().map(|p| (dir, p)));
    }
    let files = share(files);
    let checked = par_map_with_at_most(
        STACK,
        workers(),
        &files,
        eager_worker,
        |(session, mark), (dir, path)| {
            let text = std::fs::read_to_string(path).unwrap();
            // Every library file loaded first, so the lines are the file's own.
            session.rewind(mark);
            let (d, f) = (
                session.elab.kernel.env.datas().len(),
                session.elab.kernel.env.defs().len(),
            );
            if session.load(&path.display().to_string(), &text).is_err() {
                eprintln!("skipped {}", path.display());
                return 0;
            }
            let stem = path.file_stem().unwrap().to_string_lossy();
            let name = if *dir == "accept" {
                stem.to_string()
            } else {
                format!("extract-{stem}")
            };
            insta::assert_snapshot!(name, lines(session, d, f));
            1
        },
    )
    .into_iter()
    .sum::<usize>();
    if !filtering() {
        assert!(checked > 0);
    }
}

/// The declarations `text` adds to a fresh session with every library file
/// loaded, with their hashes, by [`lines`].
fn own_lines(text: &str) -> String {
    let mut session = Session::eager();
    let (d, f) = (
        session.elab.kernel.env.datas().len(),
        session.elab.kernel.env.defs().len(),
    );
    if let Err(errors) = session.load("logic.sw", text) {
        panic!("doesn't load: {errors:#?}");
    }
    lines(&session, d, f)
}

/// The logic notation's two spellings (D1200): each Unicode symbol is the
/// token its ASCII form is, so the declarations, and their hashes, are the
/// same. And each notation is sugar (D1201-D1203): a proposition written
/// with it is the term its long form writes.
#[test]
fn logic_notation_spellings_hash_the_same() {
    let ascii = "import Std (Exists, Iff, Set)
theorem a (x: Nat) (xs: List Nat) (h: x in xs): x in xs && x !in Nil := Both h (none => none)
theorem b (p: Prop) (q: Prop) (h: p -> q): (p <-> q) || !p || exists (n: Nat) => n <= 1 && n >= 0 && n != 2 := Inr (Inr (Std.Exists.Witness 0 (Both (omega) (Both (omega) (omega)))))
theorem c (s: Set Nat) (x: Nat) (h: x in s): x in s := h
def d (seen: List Nat) (x: Nat): Bool := if x in seen then x !in [1, 2] else 3 in seen || x in Set.fromList seen
";
    let unicode = "import Std (Exists, Iff, Set)
theorem a (x: Nat) (xs: List Nat) (h: x ∈ xs): x ∈ xs ∧ x ∉ Nil := Both h (none => none)
theorem b (p: Prop) (q: Prop) (h: p → q): (p ↔ q) ∨ ¬p ∨ ∃ (n: Nat) => n ≤ 1 ∧ n ≥ 0 ∧ n ≠ 2 := Inr (Inr (Std.Exists.Witness 0 (Both (omega) (Both (omega) (omega)))))
theorem c (s: Set Nat) (x: Nat) (h: x ∈ s): x ∈ s := h
def d (seen: List Nat) (x: Nat): Bool := if x ∈ seen then x ∉ [1, 2] else 3 ∈ seen ∨ x ∈ Set.fromList seen
";
    let ascii_lines = own_lines(ascii);
    // Four declarations, and `d`'s two branch equations (`d.eq.ifTrue`, `d.eq.ifFalse`).
    assert_eq!(ascii_lines.lines().count(), 6, "{ascii_lines}");
    assert_eq!(ascii_lines, own_lines(unicode));
    // The propositions in their long forms (`d`, a program, is left out:
    // its conditions are decided by another route when written in full).
    let long = "import Std (Exists, Iff, List, Set)
theorem a (x: Nat) (xs: List Nat) (h: List.Mem x xs): And (List.Mem x xs) (Not (List.Mem x Nil)) := Both h (none => none)
theorem b (p: Prop) (q: Prop) (h: p -> q): Or (Iff p q) (Or (Not p) (Exists Nat ((n: Nat) => And (n <= 1) (And (0 <= n) (Not (n = 2)))))) := Inr (Inr (Std.Exists.Witness 0 (Both (omega) (Both (omega) (omega)))))
theorem c (s: Set Nat) (x: Nat) (h: s.contains x = True): s.contains x = True := h
";
    let without_d: String = ascii_lines
        .lines()
        .filter(|l| !l.starts_with("Main.d ") && !l.starts_with("Main.d."))
        .map(|l| format!("{l}\n"))
        .collect();
    assert_eq!(without_d, own_lines(long));
}

/// `forall` and `∀` are another spelling of the dependent function type
/// (D3458): a statement written with either is the term `(x: T) -> P`
/// writes, so its hash is the same. A bare name's type is inferred.
#[test]
fn forall_hashes_as_the_function_type() {
    let pi = "theorem a: (n: Nat) -> n + 0 = n := n => rfl
theorem b (h: (a b: Nat) -> [c: Nat] -> a + b + c = c + b + a): 1 + 2 + 3 = 3 + 2 + 1 := h 1 2
theorem c (p: Nat -> Prop) (h: (n: Nat) -> p n): (m: Nat) -> m > 0 -> p m := m => _ => h m
";
    let forall = "theorem a: forall (n: Nat) => n + 0 = n := n => rfl
theorem b (h: ∀ (a b: Nat) [c: Nat] => a + b + c = c + b + a): 1 + 2 + 3 = 3 + 2 + 1 := h 1 2
theorem c (p: Nat -> Prop) (h: ∀ n => p n): ∀ (m: Nat) => m > 0 → p m := m => _ => h m
";
    assert_eq!(own_lines(pi), own_lines(forall));
}

/// A declaration with `match`es in its type and its body: its helpers are
/// numbered in source order within the owner, the type's first and the
/// body's after them, so no two share a key (docs/proposals/
/// syntax-conveniences.md §2.4, SW-874). A local definition's are numbered
/// within it.
#[test]
fn matches_in_a_type_and_its_body_are_numbered_together() {
    let text = "def pick (n: Nat) (b: Bool): (match n with | Zero => Nat | Succ _ => Nat) -> (match b with | True => Nat | False => Nat) -> Nat :=
  def go (m: Nat): Nat := 1 + (match m with
    | Zero => 1
    | Succ k => k)
  match n with
    | Zero => (x => _ => x)
    | Succ k => (x => _ => go (match b with | True => k | False => x))
";
    let found = own_lines(text);
    let paths: Vec<&str> = found
        .lines()
        .map(|l| l.split_once(' ').expect("a path and a hash").0)
        .collect();
    // In the order they're declared: the type's two before `pick`, then the
    // body's, `go`'s numbered within it, and the inner `match` (4) before
    // the one it's in (3), which calls it.
    assert_eq!(
        paths,
        [
            "Main.pick.%match1",
            "Main.pick.%match2",
            "Main.pick",
            "Main.pick.go.%match1",
            "Main.pick.go",
            "Main.pick.%match4",
            "Main.pick.%match3",
        ],
        "{found}"
    );
}

/// The accepted example projects: their declarations' hashes, as for the
/// files.
#[test]
fn projects() {
    check_examples_filter();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept");
    let mut dirs: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .filter(|p| wanted(&p.file_name().unwrap().to_string_lossy()))
        .collect();
    dirs.sort();
    let dirs = share(dirs);
    if !filtering() {
        assert!(!dirs.is_empty());
    }
    par_map_with_at_most(
        STACK,
        workers(),
        &dirs,
        eager_worker,
        |(session, mark), dir| {
            let name = dir.file_name().unwrap().to_string_lossy().to_string();
            session.rewind(mark);
            let (d, f) = (
                session.elab.kernel.env.datas().len(),
                session.elab.kernel.env.defs().len(),
            );
            let files = DiskFiles { root: dir.clone() };
            if let Err(errors) = session.load_project(&files, &name, &Target::Everything) {
                panic!("{name} doesn't load: {errors:#?}");
            }
            insta::assert_snapshot!(format!("project-{name}"), lines(session, d, f));
        },
    );
}

/// A project namespace imported as a qualifier (`import Shop (Spec)`, then
/// `Spec.total`), or a name imported under another (`import M (x as y)`),
/// only chooses which declaration a name means: the project written with
/// every name in full has the same hashes, declaration for declaration
/// (docs/proposals/import-aliases.md §6.7, §11).
#[test]
fn import_items_hash_as_full_names() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept");
    let load = |name: &str| {
        let mut session = Session::new();
        let files = DiskFiles {
            root: root.join(name),
        };
        if let Err(errors) = session.load_project(&files, name, &Target::Everything) {
            panic!("{name} doesn't load: {errors:#?}");
        }
        lines(&session, 0, 0)
    };
    for name in ["import-namespace-item", "import-rename"] {
        let short = load(name);
        assert!(short.contains("Shop.Spec.total "), "{short}");
        assert_eq!(short, load(&format!("{name}-full-names")), "{name}");
    }
}

/// Checking a namespace on its own gives the same hashes as checking the
/// whole project (docs/proposals/multi-file.md: a target never changes
/// meaning): every declaration of the target, and of what it uses, has the
/// hash it has in the full check, and the target's declarations are all there.
#[test]
fn a_namespace_checked_alone_has_the_same_hashes() {
    check_examples_filter();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/projects/accept");
    let mut dirs: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .filter(|p| wanted(&p.file_name().unwrap().to_string_lossy()))
        .collect();
    dirs.sort();
    if !filtering() {
        assert!(!dirs.is_empty());
        // These two projects reach a namespace only through `import N (..)`: if
        // they went missing, checking alone would silently stop covering wildcards.
        for wildcard in ["wildcard-precedence", "wildcard-only-edge"] {
            assert!(
                dirs.iter()
                    .any(|d| d.file_name().is_some_and(|n| n == wildcard)),
                "{wildcard} is missing"
            );
        }
    }
    par_map(STACK, &dirs, |dir| {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let files = DiskFiles { root: dir.clone() };
        let mut whole = Session::new();
        let loaded = whole
            .load_project(&files, &name, &Target::Everything)
            .unwrap_or_else(|e| panic!("{name} doesn't load: {e:#?}"));
        let all = lines(&whole, 0, 0);
        let all: stitchwort_core::collections::HashSet<&str> = all.lines().collect();
        // The whole project's lines, without the prelude's.
        let prelude = Session::new();
        let base = lines(&prelude, 0, 0);
        let base: stitchwort_core::collections::HashSet<&str> = base.lines().collect();
        // Whether a declaration's name is in `namespace` itself, not in a
        // namespace under it (`P.Spec.f` isn't `P`'s).
        let belongs = |declared: &str, namespace: &str| {
            let longest = loaded
                .checked
                .iter()
                .filter(|q| declared.starts_with(&format!("{q}.")))
                .max_by_key(|q| q.len());
            longest.is_some_and(|q| q == namespace)
        };
        for namespace in &loaded.checked {
            let mut alone = Session::new();
            alone
                .load_project(&files, &name, &Target::Namespaces(vec![namespace.clone()]))
                .unwrap_or_else(|e| panic!("{name}: {namespace} alone doesn't load: {e:#?}"));
            let text = lines(&alone, 0, 0);
            let mut own = 0;
            for line in text.lines().filter(|l| !base.contains(l)) {
                assert!(
                    all.contains(line),
                    "{name}: `{line}` differs when {namespace} is checked alone"
                );
                let declared = line.strip_prefix("data ").unwrap_or(line);
                if belongs(declared, namespace) {
                    own += 1;
                }
            }
            let expected = all
                .iter()
                .filter(|l| !base.contains(*l))
                .filter(|l| belongs(l.strip_prefix("data ").unwrap_or(l), namespace))
                .count();
            assert_eq!(
                own, expected,
                "{name}: {namespace} alone lacks declarations"
            );
        }
    });
}

/// Stack for [`dump`]'s thread: the command line's (`crates/cli/src/main.rs`),
/// so a project loads as `stitchwort check` loads it. On the test harness's
/// default stack AoC's proofs run out (`E-RESOURCE`, SW-906).
const DUMP_STACK: usize = 64 * 1024 * 1024;

/// Writes every declaration's hash, for the prelude with every library file
/// and for a project (`HASH_DUMP_PROJECT`, a directory relative to the
/// repository's root; `aoc` if unset), to the file `HASH_DUMP` names, one
/// sorted line per declaration: for comparing two versions of the compiler
/// (docs/proposals/interfaces.md stage 5's hash oracle). Run with
/// `HASH_DUMP=… cargo test --release -p stitchwort-driver --test
/// hash_stability -- --ignored dump` (docs/testing.md, "Hash dumps").
#[test]
#[ignore]
fn dump() {
    std::thread::Builder::new()
        .stack_size(DUMP_STACK)
        .spawn(dump_on_this_thread)
        .unwrap()
        .join()
        .unwrap();
}

fn dump_on_this_thread() {
    let Ok(path) = std::env::var("HASH_DUMP") else {
        return;
    };
    let project = std::env::var("HASH_DUMP_PROJECT").unwrap_or_else(|_| "aoc".to_string());
    let mut session = Session::eager_from_source_for_stack(DUMP_STACK);
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(&project);
    let name = root.file_name().unwrap().to_string_lossy().to_string();
    let files = DiskFiles { root };
    if let Err(errors) = session.load_project(&files, &name, &Target::Everything) {
        panic!("{project} doesn't load: {errors:#?}");
    }
    let mut out: Vec<String> = lines(&session, 0, 0).lines().map(str::to_string).collect();
    out.sort();
    std::fs::write(path, out.join("\n") + "\n").unwrap();
    // With `HASH_DEPS`, also each definition's direct references (in its
    // type and body), one line per definition: `name ref ref …`, for
    // working out the dependency closure of what changed.
    let Ok(path) = std::env::var("HASH_DEPS") else {
        return;
    };
    let g = &session.elab.ev();
    let mut deps = Vec::new();
    for def in g.env.defs() {
        let mut refs = std::collections::BTreeSet::new();
        for term in std::iter::once(def.ty()).chain(def.body().map(|b| &**b)) {
            for (t, _) in term.subterms() {
                match t {
                    stitchwort_core::Term::Def(id) => {
                        refs.insert(g.def(*id).path().to_string());
                    }
                    stitchwort_core::Term::Data(d, _)
                    | stitchwort_core::Term::Ctor(d, _, _)
                    | stitchwort_core::Term::Case(_, d, _) => {
                        refs.insert(format!("data {}", g.data(*d).path()));
                    }
                    _ => {}
                }
            }
        }
        let refs: Vec<String> = refs.into_iter().collect();
        deps.push(format!("{}\t{}", def.path(), refs.join("\t")));
    }
    deps.sort();
    std::fs::write(path, deps.join("\n") + "\n").unwrap();
}
