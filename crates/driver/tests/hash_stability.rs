//! Pins the content hash of every declaration in the prelude and in each
//! `examples/accept` and `examples/extract` file that loads in a fresh
//! session, so a change to the elaborator can be shown to leave every
//! existing declaration's hash unchanged. One snapshot per source, one line
//! per declaration (`data` types first, then definitions), in declaration
//! order. For examples only the declarations the file added are listed.
//!
//! Files that fail to load in a fresh session are skipped (computed, not
//! hard-coded).

use std::path::Path;

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{Session, par_map, par_map_with};
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

/// Whether the example called `name` should run: `EXAMPLES` unset or empty
/// means every example, otherwise only those whose name contains it.
fn wanted(name: &str) -> bool {
    std::env::var("EXAMPLES").map_or(true, |filter| filter.is_empty() || name.contains(&filter))
}

/// A worker's eager session (every library file loaded, which takes a
/// second or two), marked so that each example can be checked in it and
/// then rewound: as a fresh eager session, without loading the library
/// again for every example. The rewind tests check that rewinding gives
/// exactly what a fresh session does.
fn eager_worker() -> (Session, Mark) {
    let session = Session::eager_for_stack(STACK);
    let mark = session.mark();
    (session, mark)
}

/// Whether `EXAMPLES` is filtering the examples.
fn filtering() -> bool {
    std::env::var("EXAMPLES").is_ok_and(|filter| !filter.is_empty())
}

fn lines(session: &Session, first_data: usize, first_def: usize) -> String {
    let g = &session.elab.globals;
    let mut out = String::new();
    for i in first_data..g.datas.len() {
        let h = show(data_hash(g, DataId(i)));
        out += &format!("data {} {h}\n", g.datas[i].path);
    }
    for i in first_def..g.defs.len() {
        let h = show(def_hash(g, DefId(i)));
        out += &format!("{} {h}\n", g.defs[i].path);
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
    let session = Session::eager();
    let text = lines(&session, 0, 0);
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
    let checked = par_map_with(
        STACK,
        &files,
        eager_worker,
        |(session, mark), (dir, path)| {
            let text = std::fs::read_to_string(path).unwrap();
            // Every library file loaded first, so the lines are the file's own.
            session.rewind(mark);
            let (d, f) = (
                session.elab.globals.datas.len(),
                session.elab.globals.defs.len(),
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
        session.elab.globals.datas.len(),
        session.elab.globals.defs.len(),
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
    assert_eq!(ascii_lines.lines().count(), 4, "{ascii_lines}");
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
        .filter(|l| !l.starts_with("Main.d "))
        .map(|l| format!("{l}\n"))
        .collect();
    assert_eq!(without_d, own_lines(long));
}

/// The accepted example projects: their declarations' hashes, as for the
/// files.
#[test]
fn projects() {
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
    }
    par_map_with(STACK, &dirs, eager_worker, |(session, mark), dir| {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        session.rewind(mark);
        let (d, f) = (
            session.elab.globals.datas.len(),
            session.elab.globals.defs.len(),
        );
        let files = DiskFiles { root: dir.clone() };
        if let Err(errors) = session.load_project(&files, &name, &Target::Everything) {
            panic!("{name} doesn't load: {errors:#?}");
        }
        insta::assert_snapshot!(format!("project-{name}"), lines(session, d, f));
    });
}

/// Checking a namespace on its own gives the same hashes as checking the
/// whole project (docs/proposals/multi-file.md: a target never changes
/// meaning): every declaration of the target, and of what it uses, has the
/// hash it has in the full check, and the target's declarations are all there.
#[test]
fn a_namespace_checked_alone_has_the_same_hashes() {
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

/// Writes every declaration's hash, for the prelude with every library file
/// and for the AoC project, to the file `HASH_DUMP` names, one sorted line
/// per declaration: for comparing two versions of the compiler
/// (docs/proposals/interfaces.md stage 5's hash oracle). Run with
/// `HASH_DUMP=… cargo test --release -p stitchwort-driver --test
/// hash_stability -- --ignored dump`.
#[test]
#[ignore]
fn dump() {
    let Ok(path) = std::env::var("HASH_DUMP") else {
        return;
    };
    let mut session = Session::eager();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let files = DiskFiles { root };
    if let Err(errors) = session.load_project(&files, "aoc", &Target::Everything) {
        panic!("aoc doesn't load: {errors:#?}");
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
    let g = &session.elab.globals;
    let mut deps = Vec::new();
    for def in &g.defs {
        let mut refs = std::collections::BTreeSet::new();
        for term in std::iter::once(&def.ty).chain(def.body().map(|b| &**b)) {
            for (t, _) in term.subterms() {
                match t {
                    stitchwort_core::Term::Def(id) => {
                        refs.insert(g.def(*id).path.to_string());
                    }
                    stitchwort_core::Term::Data(d, _)
                    | stitchwort_core::Term::Ctor(d, _, _)
                    | stitchwort_core::Term::Case(_, d, _) => {
                        refs.insert(format!("data {}", g.data(*d).path));
                    }
                    _ => {}
                }
            }
        }
        let refs: Vec<String> = refs.into_iter().collect();
        deps.push(format!("{}\t{}", def.path, refs.join("\t")));
    }
    deps.sort();
    std::fs::write(path, deps.join("\n") + "\n").unwrap();
}
