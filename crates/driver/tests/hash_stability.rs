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
use stitchwort_driver::driver::Session;
use stitchwort_driver::project::{DiskFiles, Target};

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
    let mut checked = 0;
    for dir in ["accept", "extract"] {
        let mut files: Vec<_> = std::fs::read_dir(root.join(dir))
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .filter(|p| wanted(&p.file_name().unwrap().to_string_lossy()))
            .collect();
        files.sort();
        for path in files {
            let text = std::fs::read_to_string(&path).unwrap();
            // Every library file loaded first, so the lines are the file's own.
            let mut session = Session::eager();
            let (d, f) = (
                session.elab.globals.datas.len(),
                session.elab.globals.defs.len(),
            );
            if session.load(&path.display().to_string(), &text).is_err() {
                eprintln!("skipped {}", path.display());
                continue;
            }
            let stem = path.file_stem().unwrap().to_string_lossy();
            let name = if dir == "accept" {
                stem.to_string()
            } else {
                format!("extract-{stem}")
            };
            insta::assert_snapshot!(name, lines(&session, d, f));
            checked += 1;
        }
    }
    if !filtering() {
        assert!(checked > 0);
    }
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
    for dir in dirs {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let mut session = Session::eager();
        let (d, f) = (
            session.elab.globals.datas.len(),
            session.elab.globals.defs.len(),
        );
        let files = DiskFiles { root: dir.clone() };
        if let Err(errors) = session.load_project(&files, &name, &Target::Everything) {
            panic!("{name} doesn't load: {errors:#?}");
        }
        insta::assert_snapshot!(format!("project-{name}"), lines(&session, d, f));
    }
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
    for dir in dirs {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let files = DiskFiles { root: dir.clone() };
        let mut whole = Session::new();
        let loaded = whole
            .load_project(&files, &name, &Target::Everything)
            .unwrap_or_else(|e| panic!("{name} doesn't load: {e:#?}"));
        let all = lines(&whole, 0, 0);
        let all: std::collections::HashSet<&str> = all.lines().collect();
        // The whole project's lines, without the prelude's.
        let prelude = Session::new();
        let base = lines(&prelude, 0, 0);
        let base: std::collections::HashSet<&str> = base.lines().collect();
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
                if declared.starts_with(&format!("{namespace}.")) {
                    own += 1;
                }
            }
            let expected = all
                .iter()
                .filter(|l| !base.contains(*l))
                .filter(|l| {
                    l.strip_prefix("data ")
                        .unwrap_or(l)
                        .starts_with(&format!("{namespace}."))
                })
                .count();
            assert_eq!(
                own, expected,
                "{name}: {namespace} alone lacks declarations"
            );
        }
    }
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
