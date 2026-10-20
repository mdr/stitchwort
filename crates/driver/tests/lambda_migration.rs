//! Throwaway tool for the lambda syntax switch (SW-90,
//! docs/proposals/lambda-syntax.md §8.2): delete every `\` token of every
//! `.sw` file (found with the real lexer, so `\n` in a string is untouched),
//! then check that nothing the parser or the elaborator sees has changed.
//!
//! All three tests are ignored; `LAMBDA_MIGRATION_OUT` names a scratch
//! directory. Run, in order:
//!
//! 1. in a checkout of the OLD syntax (this file copied in):
//!    `cargo test -p stitchwort-driver --test lambda_migration old -- --ignored`
//!    writes the migrated text of every file (`files/`), the old parser's
//!    syntax-tree shape of every original (`shapes/`), and every declaration's
//!    content hash with the old code (`hashes-old/`);
//! 2. in the NEW checkout: `... shapes -- --ignored` parses each migrated file
//!    with the new parser and compares shapes; with `LAMBDA_MIGRATION_APPLY=1`
//!    it also writes the migrated text over the tree's files;
//! 3. in the NEW checkout, once applied: `... hashes -- --ignored` recomputes
//!    the hashes with the new code and compares them with step 1's.
//!
//! Acceptance: every shape equal, every hash equal.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::Session;
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_syntax::equivalence::parse_shape;
use stitchwort_syntax::{SourceMap, lex};

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn out() -> PathBuf {
    PathBuf::from(std::env::var("LAMBDA_MIGRATION_OUT").expect("set LAMBDA_MIGRATION_OUT"))
}

/// Every `.sw` file under the repository, as paths relative to its root.
fn sw_files() -> Vec<String> {
    fn walk(dir: &Path, root: &Path, found: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            if path.is_dir() {
                if ![".git", "target", "node_modules", ".claude", "inputs"].contains(&name.as_str())
                {
                    walk(&path, root, found);
                }
            } else if name.ends_with(".sw") {
                let rel = path.strip_prefix(root).unwrap();
                found.push(rel.to_string_lossy().to_string());
            }
        }
    }
    let mut found = Vec::new();
    walk(&root(), &root(), &mut found);
    found.sort();
    found
}

/// `text` without its `\` tokens, and how many there were; `None` if the
/// old lexer rejects the file.
fn migrate(text: &str) -> Option<(String, usize)> {
    let mut sources = SourceMap::new();
    let file = sources.add("migrate.sw", text);
    let tokens = lex(file, text).ok()?;
    let mut result = String::new();
    let mut at = 0;
    let mut count = 0;
    for token in &tokens {
        if format!("{:?}", token.tok) == "Backslash" {
            let (start, end) = (token.span.start as usize, token.span.end as usize);
            assert_eq!(&text[start..end], "\\");
            result.push_str(&text[at..start]);
            at = end;
            count += 1;
        }
    }
    result.push_str(&text[at..]);
    Some((result, count))
}

fn show(h: stitchwort_core::budget::Result<Option<ContentHash>>) -> String {
    match h {
        Ok(Some(h)) => h.hex(),
        _ => "<none>".to_string(),
    }
}

fn lines(session: &Session, first_data: usize, first_def: usize) -> String {
    let g = &session.elab.globals;
    let mut out = String::new();
    for i in first_data..g.datas.len() {
        out += &format!(
            "data {} {}\n",
            g.datas[i].path,
            show(data_hash(g, DataId(i)))
        );
    }
    for i in first_def..g.defs.len() {
        out += &format!("{} {}\n", g.defs[i].path, show(def_hash(g, DefId(i))));
    }
    out
}

/// Every unit whose declarations' hashes are compared: the library, each
/// accepted or extracted example file, each accepted example project, and
/// the Advent of Code project. Name, then the hash lines.
fn all_hashes() -> BTreeMap<String, String> {
    let mut units = BTreeMap::new();
    let root = root();
    units.insert("prelude".to_string(), lines(&Session::eager(), 0, 0));
    for dir in ["accept", "extract"] {
        let mut files: Vec<_> = std::fs::read_dir(root.join("examples").join(dir))
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.extension().is_some_and(|e| e == "sw"))
            .collect();
        files.sort();
        for path in files {
            let text = std::fs::read_to_string(&path).unwrap();
            let mut session = Session::eager();
            let (d, f) = (
                session.elab.globals.datas.len(),
                session.elab.globals.defs.len(),
            );
            let name = format!("{dir}-{}", path.file_stem().unwrap().to_string_lossy());
            let unit = match session.load(&path.display().to_string(), &text) {
                Ok(_) => lines(&session, d, f),
                Err(_) => "<does not load>\n".to_string(),
            };
            units.insert(name, unit);
        }
    }
    let mut projects: Vec<(String, PathBuf)> =
        std::fs::read_dir(root.join("examples/projects/accept"))
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.is_dir())
            .map(|p| {
                (
                    format!("project-{}", p.file_name().unwrap().to_string_lossy()),
                    p,
                )
            })
            .collect();
    projects.push(("aoc".to_string(), root.join("aoc")));
    for (name, dir) in projects {
        let mut session = Session::eager();
        let (d, f) = (
            session.elab.globals.datas.len(),
            session.elab.globals.defs.len(),
        );
        let files = DiskFiles { root: dir };
        let project = name.strip_prefix("project-").unwrap_or(&name).to_string();
        let unit = match session.load_project(&files, &project, &Target::Everything) {
            Ok(_) => lines(&session, d, f),
            Err(e) => format!("<does not load: {} errors>\n", e.len()),
        };
        units.insert(name, unit);
    }
    units
}

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, text).unwrap();
}

#[test]
#[ignore]
fn old() {
    let out = out();
    let (mut files, mut lambdas, mut unlexable, mut unparsable) = (0, 0, 0, 0);
    for rel in sw_files() {
        let text = std::fs::read_to_string(root().join(&rel)).unwrap();
        files += 1;
        let migrated = match migrate(&text) {
            Some((migrated, n)) => {
                lambdas += n;
                migrated
            }
            None => {
                unlexable += 1;
                text.clone()
            }
        };
        let shape = parse_shape(&text);
        if shape.is_err() {
            unparsable += 1;
        }
        write(&out.join("files").join(&rel), &migrated);
        write(
            &out.join("shapes").join(&rel),
            &match shape {
                Ok(s) => s,
                Err(_) => "<does not parse>".to_string(),
            },
        );
    }
    let hashes = all_hashes();
    for (name, text) in &hashes {
        write(&out.join("hashes-old").join(name), text);
    }
    eprintln!(
        "old: {files} files, {lambdas} backslash tokens deleted, {unlexable} unlexable, \
         {unparsable} not parsing; {} hash units",
        hashes.len()
    );
}

#[test]
#[ignore]
fn shapes() {
    let out = out();
    let apply = std::env::var("LAMBDA_MIGRATION_APPLY").is_ok();
    let (mut files, mut equal, mut skipped_errors, mut changed) = (0, 0, 0, 0);
    let mut failures = Vec::new();
    for rel in sw_files() {
        files += 1;
        let migrated = std::fs::read_to_string(out.join("files").join(&rel)).unwrap();
        let old_shape = std::fs::read_to_string(out.join("shapes").join(&rel)).unwrap();
        if old_shape == "<does not parse>" {
            // A file the old parser rejected: only counted.
            skipped_errors += 1;
        } else {
            match parse_shape(&migrated) {
                Ok(new_shape) if new_shape == old_shape => equal += 1,
                Ok(_) => failures.push(format!("{rel}: the shape differs")),
                Err(e) => failures.push(format!("{rel}: the new parser fails: {e}")),
            }
        }
        if apply {
            let original = std::fs::read_to_string(root().join(&rel)).unwrap();
            if original != migrated {
                changed += 1;
                std::fs::write(root().join(&rel), &migrated).unwrap();
            }
        }
    }
    eprintln!(
        "shapes: {files} files, {equal} shapes equal, {skipped_errors} rejected by the old \
         parser (not compared), {} failures, {changed} files rewritten",
        failures.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
}

#[test]
#[ignore]
fn hashes() {
    let out = out();
    let now = all_hashes();
    let (mut equal, mut declarations) = (0, 0);
    let mut failures = Vec::new();
    for (name, text) in &now {
        let old = std::fs::read_to_string(out.join("hashes-old").join(name)).unwrap();
        if &old == text {
            equal += 1;
            declarations += text.lines().count();
        } else {
            failures.push(name.clone());
        }
    }
    eprintln!(
        "hashes: {} units, {equal} equal ({declarations} declaration lines), {} differ",
        now.len(),
        failures.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
}
