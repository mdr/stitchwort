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

#[test]
fn prelude() {
    let session = Session::new();
    insta::assert_snapshot!("prelude", lines(&session, 0, 0));
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
            .collect();
        files.sort();
        for path in files {
            let text = std::fs::read_to_string(&path).unwrap();
            let mut session = Session::new();
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
    assert!(checked > 0);
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
        .collect();
    dirs.sort();
    assert!(!dirs.is_empty());
    for dir in dirs {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let mut session = Session::new();
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
