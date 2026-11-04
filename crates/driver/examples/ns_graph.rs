//! Prints an import graph, one line per unit: `name<TAB>dep,dep,...`.
//! For dev/measurements/parallel-checking.md (SW-1170); not part of the CLI.
//!
//! `ns_graph PROJECT_DIR`: a project's namespaces and their direct edges
//! (the ones `check` orders by). `ns_graph --std`: the standard library's
//! files (`std/Map/Spec.sw`, as `STITCHWORT_TIMINGS` labels them) and the
//! files each needs.
//!
//! cargo run --release -p stitchwort-driver --example ns_graph -- aoc

use std::path::PathBuf;

use stitchwort_driver::driver::Session;
use stitchwort_driver::project::{DiskFiles, analyse, project_sources};
use stitchwort_elab::LibraryIndex;

fn main() {
    let arg = std::env::args().nth(1).expect("a project folder, or --std");
    if arg == "--std" {
        let index = LibraryIndex::standard(8 << 20).expect("the library parses");
        let label = |f: usize| {
            let p = &index.files[f].path;
            if p == "core" {
                p.clone()
            } else {
                format!("std/{p}")
            }
        };
        for (f, file) in index.files.iter().enumerate() {
            let mut deps: Vec<String> = file.edges.iter().map(|&d| label(d)).collect();
            deps.sort();
            println!("{}\t{}", label(f), deps.join(","));
        }
        return;
    }
    let root = PathBuf::from(arg);
    let name = (root.canonicalize().unwrap().file_name().unwrap())
        .to_string_lossy()
        .into_owned();
    let mut session = Session::new();
    let files = DiskFiles { root };
    let sources = project_sources(&files, &name, &mut session.sources)
        .unwrap_or_else(|_| panic!("can't read the project"));
    let analysis = analyse(&mut session, &name, sources);
    for ns in &analysis.namespaces {
        let mut deps: Vec<&str> = ns.edges.iter().map(|e| e.target.as_str()).collect();
        deps.sort();
        deps.dedup();
        deps.retain(|d| *d != ns.name);
        println!("{}\t{}", ns.name, deps.join(","));
    }
}
