//! The build fingerprint: a hash of the source of everything that decides a
//! test's result (docs/proposals/compact-text.md, "Hashing and caches").
//!
//! Test results are cached by the test's content hash, which covers the
//! program but not the compiler. So the cache key also has this fingerprint,
//! of the sources of the syntax, the core (the evaluator, the kernel, the
//! natives and the compact representations), the elaborator with the prelude,
//! and this crate, which runs the tests, and of `Cargo.lock`: a change to
//! any of them, even without a new version number, starts a fresh cache.
//! That invalidates more than it needs to, which is preferred to tracking
//! which Rust code a result depends on. The check cache's keys have it too
//! (docs/proposals/check-cache.md §4.2). So do the Rust toolchain and the
//! target (`rustc -vV`, `TARGET`), which no source or lock file covers:
//! float literals are parsed by the standard library, and the float
//! primitives compiled by it (docs/proposals/float.md §3.3).

use std::path::{Path, PathBuf};

#[path = "src/fingerprint.rs"]
mod fingerprint;

/// The crates whose sources are hashed, relative to this one.
const SOURCES: &[&str] = &["../syntax/src", "../core/src", "../elab/src", "src"];

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("set by cargo"));
    // The versions of the crates it's built with, too
    // (docs/proposals/check-cache.md §4.2): a new `num-bigint` could change
    // what the checker computes.
    let lock = manifest.join("../../Cargo.lock");
    println!("cargo:rerun-if-changed={}", lock.display());
    let lock = std::fs::read(&lock).ok();
    let mut sources = Vec::new();
    for dir in SOURCES {
        println!("cargo:rerun-if-changed={dir}");
        let mut files = Vec::new();
        collect(&manifest.join(dir), &mut files);
        files.sort();
        for file in files {
            let relative = file.strip_prefix(&manifest).unwrap_or(&file);
            let text = std::fs::read(&file).expect("a source file can be read");
            sources.push((relative.to_string_lossy().into_owned(), text));
        }
    }
    // The compiler: `rustc -vV` names its version, commit and LLVM; and the
    // target it compiles for.
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let version = std::process::Command::new(&rustc)
        .arg("-vV")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
        .unwrap_or_default();
    let target = std::env::var("TARGET").unwrap_or_default();
    let hex = fingerprint::fingerprint(lock.as_deref(), &sources, &version, &target);
    println!("cargo:rustc-env=STITCHWORT_FINGERPRINT={hex}");
}

/// The Rust and Stitchwort sources under `dir`, recursively.
fn collect(dir: &Path, files: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, files);
        } else if path
            .extension()
            .is_some_and(|ext| ext == "rs" || ext == "sw")
        {
            files.push(path);
        }
    }
}
