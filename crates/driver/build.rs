//! The build fingerprint: a hash of the source of everything that decides a
//! test's result (docs/proposals/compact-text.md, "Hashing and caches").
//!
//! Test results are cached by the test's content hash, which covers the
//! program but not the compiler. So the cache key also has this fingerprint,
//! of the sources of the syntax, the core (the evaluator, the kernel, the
//! natives and the compact representations), the elaborator with the prelude,
//! and this crate, which runs the tests: a change to any of them, even
//! without a new version number, starts a fresh cache. That invalidates more
//! than it needs to, which is preferred to tracking which Rust code a result
//! depends on.

use std::path::{Path, PathBuf};

/// The crates whose sources are hashed, relative to this one.
const SOURCES: &[&str] = &["../syntax/src", "../core/src", "../elab/src", "src"];

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("set by cargo"));
    let mut hasher = blake3::Hasher::new();
    for dir in SOURCES {
        println!("cargo:rerun-if-changed={dir}");
        let mut files = Vec::new();
        collect(&manifest.join(dir), &mut files);
        files.sort();
        for file in files {
            let relative = file.strip_prefix(&manifest).unwrap_or(&file);
            let text = std::fs::read(&file).expect("a source file can be read");
            // Each file's name and contents, with their lengths, so adjacent
            // files can't run together.
            let name = relative.to_string_lossy();
            hasher.update(&(name.len() as u64).to_le_bytes());
            hasher.update(name.as_bytes());
            hasher.update(&(text.len() as u64).to_le_bytes());
            hasher.update(&text);
        }
    }
    let hex: String = hasher.finalize().as_bytes()[..12]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
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
