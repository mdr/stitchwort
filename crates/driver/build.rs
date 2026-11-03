//! The build fingerprint: a hash of the source of everything that decides a
//! test's result (docs/proposals/compact-text.md, "Hashing and caches").
//!
//! Test results are cached by the test's content hash, which covers the
//! program but not the compiler. So the cache key also has this fingerprint,
//! of the sources of this crate, which runs the tests, and of every
//! workspace crate it's built with: the syntax, the core (the evaluator, the
//! kernel, the natives and the compact representations), the elaborator
//! with the prelude, the runtime that runs the tests, the JavaScript
//! backend (whose export checks are diagnostics) and the host; each crate's
//! manifest and build script too; and `Cargo.lock`. The crates are read
//! from the manifests ([`fingerprint::source_crates`]), so a new dependency
//! is covered without a list to update (SW-1123: the runtime wasn't). A
//! change to any of them, even without a new version number, starts a fresh
//! cache. That invalidates more than it needs to, which is preferred to
//! tracking which Rust code a result depends on. The check cache's keys have
//! it too (docs/proposals/check-cache.md §4.2). So do the Rust toolchain and
//! the target (`rustc -vV`, `TARGET`), which no source or lock file covers:
//! float literals are parsed by the standard library, and the float
//! primitives compiled by it (docs/proposals/float.md §3.3).

use std::path::PathBuf;

#[path = "src/fingerprint.rs"]
mod fingerprint;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("set by cargo"));
    let root = manifest.join("../..");
    // The versions of the crates it's built with, too
    // (docs/proposals/check-cache.md §4.2): a new `num-bigint` could change
    // what the checker computes.
    let lock = root.join("Cargo.lock");
    println!("cargo:rerun-if-changed={}", lock.display());
    println!(
        "cargo:rerun-if-changed={}",
        root.join("Cargo.toml").display()
    );
    let lock = std::fs::read(&lock).ok();
    let crates = fingerprint::source_crates(&root, "crates/driver");
    let mut sources = Vec::new();
    for dir in &crates {
        // Only paths that exist: Cargo reruns the script every build for
        // one that doesn't.
        for watched in ["Cargo.toml", "build.rs", "src"] {
            let path = root.join(dir).join(watched);
            if path.exists() {
                println!("cargo:rerun-if-changed={}", path.display());
            }
        }
        for file in fingerprint::source_files(&root, dir) {
            let text = std::fs::read(root.join(&file)).expect("a source file can be read");
            sources.push((file.to_string_lossy().into_owned(), text));
        }
    }
    println!(
        "cargo:rustc-env=STITCHWORT_FINGERPRINT_CRATES={}",
        crates.join(",")
    );
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
    // The sources alone, the same for every target: so a test can tell
    // whether the WebAssembly bundle was built from these sources.
    let sources_only = fingerprint::fingerprint(lock.as_deref(), &sources, "", "");
    println!("cargo:rustc-env=STITCHWORT_SOURCE_FINGERPRINT={sources_only}");
}
