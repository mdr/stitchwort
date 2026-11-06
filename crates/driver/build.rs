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
//!
//! The test cache's key has a narrower fingerprint
//! ([`fingerprint::evaluation_fingerprint`], SW-1329): only the Rust that
//! decides what a test computes once its term is fixed (`core`, `rt`,
//! `dev-features`, the driver's `test_run.rs`, the manifests that pick their
//! features, `Cargo.lock`, the toolchain). A test's content hash covers its
//! program and the standard library it uses, so a change to the elaborator,
//! the parser or std can only change a result by changing the hash. The
//! check cache keeps the whole-graph fingerprint above.
//!
//! The bundle-staleness fingerprint ([`fingerprint::fingerprint`] without the
//! toolchain) covers web's crate graph instead, so editing `crates/web` marks
//! `web/pkg` stale (SW-1132). The cache fingerprints stay over the driver's
//! graph: a web-only edit doesn't affect a cached test result.

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
    let crates = fingerprint::check_crates(&root);
    let mut sources = Vec::new();
    for dir in &crates {
        // The files hashed, one by one: a directory is scanned whole, and
        // the standard library's `.sw` files under `elab/src/std` must not
        // rerun this script (nothing compiled depends on them).
        for file in fingerprint::source_files(&root, dir) {
            println!("cargo:rerun-if-changed={}", root.join(&file).display());
            let text = std::fs::read(root.join(&file)).expect("a source file can be read");
            sources.push((file.to_string_lossy().into_owned(), text));
        }
    }
    println!(
        "cargo:rustc-env=STITCHWORT_FINGERPRINT_CRATES={}",
        crates.join(",")
    );
    // The bundle's staleness check also needs the web crate itself, whose
    // sources aren't part of the driver's graph (SW-1132). Its graph is the
    // driver's plus the formatter (a web dependency, not a driver one), so
    // read it from web's manifest rather than adding a list here.
    let web_crates = fingerprint::source_crates(&root, "crates/web");
    let mut web_sources = Vec::new();
    for dir in &web_crates {
        for file in fingerprint::source_files(&root, dir) {
            println!("cargo:rerun-if-changed={}", root.join(&file).display());
            let text = std::fs::read(root.join(&file)).expect("a source file can be read");
            web_sources.push((file.to_string_lossy().into_owned(), text));
        }
    }
    println!(
        "cargo:rustc-env=STITCHWORT_SOURCE_FINGERPRINT_CRATES={}",
        web_crates.join(",")
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
    // The evaluation fingerprint: the test cache's key (see above).
    for file in fingerprint::evaluation_files(&root) {
        println!("cargo:rerun-if-changed={}", root.join(file).display());
    }
    println!(
        "cargo:rustc-env=STITCHWORT_EVAL_FINGERPRINT_CRATES={}",
        fingerprint::evaluation_crates(&root).join(",")
    );
    println!(
        "cargo:rustc-env=STITCHWORT_EVAL_FINGERPRINT={}",
        fingerprint::evaluation_fingerprint(&root, &version, &target)
    );
    // The sources alone, the same for every target: so a test can tell
    // whether the WebAssembly bundle was built from these sources. Over
    // web's graph, not the driver's, because a change to the web crate's
    // own sources (or the formatter's) changes the bundle too.
    let sources_only = fingerprint::fingerprint(lock.as_deref(), &web_sources, "", "");
    println!("cargo:rustc-env=STITCHWORT_SOURCE_FINGERPRINT={sources_only}");
}
