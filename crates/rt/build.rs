//! The build hash the program codec checks (`src/codec.rs`): a hash of this
//! crate's sources and of every workspace crate it's built with, so an
//! encoded program is only read by a runtime built from the same code, even
//! when the version number hasn't changed.
//!
//! The encoded format's tags are the variants of `stitchwort_core`'s
//! `Native` and `Primitive` enums (plus the runtime's own), and the program's
//! types and names come from the definitions the compiler lowered, so the
//! format depends on more than this crate's `src`. Like the driver's
//! fingerprint, the hash therefore covers the runtime's whole workspace
//! dependency graph, read from the manifests
//! ([`fingerprint::source_crates`]): core, syntax and the runtime. That
//! invalidates more than it needs to, which is preferred to tracking which
//! Rust code the bytes depend on, and covers a new dependency without a list
//! here to update. The enabled features (`CARGO_FEATURE_*`) are hashed too: a
//! feature can change the code without changing any source file.

use std::path::PathBuf;

#[path = "../driver/src/fingerprint.rs"]
#[allow(dead_code)] // the hash here is FNV, not `fingerprint::fingerprint`
mod fingerprint;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("set by cargo"));
    let root = manifest.join("../..");
    // The helper is shared with the driver's build script: rerun if it
    // changes, and cover the workspace's dependency paths and lock file,
    // which decide which crates and versions are built.
    println!("cargo:rerun-if-changed=../driver/src/fingerprint.rs");
    for file in ["Cargo.toml", "Cargo.lock"] {
        println!("cargo:rerun-if-changed={}", root.join(file).display());
    }
    let crates = fingerprint::source_crates(&root, "crates/rt");
    let mut files = Vec::new();
    for dir in &crates {
        for file in fingerprint::source_files(&root, dir) {
            println!("cargo:rerun-if-changed={}", root.join(&file).display());
            files.push(file);
        }
    }
    let mut features: Vec<(String, String)> = std::env::vars()
        .filter(|(name, _)| name.starts_with("CARGO_FEATURE_"))
        .collect();
    features.sort();
    for (name, _) in &features {
        println!("cargo:rerun-if-env-changed={name}");
    }
    let lock = std::fs::read(root.join("Cargo.lock")).ok();
    // FNV-1a over each field, with its length first so adjacent fields can't
    // run together.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut field = |bytes: &[u8]| {
        for b in (bytes.len() as u64)
            .to_le_bytes()
            .iter()
            .chain(bytes.iter())
        {
            hash ^= u64::from(*b);
            hash = hash.wrapping_mul(0x0100_0000_01b3);
        }
    };
    if let Some(lock) = &lock {
        field(b"Cargo.lock");
        field(lock);
    }
    for file in &files {
        field(file.to_string_lossy().as_bytes());
        field(&std::fs::read(root.join(file)).unwrap_or_default());
    }
    field(b"features");
    for (name, value) in &features {
        field(name.as_bytes());
        field(value.as_bytes());
    }
    println!("cargo:rustc-env=SW_RT_BUILD_HASH={hash}");
    println!("cargo:rustc-env=SW_RT_BUILD_CRATES={}", crates.join(","));
    println!(
        "cargo:rustc-env=SW_RT_BUILD_INPUTS={}",
        files
            .iter()
            .map(|f| f.to_string_lossy())
            .collect::<Vec<_>>()
            .join(",")
    );
    println!(
        "cargo:rustc-env=SW_RT_BUILD_FEATURES={}",
        features
            .iter()
            .map(|(name, _)| name
                .trim_start_matches("CARGO_FEATURE_")
                .to_lowercase()
                .replace('_', "-"))
            .collect::<Vec<_>>()
            .join(",")
    );
}
