//! The build hash the program codec checks (`src/codec.rs`): a hash of this
//! crate's sources, so an encoded program is only read by a runtime built
//! from the same code, even when the version number hasn't changed.

use std::path::{Path, PathBuf};

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("set by cargo"));
    println!("cargo:rerun-if-changed=src");
    let mut files = Vec::new();
    collect(&manifest.join("src"), &mut files);
    files.sort();
    // FNV-1a over each file's relative path and bytes.
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    let mut feed = |bytes: &[u8]| {
        for b in bytes {
            hash ^= u64::from(*b);
            hash = hash.wrapping_mul(0x0100_0000_01b3);
        }
    };
    for file in files {
        let relative = file.strip_prefix(&manifest).unwrap_or(&file);
        feed(relative.to_string_lossy().as_bytes());
        feed(&std::fs::read(&file).unwrap_or_default());
    }
    println!("cargo:rustc-env=SW_RT_BUILD_HASH={hash}");
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, out);
        } else {
            out.push(path);
        }
    }
}
