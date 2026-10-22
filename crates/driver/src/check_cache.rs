//! Where the check cache keeps its entries (docs/proposals/check-cache.md
//! §6): `check/` in a cache directory (`.stitchwort/cache` in the project,
//! next to `tests/`), one file per entry.
//!
//! - **Names.** An entry's file is `{fingerprint}-{unit}-{key}`: the
//!   compiler build, the unit (a library file, `std.List.Toolkit`, or a
//!   project namespace, `ns.Aoc.Day05`; `+nav` when navigation is
//!   recorded), and the entry's key in hex.
//! - **The header.** `check/header` holds the directory's random salt
//!   (§3.1), made the first time the directory is used. Every entry
//!   carries it, so an entry copied from another cache directory is a miss.
//! - **Writing** goes to a temporary file that is then renamed, so a reader
//!   never sees half an entry, and two writers at once (the editor and a
//!   command) just leave the last one.
//! - **Eviction (D283).** Writing an entry deletes the unit's other entries
//!   for this build; the first write of a run deletes entries of other
//!   builds that are more than a day old (two builds may share a project
//!   folder, hence the grace period).
//!
//! The elaborator encodes, checks and replays entries; this only stores
//! them.

use std::cell::Cell;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use stitchwort_elab::cache::{Key, Store};

use crate::driver::FINGERPRINT;

/// How long entries of other builds are kept.
pub(crate) const GRACE: Duration = Duration::from_secs(24 * 60 * 60);

/// A check cache in a directory.
pub struct CheckCache {
    dir: PathBuf,
    compiler: String,
    salt: [u8; 16],
    /// Whether this run has written yet (the first write sweeps).
    written: Cell<bool>,
}

impl CheckCache {
    /// The check cache in the cache directory `cache_dir` (its `check/`
    /// folder, made if needed).
    pub fn at(cache_dir: &Path) -> CheckCache {
        let dir = cache_dir.join("check");
        let salt = salt(&dir);
        CheckCache {
            dir,
            compiler: format!("stitchwort-{}-{FINGERPRINT}", env!("CARGO_PKG_VERSION")),
            salt,
            written: Cell::new(false),
        }
    }

    fn file(&self, unit: &str, key: &Key) -> PathBuf {
        self.dir.join(format!("{FINGERPRINT}-{unit}-{}", hex(key)))
    }

    /// Deletes this unit's other entries for this build, and on the first
    /// write of a run, other builds' entries older than [`GRACE`] and
    /// temporary files left behind.
    fn evict(&self, unit: &str, keep: &Path) {
        let first = !self.written.replace(true);
        let Ok(entries) = std::fs::read_dir(&self.dir) else {
            return;
        };
        let own = format!("{FINGERPRINT}-{unit}-");
        let now = SystemTime::now();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if name == "header" || path == keep {
                continue;
            }
            let stale = name.starts_with(&own)
                || (first
                    && !name.starts_with(&format!("{FINGERPRINT}-"))
                    && entry
                        .metadata()
                        .and_then(|m| m.modified())
                        .ok()
                        .and_then(|t| now.duration_since(t).ok())
                        .is_some_and(|age| age > GRACE));
            if stale {
                let _ = std::fs::remove_file(&path);
            }
        }
    }
}

impl Store for CheckCache {
    fn compiler(&self) -> &str {
        &self.compiler
    }

    fn salt(&self) -> [u8; 16] {
        self.salt
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        std::fs::read(self.file(unit, key)).ok()
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        let path = self.file(unit, key);
        if write_atomically(&self.dir, &path, entry).is_ok() {
            self.evict(unit, &path);
        }
    }
}

/// Writes `bytes` to `path` in `dir` by way of a temporary file there.
fn write_atomically(dir: &Path, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let temp = dir.join(format!(".tmp-{}-{nanos}", std::process::id()));
    let result = std::fs::write(&temp, bytes).and_then(|()| std::fs::rename(&temp, path));
    if result.is_err() {
        let _ = std::fs::remove_file(&temp);
    }
    result
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

const HEADER: &str = "stitchwort check cache\nsalt ";

/// The salt in `dir`'s header, making the header if there isn't one. If it
/// can't be written, a new salt for this run only (its entries can't be
/// read by a later run, which is just a miss).
fn salt(dir: &Path) -> [u8; 16] {
    let header = dir.join("header");
    let read = || -> Option<[u8; 16]> {
        let text = std::fs::read_to_string(&header).ok()?;
        let hex = text.strip_prefix(HEADER)?.trim();
        let mut salt = [0u8; 16];
        if hex.len() != 32 {
            return None;
        }
        for (i, byte) in salt.iter_mut().enumerate() {
            *byte = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
        }
        Some(salt)
    };
    if let Some(salt) = read() {
        return salt;
    }
    let fresh = random_salt();
    let text = format!("{HEADER}{}\n", hex(&fresh));
    if write_atomically(dir, &header, text.as_bytes()).is_err() {
        return fresh;
    }
    // Another run may have written its header at the same time: the one on
    // disk wins.
    read().unwrap_or(fresh)
}

/// 16 random bytes, from the standard library's randomly keyed hasher.
fn random_salt() -> [u8; 16] {
    use std::hash::BuildHasher;
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let mut salt = [0u8; 16];
    for (i, chunk) in salt.chunks_mut(8).enumerate() {
        let state = std::hash::RandomState::new();
        let word = state.hash_one((nanos, std::process::id(), i));
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    salt
}
