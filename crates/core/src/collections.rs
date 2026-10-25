//! Hash maps and sets whose hashes are the same on every run.
//!
//! The standard library's maps hash with a key chosen at random for each
//! map, so where a key lands differs between runs. Most of the time nothing
//! can tell, but the order of iteration differs, and so, now and then, does
//! when a map that has had keys removed grows rather than reuses its free
//! slots: a run then makes one more or one fewer allocation, and the
//! benchmarks' allocation counts differ between runs of the same program
//! (`crates/bench/tests/repeat.rs`). With these, every run does the same.
//!
//! They don't resist keys chosen to collide, which a compiler reading its
//! own user's programs doesn't need. `clippy.toml` disallows the standard
//! library's.

use std::hash::{BuildHasherDefault, Hasher};

/// A hash map whose hashes are the same on every run.
#[allow(clippy::disallowed_types)]
pub type HashMap<K, V> = std::collections::HashMap<K, V, Fixed>;

/// A hash set whose hashes are the same on every run.
#[allow(clippy::disallowed_types)]
pub type HashSet<T> = std::collections::HashSet<T, Fixed>;

/// What [`HashMap`] and [`HashSet`] hash with.
pub type Fixed = BuildHasherDefault<QuickHasher>;

/// A fast, non-cryptographic hasher: the multiply-and-rotate step of the
/// Rust compiler's `FxHasher`.
#[derive(Default, Clone, Copy)]
pub struct QuickHasher(u64);

impl QuickHasher {
    fn add(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}

impl Hasher for QuickHasher {
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            self.add(u64::from_le_bytes(word));
        }
    }
    fn write_u8(&mut self, n: u8) {
        self.add(n.into());
    }
    fn write_u16(&mut self, n: u16) {
        self.add(n.into());
    }
    fn write_u32(&mut self, n: u32) {
        self.add(n.into());
    }
    fn write_u64(&mut self, n: u64) {
        self.add(n);
    }
    fn write_usize(&mut self, n: usize) {
        self.add(n as u64);
    }
    fn finish(&self) -> u64 {
        self.0
    }
}
