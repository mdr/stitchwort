//! Native code in a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): how the object `stitchwort
//! build --native` writes describes its compiled islands to the runtime
//! library that links it.
//!
//! The object defines `sw_native_manifest`, a [`Manifest`]: the hash of the
//! image the code was compiled for ([`image_hash`]), the island roots and
//! their trampolines, the code of each global and lambda as a function
//! value's (`Context::functions` and `lambdas`), and how many `Apply`
//! caches the code numbers. An object written without `--native` defines one
//! too, with no roots ([`Manifest::empty_bytes`]), so the library always
//! finds the symbol.
//!
//! The runtime rebuilds the image from the embedded program, so the
//! numbering the code bakes in (constants, operations, number tables) holds
//! only if it rebuilt the same image. The hash checks that before any
//! native code runs: a mismatch is an internal error, never a silent
//! miscompile.

use std::fmt::Write as _;

use crate::code::Image;

/// `Manifest::magic`: "swnative", little-endian.
pub const MANIFEST_MAGIC: u64 = u64::from_le_bytes(*b"swnative");
/// `Manifest::version`: the layout of [`Manifest`] and [`ManifestRoot`].
pub const MANIFEST_VERSION: u64 = 1;

/// What `sw_native_manifest` holds. `repr(C)`, written by the compiler as
/// bytes at the offsets of its fields (with relocations for the pointers),
/// read by the runtime as this struct. Every field is a 64-bit word.
#[repr(C)]
pub struct Manifest {
    pub magic: u64,
    pub version: u64,
    /// [`image_hash`] of the image the code was compiled for.
    pub image_hash: u64,
    /// How many `Apply` sites the code has (`Tables::n_caches`).
    pub n_caches: u64,
    /// The length of `functions`: the program's globals, or 0 with no roots.
    pub n_globals: u64,
    /// The length of `lambdas`: the image's lambdas, or 0 with no roots.
    pub n_lambdas: u64,
    pub n_roots: u64,
    /// For each global, its compiled code as a function value's, or null
    /// (`Context::functions`).
    pub functions: *const *const u8,
    /// For each lambda, its compiled code, or null (`Context::lambdas`).
    pub lambdas: *const *const u8,
    pub roots: *const ManifestRoot,
}

// SAFETY: a manifest is read-only data (the object's, for the process's
// life): its pointers are only read, from any thread.
#[allow(unsafe_code)]
unsafe impl Sync for Manifest {}

/// One island root of a [`Manifest`].
#[repr(C)]
pub struct ManifestRoot {
    pub global: u64,
    /// 1 if the island applies function values, so that the crossing must
    /// check its arguments hold only compiled ones.
    pub checks_arguments: u64,
    /// `(context, arguments, result)` in the host's C calling convention.
    pub trampoline: *const u8,
}

impl Manifest {
    pub const SIZE: usize = size_of::<Manifest>();
    pub const IMAGE_HASH_AT: usize = std::mem::offset_of!(Manifest, image_hash);
    pub const N_CACHES_AT: usize = std::mem::offset_of!(Manifest, n_caches);
    pub const N_GLOBALS_AT: usize = std::mem::offset_of!(Manifest, n_globals);
    pub const N_LAMBDAS_AT: usize = std::mem::offset_of!(Manifest, n_lambdas);
    pub const N_ROOTS_AT: usize = std::mem::offset_of!(Manifest, n_roots);
    pub const FUNCTIONS_AT: usize = std::mem::offset_of!(Manifest, functions);
    pub const LAMBDAS_AT: usize = std::mem::offset_of!(Manifest, lambdas);
    pub const ROOTS_AT: usize = std::mem::offset_of!(Manifest, roots);

    /// The manifest's bytes with `magic` and `version` filled in and every
    /// other field 0 (no roots, null pointers): what an object without
    /// native code holds, and what the compiler starts from.
    pub fn empty_bytes() -> Vec<u8> {
        let mut bytes = vec![0u8; Manifest::SIZE];
        bytes[..8].copy_from_slice(&MANIFEST_MAGIC.to_le_bytes());
        bytes[8..16].copy_from_slice(&MANIFEST_VERSION.to_le_bytes());
        bytes
    }

    /// The manifest's bytes for `n_roots` roots compiled for an image of
    /// hash `image_hash`, with `n_caches` caches, `n_globals` globals and
    /// `n_lambdas` lambdas; the pointers are 0, for relocations to fill.
    pub fn bytes(
        image_hash: u64,
        n_caches: u64,
        n_globals: u64,
        n_lambdas: u64,
        n_roots: u64,
    ) -> Vec<u8> {
        let mut bytes = Manifest::empty_bytes();
        for (at, value) in [
            (Manifest::IMAGE_HASH_AT, image_hash),
            (Manifest::N_CACHES_AT, n_caches),
            (Manifest::N_GLOBALS_AT, n_globals),
            (Manifest::N_LAMBDAS_AT, n_lambdas),
            (Manifest::N_ROOTS_AT, n_roots),
        ] {
            bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
        bytes
    }
}

impl ManifestRoot {
    pub const SIZE: usize = size_of::<ManifestRoot>();
    pub const TRAMPOLINE_AT: usize = std::mem::offset_of!(ManifestRoot, trampoline);

    /// A root's bytes, its trampoline 0 for a relocation to fill.
    pub fn bytes(global: u32, checks_arguments: bool) -> Vec<u8> {
        let mut bytes = vec![0u8; ManifestRoot::SIZE];
        bytes[..8].copy_from_slice(&u64::from(global).to_le_bytes());
        bytes[8..16].copy_from_slice(&u64::from(checks_arguments).to_le_bytes());
        bytes
    }
}

/// A hash of everything compiled code numbers by: the image's bodies (their
/// instructions, operands and tables), which body is each global's and
/// lambda's, the entry, and the constant pool. FNV-1a over the image's
/// `Debug` text, which holds no address (the codec's tests compare images
/// by it).
pub fn image_hash(image: &Image) -> u64 {
    struct Fnv(u64);
    impl std::fmt::Write for Fnv {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            for byte in s.bytes() {
                self.0 = (self.0 ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3);
            }
            Ok(())
        }
    }
    let mut hash = Fnv(0xcbf2_9ce4_8422_2325);
    let _ = write!(
        hash,
        "{:?}{:?}{:?}{:?}{:?}",
        image.codes, image.global_code, image.lambda_code, image.entry_code, image.pool
    );
    hash.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_layout_is_words_in_order() {
        assert_eq!(Manifest::SIZE, 80);
        assert_eq!(Manifest::ROOTS_AT, 72);
        assert_eq!(ManifestRoot::SIZE, 24);
        assert_eq!(ManifestRoot::TRAMPOLINE_AT, 16);
        let bytes = Manifest::bytes(7, 1, 2, 3, 4);
        assert_eq!(&bytes[..8], b"swnative");
        assert_eq!(bytes[Manifest::IMAGE_HASH_AT], 7);
        assert_eq!(bytes[Manifest::N_ROOTS_AT], 4);
    }
}
