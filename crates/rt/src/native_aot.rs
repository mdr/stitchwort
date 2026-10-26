//! Native code in a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): how the object `stitchwort
//! build --native` writes describes its compiled bodies to the runtime
//! library that links it.
//!
//! The object defines `sw_native_manifest`, a [`Manifest`]: the hash of the
//! image the code was compiled for ([`image_hash`]), the trampolines from
//! the runtime into the code (stage NO4 of docs/proposals/native-only.md:
//! into the entry, the apply stubs and the effect runtime's loop), the code
//! of each global and lambda as a function value's (`Context::functions`
//! and `lambdas`), how many `Apply` caches the code numbers, and its
//! frames' bound. An object written without `--native` defines one too,
//! with no code ([`Manifest::empty_bytes`]), so the library always finds
//! the symbol.
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
/// `Manifest::version`: the layout of [`Manifest`]. Version 2 (stage N4):
/// trampolines by number of arguments, called for any compiled body, where
/// version 1 had one per island root. Version 3 (stage NO2 of
/// native-only.md): `flags`, where version 2 had `nests` (now
/// [`FLAG_NESTS`]). Version 4 (stage NO4): the trampolines into the entry,
/// the apply stubs and the loop, where version 3 had a list by number of
/// arguments.
pub const MANIFEST_VERSION: u64 = 4;

/// A [`Manifest`]'s `flags`: native frames may nest inside runs of the
/// machine (none since stage NO4, when native code runs only if every body
/// is compiled), so each counted frame may take more stack
/// (`native_abi::level_bound`).
pub const FLAG_NESTS: u64 = 1;
/// A [`Manifest`]'s `flags`: the code has the effect runtime's bodies,
/// which run eager resumptions (`native_abi::Context::resumes`).
pub const FLAG_RESUMES: u64 = 2;

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
    /// A bound on the stack one level of recursion of the code uses, in
    /// bytes, for the stack check behind the frame limit.
    pub max_frame: u64,
    /// What the code is like: [`FLAG_NESTS`] and [`FLAG_RESUMES`].
    pub flags: u64,
    /// The length of `functions`: the program's globals, or 0 with no code.
    pub n_globals: u64,
    /// The length of `lambdas`: the image's lambdas, or 0 with no code.
    pub n_lambdas: u64,
    /// For each global, its compiled code as a function value's, or null
    /// (`Context::functions`).
    pub functions: *const *const u8,
    /// For each lambda, its compiled code, or null (`Context::lambdas`).
    pub lambdas: *const *const u8,
    /// `native_abi::EnterTrampoline`, or null with no code.
    pub enter: *const u8,
    /// `native_abi::ApplyTrampoline`s, for one and two arguments.
    pub apply1: *const u8,
    pub apply2: *const u8,
    /// `native_abi::StepTrampoline`, or null if the code has no effect
    /// runtime.
    pub step: *const u8,
}

// SAFETY: a manifest is read-only data (the object's, for the process's
// life): its pointers are only read, from any thread.
#[allow(unsafe_code)]
unsafe impl Sync for Manifest {}

impl Manifest {
    pub const SIZE: usize = size_of::<Manifest>();
    pub const IMAGE_HASH_AT: usize = std::mem::offset_of!(Manifest, image_hash);
    pub const N_CACHES_AT: usize = std::mem::offset_of!(Manifest, n_caches);
    pub const MAX_FRAME_AT: usize = std::mem::offset_of!(Manifest, max_frame);
    pub const FLAGS_AT: usize = std::mem::offset_of!(Manifest, flags);
    pub const N_GLOBALS_AT: usize = std::mem::offset_of!(Manifest, n_globals);
    pub const N_LAMBDAS_AT: usize = std::mem::offset_of!(Manifest, n_lambdas);
    pub const FUNCTIONS_AT: usize = std::mem::offset_of!(Manifest, functions);
    pub const LAMBDAS_AT: usize = std::mem::offset_of!(Manifest, lambdas);
    pub const ENTER_AT: usize = std::mem::offset_of!(Manifest, enter);
    pub const APPLY1_AT: usize = std::mem::offset_of!(Manifest, apply1);
    pub const APPLY2_AT: usize = std::mem::offset_of!(Manifest, apply2);
    pub const STEP_AT: usize = std::mem::offset_of!(Manifest, step);

    /// The manifest's bytes with `magic` and `version` filled in and every
    /// other field 0 (no code, null pointers): what an object without
    /// native code holds, and what the compiler starts from.
    pub fn empty_bytes() -> Vec<u8> {
        let mut bytes = vec![0u8; Manifest::SIZE];
        bytes[..8].copy_from_slice(&MANIFEST_MAGIC.to_le_bytes());
        bytes[8..16].copy_from_slice(&MANIFEST_VERSION.to_le_bytes());
        bytes
    }

    /// The manifest's bytes for code compiled for an image of hash
    /// `image_hash`, with `n_caches` caches, frames of at most `max_frame`
    /// bytes with `flags` (`FLAG_NESTS` and the others), `n_globals`
    /// globals and `n_lambdas` lambdas; the pointers are 0, for relocations
    /// to fill.
    pub fn bytes(
        image_hash: u64,
        n_caches: u64,
        max_frame: u64,
        flags: u64,
        n_globals: u64,
        n_lambdas: u64,
    ) -> Vec<u8> {
        let mut bytes = Manifest::empty_bytes();
        for (at, value) in [
            (Manifest::IMAGE_HASH_AT, image_hash),
            (Manifest::N_CACHES_AT, n_caches),
            (Manifest::MAX_FRAME_AT, max_frame),
            (Manifest::FLAGS_AT, flags),
            (Manifest::N_GLOBALS_AT, n_globals),
            (Manifest::N_LAMBDAS_AT, n_lambdas),
        ] {
            bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
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
        assert_eq!(Manifest::SIZE, 112);
        assert_eq!(Manifest::ENTER_AT, 80);
        assert_eq!(Manifest::STEP_AT, 104);
        let bytes = Manifest::bytes(7, 1, 304, FLAG_NESTS, 2, 3);
        assert_eq!(&bytes[..8], b"swnative");
        assert_eq!(bytes[8], 4);
        assert_eq!(bytes[Manifest::IMAGE_HASH_AT], 7);
        assert_eq!(bytes[Manifest::FLAGS_AT], 1);
        assert_eq!(bytes[Manifest::N_LAMBDAS_AT], 3);
    }
}
