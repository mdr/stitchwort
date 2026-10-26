//! What a standalone executable's object tells the runtime library that
//! links it (stage S5 of docs/proposals/standalone-executables.md; stage
//! NO6 of docs/proposals/native-only.md): `sw_native_manifest`, a
//! [`Manifest`].
//!
//! Every object `stitchwort build` writes defines one. It says which of the
//! library's two ways of running the executable takes (`run`), and gives
//! that way its data (`data`, `data_len`):
//! - **built with `--native`:** `sw_run_native`, and the tables and literals
//!   ([`crate::linked`]). The manifest also describes the compiled code: the
//!   trampolines from the runtime into it (the entry, the apply stubs and
//!   the effect runtime's loop), the code of each global and lambda as a
//!   function value's (`Context::functions` and `lambdas`), how many `Apply`
//!   caches the code numbers, its frames' bound, and the stack the build
//!   sized for them (stage NO5).
//! - **built without:** `sw_run_machine`, and the encoded program
//!   ([`crate::codec`]), which the machine runs; the code fields are 0.
//!
//! The library's C `main` calls `run` and refers to neither way itself, so
//! the linker, which drops what nothing reaches, keeps only the one the
//! object names: an executable built with `--native` has no machine,
//! bytecode compiler or codec in it (D1298, D1300).

/// `Manifest::magic`: "swnative", little-endian.
pub const MANIFEST_MAGIC: u64 = u64::from_le_bytes(*b"swnative");
/// `Manifest::version`: the layout of [`Manifest`]. Version 2 (stage N4):
/// trampolines by number of arguments, called for any compiled body, where
/// version 1 had one per island root. Version 3 (stage NO2 of
/// native-only.md): `flags`, where version 2 had `nests`. Version 4 (stage
/// NO4): the trampolines into the entry, the apply stubs and the loop,
/// where version 3 had a list by number of arguments. Version 5 (stage
/// NO5): `stack_size`, and no flag for frames that nest inside runs of the
/// machine (none do). Version 6 (stage NO6): `run`, `data` and `data_len`,
/// where version 5 had the image's hash (the executable has no image to
/// check against).
pub const MANIFEST_VERSION: u64 = 6;

/// A [`Manifest`]'s `flags`: the code has the effect runtime's bodies,
/// which run eager resumptions (`native_abi::Context::resumes`).
pub const FLAG_RESUMES: u64 = 1;

/// The library's way of running an executable built with `--native`, which
/// `run` names.
pub const RUN_NATIVE: &str = "sw_run_native";
/// The library's way of running an executable built without `--native`.
pub const RUN_MACHINE: &str = "sw_run_machine";

/// What [`Manifest::run`] points at: `sw_run_native` or `sw_run_machine`,
/// given the manifest, returning the exit status.
pub type RunExecutable = unsafe extern "C" fn(&'static Manifest) -> i32;

/// What `sw_native_manifest` holds. `repr(C)`, written by the compiler as
/// bytes at the offsets of its fields (with relocations for the pointers),
/// read by the runtime as this struct. Every field is a 64-bit word.
#[repr(C)]
pub struct Manifest {
    pub magic: u64,
    pub version: u64,
    /// How many `Apply` sites the code has (`Tables::n_caches`).
    pub n_caches: u64,
    /// A bound on the stack one level of recursion of the code uses, in
    /// bytes, for the stack check behind the frame limit.
    pub max_frame: u64,
    /// The stack the executable runs native code on, in bytes: as `build`
    /// sized it (`native_abi::native_stack`) for the frame limit.
    pub stack_size: u64,
    /// What the code is like: [`FLAG_RESUMES`].
    pub flags: u64,
    /// The length of `functions`: the program's globals, or 0 with no code.
    pub n_globals: u64,
    /// The length of `lambdas`: the image's lambdas, or 0 with no code.
    pub n_lambdas: u64,
    /// [`RunExecutable`]: how the library runs this executable.
    pub run: *const u8,
    /// `run`'s data: the tables, or the encoded program.
    pub data: *const u8,
    pub data_len: u64,
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
    pub const N_CACHES_AT: usize = std::mem::offset_of!(Manifest, n_caches);
    pub const MAX_FRAME_AT: usize = std::mem::offset_of!(Manifest, max_frame);
    pub const STACK_SIZE_AT: usize = std::mem::offset_of!(Manifest, stack_size);
    pub const FLAGS_AT: usize = std::mem::offset_of!(Manifest, flags);
    pub const N_GLOBALS_AT: usize = std::mem::offset_of!(Manifest, n_globals);
    pub const N_LAMBDAS_AT: usize = std::mem::offset_of!(Manifest, n_lambdas);
    pub const RUN_AT: usize = std::mem::offset_of!(Manifest, run);
    pub const DATA_AT: usize = std::mem::offset_of!(Manifest, data);
    pub const DATA_LEN_AT: usize = std::mem::offset_of!(Manifest, data_len);
    pub const FUNCTIONS_AT: usize = std::mem::offset_of!(Manifest, functions);
    pub const LAMBDAS_AT: usize = std::mem::offset_of!(Manifest, lambdas);
    pub const ENTER_AT: usize = std::mem::offset_of!(Manifest, enter);
    pub const APPLY1_AT: usize = std::mem::offset_of!(Manifest, apply1);
    pub const APPLY2_AT: usize = std::mem::offset_of!(Manifest, apply2);
    pub const STEP_AT: usize = std::mem::offset_of!(Manifest, step);

    /// The manifest's bytes with `magic`, `version` and `data_len` filled
    /// in and every other field 0 (no code, null pointers): an executable
    /// built without `--native`'s, before relocations fill `run` and
    /// `data`.
    pub fn machine_bytes(data_len: u64) -> Vec<u8> {
        Manifest::bytes(0, 0, 0, 0, 0, 0, data_len)
    }

    /// The manifest's bytes for code with `n_caches` caches, frames of at
    /// most `max_frame` bytes on a stack of `stack_size`, with `flags`
    /// ([`FLAG_RESUMES`]), `n_globals` globals and `n_lambdas` lambdas, and
    /// `data_len` bytes of data; the pointers are 0, for relocations to
    /// fill.
    #[allow(clippy::too_many_arguments)]
    pub fn bytes(
        n_caches: u64,
        max_frame: u64,
        stack_size: u64,
        flags: u64,
        n_globals: u64,
        n_lambdas: u64,
        data_len: u64,
    ) -> Vec<u8> {
        let mut bytes = vec![0u8; Manifest::SIZE];
        for (at, value) in [
            (0, MANIFEST_MAGIC),
            (8, MANIFEST_VERSION),
            (Manifest::N_CACHES_AT, n_caches),
            (Manifest::MAX_FRAME_AT, max_frame),
            (Manifest::STACK_SIZE_AT, stack_size),
            (Manifest::FLAGS_AT, flags),
            (Manifest::N_GLOBALS_AT, n_globals),
            (Manifest::N_LAMBDAS_AT, n_lambdas),
            (Manifest::DATA_LEN_AT, data_len),
        ] {
            bytes[at..at + 8].copy_from_slice(&value.to_le_bytes());
        }
        bytes
    }

    /// `data`, as a slice.
    ///
    /// # Safety
    /// `data` points at `data_len` bytes that live forever (or is null with
    /// `data_len` 0).
    #[allow(unsafe_code)]
    pub unsafe fn data(&'static self) -> &'static [u8] {
        if self.data.is_null() || self.data_len == 0 {
            &[]
        } else {
            // SAFETY: the caller's contract.
            unsafe { std::slice::from_raw_parts(self.data, self.data_len as usize) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_layout_is_words_in_order() {
        assert_eq!(Manifest::SIZE, 136);
        assert_eq!(Manifest::RUN_AT, 64);
        assert_eq!(Manifest::DATA_AT, 72);
        assert_eq!(Manifest::ENTER_AT, 104);
        assert_eq!(Manifest::STEP_AT, 128);
        let bytes = Manifest::bytes(1, 304, 9, FLAG_RESUMES, 2, 3, 77);
        assert_eq!(&bytes[..8], b"swnative");
        assert_eq!(bytes[8], 6);
        assert_eq!(bytes[Manifest::N_CACHES_AT], 1);
        assert_eq!(bytes[Manifest::STACK_SIZE_AT], 9);
        assert_eq!(bytes[Manifest::FLAGS_AT], 1);
        assert_eq!(bytes[Manifest::N_LAMBDAS_AT], 3);
        assert_eq!(bytes[Manifest::DATA_LEN_AT], 77);
        assert_eq!(Manifest::machine_bytes(5)[Manifest::DATA_LEN_AT], 5);
    }
}
