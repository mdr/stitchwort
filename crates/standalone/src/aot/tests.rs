//! The linked native code's manifest and tables (stage S5 of
//! docs/proposals/standalone-executables.md; stage NO6 of
//! docs/proposals/native-only.md): the runtime refuses, before any code
//! runs, a manifest of another version, one with no code, tables it can't
//! read (corrupt, or written by another build) and tables that don't match
//! the code. (Code that does run is tested end to end, linked, in
//! `crates/cli/tests/build.rs`.)

use super::{AotIslands, Mismatch};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::code;
use stitchwort_rt::native_abi::Context;
use stitchwort_rt::native_aot::{MANIFEST_MAGIC, MANIFEST_VERSION, Manifest};
use stitchwort_rt::value::Value;

const STACK: usize = 256 * 1024 * 1024;

const SOURCE: &str = "import Std (IO, Nat)\n\n\
                      def next (n: Nat): Nat := n + 1\n\n\
                      def main(): {IO} () := IO.print (Nat.toText (next 2))\n";

/// `source`'s tables and literals (`stitchwort_rt::linked`), and how many
/// globals and lambdas it has.
fn tables(source: &str) -> (Vec<u8>, usize, usize) {
    let mut session = Session::for_stack(STACK);
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("a `main`");
    let program = session.lower_fast(&main).expect("lowers");
    let image = code::compile(&program);
    let limits = stitchwort_rt::Limits::from_core(session.elab.limits);
    (
        stitchwort_rt::linked::encode(&program, &image, &limits),
        program.globals.len(),
        image.lambda_code.len(),
    )
}

/// The trampolines of the manifests here, which the tests never call.
extern "C" fn never(_: *mut Context, _: *mut Value) {
    unreachable!("a test called a trampoline")
}

/// A manifest whose trampolines are `never` (never called: the checks come
/// first), the apply trampolines at `apply`, with `tables` as its data, for
/// code compiled for `globals` globals and `lambdas` lambdas.
fn manifest(tables: &[u8], globals: usize, lambdas: usize, apply: *const u8) -> &'static Manifest {
    let enter = never as *const u8;
    let functions = Box::leak(vec![std::ptr::null::<u8>(); globals].into_boxed_slice());
    let lambda_table = Box::leak(vec![std::ptr::null::<u8>(); lambdas].into_boxed_slice());
    let data = Box::leak(tables.to_vec().into_boxed_slice());
    Box::leak(Box::new(Manifest {
        magic: MANIFEST_MAGIC,
        version: MANIFEST_VERSION,
        n_caches: 0,
        max_frame: 0,
        stack_size: 0,
        flags: 0,
        n_globals: globals as u64,
        n_lambdas: lambdas as u64,
        run: std::ptr::null(),
        data: data.as_ptr(),
        data_len: data.len() as u64,
        functions: functions.as_ptr(),
        lambdas: lambda_table.as_ptr(),
        enter,
        apply1: apply,
        apply2: apply,
        step: std::ptr::null(),
    }))
}

/// Whether the runtime takes `manifest`, or why not.
#[allow(unsafe_code)]
fn islands(manifest: &'static Manifest) -> Result<(), String> {
    // SAFETY: the manifest's tables and data are leaked, so they live
    // forever, and its trampolines are never called.
    match unsafe { AotIslands::read(manifest) } {
        Ok(_) => Ok(()),
        Err(Mismatch(why)) => Err(why),
    }
}

#[test]
fn matching_tables_are_taken_and_others_refused() {
    with_stack(STACK, || {
        let (bytes, globals, lambdas) = tables(SOURCE);
        assert_eq!(
            islands(manifest(&bytes, globals, lambdas, never as *const u8)),
            Ok(())
        );
        // Not with a trampoline missing.
        let missing = std::ptr::null();
        assert!(islands(manifest(&bytes, globals, lambdas, missing)).is_err());
        // Not for code compiled for another number of globals.
        let why = islands(manifest(&bytes, globals + 1, lambdas, never as *const u8))
            .expect_err("refused");
        assert!(
            why.starts_with("its native code was compiled for "),
            "{why}"
        );
        // Not tables that can't be read: truncated, or written by another
        // build of the runtime (the build hash follows the crate version).
        let why = islands(manifest(
            &bytes[..bytes.len() - 1],
            globals,
            lambdas,
            never as *const u8,
        ))
        .expect_err("refused");
        assert!(why.starts_with("its tables can't be read: "), "{why}");
        let version = env!("CARGO_PKG_VERSION");
        let at = bytes
            .windows(version.len())
            .position(|w| w == version.as_bytes())
            .expect("the version")
            + version.len();
        let mut other_build = bytes.clone();
        other_build[at] ^= 1;
        let why = islands(manifest(&other_build, globals, lambdas, never as *const u8))
            .expect_err("refused");
        assert!(why.contains("a different build of the runtime"), "{why}");
    });
}

#[test]
fn no_code_and_a_foreign_manifest_are_refused() {
    with_stack(STACK, || {
        // The bytes as words, so aligned as a manifest is, and leaked.
        #[allow(unsafe_code)]
        let read = |bytes: Vec<u8>| -> &'static Manifest {
            let words: Vec<u64> = bytes
                .chunks(8)
                .map(|word| u64::from_le_bytes(word.try_into().expect("a word")))
                .collect();
            let words = Box::leak(words.into_boxed_slice());
            // SAFETY: a manifest is its words in order, all of them plain
            // numbers or (here) null pointers.
            unsafe { &*words.as_ptr().cast::<Manifest>() }
        };
        let empty = Manifest::machine_bytes(0);
        let why = islands(read(empty.clone())).expect_err("refused");
        assert_eq!(why, "it has no native code");
        let mut foreign = empty;
        foreign[8] = 99;
        let why = islands(read(foreign)).expect_err("refused");
        assert!(why.contains("version 99"), "{why}");
    });
}
