//! The linked native code's manifest (stage S5 of
//! docs/proposals/standalone-executables.md): the runtime refuses code
//! compiled for another image, before any of it runs, and runs everything
//! on the machine when there's none. (Code that does run is tested end to
//! end, linked, in `crates/cli/tests/build.rs`.)

use super::{AotIslands, Mismatch};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::Program;
use stitchwort_rt::code::{self, Image};
use stitchwort_rt::native_abi::Context;
use stitchwort_rt::native_aot::{
    MANIFEST_MAGIC, MANIFEST_VERSION, Manifest, ManifestRoot, image_hash,
};
use stitchwort_rt::value::Value;

const STACK: usize = 256 * 1024 * 1024;

const SOURCE: &str = "import Std (IO, Nat)\n\n\
                      def next (n: Nat): Nat := n + 1\n\n\
                      def main(): {IO} () := IO.print (Nat.toText (next 2))\n";

/// `source` checked, its `main` lowered, and the image compiled.
fn lowered(source: &str) -> (Program, Image) {
    let mut session = Session::for_stack(STACK);
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("a `main`");
    let program = session.lower_fast(&main).expect("lowers");
    let image = code::compile(&program);
    (program, image)
}

/// The trampoline of the manifests here, which the tests never call.
extern "C" fn never(_: *mut Context, _: *mut Value, _: *mut Value) {
    unreachable!("a test called a trampoline")
}

/// A manifest of one root, global `global`, whose trampoline is never
/// called (the checks come first), for an image of hash `hash`.
fn manifest(hash: u64, globals: usize, lambdas: usize, global: u64) -> &'static Manifest {
    let root = Box::leak(Box::new(ManifestRoot {
        global,
        checks_arguments: 0,
        trampoline: never as *const u8,
    }));
    let functions = Box::leak(vec![std::ptr::null::<u8>(); globals].into_boxed_slice());
    let lambda_table = Box::leak(vec![std::ptr::null::<u8>(); lambdas].into_boxed_slice());
    Box::leak(Box::new(Manifest {
        magic: MANIFEST_MAGIC,
        version: MANIFEST_VERSION,
        image_hash: hash,
        n_caches: 0,
        max_frame: 0,
        n_globals: globals as u64,
        n_lambdas: lambdas as u64,
        n_roots: 1,
        functions: functions.as_ptr(),
        lambdas: lambda_table.as_ptr(),
        roots: root,
    }))
}

/// Whether the runtime takes `manifest` for `program`: native code, none,
/// or why not.
#[allow(unsafe_code)]
fn islands(manifest: &'static Manifest, program: &Program, image: &Image) -> Result<bool, String> {
    // SAFETY: the manifest's tables are leaked, so they live forever, and
    // its trampoline is never called.
    match unsafe { AotIslands::new(manifest, program, image, STACK) } {
        Ok(islands) => Ok(islands.is_some()),
        Err(Mismatch(why)) => Err(why),
    }
}

#[test]
fn code_compiled_for_another_image_is_refused() {
    with_stack(STACK, || {
        let (program, image) = lowered(SOURCE);
        let hash = image_hash(&image);
        let globals = program.globals.len();
        let lambdas = image.lambda_code.len();
        let why = islands(manifest(hash ^ 1, globals, lambdas, 0), &program, &image)
            .expect_err("a mismatched hash is refused");
        assert!(
            why.starts_with("its native code was compiled for another program image"),
            "{why}"
        );

        // A program that differs only in a constant has another image.
        let (other, other_image) = lowered(&SOURCE.replace("n + 1", "n + 2"));
        assert_ne!(image_hash(&other_image), hash);
        assert!(islands(manifest(hash, globals, lambdas, 0), &other, &other_image).is_err());

        // The same program lowered again has the same image, and is taken.
        let (again, again_image) = lowered(SOURCE);
        assert_eq!(image_hash(&again_image), hash);
        assert_eq!(
            islands(manifest(hash, globals, lambdas, 0), &again, &again_image),
            Ok(true)
        );
        // But not with a root the program doesn't have.
        let past = globals as u64;
        assert!(islands(manifest(hash, globals, lambdas, past), &again, &again_image).is_err());
    });
}

#[test]
fn no_roots_is_no_native_code_and_a_foreign_manifest_is_refused() {
    with_stack(STACK, || {
        let (program, image) = lowered(SOURCE);
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
        let empty = Manifest::empty_bytes();
        assert_eq!(islands(read(empty.clone()), &program, &image), Ok(false));
        let mut foreign = empty;
        foreign[8] = 99;
        let why = islands(read(foreign), &program, &image).expect_err("refused");
        assert!(why.contains("version 99"), "{why}");
    });
}
