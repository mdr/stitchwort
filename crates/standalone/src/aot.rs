//! The native code linked into a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): the counterpart of
//! `stitchwort_native::n1::Islands` for code `stitchwort build --native`
//! compiled into the object, described by its `sw_native_manifest`
//! (`stitchwort_rt::native_aot`).
//!
//! The run is `run --native`'s (the note's §3.3): the machine runs `main`'s
//! entry body and hands the island roots it calls to native code, through
//! the same crossing (`native_abi::Crossing`). The runtime builds the
//! tables the code reads (`TableStore`) from the image it rebuilt, after
//! checking that it is the image the code was compiled for.

use stitchwort_core::ResourceError;
use stitchwort_rt::code::Image;
use stitchwort_rt::ir::Program;
use stitchwort_rt::native_abi::{self as abi, NativeIslands, NativeRun, Trampoline};
use stitchwort_rt::native_aot::{MANIFEST_MAGIC, MANIFEST_VERSION, Manifest, image_hash};
use stitchwort_rt::value::Value;

struct Root {
    trampoline: Trampoline,
    checks_arguments: bool,
}

/// The linked islands of one program.
pub struct AotIslands {
    /// For each global: its trampoline, if it's an island root.
    roots: Vec<Option<Root>>,
    /// The code's tables and the crossing, shared with `run --native`.
    crossing: abi::Crossing,
}

/// Why linked native code can't run the program.
#[derive(Debug, PartialEq, Eq)]
pub struct Mismatch(pub String);

/// A slice of `len` items at `pointer`, which may be null when `len` is 0.
///
/// # Safety
/// Unless `len` is 0, `pointer` points at `len` items that live forever.
#[allow(unsafe_code)]
unsafe fn table<T>(pointer: *const T, len: u64) -> &'static [T] {
    if len == 0 || pointer.is_null() {
        &[]
    } else {
        // SAFETY: the caller's contract.
        unsafe { std::slice::from_raw_parts(pointer, len as usize) }
    }
}

impl AotIslands {
    /// The islands `manifest` describes, for `program` and its rebuilt
    /// `image`, running on a stack of `stack_size` bytes: `Ok(None)` if the
    /// executable has no native code (built without `--native`, or nothing
    /// fitted), and an error if the code was compiled for another image
    /// (never run it then: its numbering would be wrong).
    ///
    /// # Safety
    /// `manifest` is a manifest as the compiler writes it, whose tables
    /// and code live as long as the process: `sw_native_manifest`.
    #[allow(unsafe_code)]
    pub unsafe fn new(
        manifest: &'static Manifest,
        program: &Program,
        image: &Image,
        stack_size: usize,
    ) -> Result<Option<AotIslands>, Mismatch> {
        if manifest.magic != MANIFEST_MAGIC || manifest.version != MANIFEST_VERSION {
            return Err(Mismatch(format!(
                "its native code's manifest is version {} ({:#x}), where this runtime reads \
                 version {MANIFEST_VERSION}",
                manifest.version, manifest.magic
            )));
        }
        if manifest.n_roots == 0 {
            return Ok(None);
        }
        let hash = image_hash(image);
        if manifest.image_hash != hash {
            return Err(Mismatch(format!(
                "its native code was compiled for another program image (hash {:#018x}, where \
                 the program's is {hash:#018x})",
                manifest.image_hash
            )));
        }
        if manifest.n_globals != program.globals.len() as u64
            || manifest.n_lambdas != image.lambda_code.len() as u64
        {
            return Err(Mismatch(format!(
                "its native code was compiled for {} globals and {} lambdas, where the program \
                 has {} and {}",
                manifest.n_globals,
                manifest.n_lambdas,
                program.globals.len(),
                image.lambda_code.len()
            )));
        }
        if abi::probe_layout().is_err() {
            // The same check `run --native` makes: the layout native code
            // assumes doesn't hold, so the machine runs everything.
            return Ok(None);
        }
        // SAFETY: the manifest's tables are as long as it says, and live
        // as long as the process (the caller's contract).
        let (functions, lambdas, roots) = unsafe {
            (
                table(manifest.functions, manifest.n_globals),
                table(manifest.lambdas, manifest.n_lambdas),
                table(manifest.roots, manifest.n_roots),
            )
        };
        let mut by_global: Vec<Option<Root>> = (0..program.globals.len()).map(|_| None).collect();
        for root in roots {
            let Some(slot) = by_global.get_mut(root.global as usize) else {
                return Err(Mismatch(format!(
                    "its native code has a root for global {}, which the program doesn't have",
                    root.global
                )));
            };
            if root.trampoline.is_null() {
                return Err(Mismatch(format!(
                    "its native code's root for global {} has no trampoline",
                    root.global
                )));
            }
            *slot = Some(Root {
                // SAFETY: the compiler wrote a trampoline's address, whose
                // signature is `Trampoline`'s.
                trampoline: unsafe {
                    std::mem::transmute::<*const u8, Trampoline>(root.trampoline)
                },
                checks_arguments: root.checks_arguments != 0,
            });
        }
        Ok(Some(AotIslands {
            roots: by_global,
            crossing: abi::Crossing::new(
                program,
                functions.into(),
                lambdas.into(),
                abi::TableStore::new(program, image, manifest.n_caches as usize),
                Some(stack_size),
                manifest.max_frame as usize,
            ),
        }))
    }
}

impl NativeIslands for AotIslands {
    fn is_root(&self, g: u32) -> bool {
        self.roots.get(g as usize).is_some_and(Option::is_some)
    }

    fn accepts(&self, g: u32, args: &[&Value], frame_limit: u64) -> bool {
        // The executable has no `--verbose`, so a call left to the machine
        // needs no note.
        let root = self.roots[g as usize].as_ref().expect("a root");
        self.crossing
            .admits(root.checks_arguments, args, frame_limit)
            .is_ok()
    }

    #[allow(unsafe_code)]
    fn call(
        &self,
        g: u32,
        args: Vec<Value>,
        run: &mut NativeRun<'_>,
    ) -> Result<Value, ResourceError> {
        let root = self.roots[g as usize].as_ref().expect("a root");
        // SAFETY: the trampoline and the tables are those the manifest
        // describes, linked into this executable, for this image (checked
        // in `new`).
        unsafe { self.crossing.call(root.trampoline, args, run) }
    }

    fn release_unwound(&self) {
        self.crossing.release_unwound();
    }

    fn release_unwound_frames(&self) {
        self.crossing.release_unwound_frames();
    }
}

#[cfg(test)]
mod tests;
