//! The native code linked into a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): the counterpart of
//! `stitchwort_native::n1::Islands` for code `stitchwort build --native`
//! compiled into the object, described by its `sw_native_manifest`
//! (`stitchwort_rt::native_aot`).
//!
//! The run is `run --native`'s (the note's §3.3): the runner drives the
//! native code, entry and all, through the same executor and crossing
//! (`native_abi::NativeExecutor`, `Crossing`; stage NO4 of
//! native-only.md), with no part on the machine. The runtime builds
//! the tables the code reads (`TableStore`) from the image it rebuilt,
//! after checking that it is the image the code was compiled for.

use stitchwort_rt::code::Image;
use stitchwort_rt::ir::Program;
use stitchwort_rt::native_abi::{
    self as abi, ApplyTrampoline, CrossingCode, EnterTrampoline, NativeIslands, StepTrampoline,
};
use stitchwort_rt::native_aot::{
    FLAG_NESTS, FLAG_RESUMES, MANIFEST_MAGIC, MANIFEST_VERSION, Manifest, image_hash,
};

/// The linked native code of one program.
pub struct AotIslands {
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
    /// The code `manifest` describes, for `program` and its rebuilt
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
        if manifest.enter.is_null() {
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
        let (functions, lambdas) = unsafe {
            (
                table(manifest.functions, manifest.n_globals),
                table(manifest.lambdas, manifest.n_lambdas),
            )
        };
        if manifest.apply1.is_null() || manifest.apply2.is_null() {
            return Err(Mismatch(
                "its native code's apply trampolines are missing".to_string(),
            ));
        }
        // SAFETY: the compiler wrote each trampoline's address, whose
        // signature is its type's (`n1::Trampoline`).
        let (enter, apply, step) = unsafe {
            (
                std::mem::transmute::<*const u8, EnterTrampoline>(manifest.enter),
                [
                    std::mem::transmute::<*const u8, ApplyTrampoline>(manifest.apply1),
                    std::mem::transmute::<*const u8, ApplyTrampoline>(manifest.apply2),
                ],
                (!manifest.step.is_null())
                    .then(|| std::mem::transmute::<*const u8, StepTrampoline>(manifest.step)),
            )
        };
        Ok(Some(AotIslands {
            crossing: abi::Crossing::new(
                CrossingCode {
                    functions: functions.into(),
                    lambdas: lambdas.into(),
                    enter,
                    apply,
                    step,
                    max_frame: manifest.max_frame as usize,
                    nests: manifest.flags & FLAG_NESTS != 0,
                    resumes: manifest.flags & FLAG_RESUMES != 0,
                },
                abi::TableStore::new(program, image, manifest.n_caches as usize),
                Some(stack_size),
            ),
        }))
    }
}

impl NativeIslands for AotIslands {
    fn fits(&self, frame_limit: u64) -> bool {
        // The executable has no `--verbose`, so a run left to the machine
        // needs no note.
        self.crossing.fits(frame_limit)
    }

    fn crossing(&self) -> &abi::Crossing {
        // The tables and trampolines the manifest describes, linked into
        // this executable, for this image (checked in `new`).
        &self.crossing
    }
}

#[cfg(test)]
mod tests;
