//! The native code linked into a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): the counterpart of
//! `stitchwort_native::n1::Islands` for code `stitchwort build --native`
//! compiled into the object, described by its `sw_native_manifest`
//! (`stitchwort_rt::native_aot`).
//!
//! The run is `run --native`'s (the note's §3.3): the machine runs `main`'s
//! entry body and hands every compiled body it would push a frame for to
//! native code, through the same crossing (`native_abi::Crossing`); native
//! code has the machine (linked in with the rest of the runtime) run what
//! isn't compiled, effects and `Text.fold` (stage N4). The runtime builds
//! the tables the code reads (`TableStore`) from the image it rebuilt,
//! after checking that it is the image the code was compiled for.

use std::rc::Rc;

use stitchwort_core::ResourceError;
use stitchwort_rt::code::Image;
use stitchwort_rt::ir::Program;
use stitchwort_rt::native_abi::{self as abi, CrossingCode, NativeIslands, NativeRun, Trampoline};
use stitchwort_rt::native_aot::{
    FLAG_NESTS, FLAG_RESUMES, MANIFEST_MAGIC, MANIFEST_VERSION, Manifest, image_hash,
};
use stitchwort_rt::value::{Fun, Value};

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
        if manifest.n_trampolines == 0 {
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
        let (functions, lambdas, listed) = unsafe {
            (
                table(manifest.functions, manifest.n_globals),
                table(manifest.lambdas, manifest.n_lambdas),
                table(manifest.trampolines, manifest.n_trampolines),
            )
        };
        let mut trampolines: Vec<(u32, Trampoline)> = Vec::new();
        for listed in listed {
            if listed.trampoline.is_null() || listed.arity > u64::from(u16::MAX) {
                return Err(Mismatch(format!(
                    "its native code's trampoline for {} arguments is missing",
                    listed.arity
                )));
            }
            trampolines.push((
                listed.arity as u32,
                // SAFETY: the compiler wrote a trampoline's address, whose
                // signature is `Trampoline`'s.
                unsafe { std::mem::transmute::<*const u8, Trampoline>(listed.trampoline) },
            ));
        }
        Ok(Some(AotIslands {
            crossing: abi::Crossing::new(
                image,
                CrossingCode {
                    functions: functions.into(),
                    lambdas: lambdas.into(),
                    trampolines: &trampolines,
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
    fn compiled(&self, code: u32) -> bool {
        self.crossing.compiled(code)
    }

    fn fits(&self, frame_limit: u64) -> bool {
        // The executable has no `--verbose`, so a run left to the machine
        // needs no note.
        self.crossing.fits(frame_limit)
    }

    #[allow(unsafe_code)]
    fn call(
        &self,
        code: u32,
        env: Option<Rc<Fun>>,
        args: Vec<Value>,
        run: &mut NativeRun<'_>,
    ) -> Result<Value, ResourceError> {
        // SAFETY: the trampolines and the tables are those the manifest
        // describes, linked into this executable, for this image (checked
        // in `new`); the machine calls only compiled bodies.
        unsafe { self.crossing.call(code, env, args, run) }
    }
}

#[cfg(test)]
mod tests;
