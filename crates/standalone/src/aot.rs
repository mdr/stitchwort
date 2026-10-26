//! The native code linked into a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): the counterpart of
//! `stitchwort_native::n1::Islands` for code `stitchwort build --native`
//! compiled into the object, described by its `sw_native_manifest`
//! (`stitchwort_rt::native_aot`).
//!
//! The run is `run --native`'s (the note's §3.3): the runner drives the
//! native code, entry and all, through the same executor and crossing
//! (`native_abi::NativeExecutor`, `Crossing`; stage NO4 of
//! native-only.md). Since stage NO6 there is no program, image or machine
//! here: the runtime builds the tables the code reads (`TableStore`) from
//! the tables and literals the object carries (`stitchwort_rt::linked`).

use stitchwort_rt::Limits;
use stitchwort_rt::linked::{self, LinkedTables, Outline};
use stitchwort_rt::native_abi::{
    self as abi, ApplyTrampoline, CrossingCode, EnterTrampoline, NativeIslands, StepTrampoline,
};
use stitchwort_rt::native_aot::{FLAG_RESUMES, MANIFEST_MAGIC, MANIFEST_VERSION, Manifest};

/// The linked native code of one program, and the tables it reads.
pub struct AotIslands {
    /// The code's tables and the crossing, shared with `run --native`;
    /// dropped before the tables it points into.
    crossing: abi::Crossing,
    _tables: LinkedTables,
}

/// What [`AotIslands::read`] reads from the object: the code, what the
/// runtime needs to know of the program, and the limits it runs under.
pub struct Linked {
    pub islands: AotIslands,
    pub outline: Outline,
    pub limits: Limits,
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

/// Whether `manifest` is one this runtime reads: the magic and version.
pub fn check_version(manifest: &Manifest) -> Result<(), Mismatch> {
    if manifest.magic != MANIFEST_MAGIC || manifest.version != MANIFEST_VERSION {
        return Err(Mismatch(format!(
            "its native code's manifest is version {} ({:#x}), where this runtime reads \
             version {MANIFEST_VERSION}",
            manifest.version, manifest.magic
        )));
    }
    Ok(())
}

impl AotIslands {
    /// The code `manifest` describes, with its tables and literals read,
    /// or an error if the code can't run: a manifest of another version,
    /// no code, tables that can't be read (written by another build, say:
    /// the code's numbering is that build's) or that don't match the code,
    /// or a layout of values this runtime doesn't have
    /// (`abi::probe_layout`). The stack it runs on is the manifest's
    /// `stack_size`, which the caller reserved.
    ///
    /// # Safety
    /// `manifest` is a manifest as the compiler writes it, whose tables,
    /// data and code live as long as the process: `sw_native_manifest`.
    #[allow(unsafe_code)]
    pub unsafe fn read(manifest: &'static Manifest) -> Result<Linked, Mismatch> {
        check_version(manifest)?;
        if manifest.enter.is_null() {
            return Err(Mismatch("it has no native code".to_string()));
        }
        // SAFETY: the caller's contract.
        let bytes = unsafe { manifest.data() };
        let linked::Linked {
            outline,
            tables,
            limits,
        } = linked::decode(bytes)
            .map_err(|e| Mismatch(format!("its tables can't be read: {}", e.0)))?;
        let n_globals = outline.globals.len() as u64;
        let n_lambdas = outline.lambda_params.len() as u64;
        if manifest.n_globals != n_globals || manifest.n_lambdas != n_lambdas {
            return Err(Mismatch(format!(
                "its native code was compiled for {} globals and {} lambdas, where its tables \
                 have {n_globals} and {n_lambdas}",
                manifest.n_globals, manifest.n_lambdas,
            )));
        }
        // The same check `build --native` made (stage NO5 of
        // native-only.md): the layout native code assumes must hold here too.
        abi::probe_layout().map_err(Mismatch)?;
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
        // The tables point into `tables`' boxes, which don't move when the
        // islands do, and are dropped after the crossing.
        let store = abi::TableStore::from_parts(
            &tables.shapes,
            &tables.pool,
            &tables.num_tables,
            tables.ops.clone(),
            manifest.n_caches as usize,
        );
        let islands = AotIslands {
            crossing: abi::Crossing::new(
                CrossingCode {
                    functions: functions.into(),
                    lambdas: lambdas.into(),
                    enter,
                    apply,
                    step,
                    max_frame: manifest.max_frame as usize,
                    resumes: manifest.flags & FLAG_RESUMES != 0,
                },
                store,
            ),
            _tables: tables,
        };
        Ok(Linked {
            islands,
            outline,
            limits,
        })
    }
}

impl NativeIslands for AotIslands {
    fn crossing(&self) -> &abi::Crossing {
        // The tables and trampolines the manifest describes, linked into
        // this executable, with the tables read from it.
        &self.crossing
    }
}

#[cfg(test)]
mod tests;
