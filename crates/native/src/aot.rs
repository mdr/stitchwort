//! Native code in an object file, for a standalone executable (stage S5 of
//! docs/proposals/standalone-executables.md): `stitchwort build --native`.
//!
//! The code is [`crate::n1`]'s, made by the same generator (`n1::emit`)
//! into a `cranelift-object` module instead of the JIT, as
//! position-independent code (§1.2: macOS can't relocate absolute addresses
//! in the code): every body `main` reaches but its entry (stage N4). The
//! code holds no host address (stage S4): what it needs of the runtime's
//! memory it reaches through `Context::tables`, which the runtime builds
//! from the image it rebuilds, and the helpers (`sw_ctor` and the rest,
//! with N4's `sw_effect`, `sw_perform` and the others that run
//! the machine for native code) are left for the linker to resolve against
//! the runtime library, which has the machine.
//!
//! The object describes the code to the runtime in data
//! (`stitchwort_rt::native_aot`):
//! - `sw_functions`: for each global, its code as a function value's (its
//!   adapter, `value{g}`), or null: `Context::functions`;
//! - `sw_lambdas`: for each lambda, its body, or null: `Context::lambdas`;
//! - `sw_trampolines`: the crossing's trampolines, by number of arguments
//!   (also exported as `sw_cross_<number>`);
//! - `sw_native_manifest`, the one the runtime looks up: the image's hash,
//!   the cache count, the frames' bound and whether they nest, the counts of
//!   the three tables and pointers to them.
//!
//! The pointers are data relocations, which the loader fills in.

use std::time::{Duration, Instant};

use cranelift_module::{DataDescription, DataId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule, object};
use stitchwort_rt::code::Image;
use stitchwort_rt::ir::Program;
use stitchwort_rt::native_abi as abi;
use stitchwort_rt::native_aot::{
    FLAG_NESTS, FLAG_RESUMES, Manifest, ManifestTrampoline, image_hash,
};

use crate::n1::{self, Audit, Emitted, Options};

/// A program's bodies, compiled into an object.
pub struct ObjectCode {
    /// The object: the code and its manifest. The caller adds the program
    /// (`sw_program`) and writes it.
    pub object: object::write::Object<'static>,
    /// How many bodies were compiled, of how many `main` reaches (its entry
    /// included), and in what time.
    pub bodies: usize,
    pub reachable: usize,
    pub compile_time: Duration,
    /// A bound on the stack the widest body uses.
    pub max_frame: usize,
    /// Why any body `main` reaches isn't compiled.
    pub notes: Vec<String>,
}

impl ObjectCode {
    /// What `build --native --verbose` says: the notes, then what compiled.
    pub fn report(&self) -> Vec<String> {
        let mut report = self.notes.clone();
        report.push(format!(
            "native: compiled {} of the {} bodies `main` reaches (frames of at most {} bytes, in {:.1} ms)",
            self.bodies,
            self.reachable,
            self.max_frame,
            self.compile_time.as_secs_f64() * 1000.0
        ));
        report
    }
}

/// Compiles the bodies `program`'s entry reaches (`image` is its compiled
/// image, which the runtime will rebuild) into an object for this machine,
/// or says why the whole run stays on the machine. `options.stack_size`
/// should be the stack the executable runs native code on.
pub fn compile_object(
    program: &Program,
    image: &Image,
    options: Options,
) -> Result<ObjectCode, Vec<String>> {
    abi::probe_layout().map_err(|e| vec![format!("native: {e}")])?;
    let plan = n1::plan(program, image)?;
    let start = Instant::now();
    let fail = |e: String| vec![format!("native: compiling failed: {e}")];
    let isa = n1::host_isa(true).map_err(fail)?;
    let builder = ObjectBuilder::new(isa, "program", default_libcall_names())
        .map_err(|e| fail(e.to_string()))?;
    let mut module = ObjectModule::new(builder);
    let dump = std::env::var_os("STITCHWORT_NATIVE_DUMP").is_some();
    let mut audit = Audit::new(program, image, false);
    let Emitted {
        functions,
        adapters,
        lambda_of,
        trampolines,
        n_caches,
        max_frame,
    } = n1::emit(
        &mut module,
        program,
        image,
        &plan,
        options,
        dump,
        &mut audit,
        true,
    )?;

    let n_globals = program.globals.len();
    let n_lambdas = image.lambda_code.len();
    let mut table = |name: &str,
                     len: usize,
                     entries: &mut dyn Iterator<Item = (usize, cranelift_module::FuncId)>|
     -> Result<Option<DataId>, Vec<String>> {
        if len == 0 {
            return Ok(None);
        }
        let id = module
            .declare_data(name, Linkage::Local, false, false)
            .map_err(|e| fail(e.to_string()))?;
        let mut data = DataDescription::new();
        data.define(vec![0u8; len * 8].into_boxed_slice());
        data.set_align(8);
        for (i, function) in entries {
            let function = module.declare_func_in_data(function, &mut data);
            data.write_function_addr((i * 8) as u32, function);
        }
        module
            .define_data(id, &data)
            .map_err(|e| fail(e.to_string()))?;
        Ok(Some(id))
    };
    let functions_table = table(
        "sw_functions",
        n_globals,
        &mut adapters.iter().map(|(&g, &(id, _))| (g as usize, id)),
    )?;
    let lambdas_table = table(
        "sw_lambdas",
        n_lambdas,
        &mut lambda_of
            .iter()
            .map(|(code, &l)| (l as usize, functions[code])),
    )?;

    let trampolines_id = module
        .declare_data("sw_trampolines", Linkage::Local, false, false)
        .map_err(|e| fail(e.to_string()))?;
    let mut data = DataDescription::new();
    let mut bytes = Vec::new();
    for &(arity, _) in &trampolines {
        bytes.extend(ManifestTrampoline::bytes(arity));
    }
    data.define(bytes.into_boxed_slice());
    data.set_align(8);
    for (i, &(_, id)) in trampolines.iter().enumerate() {
        let function = module.declare_func_in_data(id, &mut data);
        data.write_function_addr(
            (i * ManifestTrampoline::SIZE + ManifestTrampoline::TRAMPOLINE_AT) as u32,
            function,
        );
    }
    module
        .define_data(trampolines_id, &data)
        .map_err(|e| fail(e.to_string()))?;

    let manifest_id = module
        .declare_data("sw_native_manifest", Linkage::Export, false, false)
        .map_err(|e| fail(e.to_string()))?;
    let mut manifest = DataDescription::new();
    manifest.define(
        Manifest::bytes(
            image_hash(image),
            n_caches as u64,
            max_frame as u64,
            if plan.nests { FLAG_NESTS } else { 0 } | if plan.effects { FLAG_RESUMES } else { 0 },
            if functions_table.is_some() {
                n_globals as u64
            } else {
                0
            },
            if lambdas_table.is_some() {
                n_lambdas as u64
            } else {
                0
            },
            trampolines.len() as u64,
        )
        .into_boxed_slice(),
    );
    manifest.set_align(8);
    for (at, data) in [
        (Manifest::FUNCTIONS_AT, functions_table),
        (Manifest::LAMBDAS_AT, lambdas_table),
        (Manifest::TRAMPOLINES_AT, Some(trampolines_id)),
    ] {
        if let Some(data) = data {
            let value = module.declare_data_in_data(data, &mut manifest);
            manifest.write_data_addr(at as u32, value, 0);
        }
    }
    module
        .define_data(manifest_id, &manifest)
        .map_err(|e| fail(e.to_string()))?;

    let product = module.finish();
    Ok(ObjectCode {
        object: product.object,
        bodies: plan.bodies.len(),
        reachable: plan.reachable,
        compile_time: start.elapsed(),
        max_frame,
        notes: plan.notes,
    })
}
