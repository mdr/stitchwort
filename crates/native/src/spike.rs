//! Stage N0 of docs/proposals/native-compilation.md: a Cranelift spike.
//!
//! Hand-built functions, JIT-compiled in-process, that exercise what the
//! native backend will need and nothing of the language yet:
//! - a call from native code back into a Rust `extern "C"` runtime function;
//! - a step counter and a frame counter in a context struct, checked on every
//!   call, leaving on a cold path with an error code when over a limit;
//! - a self tail call compiled as a loop;
//! - mutual tail calls through Cranelift's `tail` calling convention and
//!   `return_call`;
//! - deep non-tail recursion on a thread with a large reserved stack.
//!
//! The counting rules are the machine's (`crates/rt/src/machine.rs`): every
//! function entered is a step, and a frame is pending for each non-tail call
//! that hasn't returned. So here the caller of a non-tail call counts the
//! frame (one more before the call, one fewer after it), and a tail call
//! counts no frame.

use std::time::{Duration, Instant};

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, FuncRef, InstBuilder, MemFlagsData, Value, types};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::{Context as CodegenContext, ir};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module, default_libcall_names};

/// No error: the function returned normally.
pub const OK: u64 = 0;
/// More steps than `Context::step_limit`.
pub const OUT_OF_STEPS: u64 = 1;
/// More frames pending than `Context::frame_limit`.
pub const OUT_OF_FRAMES: u64 = 2;

/// The state native code shares with the runtime, passed by pointer as every
/// function's first argument. `repr(C)` because the generated code reads and
/// writes its fields at fixed offsets (the `*_AT` constants below).
#[repr(C)]
#[derive(Debug, Clone)]
pub struct Context {
    pub steps: u64,
    pub step_limit: u64,
    pub frames: u64,
    pub frame_limit: u64,
    /// `OK`, or why the run stopped. Set on a cold path; once set, each
    /// function returns at once without doing more work.
    pub error: u64,
    /// How many times native code called back into `note_step`.
    pub callbacks: u64,
    /// The lowest stack address `note_step` has seen, to measure the native
    /// stack the generated code uses.
    pub lowest_stack: u64,
}

const STEPS_AT: i32 = 0;
const STEP_LIMIT_AT: i32 = 8;
const FRAMES_AT: i32 = 16;
const FRAME_LIMIT_AT: i32 = 24;
const ERROR_AT: i32 = 32;

impl Context {
    pub fn new(step_limit: u64, frame_limit: u64) -> Self {
        Context {
            steps: 0,
            step_limit,
            frames: 0,
            frame_limit,
            error: OK,
            callbacks: 0,
            lowest_stack: u64::MAX,
        }
    }

    /// No limits: for measuring, and for code built without counting.
    pub fn unlimited() -> Self {
        Self::new(u64::MAX, u64::MAX)
    }
}

/// The runtime function the generated code calls on each step: counts the
/// call, notes how deep the native stack is, and gives back `n` (so the
/// functions compute ordinary sums and the result checks every call
/// happened).
extern "C" fn note_step(context: *mut Context, n: i64) -> i64 {
    // The address of a local is (within a frame) the stack pointer.
    let marker = 0u8;
    let here = std::hint::black_box(&marker) as *const u8 as u64;
    note_step_in(context, here);
    n
}

#[allow(unsafe_code)]
fn note_step_in(context: *mut Context, here: u64) {
    // SAFETY: native code passes the pointer it was given, which the caller
    // in this module made from a `&mut Context` that outlives the call, and
    // nothing else touches the context while native code runs.
    let context = unsafe { &mut *context };
    context.callbacks += 1;
    context.lowest_stack = context.lowest_stack.min(here);
}

/// A compiled function of a context and one or two integers.
type Unary = extern "C" fn(*mut Context, i64) -> i64;
type Binary = extern "C" fn(*mut Context, i64, i64) -> i64;

/// How the `sum` functions are built, for comparing what counting and the
/// call into Rust cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Variant {
    /// Count steps and frames and check them on every call.
    pub counting: bool,
    /// Call `note_step` on every step.
    pub callback: bool,
}

pub const VARIANTS: [Variant; 4] = [
    Variant {
        counting: false,
        callback: false,
    },
    Variant {
        counting: true,
        callback: false,
    },
    Variant {
        counting: false,
        callback: true,
    },
    Variant {
        counting: true,
        callback: true,
    },
];

/// The compiled spike: the JIT module (which owns the code memory) and the
/// entry points.
pub struct Spike {
    /// The module; dropping it leaks the code memory rather than freeing it
    /// (so `code` stays valid), which is fine for a spike.
    _module: JITModule,
    /// The entry points, which other threads may call while this lives.
    pub code: Code,
    /// How long each function took to compile, and the whole module.
    pub compile_times: Vec<(String, Duration)>,
    pub total_compile_time: Duration,
}

/// Where compiled code goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodeMemory {
    /// cranelift-jit's own provider: an anonymous mapping, `mprotect`ed to
    /// read+execute.
    System,
    /// `MAP_JIT` memory (`crate::map_jit`), as Apple asks of JITs.
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    MapJit,
}

impl Default for CodeMemory {
    /// `MapJit` on macOS on Apple Silicon, which works however the binary
    /// is signed, as long as JIT code is allowed at all; `System` elsewhere.
    fn default() -> Self {
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        return CodeMemory::MapJit;
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        return CodeMemory::System;
    }
}

impl std::str::FromStr for CodeMemory {
    type Err = String;

    fn from_str(text: &str) -> Result<Self, String> {
        match text {
            "system" => Ok(CodeMemory::System),
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            "map-jit" => Ok(CodeMemory::MapJit),
            _ => Err(format!("`{text}` isn't a kind of code memory here")),
        }
    }
}

/// Which parts of the target the spike runs on, for the report.
pub fn target_description() -> String {
    format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS)
}

/// The compiled entry points. Plain function pointers, so they can be called
/// from any thread (each with its own `Context`); the code they point to is
/// never unmapped (see `unary`).
#[derive(Clone, Copy)]
pub struct Code {
    /// `sum(n) = n + sum(n - 1)`, non-tail, one per `VARIANTS` entry.
    sums: [Unary; 4],
    /// `count_loop(n, acc)`: a self tail call, compiled as a loop.
    count_loop: Binary,
    /// `run_even(n)`: enters `even`/`odd`, which tail-call each other.
    run_even: Unary,
}

impl Spike {
    /// JIT-compiles every function of the spike into the platform's default
    /// code memory (`CodeMemory::default`).
    pub fn compile() -> Result<Spike, String> {
        Self::compile_into(CodeMemory::default())
    }

    /// JIT-compiles every function of the spike into `memory`.
    pub fn compile_into(memory: CodeMemory) -> Result<Spike, String> {
        let start = Instant::now();
        let mut flags = settings::builder();
        flags.set("opt_level", "speed").map_err(|e| e.to_string())?;
        // The JIT patches absolute addresses; position-independent code is
        // for object files.
        flags.set("is_pic", "false").map_err(|e| e.to_string())?;
        // On x86-64, Cranelift 0.136's `return_call` panics without frame
        // pointers ("the current implementation relies on them being
        // present", isa/x64/inst/emit.rs); found running this spike on
        // x86-64 Linux. They also let profilers walk JIT frames.
        flags
            .set("preserve_frame_pointers", "true")
            .map_err(|e| e.to_string())?;
        let isa = cranelift_native::builder()
            .map_err(|e| format!("this machine isn't supported: {e}"))?
            .finish(settings::Flags::new(flags))
            .map_err(|e| e.to_string())?;
        let mut builder = JITBuilder::with_isa(isa, default_libcall_names());
        builder.symbol("note_step", note_step as *const u8);
        match memory {
            CodeMemory::System => {}
            #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
            CodeMemory::MapJit => {
                let provider =
                    crate::map_jit::MapJitMemoryProvider::new().map_err(|e| e.to_string())?;
                builder.memory_provider(Box::new(provider));
            }
        }
        let mut module = JITModule::new(builder);
        let mut compiler = Compiler::new(&mut module);
        let mut compile_times = Vec::new();

        let mut sum_ids = [FuncId::from_u32(0); 4];
        for (index, variant) in VARIANTS.into_iter().enumerate() {
            let name = format!(
                "sum{}{}",
                if variant.counting { "_counting" } else { "" },
                if variant.callback { "_callback" } else { "" }
            );
            let time = Instant::now();
            sum_ids[index] = compiler.sum(&name, variant)?;
            compile_times.push((name, time.elapsed()));
        }
        let time = Instant::now();
        let count_loop_id = compiler.count_loop()?;
        compile_times.push(("count_loop".to_string(), time.elapsed()));
        let time = Instant::now();
        let run_even_id = compiler.even_and_odd()?;
        compile_times.push(("run_even + even + odd".to_string(), time.elapsed()));

        let time = Instant::now();
        module
            .finalize_definitions()
            .map_err(|e| format!("finalizing: {e}"))?;
        compile_times.push((
            "finalize (link, map executable)".to_string(),
            time.elapsed(),
        ));

        let sums = sum_ids.map(|id| unary(module.get_finalized_function(id)));
        let count_loop = binary(module.get_finalized_function(count_loop_id));
        let run_even = unary(module.get_finalized_function(run_even_id));
        Ok(Spike {
            _module: module,
            code: Code {
                sums,
                count_loop,
                run_even,
            },
            compile_times,
            total_compile_time: start.elapsed(),
        })
    }
}

impl Code {
    /// `n + (n - 1) + … + 1` by non-tail recursion, `n + 1` calls deep.
    pub fn sum(&self, variant: Variant, context: &mut Context, n: i64) -> i64 {
        let index = VARIANTS.iter().position(|&v| v == variant).unwrap();
        (self.sums[index])(context, n)
    }

    /// `acc + n + (n - 1) + … + 1` by a self tail call: a loop.
    pub fn count_loop(&self, context: &mut Context, n: i64, acc: i64) -> i64 {
        (self.count_loop)(context, n, acc)
    }

    /// `n + (n - 1) + … + 1` by `even` and `odd` tail-calling each other.
    pub fn even_odd(&self, context: &mut Context, n: i64) -> i64 {
        (self.run_even)(context, n)
    }
}

/// The code at `pointer` as a function of a context and an integer.
#[allow(unsafe_code)]
fn unary(pointer: *const u8) -> Unary {
    // SAFETY: `pointer` is a function `Compiler` finished with the host's
    // default calling convention (the C one) and the signature
    // `(pointer, i64) -> i64`, which is `Unary`'s. The code stays mapped for
    // the life of the process: neither cranelift-jit's memory provider nor
    // `MapJitMemoryProvider` unmaps code when the module is dropped, and
    // nothing here calls `JITModule::free_memory`.
    unsafe { std::mem::transmute::<*const u8, Unary>(pointer) }
}

/// The code at `pointer` as a function of a context and two integers.
#[allow(unsafe_code)]
fn binary(pointer: *const u8) -> Binary {
    // SAFETY: as for `unary`, with the signature `(pointer, i64, i64) -> i64`.
    unsafe { std::mem::transmute::<*const u8, Binary>(pointer) }
}

/// Builds the functions into a module.
struct Compiler<'m> {
    module: &'m mut JITModule,
    context: CodegenContext,
    builder_context: FunctionBuilderContext,
    pointer: ir::Type,
    note_step: FuncId,
}

impl<'m> Compiler<'m> {
    fn new(module: &'m mut JITModule) -> Self {
        let pointer = module.target_config().pointer_type();
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(pointer));
        signature.params.push(AbiParam::new(types::I64));
        signature.returns.push(AbiParam::new(types::I64));
        let note_step = module
            .declare_function("note_step", Linkage::Import, &signature)
            .expect("declaring note_step");
        Compiler {
            context: module.make_context(),
            builder_context: FunctionBuilderContext::new(),
            module,
            pointer,
            note_step,
        }
    }

    /// `(context, i64 × arity) -> i64` in the given calling convention.
    fn signature(&self, arity: usize, call_conv: CallConv) -> ir::Signature {
        let mut signature = ir::Signature::new(call_conv);
        signature.params.push(AbiParam::new(self.pointer));
        for _ in 0..arity {
            signature.params.push(AbiParam::new(types::I64));
        }
        signature.returns.push(AbiParam::new(types::I64));
        signature
    }

    fn default_call_conv(&self) -> CallConv {
        self.module.isa().default_call_conv()
    }

    /// Compiles the function `id` whose body `body` builds.
    fn define(
        &mut self,
        id: FuncId,
        signature: ir::Signature,
        body: impl FnOnce(&mut FunctionBuilder, &mut Refs),
    ) -> Result<(), String> {
        self.context.func.signature = signature;
        self.context.func.name = ir::UserFuncName::user(0, id.as_u32());
        let mut refs = Refs {
            functions: Vec::new(),
        };
        {
            let mut builder =
                FunctionBuilder::new(&mut self.context.func, &mut self.builder_context);
            // Every function may call `note_step`; refs.functions[0] is it.
            let note = self
                .module
                .declare_func_in_func(self.note_step, builder.func);
            refs.functions.push(note);
            body(&mut builder, &mut refs);
            builder.seal_all_blocks();
            builder.finalize(self.module.target_config());
        }
        self.module
            .define_function(id, &mut self.context)
            .map_err(|e| format!("compiling: {e:?}"))?;
        self.module.clear_context(&mut self.context);
        Ok(())
    }

    /// `sum(context, n)`: `if n == 0 { 0 } else { note(n) + sum(n - 1) }`,
    /// with the recursive call not in tail position.
    fn sum(&mut self, name: &str, variant: Variant) -> Result<FuncId, String> {
        let signature = self.signature(1, self.default_call_conv());
        let id = self
            .module
            .declare_function(name, Linkage::Local, &signature)
            .map_err(|e| e.to_string())?;
        let self_ref = self.module.declare_func_in_func(id, &mut self.context.func);
        self.define(id, signature, |b, refs| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let context = b.block_params(entry)[0];
            let n = b.block_params(entry)[1];
            if variant.counting {
                refs.count_step(b, context);
            }
            let base = b.create_block();
            let recurse = b.create_block();
            b.ins().brif(n, recurse, &[], base, &[]);

            b.switch_to_block(base);
            let zero = b.ins().iconst(types::I64, 0);
            b.ins().return_(&[zero]);

            b.switch_to_block(recurse);
            let smaller = b.ins().iadd_imm_s(n, -1);
            if variant.counting {
                refs.push_frame(b, context);
            }
            let call = b.ins().call(self_ref, &[context, smaller]);
            let rest = b.inst_results(call)[0];
            if variant.counting {
                // Leave at once if the callee ran out, leaving the counters
                // as they were where it ran out.
                refs.return_if_failed(b, context);
                refs.pop_frame(b, context);
            }
            let here = if variant.callback {
                let note = refs.functions[0];
                let call = b.ins().call(note, &[context, n]);
                b.inst_results(call)[0]
            } else {
                n
            };
            let total = b.ins().iadd(here, rest);
            b.ins().return_(&[total]);
        })?;
        Ok(id)
    }

    /// `count_loop(context, n, acc)`:
    /// `if n == 0 { acc } else { count_loop(n - 1, acc + note(n)) }`, where
    /// the self tail call becomes a jump back to the top.
    fn count_loop(&mut self) -> Result<FuncId, String> {
        let signature = self.signature(2, self.default_call_conv());
        let id = self
            .module
            .declare_function("count_loop", Linkage::Local, &signature)
            .map_err(|e| e.to_string())?;
        self.define(id, signature, |b, refs| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let context = b.block_params(entry)[0];
            let n = b.block_params(entry)[1];
            let acc = b.block_params(entry)[2];
            // The loop's header stands for entering the function again.
            let top = b.create_block();
            b.append_block_param(top, types::I64);
            b.append_block_param(top, types::I64);
            b.ins().jump(top, &[n.into(), acc.into()]);

            b.switch_to_block(top);
            let n = b.block_params(top)[0];
            let acc = b.block_params(top)[1];
            refs.count_step(b, context);
            let done = b.create_block();
            let again = b.create_block();
            b.ins().brif(n, again, &[], done, &[]);

            b.switch_to_block(done);
            b.ins().return_(&[acc]);

            b.switch_to_block(again);
            let note = refs.functions[0];
            let call = b.ins().call(note, &[context, n]);
            let here = b.inst_results(call)[0];
            let acc = b.ins().iadd(acc, here);
            let n = b.ins().iadd_imm_s(n, -1);
            b.ins().jump(top, &[n.into(), acc.into()]);
        })?;
        Ok(id)
    }

    /// `even(context, n, acc)` and `odd(context, n, acc)`, in the `tail`
    /// calling convention: each counts a step, adds `note(n)` and
    /// `return_call`s the other on `n - 1`, until `n` is 0. `run_even`, in
    /// the host's convention, is how Rust enters them: a non-tail call, so
    /// it counts a frame.
    fn even_and_odd(&mut self) -> Result<FuncId, String> {
        let tail_signature = self.signature(2, CallConv::Tail);
        let even = self
            .module
            .declare_function("even", Linkage::Local, &tail_signature)
            .map_err(|e| e.to_string())?;
        let odd = self
            .module
            .declare_function("odd", Linkage::Local, &tail_signature)
            .map_err(|e| e.to_string())?;
        for (this, other) in [(even, odd), (odd, even)] {
            let other_ref = self
                .module
                .declare_func_in_func(other, &mut self.context.func);
            self.define(this, tail_signature.clone(), |b, refs| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                let context = b.block_params(entry)[0];
                let n = b.block_params(entry)[1];
                let acc = b.block_params(entry)[2];
                refs.count_step(b, context);
                let done = b.create_block();
                let again = b.create_block();
                b.ins().brif(n, again, &[], done, &[]);

                b.switch_to_block(done);
                b.ins().return_(&[acc]);

                b.switch_to_block(again);
                let note = refs.functions[0];
                let call = b.ins().call(note, &[context, n]);
                let here = b.inst_results(call)[0];
                let acc = b.ins().iadd(acc, here);
                let n = b.ins().iadd_imm_s(n, -1);
                b.ins().return_call(other_ref, &[context, n, acc]);
            })?;
        }

        let signature = self.signature(1, self.default_call_conv());
        let run_even = self
            .module
            .declare_function("run_even", Linkage::Local, &signature)
            .map_err(|e| e.to_string())?;
        let even_ref = self
            .module
            .declare_func_in_func(even, &mut self.context.func);
        self.define(run_even, signature, |b, refs| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let context = b.block_params(entry)[0];
            let n = b.block_params(entry)[1];
            refs.push_frame(b, context);
            let zero = b.ins().iconst(types::I64, 0);
            let call = b.ins().call(even_ref, &[context, n, zero]);
            let result = b.inst_results(call)[0];
            refs.pop_frame(b, context);
            b.ins().return_(&[result]);
        })?;
        Ok(run_even)
    }
}

/// What a function body refers to, and the counting code every body shares.
struct Refs {
    functions: Vec<FuncRef>,
}

impl Refs {
    fn load(&self, b: &mut FunctionBuilder, context: Value, at: i32) -> Value {
        b.ins()
            .load(types::I64, MemFlagsData::trusted(), context, at)
    }

    fn store(&self, b: &mut FunctionBuilder, context: Value, at: i32, value: Value) {
        b.ins().store(MemFlagsData::trusted(), value, context, at);
    }

    /// Counts a step; leaves with `OUT_OF_STEPS` if over the limit.
    fn count_step(&self, b: &mut FunctionBuilder, context: Value) {
        let steps = self.load(b, context, STEPS_AT);
        let steps = b.ins().iadd_imm_s(steps, 1);
        self.store(b, context, STEPS_AT, steps);
        let limit = self.load(b, context, STEP_LIMIT_AT);
        let over = b.ins().icmp(IntCC::UnsignedGreaterThan, steps, limit);
        self.fail_if(b, context, over, OUT_OF_STEPS);
    }

    /// Counts a frame pending before a non-tail call; leaves with
    /// `OUT_OF_FRAMES` if over the limit.
    fn push_frame(&self, b: &mut FunctionBuilder, context: Value) {
        let frames = self.load(b, context, FRAMES_AT);
        let frames = b.ins().iadd_imm_s(frames, 1);
        self.store(b, context, FRAMES_AT, frames);
        let limit = self.load(b, context, FRAME_LIMIT_AT);
        let over = b.ins().icmp(IntCC::UnsignedGreaterThan, frames, limit);
        self.fail_if(b, context, over, OUT_OF_FRAMES);
    }

    /// The frame is no longer pending: the call returned.
    fn pop_frame(&self, b: &mut FunctionBuilder, context: Value) {
        let frames = self.load(b, context, FRAMES_AT);
        let frames = b.ins().iadd_imm_s(frames, -1);
        self.store(b, context, FRAMES_AT, frames);
    }

    /// After a call: leave if the callee stopped with an error.
    fn return_if_failed(&self, b: &mut FunctionBuilder, context: Value) {
        let error = self.load(b, context, ERROR_AT);
        let failed = b.create_block();
        let fine = b.create_block();
        b.ins().brif(error, failed, &[], fine, &[]);
        b.set_cold_block(failed);
        b.switch_to_block(failed);
        let zero = b.ins().iconst(types::I64, 0);
        b.ins().return_(&[zero]);
        b.switch_to_block(fine);
    }

    /// If `condition`, record `code` and return 0, on a cold path.
    fn fail_if(&self, b: &mut FunctionBuilder, context: Value, condition: Value, code: u64) {
        let failed = b.create_block();
        let fine = b.create_block();
        b.ins().brif(condition, failed, &[], fine, &[]);
        b.set_cold_block(failed);
        b.switch_to_block(failed);
        let code = b.ins().iconst(types::I64, code as i64);
        self.store(b, context, ERROR_AT, code);
        let zero = b.ins().iconst(types::I64, 0);
        b.ins().return_(&[zero]);
        b.switch_to_block(fine);
    }
}
