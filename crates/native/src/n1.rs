//! Stages N1 and N2a of docs/proposals/native-compilation.md: the machine's
//! bytecode (`stitchwort_rt::code`) translated instruction by instruction to
//! machine code with Cranelift, for whole reachable islands, behind `run
//! --native`.
//!
//! **The thesis.** This is an executor for the machine compiler's
//! decisions, not an optimiser: each instruction does what the machine's
//! does, with the same moves, clones, drops and reuse in the same order, on
//! the machine's own values (`stitchwort_rt::native_abi` has the layout and
//! the crossing). Only the interpreter's overhead goes: dispatch, the
//! register vector, frame push and pop.
//!
//! **Islands** (the note's §4.6). The machine runs `main`'s entry body (its
//! glue builds the `Delay` the runner steps, which N1 doesn't compile). Each
//! function the entry body calls is an island root; its island is every
//! body it can call or make a function value of (`census::island`). The run
//! uses native code only if every root's island fits: every instruction in
//! the N1 subset (`census::n1_blocker`, which the census also uses), and,
//! where an island applies function values, every function value it can
//! make is a compiled global function taking as many arguments as each
//! `Apply` passes, and no native operation is made a value. Otherwise the
//! whole run stays on the machine, with notes saying why. Function values
//! can also come in as a root's arguments: for an island with an `Apply`,
//! the crossing checks the arguments hold none, and a call that has one
//! runs on the machine instead.
//!
//! **Frames.** A compiled body is one function in Cranelift's `tail` calling
//! convention: the context, the frames pending (its own included), then
//! each argument as its value's three words; it returns its result's three
//! words. Calls are direct calls; a self tail call is a jump back to the
//! top, any other tail call a `return_call`; `Apply` looks its target up
//! through the runtime, and each `Apply` keeps the last one it found
//! (`native_abi::ApplyCache`): applying the same function value again calls
//! the same code without asking.
//!
//! **Registers** (stage N2a). Each bytecode register is three Cranelift
//! variables, one per word of its value, so Cranelift keeps them in machine
//! registers and spills only what it must. An empty register's words are
//! all 0 (`Erased`): the ones past the arguments start so (the machine's
//! `resize`), and a move out sets them so, which is free, so a register
//! known to be empty is never erased in memory and never dropped (`full`,
//! the registers that may hold a value at each instruction, says which a
//! write, a return or an exit must drop). Values are written to memory only
//! where the runtime needs a pointer, and always as the machine would have
//! them in its register vector:
//! - a helper that reads values (a native operation, a test, a big
//!   number's switch) is given copies of the words in a spill slot, which
//!   it borrows;
//! - a helper that takes a value (`DropReuse`'s source, `CtorReuse`'s
//!   token) is given it in a spill slot, and the register is empty after;
//! - a helper that writes a register writes an empty spill slot, and the
//!   value is then assigned to the register as any other write (the old
//!   value dropped after, as the machine's assignment drops it);
//! - under the trace, `Unpack` goes through the runtime on all the
//!   registers, written out and read back.
//!
//! Ownership never changes hands at this boundary: each value is in exactly
//! one place (a variable, or a spill slot a helper is given), and every
//! move, clone and drop is the bytecode's.
//!
//! **Counting** (D1253). A call counts a step and checks the frame limit
//! before it, then a frame is pending until it returns; a tail call counts
//! a step; a constant computed for the first time is a call. These are the
//! machine's `enter_frame` and `replace`, so a run runs out at the same
//! points. Both counters are in registers: the steps left in Cranelift's
//! pinned register (set by the trampoline from the context, and written
//! back to it after; the host's value of the register is kept and put
//! back), and the frames pending as each body's argument, so a return needs
//! no decrement. Out of either, the context's error is set, and the frame
//! leaves through that point's own exit, which drops the registers that may
//! hold a value there and returns; callers check the error after every
//! call, and leave the same way. The stack-pointer check behind the frame
//! limit is only a safety margin (§4.3): with a stack big enough for the
//! frame limit it never fires, and stage N2b sizes and tests that.
//!
//! **Looking at the code.** With `STITCHWORT_NATIVE_DUMP` set, compiling
//! writes to stderr each body's Cranelift IR, its machine code as Cranelift
//! prints it and as an assembler's `.byte` line, and each global function's
//! address (to place a profiler's samples).
//!
//! **Reference counts.** Clones and drops are inline (an increment, or a
//! decrement unless the count is 1, when the runtime frees the value), as
//! are the unique-cell paths of `Unpack` and `CtorReuse`. With
//! [`Options::trace_refcounts`], every count goes through the runtime
//! instead, so the allocation trace sees each one.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::mem::{ManuallyDrop, MaybeUninit};
use std::rc::Rc;
use std::time::Instant;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    self, AbiParam, Block, FuncRef, InstBuilder, MemFlagsData, SigRef, StackSlot, StackSlotData,
    StackSlotKind, TrapCode, Value as IrValue, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Switch, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module, default_libcall_names};
use stitchwort_core::ResourceError;
use stitchwort_core::native::Native;
use stitchwort_rt::census::{island, n1_blocker};
use stitchwort_rt::code::{Code, Image, Instr, MOVE, NO_REG, Ops, Reg};
use stitchwort_rt::ir::{GlobalKind, PrimOp, Program};
use stitchwort_rt::native_abi::{
    self as abi, Context, NativeIslands, NativeRun, Numbering, OUT_OF_FRAMES, OUT_OF_STEPS,
    OWNING_TAGS, RC_VALUE_AT, STRONG_AT, TAG_DATA, TAG_FLOAT, TAG_INT, TAG_NAT, TAG_TAG, Tables,
    VALUE_SIZE, WEAK_AT,
};
use stitchwort_rt::value::Value;

/// How to compile.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// Count references through the runtime, so the allocation trace sees
    /// every count (for comparing native code with the machine).
    pub trace_refcounts: bool,
    /// The stack the code runs on, if known: native code then stops with
    /// `E-RESOURCE` rather than run off its end (a safety margin, never the
    /// limit; the module comment).
    pub stack_size: Option<usize>,
}

/// How much of the stack `Options::stack_size` gives native code is kept
/// back: what the host used above the crossing, and room at the bottom for
/// the runtime's helpers.
const STACK_SLACK: usize = 16 * 1024 * 1024;

/// A root's trampoline: `(context, arguments, result)`, the arguments moved
/// in, the result written.
type Trampoline = extern "C" fn(*mut Context, *mut Value, *mut Value);

struct Root {
    trampoline: Trampoline,
    /// The island applies function values, so its arguments mustn't hold
    /// any (the module comment).
    checks_arguments: bool,
    name: String,
}

/// A program's islands, compiled.
pub struct Islands {
    /// Owns the code memory (never unmapped, so the pointers stay valid).
    _module: JITModule,
    /// For each global: its trampoline, if it's an island root.
    roots: Vec<Option<Root>>,
    /// For each global: its compiled code, or null (`Context::functions`).
    table: Box<[*const u8]>,
    /// Each `Apply`'s cache of its target, at the address its code reads.
    #[allow(clippy::vec_box)]
    _caches: Vec<Box<abi::ApplyCache>>,
    /// What the code refers to by number (`Context::tables`).
    tables: abi::TableStore,
    stack_size: Option<usize>,
    /// What happened at the crossing, for `--verbose`.
    notes: Rc<RefCell<Vec<String>>>,
    /// How many bodies were compiled, and in what time.
    pub bodies: usize,
    pub compile_time: std::time::Duration,
}

impl Islands {
    /// The island roots, by name.
    pub fn root_names(&self) -> Vec<String> {
        self.roots
            .iter()
            .flatten()
            .map(|r| r.name.clone())
            .collect()
    }
}

impl NativeIslands for Islands {
    fn is_root(&self, g: u32) -> bool {
        self.roots.get(g as usize).is_some_and(Option::is_some)
    }

    fn accepts(&self, g: u32, args: &[&Value]) -> bool {
        let root = self.roots[g as usize].as_ref().expect("a root");
        if root.checks_arguments && args.iter().any(|v| abi::holds_function(v)) {
            self.notes.borrow_mut().push(format!(
                "native: `{}` was given a function value, so this call ran on the machine",
                root.name
            ));
            return false;
        }
        true
    }

    #[allow(unsafe_code)]
    fn call(
        &self,
        g: u32,
        args: Vec<Value>,
        run: &mut NativeRun<'_>,
    ) -> Result<Value, ResourceError> {
        let root = self.roots[g as usize].as_ref().expect("a root");
        let here = {
            let marker = 0u8;
            std::hint::black_box(&marker) as *const u8 as u64
        };
        let stack_limit = match self.stack_size {
            Some(size) if size > STACK_SLACK => here.saturating_sub((size - STACK_SLACK) as u64),
            _ => 0,
        };
        let mut context = Context {
            steps: run.steps,
            step_limit: run.limits.steps,
            frames: run.frames,
            frame_limit: run.limits.frames as u64,
            error: abi::OK,
            stack_limit,
            functions: self.table.as_ptr(),
            run: (run as *mut NativeRun<'_>).cast::<NativeRun<'static>>(),
            tables: self.tables.tables(),
        };
        let mut args = ManuallyDrop::new(args);
        let mut out = MaybeUninit::<Value>::uninit();
        (root.trampoline)(&mut context, args.as_mut_ptr(), out.as_mut_ptr());
        // SAFETY: native code took the arguments (moved, as `Call` moves
        // them into a frame), so the vector gives back only its buffer; it
        // wrote a whole value to `out` (`Erased` after an error), which is
        // now ours. `context.run` isn't used after the call.
        let result = unsafe {
            args.set_len(0);
            ManuallyDrop::drop(&mut args);
            out.assume_init()
        };
        run.steps = context.steps;
        context.result().map(|()| result)
    }
}

// --------------------------------------------------------------- admission

/// What runs natively: the roots, and every body their islands reach.
struct Plan {
    /// `(global, code)` of each root.
    roots: Vec<(u32, u32)>,
    bodies: BTreeSet<u32>,
    /// The roots whose islands apply function values.
    applying: BTreeSet<u32>,
}

/// The names of the image's bodies, for notes.
fn body_name(program: &Program, image: &Image, code: u32) -> String {
    match image.global_code.iter().position(|c| *c == Some(code)) {
        Some(g) => program.globals[g].name.to_string(),
        None => format!("body #{code}"),
    }
}

/// Which island roots fit N1 (the module comment), or why the run stays on
/// the machine.
fn plan(program: &Program, image: &Image) -> Result<Plan, Vec<String>> {
    let mut roots = Vec::new();
    for instr in &image.codes[image.entry_code as usize].instrs {
        if let Instr::Call { g, .. } = instr
            && let Some(code) = image.global_code[*g as usize]
            && !roots.contains(&(*g, code))
        {
            roots.push((*g, code));
        }
    }
    if roots.is_empty() {
        return Err(vec![
            "native: `main` calls no function, so there's nothing to run natively".to_string(),
        ]);
    }
    let mut why = Vec::new();
    let mut bodies = BTreeSet::new();
    let mut applying = BTreeSet::new();
    for &(g, code) in &roots {
        let reach = island(image, code);
        let root = &program.globals[g as usize].name;
        let mut blockers: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        let mut apply_arities = BTreeSet::new();
        let mut value_arities: BTreeMap<u32, String> = BTreeMap::new();
        let mut native_values = BTreeSet::new();
        for &c in &reach {
            for instr in &image.codes[c as usize].instrs {
                if let Some(key) = n1_blocker(instr) {
                    blockers
                        .entry(key)
                        .or_default()
                        .insert(body_name(program, image, c));
                }
                match instr {
                    Instr::Apply { args, .. } | Instr::TailApply { args, .. } => {
                        apply_arities.insert(args.len);
                    }
                    Instr::Global { g: v, .. } => match &program.globals[*v as usize].kind {
                        GlobalKind::Function { params, .. } => {
                            value_arities
                                .insert(*params, program.globals[*v as usize].name.to_string());
                        }
                        GlobalKind::Native(op) if op.arity() > 0 => {
                            let name = program.globals[*v as usize].name.to_string();
                            if abi::applicable_native(*op) {
                                value_arities.insert(op.arity(), name);
                            } else {
                                native_values.insert(name);
                            }
                        }
                        _ => {}
                    },
                    _ => {}
                }
            }
        }
        for (key, places) in &blockers {
            let places: Vec<&str> = places.iter().map(String::as_str).collect();
            why.push(format!(
                "native: `{root}`'s island has `{key}`, which N1 doesn't compile (in {})",
                places.join(", ")
            ));
        }
        if !apply_arities.is_empty() {
            applying.insert(g);
            for name in &native_values {
                why.push(format!(
                    "native: `{root}`'s island applies function values and makes `{name}`, which runs on the machine's frames, one"
                ));
            }
            for (arity, name) in &value_arities {
                if apply_arities.iter().any(|n| n != arity) {
                    why.push(format!(
                        "native: `{root}`'s island may apply `{name}` (taking {arity}) to another number of arguments"
                    ));
                }
            }
        }
        bodies.extend(reach);
    }
    if why.is_empty() {
        Ok(Plan {
            roots,
            bodies,
            applying,
        })
    } else {
        why.push("native: so the whole run is on the machine".to_string());
        Err(why)
    }
}

// --------------------------------------------------------------- compiling

/// Compiles the islands of `program`'s entry (`image` is the machine's
/// compiled image, which must outlive the result: the code refers to its
/// constants and tables), or says why the run stays on the machine.
pub fn compile(
    program: &Program,
    image: &Image,
    options: Options,
    notes: Rc<RefCell<Vec<String>>>,
) -> Result<Islands, Vec<String>> {
    abi::probe_layout().map_err(|e| vec![format!("native: {e}")])?;
    let plan = plan(program, image)?;
    let dump = std::env::var_os("STITCHWORT_NATIVE_DUMP").is_some();
    let start = Instant::now();
    let fail = |e: String| vec![format!("native: compiling failed: {e}")];
    let mut flags = settings::builder();
    flags
        .set("opt_level", "speed")
        .map_err(|e| fail(e.to_string()))?;
    flags
        .set("is_pic", "false")
        .map_err(|e| fail(e.to_string()))?;
    // Cranelift's `return_call` needs frame pointers on x86-64 (stage N0).
    flags
        .set("preserve_frame_pointers", "true")
        .map_err(|e| fail(e.to_string()))?;
    // The steps left live in the pinned register (the module comment).
    flags
        .set("enable_pinned_reg", "true")
        .map_err(|e| fail(e.to_string()))?;
    let isa = cranelift_native::builder()
        .map_err(|e| fail(format!("this machine isn't supported: {e}")))?
        .finish(settings::Flags::new(flags))
        .map_err(|e| fail(e.to_string()))?;
    let mut builder = JITBuilder::with_isa(isa, default_libcall_names());
    for (name, address) in helper_addresses() {
        builder.symbol(name, address);
    }
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    {
        let provider =
            crate::map_jit::MapJitMemoryProvider::new().map_err(|e| fail(e.to_string()))?;
        builder.memory_provider(Box::new(provider));
    }
    let mut module = JITModule::new(builder);
    let mut caches: Vec<Box<abi::ApplyCache>> = Vec::new();
    let Emitted {
        functions,
        trampolines,
    } = emit(
        &mut module,
        program,
        image,
        &plan,
        options,
        dump,
        &mut caches,
    )?;
    module
        .finalize_definitions()
        .map_err(|e| fail(e.to_string()))?;

    let mut table = vec![std::ptr::null::<u8>(); program.globals.len()].into_boxed_slice();
    for (g, code) in image.global_code.iter().enumerate() {
        if let Some(code) = code
            && let Some(id) = functions.get(code)
            && matches!(program.globals[g].kind, GlobalKind::Function { .. })
        {
            table[g] = module.get_finalized_function(*id);
            if dump {
                eprintln!("@@ {:p} {}", table[g], program.globals[g].name);
            }
        }
    }
    let mut roots: Vec<Option<Root>> = (0..program.globals.len()).map(|_| None).collect();
    for (g, id) in trampolines {
        roots[g as usize] = Some(Root {
            trampoline: trampoline(module.get_finalized_function(id)),
            checks_arguments: plan.applying.contains(&g),
            name: program.globals[g as usize].name.to_string(),
        });
    }
    Ok(Islands {
        _module: module,
        roots,
        table,
        _caches: caches,
        tables: abi::TableStore::new(program, image, 0),
        stack_size: options.stack_size,
        notes,
        bodies: plan.bodies.len(),
        compile_time: start.elapsed(),
    })
}

/// What [`emit`] declared in the module.
struct Emitted {
    /// Each body's function.
    functions: BTreeMap<u32, FuncId>,
    /// `(global, trampoline)` of each root.
    trampolines: Vec<(u32, FuncId)>,
}

/// Generates the code of `plan`'s bodies, and a trampoline for each root,
/// into `module`: the code generator, apart from where the code goes (stage
/// S4 of docs/proposals/standalone-executables.md), so the JIT and an object
/// file get the same code.
#[allow(clippy::too_many_arguments)]
fn emit(
    module: &mut dyn Module,
    program: &Program,
    image: &Image,
    plan: &Plan,
    options: Options,
    dump: bool,
    #[allow(clippy::vec_box)] caches: &mut Vec<Box<abi::ApplyCache>>,
) -> Result<Emitted, Vec<String>> {
    let fail = |e: String| vec![format!("native: compiling failed: {e}")];
    let frontend_config = module.target_config();
    let pointer = frontend_config.pointer_type();
    let call_conv = module.isa().default_call_conv();

    // Every body, declared first so that they can call each other.
    let mut functions: BTreeMap<u32, FuncId> = BTreeMap::new();
    for &code in &plan.bodies {
        let params = image.codes[code as usize].params;
        let id = module
            .declare_function(
                &format!("body{code}"),
                Linkage::Local,
                &body_signature(pointer, params),
            )
            .map_err(|e| fail(e.to_string()))?;
        functions.insert(code, id);
    }
    let helpers = Helpers::declare(module, pointer, call_conv).map_err(fail)?;
    let numbering = Numbering::of(image);
    let mut context = module.make_context();
    let mut builder_context = FunctionBuilderContext::new();
    for &code in &plan.bodies {
        context.func.signature = body_signature(pointer, image.codes[code as usize].params);
        context.func.name = ir::UserFuncName::user(0, functions[&code].as_u32());
        {
            let b = FunctionBuilder::new(&mut context.func, &mut builder_context);
            let mut generator = Gen {
                b,
                module: &mut *module,
                program,
                image,
                code_index: code,
                code: &image.codes[code as usize],
                functions: &functions,
                helpers: &helpers,
                numbering: &numbering,
                refs: BTreeMap::new(),
                signatures: BTreeMap::new(),
                caches: &mut *caches,
                pointer,
                options,
                vars: Vec::new(),
                spill: StackSlot::from_u32(0),
                temps: StackSlot::from_u32(0),
                pointers: StackSlot::from_u32(0),
                fun: StackSlot::from_u32(0),
                full: maybe_full(&image.codes[code as usize]),
                blocks: BTreeMap::new(),
                top: Block::from_u32(0),
                trap: Block::from_u32(0),
                ctx: IrValue::from_u32(0),
                frames: IrValue::from_u32(0),
            };
            generator.body();
            generator.b.seal_all_blocks();
            generator.b.finalize(frontend_config);
        }
        if dump {
            context.set_disasm(true);
            eprintln!(
                "==== {} (body{code})\n{}",
                body_name(program, image, code),
                context.func.display()
            );
        }
        module
            .define_function(functions[&code], &mut context)
            .map_err(|e| fail(format!("{} ({e:?})", body_name(program, image, code))))?;
        if dump && let Some(c) = context.compiled_code() {
            eprintln!("---- vcode\n{}", c.vcode.as_deref().unwrap_or("?"));
            // As an assembler's `.byte` line, so that a disassembler can
            // read the machine code (assemble it, then disassemble that).
            let bytes: Vec<String> = c
                .code_buffer()
                .iter()
                .map(|b| format!("0x{b:02x}"))
                .collect();
            eprintln!("---- bytes\n.byte {}", bytes.join(","));
        }
        module.clear_context(&mut context);
    }

    // A trampoline for each root, in the host's calling convention.
    let mut trampolines = Vec::new();
    for &(g, code) in &plan.roots {
        let mut signature = ir::Signature::new(call_conv);
        for _ in 0..3 {
            signature.params.push(AbiParam::new(pointer));
        }
        let id = module
            .declare_function(&format!("root{g}"), Linkage::Local, &signature)
            .map_err(|e| fail(e.to_string()))?;
        context.func.signature = signature;
        context.func.name = ir::UserFuncName::user(1, g);
        {
            let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let (ctx, args, out) = (
                b.block_params(entry)[0],
                b.block_params(entry)[1],
                b.block_params(entry)[2],
            );
            // The steps left, in the pinned register for the call; the
            // host's value of that register is kept and put back after.
            let host = b.ins().get_pinned_reg(types::I64);
            let steps = b
                .ins()
                .load(types::I64, MemFlagsData::trusted(), ctx, Context::STEPS_AT);
            let limit = b.ins().load(
                types::I64,
                MemFlagsData::trusted(),
                ctx,
                Context::STEP_LIMIT_AT,
            );
            let left = b.ins().isub(limit, steps);
            b.ins().set_pinned_reg(left);
            let frames = b
                .ins()
                .load(types::I64, MemFlagsData::trusted(), ctx, Context::FRAMES_AT);
            let mut call_args = vec![ctx, frames];
            for i in 0..image.codes[code as usize].params {
                for w in 0..3 {
                    call_args.push(b.ins().load(
                        types::I64,
                        MemFlagsData::trusted(),
                        args,
                        (i as usize * VALUE_SIZE + w * 8) as i32,
                    ));
                }
            }
            let callee = module.declare_func_in_func(functions[&code], b.func);
            let call = b.ins().call(callee, &call_args);
            let results = b.inst_results(call).to_vec();
            for (w, r) in results.into_iter().enumerate() {
                b.ins()
                    .store(MemFlagsData::trusted(), r, out, (w * 8) as i32);
            }
            let left = b.ins().get_pinned_reg(types::I64);
            let steps = b.ins().isub(limit, left);
            b.ins()
                .store(MemFlagsData::trusted(), steps, ctx, Context::STEPS_AT);
            b.ins().set_pinned_reg(host);
            b.ins().return_(&[]);
            b.seal_all_blocks();
            b.finalize(module.target_config());
        }
        module
            .define_function(id, &mut context)
            .map_err(|e| fail(format!("trampoline: {e:?}")))?;
        module.clear_context(&mut context);
        trampolines.push((g, id));
    }
    Ok(Emitted {
        functions,
        trampolines,
    })
}

/// The code at `pointer` as a trampoline.
#[allow(unsafe_code)]
fn trampoline(pointer: *const u8) -> Trampoline {
    // SAFETY: `pointer` is a finished trampoline: the host's calling
    // convention and three pointer arguments, which is `Trampoline`'s
    // signature. The code is never unmapped (`Islands::_module`).
    unsafe { std::mem::transmute::<*const u8, Trampoline>(pointer) }
}

/// A body's signature: the context, the frames pending with its own (the
/// module comment), and three words per argument, returning three words, in
/// the `tail` convention.
fn body_signature(pointer: ir::Type, params: u32) -> ir::Signature {
    let mut signature = ir::Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    for _ in 0..params * 3 {
        signature.params.push(AbiParam::new(types::I64));
    }
    for _ in 0..3 {
        signature.returns.push(AbiParam::new(types::I64));
    }
    signature
}

// ----------------------------------------------------------------- helpers

/// The runtime's helpers: `(name, address)`.
fn helper_addresses() -> Vec<(&'static str, *const u8)> {
    vec![
        ("sw_drop_words", abi::sw_drop_words as *const u8),
        ("sw_inc", abi::sw_inc as *const u8),
        ("sw_release", abi::sw_release as *const u8),
        ("sw_ctor", abi::sw_ctor as *const u8),
        ("sw_ctor_reuse", abi::sw_ctor_reuse as *const u8),
        ("sw_unpack", abi::sw_unpack as *const u8),
        ("sw_empty_cell", abi::sw_empty_cell as *const u8),
        ("sw_drop_reuse", abi::sw_drop_reuse as *const u8),
        ("sw_prim", abi::sw_prim as *const u8),
        ("sw_test", abi::sw_test as *const u8),
        ("sw_nat_pred", abi::sw_nat_pred as *const u8),
        ("sw_num_switch", abi::sw_num_switch as *const u8),
        ("sw_global", abi::sw_global as *const u8),
        ("sw_global_set", abi::sw_global_set as *const u8),
        ("sw_apply_native", abi::sw_apply_native as *const u8),
        ("sw_apply_cached", abi::sw_apply_cached as *const u8),
        ("sw_free_emptied", abi::sw_free_emptied as *const u8),
    ]
}

/// The helpers, declared in the module.
struct Helpers {
    drop_words: FuncId,
    inc: FuncId,
    release: FuncId,
    ctor: FuncId,
    ctor_reuse: FuncId,
    unpack: FuncId,
    empty_cell: FuncId,
    drop_reuse: FuncId,
    prim: FuncId,
    test: FuncId,
    nat_pred: FuncId,
    num_switch: FuncId,
    global: FuncId,
    global_set: FuncId,
    apply_native: FuncId,
    apply_cached: FuncId,
    free_emptied: FuncId,
}

impl Helpers {
    fn declare(
        module: &mut dyn Module,
        pointer: ir::Type,
        cc: CallConv,
    ) -> Result<Helpers, String> {
        use types::{I32, I64};
        let p = pointer;
        let mut declare = |name: &str, params: &[ir::Type], returns: &[ir::Type]| {
            let mut s = ir::Signature::new(cc);
            s.params.extend(params.iter().map(|t| AbiParam::new(*t)));
            s.returns.extend(returns.iter().map(|t| AbiParam::new(*t)));
            module
                .declare_function(name, Linkage::Import, &s)
                .map_err(|e| e.to_string())
        };
        Ok(Helpers {
            drop_words: declare("sw_drop_words", &[I64, I64, I64], &[])?,
            inc: declare("sw_inc", &[I64, I64, I64], &[])?,
            release: declare("sw_release", &[p, I64], &[])?,
            ctor: declare("sw_ctor", &[I32, p, I64, p], &[])?,
            ctor_reuse: declare("sw_ctor_reuse", &[I32, p, I64, p, p], &[])?,
            unpack: declare("sw_unpack", &[p, I32, p, I64, I32], &[])?,
            empty_cell: declare("sw_empty_cell", &[I64, I64], &[])?,
            drop_reuse: declare("sw_drop_reuse", &[p, p], &[])?,
            prim: declare("sw_prim", &[p, I32, p, I64, p], &[])?,
            test: declare("sw_test", &[p, I32, p, I64], &[I64])?,
            nat_pred: declare("sw_nat_pred", &[p, p], &[])?,
            num_switch: declare("sw_num_switch", &[p, I32, p], &[I64])?,
            global: declare("sw_global", &[p, I32, p], &[I64])?,
            global_set: declare("sw_global_set", &[p, I32, p], &[])?,
            apply_native: declare("sw_apply_native", &[p, p, p, I64, p], &[])?,
            apply_cached: declare("sw_apply_cached", &[p, p, I64, p], &[I64])?,
            free_emptied: declare("sw_free_emptied", &[I64, I64, I64], &[])?,
        })
    }
}

// ------------------------------------------------- registers maybe holding

/// A set of registers.
#[derive(Clone, PartialEq, Eq)]
struct Regs(Vec<u64>);

impl Regs {
    fn new(n: u32) -> Regs {
        Regs(vec![0; (n as usize).div_ceil(64).max(1)])
    }
    fn has(&self, r: Reg) -> bool {
        self.0[r as usize / 64] >> (r % 64) & 1 == 1
    }
    fn add(&mut self, r: Reg) {
        self.0[r as usize / 64] |= 1 << (r % 64);
    }
    fn remove(&mut self, r: Reg) {
        self.0[r as usize / 64] &= !(1 << (r % 64));
    }
    fn union(&mut self, other: &Regs) -> bool {
        let mut changed = false;
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            let n = *a | b;
            changed |= n != *a;
            *a = n;
        }
        changed
    }
    fn len(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }
    /// The registers in it, highest first (the order the machine releases
    /// a frame's registers in).
    fn descending(&self, n: u32) -> Vec<Reg> {
        (0..n).rev().filter(|r| self.has(*r)).collect()
    }
}

/// The instructions an instruction can go to next.
fn successors(code: &Code, pc: usize) -> Vec<usize> {
    match code.instrs[pc] {
        Instr::Jump { target } => vec![target as usize],
        Instr::JumpIfFalse { target, .. } | Instr::Test { target, .. } => {
            vec![pc + 1, target as usize]
        }
        Instr::NatCase { zero, .. } => vec![pc + 1, zero as usize],
        Instr::Switch { table, .. } => {
            let mut t: Vec<usize> = code.tables[table as usize]
                .iter()
                .map(|t| *t as usize)
                .collect();
            t.sort_unstable();
            t.dedup();
            t
        }
        Instr::NumSwitch { table, .. } => {
            let table = &code.num_tables[table as usize];
            let mut t: Vec<usize> = table
                .small
                .iter()
                .map(|(_, t)| *t as usize)
                .chain(table.big.iter().map(|(_, t)| *t as usize))
                .chain([table.default as usize])
                .collect();
            t.sort_unstable();
            t.dedup();
            t
        }
        Instr::Return { .. }
        | Instr::TailCall { .. }
        | Instr::TailApply { .. }
        | Instr::TailPrim { .. }
        | Instr::Unreachable => vec![],
        _ => vec![pc + 1],
    }
}

fn ops(code: &Code, o: Ops) -> &[Reg] {
    &code.ops[o.start as usize..(o.start + o.len) as usize]
}

/// For each instruction, the registers that may hold a value other than
/// `Erased` before it: a forward analysis over the body, so that a write,
/// a return or a tail call drops only what may be there. Every other
/// register is `Erased` then, so skipping it changes nothing.
fn maybe_full(code: &Code) -> Vec<Regs> {
    let n = code.instrs.len();
    let empty = Regs::new(code.regs);
    let mut before = vec![empty.clone(); n];
    let mut seen = vec![false; n];
    let mut start = empty.clone();
    for r in 0..code.params {
        start.add(r);
    }
    before[0] = start;
    seen[0] = true;
    let mut work = vec![0usize];
    while let Some(pc) = work.pop() {
        let mut after = before[pc].clone();
        let unmove = |after: &mut Regs, o: Ops| {
            for r in ops(code, o) {
                if r & MOVE != 0 {
                    after.remove(r & !MOVE);
                }
            }
        };
        match code.instrs[pc] {
            Instr::Move { dst, .. }
            | Instr::Const { dst, .. }
            | Instr::Captured { dst, .. }
            | Instr::Global { dst, .. }
            | Instr::NatPred { dst, .. }
            | Instr::IntOfNat { dst, .. }
            | Instr::IntNegSucc { dst, .. }
            | Instr::TextChars { dst, .. }
            | Instr::Field { dst, .. }
            | Instr::Prim { dst, .. } => after.add(dst),
            Instr::Take { dst, src } => {
                after.remove(src);
                after.add(dst);
            }
            Instr::Drop { reg } => after.remove(reg),
            Instr::Call { dst, args, .. }
            | Instr::Pap { dst, args, .. }
            | Instr::Closure { dst, args, .. }
            | Instr::Ctor { dst, args, .. } => {
                unmove(&mut after, args);
                after.add(dst);
            }
            Instr::CtorReuse {
                dst, args, token, ..
            } => {
                unmove(&mut after, args);
                after.remove(token);
                after.add(dst);
            }
            Instr::Apply { dst, f, args } => {
                if f & MOVE != 0 {
                    after.remove(f & !MOVE);
                }
                unmove(&mut after, args);
                after.add(dst);
            }
            Instr::Unpack { src, fields, token } => {
                after.remove(src);
                for p in ops(code, fields).chunks(2) {
                    after.add(p[1]);
                }
                if token != NO_REG {
                    after.add(token);
                }
            }
            Instr::DropReuse { src, token } => {
                after.remove(src);
                after.add(token);
            }
            _ => {}
        }
        for s in successors(code, pc) {
            if s >= n {
                continue;
            }
            if !seen[s] {
                seen[s] = true;
                before[s] = after.clone();
                work.push(s);
            } else if before[s].union(&after) {
                work.push(s);
            }
        }
    }
    before
}

// -------------------------------------------------------------- generation

/// A value in three words.
#[derive(Clone, Copy)]
struct Val([IrValue; 3]);

/// Where a value is.
#[derive(Clone, Copy)]
enum Loc {
    Reg(Reg),
    /// At an address plus an offset.
    Mem(IrValue, i32),
}

struct Gen<'a, 'm> {
    b: FunctionBuilder<'a>,
    module: &'m mut dyn Module,
    program: &'m Program,
    image: &'m Image,
    code_index: u32,
    code: &'m Code,
    functions: &'m BTreeMap<u32, FuncId>,
    helpers: &'m Helpers,
    numbering: &'m Numbering,
    refs: BTreeMap<FuncId, FuncRef>,
    signatures: BTreeMap<u32, SigRef>,
    #[allow(clippy::vec_box)] // addresses stay put (`Islands::_caches`)
    caches: &'m mut Vec<Box<abi::ApplyCache>>,
    pointer: ir::Type,
    options: Options,
    /// Each register's three words, as Cranelift variables, so that they
    /// live in machine registers (stage N2a). An empty register's words are
    /// all 0 (`Erased`).
    vars: Vec<[Variable; 3]>,
    /// Room for registers written out: for a helper that takes values by
    /// pointer, or to release them on an error exit.
    spill: StackSlot,
    /// Room for a constructor's fields and a helper's result.
    temps: StackSlot,
    /// Room for a native operation's argument pointers.
    pointers: StackSlot,
    /// An `Apply`'s function value.
    fun: StackSlot,
    full: Vec<Regs>,
    /// The block each leader instruction starts.
    blocks: BTreeMap<usize, Block>,
    /// Where the body starts, given its arguments: a self tail call jumps
    /// here.
    top: Block,
    /// A switch on a tag outside its table: an internal error.
    trap: Block,
    ctx: IrValue,
    /// The frames pending, this one's included: an argument, so the count
    /// lives in a register and a return needs no decrement.
    frames: IrValue,
}

const fn spill_at(i: usize) -> i32 {
    (i * VALUE_SIZE) as i32
}

fn flags() -> MemFlagsData {
    MemFlagsData::trusted()
}

/// For loads of what doesn't change while compiled code runs (the context's
/// tables): Cranelift may share them and move them out of loops.
fn fixed() -> MemFlagsData {
    MemFlagsData::trusted().with_readonly().with_can_move()
}

impl Gen<'_, '_> {
    fn func_ref(&mut self, id: FuncId) -> FuncRef {
        if let Some(r) = self.refs.get(&id) {
            return *r;
        }
        let r = self.module.declare_func_in_func(id, self.b.func);
        self.refs.insert(id, r);
        r
    }

    fn call_helper(&mut self, id: FuncId, args: &[IrValue]) -> Vec<IrValue> {
        let f = self.func_ref(id);
        let call = self.b.ins().call(f, args);
        self.b.inst_results(call).to_vec()
    }

    fn iconst(&mut self, n: u64) -> IrValue {
        self.b.ins().iconst(types::I64, n as i64)
    }

    fn i32const(&mut self, n: u32) -> IrValue {
        self.b.ins().iconst(types::I32, i64::from(n))
    }

    fn address(&mut self, n: usize) -> IrValue {
        self.b.ins().iconst(self.pointer, n as i64)
    }

    /// The address of spill slot `i`.
    fn spill_address(&mut self, i: usize) -> IrValue {
        self.b
            .ins()
            .stack_addr(self.pointer, self.spill, spill_at(i))
    }

    /// Writes `v` to spill slot `i`, for a helper that takes it by pointer;
    /// its address.
    fn spill_value(&mut self, i: usize, v: Val) -> IrValue {
        let at = self.spill_address(i);
        self.store(Loc::Mem(at, 0), v);
        at
    }

    /// An `Erased` spill slot `i`, for a helper to write a value to (as it
    /// would a register, dropping what's there); its address.
    fn spill_erased(&mut self, i: usize) -> IrValue {
        let at = self.spill_address(i);
        self.erase(Loc::Mem(at, 0));
        at
    }

    fn load(&mut self, loc: Loc) -> Val {
        let mut w = [IrValue::from_u32(0); 3];
        for (i, word) in w.iter_mut().enumerate() {
            *word = match loc {
                Loc::Reg(r) => self.b.use_var(self.vars[r as usize][i]),
                Loc::Mem(base, at) => {
                    self.b
                        .ins()
                        .load(types::I64, flags(), base, at + 8 * i as i32)
                }
            };
        }
        Val(w)
    }

    fn store(&mut self, loc: Loc, v: Val) {
        for (i, word) in v.0.iter().enumerate() {
            match loc {
                Loc::Reg(r) => self.b.def_var(self.vars[r as usize][i], *word),
                Loc::Mem(base, at) => {
                    self.b.ins().store(flags(), *word, base, at + 8 * i as i32);
                }
            }
        }
    }

    /// Makes a register `Erased`: in memory its tag byte 0; in variables
    /// all three words 0, so the old words are dead and the register is
    /// known empty.
    fn erase(&mut self, loc: Loc) {
        match loc {
            Loc::Reg(_) => {
                let zero = self.iconst(0);
                self.store(loc, Val([zero; 3]));
            }
            Loc::Mem(base, at) => {
                let zero = self.b.ins().iconst(types::I8, 0);
                self.b.ins().store(flags(), zero, base, at);
            }
        }
    }

    fn tag(&mut self, v: Val) -> IrValue {
        self.b.ins().band_imm_u(v.0[0], 0xff)
    }

    fn is_tag(&mut self, v: Val, tag: u8) -> IrValue {
        let t = self.tag(v);
        self.b.ins().icmp_imm_u(IntCC::Equal, t, i64::from(tag))
    }

    /// A `Tag`'s or a constructor's tag (bytes 4-7).
    fn ctor_tag(&mut self, v: Val) -> IrValue {
        let t = self.b.ins().ushr_imm_u(v.0[0], 32);
        self.b.ins().ireduce(types::I32, t)
    }

    /// 1 if the value holds a reference.
    fn owns(&mut self, v: Val) -> IrValue {
        let t = self.tag(v);
        let mask = self.iconst(OWNING_TAGS);
        let bit = self.b.ins().ushr(mask, t);
        self.b.ins().band_imm_u(bit, 1)
    }

    /// A small value's words.
    fn small(&mut self, tag: u8, payload_hi: u32, payload: u64) -> Val {
        let w0 = self.iconst(u64::from(tag) | (u64::from(payload_hi) << 32));
        let w1 = self.iconst(payload);
        let w2 = self.iconst(0);
        Val([w0, w1, w2])
    }

    fn nat(&mut self, n: IrValue) -> Val {
        let w0 = self.iconst(u64::from(TAG_NAT));
        let w2 = self.iconst(0);
        Val([w0, n, w2])
    }

    /// Runs `then` in a new block if `cond` (otherwise skips it), then
    /// continues after.
    fn when(&mut self, cond: IrValue, cold: bool, then: impl FnOnce(&mut Self)) {
        let yes = self.b.create_block();
        let after = self.b.create_block();
        self.b.ins().brif(cond, yes, &[], after, &[]);
        if cold {
            self.b.set_cold_block(yes);
        }
        self.b.switch_to_block(yes);
        then(self);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    /// A copy of the value at `loc`: its words, with its count taken.
    fn clone_from(&mut self, loc: Loc) -> Val {
        let v = self.load(loc);
        let owns = self.owns(v);
        let trace = self.options.trace_refcounts;
        self.when(owns, false, |g| {
            if trace {
                g.call_helper(g.helpers.inc, &v.0);
            } else {
                let strong = g.b.ins().load(types::I64, flags(), v.0[1], STRONG_AT);
                let strong = g.b.ins().iadd_imm_s(strong, 1);
                g.b.ins().store(flags(), strong, v.0[1], STRONG_AT);
            }
        });
        v
    }

    /// Drops a value native code holds.
    fn drop_value(&mut self, v: Val) {
        let owns = self.owns(v);
        let trace = self.options.trace_refcounts;
        self.when(owns, false, |g| {
            if trace {
                g.call_helper(g.helpers.drop_words, &v.0);
                return;
            }
            let strong = g.b.ins().load(types::I64, flags(), v.0[1], STRONG_AT);
            let last = g.b.ins().icmp_imm_u(IntCC::Equal, strong, 1);
            let free = g.b.create_block();
            let keep = g.b.create_block();
            let after = g.b.create_block();
            g.b.ins().brif(last, free, &[], keep, &[]);
            g.b.switch_to_block(free);
            g.call_helper(g.helpers.drop_words, &v.0);
            g.b.ins().jump(after, &[]);
            g.b.switch_to_block(keep);
            let fewer = g.b.ins().iadd_imm_s(strong, -1);
            g.b.ins().store(flags(), fewer, v.0[1], STRONG_AT);
            g.b.ins().jump(after, &[]);
            g.b.switch_to_block(after);
        });
    }

    /// `reg = v`: the old value (if the register may hold one) dropped.
    fn assign(&mut self, pc: usize, r: Reg, v: Val) {
        if self.full[pc].has(r) {
            let old = self.load(Loc::Reg(r));
            self.store(Loc::Reg(r), v);
            self.drop_value(old);
        } else {
            self.store(Loc::Reg(r), v);
        }
    }

    /// An operand, as `get!` takes it: moved out if marked `MOVE`,
    /// otherwise cloned.
    fn operand(&mut self, r: Reg) -> Val {
        if r & MOVE != 0 {
            let r = r & !MOVE;
            let v = self.load(Loc::Reg(r));
            self.erase(Loc::Reg(r));
            v
        } else {
            self.clone_from(Loc::Reg(r))
        }
    }

    fn operands(&mut self, o: Ops) -> Vec<Val> {
        ops(self.code, o)
            .to_vec()
            .into_iter()
            .map(|r| self.operand(r))
            .collect()
    }

    /// The field at `at` of the context's tables (`abi::Tables`): how
    /// compiled code reaches the host's memory, which it holds no address
    /// of (stage S4 of docs/proposals/standalone-executables.md).
    fn tables_field(&mut self, at: i32) -> IrValue {
        let tables = self
            .b
            .ins()
            .load(self.pointer, fixed(), self.ctx, Context::TABLES_AT);
        self.b.ins().load(self.pointer, fixed(), tables, at)
    }

    fn ctx_load(&mut self, at: i32) -> IrValue {
        self.b.ins().load(types::I64, flags(), self.ctx, at)
    }

    fn ctx_store(&mut self, at: i32, v: IrValue) {
        self.b.ins().store(flags(), v, self.ctx, at);
    }

    /// If `cond`, leaves the frame on an error: sets the context's error
    /// to `error` (unless a callee already did), drops the registers in
    /// `live` (the registers that may hold a value at this point: registers
    /// live in variables, so each exit releases its own), and returns.
    /// Otherwise continues.
    fn exit_if(&mut self, cond: IrValue, live: &Regs, error: Option<u64>) {
        let exit = self.b.create_block();
        let fine = self.b.create_block();
        self.b.ins().brif(cond, exit, &[], fine, &[]);
        self.b.switch_to_block(exit);
        self.b.set_cold_block(exit);
        if let Some(error) = error {
            if error == OUT_OF_STEPS {
                // One step over the limit, as the machine counts it.
                let over = self.iconst(u64::MAX);
                self.b.ins().set_pinned_reg(over);
            }
            let error = self.iconst(error);
            self.ctx_store(Context::ERROR_AT, error);
        }
        // Written out lowest first, so that `sw_release` (which drops the
        // last first) drops them highest first, as the machine releases a
        // frame.
        let regs = live.descending(self.code.regs);
        for (i, r) in regs.iter().rev().enumerate() {
            let v = self.load(Loc::Reg(*r));
            self.spill_value(i, v);
        }
        if !regs.is_empty() {
            let at = self.spill_address(0);
            let count = self.iconst(regs.len() as u64);
            self.call_helper(self.helpers.release, &[at, count]);
        }
        let zero = self.iconst(0);
        self.b.ins().return_(&[zero, zero, zero]);
        self.b.switch_to_block(fine);
    }

    /// A frame entered: a step, out of steps if over the limit (`live`
    /// as for [`Gen::exit_if`]).
    fn count_step(&mut self, live: &Regs) {
        // The steps left are in the pinned register: none left means this
        // step is one over the limit.
        let left = self.b.ins().get_pinned_reg(types::I64);
        let over = self.b.ins().icmp_imm_u(IntCC::Equal, left, 0);
        self.exit_if(over, live, Some(OUT_OF_STEPS));
        let left = self.b.ins().iadd_imm_s(left, -1);
        self.b.ins().set_pinned_reg(left);
    }

    /// A frame about to be pushed: out of frames if as many are pending as
    /// the limit allows (or at the stack's safety margin). The frames
    /// pending with the new one, which the callee is given.
    fn push_frame(&mut self, live: &Regs) -> IrValue {
        let frames = self.frames;
        let limit = self.ctx_load(Context::FRAME_LIMIT_AT);
        let over = self
            .b
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, frames, limit);
        if self.options.stack_size.is_some() {
            let sp = self.b.ins().get_stack_pointer(self.pointer);
            let floor = self.ctx_load(Context::STACK_LIMIT_AT);
            let low = self.b.ins().icmp(IntCC::UnsignedLessThan, sp, floor);
            let either = self.b.ins().bor(over, low);
            self.exit_if(either, live, Some(OUT_OF_FRAMES));
        } else {
            self.exit_if(over, live, Some(OUT_OF_FRAMES));
        }
        self.b.ins().iadd_imm_s(frames, 1)
    }

    /// After a call returned: an error in the callee unwinds this frame
    /// too. (The callee's frame is no longer pending: the count is this
    /// frame's again, which it never changed.)
    fn after_call(&mut self, live: &Regs) {
        let error = self.ctx_load(Context::ERROR_AT);
        self.exit_if(error, live, None);
    }

    /// `regs` without the registers `o` moves out (marked `MOVE`).
    fn without_moved(&self, regs: &Regs, o: &[Reg]) -> Regs {
        let mut left = regs.clone();
        for r in o {
            if r & MOVE != 0 {
                left.remove(r & !MOVE);
            }
        }
        left
    }

    fn words(args: &[Val]) -> impl Iterator<Item = IrValue> + '_ {
        args.iter().flat_map(|v| v.0)
    }

    /// Drops the registers in `regs`, highest first, as the machine
    /// releases a frame.
    fn release(&mut self, regs: &Regs) {
        for r in regs.descending(self.code.regs) {
            let v = self.load(Loc::Reg(r));
            self.drop_value(v);
        }
    }

    fn block_of(&self, pc: u32) -> Block {
        self.blocks[&(pc as usize)]
    }

    fn signature(&mut self, params: u32) -> SigRef {
        if let Some(s) = self.signatures.get(&params) {
            return *s;
        }
        let s = self
            .b
            .import_signature(body_signature(self.pointer, params));
        self.signatures.insert(params, s);
        s
    }

    /// The array of pointers to registers `regs`, for a helper.
    /// The registers are written to the first spill slots (borrowed: the
    /// helper only reads them).
    fn pointer_array(&mut self, regs: &[Reg]) -> IrValue {
        for (i, r) in regs.iter().enumerate() {
            let v = self.load(Loc::Reg(*r));
            let at = self.spill_value(i, v);
            self.b
                .ins()
                .stack_store(self.pointer, at, self.pointers, (i * 8) as i32);
        }
        self.b.ins().stack_addr(self.pointer, self.pointers, 0)
    }

    fn temp_address(&mut self, at: usize) -> IrValue {
        self.b.ins().stack_addr(self.pointer, self.temps, at as i32)
    }

    fn body(&mut self) {
        let code = self.code;
        let n = code.instrs.len();
        let max_ops = code
            .instrs
            .iter()
            .map(|i| match i {
                Instr::Ctor { args, .. }
                | Instr::CtorReuse { args, .. }
                | Instr::Apply { args, .. }
                | Instr::TailApply { args, .. } => args.len as usize,
                _ => 0,
            })
            .max()
            .unwrap_or(0);
        let max_prim = code
            .instrs
            .iter()
            .map(|i| match i {
                Instr::Prim { args, .. } | Instr::Test { args, .. } => args.len as usize,
                _ => 0,
            })
            .max()
            .unwrap_or(0);
        // Room for: the registers an error exit releases (at most those
        // that may hold a value at some instruction), a helper's operands
        // and result, and, under the trace, every register (`Unpack`).
        let released = self.full.iter().map(Regs::len).max().unwrap_or(0);
        let traced = if self.options.trace_refcounts {
            code.regs as usize
        } else {
            0
        };
        let spills = released.max(traced).max(max_prim + 1).max(2);
        self.spill = self.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (spills * VALUE_SIZE) as u32,
            3,
        ));
        self.vars = (0..code.regs)
            .map(|_| std::array::from_fn(|_| self.b.declare_var(types::I64)))
            .collect();
        self.temps = self.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            ((max_ops + 1) * VALUE_SIZE) as u32,
            3,
        ));
        self.fun = self.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            VALUE_SIZE as u32,
            3,
        ));
        self.pointers = self.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (max_prim.max(1) * 8) as u32,
            3,
        ));

        // Leaders: the start, every target, and what follows a branch.
        let mut leaders = BTreeSet::from([0usize]);
        for pc in 0..n {
            let next = successors(code, pc);
            let falls = next == [pc + 1] && !matches!(code.instrs[pc], Instr::Jump { .. });
            if !falls {
                leaders.extend(next.iter().copied().filter(|s| *s < n));
                if pc + 1 < n {
                    leaders.insert(pc + 1);
                }
            }
        }
        for pc in leaders {
            let block = self.b.create_block();
            self.blocks.insert(pc, block);
        }

        let entry = self.b.create_block();
        self.b.append_block_params_for_function_params(entry);
        self.top = self.b.create_block();
        for _ in 0..code.params * 3 {
            self.b.append_block_param(self.top, types::I64);
        }

        self.b.switch_to_block(entry);
        self.ctx = self.b.block_params(entry)[0];
        self.frames = self.b.block_params(entry)[1];
        let args: Vec<IrValue> = self.b.block_params(entry)[2..].to_vec();
        let args: Vec<ir::BlockArg> = args.into_iter().map(Into::into).collect();
        self.b.ins().jump(self.top, &args);

        self.b.switch_to_block(self.top);
        let params: Vec<IrValue> = self.b.block_params(self.top).to_vec();
        for r in 0..code.params {
            let i = r as usize * 3;
            self.store(Loc::Reg(r), Val([params[i], params[i + 1], params[i + 2]]));
        }
        for r in code.params..code.regs {
            self.erase(Loc::Reg(r));
        }
        let first = self.blocks[&0];
        self.b.ins().jump(first, &[]);

        self.trap = self.b.create_block();
        self.b.switch_to_block(self.trap);
        self.b.set_cold_block(self.trap);
        self.b.ins().trap(TrapCode::unwrap_user(3));

        let mut open = false;
        for pc in 0..n {
            if let Some(block) = self.blocks.get(&pc).copied() {
                if open {
                    self.b.ins().jump(block, &[]);
                }
                self.b.switch_to_block(block);
                open = true;
            }
            if !open {
                continue;
            }
            open = self.instr(pc);
        }
        if open {
            self.b.ins().trap(TrapCode::unwrap_user(1));
        }
    }

    /// Compiles instruction `pc`; whether control can fall through to the
    /// next one.
    fn instr(&mut self, pc: usize) -> bool {
        let code = self.code;
        let s = self.program.shapes;
        match code.instrs[pc] {
            Instr::Move { dst, src } => {
                let v = self.clone_from(Loc::Reg(src));
                self.assign(pc, dst, v);
            }
            Instr::Take { dst, src } => {
                let v = self.load(Loc::Reg(src));
                self.erase(Loc::Reg(src));
                self.assign(pc, dst, v);
            }
            Instr::Drop { reg } => {
                if self.full[pc].has(reg) {
                    let v = self.load(Loc::Reg(reg));
                    self.erase(Loc::Reg(reg));
                    self.drop_value(v);
                }
            }
            Instr::Const { dst, k } => {
                let value = &self.image.pool[k as usize];
                let v = match value {
                    Value::Erased => self.small(0, 0, 0),
                    Value::Nat(n) => self.small(TAG_NAT, 0, *n),
                    Value::Int(i) => self.small(TAG_INT, 0, *i as u64),
                    Value::Float(x) => self.small(TAG_FLOAT, 0, x.to_bits()),
                    Value::Tag(t) => self.small(TAG_TAG, *t, 0),
                    _ => {
                        let pool = self.tables_field(Tables::POOL_AT);
                        let at = i32::try_from(k as usize * VALUE_SIZE)
                            .expect("the constant pool fits an offset");
                        self.clone_from(Loc::Mem(pool, at))
                    }
                };
                self.assign(pc, dst, v);
            }
            Instr::Global { dst, g } => self.global(pc, dst, g),
            Instr::Call { dst, g, args } => {
                let live = self.full[pc].clone();
                self.count_step(&live);
                let frames = self.push_frame(&live);
                let values = self.operands(args);
                let live = self.without_moved(&live, ops(code, args));
                let callee = self.image.global_code[g as usize].expect("a function has code");
                let f = self.func_ref(self.functions[&callee]);
                let mut call_args = vec![self.ctx, frames];
                call_args.extend(Self::words(&values));
                let call = self.b.ins().call(f, &call_args);
                let r = self.b.inst_results(call).to_vec();
                self.after_call(&live);
                self.assign(pc, dst, Val([r[0], r[1], r[2]]));
            }
            Instr::TailCall { g, args } => {
                self.count_step(&self.full[pc].clone());
                let values = self.operands(args);
                let left = self.without_moved(&self.full[pc], ops(code, args));
                self.release(&left);
                let callee = self.image.global_code[g as usize].expect("a function has code");
                let words: Vec<IrValue> = Self::words(&values).collect();
                if callee == self.code_index {
                    let args: Vec<ir::BlockArg> = words.into_iter().map(Into::into).collect();
                    self.b.ins().jump(self.top, &args);
                } else {
                    let f = self.func_ref(self.functions[&callee]);
                    let mut call_args = vec![self.ctx, self.frames];
                    call_args.extend(words);
                    self.b.ins().return_call(f, &call_args);
                }
                return false;
            }
            Instr::Apply { dst, f, args } => {
                // As the machine: the function value taken, then a frame
                // for compiled code (`exact`), or a native's value computed
                // with no frame (eval/apply).
                let (fv, target) = self.apply_target(f, args.len);
                let compiled = self.b.create_block();
                let native = self.b.create_block();
                let after = self.b.create_block();
                self.b.ins().brif(target, compiled, &[], native, &[]);

                self.b.switch_to_block(compiled);
                self.drop_value(fv);
                let live = self.without_moved(&self.full[pc], &[f]);
                self.count_step(&live);
                let frames = self.push_frame(&live);
                let values = self.operands(args);
                let live = self.without_moved(&live, ops(code, args));
                let sig = self.signature(args.len);
                let mut call_args = vec![self.ctx, frames];
                call_args.extend(Self::words(&values));
                let call = self.b.ins().call_indirect(sig, target, &call_args);
                let r = self.b.inst_results(call).to_vec();
                self.after_call(&live);
                self.assign(pc, dst, Val([r[0], r[1], r[2]]));
                self.b.ins().jump(after, &[]);

                self.b.switch_to_block(native);
                let values = self.operands(args);
                let v = self.apply_native(&values);
                self.assign(pc, dst, v);
                self.b.ins().jump(after, &[]);
                self.b.switch_to_block(after);
            }
            Instr::TailApply { f, args } => {
                let (fv, target) = self.apply_target(f, args.len);
                let taken = self.without_moved(&self.full[pc], &[f]);
                let left = self.without_moved(&taken, ops(code, args));
                let compiled = self.b.create_block();
                let native = self.b.create_block();
                self.b.ins().brif(target, compiled, &[], native, &[]);

                self.b.switch_to_block(compiled);
                self.drop_value(fv);
                self.count_step(&taken);
                let values = self.operands(args);
                self.release(&left);
                let sig = self.signature(args.len);
                let mut call_args = vec![self.ctx, self.frames];
                call_args.extend(Self::words(&values));
                self.b.ins().return_call_indirect(sig, target, &call_args);

                self.b.switch_to_block(native);
                let values = self.operands(args);
                for (i, v) in values.iter().enumerate() {
                    let at = self.temp_address(i * VALUE_SIZE);
                    self.store(Loc::Mem(at, 0), *v);
                }
                self.release(&left);
                let v = self.apply_native_stored(values.len());
                self.b.ins().return_(&v.0);
                return false;
            }
            Instr::Return { src } => {
                let v = self.load(Loc::Reg(src));
                let mut left = self.full[pc].clone();
                left.remove(src);
                self.release(&left);
                self.b.ins().return_(&v.0);
                return false;
            }
            Instr::Prim { dst, op, args } => self.prim(pc, dst, op, args),
            Instr::Test { op, args, target } => {
                let o = ops(code, args).to_vec();
                let holds = self.test(op, &o);
                let next = self.block_of(pc as u32 + 1);
                let target = self.block_of(target);
                self.b.ins().brif(holds, next, &[], target, &[]);
                return false;
            }
            Instr::JumpIfFalse { cond, target } => {
                let v = self.load(Loc::Reg(cond));
                let t = self.ctor_tag(v);
                let is_true = self.b.ins().icmp_imm_u(IntCC::Equal, t, i64::from(s.true_));
                let next = self.block_of(pc as u32 + 1);
                let target = self.block_of(target);
                self.b.ins().brif(is_true, next, &[], target, &[]);
                return false;
            }
            Instr::Jump { target } => {
                let target = self.block_of(target);
                self.b.ins().jump(target, &[]);
                return false;
            }
            Instr::Switch { src, table } => {
                let v = self.load(Loc::Reg(src));
                let t = self.ctor_tag(v);
                let mut switch = Switch::new();
                for (tag, target) in code.tables[table as usize].iter().enumerate() {
                    switch.set_entry(tag as u128, self.block_of(*target));
                }
                let otherwise = self.trap;
                switch.emit(&mut self.b, t, otherwise);
                return false;
            }
            Instr::Field { dst, src, i } => {
                let cell = self.load(Loc::Reg(src)).0[1];
                let v = self.clone_from(Loc::Mem(
                    cell,
                    RC_VALUE_AT + (i as usize * VALUE_SIZE) as i32,
                ));
                self.assign(pc, dst, v);
            }
            Instr::Unpack { src, fields, token } => self.unpack(pc, src, fields, token),
            Instr::DropReuse { src, token } => {
                // The helper takes the value from its slot and writes the
                // token to an empty one; the token register is then assigned
                // as the machine's `*token = v` assigns it.
                let v = self.load(Loc::Reg(src));
                self.erase(Loc::Reg(src));
                let from = self.spill_value(0, v);
                let to = self.spill_erased(1);
                self.call_helper(self.helpers.drop_reuse, &[from, to]);
                let t = self.load(Loc::Mem(to, 0));
                self.assign(pc, token, t);
            }
            Instr::Ctor { dst, tag, args } => {
                let values = self.operands(args);
                let v = self.new_cell(tag, &values);
                self.assign(pc, dst, v);
            }
            Instr::CtorReuse {
                dst,
                tag,
                args,
                token,
            } => self.ctor_reuse(pc, dst, tag, args, token),
            Instr::NatCase { src, zero } => {
                let v = self.load(Loc::Reg(src));
                let nat = self.is_tag(v, TAG_NAT);
                let is_zero = self.b.ins().icmp_imm_u(IntCC::Equal, v.0[1], 0);
                let both = self.b.ins().band(nat, is_zero);
                let zero = self.block_of(zero);
                let next = self.block_of(pc as u32 + 1);
                self.b.ins().brif(both, zero, &[], next, &[]);
                return false;
            }
            Instr::NatPred { dst, src } => {
                let v = self.load(Loc::Reg(src));
                let nat = self.is_tag(v, TAG_NAT);
                let small = self.b.create_block();
                let big = self.b.create_block();
                let after = self.b.create_block();
                self.b.ins().brif(nat, small, &[], big, &[]);
                self.b.switch_to_block(small);
                let n = self.b.ins().iadd_imm_s(v.0[1], -1);
                let n = self.nat(n);
                self.assign(pc, dst, n);
                self.b.ins().jump(after, &[]);
                self.b.switch_to_block(big);
                self.b.set_cold_block(big);
                let from = self.spill_value(0, v);
                let to = self.spill_erased(1);
                self.call_helper(self.helpers.nat_pred, &[from, to]);
                let n = self.load(Loc::Mem(to, 0));
                self.assign(pc, dst, n);
                self.b.ins().jump(after, &[]);
                self.b.switch_to_block(after);
            }
            Instr::NumSwitch { src, table } => {
                let t = &code.num_tables[table as usize];
                let v = self.load(Loc::Reg(src));
                let nat = self.is_tag(v, TAG_NAT);
                let small = self.b.create_block();
                let big = self.b.create_block();
                self.b.ins().brif(nat, small, &[], big, &[]);
                self.b.switch_to_block(small);
                let mut switch = Switch::new();
                for (k, target) in &t.small {
                    switch.set_entry(u128::from(*k), self.block_of(*target));
                }
                let default = self.block_of(t.default);
                switch.emit(&mut self.b, v.0[1], default);
                self.b.switch_to_block(big);
                self.b.set_cold_block(big);
                let number = self.numbering.num_table(self.code_index, table);
                let number = self.i32const(number);
                let src = self.spill_value(0, v);
                let r = self.call_helper(self.helpers.num_switch, &[self.ctx, number, src]);
                let mut switch = Switch::new();
                let mut targets: Vec<u32> = t.big.iter().map(|(_, t)| *t).collect();
                targets.sort_unstable();
                targets.dedup();
                for target in targets {
                    switch.set_entry(u128::from(target), self.block_of(target));
                }
                switch.emit(&mut self.b, r[0], default);
                return false;
            }
            Instr::Unreachable => {
                self.b.ins().trap(TrapCode::unwrap_user(2));
                return false;
            }
            other => unreachable!("{other:?} isn't in the N1 subset"),
        }
        true
    }

    /// A new cell of `tag` with `values` (moved into it).
    fn new_cell(&mut self, tag: u32, values: &[Val]) -> Val {
        for (i, v) in values.iter().enumerate() {
            let at = self.temp_address(i * VALUE_SIZE);
            self.store(Loc::Mem(at, 0), *v);
        }
        let fields = self.temp_address(0);
        let out = self.temp_address(values.len() * VALUE_SIZE);
        let tag = self.i32const(tag);
        let n = self.iconst(values.len() as u64);
        self.call_helper(self.helpers.ctor, &[tag, fields, n, out]);
        self.load(Loc::Mem(out, 0))
    }

    fn global(&mut self, pc: usize, dst: Reg, g: u32) {
        let out = self.temp_address(0);
        let gc = self.i32const(g);
        let known = self.call_helper(self.helpers.global, &[self.ctx, gc, out])[0];
        let is_constant = matches!(
            self.program.globals[g as usize].kind,
            GlobalKind::Constant { .. }
        );
        if !is_constant {
            let v = self.load(Loc::Mem(out, 0));
            self.assign(pc, dst, v);
            return;
        }
        let have = self.b.create_block();
        let compute = self.b.create_block();
        let after = self.b.create_block();
        self.b.ins().brif(known, have, &[], compute, &[]);
        self.b.switch_to_block(have);
        let v = self.load(Loc::Mem(out, 0));
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);

        // The first use: computed as the machine computes it, in a frame.
        self.b.switch_to_block(compute);
        self.b.set_cold_block(compute);
        let live = self.full[pc].clone();
        self.count_step(&live);
        let frames = self.push_frame(&live);
        let code = self.image.global_code[g as usize].expect("a constant has code");
        let f = self.func_ref(self.functions[&code]);
        let call = self.b.ins().call(f, &[self.ctx, frames]);
        let r = self.b.inst_results(call).to_vec();
        self.after_call(&live);
        let v = Val([r[0], r[1], r[2]]);
        let out = self.temp_address(0);
        self.store(Loc::Mem(out, 0), v);
        let gc = self.i32const(g);
        self.call_helper(self.helpers.global_set, &[self.ctx, gc, out]);
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    /// `Apply`'s function value, taken from `f` (moved or cloned) and kept
    /// in the `fun` slot, and its compiled code, or 0 for a native.
    fn apply_target(&mut self, f: Reg, n: u32) -> (Val, IrValue) {
        let v = self.operand(f);
        let at = self.b.ins().stack_addr(self.pointer, self.fun, 0);
        self.store(Loc::Mem(at, 0), v);
        // This site's cache (`abi::ApplyCache`): the same function value as
        // last time calls the same code, with no runtime call.
        let cache = Box::new(abi::ApplyCache::new());
        let cache_at = self.address(&*cache as *const abi::ApplyCache as usize);
        self.caches.push(cache);
        let key = self
            .b
            .ins()
            .load(types::I64, flags(), cache_at, abi::ApplyCache::KEY_AT);
        let is_fun = self.is_tag(v, abi::TAG_FUN);
        let same = self.b.ins().icmp(IntCC::Equal, key, v.0[1]);
        let hit = self.b.ins().band(is_fun, same);
        let cached = self.b.create_block();
        let miss = self.b.create_block();
        let after = self.b.create_block();
        self.b.append_block_param(after, self.pointer);
        self.b.ins().brif(hit, cached, &[], miss, &[]);
        self.b.switch_to_block(cached);
        let code = self
            .b
            .ins()
            .load(self.pointer, flags(), cache_at, abi::ApplyCache::CODE_AT);
        self.b.ins().jump(after, &[code.into()]);
        self.b.switch_to_block(miss);
        self.b.set_cold_block(miss);
        let n = self.iconst(u64::from(n));
        let target = self.call_helper(self.helpers.apply_cached, &[self.ctx, at, n, cache_at])[0];
        self.b.ins().jump(after, &[target.into()]);
        self.b.switch_to_block(after);
        (v, self.b.block_params(after)[0])
    }

    /// The native in the `fun` slot applied to `values` (moved).
    fn apply_native(&mut self, values: &[Val]) -> Val {
        for (i, v) in values.iter().enumerate() {
            let at = self.temp_address(i * VALUE_SIZE);
            self.store(Loc::Mem(at, 0), *v);
        }
        self.apply_native_stored(values.len())
    }

    /// The native in the `fun` slot applied to the `n` values in the temps.
    fn apply_native_stored(&mut self, n: usize) -> Val {
        let f = self.b.ins().stack_addr(self.pointer, self.fun, 0);
        let args = self.temp_address(0);
        let out = self.temp_address(n * VALUE_SIZE);
        let count = self.iconst(n as u64);
        self.call_helper(self.helpers.apply_native, &[self.ctx, f, args, count, out]);
        self.load(Loc::Mem(out, 0))
    }

    fn prim(&mut self, pc: usize, dst: Reg, op: PrimOp, args: Ops) {
        let o = ops(self.code, args).to_vec();
        let fast =
            matches!(op, PrimOp::Nat(Native::Add | Native::Sub | Native::Mul)) && o.len() == 2;
        let slow = self.b.create_block();
        let after = self.b.create_block();
        if fast {
            let a = self.load(Loc::Reg(o[0]));
            let b = self.load(Loc::Reg(o[1]));
            let na = self.is_tag(a, TAG_NAT);
            let nb = self.is_tag(b, TAG_NAT);
            let both = self.b.ins().band(na, nb);
            let small = self.b.create_block();
            self.b.ins().brif(both, small, &[], slow, &[]);
            self.b.switch_to_block(small);
            let (x, y) = (a.0[1], b.0[1]);
            let result = match op {
                PrimOp::Nat(Native::Sub) => {
                    let diff = self.b.ins().isub(x, y);
                    let under = self.b.ins().icmp(IntCC::UnsignedLessThan, x, y);
                    let zero = self.iconst(0);
                    Some(self.b.ins().select(under, zero, diff))
                }
                _ => None,
            };
            let z = match result {
                Some(z) => z,
                None => {
                    let (z, over) = if op == PrimOp::Nat(Native::Add) {
                        self.b.ins().uadd_overflow(x, y)
                    } else {
                        self.b.ins().umul_overflow(x, y)
                    };
                    let fits = self.b.create_block();
                    self.b.ins().brif(over, slow, &[], fits, &[]);
                    self.b.switch_to_block(fits);
                    z
                }
            };
            let v = self.nat(z);
            self.assign(pc, dst, v);
            self.b.ins().jump(after, &[]);
            self.b.set_cold_block(slow);
        } else {
            self.b.ins().jump(slow, &[]);
        }
        self.b.switch_to_block(slow);
        let op = self.i32const(self.numbering.op(op));
        let array = self.pointer_array(&o);
        let n = self.iconst(o.len() as u64);
        let out = self.spill_erased(o.len());
        self.call_helper(self.helpers.prim, &[self.ctx, op, array, n, out]);
        let v = self.load(Loc::Mem(out, 0));
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    /// 1 if the test holds.
    fn test(&mut self, op: PrimOp, o: &[Reg]) -> IrValue {
        let slow = self.b.create_block();
        let after = self.b.create_block();
        self.b.append_block_param(after, types::I8);
        let cc = match op {
            PrimOp::Nat(Native::Leq) => Some(IntCC::UnsignedLessThanOrEqual),
            PrimOp::Nat(Native::EqNat) => Some(IntCC::Equal),
            _ => None,
        };
        if let (Some(cc), [a, b]) = (cc, o) {
            let a = self.load(Loc::Reg(*a));
            let b = self.load(Loc::Reg(*b));
            let na = self.is_tag(a, TAG_NAT);
            let nb = self.is_tag(b, TAG_NAT);
            let both = self.b.ins().band(na, nb);
            let small = self.b.create_block();
            self.b.ins().brif(both, small, &[], slow, &[]);
            self.b.switch_to_block(small);
            let holds = self.b.ins().icmp(cc, a.0[1], b.0[1]);
            self.b.ins().jump(after, &[holds.into()]);
            self.b.set_cold_block(slow);
        } else {
            self.b.ins().jump(slow, &[]);
        }
        self.b.switch_to_block(slow);
        let op = self.i32const(self.numbering.op(op));
        let array = self.pointer_array(o);
        let n = self.iconst(o.len() as u64);
        let r = self.call_helper(self.helpers.test, &[self.ctx, op, array, n])[0];
        let holds = self.b.ins().icmp_imm_u(IntCC::NotEqual, r, 0);
        self.b.ins().jump(after, &[holds.into()]);
        self.b.switch_to_block(after);
        self.b.block_params(after)[0]
    }

    /// Whether the cell whose address is `cell` is unique (strong count 1,
    /// no weak references).
    fn unique(&mut self, cell: IrValue) -> IrValue {
        let strong = self.b.ins().load(types::I64, flags(), cell, STRONG_AT);
        let weak = self.b.ins().load(types::I64, flags(), cell, WEAK_AT);
        let s1 = self.b.ins().icmp_imm_u(IntCC::Equal, strong, 1);
        let w1 = self.b.ins().icmp_imm_u(IntCC::Equal, weak, 1);
        self.b.ins().band(s1, w1)
    }

    fn unpack(&mut self, pc: usize, src: Reg, fields: Ops, token: Reg) {
        let pairs: Vec<(u32, Reg)> = ops(self.code, fields)
            .chunks(2)
            .map(|p| (p[0], p[1]))
            .collect();
        if self.options.trace_refcounts {
            // The helper works on the frame's registers as the machine
            // does, so they're all written out and read back.
            for r in 0..self.code.regs {
                let v = self.load(Loc::Reg(r));
                self.spill_value(r as usize, v);
            }
            let regs = self.spill_address(0);
            let src = self.i32const(src);
            let at = self.address(ops(self.code, fields).as_ptr() as usize);
            let n = self.iconst(pairs.len() as u64);
            let token = self.i32const(token);
            self.call_helper(self.helpers.unpack, &[regs, src, at, n, token]);
            for r in 0..self.code.regs {
                let at = self.spill_address(r as usize);
                let v = self.load(Loc::Mem(at, 0));
                self.store(Loc::Reg(r), v);
            }
            return;
        }
        let v = self.load(Loc::Reg(src));
        self.erase(Loc::Reg(src));
        let cell = v.0[1];
        let field_at = |i: u32| RC_VALUE_AT + (i as usize * VALUE_SIZE) as i32;
        let unique = self.unique(cell);
        let mine = self.b.create_block();
        let shared = self.b.create_block();
        let after = self.b.create_block();
        self.b.ins().brif(unique, mine, &[], shared, &[]);

        // Unique: the fields are moved out.
        self.b.switch_to_block(mine);
        let taken = pairs.iter().map(|p| p.0).collect::<BTreeSet<u32>>().len();
        // A cell that's freed without a walk over its fields needn't have
        // the fields it gave up erased; they're erased below only if it's
        // walked (each field taken once, so no field is read twice).
        let later = token == NO_REG && taken == pairs.len();
        for &(i, d) in &pairs {
            let f = self.load(Loc::Mem(cell, field_at(i)));
            if !later {
                self.erase(Loc::Mem(cell, field_at(i)));
            }
            self.assign(pc, d, f);
        }
        if token == NO_REG {
            // The emptied cell (and whatever fields the arm doesn't use)
            // freed; with every field taken, there's nothing in it to walk.
            let n = v.0[2];
            let all = self.b.ins().icmp_imm_u(IntCC::Equal, n, taken as i64);
            let emptied = self.b.create_block();
            let partial = self.b.create_block();
            let freed = self.b.create_block();
            self.b.ins().brif(all, emptied, &[], partial, &[]);
            self.b.switch_to_block(emptied);
            self.call_helper(self.helpers.free_emptied, &v.0);
            self.b.ins().jump(freed, &[]);
            self.b.switch_to_block(partial);
            if later {
                for &(i, _) in &pairs {
                    self.erase(Loc::Mem(cell, field_at(i)));
                }
            }
            self.call_helper(self.helpers.drop_words, &v.0);
            self.b.ins().jump(freed, &[]);
            self.b.switch_to_block(freed);
        } else {
            let n = v.0[2];
            let partial = self
                .b
                .ins()
                .icmp_imm_u(IntCC::NotEqual, n, pairs.len() as i64);
            self.when(partial, false, |g| {
                g.call_helper(g.helpers.empty_cell, &[cell, n]);
            });
            self.assign(pc, token, v);
        }
        self.b.ins().jump(after, &[]);

        // Shared: the fields are copied and the cell left alone.
        self.b.switch_to_block(shared);
        for &(i, d) in &pairs {
            let f = self.clone_from(Loc::Mem(cell, field_at(i)));
            self.assign(pc, d, f);
        }
        if token != NO_REG {
            let erased = self.small(0, 0, 0);
            self.assign(pc, token, erased);
        }
        self.drop_value(v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    fn ctor_reuse(&mut self, pc: usize, dst: Reg, tag: u32, args: Ops, token: Reg) {
        let n = args.len;
        let slow = self.b.create_block();
        let after = self.b.create_block();
        if !self.options.trace_refcounts {
            let t = self.load(Loc::Reg(token));
            let data = self.is_tag(t, TAG_DATA);
            let len = self.b.ins().icmp_imm_u(IntCC::Equal, t.0[2], i64::from(n));
            let shaped = self.b.ins().band(data, len);
            let check = self.b.create_block();
            self.b.ins().brif(shaped, check, &[], slow, &[]);
            self.b.switch_to_block(check);
            let unique = self.unique(t.0[1]);
            let reuse = self.b.create_block();
            self.b.ins().brif(unique, reuse, &[], slow, &[]);
            self.b.switch_to_block(reuse);
            self.erase(Loc::Reg(token));
            let cell = t.0[1];
            for (i, r) in ops(self.code, args).to_vec().into_iter().enumerate() {
                let v = self.operand(r);
                self.store(Loc::Mem(cell, RC_VALUE_AT + (i * VALUE_SIZE) as i32), v);
            }
            let w0 = self.iconst(u64::from(TAG_DATA) | (u64::from(tag) << 32));
            self.assign(pc, dst, Val([w0, cell, t.0[2]]));
            self.b.ins().jump(after, &[]);
            self.b.set_cold_block(slow);
        } else {
            self.b.ins().jump(slow, &[]);
        }
        self.b.switch_to_block(slow);
        let values = self.operands(args);
        for (i, v) in values.iter().enumerate() {
            let at = self.temp_address(i * VALUE_SIZE);
            self.store(Loc::Mem(at, 0), *v);
        }
        let fields = self.temp_address(0);
        let out = self.temp_address(values.len() * VALUE_SIZE);
        let tag = self.i32const(tag);
        let count = self.iconst(u64::from(n));
        let t = self.load(Loc::Reg(token));
        self.erase(Loc::Reg(token));
        let token = self.spill_value(0, t);
        self.call_helper(self.helpers.ctor_reuse, &[tag, fields, count, token, out]);
        let v = self.load(Loc::Mem(out, 0));
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }
}

/// Makes the factory `run --native` gives the runtime: compiles each
/// program's islands with `options`, noting in `notes` what runs natively
/// and why anything doesn't.
pub fn factory(
    options: Options,
    notes: Rc<RefCell<Vec<String>>>,
) -> impl FnMut(&Program, &Image) -> Option<Box<dyn NativeIslands>> {
    move |program, image| match compile(program, image, options, notes.clone()) {
        Ok(islands) => {
            notes.borrow_mut().push(format!(
                "native: running {} natively ({} bodies, compiled in {:.1} ms)",
                islands
                    .root_names()
                    .iter()
                    .map(|n| format!("`{n}`"))
                    .collect::<Vec<_>>()
                    .join(", "),
                islands.bodies,
                islands.compile_time.as_secs_f64() * 1000.0
            ));
            Some(Box::new(islands))
        }
        Err(why) => {
            notes.borrow_mut().extend(why);
            None
        }
    }
}
