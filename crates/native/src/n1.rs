//! Stages N1 to N4 of docs/proposals/native-compilation.md: the machine's
//! bytecode (`stitchwort_rt::code`) translated instruction by instruction to
//! machine code with Cranelift, for every body `main` reaches, behind `run
//! --native`.
//!
//! **The thesis.** This is an executor for the machine compiler's
//! decisions, not an optimiser: each instruction does what the machine's
//! does, with the same moves, clones, drops and reuse in the same order, on
//! the machine's own values (`stitchwort_rt::native_abi` has the layout and
//! the crossing). Only the interpreter's overhead goes: dispatch, the
//! register vector, frame push and pop. Borrowed parameters
//! (`stitchwort_rt::borrow`) are the one place the two differ in what they
//! count: a lent register (`Peek`, `Lend`, `Forget`, `Own`, and a call's
//! borrowed operands) is a plain copy of words here, with no increment or
//! decrement, where the machine keeps an uncounted clone and checks it.
//!
//! **What runs natively** (stage NO4 of docs/proposals/native-only.md).
//! Every body `main`'s entry reaches (`census::island`), the entry
//! included, is compiled, or the program is refused with why (stage NO5: a
//! body with an instruction native code doesn't compile,
//! `census::n1_blocker`, none since N4; a failed layout probe; a target
//! Cranelift or the runtime doesn't support; a stack over the cap). There
//! is no machine to fall back to: `stitchwort run` is the machine. The runner drives native code
//! through `native_abi::NativeExecutor`, which enters it by three
//! trampolines (the entry, the apply stubs, the effect runtime's loop),
//! and native code has the machine run nothing for it: `Text.fold` is a
//! runtime body (`rt_text_fold`, NO1), the effect runtime's loop and
//! resumptions are too (`rt_loop`, `rt_resume`, NO2), and its leaf function
//! values and state-passing handlers are the runtime's leaves (NO3).
//!
//! **Effects** (stage N4, and NO2–NO3 of native-only.md). `bind c k` is
//! inline: `abi::sw_bind` takes `c` apart, and for `Done x` native code
//! applies `k` to `x` as `Apply` (or `TailApply`) would, compiled
//! continuations called directly; otherwise the node `Bind c k` is the
//! result. A fold, `translate` and `runPure` start the effect runtime's
//! loop (`runtime::emit_loop`), and a state-passing handler's fold makes its
//! function of the state by a leaf (`abi::sw_eff_state`); the loop's leaves
//! share the machine's code (`machine::handler_for`, `state_step`), so every
//! effect value, count and allocation is the machine's.
//!
//! **Frames.** A compiled global body is one function in Cranelift's `tail`
//! calling convention: the context, the frames pending (its own included),
//! then each argument as its value's three words; it returns its result's
//! three words. Calls are direct calls; a self tail call is a jump back to
//! the top, any other tail call a `return_call`.
//!
//! **Closures** (stage N3). A lambda's body, and an adapter per global
//! function (`value{g}`, which drops the function value and tail-calls the
//! body), take the same arguments plus one more word last: the function
//! value's `Rc` (a closure's captures), owned by the callee and released
//! when the body returns, tail-calls or leaves by an exit; `Captured` loads
//! from it. These are the "value convention", the code
//! `native_abi::Context::functions` and `lambdas` list. `Closure` and `Pap`
//! make values through the runtime (`sw_closure`, `sw_pap`). `Apply` of a
//! function value to exactly its arity with nothing yet applied is the fast
//! path: each `Apply` keeps the last target it found (`native_abi::ApplyCache`,
//! keyed by the `Fun`'s variant and index, the value's first word masked),
//! and a hit is an indirect call, a miss one runtime lookup. Everything else
//! (a partial application to extend, under-application making a new one,
//! over-application applying the result to the rest, a native operation,
//! `DoneK`) goes through one shared stub per argument count (`apply{n}`):
//! `sw_apply_prepare` does what the machine's `apply` and `enter` do, the
//! clones and drops in the machine's order, then the stub counts the step,
//! checks the frame and calls the code it was given, looping on any
//! arguments left over. A `TailApply` is a `return_call` (to the target, or
//! to the stub), so tail applies run in constant stack.
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
//! **Large bodies** (SW-2557). A body with more than `VARIABLE_REGISTERS`
//! registers or more than `PART_INSTRS` instructions (generated code: a
//! long list literal holds every element in a register until the list is
//! built) keeps its registers in a register file on the heap
//! (`sw_regs_new`) instead, laid out as the machine's register vector. An
//! error exit hands the whole file to the runtime and a release drops it
//! whole (`sw_release_down`): registers that hold nothing there are
//! `Erased`, so this gives up what the variables would, in the same order,
//! without writing out every register at every exit. Such a body is
//! compiled in parts of at most `PART_INSTRS` instructions, each its own
//! function; a part goes on in another by a tail call that passes the
//! frame's state (`part_signature`), so no function Cranelift is given
//! grows with the program. Its exits that hold nothing outside the
//! registers are shared, one per error, and a write drops the register's
//! old value only if an instruction before it may have filled the register
//! (`first_fills`).
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
//! limit is only a backstop (§4.3), sized by `frames` (stage N2b): the
//! run reserves a stack big enough for the frame limit times the widest
//! body's frame bound ([`stack_for`], stage NO5), so it never fires; if it
//! did, it would stop the run with the same `E-RESOURCE` and depth note.
//!
//! **Looking at the code.** With `STITCHWORT_NATIVE_DUMP` set, compiling
//! writes to stderr each body's Cranelift IR, its machine code as Cranelift
//! prints it and as an assembler's `.byte` line, and each global function's
//! address (to place a profiler's samples). With [`Options::pc_map`],
//! each body's machine code is mapped to the bytecode instruction, and the
//! [`Part`] of it, each stretch is for ([`BodyMap`]), through Cranelift's
//! source locations, which leave the code as it is.
//!
//! **Reference counts.** Clones and drops are inline (an increment, or a
//! decrement unless the count is 1, when the runtime frees the value), as
//! are the unique-cell paths of `Unpack` and `CtorReuse`. With
//! [`Options::trace_refcounts`], every count goes through the runtime
//! instead, so the allocation trace sees each one.

use std::collections::{BTreeMap, BTreeSet};
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
use stitchwort_core::native::Native;
use stitchwort_rt::cell_cache::{self, CellCache};
use stitchwort_rt::census::{island, n1_blocker};
use stitchwort_rt::code::{Code, Image, Instr, MOVE, NO_REG, Ops, Reg};
use stitchwort_rt::effect::EffectOp;
use stitchwort_rt::ir::{GlobalKind, HoleOp, PrimOp, Program, Reuse};
use stitchwort_rt::linked::Outline;
use stitchwort_rt::native_abi::{
    self as abi, ARRAY_ITEMS_AT, ARRAY_LEN_AT, ApplyPlan, Context, CrossingCode, FUN_CAPTURES_AT,
    FUN_CLOSURE, FUN_KEY_MASK, NativeIslands, Numbering, OUT_OF_FRAMES, OUT_OF_STEPS, OWNING_TAGS,
    RC_VALUE_AT, STRONG_AT, TAG_ARRAY, TAG_DATA, TAG_FLOAT, TAG_FUN, TAG_INT, TAG_NAT, TAG_TAG,
    Tables, VALUE_SIZE, WEAK_AT,
};
use stitchwort_rt::natives::{ArrayNative, IntNative, TextNative};
use stitchwort_rt::value::Value;

use crate::frames;

mod runtime;

/// How to compile.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// Count references through the runtime, so the allocation trace sees
    /// every count (for comparing native code with the machine).
    pub trace_refcounts: bool,
    /// Each body counts its own entries (`sw_count_body`, a call with the
    /// body's symbol name), and each inline cell-cache hit calls
    /// `sw_count_cell_hit` (the hit is decided in compiled code, so this is
    /// the only way to see it), for a profiling build linked against a runtime
    /// with the `call-counts` feature. Off, the code is the same as
    /// without the option.
    pub count_bodies: bool,
    /// Records which bytecode instruction, and which [`Part`] of it, each
    /// stretch of a body's machine code is for ([`BodyMap`]), so that a
    /// profiler can fold samples by address into instructions and parts.
    /// The code is the same as without the option: only Cranelift's
    /// source locations are set.
    pub pc_map: bool,
}

/// What a stretch of a body's machine code does for its instruction, in a
/// [`BodyMap`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Part {
    /// Before the first instruction: the parameters into registers (and,
    /// under `count_bodies`, the count).
    Entry,
    /// The instruction's own work: loads, stores, tests, arithmetic, and
    /// the runtime helpers it calls (`sw_ctor`, `sw_prim`).
    Work,
    /// The step count, the frame-limit and stack checks before a call, and
    /// the error-flag test after one.
    Check,
    /// A reference count taken (a clone).
    Inc,
    /// A reference count given up (a drop), freeing through the runtime
    /// when it was the last.
    Dec,
    /// A call to compiled code, or a tail call: the call itself and its
    /// arguments' moves.
    Call,
    /// A return, with the epilogue Cranelift puts there.
    Return,
    /// An error exit: the registers handed to `sw_unwind` (cold code).
    Unwind,
    /// The prologue, which Cranelift emits with no source location.
    Prologue,
    /// Code of no instruction: what Cranelift's optimiser made or moved
    /// (constants, values shared between instructions), which keeps no
    /// source location, and the register allocator's moves at a block's
    /// start.
    Untagged,
}

impl Part {
    /// Every part but `Prologue`, by its number in a source location.
    const TAGGED: [Part; 8] = [
        Part::Entry,
        Part::Work,
        Part::Check,
        Part::Inc,
        Part::Dec,
        Part::Call,
        Part::Return,
        Part::Unwind,
    ];

    /// The source location for this part of instruction `slot - 1` (slot 0:
    /// before the first instruction): the slot above three bits of part.
    fn at(self, slot: u32) -> ir::SourceLoc {
        let part = Part::TAGGED
            .iter()
            .position(|p| *p == self)
            .expect("a part with a source location");
        ir::SourceLoc::new(slot << 3 | part as u32)
    }

    /// The instruction (`None` before the first) and part a location
    /// names, `Untagged` for the default location.
    fn of(loc: ir::SourceLoc) -> (Option<u32>, Part) {
        if loc.is_default() {
            return (None, Part::Untagged);
        }
        let bits = loc.bits();
        (
            (bits >> 3).checked_sub(1),
            Part::TAGGED[(bits & 7) as usize],
        )
    }

    /// Its name in a profile's report: `entry`, `work`, `check`, and so on.
    pub fn name(self) -> &'static str {
        match self {
            Part::Entry => "entry",
            Part::Work => "work",
            Part::Check => "check",
            Part::Inc => "inc",
            Part::Dec => "dec",
            Part::Call => "call",
            Part::Return => "return",
            Part::Unwind => "unwind",
            Part::Prologue => "prologue",
            Part::Untagged => "untagged",
        }
    }
}

/// Under [`Options::pc_map`], where a body's machine code came from.
#[derive(Clone, Debug)]
pub struct BodyMap {
    /// The body's symbol, as `nm` and samply show it (without Mach-O's `_`).
    pub symbol: String,
    /// The size of its machine code, in bytes.
    pub size: u32,
    /// Its bytecode instructions, as `Debug` prints them, by `pc`.
    pub instrs: Vec<String>,
    /// Stretches of its machine code, by offset from the symbol, in order,
    /// covering it.
    pub stretches: Vec<Stretch>,
}

/// Bytes `start..end` of a body's code are `part` of instruction `pc`
/// (`None`: of no instruction, for `Entry`, `Prologue` and `Untagged`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stretch {
    pub start: u32,
    pub end: u32,
    pub pc: Option<u32>,
    pub part: Part,
}

/// A program's bodies, compiled, with the image they were compiled for.
///
/// It owns everything its crossing points into: the code memory (the
/// module) and the image whose constant pool and number tables the tables
/// point at. Its fields are private, so safe code can't take the crossing
/// away from them.
pub struct Islands {
    /// The code's tables and the crossing, shared with a standalone
    /// executable's linked code. Declared first, so dropped first.
    crossing: abi::Crossing,
    /// Owns the code memory (never unmapped, so the pointers stay valid).
    _module: JITModule,
    /// What the tables point into: the pool and the number tables, in the
    /// image's own heap buffers, which stay put when the image moves.
    _image: Image,
    /// A bound on the stack one counted frame uses (`frames`).
    pub max_frame: usize,
    /// The body with the widest frame, by name.
    pub widest: String,
    /// How many bodies were compiled (every one `main` reaches, its entry
    /// included), and in what time.
    pub bodies: usize,
    pub compile_time: std::time::Duration,
}

impl Islands {
    /// What `run --native --verbose` says about the code.
    pub fn note(&self) -> String {
        format!(
            "native: running {} of the {} bodies `main` reaches natively (frames of at most {} bytes, compiled in {:.1} ms)",
            self.bodies,
            self.bodies,
            self.max_frame,
            self.compile_time.as_secs_f64() * 1000.0
        )
    }
}

impl NativeIslands for Islands {
    fn crossing(&self) -> &abi::Crossing {
        // Valid while `self` is: `_module` and `_image` are kept with it.
        &self.crossing
    }
}

/// The stack a native run of code whose frames are at most `max_frame`
/// bytes (the widest `widest`'s) reserves under a limit of `frame_limit`
/// frames (`abi::native_stack`: §3 of docs/proposals/native-only.md), or,
/// if that passes the cap (D1299), why the program can't be compiled: the
/// message, then a note.
pub fn stack_for(frame_limit: u64, max_frame: usize, widest: &str) -> Result<usize, Vec<String>> {
    abi::native_stack(frame_limit, max_frame).ok_or_else(|| {
        let gib = |bytes: f64| bytes / (1024.0 * 1024.0 * 1024.0);
        let needed = (frame_limit as f64 + 1.0) * max_frame as f64
            + (abi::HOST_ROOM + abi::HELPER_ROOM) as f64;
        vec![
            format!(
                "the native stack would be too big: {frame_limit} frames (the frame limit) of up to {max_frame} bytes (`{widest}`'s, the widest) need {:.1} GiB, over the cap of {:.0} GiB",
                gib(needed),
                gib(abi::STACK_CAP as f64)
            ),
            format!(
                "split `{widest}` into smaller functions, or run the program on the machine with `stitchwort run`"
            ),
        ]
    })
}

// --------------------------------------------------------------- admission

/// What runs natively: every body reachable from the entry, the entry
/// included (stage NO4 of native-only.md: all or nothing).
pub(crate) struct Plan {
    pub(crate) bodies: BTreeSet<u32>,
    /// The constants compiled as roots of their own, each with an entry
    /// trampoline into its body ([`compile_roots`]), by global.
    pub(crate) roots: Vec<u32>,
    /// Whether anything `main` reaches may run a state-passing handler
    /// ([`uses_state_handlers`]), so the runtime's bodies need their part
    /// for one (stage NO3 of docs/proposals/native-only.md).
    pub(crate) states: bool,
    /// Whether anything `main` reaches uses `Text.fold` (a `Prim`, or its
    /// function value), so the module needs the compiled `Text.fold`
    /// ([`emit_text_fold`]).
    pub(crate) folds: bool,
    /// Whether anything `main` reaches uses the effect runtime (an effect
    /// native, or its function value), so the module needs the runtime's
    /// bodies (`runtime`: stage NO2 of docs/proposals/native-only.md) for
    /// the loops and resumptions it may run.
    pub(crate) effects: bool,
}

/// The names of the image's bodies, for notes.
pub(crate) fn body_name(program: &Program, image: &Image, code: u32) -> String {
    if let Some(g) = image.global_code.iter().position(|c| *c == Some(code)) {
        return program.globals[g].name.to_string();
    }
    match image.lambda_code.iter().position(|c| *c == code) {
        Some(l) => format!("lambda #{l}"),
        None => format!("body #{code}"),
    }
}

/// Each body's symbol, for a profiler or debugger reading the executable
/// (`nm`, samply): a global's body is its full name, a lambda's is the
/// symbol of the body that makes it plus `/lambda{l}` (`/dispatch{l}` for
/// a handler's dispatch, [`stitchwort_rt::dispatch`]), so a sample in a
/// lambda says which definition it belongs to. Every symbol ends `#{code}`,
/// the body's number in `STITCHWORT_NATIVE_DUMP`, which also keeps it apart
/// from the runtime's and the stubs' symbols.
fn body_symbols(program: &Program, image: &Image) -> BTreeMap<u32, String> {
    let mut maker: BTreeMap<u32, u32> = BTreeMap::new();
    for (code, body) in image.codes.iter().enumerate() {
        for instr in &body.instrs {
            if let Instr::Closure { lambda, .. } | Instr::StaticClosure { lambda, .. } = instr {
                maker.entry(*lambda).or_insert(code as u32);
            }
        }
    }
    let mut names: BTreeMap<u32, String> = BTreeMap::new();
    for (g, code) in image.global_code.iter().enumerate() {
        if let Some(code) = code {
            names.insert(*code, program.globals[g].name.to_string());
        }
    }
    fn lambda_name(
        l: u32,
        program: &Program,
        image: &Image,
        maker: &BTreeMap<u32, u32>,
        names: &BTreeMap<u32, String>,
        depth: usize,
    ) -> String {
        let owner = match maker.get(&l) {
            Some(&code) if depth < 16 => match names.get(&code) {
                Some(name) => name.clone(),
                None => match image.lambda_code.iter().position(|c| *c == code) {
                    Some(outer) => {
                        lambda_name(outer as u32, program, image, maker, names, depth + 1)
                    }
                    None => format!("body{code}"),
                },
            },
            _ => "?".to_string(),
        };
        let kind = match program.lambdas.get(l as usize) {
            Some(lambda) if lambda.dispatch => "dispatch",
            _ => "lambda",
        };
        format!("{owner}/{kind}{l}")
    }
    let mut symbols = BTreeMap::new();
    for code in 0..image.codes.len() as u32 {
        let base = match names.get(&code) {
            Some(name) => name.clone(),
            None => match image.lambda_code.iter().position(|c| *c == code) {
                Some(l) => lambda_name(l as u32, program, image, &maker, &names, 0),
                None => "body".to_string(),
            },
        };
        symbols.insert(code, format!("{base}#{code}"));
    }
    symbols
}

/// The targets native code is compiled for (§4 of
/// docs/proposals/native-only.md, as stage S5 of
/// standalone-executables.md): the ones Cranelift and the runtime support.
pub const SUPPORTED_TARGETS: [&str; 6] = [
    "aarch64-apple-darwin",
    "x86_64-apple-darwin",
    "aarch64-unknown-linux-musl",
    "x86_64-unknown-linux-musl",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-gnu",
];

/// This machine's target, as [`SUPPORTED_TARGETS`] names them.
pub fn host_target() -> String {
    let os = match std::env::consts::OS {
        "macos" => "apple-darwin",
        "linux" if cfg!(target_env = "musl") => "unknown-linux-musl",
        "linux" => "unknown-linux-gnu",
        other => other,
    };
    format!("{}-{os}", std::env::consts::ARCH)
}

/// Whether `target` is one native code supports, or why not.
pub fn check_target(target: &str) -> Result<(), String> {
    if SUPPORTED_TARGETS.contains(&target) {
        return Ok(());
    }
    Err(format!(
        "native code doesn't support this target, `{target}`: only {}",
        SUPPORTED_TARGETS
            .iter()
            .map(|t| format!("`{t}`"))
            .collect::<Vec<_>>()
            .join(", ")
    ))
}

/// What every native compilation checks first: the target, then the layout
/// of values native code relies on (`abi::probe_layout`). The CLI and the
/// runtime library come from one workspace build, so a layout the compiler
/// sees is the one an executable it builds will have; the executable
/// checks again at start-up all the same.
pub(crate) fn preflight() -> Result<(), Vec<String>> {
    check_target(&host_target()).map_err(|e| vec![e])?;
    abi::probe_layout().map_err(|e| vec![e])
}

/// Which bodies run natively: every body reachable from the entry, the
/// entry included (stage NO4 of native-only.md), and from each constant
/// of `roots` (global numbers), or, if any has an instruction native code
/// doesn't compile, why the program can't be compiled (stage NO5: there's
/// no machine to run that body).
pub(crate) fn plan(program: &Program, image: &Image, roots: &[u32]) -> Result<Plan, Vec<String>> {
    let mut starts = vec![image.entry_code];
    for &g in roots {
        match (
            &program.globals.get(g as usize),
            image.global_code.get(g as usize),
        ) {
            (Some(global), Some(Some(code)))
                if matches!(global.kind, GlobalKind::Constant { .. }) =>
            {
                starts.push(*code);
            }
            _ => return Err(vec![format!("global {g} isn't a constant with a body")]),
        }
    }
    let reach: Vec<u32> = {
        let mut seen = BTreeSet::new();
        for start in starts {
            seen.extend(island(image, start));
        }
        seen.into_iter().collect()
    };
    let states = reach.iter().any(|&code| {
        image.codes[code as usize]
            .instrs
            .iter()
            .any(|instr| uses_state_handlers(program, instr))
    });
    let folds = reach.iter().any(|&code| {
        image.codes[code as usize]
            .instrs
            .iter()
            .any(|instr| uses_text_fold(program, instr))
    });
    let effects = reach.iter().any(|&code| {
        image.codes[code as usize]
            .instrs
            .iter()
            .any(|instr| uses_effects(program, instr))
    });
    let mut refusals = Vec::new();
    for &code in &reach {
        let mut blockers = BTreeSet::new();
        for instr in &image.codes[code as usize].instrs {
            if let Some(key) = n1_blocker(instr) {
                blockers.insert(key);
            }
        }
        if !blockers.is_empty() {
            let keys: Vec<String> = blockers.into_iter().map(|k| format!("`{k}`")).collect();
            refusals.push(format!(
                "`{}` uses {}, which the native compiler doesn't compile yet",
                body_name(program, image, code),
                keys.join(", ")
            ));
        }
    }
    if !refusals.is_empty() {
        let reaching = if roots.is_empty() {
            "`main` reaches"
        } else {
            "the roots reach"
        };
        let mut why = vec![format!(
            "not every function {reaching} can be compiled natively"
        )];
        why.extend(refusals);
        return Err(why);
    }
    Ok(Plan {
        bodies: reach.into_iter().collect(),
        roots: roots.to_vec(),
        states,
        folds,
        effects,
    })
}

/// Whether `instr` is an effect native, or makes one's function value.
fn uses_effects(program: &Program, instr: &Instr) -> bool {
    match instr {
        Instr::Prim { op, .. } | Instr::TailPrim { op, .. } => matches!(op, PrimOp::Effect(_)),
        Instr::Global { g, .. } | Instr::Pap { g, .. } => matches!(
            program.globals[*g as usize].kind,
            GlobalKind::Native(PrimOp::Effect(_))
        ),
        _ => false,
    }
}

/// Whether native code runs effect native `op` itself (stage NO2 of
/// docs/proposals/native-only.md: `rt_loop`), rather than having the machine
/// run it: a fold, `translate` or `runPure`.
pub(crate) fn runs_loop(op: EffectOp) -> bool {
    matches!(
        op,
        EffectOp::Fold
            | EffectOp::FoldLazy
            | EffectOp::FoldIn
            | EffectOp::FoldForwarding
            | EffectOp::Translate
            | EffectOp::RunPure
    )
}

/// Whether `instr` is `Text.fold`, or makes its function value.
fn uses_text_fold(program: &Program, instr: &Instr) -> bool {
    let fold = PrimOp::Text(TextNative::TextFold);
    match instr {
        Instr::Prim { op, .. } | Instr::TailPrim { op, .. } => *op == fold,
        Instr::Global { g, .. } | Instr::Pap { g, .. } => {
            matches!(program.globals[*g as usize].kind, GlobalKind::Native(op) if op == fold)
        }
        _ => false,
    }
}

/// Whether `instr` may make a state-passing handler: its fold, or an
/// effect native's function value (which may be one): the runtime's
/// bodies then need their part for a state loop (stage NO3 of
/// docs/proposals/native-only.md).
fn uses_state_handlers(program: &Program, instr: &Instr) -> bool {
    match instr {
        Instr::Prim {
            op: PrimOp::Effect(op),
            ..
        }
        | Instr::TailPrim {
            op: PrimOp::Effect(op),
            ..
        } => matches!(op, EffectOp::FoldState | EffectOp::FoldStateComp),
        Instr::Global { g, .. } | Instr::Pap { g, .. } => matches!(
            program.globals[*g as usize].kind,
            GlobalKind::Native(PrimOp::Effect(_))
        ),
        _ => false,
    }
}

// --------------------------------------------------------------- compiling

/// Compiles every body `program`'s entry reaches (`image` is the
/// machine's compiled image of it, which the result keeps: the tables
/// point at its constants and number tables), or says why it can't: the
/// message, then any notes.
///
/// The code can't outlive its image, as it could when this borrowed the
/// image (SW-1124): it takes it.
///
/// ```compile_fail,E0308
/// # fn f(program: &stitchwort_rt::Program) {
/// let image = stitchwort_rt::code::compile(program);
/// let code = stitchwort_native::n1::compile(program, &image, Default::default());
/// drop(image);
/// # }
/// ```
///
/// Nor can safe code run it on a stack that is too small:
/// [`NativeExecutor`](stitchwort_rt::native_abi::NativeExecutor) checks the
/// stack it is told it has against the thread's real one at its first
/// crossing, and stops the run with a depth error if the thread has less.
pub fn compile(program: &Program, image: Image, options: Options) -> Result<Islands, Vec<String>> {
    compile_roots(program, image, &[], options)
}

/// [`compile`], and also every body each constant of `roots` (global
/// numbers) reaches, with a way into each of those constants
/// ([`NativeExecutor::global`](stitchwort_rt::native_abi::NativeExecutor::global)):
/// for a program of several roots whose entry is nothing, as `stitchwort
/// test` lowers its tests (`lower_definitions`).
pub fn compile_roots(
    program: &Program,
    image: Image,
    roots: &[u32],
    options: Options,
) -> Result<Islands, Vec<String>> {
    let compiled = compile_audited(
        program,
        &image,
        roots,
        options,
        &mut Audit::new(program, &image, false),
    )?;
    let Compiled {
        module,
        code,
        n_caches,
        widest,
        bodies,
        compile_time,
    } = compiled;
    let max_frame = code.max_frame;
    // The tables point into `image`'s pool and number tables (heap
    // buffers, which don't move when `image` moves into the islands below).
    let tables = abi::TableStore::new(program, &image, n_caches);
    let outline = Outline::of(program, &image);
    // SAFETY: `code` is `compile_audited`'s finished code for `program` and
    // `image`, against these tables and this outline; the islands own the
    // module (whose code is never unmapped) and the image, and keep the
    // crossing private, so both outlive it.
    #[allow(unsafe_code)]
    let crossing = unsafe { abi::Crossing::new(code, tables, outline) };
    Ok(Islands {
        crossing,
        _module: module,
        _image: image,
        max_frame,
        widest,
        bodies,
        compile_time,
    })
}

/// What [`compile_audited`] made: the finished module and the ways into
/// its code, before the tables are made.
struct Compiled {
    module: JITModule,
    code: CrossingCode,
    n_caches: usize,
    widest: String,
    bodies: usize,
    compile_time: std::time::Duration,
}

/// The Cranelift IR of every function [`compile`] makes for `program`'s
/// islands, as text: a function of the program alone, since the code holds
/// no host address (stage S4 of docs/proposals/standalone-executables.md),
/// so the same program lowered twice, at other addresses, gives the same
/// text.
pub fn listing(program: &Program, image: &Image, options: Options) -> Result<String, Vec<String>> {
    let mut audit = Audit::new(program, image, true);
    compile_audited(program, image, &[], options, &mut audit)?;
    Ok(audit.listing.unwrap_or_default())
}

/// The code generator for this machine. `pic`: position-independent code,
/// for an object file (without it, outside symbols are absolute addresses
/// in the code, which macOS can't relocate: standalone-executables.md
/// §1.2); the JIT places its code itself.
pub(crate) fn host_isa(pic: bool) -> Result<cranelift_codegen::isa::OwnedTargetIsa, String> {
    let mut flags = settings::builder();
    let set = |flags: &mut settings::Builder, name: &str, value: &str| {
        flags.set(name, value).map_err(|e| e.to_string())
    };
    set(&mut flags, "opt_level", "speed")?;
    set(&mut flags, "is_pic", if pic { "true" } else { "false" })?;
    // Cranelift's `return_call` needs frame pointers on x86-64 (stage N0).
    set(&mut flags, "preserve_frame_pointers", "true")?;
    // The steps left live in the pinned register (the module comment).
    set(&mut flags, "enable_pinned_reg", "true")?;
    // Probe the stack of every frame of a page or more, a page at a time
    // (SW-1157): a frame can pass a page (a body with many live values), and
    // an unprobed one could step over the guard page. A frame under a page
    // gets no probe, so the usual body costs nothing. Cranelift has no
    // outline probes on aarch64.
    set(&mut flags, "enable_probestack", "true")?;
    set(&mut flags, "probestack_strategy", "inline")?;
    set(&mut flags, "probestack_size_log2", "12")?;
    cranelift_native::builder()
        .map_err(|e| format!("this machine isn't supported: {e}"))?
        .finish(settings::Flags::new(flags))
        .map_err(|e| e.to_string())
}

fn compile_audited(
    program: &Program,
    image: &Image,
    roots: &[u32],
    options: Options,
    audit: &mut Audit,
) -> Result<Compiled, Vec<String>> {
    preflight()?;
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    if let Some(why) = crate::map_jit::jit_unavailable() {
        return Err(vec![why]);
    }
    let plan = plan(program, image, roots)?;
    let dump = std::env::var_os("STITCHWORT_NATIVE_DUMP").is_some();
    let start = Instant::now();
    let fail = |e: String| vec![format!("compiling to native code failed: {e}")];
    let isa = host_isa(false).map_err(fail)?;
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
    let Emitted {
        functions,
        adapters,
        lambda_of,
        trampolines,
        n_caches,
        max_frame,
        widest,
        ..
    } = emit(
        &mut module,
        program,
        image,
        &plan,
        options,
        dump,
        audit,
        false,
    )?;
    module
        .finalize_definitions()
        .map_err(|e| fail(e.to_string()))?;

    let mut table = vec![std::ptr::null::<u8>(); program.globals.len()].into_boxed_slice();
    for (g, global) in program.globals.iter().enumerate() {
        if let Some((id, _)) = adapters.get(&(g as u32)) {
            table[g] = module.get_finalized_function(*id);
            if dump {
                eprintln!("@@ {:p} {}", table[g], global.name);
            }
        }
    }
    let mut lambdas = vec![std::ptr::null::<u8>(); image.lambda_code.len()].into_boxed_slice();
    for (&code, &l) in &lambda_of {
        lambdas[l as usize] = module.get_finalized_function(functions[&code]);
        if dump {
            eprintln!("@@ {:p} lambda #{l}", lambdas[l as usize]);
        }
    }
    let address = |id: FuncId| module.get_finalized_function(id);
    // SAFETY: each is a finished trampoline of its kind (`emit`), in this
    // module's code, which is never unmapped (`_module`).
    #[allow(unsafe_code)]
    let (enter, constants, apply, step) = unsafe {
        let mut constants = vec![None; program.globals.len()];
        for &(g, id) in &trampolines.constants {
            constants[g as usize] = Some(trampoline::<abi::EnterTrampoline>(address(id)));
        }
        (
            trampoline::<abi::EnterTrampoline>(address(trampolines.enter)),
            constants.into_boxed_slice(),
            [
                trampoline::<abi::ApplyTrampoline>(address(trampolines.apply[0])),
                trampoline::<abi::ApplyTrampoline>(address(trampolines.apply[1])),
            ],
            trampolines
                .step
                .map(|id| trampoline::<abi::StepTrampoline>(address(id))),
        )
    };
    Ok(Compiled {
        module,
        code: CrossingCode {
            functions: table,
            lambdas,
            enter,
            constants,
            apply,
            step,
            max_frame,
            resumes: plan.effects,
        },
        n_caches,
        widest: body_name(program, image, widest),
        bodies: plan.bodies.len(),
        compile_time: start.elapsed(),
    })
}

/// A body's source locations as [`Stretch`]es covering its `size` bytes:
/// what Cranelift leaves out (moves at a block's start) is `Untagged`, or
/// `Prologue` before the first tagged code (the arguments moved to their
/// registers). Untagged code between two stretches of the same
/// instruction and part (the moves and constants of its blocks) is taken
/// as theirs, and neighbours alike are merged.
fn stretches(
    locs: &[cranelift_codegen::MachSrcLoc<cranelift_codegen::Final>],
    size: u32,
) -> Vec<Stretch> {
    let mut out: Vec<Stretch> = Vec::new();
    let mut push = |start: u32, end: u32, pc: Option<u32>, part: Part| {
        if start >= end {
            return;
        }
        match out.last_mut() {
            Some(last) if last.end == start && last.pc == pc && last.part == part => {
                last.end = end;
            }
            _ => out.push(Stretch {
                start,
                end,
                pc,
                part,
            }),
        }
    };
    let mut at = 0;
    let mut tagged = false;
    for loc in locs {
        let (pc, part) = Part::of(loc.loc);
        let (gap, part) = match (tagged, part) {
            (false, Part::Untagged) => (Part::Prologue, Part::Prologue),
            (false, _) => (Part::Prologue, part),
            (true, _) => (Part::Untagged, part),
        };
        tagged |= part != Part::Prologue;
        push(at, loc.start, None, gap);
        push(loc.start, loc.end, pc, part);
        at = at.max(loc.end);
    }
    push(at, size, None, Part::Untagged);
    let mut merged: Vec<Stretch> = Vec::with_capacity(out.len());
    for s in out {
        if let [.., before, gap] = &merged[..]
            && gap.part == Part::Untagged
            && (before.pc, before.part) == (s.pc, s.part)
        {
            merged.pop();
        }
        match merged.last_mut() {
            Some(last) if (last.pc, last.part) == (s.pc, s.part) => last.end = s.end,
            _ => merged.push(s),
        }
    }
    merged
}

/// What [`emit`] declared in the module.
pub(crate) struct Emitted {
    /// Each body's function.
    pub(crate) functions: BTreeMap<u32, FuncId>,
    /// Each compiled global function's adapter (its entry as a function
    /// value), and its body.
    pub(crate) adapters: BTreeMap<u32, (FuncId, u32)>,
    /// Which bodies are lambdas', and whose.
    pub(crate) lambda_of: BTreeMap<u32, u32>,
    /// The trampolines from the runtime into the code.
    pub(crate) trampolines: Trampolines,
    /// How many `Apply` sites the code has, each with a cache in the
    /// tables (`abi::Tables::caches`).
    pub(crate) n_caches: usize,
    /// A bound on the stack one level of recursion uses (`frames`).
    pub(crate) max_frame: usize,
    /// The body with the widest frame.
    pub(crate) widest: u32,
    /// Under [`Options::pc_map`], each body's map.
    pub(crate) pc_map: Option<Vec<BodyMap>>,
}

/// The check that generated code holds no host address (stage S4 of
/// docs/proposals/standalone-executables.md), run on each function before
/// it's compiled: in debug builds (so every native test runs it), no
/// integer constant may be an address in the host memory the code could
/// otherwise have named: the image's constants, bodies, operand lists and
/// tables, the program and its shapes and globals, and the runtime's
/// helpers. Nothing in the generator makes a pointer constant
/// (`Gen::address` is gone); this catches one coming back. [`listing`]
/// also keeps each function's IR, for the test that it's the same text
/// wherever the program is in memory.
pub(crate) struct Audit {
    /// Sorted, disjoint enough to search: `[start, end)` of each host
    /// object. Empty in release builds.
    host: Vec<(u64, u64)>,
    listing: Option<String>,
}

impl Audit {
    pub(crate) fn new(program: &Program, image: &Image, listing: bool) -> Audit {
        let mut host = Vec::new();
        if cfg!(debug_assertions) || listing {
            fn span<T>(host: &mut Vec<(u64, u64)>, items: &[T]) {
                // An empty slice's pointer is a dangling one (its
                // alignment), not an object.
                if size_of_val(items) > 0 {
                    let start = items.as_ptr() as u64;
                    host.push((start, start + size_of_val(items) as u64));
                }
            }
            fn one<T>(host: &mut Vec<(u64, u64)>, item: &T) {
                span(host, std::slice::from_ref(item));
            }
            one(&mut host, program);
            one(&mut host, &program.shapes);
            span(&mut host, &program.globals);
            one(&mut host, image);
            span(&mut host, &image.pool);
            span(&mut host, &image.codes);
            span(&mut host, &image.global_code);
            span(&mut host, &image.lambda_code);
            for code in &image.codes {
                span(&mut host, &code.instrs);
                span(&mut host, &code.ops);
                span(&mut host, &code.tables);
                span(&mut host, &code.num_tables);
                for table in &code.tables {
                    span(&mut host, table);
                }
            }
            for (_, address) in helper_addresses() {
                host.push((address as u64, address as u64 + 1));
            }
            host.sort_unstable();
        }
        Audit {
            host,
            listing: listing.then(String::new),
        }
    }

    /// Checks `func`, and keeps its text for a listing.
    fn function(&mut self, func: &ir::Function) -> Result<(), String> {
        if let Some(listing) = &mut self.listing {
            listing.push_str(&func.display().to_string());
            listing.push('\n');
        }
        if self.host.is_empty() {
            return Ok(());
        }
        for block in func.layout.blocks() {
            for inst in func.layout.block_insts(block) {
                if let ir::InstructionData::UnaryImm {
                    opcode: ir::Opcode::Iconst,
                    imm,
                } = func.dfg.insts[inst]
                {
                    let n = imm.bits() as u64;
                    // The last object starting at or before `n`.
                    let i = self.host.partition_point(|(start, _)| *start <= n);
                    if i > 0 && n < self.host[i - 1].1 {
                        return Err(format!(
                            "internal error: the code holds the host address {n:#x} ({})",
                            func.dfg.display_inst(inst)
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}

/// Generates the code of `plan`'s bodies, the adapters and `Apply` stubs,
/// and a trampoline for each number of arguments, into `module`: the code
/// generator, apart from where the code goes (stage S4 of
/// docs/proposals/standalone-executables.md), so the JIT and an object file
/// get the same code. The code holds no host address: what it needs of the
/// host's memory it reaches through `Context::tables`, by number.
/// `export_trampolines`: the trampolines are exported as `sw_cross_enter`,
/// `sw_cross_apply1` and the others (for an object file) rather than local.
#[allow(clippy::too_many_arguments)]
pub(crate) fn emit(
    module: &mut dyn Module,
    program: &Program,
    image: &Image,
    plan: &Plan,
    options: Options,
    dump: bool,
    audit: &mut Audit,
    export_trampolines: bool,
) -> Result<Emitted, Vec<String>> {
    let fail = |e: String| vec![format!("native: compiling failed: {e}")];
    let frontend_config = module.target_config();
    let pointer = frontend_config.pointer_type();
    let call_conv = module.isa().default_call_conv();

    // Which bodies are lambdas' (they take their closure last).
    let lambda_of: BTreeMap<u32, u32> = image
        .lambda_code
        .iter()
        .enumerate()
        .filter(|(_, code)| plan.bodies.contains(code))
        .map(|(l, code)| (*code, l as u32))
        .collect();
    // Every body, declared first so that they can call each other.
    let symbols = body_symbols(program, image);
    let mut functions: BTreeMap<u32, FuncId> = BTreeMap::new();
    for &code in &plan.bodies {
        let params = image.codes[code as usize].params;
        let signature = if lambda_of.contains_key(&code) {
            value_signature(pointer, params)
        } else {
            body_signature(pointer, params)
        };
        let id = module
            .declare_function(&symbols[&code], Linkage::Local, &signature)
            .map_err(|e| fail(e.to_string()))?;
        functions.insert(code, id);
    }
    // Each compiled global function's entry as a function value: it takes
    // the function value last, as a lambda's body takes its closure, so
    // that `Apply` calls both the same way. A copy taking a reuse token is
    // never a function value (`Program::validate`), so it has none.
    let mut adapters: BTreeMap<u32, (FuncId, u32)> = BTreeMap::new();
    for (g, global) in program.globals.iter().enumerate() {
        if let GlobalKind::Function { params, .. } = global.kind
            && !matches!(global.reuse, Reuse::Copy { .. })
            && let Some(code) = image.global_code[g]
            && plan.bodies.contains(&code)
        {
            let id = module
                .declare_function(
                    &format!("{}/value", global.name),
                    Linkage::Local,
                    &value_signature(pointer, params),
                )
                .map_err(|e| fail(e.to_string()))?;
            adapters.insert(g as u32, (id, code));
        }
    }
    // The arities `Apply` may call, and the shared slow path of `Apply`
    // for each number of arguments a site passes.
    let arities: BTreeSet<u32> = plan
        .bodies
        .iter()
        .filter(|code| lambda_of.contains_key(code))
        .map(|code| image.codes[*code as usize].params)
        .chain(
            adapters
                .values()
                .map(|(_, code)| image.codes[*code as usize].params),
        )
        .collect();
    let mut apply_any: BTreeMap<u32, FuncId> = BTreeMap::new();
    for &code in &plan.bodies {
        for instr in &image.codes[code as usize].instrs {
            let n = match instr {
                Instr::Apply { args, .. } | Instr::TailApply { args, .. } => args.len,
                // An inline `bind c k` applies `k` to one value (`Gen::bind`).
                Instr::Prim {
                    op: PrimOp::Effect(EffectOp::Bind),
                    args,
                    ..
                }
                | Instr::TailPrim {
                    op: PrimOp::Effect(EffectOp::Bind),
                    args,
                } if args.len == 2 => 1,
                _ => continue,
            };
            if let std::collections::btree_map::Entry::Vacant(slot) = apply_any.entry(n) {
                let id = module
                    .declare_function(
                        &format!("apply{n}"),
                        Linkage::Local,
                        &apply_signature(pointer, n),
                    )
                    .map_err(|e| fail(e.to_string()))?;
                slot.insert(id);
            }
        }
    }
    // The compiled `Text.fold`, which applies its function through `apply2`.
    let text_fold = if plan.folds {
        if let std::collections::btree_map::Entry::Vacant(slot) = apply_any.entry(2) {
            let id = module
                .declare_function("apply2", Linkage::Local, &apply_signature(pointer, 2))
                .map_err(|e| fail(e.to_string()))?;
            slot.insert(id);
        }
        Some(
            module
                .declare_function("rt_text_fold", Linkage::Local, &body_signature(pointer, 3))
                .map_err(|e| fail(e.to_string()))?,
        )
    } else {
        None
    };
    // The effect runtime's bodies (stage NO2 of native-only.md), which apply
    // continuations to one value and a fold's clause to two, and (stage
    // NO3) a state-passing handler's clause to four.
    let runtime = if plan.effects {
        let counts: &[u32] = if plan.states { &[1, 2, 4] } else { &[1, 2] };
        for &n in counts {
            if let std::collections::btree_map::Entry::Vacant(slot) = apply_any.entry(n) {
                let id = module
                    .declare_function(
                        &format!("apply{n}"),
                        Linkage::Local,
                        &apply_signature(pointer, n),
                    )
                    .map_err(|e| fail(e.to_string()))?;
                slot.insert(id);
            }
        }
        Some(runtime::Runtime {
            run_loop: module
                .declare_function("rt_loop", Linkage::Local, &runtime::loop_signature(pointer))
                .map_err(|e| fail(e.to_string()))?,
            resume: module
                .declare_function(
                    "rt_resume",
                    Linkage::Local,
                    &runtime::resume_signature(pointer),
                )
                .map_err(|e| fail(e.to_string()))?,
            states: plan.states,
        })
    } else {
        None
    };
    // The runner applies functions to one or two values (stage NO4 of
    // native-only.md), through these stubs.
    for n in [1, 2] {
        if let std::collections::btree_map::Entry::Vacant(slot) = apply_any.entry(n) {
            let id = module
                .declare_function(
                    &format!("apply{n}"),
                    Linkage::Local,
                    &apply_signature(pointer, n),
                )
                .map_err(|e| fail(e.to_string()))?;
            slot.insert(id);
        }
    }
    let helpers =
        Helpers::declare(module, pointer, call_conv, options.count_bodies).map_err(fail)?;
    let numbering = Numbering::of(image);
    let mut caches = 0u32;
    let mut context = module.make_context();
    let mut builder_context = FunctionBuilderContext::new();
    let mut max_frame = 0;
    let mut widest = image.entry_code;
    let mut pc_map = options.pc_map.then(Vec::new);
    // With `STITCHWORT_NATIVE_PARTS=n`, every body has a register file and
    // is compiled in parts of `n` instructions, so that the tests can run
    // small programs the way a large body is compiled.
    let (variable_registers, part_instrs) = match std::env::var("STITCHWORT_NATIVE_PARTS")
        .ok()
        .and_then(|n| n.parse::<usize>().ok())
    {
        Some(n) => (0, n.max(1)),
        None => (VARIABLE_REGISTERS, PART_INSTRS),
    };
    for &code in &plan.bodies {
        let body = &image.codes[code as usize];
        let params = body.params;
        let lambda = lambda_of.get(&code).copied();
        // A body with borrowed parameters holds lent values, which a
        // register file's error exits would drop: its registers are
        // variables whatever its size (`borrow::MAX_REGS` keeps it small).
        let lends = body.borrowed.iter().any(|b| *b);
        let in_file = !lends && (body.regs > variable_registers || body.instrs.len() > part_instrs);
        // A body with a register file is compiled in parts of at most
        // `part_instrs` instructions, each its own function, so that no
        // function Cranelift is given grows with the program; the first is
        // the body's, and the rest are entered by tail calls
        // (`part_signature`).
        let mut parts: Vec<(usize, FuncId)> = vec![(0, functions[&code])];
        if in_file {
            for (k, start) in (part_instrs..body.instrs.len())
                .step_by(part_instrs)
                .enumerate()
            {
                let id = module
                    .declare_function(
                        &format!("{}/part{}", symbols[&code], k + 1),
                        Linkage::Local,
                        &part_signature(pointer),
                    )
                    .map_err(|e| fail(e.to_string()))?;
                parts.push((start, id));
            }
        }
        let full = if in_file {
            Vec::new()
        } else {
            maybe_full(body)
        };
        let first = if in_file { first_fills(body) } else { None };
        let (leaders, entries) = leaders(body, &parts);
        let entry_name = if options.count_bodies {
            Some(define_name(module, &symbols[&code]).map_err(fail)?)
        } else {
            None
        };
        for (part, &(start, id)) in parts.iter().enumerate() {
            let end = parts.get(part + 1).map_or(body.instrs.len(), |p| p.0);
            context.func.signature = if part > 0 {
                part_signature(pointer)
            } else if lambda.is_some() {
                value_signature(pointer, params)
            } else {
                body_signature(pointer, params)
            };
            context.func.name = ir::UserFuncName::user(0, id.as_u32());
            let symbol = if part == 0 {
                symbols[&code].clone()
            } else {
                format!("{}/part{part}", symbols[&code])
            };
            {
                let b = FunctionBuilder::new(&mut context.func, &mut builder_context);
                let mut generator = Gen {
                    b,
                    module: &mut *module,
                    program,
                    image,
                    code_index: code,
                    code: body,
                    lambda,
                    functions: &functions,
                    apply_any: &apply_any,
                    text_fold,
                    runtime,
                    helpers: &helpers,
                    refs: BTreeMap::new(),
                    signatures: BTreeMap::new(),
                    numbering: &numbering,
                    caches: &mut caches,
                    pointer,
                    options,
                    vars: Vec::new(),
                    file: None,
                    in_file,
                    parts: &parts,
                    range: start..end,
                    stubs: BTreeMap::new(),
                    exits: BTreeMap::new(),
                    leaders: &leaders,
                    entries: &entries[part],
                    spill: StackSlot::from_u32(0),
                    temps: StackSlot::from_u32(0),
                    pointers: StackSlot::from_u32(0),
                    fun: StackSlot::from_u32(0),
                    full: &full,
                    first_fills: first.as_deref(),
                    blocks: BTreeMap::new(),
                    top: None,
                    trap: Block::from_u32(0),
                    ctx: IrValue::from_u32(0),
                    frames: IrValue::from_u32(0),
                    env: None,
                    entry_name: if part == 0 { entry_name } else { None },
                    slot: 0,
                };
                generator.body();
                generator.b.seal_all_blocks();
                generator.b.finalize(frontend_config);
            }
            let name = if part == 0 {
                body_name(program, image, code)
            } else {
                format!("{} (part {part})", body_name(program, image, code))
            };
            if dump {
                context.set_disasm(true);
                eprintln!("==== {name} (body{code})\n{}", context.func.display());
            }
            audit
                .function(&context.func)
                .map_err(|e| fail(format!("{name} ({e})")))?;
            module
                .define_function(id, &mut context)
                .map_err(|e| fail(format!("{name} ({e:?})")))?;
            if let Some(compiled) = context.compiled_code() {
                let bound = frames::frame_bound(&context.func, compiled);
                if bound > max_frame {
                    (max_frame, widest) = (bound, code);
                }
                if let Some(map) = &mut pc_map {
                    let size = compiled.code_buffer().len() as u32;
                    map.push(BodyMap {
                        symbol,
                        size,
                        instrs: body.instrs.iter().map(|i| format!("{i:?}")).collect(),
                        stretches: stretches(compiled.buffer.get_srclocs_sorted(), size),
                    });
                }
            }
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
    }
    let mut adapter_frame = 0;
    let mut stub_frame = 0;
    for (&g, &(id, code)) in &adapters {
        let params = image.codes[code as usize].params;
        context.func.signature = value_signature(pointer, params);
        context.func.name = ir::UserFuncName::user(2, g);
        {
            let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
            emit_adapter(
                &mut b,
                &mut *module,
                &helpers,
                functions[&code],
                params,
                pointer,
            );
            b.seal_all_blocks();
            b.finalize(frontend_config);
        }
        audit.function(&context.func).map_err(fail)?;
        module
            .define_function(id, &mut context)
            .map_err(|e| fail(format!("adapter: {e:?}")))?;
        if let Some(compiled) = context.compiled_code() {
            adapter_frame = adapter_frame.max(frames::frame_bound(&context.func, compiled));
        }
        module.clear_context(&mut context);
    }
    let cap = arities.iter().copied().max().unwrap_or(0);
    for (&n, &id) in &apply_any {
        context.func.signature = apply_signature(pointer, n);
        context.func.name = ir::UserFuncName::user(3, n);
        {
            let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
            emit_apply_any(
                &mut b,
                &mut *module,
                &helpers,
                n,
                &arities,
                // Every count the plan holds: a partial application's held
                // arguments (fewer than its head takes) and the new ones
                // (`Text.fold`'s three, if it may be applied).
                n + if text_fold.is_some() { cap.max(3) } else { cap },
                pointer,
                text_fold,
                runtime,
            );
            b.seal_all_blocks();
            b.finalize(frontend_config);
        }
        if dump {
            eprintln!("==== apply{n}\n{}", context.func.display());
        }
        audit.function(&context.func).map_err(fail)?;
        module
            .define_function(id, &mut context)
            .map_err(|e| fail(format!("apply{n}: {e:?}")))?;
        if let Some(compiled) = context.compiled_code() {
            stub_frame = stub_frame.max(frames::frame_bound(&context.func, compiled));
        }
        module.clear_context(&mut context);
    }
    let mut fold_frame = 0;
    if let Some(id) = text_fold {
        context.func.signature = body_signature(pointer, 3);
        context.func.name = ir::UserFuncName::user(4, 0);
        {
            let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
            emit_text_fold(&mut b, &mut *module, &helpers, apply_any[&2], pointer);
            b.seal_all_blocks();
            b.finalize(frontend_config);
        }
        if dump {
            eprintln!("==== rt_text_fold\n{}", context.func.display());
        }
        audit.function(&context.func).map_err(fail)?;
        module
            .define_function(id, &mut context)
            .map_err(|e| fail(format!("rt_text_fold: {e:?}")))?;
        if let Some(compiled) = context.compiled_code() {
            fold_frame = frames::frame_bound(&context.func, compiled);
        }
        module.clear_context(&mut context);
    }
    // The effect runtime's bodies.
    let mut runtime_frame = 0;
    if let Some(ids) = runtime {
        let emit = runtime::Emit {
            helpers: &helpers,
            apply_any: &apply_any,
            runtime: ids,
            pointer,
            call_tag: program.shapes.call,
        };
        for (name, id, signature) in [
            ("rt_loop", ids.run_loop, runtime::loop_signature(pointer)),
            ("rt_resume", ids.resume, runtime::resume_signature(pointer)),
        ] {
            context.func.signature = signature;
            context.func.name = ir::UserFuncName::user(5, id.as_u32());
            {
                let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
                if id == ids.run_loop {
                    runtime::emit_loop(&mut b, &mut *module, &mut caches, &emit);
                } else {
                    runtime::emit_resume(&mut b, &mut *module, &mut caches, &emit);
                }
                b.seal_all_blocks();
                b.finalize(frontend_config);
            }
            if dump {
                eprintln!("==== {name}\n{}", context.func.display());
            }
            audit.function(&context.func).map_err(fail)?;
            module
                .define_function(id, &mut context)
                .map_err(|e| fail(format!("{name}: {e:?}")))?;
            if let Some(compiled) = context.compiled_code() {
                runtime_frame = runtime_frame.max(frames::frame_bound(&context.func, compiled));
            }
            module.clear_context(&mut context);
        }
    }

    // The trampolines from the runtime into the code (stage NO4 of
    // native-only.md), in the host's calling convention: into the entry
    // body, into the apply stubs for one and two arguments, and into the
    // effect runtime's loop.
    let entry_body = functions[&image.entry_code];
    let mut trampoline_ids = Vec::new();
    let mut kinds = vec![
        Trampoline::Enter,
        Trampoline::Apply(1),
        Trampoline::Apply(2),
    ];
    if runtime.is_some() {
        kinds.push(Trampoline::Step);
    }
    kinds.extend(plan.roots.iter().map(|&g| Trampoline::Constant(g)));
    for kind in kinds {
        let mut signature = ir::Signature::new(call_conv);
        for _ in 0..kind.params() {
            signature.params.push(AbiParam::new(pointer));
        }
        let (name, linkage) = if export_trampolines {
            (format!("sw_cross_{}", kind.name()), Linkage::Export)
        } else {
            (format!("cross_{}", kind.name()), Linkage::Local)
        };
        let id = module
            .declare_function(&name, linkage, &signature)
            .map_err(|e| fail(e.to_string()))?;
        context.func.signature = signature;
        context.func.name = ir::UserFuncName::user(kind.namespace(), kind.number());
        {
            let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let p = b.block_params(entry).to_vec();
            let (ctx, out) = (p[0], p[p.len() - 1]);
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
            let words = |b: &mut FunctionBuilder<'_>, at: IrValue, values: usize| {
                let mut words = Vec::new();
                for i in 0..values * 3 {
                    words.push(b.ins().load(
                        types::I64,
                        MemFlagsData::trusted(),
                        at,
                        (i * 8) as i32,
                    ));
                }
                words
            };
            let zero = b.ins().iconst(types::I64, 0);
            let (callee, call_args) = match kind {
                // The entry body, its frame counted by the runtime.
                Trampoline::Enter => (entry_body, vec![ctx, frames]),
                // A root constant's body, as the entry's.
                Trampoline::Constant(g) => {
                    let code = image.global_code[g as usize].expect("a constant has code");
                    (functions[&code], vec![ctx, frames])
                }
                // The stub, with nothing for it to drop: `(context, frames,
                // drops, closure, function value, arguments)`.
                Trampoline::Apply(n) => {
                    let mut call_args = vec![ctx, frames, zero, zero];
                    call_args.extend(words(&mut b, p[1], 1));
                    call_args.extend(words(&mut b, p[2], n as usize));
                    (apply_any[&n], call_args)
                }
                // The loop, from the computation with nothing pending and
                // no state, for the handler: `(context, frames, computation,
                // pending, state, handler, function value, closure)`.
                Trampoline::Step => {
                    let mut call_args = vec![ctx, frames];
                    call_args.extend(words(&mut b, p[1], 1));
                    call_args.extend([zero; 6]);
                    call_args.extend([p[2], zero, zero]);
                    let ids = runtime.expect("the effect runtime");
                    (ids.run_loop, call_args)
                }
            };
            let callee = module.declare_func_in_func(callee, b.func);
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
        audit.function(&context.func).map_err(fail)?;
        module
            .define_function(id, &mut context)
            .map_err(|e| fail(format!("trampoline: {e:?}")))?;
        module.clear_context(&mut context);
        trampoline_ids.push((kind, id));
    }
    let trampoline_of = |kind: Trampoline| {
        trampoline_ids
            .iter()
            .find(|(k, _)| *k == kind)
            .map(|(_, id)| *id)
    };
    let trampolines = Trampolines {
        enter: trampoline_of(Trampoline::Enter).expect("an entry trampoline"),
        apply: [
            trampoline_of(Trampoline::Apply(1)).expect("an apply trampoline"),
            trampoline_of(Trampoline::Apply(2)).expect("an apply trampoline"),
        ],
        step: trampoline_of(Trampoline::Step),
        constants: plan
            .roots
            .iter()
            .map(|&g| {
                let id = trampoline_of(Trampoline::Constant(g)).expect("a constant's trampoline");
                (g, id)
            })
            .collect(),
    };
    // A Stitchwort frame can be a body (an adapter tail-calls it, taking its
    // place), reached through an apply stub that may stay on the stack while
    // it runs, and through the compiled `Text.fold` (stage NO1 of
    // native-only.md: one runtime frame per level): the bound for one level
    // of recursion is the larger of body and adapter, a stub, and the fold.
    // With the effect runtime's bodies (stage NO2), in place of the fold
    // there may be the loop or a resumption (never both: the resumption
    // tail-calls the loop, and the loop's resumption is a tail call from
    // the stub) and a second stub: a stub applying a resumption to more
    // than one argument calls `rt_resume`, which applies the rest of the
    // computation through another. So the larger of the two bodies and a
    // stub, or the fold, whichever is more.
    if dump {
        eprintln!(
            "frames: bodies {max_frame}, adapters {adapter_frame}, apply stubs {stub_frame}, fold {fold_frame}, runtime {runtime_frame}"
        );
    }
    let effects_frame = if runtime.is_some() {
        runtime_frame + stub_frame
    } else {
        0
    };
    let max_frame = max_frame.max(adapter_frame) + stub_frame + fold_frame.max(effects_frame);
    Ok(Emitted {
        functions,
        adapters,
        lambda_of,
        trampolines,
        n_caches: caches as usize,
        max_frame,
        widest,
        pc_map,
    })
}

/// A trampoline from the runtime into the code (stage NO4 of
/// docs/proposals/native-only.md; `abi::Crossing`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Trampoline {
    /// Into the entry body: `abi::EnterTrampoline`.
    Enter,
    /// Into the apply stub for this many arguments: `abi::ApplyTrampoline`.
    Apply(u32),
    /// Into the effect runtime's loop: `abi::StepTrampoline`.
    Step,
    /// Into the body of a constant compiled as a root, by global:
    /// `abi::EnterTrampoline`.
    Constant(u32),
}

impl Trampoline {
    /// How many pointer-sized parameters it takes.
    fn params(self) -> usize {
        match self {
            Trampoline::Enter | Trampoline::Constant(_) => 2,
            Trampoline::Apply(_) | Trampoline::Step => 4,
        }
    }

    /// Its name, after `sw_cross_` (exported) or `cross_`.
    fn name(self) -> String {
        match self {
            Trampoline::Enter => "enter".to_string(),
            Trampoline::Apply(n) => format!("apply{n}"),
            Trampoline::Step => "step".to_string(),
            Trampoline::Constant(g) => format!("constant{g}"),
        }
    }

    /// The namespace of its IR name: the constants' are numbered apart.
    fn namespace(self) -> u32 {
        match self {
            Trampoline::Constant(_) => 6,
            _ => 1,
        }
    }

    /// A number for its IR name.
    fn number(self) -> u32 {
        match self {
            Trampoline::Enter => 0,
            Trampoline::Apply(n) => n,
            Trampoline::Step => u32::MAX,
            Trampoline::Constant(g) => g,
        }
    }
}

/// The trampolines [`emit`] made.
pub(crate) struct Trampolines {
    pub(crate) enter: FuncId,
    /// For one and two arguments.
    pub(crate) apply: [FuncId; 2],
    /// If the code has the effect runtime.
    pub(crate) step: Option<FuncId>,
    /// For each root constant, by global.
    pub(crate) constants: Vec<(u32, FuncId)>,
}

/// The code at `pointer` as a trampoline of type `T` (one of
/// `abi::EnterTrampoline`, `ApplyTrampoline` and `StepTrampoline`).
///
/// # Safety
/// `pointer` is a finished trampoline of that type, in code that is never
/// unmapped (`Islands::_module`).
#[allow(unsafe_code)]
unsafe fn trampoline<T: Copy>(pointer: *const u8) -> T {
    assert_eq!(size_of::<T>(), size_of::<*const u8>());
    // SAFETY: the caller's contract; `T` is a function pointer type.
    unsafe { std::mem::transmute_copy::<*const u8, T>(&pointer) }
}
/// A global body's signature: the context, the frames pending with its own
/// (the module comment), and three words per argument, returning three
/// words, in the `tail` convention.
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

/// A later part of a body compiled in parts (`PART_INSTRS`), entered by a
/// tail call from another part of the same frame: the context, the frames
/// pending, the register file, the closure (a lambda's; 0 otherwise) and
/// the instruction to go on from; returning the body's three words.
fn part_signature(pointer: ir::Type) -> ir::Signature {
    let mut signature = ir::Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    for _ in 0..3 {
        signature.returns.push(AbiParam::new(types::I64));
    }
    signature
}

/// How a function value is called (a lambda's body, a global function's
/// adapter): a body's signature, then the function value's address word
/// (its `Rc`'s, which the callee owns: a closure's, for `Captured`, or a
/// global function's, which its adapter drops; 0 for none).
fn value_signature(pointer: ir::Type, params: u32) -> ir::Signature {
    let mut signature = body_signature(pointer, params);
    signature.params.push(AbiParam::new(pointer));
    signature
}

/// `Apply`'s slow path for `n` arguments ([`emit_apply_any`]): the context,
/// the frames pending without the callee, a function value to drop once the
/// function value is taken apart (the resumption the effect runtime's
/// `rt_resume` has begun, as the machine drops the function value its
/// `apply` was given; or 0), a closure to drop after it (a tail apply's
/// own, or 0), the function value, and the arguments, three words each;
/// returning three words. (Until stage NO3 of native-only.md, also whether
/// it was a tail apply, for a tail request.)
fn apply_signature(pointer: ir::Type, n: u32) -> ir::Signature {
    let mut signature = ir::Signature::new(CallConv::Tail);
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(types::I64));
    signature.params.push(AbiParam::new(pointer));
    signature.params.push(AbiParam::new(pointer));
    for _ in 0..(n + 1) * 3 {
        signature.params.push(AbiParam::new(types::I64));
    }
    for _ in 0..3 {
        signature.returns.push(AbiParam::new(types::I64));
    }
    signature
}

/// Drops the function value whose address word is `fun` (not 0), inline:
/// its count goes down, and the runtime frees it if this was the last.
/// Function values aren't in the allocation trace, so this is inline under
/// the trace too (what freeing one releases goes through the runtime).
fn drop_fun(b: &mut FunctionBuilder<'_>, drop_words: FuncRef, fun: IrValue) {
    let strong = b.ins().load(types::I64, flags(), fun, STRONG_AT);
    let last = b.ins().icmp_imm_u(IntCC::Equal, strong, 1);
    let free = b.create_block();
    let keep = b.create_block();
    let after = b.create_block();
    b.ins().brif(last, free, &[], keep, &[]);
    b.switch_to_block(free);
    let tag = b.ins().iconst(types::I64, i64::from(TAG_FUN));
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().call(drop_words, &[tag, fun, zero]);
    b.ins().jump(after, &[]);
    b.switch_to_block(keep);
    let fewer = b.ins().iadd_imm_s(strong, -1);
    b.ins().store(flags(), fewer, fun, STRONG_AT);
    b.ins().jump(after, &[]);
    b.switch_to_block(after);
}

/// Drops the function values an apply stub put off (`abi::sw_defer_fun`),
/// if there are any (`drop` is `sw_drop_deferred`): right after the
/// function value a body or stub was given to drop, the innermost, as the
/// machine's nested `apply`s drop theirs (stage NO4 of native-only.md).
fn drop_deferred(b: &mut FunctionBuilder<'_>, drop: FuncRef, ctx: IrValue) {
    let n = b.ins().load(types::I64, flags(), ctx, Context::DEFERRED_AT);
    let dropping = b.create_block();
    let after = b.create_block();
    b.ins().brif(n, dropping, &[], after, &[]);
    b.switch_to_block(dropping);
    b.set_cold_block(dropping);
    b.ins().call(drop, &[ctx]);
    b.ins().jump(after, &[]);
    b.switch_to_block(after);
}

/// A global function's entry as a function value (`value_signature`):
/// drops the function value it was called through, then is the body. The
/// machine drops it at the same point (after pushing the frame, before the
/// body runs); a global's function value is never freed there anyway, as
/// the constants' cache keeps it.
fn emit_adapter(
    b: &mut FunctionBuilder<'_>,
    module: &mut dyn Module,
    helpers: &Helpers,
    body: FuncId,
    params: u32,
    pointer: ir::Type,
) {
    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let all = b.block_params(entry).to_vec();
    let fun = all[all.len() - 1];
    let drop_words = module.declare_func_in_func(helpers.drop_words, b.func);
    let is_fun = b.ins().icmp_imm_u(IntCC::NotEqual, fun, 0);
    let dropping = b.create_block();
    let call = b.create_block();
    b.ins().brif(is_fun, dropping, &[], call, &[]);
    b.switch_to_block(dropping);
    drop_fun(b, drop_words, fun);
    b.ins().jump(call, &[]);
    b.switch_to_block(call);
    let callee = module.declare_func_in_func(body, b.func);
    let args = &all[..2 + params as usize * 3];
    let _ = pointer;
    b.ins().return_call(callee, args);
}

/// The steps left, from the pinned register, written to the context as the
/// steps so far, for a helper that runs the machine.
fn steps_out(b: &mut FunctionBuilder<'_>, ctx: IrValue) {
    let left = b.ins().get_pinned_reg(types::I64);
    let limit = b
        .ins()
        .load(types::I64, flags(), ctx, Context::STEP_LIMIT_AT);
    let steps = b.ins().isub(limit, left);
    b.ins().store(flags(), steps, ctx, Context::STEPS_AT);
}

/// The steps so far, read back from the context into the pinned register
/// as the steps left, after a helper that runs the machine.
fn steps_in(b: &mut FunctionBuilder<'_>, ctx: IrValue) {
    let limit = b
        .ins()
        .load(types::I64, flags(), ctx, Context::STEP_LIMIT_AT);
    let steps = b.ins().load(types::I64, flags(), ctx, Context::STEPS_AT);
    let left = b.ins().isub(limit, steps);
    b.ins().set_pinned_reg(left);
}

/// `Apply`'s slow path for `n` arguments (`apply_signature`): the
/// machine's eval/apply. Each step is the runtime's `sw_apply_prepare` on a
/// plan in this frame (`ApplyPlan`, with room for `cap` values): a value
/// now (a partial application, a native's result, `Done`, or what the
/// machine computed for a function value without native code), or code to
/// call with a frame, counted as the machine's `enter` counts it, or one of
/// the runtime bodies to call with none (the compiled `Text.fold`, the
/// effect runtime's `rt_resume` and `rt_loop`). Then any over-application's
/// other arguments are applied to the result, the same way, until none are
/// left. A last call with nothing left over is a tail call, so a tail apply
/// stays in constant stack. Running out of steps or frames, or a callee's
/// error, releases what the plan holds.
#[allow(clippy::too_many_arguments)]
fn emit_apply_any(
    b: &mut FunctionBuilder<'_>,
    module: &mut dyn Module,
    helpers: &Helpers,
    n: u32,
    arities: &BTreeSet<u32>,
    cap: u32,
    pointer: ir::Type,
    text_fold: Option<FuncId>,
    runtime: Option<runtime::Runtime>,
) {
    let failed = b.create_block();
    let prepare = module.declare_func_in_func(helpers.apply_prepare, b.func);
    let release = module.declare_func_in_func(helpers.release, b.func);
    let unwind = module.declare_func_in_func(helpers.unwind, b.func);
    let drop_words = module.declare_func_in_func(helpers.drop_words, b.func);
    let drop_deferred_ref = module.declare_func_in_func(helpers.drop_deferred, b.func);
    let slot = |b: &mut FunctionBuilder<'_>, size: usize| {
        b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size as u32,
            3,
        ))
    };
    let fun_slot = slot(b, VALUE_SIZE);
    let in_slot = slot(b, VALUE_SIZE * (n as usize).max(1));
    let plan_slot = slot(b, ApplyPlan::ARGS_AT as usize + VALUE_SIZE * cap as usize);

    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let params = b.block_params(entry).to_vec();
    let (ctx, frames, drops, drop_env) = (params[0], params[1], params[2], params[3]);
    let fun_at = b.ins().stack_addr(pointer, fun_slot, 0);
    for w in 0..3 {
        b.ins()
            .store(flags(), params[4 + w], fun_at, (w * 8) as i32);
    }
    let in_at = b.ins().stack_addr(pointer, in_slot, 0);
    for i in 0..n as usize * 3 {
        b.ins().store(flags(), params[7 + i], in_at, (i * 8) as i32);
    }
    let plan = b.ins().stack_addr(pointer, plan_slot, 0);
    let cap_value = b.ins().iconst(types::I64, i64::from(cap));
    b.ins().store(flags(), cap_value, plan, ApplyPlan::CAP_AT);
    let count = b.ins().iconst(types::I64, i64::from(n));
    steps_out(b, ctx);
    b.ins()
        .call(prepare, &[ctx, frames, fun_at, in_at, count, plan]);
    steps_in(b, ctx);
    // A failure in `sw_apply_prepare` (in the machine, for a body that
    // isn't compiled), with the function value and the closure to drop if
    // they're still this frame's.
    let unprepared = b.create_block();
    b.append_block_param(unprepared, pointer);
    b.append_block_param(unprepared, pointer);
    let error = b.ins().load(types::I64, flags(), ctx, Context::ERROR_AT);
    let prepared = b.create_block();
    b.ins().brif(
        error,
        unprepared,
        &[drops.into(), drop_env.into()],
        prepared,
        &[],
    );
    // What the plan says, with the function value and the closure to drop
    // (`settle`).
    let settle = b.create_block();
    b.append_block_param(settle, pointer);
    b.append_block_param(settle, pointer);
    b.switch_to_block(prepared);
    b.ins().jump(settle, &[drops.into(), drop_env.into()]);
    b.switch_to_block(settle);
    let drops_left = b.block_params(settle)[0];
    let env_left = b.block_params(settle)[1];
    let code = b.ins().load(pointer, flags(), plan, ApplyPlan::CODE_AT);
    let resuming = b.create_block();
    let looping = b.create_block();
    let not_resuming = b.create_block();
    if runtime.is_some() {
        let is_resume = b
            .ins()
            .icmp_imm_u(IntCC::Equal, code, abi::RESUME_CODE as i64);
        let other = b.create_block();
        b.ins().brif(is_resume, resuming, &[], other, &[]);
        b.switch_to_block(other);
        let is_loop = b
            .ins()
            .icmp_imm_u(IntCC::Equal, code, abi::LOOP_CODE as i64);
        b.ins().brif(is_loop, looping, &[], not_resuming, &[]);
    } else {
        b.ins().jump(not_resuming, &[]);
    }
    // The function value and the closure dropped as the machine drops the
    // function values its `apply`s were given and its frame's closure: after
    // the function value is taken apart (a resumption takes it further
    // first).
    b.switch_to_block(not_resuming);
    let dropping_list = b.create_block();
    let list_gone = b.create_block();
    b.ins().brif(drops_left, dropping_list, &[], list_gone, &[]);
    b.switch_to_block(dropping_list);
    drop_fun(b, drop_words, drops_left);
    drop_deferred(b, drop_deferred_ref, ctx);
    b.ins().jump(list_gone, &[]);
    b.switch_to_block(list_gone);
    let dropping = b.create_block();
    let dispatch = b.create_block();
    b.ins().brif(env_left, dropping, &[], dispatch, &[]);
    b.switch_to_block(dropping);
    drop_fun(b, drop_words, env_left);
    b.ins().jump(dispatch, &[]);

    b.switch_to_block(dispatch);
    let enter = b.create_block();
    let ready = b.create_block();
    let folding = b.create_block();
    if text_fold.is_some() {
        let is_fold = b
            .ins()
            .icmp_imm_u(IntCC::Equal, code, abi::FOLD_CODE as i64);
        let other = b.create_block();
        b.ins().brif(is_fold, folding, &[], other, &[]);
        b.switch_to_block(other);
    }
    b.ins().brif(code, enter, &[], ready, &[]);

    // A value now: the result, or applied to what's left.
    let again = b.create_block();
    for _ in 0..3 {
        b.append_block_param(again, types::I64);
    }
    b.switch_to_block(ready);
    let v: Vec<IrValue> = (0..3)
        .map(|w| {
            b.ins()
                .load(types::I64, flags(), plan, ApplyPlan::VALUE_AT + 8 * w)
        })
        .collect();
    let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
    let done = b.create_block();
    let v_args: Vec<ir::BlockArg> = v.iter().map(|x| (*x).into()).collect();
    b.ins().brif(rest, again, &v_args, done, &[]);
    b.switch_to_block(done);
    b.ins().return_(&v);

    // The result applied to the rest of an over-application.
    b.switch_to_block(again);
    let v = b.block_params(again).to_vec();
    for (w, x) in v.iter().enumerate() {
        b.ins().store(flags(), *x, fun_at, (w * 8) as i32);
    }
    let arity = b.ins().load(types::I64, flags(), plan, ApplyPlan::ARITY_AT);
    let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
    let skip = b.ins().imul_imm_s(arity, VALUE_SIZE as i64);
    let from = b.ins().iadd(plan, skip);
    let from = b.ins().iadd_imm_s(from, i64::from(ApplyPlan::ARGS_AT));
    let none = b.ins().iconst(pointer, 0);
    steps_out(b, ctx);
    b.ins()
        .call(prepare, &[ctx, frames, fun_at, from, rest, plan]);
    steps_in(b, ctx);
    let error = b.ins().load(types::I64, flags(), ctx, Context::ERROR_AT);
    b.ins().brif(
        error,
        unprepared,
        &[none.into(), none.into()],
        settle,
        &[none.into(), none.into()],
    );

    // A runtime body's value: the result if nothing is left over (then it
    // was a tail call), else applied to the rest, as for a call.
    let runtime_call = |b: &mut FunctionBuilder<'_>, callee: FuncRef, call_args: &[IrValue]| {
        let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
        let tail = b.create_block();
        let call = b.create_block();
        b.ins().brif(rest, call, &[], tail, &[]);
        b.switch_to_block(tail);
        b.ins().return_call(callee, call_args);
        b.switch_to_block(call);
        let called = b.ins().call(callee, call_args);
        let r: Vec<ir::BlockArg> = b
            .inst_results(called)
            .to_vec()
            .into_iter()
            .map(Into::into)
            .collect();
        let error = b.ins().load(types::I64, flags(), ctx, Context::ERROR_AT);
        b.ins().brif(error, failed, &[], again, &r);
    };

    // An eager resumption, or a state-passing handler's function of the
    // state: the effect runtime's `rt_resume` on the plan's value and the
    // function value (the plan's `env`), with no step or frame of its own,
    // as the machine's `enter` runs `resume`; given the closure still to
    // drop.
    b.switch_to_block(resuming);
    match runtime {
        Some(runtime) => {
            let resume = module.declare_func_in_func(runtime.resume, b.func);
            // The function value this stub was given to drop is put off
            // until the resumption has taken its `rest` apart (stage NO4):
            // the machine's `apply` drops it once the nested `apply`s of
            // `resume` have returned.
            let defer = module.declare_func_in_func(helpers.defer_fun, b.func);
            let dropping = b.create_block();
            let gone = b.create_block();
            b.ins().brif(drops_left, dropping, &[], gone, &[]);
            b.switch_to_block(dropping);
            b.ins().call(defer, &[ctx, drops_left]);
            b.ins().jump(gone, &[]);
            b.switch_to_block(gone);
            let mut call_args = vec![ctx, frames];
            for i in 0..3 {
                call_args.push(
                    b.ins()
                        .load(types::I64, flags(), plan, ApplyPlan::ARGS_AT + 8 * i),
                );
            }
            call_args.push(b.ins().load(types::I64, flags(), plan, ApplyPlan::ENV_AT));
            call_args.push(env_left);
            runtime_call(b, resume, &call_args);
        }
        None => {
            b.set_cold_block(resuming);
            b.ins().trap(TrapCode::unwrap_user(4));
        }
    }

    // An effect native that runs a loop, applied (stage NO3): the effect
    // runtime's `rt_loop` on the plan's value (the computation) and handler
    // (the plan's `env`), with nothing pending and no state, as the
    // machine's `enter` runs `effect`; given the function value and the
    // closure still to drop, which it drops once it has begun.
    b.switch_to_block(looping);
    match runtime {
        Some(runtime) => {
            let run_loop = module.declare_func_in_func(runtime.run_loop, b.func);
            let mut call_args = vec![ctx, frames];
            for i in 0..3 {
                call_args.push(
                    b.ins()
                        .load(types::I64, flags(), plan, ApplyPlan::ARGS_AT + 8 * i),
                );
            }
            let zero = b.ins().iconst(types::I64, 0);
            call_args.extend([zero; 6]);
            call_args.push(b.ins().load(types::I64, flags(), plan, ApplyPlan::ENV_AT));
            call_args.extend([drops_left, env_left]);
            runtime_call(b, run_loop, &call_args);
        }
        None => {
            b.set_cold_block(looping);
            b.ins().trap(TrapCode::unwrap_user(4));
        }
    }

    // Code to call: a step and a frame, as the machine's `enter_frame`.
    b.switch_to_block(enter);
    let out_of_steps = b.create_block();
    let counted = b.create_block();
    let left = b.ins().get_pinned_reg(types::I64);
    let none_left = b.ins().icmp_imm_u(IntCC::Equal, left, 0);
    b.ins().brif(none_left, out_of_steps, &[], counted, &[]);
    b.switch_to_block(counted);
    let fewer = b.ins().iadd_imm_s(left, -1);
    b.ins().set_pinned_reg(fewer);
    let limit = b
        .ins()
        .load(types::I64, flags(), ctx, Context::FRAME_LIMIT_AT);
    let mut over = b
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, frames, limit);
    let sp = b.ins().get_stack_pointer(pointer);
    let floor = b
        .ins()
        .load(types::I64, flags(), ctx, Context::STACK_LIMIT_AT);
    let low = b.ins().icmp(IntCC::UnsignedLessThan, sp, floor);
    over = b.ins().bor(over, low);
    let out_of_frames = b.create_block();
    let entering = b.create_block();
    b.ins().brif(over, out_of_frames, &[], entering, &[]);
    b.switch_to_block(entering);
    let pushed = b.ins().iadd_imm_s(frames, 1);
    let arity = b.ins().load(types::I64, flags(), plan, ApplyPlan::ARITY_AT);
    let trap = b.create_block();
    let mut switch = Switch::new();
    let mut arms = Vec::new();
    for &k in arities {
        let arm = b.create_block();
        switch.set_entry(u128::from(k), arm);
        arms.push((k, arm));
    }
    switch.emit(b, arity, trap);
    for (k, arm) in arms {
        b.switch_to_block(arm);
        let mut call_args = vec![ctx, pushed];
        for i in 0..k as i32 * 3 {
            call_args.push(
                b.ins()
                    .load(types::I64, flags(), plan, ApplyPlan::ARGS_AT + 8 * i),
            );
        }
        call_args.push(b.ins().load(pointer, flags(), plan, ApplyPlan::ENV_AT));
        let signature = b.import_signature(value_signature(pointer, k));
        let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
        let tail = b.create_block();
        let call = b.create_block();
        b.ins().brif(rest, call, &[], tail, &[]);
        b.switch_to_block(tail);
        b.ins().return_call_indirect(signature, code, &call_args);
        b.switch_to_block(call);
        let called = b.ins().call_indirect(signature, code, &call_args);
        let r: Vec<ir::BlockArg> = b
            .inst_results(called)
            .to_vec()
            .into_iter()
            .map(Into::into)
            .collect();
        let error = b.ins().load(types::I64, flags(), ctx, Context::ERROR_AT);
        b.ins().brif(error, failed, &[], again, &r);
    }
    b.switch_to_block(trap);
    b.set_cold_block(trap);
    b.ins().trap(TrapCode::unwrap_user(4));

    // `Text.fold` applied (its three values first in the plan): the
    // compiled one, with no step or frame of its own, as the machine's
    // `enter` runs `fold_start`.
    b.switch_to_block(folding);
    match text_fold {
        Some(fold) => {
            let fold = module.declare_func_in_func(fold, b.func);
            let mut call_args = vec![ctx, frames];
            for i in 0..9 {
                call_args.push(
                    b.ins()
                        .load(types::I64, flags(), plan, ApplyPlan::ARGS_AT + 8 * i),
                );
            }
            runtime_call(b, fold, &call_args);
        }
        None => {
            b.set_cold_block(folding);
            b.ins().trap(TrapCode::unwrap_user(4));
        }
    }

    // Out of steps or frames before the call: the plan's values and closure
    // released.
    let release_all = b.create_block();
    b.switch_to_block(out_of_steps);
    b.set_cold_block(out_of_steps);
    let over = b.ins().iconst(types::I64, -1);
    b.ins().set_pinned_reg(over);
    let error = b.ins().iconst(types::I64, OUT_OF_STEPS as i64);
    b.ins().store(flags(), error, ctx, Context::ERROR_AT);
    b.ins().jump(release_all, &[]);
    b.switch_to_block(out_of_frames);
    b.set_cold_block(out_of_frames);
    let error = b.ins().iconst(types::I64, OUT_OF_FRAMES as i64);
    b.ins().store(flags(), error, ctx, Context::ERROR_AT);
    b.ins().jump(release_all, &[]);
    b.switch_to_block(release_all);
    b.set_cold_block(release_all);
    let arity = b.ins().load(types::I64, flags(), plan, ApplyPlan::ARITY_AT);
    let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
    // As the machine's `push` returning its error, which drops its
    // parameters last to first: the rest of an over-application (in the
    // `Ret`), the closure, then the arguments.
    let values = b.ins().iadd_imm_s(plan, i64::from(ApplyPlan::ARGS_AT));
    let skip = b.ins().imul_imm_s(arity, VALUE_SIZE as i64);
    let from = b.ins().iadd(values, skip);
    b.ins().call(release, &[from, rest]);
    let env = b.ins().load(pointer, flags(), plan, ApplyPlan::ENV_AT);
    let dropping = b.create_block();
    let gone = b.create_block();
    b.ins().brif(env, dropping, &[], gone, &[]);
    b.switch_to_block(dropping);
    drop_fun(b, drop_words, env);
    b.ins().jump(gone, &[]);
    b.switch_to_block(gone);
    b.ins().call(release, &[values, arity]);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[zero, zero, zero]);

    // The machine failed in `sw_apply_prepare`: the function value, the
    // over-application's rest (the plan's only values then) and the
    // closure released.
    b.switch_to_block(unprepared);
    b.set_cold_block(unprepared);
    let drops = b.block_params(unprepared)[0];
    let env = b.block_params(unprepared)[1];
    let dropping_fun = b.create_block();
    let fun_gone = b.create_block();
    b.ins().brif(drops, dropping_fun, &[], fun_gone, &[]);
    b.switch_to_block(dropping_fun);
    b.set_cold_block(dropping_fun);
    drop_fun(b, drop_words, drops);
    b.ins().jump(fun_gone, &[]);
    b.switch_to_block(fun_gone);
    let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
    let values = b.ins().iadd_imm_s(plan, i64::from(ApplyPlan::ARGS_AT));
    b.ins().call(release, &[values, rest]);
    let dropping = b.create_block();
    let leave = b.create_block();
    b.ins().brif(env, dropping, &[], leave, &[]);
    b.switch_to_block(dropping);
    b.set_cold_block(dropping);
    drop_fun(b, drop_words, env);
    b.ins().jump(leave, &[]);
    b.switch_to_block(leave);
    b.set_cold_block(leave);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[zero, zero, zero]);

    // A callee's error, with an over-application's rest still held: the
    // callee's frame holds the rest in its `Ret`, so it goes with the
    // frame's closure, in the group it just pushed.
    b.switch_to_block(failed);
    b.set_cold_block(failed);
    let arity = b.ins().load(types::I64, flags(), plan, ApplyPlan::ARITY_AT);
    let rest = b.ins().load(types::I64, flags(), plan, ApplyPlan::REST_AT);
    let skip = b.ins().imul_imm_s(arity, VALUE_SIZE as i64);
    let from = b.ins().iadd(plan, skip);
    let from = b.ins().iadd_imm_s(from, i64::from(ApplyPlan::ARGS_AT));
    let join = b.ins().iconst(types::I64, 3);
    let no_body = b.ins().iconst(types::I64, 0);
    b.ins().call(unwind, &[ctx, from, rest, join, no_body]);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[zero, zero, zero]);
}

/// The compiled `Text.fold text initial f` (stage NO1 of
/// docs/proposals/native-only.md), a runtime body with a global body's
/// signature (`body_signature`, three values, all moved in), but the frames
/// pending are the caller's: like the machine's `fold_start` and
/// `fold_step`, it counts no step and pushes no frame itself. It loops over
/// the characters from the last (each made by the leaf `sw_text_last`),
/// applying `f` to the character and the value so far as the machine's
/// `apply` does, with the step and the frame counted for each call: directly
/// if `f` is a global function or a closure taking two (`sw_apply_cached`,
/// once, since `f` doesn't change), otherwise through `apply2`. What the
/// machine keeps in `Ret::Fold` while a call runs (`f`, and the text) lives
/// in this frame instead.
///
/// The way out on an error is the machine's for a `Ret`: out of steps or
/// frames before a call, the character, the value so far and then `f` are
/// dropped at once (`push` drops its `Ret` and arguments; `f`'s last copy
/// is `apply`'s, dropped after them). A callee's error leaves `f` with the
/// callee's group in the unwind log, where the machine has it in the
/// callee frame's `Ret` (`sw_unwind`'s mode 3). The text isn't in the
/// allocation trace, so it's dropped whenever.
fn emit_text_fold(
    b: &mut FunctionBuilder<'_>,
    module: &mut dyn Module,
    helpers: &Helpers,
    apply2: FuncId,
    pointer: ir::Type,
) {
    let text_last = module.declare_func_in_func(helpers.text_last, b.func);
    let apply_cached = module.declare_func_in_func(helpers.apply_cached, b.func);
    let drop_words = module.declare_func_in_func(helpers.drop_words, b.func);
    let unwind = module.declare_func_in_func(helpers.unwind, b.func);
    let apply = module.declare_func_in_func(apply2, b.func);
    let slot = |b: &mut FunctionBuilder<'_>, size: usize| {
        b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            size as u32,
            3,
        ))
    };
    let t_slot = slot(b, VALUE_SIZE);
    let f_slot = slot(b, VALUE_SIZE);
    let c_slot = slot(b, VALUE_SIZE);
    let cache_slot = slot(b, size_of::<abi::ApplyCache>());

    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let params = b.block_params(entry).to_vec();
    let (ctx, frames) = (params[0], params[1]);
    let (t, z, f) = (&params[2..5], &params[5..8], &params[8..11]);
    let t_at = b.ins().stack_addr(pointer, t_slot, 0);
    let f_at = b.ins().stack_addr(pointer, f_slot, 0);
    for w in 0..3 {
        b.ins().store(flags(), t[w], t_at, (w * 8) as i32);
        b.ins().store(flags(), f[w], f_at, (w * 8) as i32);
    }
    let cache_at = b.ins().stack_addr(pointer, cache_slot, 0);
    let two = b.ins().iconst(types::I64, 2);
    let call = b.ins().call(apply_cached, &[ctx, f_at, two, cache_at]);
    let target = b.inst_results(call)[0];
    let looping = b.create_block();
    b.append_block_param(looping, types::I64);
    for _ in 0..3 {
        b.append_block_param(looping, types::I64);
    }
    let whole = b.ins().iconst(types::I64, -1);
    b.ins().jump(
        looping,
        &[whole.into(), z[0].into(), z[1].into(), z[2].into()],
    );

    // The next character from the end, if any.
    b.switch_to_block(looping);
    let p = b.block_params(looping).to_vec();
    let (end, acc) = (p[0], [p[1], p[2], p[3]]);
    let c_at = b.ins().stack_addr(pointer, c_slot, 0);
    let call = b.ins().call(text_last, &[ctx, t_at, end, c_at]);
    let next = b.inst_results(call)[0];
    let none_left = b.ins().icmp_imm_u(IntCC::Equal, next, -1);
    let finish = b.create_block();
    let got = b.create_block();
    b.ins().brif(none_left, finish, &[], got, &[]);
    b.switch_to_block(got);
    let c: Vec<IrValue> = (0..3)
        .map(|w| b.ins().load(types::I64, flags(), c_at, 8 * w))
        .collect();
    let direct = b.create_block();
    let slow = b.create_block();
    b.ins().brif(target, direct, &[], slow, &[]);

    let returned = b.create_block();
    for _ in 0..3 {
        b.append_block_param(returned, types::I64);
    }
    // `f`'s copy for the call, which the callee owns.
    let inc_f = |b: &mut FunctionBuilder<'_>| {
        let strong = b.ins().load(types::I64, flags(), f[1], STRONG_AT);
        let strong = b.ins().iadd_imm_s(strong, 1);
        b.ins().store(flags(), strong, f[1], STRONG_AT);
    };

    // A step and a frame, as the machine's `enter_frame`, then the call.
    b.switch_to_block(direct);
    let out_of_steps = b.create_block();
    let counted = b.create_block();
    let left = b.ins().get_pinned_reg(types::I64);
    let no_steps = b.ins().icmp_imm_u(IntCC::Equal, left, 0);
    b.ins().brif(no_steps, out_of_steps, &[], counted, &[]);
    b.switch_to_block(counted);
    let fewer = b.ins().iadd_imm_s(left, -1);
    b.ins().set_pinned_reg(fewer);
    let limit = b
        .ins()
        .load(types::I64, flags(), ctx, Context::FRAME_LIMIT_AT);
    let mut over = b
        .ins()
        .icmp(IntCC::UnsignedGreaterThanOrEqual, frames, limit);
    let sp = b.ins().get_stack_pointer(pointer);
    let floor = b
        .ins()
        .load(types::I64, flags(), ctx, Context::STACK_LIMIT_AT);
    let low = b.ins().icmp(IntCC::UnsignedLessThan, sp, floor);
    over = b.ins().bor(over, low);
    let out_of_frames = b.create_block();
    let entering = b.create_block();
    b.ins().brif(over, out_of_frames, &[], entering, &[]);
    b.switch_to_block(entering);
    inc_f(b);
    let pushed = b.ins().iadd_imm_s(frames, 1);
    let mut call_args = vec![ctx, pushed];
    call_args.extend(&c);
    call_args.extend(acc);
    call_args.push(f[1]);
    let signature = b.import_signature(value_signature(pointer, 2));
    let call = b.ins().call_indirect(signature, target, &call_args);
    let r: Vec<ir::BlockArg> = b.inst_results(call).iter().map(|x| (*x).into()).collect();
    b.ins().jump(returned, &r);

    // Anything else: the machine's eval/apply, in the stub.
    b.switch_to_block(slow);
    inc_f(b);
    let none = b.ins().iconst(pointer, 0);
    let mut call_args = vec![ctx, frames, none, none];
    call_args.extend(f);
    call_args.extend(&c);
    call_args.extend(acc);
    let call = b.ins().call(apply, &call_args);
    let r: Vec<ir::BlockArg> = b.inst_results(call).iter().map(|x| (*x).into()).collect();
    b.ins().jump(returned, &r);

    // The value so far, or the callee's error.
    b.switch_to_block(returned);
    let r = b.block_params(returned).to_vec();
    let error = b.ins().load(types::I64, flags(), ctx, Context::ERROR_AT);
    let failed = b.create_block();
    b.ins().brif(
        error,
        failed,
        &[],
        looping,
        &[next.into(), r[0].into(), r[1].into(), r[2].into()],
    );

    // The callee failed: `f` with its group, as the machine has it in the
    // callee frame's `Ret::Fold`.
    b.switch_to_block(failed);
    b.set_cold_block(failed);
    let one = b.ins().iconst(types::I64, 1);
    let join = b.ins().iconst(types::I64, 3);
    let no_body = b.ins().iconst(types::I64, 0);
    b.ins().call(unwind, &[ctx, f_at, one, join, no_body]);
    b.ins().call(drop_words, t);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[zero, zero, zero]);

    // Out of steps or frames before the call: as the machine's `push`.
    let unready = b.create_block();
    b.switch_to_block(out_of_steps);
    b.set_cold_block(out_of_steps);
    let over = b.ins().iconst(types::I64, -1);
    b.ins().set_pinned_reg(over);
    let error = b.ins().iconst(types::I64, OUT_OF_STEPS as i64);
    b.ins().store(flags(), error, ctx, Context::ERROR_AT);
    b.ins().jump(unready, &[]);
    b.switch_to_block(out_of_frames);
    b.set_cold_block(out_of_frames);
    let error = b.ins().iconst(types::I64, OUT_OF_FRAMES as i64);
    b.ins().store(flags(), error, ctx, Context::ERROR_AT);
    b.ins().jump(unready, &[]);
    b.switch_to_block(unready);
    b.set_cold_block(unready);
    b.ins().call(drop_words, &c);
    b.ins().call(drop_words, &acc);
    b.ins().call(drop_words, f);
    b.ins().call(drop_words, t);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[zero, zero, zero]);

    // No character left: `f` and the text dropped, as the machine drops the
    // `Fold` before delivering the value.
    b.switch_to_block(finish);
    b.ins().call(drop_words, f);
    b.ins().call(drop_words, t);
    b.ins().return_(&acc);
}

// ----------------------------------------------------------------- helpers

/// The runtime's helpers: `(name, address)`.
fn helper_addresses() -> Vec<(&'static str, *const u8)> {
    vec![
        ("sw_drop_words", abi::sw_drop_words as *const u8),
        ("sw_inc", abi::sw_inc as *const u8),
        ("sw_unwind", abi::sw_unwind as *const u8),
        ("sw_release_up", abi::sw_release_up as *const u8),
        ("sw_release_down", abi::sw_release_down as *const u8),
        ("sw_regs_new", abi::sw_regs_new as *const u8),
        ("sw_regs_free", abi::sw_regs_free as *const u8),
        ("sw_cell_new", abi::sw_cell_new as *const u8),
        ("sw_ctor_reuse", abi::sw_ctor_reuse as *const u8),
        ("sw_unpack", abi::sw_unpack as *const u8),
        ("sw_empty_cell", abi::sw_empty_cell as *const u8),
        ("sw_drop_reuse", abi::sw_drop_reuse as *const u8),
        ("sw_prim", abi::sw_prim as *const u8),
        ("sw_prim_owned", abi::sw_prim_owned as *const u8),
        ("sw_test", abi::sw_test as *const u8),
        ("sw_nat_pred", abi::sw_nat_pred as *const u8),
        ("sw_num_switch", abi::sw_num_switch as *const u8),
        ("sw_global", abi::sw_global as *const u8),
        ("sw_global_set", abi::sw_global_set as *const u8),
        ("sw_apply_cached", abi::sw_apply_cached as *const u8),
        ("sw_apply_prepare", abi::sw_apply_prepare as *const u8),
        ("sw_closure", abi::sw_closure as *const u8),
        ("sw_static_closure", abi::sw_static_closure as *const u8),
        ("sw_pap", abi::sw_pap as *const u8),
        ("sw_int_negative", abi::sw_int_negative as *const u8),
        ("sw_unary", abi::sw_unary as *const u8),
        ("sw_cell_free", abi::sw_cell_free as *const u8),
        ("sw_cell_cache_full", abi::sw_cell_cache_full as *const u8),
        ("sw_bind", abi::sw_bind as *const u8),
        ("sw_text_last", abi::sw_text_last as *const u8),
        ("sw_eff_begin", abi::sw_eff_begin as *const u8),
        ("sw_eff_state", abi::sw_eff_state as *const u8),
        ("sw_eff_step", abi::sw_eff_step as *const u8),
        ("sw_state_step", abi::sw_state_step as *const u8),
        ("sw_resume_begin", abi::sw_resume_begin as *const u8),
        ("sw_unwind_handler", abi::sw_unwind_handler as *const u8),
        ("sw_unwind_resume", abi::sw_unwind_resume as *const u8),
        ("sw_defer_fun", abi::sw_defer_fun as *const u8),
        ("sw_drop_deferred", abi::sw_drop_deferred as *const u8),
        ("sw_count_body", abi::sw_count_body as *const u8),
        ("sw_count_cell_hit", abi::sw_count_cell_hit as *const u8),
    ]
}

/// The helpers, declared in the module.
struct Helpers {
    drop_words: FuncId,
    inc: FuncId,
    unwind: FuncId,
    release: FuncId,
    release_down: FuncId,
    regs_new: FuncId,
    regs_free: FuncId,
    cell_new: FuncId,
    ctor_reuse: FuncId,
    unpack: FuncId,
    empty_cell: FuncId,
    drop_reuse: FuncId,
    prim: FuncId,
    prim_owned: FuncId,
    test: FuncId,
    nat_pred: FuncId,
    num_switch: FuncId,
    global: FuncId,
    global_set: FuncId,
    apply_cached: FuncId,
    apply_prepare: FuncId,
    closure: FuncId,
    static_closure: FuncId,
    pap: FuncId,
    int_negative: FuncId,
    unary: FuncId,
    cell_free: FuncId,
    cell_cache_full: FuncId,
    bind: FuncId,
    text_last: FuncId,
    eff_begin: FuncId,
    eff_state: FuncId,
    eff_step: FuncId,
    state_step: FuncId,
    resume_begin: FuncId,
    unwind_handler: FuncId,
    unwind_resume: FuncId,
    defer_fun: FuncId,
    drop_deferred: FuncId,
    /// Only under `Options::count_bodies`.
    count_body: Option<FuncId>,
    /// Only under `Options::count_bodies`: called on each inline cell-cache
    /// hit, which has no other hook.
    count_cell_hit: Option<FuncId>,
}

impl Helpers {
    fn declare(
        module: &mut dyn Module,
        pointer: ir::Type,
        cc: CallConv,
        count_bodies: bool,
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
            unwind: declare("sw_unwind", &[p, p, I64, I64, I64], &[])?,
            release: declare("sw_release_up", &[p, I64], &[])?,
            release_down: declare("sw_release_down", &[p, I64], &[])?,
            regs_new: declare("sw_regs_new", &[I64], &[p])?,
            regs_free: declare("sw_regs_free", &[p, I64], &[])?,
            cell_new: declare("sw_cell_new", &[I32, I64], &[I64])?,
            ctor_reuse: declare("sw_ctor_reuse", &[I32, p, I64, p, p], &[])?,
            unpack: declare("sw_unpack", &[p, I32, p, I64, I32], &[])?,
            empty_cell: declare("sw_empty_cell", &[I64, I64], &[])?,
            drop_reuse: declare("sw_drop_reuse", &[p, p], &[])?,
            prim: declare("sw_prim", &[p, I32, p, I64, p], &[])?,
            prim_owned: declare("sw_prim_owned", &[p, I32, p, I64, p], &[])?,
            test: declare("sw_test", &[p, I32, p, I64], &[I64])?,
            nat_pred: declare("sw_nat_pred", &[p, p], &[])?,
            num_switch: declare("sw_num_switch", &[p, I32, p], &[I64])?,
            global: declare("sw_global", &[p, I32, p], &[I64])?,
            global_set: declare("sw_global_set", &[p, I32, p], &[])?,
            apply_cached: declare("sw_apply_cached", &[p, p, I64, p], &[I64])?,
            apply_prepare: declare("sw_apply_prepare", &[p, I64, p, p, I64, p], &[])?,
            closure: declare("sw_closure", &[I32, p, I64, p], &[])?,
            static_closure: declare("sw_static_closure", &[p, I32, p], &[])?,
            pap: declare("sw_pap", &[p, I32, p, I64, p], &[])?,
            int_negative: declare("sw_int_negative", &[p], &[I64])?,
            unary: declare("sw_unary", &[p, I32, p, p], &[])?,
            cell_free: declare("sw_cell_free", &[I64, I64], &[])?,
            cell_cache_full: declare("sw_cell_cache_full", &[p, I64, I64], &[])?,
            bind: declare("sw_bind", &[p, p, p, p], &[I64])?,
            text_last: declare("sw_text_last", &[p, p, I64, p], &[I64])?,
            eff_begin: declare("sw_eff_begin", &[p, I32, p, p], &[I64])?,
            eff_state: declare("sw_eff_state", &[p, I32, p, p], &[])?,
            eff_step: declare("sw_eff_step", &[p, p, p, p, I64, p, p], &[I64])?,
            state_step: declare("sw_state_step", &[p, p, I64, p, p, p, p, p], &[I64])?,
            resume_begin: declare("sw_resume_begin", &[I64, p, p, p], &[I64])?,
            unwind_handler: declare("sw_unwind_handler", &[p, I64], &[])?,
            unwind_resume: declare("sw_unwind_resume", &[p, I64], &[])?,
            defer_fun: declare("sw_defer_fun", &[p, I64], &[])?,
            drop_deferred: declare("sw_drop_deferred", &[p], &[])?,
            count_body: if count_bodies {
                Some(declare("sw_count_body", &[p, I64], &[])?)
            } else {
                None
            },
            count_cell_hit: if count_bodies {
                Some(declare("sw_count_cell_hit", &[], &[])?)
            } else {
                None
            },
        })
    }
}

// ------------------------------------------------- registers maybe holding

/// The most registers a body keeps in Cranelift variables. An error exit
/// hands every register that may hold a value to the runtime, so a body
/// keeping them in variables writes each out at each of its exits: with
/// many registers live across many calls (a long list literal: each element
/// a call, all held until the list is built), code and compile time grow
/// with their product (SW-2557: 250 elements took 10 s and 2 GB to
/// compile). A body with more registers keeps them in a register file on
/// the heap instead, which an exit hands over whole, so every exit is a
/// call. Real bodies have at most about 40 registers.
const VARIABLE_REGISTERS: u32 = 128;

/// The most instructions a body is compiled in one function: Cranelift's
/// register allocator grows faster than the function, so a longer body (or
/// one with a register file) is compiled in parts of this many, which pass
/// the frame on by tail calls. Real bodies have at most about 170.
const PART_INSTRS: usize = 512;

/// A set of registers.
#[derive(Clone, PartialEq, Eq)]
struct Regs(Vec<u64>);

impl Regs {
    fn new(n: u32) -> Regs {
        Regs(vec![0; (n as usize).div_ceil(64).max(1)])
    }
    /// The empty set, for any number of registers.
    fn none() -> Regs {
        Regs(Vec::new())
    }
    fn has(&self, r: Reg) -> bool {
        self.0
            .get(r as usize / 64)
            .is_some_and(|w| w >> (r % 64) & 1 == 1)
    }
    fn add(&mut self, r: Reg) {
        self.0[r as usize / 64] |= 1 << (r % 64);
    }
    fn remove(&mut self, r: Reg) {
        if let Some(w) = self.0.get_mut(r as usize / 64) {
            *w &= !(1 << (r % 64));
        }
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

/// The instructions that start a block (the start, every target, what
/// follows a branch, and where each of `parts` starts), and for each part,
/// those of its instructions another part goes to.
fn leaders(code: &Code, parts: &[(usize, FuncId)]) -> (BTreeSet<usize>, Vec<BTreeSet<usize>>) {
    let n = code.instrs.len();
    let part_of = |pc: usize| parts.partition_point(|p| p.0 <= pc) - 1;
    let mut leaders: BTreeSet<usize> = parts.iter().map(|p| p.0).collect();
    let mut entries = vec![BTreeSet::new(); parts.len()];
    for pc in 0..n {
        let next = successors(code, pc);
        let falls = next == [pc + 1] && !matches!(code.instrs[pc], Instr::Jump { .. });
        if !falls {
            leaders.extend(next.iter().copied().filter(|s| *s < n));
            if pc + 1 < n {
                leaders.insert(pc + 1);
            }
        }
        for s in next.into_iter().filter(|s| *s < n) {
            if part_of(s) != part_of(pc) {
                entries[part_of(s)].insert(s);
            }
        }
    }
    (leaders, entries)
}

/// The instructions an instruction can go to next.
fn successors(code: &Code, pc: usize) -> Vec<usize> {
    match code.instrs[pc] {
        Instr::Jump { target } => vec![target as usize],
        Instr::JumpIfFalse { target, .. } | Instr::Test { target, .. } => {
            vec![pc + 1, target as usize]
        }
        Instr::NatCase { zero, .. } => vec![pc + 1, zero as usize],
        Instr::IntCase { neg, .. } => vec![pc + 1, neg as usize],
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

/// How a comparison of two numbers that fit a word is made inline: the
/// condition and the tag its operands must have, or `None` for any other
/// operation.
fn comparison(op: PrimOp) -> Option<(IntCC, u8)> {
    match op {
        PrimOp::Nat(Native::Leq) => Some((IntCC::UnsignedLessThanOrEqual, TAG_NAT)),
        PrimOp::Nat(Native::EqNat) => Some((IntCC::Equal, TAG_NAT)),
        PrimOp::IntEqual => Some((IntCC::Equal, TAG_INT)),
        PrimOp::Int(IntNative::IntLess) => Some((IntCC::SignedLessThan, TAG_INT)),
        PrimOp::Int(IntNative::IntLeq) => Some((IntCC::SignedLessThanOrEqual, TAG_INT)),
        _ => None,
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
        // A borrowed parameter is lent: never dropped here.
        if !code.borrows(r as usize) {
            start.add(r);
        }
    }
    before[0] = start;
    seen[0] = true;
    let mut work = vec![0usize];
    while let Some(pc) = work.pop() {
        let mut after = before[pc].clone();
        transfer(code, pc, &mut after);
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

/// Registers an instruction fills and empties, for [`transfer`].
trait Holding {
    fn fill(&mut self, r: Reg);
    fn empty(&mut self, r: Reg);
}

impl Holding for Regs {
    fn fill(&mut self, r: Reg) {
        self.add(r);
    }
    fn empty(&mut self, r: Reg) {
        self.remove(r);
    }
}

/// What instruction `pc` does to the registers that may hold a value.
fn transfer(code: &Code, pc: usize, after: &mut impl Holding) {
    let unmove = |after: &mut dyn FnMut(Reg), o: Ops| {
        for r in ops(code, o) {
            if r & MOVE != 0 {
                after(r & !MOVE);
            }
        }
    };
    match code.instrs[pc] {
        Instr::Move { dst, .. }
        | Instr::Const { dst, .. }
        | Instr::Captured { dst, .. }
        | Instr::Global { dst, .. }
        | Instr::StaticClosure { dst, .. }
        | Instr::NatPred { dst, .. }
        | Instr::IntOfNat { dst, .. }
        | Instr::IntNegSucc { dst, .. }
        | Instr::TextChars { dst, .. }
        | Instr::Field { dst, .. } => after.fill(dst),
        Instr::Prim { dst, args, .. } => {
            unmove(&mut |r| after.empty(r), args);
            after.fill(dst);
        }
        Instr::Take { dst, src } => {
            after.empty(src);
            after.fill(dst);
        }
        Instr::Drop { reg } => after.empty(reg),
        Instr::Call { dst, args, .. }
        | Instr::Pap { dst, args, .. }
        | Instr::Closure { dst, args, .. }
        | Instr::Ctor { dst, args, .. } => {
            unmove(&mut |r| after.empty(r), args);
            after.fill(dst);
        }
        Instr::CtorReuse {
            dst, args, token, ..
        } => {
            unmove(&mut |r| after.empty(r), args);
            after.empty(token);
            after.fill(dst);
        }
        Instr::Apply { dst, f, args } => {
            if f & MOVE != 0 {
                after.empty(f & !MOVE);
            }
            unmove(&mut |r| after.empty(r), args);
            after.fill(dst);
        }
        Instr::Unpack { src, fields, token } => {
            after.empty(src);
            for p in ops(code, fields).chunks(2) {
                if p[1] != NO_REG {
                    after.fill(p[1]);
                }
            }
            if token != NO_REG {
                after.fill(token);
            }
        }
        Instr::DropReuse { src, token } => {
            after.empty(src);
            after.fill(token);
        }
        // A lent value is held without a count, so never dropped.
        Instr::Peek { dst, .. } | Instr::Lend { dst, .. } => after.empty(dst),
        Instr::Forget { reg } => after.empty(reg),
        Instr::Own { reg } => after.fill(reg),
        _ => {}
    }
}

/// For a body with a register file (where `maybe_full` would take memory
/// growing with registers times instructions): for each register, the
/// first instruction that fills it (`u32::MAX` for none, 0 for a
/// parameter). With every jump forward, a register may hold a value before
/// `pc` only if one of the instructions before fills it; a self tail call
/// releases every register before it goes back to the start. `None` if a
/// jump goes back.
fn first_fills(code: &Code) -> Option<Vec<u32>> {
    struct First<'a>(&'a mut [u32], u32);
    impl Holding for First<'_> {
        fn fill(&mut self, r: Reg) {
            let first = &mut self.0[r as usize];
            *first = (*first).min(self.1);
        }
        fn empty(&mut self, _: Reg) {}
    }
    let mut first = vec![u32::MAX; code.regs as usize];
    first[..code.params as usize].fill(0);
    for pc in 0..code.instrs.len() {
        if successors(code, pc).iter().any(|s| *s <= pc) {
            return None;
        }
        transfer(code, pc, &mut First(&mut first, pc as u32));
    }
    Some(first)
}

// -------------------------------------------------------------- generation

/// A value in three words.
#[derive(Clone, Copy)]
struct Val([IrValue; 3]);

/// An application's arguments ([`Gen::apply`]): registers, taken once the
/// frame is counted, as `Apply` takes them; or values already taken (`bind`'s
/// `x`).
enum ApplyArgs {
    Regs(Ops),
    Vals(Vec<Val>),
}

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
    /// The lambda whose body this is, if it's a lambda's: it takes its
    /// closure last (`value_signature`).
    lambda: Option<u32>,
    functions: &'m BTreeMap<u32, FuncId>,
    /// `Apply`'s slow path, by the number of arguments (`emit_apply_any`).
    apply_any: &'m BTreeMap<u32, FuncId>,
    /// The compiled `Text.fold` (`emit_text_fold`), if anything uses it.
    text_fold: Option<FuncId>,
    /// The effect runtime's bodies (`runtime`), if anything uses effects.
    runtime: Option<runtime::Runtime>,
    helpers: &'m Helpers,
    refs: BTreeMap<FuncId, FuncRef>,
    signatures: BTreeMap<u32, SigRef>,
    numbering: &'m Numbering,
    /// How many `Apply` sites have been compiled: each has a cache, by
    /// number, in the tables.
    caches: &'m mut u32,
    pointer: ir::Type,
    options: Options,
    /// Each register's three words, as Cranelift variables, so that they
    /// live in machine registers (stage N2a). An empty register's words are
    /// all 0 (`Erased`).
    vars: Vec<[Variable; 3]>,
    /// In a body with more registers than [`VARIABLE_REGISTERS`]: its
    /// register file, `code.regs` values on the heap (`sw_regs_new`), which
    /// the registers live in instead of `vars`. `full` is then empty.
    file: Option<IrValue>,
    /// Whether the body has a register file (`file`, once made).
    in_file: bool,
    /// The body's parts: where each starts, and its function (the first is
    /// the body's own). One part unless the body has a register file.
    parts: &'m [(usize, FuncId)],
    /// The instructions this function compiles: a part of the body.
    range: std::ops::Range<usize>,
    /// Blocks that go on in another part, by the instruction they go to.
    stubs: BTreeMap<usize, Block>,
    /// With a register file, the shared error exits (`Gen::shared_exit`).
    exits: BTreeMap<Option<u64>, Block>,
    /// The instructions that start a block: the start, every target, what
    /// follows a branch, and where each part starts.
    leaders: &'m BTreeSet<usize>,
    /// The instructions of this part that other parts go on to.
    entries: &'m BTreeSet<usize>,
    /// Room for registers written out: for a helper that takes values by
    /// pointer, or to release them on an error exit.
    spill: StackSlot,
    /// Room for a constructor's fields and a helper's result.
    temps: StackSlot,
    /// Room for a native operation's argument pointers.
    pointers: StackSlot,
    /// An `Apply`'s function value.
    fun: StackSlot,
    /// Before each instruction, the registers that may hold a value
    /// (`maybe_full`); empty for a body with a register file, where every
    /// register may.
    full: &'m [Regs],
    /// With a register file, `first_fills`.
    first_fills: Option<&'m [u32]>,
    /// The block each leader instruction starts.
    blocks: BTreeMap<usize, Block>,
    /// Where the body starts, given its arguments: a self tail call jumps
    /// here. Only in the body's first part.
    top: Option<Block>,
    /// A switch on a tag outside its table: an internal error.
    trap: Block,
    ctx: IrValue,
    /// The frames pending, this one's included: an argument, so the count
    /// lives in a register and a return needs no decrement.
    frames: IrValue,
    /// In a lambda's body, its closure's address word: owned by the frame
    /// as the machine's frame owns its `env`, and dropped where the machine
    /// drops it (after the registers on a return; before them on a tail
    /// call; with them on an error exit).
    env: Option<IrValue>,
    /// Under `Options::count_bodies`, the data holding this body's symbol
    /// name and its length.
    entry_name: Option<(cranelift_module::DataId, u64)>,
    /// Under `Options::pc_map`, the instruction being compiled, as
    /// [`Part::at`] numbers it.
    slot: u32,
}

/// A reference from `func` to the data `id`, by its full address.
///
/// `declare_data_in_func` marks module-local data `colocated`, which lets
/// Cranelift reach it PC-relative (`lea` with a 32-bit displacement on
/// x86-64, `adrp` within ±4 GiB on aarch64). But the JIT's memory providers
/// map code and data separately, wherever `mmap` puts them, so nothing keeps
/// the two near: on Linux x86-64 they ended up over 2 GiB apart and
/// cranelift-jit panicked applying the relocation (SW-3139). Calls between
/// functions don't need this: cranelift-jit sends an out-of-range call
/// through a veneer, but has no such fallback for an address.
fn far_data(
    module: &mut dyn Module,
    id: cranelift_module::DataId,
    func: &mut ir::Function,
) -> ir::GlobalValue {
    let global = module.declare_data_in_func(id, func);
    if let ir::GlobalValueData::Symbol { colocated, .. } = &mut func.global_values[global] {
        *colocated = false;
    }
    global
}

/// Defines read-only data holding `name`, for a body to report itself by.
fn define_name(
    module: &mut dyn Module,
    name: &str,
) -> Result<(cranelift_module::DataId, u64), String> {
    let id = module
        .declare_data(&format!("{name}.name"), Linkage::Local, false, false)
        .map_err(|e| e.to_string())?;
    let mut data = cranelift_module::DataDescription::new();
    data.define(name.as_bytes().to_vec().into_boxed_slice());
    module.define_data(id, &data).map_err(|e| e.to_string())?;
    Ok((id, name.len() as u64))
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
    /// Runs `emit` with what it emits tagged as `part` of the current
    /// instruction, under [`Options::pc_map`]. Nested, the innermost part
    /// wins: a drop on an error exit is a `Dec`, not `Unwind`.
    fn tagged<R>(&mut self, part: Part, emit: impl FnOnce(&mut Self) -> R) -> R {
        if !self.options.pc_map {
            return emit(self);
        }
        let outer = self.b.srcloc();
        self.b.set_srcloc(part.at(self.slot));
        let r = emit(self);
        self.b.set_srcloc(outer);
        r
    }

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

    /// Where register `r` is when the body has a register file.
    fn in_file(&self, loc: Loc) -> Loc {
        match (loc, self.file) {
            (Loc::Reg(r), Some(file)) => Loc::Mem(file, (r as usize * VALUE_SIZE) as i32),
            _ => loc,
        }
    }

    fn load(&mut self, loc: Loc) -> Val {
        let loc = self.in_file(loc);
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
        let loc = self.in_file(loc);
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
        self.tagged(Part::Inc, |g| {
            let owns = g.owns(v);
            let trace = g.options.trace_refcounts;
            g.when(owns, false, |g| {
                if trace {
                    g.call_helper(g.helpers.inc, &v.0);
                } else {
                    let strong = g.b.ins().load(types::I64, flags(), v.0[1], STRONG_AT);
                    let strong = g.b.ins().iadd_imm_s(strong, 1);
                    g.b.ins().store(flags(), strong, v.0[1], STRONG_AT);
                }
            });
        });
        v
    }

    /// Drops a value native code holds.
    fn drop_value(&mut self, v: Val) {
        self.tagged(Part::Dec, |g| g.drop_value_untagged(v));
    }

    fn drop_value_untagged(&mut self, v: Val) {
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
        if self.may_hold(pc, r) {
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

    /// A call's operands for the body `callee`: one at a borrowed
    /// parameter is lent, its words passed without an increment (and,
    /// marked `MOVE`, the register left empty); the rest as [`Gen::operand`].
    fn call_operands(&mut self, o: Ops, callee: u32) -> Vec<Val> {
        let lend = &self.image.codes[callee as usize].borrowed;
        ops(self.code, o)
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(j, r)| {
                if lend.get(j) != Some(&true) {
                    return self.operand(r);
                }
                let reg = r & !MOVE;
                let v = self.load(Loc::Reg(reg));
                if r & MOVE != 0 {
                    self.erase(Loc::Reg(reg));
                }
                v
            })
            .collect()
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
    /// to `error` (unless a callee already did), gives up the registers in
    /// `live` (the registers that may hold a value at this point: registers
    /// live in variables, so each exit gives up its own), and returns.
    /// Otherwise continues.
    ///
    /// The values are not dropped here but handed to the runtime
    /// (`sw_unwind`), which drops them as the machine clears its registers
    /// after a failed run, so that the allocation trace is the same: lowest
    /// register first, outer frames before inner ones. `tail` is a tail
    /// call's operands: the machine has fetched them (moved, or cloned)
    /// when it runs out of steps, and drops them last.
    ///
    /// `extra` is dropped too: values held outside the registers (an
    /// `Apply`'s function value: the machine's local, dropped at once). A
    /// lambda's closure (the frame's `env`) is kept for the runtime too: the
    /// machine drops every frame's closure before any register.
    fn exit_with(
        &mut self,
        cond: IrValue,
        live: &Regs,
        error: Option<u64>,
        extra: &[Val],
        tail: &[Reg],
    ) {
        if self.in_file && extra.is_empty() && tail.is_empty() {
            let exit = self.shared_exit(error);
            let fine = self.b.create_block();
            self.b.ins().brif(cond, exit, &[], fine, &[]);
            self.b.switch_to_block(fine);
            return;
        }
        let exit = self.b.create_block();
        let fine = self.b.create_block();
        self.b.ins().brif(cond, exit, &[], fine, &[]);
        self.b.switch_to_block(exit);
        self.b.set_cold_block(exit);
        self.exit_now(live, error, extra, tail);
        self.b.switch_to_block(fine);
    }

    /// With a register file, an exit that holds nothing outside the
    /// registers is the same wherever it is, so each function has one for
    /// each error (`None`: a callee's), emitted after the instructions.
    fn shared_exit(&mut self, error: Option<u64>) -> Block {
        if let Some(block) = self.exits.get(&error) {
            return *block;
        }
        let block = self.b.create_block();
        self.b.set_cold_block(block);
        self.exits.insert(error, block);
        block
    }

    /// Leaves the frame on an error, as [`Gen::exit_with`] does when its
    /// condition holds (in the current block, which this ends).
    fn exit_now(&mut self, live: &Regs, error: Option<u64>, extra: &[Val], tail: &[Reg]) {
        self.tagged(Part::Unwind, |g| {
            g.exit_now_untagged(live, error, extra, tail)
        });
    }

    fn exit_now_untagged(&mut self, live: &Regs, error: Option<u64>, extra: &[Val], tail: &[Reg]) {
        if let Some(error) = error {
            if error == OUT_OF_STEPS {
                // One step over the limit, as the machine counts it.
                let over = self.iconst(u64::MAX);
                self.b.ins().set_pinned_reg(over);
            }
            let error = self.iconst(error);
            self.ctx_store(Context::ERROR_AT, error);
        }
        let kept = self.without_moved(live, tail);
        let fetched: Vec<Val> = tail.iter().map(|r| self.operand(*r)).collect();
        for v in extra {
            self.drop_value(*v);
        }
        for (i, v) in fetched.iter().enumerate() {
            self.spill_value(i, *v);
        }
        self.unwind(fetched.len(), true);
        self.unwind_env();
        if let Some(file) = self.file {
            // The whole file: the registers outside `kept` are `Erased`.
            let n = self.iconst(u64::from(self.code.regs));
            let mode = self.iconst(0);
            let body = self.iconst(u64::from(self.code_index));
            self.call_helper(self.helpers.unwind, &[self.ctx, file, n, mode, body]);
            self.leave();
            let zero = self.iconst(0);
            self.b.ins().return_(&[zero, zero, zero]);
            return;
        }
        let mut regs = kept.descending(self.code.regs);
        regs.reverse();
        for (i, r) in regs.iter().enumerate() {
            let v = self.load(Loc::Reg(*r));
            self.spill_value(i, v);
        }
        self.unwind(regs.len(), false);
        let zero = self.iconst(0);
        self.b.ins().return_(&[zero, zero, zero]);
    }

    /// Before the frame leaves (a return, a tail call, an exit): frees its
    /// register file, if it has one, which the frame has released or
    /// unwound by then.
    fn leave(&mut self) {
        if let Some(file) = self.file {
            let n = self.iconst(u64::from(self.code.regs));
            self.call_helper(self.helpers.regs_free, &[file, n]);
        }
    }

    /// Hands the first `n` spill slots' values to the runtime (`sw_unwind`).
    fn unwind(&mut self, n: usize, tail: bool) {
        self.unwind_mode(n, u64::from(tail));
    }

    fn unwind_mode(&mut self, n: usize, mode: u64) {
        if n == 0 && mode != 2 {
            return;
        }
        let at = self.spill_address(0);
        let count = self.iconst(n as u64);
        let mode = self.iconst(mode);
        // The frame's body, for the depth note (mode 2: one per frame).
        let body = self.iconst(u64::from(self.code_index));
        self.call_helper(self.helpers.unwind, &[self.ctx, at, count, mode, body]);
    }

    /// In a lambda's body, gives its closure (the frame's `env`) to the
    /// runtime, to be dropped before the registers.
    fn unwind_env(&mut self) {
        if let Some(env) = self.env {
            let tag = self.iconst(u64::from(TAG_FUN));
            let zero = self.iconst(0);
            self.spill_value(0, Val([tag, env, zero]));
            self.unwind_mode(1, 2);
        } else {
            // Every leaving frame pushes a group (the last frame's pending
            // arguments join it).
            self.unwind_mode(0, 2);
        }
    }

    /// In a lambda's body, drops its closure (the frame's `env`).
    fn drop_env(&mut self) {
        if let Some(env) = self.env {
            let drop_words = self.func_ref(self.helpers.drop_words);
            self.tagged(Part::Dec, |g| drop_fun(&mut g.b, drop_words, env));
        }
    }

    /// A frame entered: a step, out of steps if over the limit (`live`
    /// and `tail` as for [`Gen::exit_with`]).
    fn count_step(&mut self, live: &Regs, tail: &[Reg]) {
        self.count_step_with(live, &[], tail);
    }

    /// [`Gen::count_step`], with `extra` as for [`Gen::exit_with`].
    fn count_step_with(&mut self, live: &Regs, extra: &[Val], tail: &[Reg]) {
        // The steps left are in the pinned register: none left means this
        // step is one over the limit.
        self.tagged(Part::Check, |g| {
            let left = g.b.ins().get_pinned_reg(types::I64);
            let over = g.b.ins().icmp_imm_u(IntCC::Equal, left, 0);
            g.exit_with(over, live, Some(OUT_OF_STEPS), extra, tail);
            let left = g.b.ins().iadd_imm_s(left, -1);
            g.b.ins().set_pinned_reg(left);
        });
    }

    /// A frame about to be pushed: out of frames if as many are pending as
    /// the limit allows (or at the stack's safety margin). The frames
    /// pending with the new one, which the callee is given.
    fn push_frame(&mut self, live: &Regs) -> IrValue {
        self.push_frame_with(live, &[])
    }

    /// [`Gen::push_frame`], with `extra` as for [`Gen::exit_with`].
    fn push_frame_with(&mut self, live: &Regs, extra: &[Val]) -> IrValue {
        self.tagged(Part::Check, |g| g.push_frame_untagged(live, extra))
    }

    fn push_frame_untagged(&mut self, live: &Regs, extra: &[Val]) -> IrValue {
        let frames = self.frames;
        let limit = self.ctx_load(Context::FRAME_LIMIT_AT);
        let over = self
            .b
            .ins()
            .icmp(IntCC::UnsignedGreaterThanOrEqual, frames, limit);
        // The stack-pointer check: a backstop the build's stack sizing
        // keeps from firing (§3 of docs/proposals/native-only.md).
        let sp = self.b.ins().get_stack_pointer(self.pointer);
        let floor = self.ctx_load(Context::STACK_LIMIT_AT);
        let low = self.b.ins().icmp(IntCC::UnsignedLessThan, sp, floor);
        let either = self.b.ins().bor(over, low);
        self.exit_with(either, live, Some(OUT_OF_FRAMES), extra, &[]);
        self.b.ins().iadd_imm_s(frames, 1)
    }

    /// After a call returned `r`: its result. An error in the callee
    /// unwinds this frame too.
    fn call_result(&mut self, live: &Regs, r: &[IrValue]) -> Val {
        self.tagged(Part::Check, |g| g.call_result_untagged(live, r))
    }

    fn call_result_untagged(&mut self, live: &Regs, r: &[IrValue]) -> Val {
        let error = self.ctx_load(Context::ERROR_AT);
        let done = self.b.create_block();
        for _ in 0..3 {
            self.b.append_block_param(done, types::I64);
        }
        let args: Vec<ir::BlockArg> = r.iter().map(|x| (*x).into()).collect();
        if self.in_file {
            let fail = self.shared_exit(None);
            self.b.ins().brif(error, fail, &[], done, &args);
        } else {
            let fail = self.b.create_block();
            self.b.ins().brif(error, fail, &[], done, &args);
            self.b.switch_to_block(fail);
            self.b.set_cold_block(fail);
            self.exit_now(live, None, &[], &[]);
        }
        self.b.switch_to_block(done);
        let p = self.b.block_params(done);
        Val([p[0], p[1], p[2]])
    }

    /// Whether register `r` may hold a value before instruction `pc`.
    fn may_hold(&self, pc: usize, r: Reg) -> bool {
        if self.in_file {
            self.first_fills
                .is_none_or(|first| (first[r as usize] as usize) < pc)
        } else {
            self.full[pc].has(r)
        }
    }

    /// The registers that may hold a value before instruction `pc`, for an
    /// exit or a release; none with a register file, where both work on
    /// every register.
    fn live(&self, pc: usize) -> Regs {
        if self.file.is_some() {
            Regs::none()
        } else {
            self.full[pc].clone()
        }
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
        if let Some(file) = self.file {
            // Every register not in `regs` is `Erased`, so releasing them
            // all is the same; they're left `Erased`, so a second release
            // (or an exit after) finds nothing.
            let n = self.iconst(u64::from(self.code.regs));
            self.call_helper(self.helpers.release_down, &[file, n]);
            return;
        }
        for r in regs.descending(self.code.regs) {
            let v = self.load(Loc::Reg(r));
            self.drop_value(v);
        }
    }

    /// The block that runs instruction `pc` (a leader): its own in this
    /// part, or one that goes on in the part that has it.
    fn block_of(&mut self, pc: u32) -> Block {
        let pc = pc as usize;
        if self.range.contains(&pc) {
            return self.blocks[&pc];
        }
        if let Some(block) = self.stubs.get(&pc) {
            return *block;
        }
        let block = self.b.create_block();
        self.stubs.insert(pc, block);
        block
    }

    /// How a function value taking `params` is called (`value_signature`).
    fn value_sig(&mut self, params: u32) -> SigRef {
        if let Some(s) = self.signatures.get(&params) {
            return *s;
        }
        let s = self
            .b
            .import_signature(value_signature(self.pointer, params));
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
        let in_file = self.in_file;
        let n = code.instrs.len();
        let instrs = &code.instrs[self.range.clone()];
        let max_ops = instrs
            .iter()
            .map(|i| match i {
                Instr::Ctor { args, .. }
                | Instr::CtorReuse { args, .. }
                | Instr::Apply { args, .. }
                | Instr::TailApply { args, .. }
                | Instr::TailCall { args, .. }
                | Instr::Closure { args, .. }
                | Instr::Pap { args, .. }
                | Instr::Prim { args, .. }
                | Instr::TailPrim { args, .. } => args.len as usize,
                _ => 0,
            })
            .max()
            .unwrap_or(0);
        let max_prim = instrs
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
        let traced = if self.options.trace_refcounts && !in_file {
            code.regs as usize
        } else {
            0
        };
        let spills = released.max(traced).max(max_prim + 1).max(max_ops).max(3);
        self.spill = self.b.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            (spills * VALUE_SIZE) as u32,
            3,
        ));
        if !in_file {
            self.vars = (0..code.regs)
                .map(|_| std::array::from_fn(|_| self.b.declare_var(types::I64)))
                .collect();
        }
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

        let range = self.range.clone();
        for &pc in self.leaders.range(range.clone()) {
            let block = self.b.create_block();
            self.blocks.insert(pc, block);
        }

        let entry = self.b.create_block();
        self.b.append_block_params_for_function_params(entry);
        self.b.switch_to_block(entry);
        if self.options.pc_map {
            // The base every location is relative to: the smallest, so no
            // location is stored as Cranelift's "none".
            self.b.func.params.ensure_base_srcloc(Part::Entry.at(0));
            self.b.set_srcloc(Part::Entry.at(0));
        }
        self.trap = self.b.create_block();
        if range.start == 0 {
            self.first_part(entry);
        } else {
            self.later_part(entry);
        }

        self.b.switch_to_block(self.trap);
        self.b.set_cold_block(self.trap);
        self.b.ins().trap(TrapCode::unwrap_user(3));

        let mut open = false;
        for pc in range.clone() {
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
            if self.options.pc_map {
                self.slot = pc as u32 + 1;
                self.b.set_srcloc(Part::Work.at(self.slot));
            }
            open = self.instr(pc);
        }
        if open {
            if range.end < n {
                let next = self.block_of(range.end as u32);
                self.b.ins().jump(next, &[]);
            } else {
                self.b.ins().trap(TrapCode::unwrap_user(1));
            }
        }
        // Going on in another part: a tail call to it, with this frame's
        // state (`part_signature`).
        while let Some((pc, block)) = self.stubs.pop_first() {
            self.b.switch_to_block(block);
            let part = self.parts.partition_point(|p| p.0 <= pc) - 1;
            let f = self.func_ref(self.parts[part].1);
            let file = self.file.expect("a body in parts has a register file");
            let env = match self.env {
                Some(env) => env,
                None => self.b.ins().iconst(self.pointer, 0),
            };
            let at = self.iconst(pc as u64);
            let args = [self.ctx, self.frames, file, env, at];
            self.b.ins().return_call(f, &args);
        }
        let exits = std::mem::take(&mut self.exits);
        for (error, block) in exits {
            self.b.switch_to_block(block);
            self.slot = 0;
            self.exit_now(&Regs::none(), error, &[], &[]);
        }
    }

    /// The body's entry: the frame's state from the arguments, then on to
    /// `top`, where its registers are set from them.
    fn first_part(&mut self, entry: Block) {
        let code = self.code;
        let top = self.b.create_block();
        for _ in 0..code.params * 3 {
            self.b.append_block_param(top, types::I64);
        }
        self.top = Some(top);
        self.ctx = self.b.block_params(entry)[0];
        self.frames = self.b.block_params(entry)[1];
        if self.in_file {
            let n = self.iconst(u64::from(code.regs));
            self.file = Some(self.call_helper(self.helpers.regs_new, &[n])[0]);
        }
        let mut args: Vec<IrValue> = self.b.block_params(entry)[2..].to_vec();
        if self.lambda.is_some() {
            // The closure, last; a lambda's body never jumps back to its
            // top (only a global's own tail call does), so it stays put.
            self.env = args.pop();
        }
        let args: Vec<ir::BlockArg> = args.into_iter().map(Into::into).collect();
        self.b.ins().jump(top, &args);

        self.b.switch_to_block(top);
        if let (Some(count), Some((name, len))) = (self.helpers.count_body, self.entry_name) {
            // At `top`, so a self tail call counts as a call too.
            let global = far_data(&mut *self.module, name, self.b.func);
            let at = self.b.ins().symbol_value(self.pointer, global);
            let len = self.iconst(len);
            self.call_helper(count, &[at, len]);
        }
        let params: Vec<IrValue> = self.b.block_params(top).to_vec();
        for r in 0..code.params {
            let i = r as usize * 3;
            self.store(Loc::Reg(r), Val([params[i], params[i + 1], params[i + 2]]));
        }
        // A register file starts `Erased`, and is again when a self tail
        // call comes back here (it releases every register).
        if !self.in_file {
            for r in code.params..code.regs {
                self.erase(Loc::Reg(r));
            }
        }
        let first = self.blocks[&0];
        self.b.ins().jump(first, &[]);
    }

    /// A later part's entry: the frame's state from the part before, then
    /// on to the instruction it names, one of those another part goes to.
    fn later_part(&mut self, entry: Block) {
        let params = self.b.block_params(entry).to_vec();
        self.ctx = params[0];
        self.frames = params[1];
        self.file = Some(params[2]);
        if self.lambda.is_some() {
            self.env = Some(params[3]);
        }
        let mut switch = Switch::new();
        for &pc in self.entries {
            switch.set_entry(pc as u128, self.blocks[&pc]);
        }
        let trap = self.trap;
        switch.emit(&mut self.b, params[4], trap);
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
                if self.may_hold(pc, reg) {
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
            Instr::StaticClosure { dst, lambda } => {
                let out = self.temp_address(0);
                let lambda = self.i32const(lambda);
                self.call_helper(self.helpers.static_closure, &[self.ctx, lambda, out]);
                let v = self.load(Loc::Mem(out, 0));
                self.assign(pc, dst, v);
            }
            Instr::Call { dst, g, args } => {
                let live = self.live(pc);
                self.count_step(&live, &[]);
                let frames = self.push_frame(&live);
                let callee = self.image.global_code[g as usize].expect("a function has code");
                let values = self.call_operands(args, callee);
                let live = self.without_moved(&live, ops(code, args));
                let f = self.func_ref(self.functions[&callee]);
                let mut call_args = vec![self.ctx, frames];
                call_args.extend(Self::words(&values));
                let call = self.tagged(Part::Call, |g| g.b.ins().call(f, &call_args));
                let r = self.b.inst_results(call).to_vec();
                let v = self.call_result(&live, &r);
                self.assign(pc, dst, v);
            }
            Instr::TailCall { g, args } => {
                // As the machine's `replace`: the step, then this frame's
                // closure dropped, then its registers. What goes to a
                // borrowed parameter is lent (or holds no reference), so an
                // exit before the call doesn't take it.
                let callee = self.image.global_code[g as usize].expect("a function has code");
                let lend = &self.image.codes[callee as usize].borrowed;
                let owned: Vec<Reg> = ops(code, args)
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| lend.get(*j) != Some(&true))
                    .map(|(_, r)| *r)
                    .collect();
                self.count_step(&self.live(pc), &owned);
                let values = self.call_operands(args, callee);
                let left = self.without_moved(&self.live(pc), ops(code, args));
                self.drop_env();
                self.release(&left);
                let words: Vec<IrValue> = Self::words(&values).collect();
                if let (true, Some(top)) = (callee == self.code_index, self.top) {
                    let args: Vec<ir::BlockArg> = words.into_iter().map(Into::into).collect();
                    self.b.ins().jump(top, &args);
                } else {
                    let f = self.func_ref(self.functions[&callee]);
                    let mut call_args = vec![self.ctx, self.frames];
                    call_args.extend(words);
                    self.leave();
                    self.tagged(Part::Call, |g| g.b.ins().return_call(f, &call_args));
                }
                return false;
            }
            Instr::Apply { dst, f, args } => {
                // As the machine: the function value taken; then for a
                // closure or a global function taking exactly these
                // arguments (`exact`), a frame for its code, which is given
                // the function value; anything else goes through eval/apply
                // (`emit_apply_any`).
                let (fv, target) = self.apply_target(f, args.len);
                let live = self.without_moved(&self.live(pc), &[f]);
                self.apply(pc, dst, fv, target, &live, ApplyArgs::Regs(args));
            }
            Instr::TailApply { f, args } => {
                let (fv, target) = self.apply_target(f, args.len);
                let taken = self.without_moved(&self.live(pc), &[f]);
                self.tail_apply(fv, target, &taken, ApplyArgs::Regs(args));
                return false;
            }
            Instr::Return { src } => {
                // As the machine: the registers released, then the frame's
                // closure.
                let v = self.load(Loc::Reg(src));
                if self.file.is_some() {
                    self.erase(Loc::Reg(src));
                }
                let mut left = self.live(pc);
                left.remove(src);
                self.release(&left);
                self.drop_env();
                self.leave();
                self.tagged(Part::Return, |g| g.b.ins().return_(&v.0));
                return false;
            }
            Instr::Captured { dst, i } => {
                let env = self.env.expect("a capture is in a lambda's body");
                let captures =
                    self.b
                        .ins()
                        .load(self.pointer, flags(), env, RC_VALUE_AT + FUN_CAPTURES_AT);
                let v = self.clone_from(Loc::Mem(captures, (i as usize * VALUE_SIZE) as i32));
                self.assign(pc, dst, v);
            }
            Instr::Closure { dst, lambda, args } => {
                let values = self.operands(args);
                let lambda = self.i32const(lambda);
                let v = self.made(self.helpers.closure, &[lambda], &values);
                self.assign(pc, dst, v);
            }
            Instr::Pap { dst, g, args } => {
                let values = self.operands(args);
                let g = self.i32const(g);
                let v = self.made(self.helpers.pap, &[self.ctx, g], &values);
                self.assign(pc, dst, v);
            }
            Instr::IntCase { src, neg } => {
                let v = self.load(Loc::Reg(src));
                let int = self.is_tag(v, TAG_INT);
                let small = self.b.create_block();
                let big = self.b.create_block();
                let neg = self.block_of(neg);
                let next = self.block_of(pc as u32 + 1);
                self.b.ins().brif(int, small, &[], big, &[]);
                self.b.switch_to_block(small);
                let negative = self.b.ins().icmp_imm_s(IntCC::SignedLessThan, v.0[1], 0);
                self.b.ins().brif(negative, neg, &[], next, &[]);
                self.b.switch_to_block(big);
                self.b.set_cold_block(big);
                let at = self.spill_value(0, v);
                let r = self.call_helper(self.helpers.int_negative, &[at])[0];
                self.b.ins().brif(r, neg, &[], next, &[]);
                return false;
            }
            Instr::IntOfNat { dst, src } => self.unary(pc, dst, src, abi::UNARY_INT_OF_NAT),
            Instr::IntNegSucc { dst, src } => self.unary(pc, dst, src, abi::UNARY_INT_NEG_SUCC),
            Instr::TextChars { dst, src } => self.unary(pc, dst, src, abi::UNARY_TEXT_CHARS),
            Instr::Prim {
                dst,
                op: op @ PrimOp::Effect(_),
                args,
            } => self.effect(pc, Some(dst), op, args),
            Instr::TailPrim {
                op: op @ PrimOp::Effect(_),
                args,
            } => {
                self.effect(pc, None, op, args);
                return false;
            }
            Instr::Prim {
                dst,
                op: PrimOp::Text(TextNative::TextFold),
                args,
            } => self.text_fold(pc, dst, args),
            Instr::Prim { dst, op, args } if op.consumes() => self.prim_owned(pc, dst, op, args),
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
                // A census build of the compiler puts an enum mask in the tag.
                let (tag, _) = stitchwort_rt::value_census::split_tag(tag);
                let values = self.operands(args);
                let v = self.new_cell(tag, &values);
                self.assign(pc, dst, v);
            }
            Instr::CtorReuse {
                dst,
                tag,
                args,
                token,
            } => {
                let (tag, _) = stitchwort_rt::value_census::split_tag(tag);
                self.ctor_reuse(pc, dst, tag, args, token)
            }
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
            // Lent values (`stitchwort_rt::borrow`): held without a count.
            Instr::Peek { dst, src, i } => {
                let cell = self.load(Loc::Reg(src)).0[1];
                let v = self.load(Loc::Mem(
                    cell,
                    RC_VALUE_AT + (i as usize * VALUE_SIZE) as i32,
                ));
                self.assign(pc, dst, v);
            }
            Instr::Lend { dst, src } => {
                let v = self.load(Loc::Reg(src));
                self.assign(pc, dst, v);
            }
            Instr::Forget { .. } => {}
            Instr::Own { reg } => {
                self.clone_from(Loc::Reg(reg));
            }
            other => unreachable!("{other:?} isn't in the N1 subset"),
        }
        true
    }

    /// A new cell of `tag` with `values` (moved into it).
    fn new_cell(&mut self, tag: u32, values: &[Val]) -> Val {
        let n = values.len() as u64;
        let len = self.iconst(n);
        let cell = if self.caches_cells(n) {
            self.cached_cell(tag, n)
        } else {
            let t = self.i32const(tag);
            self.call_helper(self.helpers.cell_new, &[t, len])[0]
        };
        for (i, v) in values.iter().enumerate() {
            let at = RC_VALUE_AT + (i * VALUE_SIZE) as i32;
            self.store(Loc::Mem(cell, at), *v);
        }
        let w0 = self.iconst(u64::from(TAG_DATA) | (u64::from(tag) << 32));
        Val([w0, cell, len])
    }

    /// Whether cells of `n` fields go through the run's cell cache
    /// (`stitchwort_rt::cell_cache`): not under the trace, which must see
    /// every allocation and free.
    fn caches_cells(&self, n: u64) -> bool {
        cell_cache::ENABLED
            && !self.options.trace_refcounts
            && (1..=cell_cache::ARITIES).contains(&n)
    }

    /// A new cell of `n` fields (uninitialised, counts 1): the cache's first
    /// block of that size, or a new one if it has none.
    fn cached_cell(&mut self, tag: u32, n: u64) -> IrValue {
        let head_at = Context::CELLS_AT + CellCache::head_at(n);
        let head = self.b.ins().load(types::I64, flags(), self.ctx, head_at);
        let hit = self.b.create_block();
        let miss = self.b.create_block();
        let after = self.b.create_block();
        let cell = self.b.append_block_param(after, types::I64);
        self.b.ins().brif(head, hit, &[], miss, &[]);
        self.b.switch_to_block(hit);
        if let Some(count) = self.helpers.count_cell_hit {
            self.call_helper(count, &[]);
        }
        let next = self.b.ins().load(types::I64, flags(), head, STRONG_AT);
        self.b.ins().store(flags(), next, self.ctx, head_at);
        let one = self.iconst(1);
        self.b.ins().store(flags(), one, head, STRONG_AT);
        let room_at = Context::CELLS_AT + CellCache::ROOM_AT;
        let room = self.b.ins().load(types::I64, flags(), self.ctx, room_at);
        let room = self
            .b
            .ins()
            .iadd_imm_s(room, cell_cache::block_bytes(n) as i64);
        self.b.ins().store(flags(), room, self.ctx, room_at);
        self.b.ins().jump(after, &[head.into()]);
        self.b.switch_to_block(miss);
        self.b.set_cold_block(miss);
        let t = self.i32const(tag);
        let len = self.iconst(n);
        let new = self.call_helper(self.helpers.cell_new, &[t, len])[0];
        self.b.ins().jump(after, &[new.into()]);
        self.b.switch_to_block(after);
        cell
    }

    /// Frees the unique, emptied cell of `n` fields at `cell`: into the
    /// cache if its room says so, otherwise through the runtime, which
    /// counts the room again (`sw_cell_cache_full`).
    fn free_emptied(&mut self, cell: IrValue, n: u64) {
        if !self.caches_cells(n) {
            let n = self.iconst(n);
            self.call_helper(self.helpers.cell_free, &[cell, n]);
            return;
        }
        let head_at = Context::CELLS_AT + CellCache::head_at(n);
        let room_at = Context::CELLS_AT + CellCache::ROOM_AT;
        let bytes = cell_cache::block_bytes(n) as i64;
        let room = self.b.ins().load(types::I64, flags(), self.ctx, room_at);
        let fits = self
            .b
            .ins()
            .icmp_imm_u(IntCC::UnsignedGreaterThanOrEqual, room, bytes);
        let keep = self.b.create_block();
        let free = self.b.create_block();
        let after = self.b.create_block();
        self.b.ins().brif(fits, keep, &[], free, &[]);
        self.b.switch_to_block(keep);
        let head = self.b.ins().load(types::I64, flags(), self.ctx, head_at);
        self.b.ins().store(flags(), head, cell, STRONG_AT);
        self.b.ins().store(flags(), cell, self.ctx, head_at);
        let room = self.b.ins().iadd_imm_s(room, -bytes);
        self.b.ins().store(flags(), room, self.ctx, room_at);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(free);
        self.b.set_cold_block(free);
        let n = self.iconst(n);
        self.call_helper(self.helpers.cell_cache_full, &[self.ctx, cell, n]);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
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
        let live = self.live(pc);
        self.count_step(&live, &[]);
        let frames = self.push_frame(&live);
        let code = self.image.global_code[g as usize].expect("a constant has code");
        let f = self.func_ref(self.functions[&code]);
        let call = self.tagged(Part::Call, |g| g.b.ins().call(f, &[g.ctx, frames]));
        let r = self.b.inst_results(call).to_vec();
        let v = self.call_result(&live, &r);
        let out = self.temp_address(0);
        self.store(Loc::Mem(out, 0), v);
        let gc = self.i32const(g);
        self.call_helper(self.helpers.global_set, &[self.ctx, gc, out]);
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    /// `Apply`'s function value, taken from `f` (moved or cloned), and the
    /// code to call it with directly (a closure or a global function that
    /// takes exactly `n`: the machine's `exact`), or 0 for eval/apply.
    fn apply_target(&mut self, f: Reg, n: u32) -> (Val, IrValue) {
        let v = self.operand(f);
        let target = self.apply_target_of(v, n);
        (v, target)
    }

    /// [`Gen::apply_target`] for a function value already taken.
    fn apply_target_of(&mut self, v: Val, n: u32) -> IrValue {
        // This site's cache (`abi::ApplyCache`): a function value with the
        // same key as last time (the same global function, or a closure of
        // the same lambda) calls the same code, with no runtime call.
        // Numbered in the order the sites are compiled; the caches are in
        // the tables.
        let offset = i32::try_from(*self.caches as usize * size_of::<abi::ApplyCache>())
            .expect("the caches fit an offset");
        *self.caches += 1;
        let caches = self.tables_field(Tables::CACHES_AT);
        let is_fun = self.is_tag(v, TAG_FUN);
        let check = self.b.create_block();
        let cached = self.b.create_block();
        let other = self.b.create_block();
        let miss = self.b.create_block();
        let after = self.b.create_block();
        self.b.append_block_param(after, self.pointer);
        let none = self.b.ins().iconst(self.pointer, 0);
        self.b.ins().brif(is_fun, check, &[], after, &[none.into()]);
        self.b.switch_to_block(check);
        let first = self.b.ins().load(types::I64, flags(), v.0[1], RC_VALUE_AT);
        let mine = self.b.ins().band_imm_s(first, FUN_KEY_MASK as i64);
        let key = self.b.ins().load(
            types::I64,
            flags(),
            caches,
            offset + abi::ApplyCache::KEY_AT,
        );
        let hit = self.b.ins().icmp(IntCC::Equal, key, mine);
        self.b.ins().brif(hit, cached, &[], other, &[]);
        // Only a global function or a closure can be cached
        // (`sw_apply_cached`); anything else goes to the stub without
        // asking.
        self.b.switch_to_block(other);
        self.b.set_cold_block(other);
        let variant = self.b.ins().band_imm_s(first, 0xff);
        let cacheable = self.b.ins().icmp_imm_u(
            IntCC::UnsignedLessThanOrEqual,
            variant,
            i64::from(FUN_CLOSURE),
        );
        self.b
            .ins()
            .brif(cacheable, miss, &[], after, &[none.into()]);
        self.b.switch_to_block(cached);
        let code = self.b.ins().load(
            self.pointer,
            flags(),
            caches,
            offset + abi::ApplyCache::CODE_AT,
        );
        self.b.ins().jump(after, &[code.into()]);
        self.b.switch_to_block(miss);
        self.b.set_cold_block(miss);
        let at = self.b.ins().stack_addr(self.pointer, self.fun, 0);
        self.store(Loc::Mem(at, 0), v);
        let cache_at = self.b.ins().iadd_imm_s(caches, i64::from(offset));
        let n = self.iconst(u64::from(n));
        let target = self.call_helper(self.helpers.apply_cached, &[self.ctx, at, n, cache_at])[0];
        self.b.ins().jump(after, &[target.into()]);
        self.b.switch_to_block(after);
        self.b.block_params(after)[0]
    }

    /// The arguments of an application: registers (taken as `get!` takes
    /// them, once the frame is counted), or values already taken.
    fn take_args(&mut self, args: &ApplyArgs) -> Vec<Val> {
        match args {
            ApplyArgs::Regs(o) => self.operands(*o),
            ApplyArgs::Vals(values) => values.clone(),
        }
    }

    /// `live` without the registers `args` moves out.
    fn without_args(&self, live: &Regs, args: &ApplyArgs) -> Regs {
        match args {
            ApplyArgs::Regs(o) => self.without_moved(live, ops(self.code, *o)),
            ApplyArgs::Vals(_) => live.clone(),
        }
    }

    /// `dst = fv args`, with `target` from [`Gen::apply_target`] and `live`
    /// the registers that may hold a value once `fv` is taken: the
    /// machine's `Apply`.
    fn apply(
        &mut self,
        pc: usize,
        dst: Reg,
        fv: Val,
        target: IrValue,
        live: &Regs,
        args: ApplyArgs,
    ) {
        let n = match &args {
            ApplyArgs::Regs(o) => o.len,
            ApplyArgs::Vals(values) => values.len() as u32,
        };
        // Values held outside the registers until the frame is counted.
        let mut extra = vec![fv];
        if let ApplyArgs::Vals(values) = &args {
            extra.extend(values.iter().copied());
        }
        let exact = self.b.create_block();
        let slow = self.b.create_block();
        let after = self.b.create_block();
        self.b.ins().brif(target, exact, &[], slow, &[]);

        self.b.switch_to_block(exact);
        self.count_step_with(live, &extra, &[]);
        let frames = self.push_frame_with(live, &extra);
        let values = self.take_args(&args);
        let after_args = self.without_args(live, &args);
        let sig = self.value_sig(n);
        let mut call_args = vec![self.ctx, frames];
        call_args.extend(Self::words(&values));
        call_args.push(fv.0[1]);
        let call = self.tagged(Part::Call, |g| {
            g.b.ins().call_indirect(sig, target, &call_args)
        });
        let r = self.b.inst_results(call).to_vec();
        let v = self.call_result(&after_args, &r);
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);

        self.b.switch_to_block(slow);
        let values = self.take_args(&args);
        let after_args = self.without_args(live, &args);
        let apply = self.func_ref(self.apply_any[&n]);
        let none = self.iconst(0);
        let mut call_args = vec![self.ctx, self.frames, none, none];
        call_args.extend(fv.0);
        call_args.extend(Self::words(&values));
        let call = self.tagged(Part::Call, |g| g.b.ins().call(apply, &call_args));
        let r = self.b.inst_results(call).to_vec();
        let v = self.call_result(&after_args, &r);
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    /// `fv args` in a tail position, with `target` from
    /// [`Gen::apply_target`] and `taken` the registers that may hold a value
    /// once `fv` is taken: the machine's `TailApply`. Ends the block.
    fn tail_apply(&mut self, fv: Val, target: IrValue, taken: &Regs, args: ApplyArgs) {
        let n = match &args {
            ApplyArgs::Regs(o) => o.len,
            ApplyArgs::Vals(values) => values.len() as u32,
        };
        let mut extra = vec![fv];
        if let ApplyArgs::Vals(values) = &args {
            extra.extend(values.iter().copied());
        }
        let left = self.without_args(taken, &args);
        let exact = self.b.create_block();
        let slow = self.b.create_block();
        self.b.ins().brif(target, exact, &[], slow, &[]);

        // As the machine's `replace`, as for `TailCall`: the operands
        // fetched before the step is counted (dropped last if it fails).
        self.b.switch_to_block(exact);
        let fetched: Vec<Reg> = match &args {
            ApplyArgs::Regs(o) => ops(self.code, *o).to_vec(),
            ApplyArgs::Vals(_) => Vec::new(),
        };
        self.count_step_with(taken, &extra, &fetched);
        let values = self.take_args(&args);
        self.drop_env();
        self.release(&left);
        let sig = self.value_sig(n);
        let mut call_args = vec![self.ctx, self.frames];
        call_args.extend(Self::words(&values));
        call_args.push(fv.0[1]);
        self.leave();
        self.tagged(Part::Call, |g| {
            g.b.ins().return_call_indirect(sig, target, &call_args)
        });

        // As the machine: this frame popped and its registers released,
        // then eval/apply with the frames below, which drops this frame's
        // closure once it has taken the function value apart (as the
        // machine drops the popped frame).
        self.b.switch_to_block(slow);
        let values = self.take_args(&args);
        self.release(&left);
        let apply = self.func_ref(self.apply_any[&n]);
        let below = self.b.ins().iadd_imm_s(self.frames, -1);
        let env = match self.env {
            Some(env) => env,
            None => self.b.ins().iconst(self.pointer, 0),
        };
        let none = self.b.ins().iconst(self.pointer, 0);
        let mut call_args = vec![self.ctx, below, none, env];
        call_args.extend(fv.0);
        call_args.extend(Self::words(&values));
        self.leave();
        self.tagged(Part::Call, |g| g.b.ins().return_call(apply, &call_args));
    }

    /// `bind c k` (the operands `args`), as the machine's `Bind`: for `c` =
    /// `Done x`, `k x` applied as `Apply` applies (in a tail position, as
    /// `TailApply`); otherwise the node `Bind c k`. `dst` is `None` in a
    /// tail position (`TailPrim`), which ends the block.
    fn bind(&mut self, pc: usize, dst: Option<Reg>, args: Ops) {
        let o = ops(self.code, args).to_vec();
        let c = self.operand(o[0]);
        let k = self.operand(o[1]);
        let mut live = self.without_moved(&self.live(pc), &o);
        if dst.is_none() {
            // `TailPrim`: the frame popped and its registers released
            // before the native runs.
            self.release(&live);
            live = Regs::new(self.code.regs);
        }
        let c_at = self.spill_value(0, c);
        let k_at = self.spill_value(1, k);
        let out = self.spill_erased(2);
        let done = self.call_helper(self.helpers.bind, &[self.ctx, c_at, k_at, out])[0];
        let calling = self.b.create_block();
        let node = self.b.create_block();
        self.b.ins().brif(done, calling, &[], node, &[]);

        // `k x`.
        self.b.switch_to_block(calling);
        let x = self.load(Loc::Mem(out, 0));
        let k = self.load(Loc::Mem(k_at, 0));
        let target = self.apply_target_of(k, 1);
        let after = match dst {
            Some(dst) => {
                self.apply(pc, dst, k, target, &live, ApplyArgs::Vals(vec![x]));
                let after = self.b.create_block();
                self.b.ins().jump(after, &[]);
                Some(after)
            }
            None => {
                self.tail_apply(k, target, &live, ApplyArgs::Vals(vec![x]));
                None
            }
        };

        // The node.
        self.b.switch_to_block(node);
        let v = self.load(Loc::Mem(out, 0));
        match (dst, after) {
            (Some(dst), Some(after)) => {
                self.assign(pc, dst, v);
                self.b.ins().jump(after, &[]);
                self.b.switch_to_block(after);
            }
            _ => {
                // As the machine drops the popped frame's closure: once the
                // native has run.
                self.drop_env();
                self.leave();
                self.tagged(Part::Return, |g| g.b.ins().return_(&v.0));
            }
        }
    }

    /// The machine's `Prim` of an effect native, or `TailPrim` (`dst`
    /// `None`, ending the block): `bind` here ([`Gen::bind`]), a fold,
    /// `translate` or `runPure` by the effect runtime's `rt_loop` (stage
    /// NO2 of native-only.md), and a state-passing handler's fold by a leaf
    /// (NO3).
    fn effect(&mut self, pc: usize, dst: Option<Reg>, op: PrimOp, args: Ops) {
        if op == PrimOp::Effect(EffectOp::Bind) && args.len == 2 {
            self.bind(pc, dst, args);
            return;
        }
        let o = ops(self.code, args).to_vec();
        let values = self.operands(args);
        let live = self.without_moved(&self.live(pc), &o);
        for (i, v) in values.iter().enumerate() {
            let at = self.temp_address(i * VALUE_SIZE);
            self.store(Loc::Mem(at, 0), *v);
        }
        let at = self.temp_address(0);
        let out = self.temp_address(values.len() * VALUE_SIZE);
        let PrimOp::Effect(effect) = op else {
            unreachable!("an effect native")
        };
        let op_at = self.i32const(effect.index());
        if let Some(runtime) = self.runtime
            && runs_loop(effect)
        {
            // The effect runtime's loop (stage NO2 of native-only.md): the
            // handler and the computation made by its leaf, then `rt_loop`,
            // called with this frame's count; in a tail position, this
            // frame released first (as the machine's `TailPrim` pops it) and
            // its closure given to the loop to drop once the native has
            // begun, as the machine drops the popped frame's.
            if dst.is_none() {
                self.release(&live);
            }
            let handler = self.call_helper(self.helpers.eff_begin, &[self.ctx, op_at, at, out])[0];
            let c = self.load(Loc::Mem(out, 0));
            let run_loop = self.func_ref(runtime.run_loop);
            let zero = self.iconst(0);
            let (frames, env) = match dst {
                Some(_) => (self.frames, self.b.ins().iconst(self.pointer, 0)),
                None => (
                    self.b.ins().iadd_imm_s(self.frames, -1),
                    match self.env {
                        Some(env) => env,
                        None => self.b.ins().iconst(self.pointer, 0),
                    },
                ),
            };
            let none = self.b.ins().iconst(self.pointer, 0);
            let mut call_args = vec![self.ctx, frames];
            call_args.extend(c.0);
            call_args.extend([zero; 6]);
            call_args.extend([handler, none, env]);
            match dst {
                Some(dst) => {
                    let call = self.tagged(Part::Call, |g| g.b.ins().call(run_loop, &call_args));
                    let r = self.b.inst_results(call).to_vec();
                    let v = self.call_result(&live, &r);
                    self.assign(pc, dst, v);
                }
                None => {
                    self.leave();
                    self.tagged(Part::Call, |g| g.b.ins().return_call(run_loop, &call_args));
                }
            }
            return;
        }
        // A state-passing handler's fold (stage NO3 of native-only.md): its
        // function of the state, made by a leaf, as the machine's `effect`
        // makes it; in a tail position, after this frame's registers are
        // released and before its closure is dropped, as the machine's
        // `TailPrim` pops the frame and drops it once the native is done.
        assert!(
            matches!(effect, EffectOp::FoldState | EffectOp::FoldStateComp),
            "internal error: an effect native native code has no way to run"
        );
        if dst.is_none() {
            self.release(&live);
        }
        self.call_helper(self.helpers.eff_state, &[self.ctx, op_at, at, out]);
        let v = self.load(Loc::Mem(out, 0));
        match dst {
            Some(dst) => self.assign(pc, dst, v),
            None => {
                self.drop_env();
                self.leave();
                self.tagged(Part::Return, |g| g.b.ins().return_(&v.0));
            }
        }
    }

    /// `Text.fold text initial f` (the registers `args`, read): the
    /// compiled one (`emit_text_fold`), called with this frame's count, on
    /// copies taken in order, as the machine's `Prim` takes them.
    fn text_fold(&mut self, pc: usize, dst: Reg, args: Ops) {
        let o = ops(self.code, args).to_vec();
        let mut call_args = vec![self.ctx, self.frames];
        for r in &o {
            let v = self.clone_from(Loc::Reg(*r & !MOVE));
            call_args.extend(v.0);
        }
        let live = self.live(pc);
        let fold = self
            .text_fold
            .expect("the plan has `Text.fold` where a body uses it");
        let fold = self.func_ref(fold);
        let call = self.tagged(Part::Call, |g| g.b.ins().call(fold, &call_args));
        let r = self.b.inst_results(call).to_vec();
        let v = self.call_result(&live, &r);
        self.assign(pc, dst, v);
    }

    /// A value made by `helper` from `values` (moved): the helper takes
    /// `first`, then the values' address and count, then where to put it.
    fn made(&mut self, helper: FuncId, first: &[IrValue], values: &[Val]) -> Val {
        for (i, v) in values.iter().enumerate() {
            let at = self.temp_address(i * VALUE_SIZE);
            self.store(Loc::Mem(at, 0), *v);
        }
        let fields = self.temp_address(0);
        let out = self.temp_address(values.len() * VALUE_SIZE);
        let n = self.iconst(values.len() as u64);
        let mut args = first.to_vec();
        args.extend([fields, n, out]);
        self.call_helper(helper, &args);
        self.load(Loc::Mem(out, 0))
    }

    /// One of the machine's one-operand instructions (`abi::sw_unary`),
    /// reading `src` (borrowed) and writing `dst`.
    fn unary(&mut self, pc: usize, dst: Reg, src: Reg, op: u32) {
        let v = self.load(Loc::Reg(src));
        let from = self.spill_value(0, v);
        let to = self.spill_erased(1);
        let op = self.i32const(op);
        self.call_helper(self.helpers.unary, &[self.ctx, op, from, to]);
        let r = self.load(Loc::Mem(to, 0));
        self.assign(pc, dst, r);
    }

    /// A native that takes its operands by value (`abi::sw_prim_owned`):
    /// each is moved in on its last use, as a constructor's fields are, so
    /// an array nothing else holds is changed in place.
    fn prim_owned(&mut self, pc: usize, dst: Reg, op: PrimOp, args: Ops) {
        let values = self.operands(args);
        let slow = self.b.create_block();
        let after = self.b.create_block();
        if let (PrimOp::Array(ArrayNative::Set), 3) = (op, values.len()) {
            self.array_set(pc, dst, &values, slow);
            self.b.ins().jump(after, &[]);
            self.b.set_cold_block(slow);
        } else {
            self.b.ins().jump(slow, &[]);
        }
        self.b.switch_to_block(slow);
        for (i, v) in values.iter().enumerate() {
            let at = self.temp_address(i * VALUE_SIZE);
            self.store(Loc::Mem(at, 0), *v);
        }
        let from = self.temp_address(0);
        let out = self.temp_address(values.len() * VALUE_SIZE);
        let op = self.i32const(self.numbering.op(op));
        let n = self.iconst(values.len() as u64);
        self.call_helper(self.helpers.prim_owned, &[self.ctx, op, from, n, out]);
        let v = self.load(Loc::Mem(out, 0));
        self.assign(pc, dst, v);
        self.b.ins().jump(after, &[]);
        self.b.switch_to_block(after);
    }

    fn prim(&mut self, pc: usize, dst: Reg, op: PrimOp, args: Ops) {
        let o = ops(self.code, args).to_vec();
        let division = matches!(op, PrimOp::Nat(Native::DivFuel)) && o.len() == 3;
        let fast = division
            || matches!(op, PrimOp::Nat(Native::Add | Native::Sub | Native::Mul)) && o.len() == 2;
        if op == PrimOp::Hole(HoleOp::New) && o.is_empty() {
            // The head of a chain: a one-field cell holding a hole.
            let hole = self.small(0, 0, 0);
            let v = self.new_cell(0, &[hole]);
            self.assign(pc, dst, v);
            return;
        }
        let slow = self.b.create_block();
        let after = self.b.create_block();
        if let (PrimOp::Hole(h @ HoleOp::Take), 1) | (PrimOp::Hole(h @ HoleOp::Fill), 3) =
            (op, o.len())
        {
            self.hole(pc, dst, h, &o, slow, after);
        } else if let (Some((cc, tag)), 2) = (comparison(op), o.len()) {
            self.compare(pc, dst, cc, tag, &o, slow);
            self.b.ins().jump(after, &[]);
            self.b.set_cold_block(slow);
        } else if let (PrimOp::Array(ArrayNative::GetOr), 3) = (op, o.len()) {
            self.array_get_or(pc, dst, &o, slow);
            self.b.ins().jump(after, &[]);
            self.b.set_cold_block(slow);
        } else if fast {
            let loaded: Vec<Val> = o.iter().map(|r| self.load(Loc::Reg(*r))).collect();
            let mut both = self.is_tag(loaded[0], TAG_NAT);
            for v in &loaded[1..] {
                let n = self.is_tag(*v, TAG_NAT);
                both = self.b.ins().band(both, n);
            }
            let small = self.b.create_block();
            self.b.ins().brif(both, small, &[], slow, &[]);
            self.b.switch_to_block(small);
            let z = if division {
                // `divFuel fuel n d`, as `prims::div_fuel` computes it on
                // words: 0 if `d` is 0, else the smaller of `fuel` and
                // `n / d`. (The unused division by 0 would trap, so the
                // divisor is made 1 then.)
                let (fuel, n, d) = (loaded[0].0[1], loaded[1].0[1], loaded[2].0[1]);
                let zero = self.b.ins().icmp_imm_u(IntCC::Equal, d, 0);
                let one = self.iconst(1);
                let safe = self.b.ins().select(zero, one, d);
                let quotient = self.b.ins().udiv(n, safe);
                let least = self.b.ins().umin(fuel, quotient);
                let none = self.iconst(0);
                self.b.ins().select(zero, none, least)
            } else {
                let (x, y) = (loaded[0].0[1], loaded[1].0[1]);
                match op {
                    PrimOp::Nat(Native::Sub) => {
                        let diff = self.b.ins().isub(x, y);
                        let under = self.b.ins().icmp(IntCC::UnsignedLessThan, x, y);
                        let zero = self.iconst(0);
                        self.b.ins().select(under, zero, diff)
                    }
                    _ => {
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

    /// `Take cell` and `Fill cell i v` on a cell of a chain a loop is
    /// building ([`crate::trmc`]), as `prims::hole` does them: a load and a
    /// store, not a call. Anything the checks don't cover (a cell that isn't
    /// data, an index that isn't a small number or is past the fields) goes
    /// to `slow`, which is the generic call and panics as the machine does.
    ///
    /// Ownership: `Take` hands the caller a new count on field 0. `Fill`
    /// takes a new count on `v` for the field and overwrites the hole
    /// without dropping it: the hole is `Erased`, which owns nothing, and
    /// the cell is reached only from the loop that made it, so nothing reads
    /// the field during the write (see `prims::fill`). Both leave the cell's
    /// own count alone, as the operands are borrowed.
    fn hole(&mut self, pc: usize, dst: Reg, op: HoleOp, o: &[Reg], slow: Block, after: Block) {
        let cell = self.load(Loc::Reg(o[0]));
        let is_data = self.is_tag(cell, TAG_DATA);
        let checked = self.b.create_block();
        if op == HoleOp::Take {
            let some = self.b.ins().icmp_imm_u(IntCC::NotEqual, cell.0[2], 0);
            let ok = self.b.ins().band(is_data, some);
            self.b.ins().brif(ok, checked, &[], slow, &[]);
            self.b.switch_to_block(checked);
            let v = self.clone_from(Loc::Mem(cell.0[1], RC_VALUE_AT));
            self.assign(pc, dst, v);
        } else {
            let index = self.load(Loc::Reg(o[1]));
            let small = self.is_tag(index, TAG_NAT);
            let inside = self
                .b
                .ins()
                .icmp(IntCC::UnsignedLessThan, index.0[1], cell.0[2]);
            let both = self.b.ins().band(is_data, small);
            let all = self.b.ins().band(both, inside);
            self.b.ins().brif(all, checked, &[], slow, &[]);
            self.b.switch_to_block(checked);
            let v = self.clone_from(Loc::Reg(o[2]));
            let stride = self.b.ins().imul_imm_s(index.0[1], VALUE_SIZE as i64);
            let field = self.b.ins().iadd(cell.0[1], stride);
            self.store(Loc::Mem(field, RC_VALUE_AT), v);
            let erased = self.small(0, 0, 0);
            self.assign(pc, dst, erased);
        }
        self.b.ins().jump(after, &[]);
        self.b.set_cold_block(slow);
    }

    /// 1 if the test holds.
    fn test(&mut self, op: PrimOp, o: &[Reg]) -> IrValue {
        let slow = self.b.create_block();
        let after = self.b.create_block();
        self.b.append_block_param(after, types::I8);
        // Numbers that fit a word are compared inline, as the machine's
        // `Test` compares them.
        let cc = comparison(op);
        if let (Some((cc, tag)), [a, b]) = (cc, o) {
            let a = self.load(Loc::Reg(*a));
            let b = self.load(Loc::Reg(*b));
            let na = self.is_tag(a, tag);
            let nb = self.is_tag(b, tag);
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

    /// Where the element `index` of `array` (an `Array`) is, if `array` and
    /// `index` are an array and a small number and the index is inside it:
    /// the address, in the block this leaves the generator in. Otherwise
    /// the code goes to `slow`.
    fn array_slot(&mut self, array: Val, index: Val, slow: Block) -> IrValue {
        let is_array = self.is_tag(array, TAG_ARRAY);
        let is_nat = self.is_tag(index, TAG_NAT);
        let both = self.b.ins().band(is_array, is_nat);
        let tagged = self.b.create_block();
        self.b.ins().brif(both, tagged, &[], slow, &[]);
        self.b.switch_to_block(tagged);
        // Only now is the word at byte 8 known to be an `Rc`'s address.
        let len = self
            .b
            .ins()
            .load(types::I64, flags(), array.0[1], ARRAY_LEN_AT);
        let inside = self.b.ins().icmp(IntCC::UnsignedLessThan, index.0[1], len);
        let checked = self.b.create_block();
        self.b.ins().brif(inside, checked, &[], slow, &[]);
        self.b.switch_to_block(checked);
        let items = self
            .b
            .ins()
            .load(self.pointer, flags(), array.0[1], ARRAY_ITEMS_AT);
        let stride = self.b.ins().imul_imm_s(index.0[1], VALUE_SIZE as i64);
        self.b.ins().iadd(items, stride)
    }

    /// `Array.getOr array index default` (all borrowed) with a small
    /// `index` inside the array: a load of the element and a new count on
    /// it. The default is touched only by the generic call (`slow`), which
    /// the machine's `prims::array` makes too, past the end.
    fn array_get_or(&mut self, pc: usize, dst: Reg, o: &[Reg], slow: Block) {
        let array = self.load(Loc::Reg(o[0]));
        let index = self.load(Loc::Reg(o[1]));
        let slot = self.array_slot(array, index, slow);
        let v = self.clone_from(Loc::Mem(slot, 0));
        self.assign(pc, dst, v);
    }

    /// `Array.set array index value` (all moved in, as `values`) on an array
    /// nothing else holds and a small `index` inside it, as
    /// `prims::eval_owned` does it: the element is overwritten in place and
    /// the old one dropped after the store. Ownership: `values[0]` holds
    /// the array's one reference (a count of 1, no weak ones, which is what
    /// `Rc::get_mut` needs), so the buffer is native code's to write, and
    /// the result takes that reference; the new element's reference moves
    /// into the buffer. A shared array, or an index that is past the end or
    /// isn't a small number, goes to `slow`, the generic call that copies or
    /// panics as the machine does.
    fn array_set(&mut self, pc: usize, dst: Reg, values: &[Val], slow: Block) {
        let slot = self.array_slot(values[0], values[1], slow);
        let unique = self.unique(values[0].0[1]);
        let mine = self.b.create_block();
        self.b.ins().brif(unique, mine, &[], slow, &[]);
        self.b.switch_to_block(mine);
        let old = self.load(Loc::Mem(slot, 0));
        self.store(Loc::Mem(slot, 0), values[2]);
        self.drop_value(old);
        self.assign(pc, dst, values[0]);
    }

    /// A comparison of two numbers that fit a word, made where its `Bool`
    /// is wanted as a value (`dst`) rather than branched on: compared inline
    /// and built from the program's `True` and `False`, with the generic
    /// call (`slow`) for any other operand. Neither operand owns anything on
    /// the inline path, so there is nothing to drop.
    fn compare(&mut self, pc: usize, dst: Reg, cc: IntCC, tag: u8, o: &[Reg], slow: Block) {
        let a = self.load(Loc::Reg(o[0]));
        let b = self.load(Loc::Reg(o[1]));
        let na = self.is_tag(a, tag);
        let nb = self.is_tag(b, tag);
        let both = self.b.ins().band(na, nb);
        let small = self.b.create_block();
        self.b.ins().brif(both, small, &[], slow, &[]);
        self.b.switch_to_block(small);
        let holds = self.b.ins().icmp(cc, a.0[1], b.0[1]);
        let shapes = self.program.shapes;
        let yes = self.iconst(u64::from(shapes.true_));
        let no = self.iconst(u64::from(shapes.false_));
        let ctor = self.b.ins().select(holds, yes, no);
        let high = self.b.ins().ishl_imm_u(ctor, 32);
        let w0 = self.b.ins().bor_imm_u(high, i64::from(TAG_TAG));
        let zero = self.iconst(0);
        self.assign(pc, dst, Val([w0, zero, zero]));
    }

    /// Whether the cell whose address is `cell` is unique.
    ///
    /// Tests the strong count alone. An `Rc` holds an implicit weak count of
    /// 1 while any strong reference exists, and no `Weak` is ever made to a
    /// runtime value, so the weak count is always 1 and strong == 1 means
    /// no other reference. Anything that made a `Weak` would break this.
    /// Debug builds of the compiler check the weak count and trap.
    fn unique(&mut self, cell: IrValue) -> IrValue {
        let strong = self.b.ins().load(types::I64, flags(), cell, STRONG_AT);
        if cfg!(debug_assertions) {
            let weak = self.b.ins().load(types::I64, flags(), cell, WEAK_AT);
            let w1 = self.b.ins().icmp_imm_u(IntCC::Equal, weak, 1);
            self.b.ins().trapz(w1, TrapCode::unwrap_user(4));
        }
        self.b.ins().icmp_imm_u(IntCC::Equal, strong, 1)
    }

    fn unpack(&mut self, pc: usize, src: Reg, fields: Ops, token: Reg) {
        let pairs: Vec<(u32, Reg)> = ops(self.code, fields)
            .chunks(2)
            .map(|p| (p[0], p[1]))
            .collect();
        if self.options.trace_refcounts {
            // The helper works on the frame's registers as the machine
            // does, so they're all written out and read back (or, with a
            // register file, given it).
            let regs = match self.file {
                Some(file) => file,
                None => {
                    for r in 0..self.code.regs {
                        let v = self.load(Loc::Reg(r));
                        self.spill_value(r as usize, v);
                    }
                    self.spill_address(0)
                }
            };
            let src = self.i32const(src);
            // The pairs, written to the stack (not the image's operand list
            // by address: the code holds no host address).
            let list = ops(self.code, fields).to_vec();
            let pairs_slot = self.b.create_sized_stack_slot(StackSlotData::new(
                StackSlotKind::ExplicitSlot,
                (list.len().max(1) * 4) as u32,
                2,
            ));
            for (i, x) in list.iter().enumerate() {
                let x = self.i32const(*x);
                self.b
                    .ins()
                    .stack_store(self.pointer, x, pairs_slot, (i * 4) as i32);
            }
            let at = self.b.ins().stack_addr(self.pointer, pairs_slot, 0);
            let n = self.iconst(pairs.len() as u64);
            let token = self.i32const(token);
            self.call_helper(self.helpers.unpack, &[regs, src, at, n, token]);
            if self.file.is_some() {
                return;
            }
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
            if d == NO_REG {
                // A field the arm doesn't use.
                self.drop_value(f);
            } else {
                self.assign(pc, d, f);
            }
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
            self.free_emptied(cell, taken as u64);
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
            if d == NO_REG {
                continue;
            }
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
            // An empty token (the cell was shared, or the token was passed
            // on another path) is common where tokens are passed to calls
            // (crate::reuse): a new cell, inline, as `Ctor` makes, and
            // nothing to drop.
            let empty = self.is_tag(t, 0);
            let fresh = self.b.create_block();
            let test = self.b.create_block();
            self.b.ins().brif(empty, fresh, &[], test, &[]);
            self.b.switch_to_block(fresh);
            self.erase(Loc::Reg(token));
            let values = self.operands(args);
            let v = self.new_cell(tag, &values);
            self.assign(pc, dst, v);
            self.b.ins().jump(after, &[]);
            self.b.switch_to_block(test);
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

#[cfg(test)]
mod tests {
    use super::*;

    /// A function returning the constant `n`.
    fn returning(n: i64) -> ir::Function {
        let mut signature = ir::Signature::new(CallConv::SystemV);
        signature.returns.push(AbiParam::new(types::I64));
        let mut func = ir::Function::with_name_signature(ir::UserFuncName::user(0, 0), signature);
        let mut context = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut func, &mut context);
        let entry = b.create_block();
        b.switch_to_block(entry);
        let v = b.ins().iconst(types::I64, n);
        b.ins().return_(&[v]);
        b.seal_all_blocks();
        let isa = cranelift_native::builder()
            .expect("a supported machine")
            .finish(settings::Flags::new(settings::builder()))
            .expect("an ISA");
        b.finalize(isa.frontend_config());
        func
    }

    #[test]
    fn the_audit_finds_a_host_address_in_the_code() {
        let shapes = 0x1_2345_6000u64;
        let mut audit = Audit {
            host: vec![(0x1000_0000, 0x1000_0100), (shapes, shapes + 64)],
            listing: None,
        };
        assert!(audit.function(&returning(shapes as i64 + 8)).is_err());
        assert!(audit.function(&returning(0x1000_0000)).is_err());
        assert!(audit.function(&returning(shapes as i64 + 64)).is_ok());
        assert!(audit.function(&returning(42)).is_ok());
    }

    /// A function with a stack slot of `size` bytes, written and read back.
    fn with_frame(size: u32) -> ir::Function {
        let mut signature = ir::Signature::new(CallConv::SystemV);
        signature.returns.push(AbiParam::new(types::I64));
        let mut func = ir::Function::with_name_signature(ir::UserFuncName::user(0, 0), signature);
        let mut context = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut func, &mut context);
        let entry = b.create_block();
        b.switch_to_block(entry);
        let slot =
            b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 4));
        let one = b.ins().iconst(types::I64, 1);
        b.ins().stack_store(types::I64, one, slot, 0);
        let v = b.ins().stack_load(types::I64, types::I64, slot, 0);
        b.ins().return_(&[v]);
        b.seal_all_blocks();
        b.finalize(host_isa(false).expect("an ISA").frontend_config());
        func
    }

    /// The code of `func` for `isa`.
    fn code_of(func: &ir::Function, isa: &dyn cranelift_codegen::isa::TargetIsa) -> Vec<u8> {
        let mut context = cranelift_codegen::Context::for_function(func.clone());
        context
            .compile(isa, &mut Default::default())
            .expect("compiles")
            .code_buffer()
            .to_vec()
    }

    #[test]
    fn a_frame_of_several_pages_is_probed() {
        let isa = host_isa(false).expect("an ISA");
        assert!(isa.flags().enable_probestack());
        let plain = cranelift_native::builder()
            .expect("a supported machine")
            .finish(settings::Flags::new({
                let mut flags = settings::builder();
                flags.set("preserve_frame_pointers", "true").unwrap();
                flags.set("enable_pinned_reg", "true").unwrap();
                flags.set("opt_level", "speed").unwrap();
                flags
            }))
            .expect("an ISA");
        let big = with_frame(100_000);
        // The frame reader still sees the whole frame behind the probes.
        let mut context = cranelift_codegen::Context::for_function(big.clone());
        let compiled = context
            .compile(&*isa, &mut Default::default())
            .expect("compiles");
        assert!(crate::frames::frame_bound(&big, compiled) >= 100_000);
        assert!(code_of(&big, &*isa).len() > code_of(&big, &*plain).len());
        // A frame under a page has no probe, so costs nothing.
        let small = with_frame(1000);
        assert_eq!(code_of(&small, &*isa), code_of(&small, &*plain));
    }

    /// Code from the JIT's usual provider, and data from the middle of a
    /// 16 GiB reservation, so at least 8 GiB from any code.
    struct FarData {
        code: Box<dyn cranelift_jit::JITMemoryProvider + Send>,
        middle: *mut u8,
    }

    // SAFETY: `middle` is the address of a page of a reservation the test
    // owns, which outlives the provider; nothing is tied to a thread.
    #[allow(unsafe_code)]
    unsafe impl Send for FarData {}

    impl cranelift_jit::JITMemoryProvider for FarData {
        #[allow(unsafe_code)]
        fn allocate(
            &mut self,
            size: usize,
            align: u64,
            kind: cranelift_jit::JITMemoryKind,
        ) -> std::io::Result<*mut u8> {
            if let cranelift_jit::JITMemoryKind::Executable = kind {
                return self.code.allocate(size, align, kind);
            }
            assert!(size <= 4096 && align <= 4096, "one page of data");
            // SAFETY: a page inside the reservation, which nothing else uses.
            let made = unsafe {
                libc::mprotect(self.middle.cast(), 4096, libc::PROT_READ | libc::PROT_WRITE)
            };
            assert_eq!(made, 0, "{}", std::io::Error::last_os_error());
            Ok(self.middle)
        }

        #[allow(unsafe_code)]
        unsafe fn free_memory(&mut self) {
            // SAFETY: passed on from the caller.
            unsafe { self.code.free_memory() }
        }

        fn finalize(
            &mut self,
            protection: cranelift_jit::BranchProtection,
        ) -> cranelift_module::ModuleResult<()> {
            self.code.finalize(protection)
        }
    }

    /// SW-3139: JIT code reads data however far `mmap` puts it from the
    /// code. A PC-relative reference reaches only 2 GiB (x86-64) or 4 GiB
    /// (aarch64), and cranelift-jit panics applying it beyond that.
    #[test]
    #[allow(unsafe_code)]
    fn code_reads_data_mapped_far_away() {
        const RESERVED: usize = 16 << 30;
        // SAFETY: a fresh anonymous reservation, unmapped at the end.
        let reservation = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                RESERVED,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_NORESERVE,
                -1,
                0,
            )
        };
        assert_ne!(reservation, libc::MAP_FAILED);
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        let code: Box<dyn cranelift_jit::JITMemoryProvider + Send> =
            Box::new(crate::map_jit::MapJitMemoryProvider::new().expect("MAP_JIT memory"));
        #[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
        let code: Box<dyn cranelift_jit::JITMemoryProvider + Send> =
            Box::new(cranelift_jit::SystemMemoryProvider::new());
        let provider = FarData {
            code,
            // SAFETY: the middle of the reservation is within it.
            middle: unsafe { reservation.cast::<u8>().add(RESERVED / 2) },
        };

        let mut builder =
            JITBuilder::with_isa(host_isa(false).expect("an ISA"), default_libcall_names());
        builder.memory_provider(Box::new(provider));
        let mut module = JITModule::new(builder);
        let data = module
            .declare_data("far", Linkage::Local, false, false)
            .unwrap();
        let mut description = cranelift_module::DataDescription::new();
        description.define(3139i64.to_ne_bytes().to_vec().into_boxed_slice());
        module.define_data(data, &description).unwrap();

        let mut signature = module.make_signature();
        signature.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function("read_far", Linkage::Local, &signature)
            .unwrap();
        let mut context = module.make_context();
        context.func.signature = signature;
        let mut builder_context = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut context.func, &mut builder_context);
        let entry = b.create_block();
        b.switch_to_block(entry);
        let global = far_data(&mut module, data, b.func);
        let at = b.ins().symbol_value(types::I64, global);
        let v = b.ins().load(types::I64, flags(), at, 0);
        b.ins().return_(&[v]);
        b.seal_all_blocks();
        b.finalize(module.isa().frontend_config());
        module.define_function(id, &mut context).unwrap();
        module.finalize_definitions().unwrap();

        let code = module.get_finalized_function(id);
        // SAFETY: `read_far` takes nothing and returns an i64 in the host's
        // calling convention; its data is still mapped.
        let read: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code) };
        assert_eq!(read(), 3139);
        // SAFETY: nothing runs the code or reads the data after this.
        unsafe { libc::munmap(reservation, RESERVED) };
    }
}
