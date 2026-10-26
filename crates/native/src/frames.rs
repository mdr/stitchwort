//! How much native stack a frame can use, and what that means for the
//! stack-pointer check behind the frame limit (stage N2b of
//! docs/proposals/native-compilation.md).
//!
//! Cranelift 0.136 doesn't report a compiled function's frame size, so it is
//! read from what the prologue was emitted as, by architecture:
//! - **aarch64**: the machine buffer keeps the unwind pseudo-instructions
//!   (`vcode` prints them as `unwind ...`): `PushFrameRegs` (the saved frame
//!   pointer and link register), `DefineNewFrame` (the saved callee-saved
//!   registers) and `StackAlloc` (the rest: stack slots, spill slots and the
//!   outgoing argument area). Their sum is the frame; an aarch64 body
//!   measured by hand at 304 bytes agrees.
//! - **x86-64**: Cranelift emits no `StackAlloc` there, but the prologue is
//!   always `push %rbp; mov %rsp,%rbp; sub $N,%rsp`, so `N` is read from the
//!   code bytes. Frames of a page or more are probed first (a `sub` of the
//!   guard size), and any other start is a prologue the reader doesn't know
//!   (a tail call to a callee with more stack arguments moves the frame
//!   first): both take the fallback.
//!
//! A tail call to a callee that takes more arguments on the stack than the
//! caller was given grows the frame by the difference, which none of these
//! record, so a bound adds every stack argument its widest signature could
//! have. A body whose prologue isn't read falls back to a bound from its IR
//! (stack slots, and two spill slots for each value), which is safe but far
//! above the real size.
//!
//! Since stage N4 native frames do nest inside runtime helpers: a helper
//! that runs the machine for native code (an effect, `Text.fold`, a
//! function value with no native code) can call native code again. Each
//! such level has at least one counted native frame above it before it can
//! nest again, so the stack a run uses is at most the frames pending times
//! the widest body's bound and one level of nesting (`level_bound`), plus
//! whatever a helper uses at the bottom (`HELPER_ROOM`) and what the host
//! used above the first crossing (`HOST_ROOM`).

use cranelift_codegen::CompiledCode;
use cranelift_codegen::ir::Function;
use cranelift_codegen::isa::unwind::UnwindInst;

/// What the host (the driver, the machine, the CLI) may have used above
/// the crossing into native code.
pub const HOST_ROOM: usize = 8 * 1024 * 1024;
/// What a runtime helper may use at the bottom of the stack (freeing a
/// value, a big number's arithmetic, a native operation).
pub const HELPER_ROOM: usize = 8 * 1024 * 1024;

/// The page size Cranelift probes frames by (its default,
/// `probestack_size_log2` 12).
const GUARD: usize = 4096;

/// A bound on the stack one call of the compiled `func` uses, in bytes.
pub fn frame_bound(func: &Function, compiled: &CompiledCode) -> usize {
    // What a tail call grows the frame by: its callee's stack arguments
    // beyond the ones this body was given. Arguments are words; at least 4
    // of a callee's go in registers (aarch64 has 8, x86-64 fewer but more
    // than 4 in the `tail` convention), and at most 8 of this body's own.
    let own_stack = func.signature.params.len().saturating_sub(8);
    let arguments = func
        .layout
        .blocks()
        .flat_map(|block| func.layout.block_insts(block))
        .filter(|inst| {
            let op = func.dfg.insts[*inst].opcode();
            op.is_call() && op.is_return()
        })
        .filter_map(|inst| func.dfg.call_signature(inst))
        .map(|sig| {
            func.dfg.signatures[sig]
                .params
                .len()
                .saturating_sub(4)
                .saturating_sub(own_stack)
                * 8
        })
        .max()
        .unwrap_or(0);
    // 16 for alignment.
    match read_frame(compiled) {
        Some(frame) => frame + arguments + 16,
        None => fallback_bound(func) + arguments,
    }
}

/// The frame the prologue sets up, if it is one of the two known shapes.
fn read_frame(compiled: &CompiledCode) -> Option<usize> {
    let (mut pushed, mut clobbers, mut allocated) = (0, 0, None);
    for (_, inst) in &compiled.buffer.unwind_info {
        match inst {
            UnwindInst::PushFrameRegs {
                offset_upward_to_caller_sp,
            } => pushed = pushed.max(*offset_upward_to_caller_sp as usize),
            UnwindInst::DefineNewFrame {
                offset_downward_to_clobbers,
                ..
            } => clobbers = clobbers.max(*offset_downward_to_clobbers as usize),
            UnwindInst::StackAlloc { size } => {
                allocated = Some(allocated.unwrap_or(0) + *size as usize);
            }
            _ => {}
        }
    }
    match allocated {
        Some(allocated) => Some(pushed.max(16) + clobbers + allocated),
        None => x64_frame(compiled.code_buffer()),
    }
}

/// The frame of x86-64 code that starts `push %rbp; mov %rsp,%rbp; sub $N,%rsp`
/// with `N` under a page: the return address, the saved `%rbp` and `N`.
fn x64_frame(code: &[u8]) -> Option<usize> {
    let rest = code.strip_prefix(&[0x55, 0x48, 0x89, 0xE5])?;
    let n = match rest {
        [0x48, 0x83, 0xEC, imm, ..] if *imm < 0x80 => *imm as usize,
        [0x48, 0x81, 0xEC, a, b, c, d, ..] => u32::from_le_bytes([*a, *b, *c, *d]) as usize,
        _ => return None,
    };
    (n < GUARD).then_some(16 + n)
}

/// For a body whose prologue wasn't read: its stack slots and two spill
/// slots for each value, with generous room for saved registers.
fn fallback_bound(func: &Function) -> usize {
    let slots: usize = func
        .sized_stack_slots
        .values()
        .map(|s| (s.size as usize).next_multiple_of(16))
        .sum();
    16 + 512 + slots + func.dfg.num_values() * 16 + 16
}

/// What nesting through the machine may add to each counted frame on the
/// native stack (stage N4): a helper that runs the machine (`sw_fold`,
/// `sw_apply_prepare`, `sw_perform`, `sw_effect`), the machine's `nested`
/// and `run`, its way back (`State::cross`, `Islands::call`) and a
/// trampoline. Measured on the release build (aarch64, 26 October 2026),
/// as the stack address at each nested run: a recursion through
/// `Text.fold` used 4,208 bytes per level, two counted frames each (2,104
/// per frame, native frames of at most 792 bytes included); a handler whose
/// clause resumes in a non-tail position (`k 1 + 1`) nests twice per
/// counted frame, 3,904 bytes per frame (native frames of at most 1,384
/// bytes included). Handlers in other positions don't nest: the depth stays
/// in the machine's frames. 4 KiB is more than either whole measurement,
/// native frames included, so with the widest body's bound added
/// (`level_bound`) the margin is that bound (5,480 bytes allowed against
/// 3,904 used in the second case). Larger would keep the roguelike's
/// 2,000,000 frames (bodies up to 2,760 bytes) off the 16 GiB stack
/// (`stitchwort_host::NATIVE_STACK`).
pub const NEST_ROOM: usize = 4 * 1024;

/// A bound on the stack one counted frame uses: a body (`max_frame`) and
/// the nesting through the machine that can come with it (`NEST_ROOM`).
pub fn level_bound(max_frame: usize) -> usize {
    max_frame + NEST_ROOM
}

/// How far below the crossing the stack-pointer check puts its floor, for
/// a stack of `stack_size` bytes and bodies of at most `max_frame`: the
/// whole stack less the host's and helpers' room and one more frame (the
/// check runs before a call pushes its frame). `None` if the stack is too
/// small for that.
pub fn floor_depth(stack_size: usize, max_frame: usize) -> Option<usize> {
    stack_size.checked_sub(HOST_ROOM + HELPER_ROOM + max_frame)
}

/// Whether the frame counter always fires before the stack-pointer check:
/// `frame_limit` frames of at most `max_frame` fit above the floor.
pub fn counter_fires_first(frame_limit: u64, stack_size: usize, max_frame: usize) -> bool {
    floor_depth(stack_size, max_frame)
        .is_some_and(|depth| frame_limit.saturating_mul(max_frame as u64) <= depth as u64)
}
