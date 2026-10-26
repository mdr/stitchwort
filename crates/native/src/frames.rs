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
//! that runs the machine for native code (an effect, a
//! function value with no native code) can call native code again. Each
//! such level has at least one counted native frame above it before it can
//! nest again, so the stack a run uses is at most the frames pending times
//! the widest body's bound and one level of nesting (`level_bound`), plus
//! whatever a helper uses at the bottom (`HELPER_ROOM`) and what the host
//! used above the first crossing (`HOST_ROOM`).

use cranelift_codegen::CompiledCode;
use cranelift_codegen::ir::Function;
use cranelift_codegen::isa::unwind::UnwindInst;
// The rule for the stack check is the crossing's, in the runtime, which a
// standalone executable's linked code shares (standalone-executables.md
// S5).
pub use stitchwort_rt::native_abi::{
    HELPER_ROOM, HOST_ROOM, NEST_ROOM, counter_fires_first, floor_depth, level_bound,
};

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
