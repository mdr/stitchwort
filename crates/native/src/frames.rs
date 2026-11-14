//! How much native stack a frame can use, and what that means for the
//! stack-pointer check behind the frame limit (stage N2b of
//! docs/proposals/native-compilation.md).
//!
//! A compiled function's frame is what its machine buffer's frame layout
//! says (`MachBufferFinalized::frame_layout`): the distance from the stack
//! pointer after the prologue up to the frame pointer, which covers the
//! saved callee-saved registers, the stack and spill slots and the outgoing
//! argument area, plus the frame pointer and return address saved above it.
//! It holds on every architecture, whatever the prologue's code: a frame of
//! a page or more is probed first (SW-1157), so reading the frame from the
//! code would mean knowing every probe sequence.
//!
//! A tail call to a callee that takes more arguments on the stack than the
//! caller was given grows the frame by the difference, which the frame
//! layout doesn't include, so a bound adds every stack argument its widest
//! signature could have. Code without a frame layout (none Cranelift
//! emits) falls back to a bound from its IR (stack slots, and two spill
//! slots for each value), which is safe but far above the real size.
//!
//! Nothing nests (stage NO4 of native-only.md): every crossing is from the
//! runner, near the top of the stack, and one counted frame is a body with
//! the runtime frames that may come with it (`n1::emit` adds them to the
//! bound). So the stack a run uses is at most the frames pending times that
//! bound, plus whatever a helper uses at the bottom (`HELPER_ROOM`) and what
//! the host used above the first crossing (`HOST_ROOM`): what
//! `native_stack` reserves (stage NO5).

use cranelift_codegen::CompiledCode;
use cranelift_codegen::ir::Function;
// The rule for the stack check is the crossing's, in the runtime, which a
// standalone executable's linked code shares (standalone-executables.md
// S5).
pub use stitchwort_rt::native_abi::{
    HELPER_ROOM, HOST_ROOM, STACK_CAP, counter_fires_first, floor_depth, native_stack,
};

/// The frame pointer and the return address (the link register on
/// aarch64), saved above the frame layout's part: the setup area of every
/// body, since `n1` keeps frame pointers.
const SETUP: usize = 16;

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
    match compiled.buffer.frame_layout() {
        Some(layout) => SETUP + layout.frame_to_fp_offset as usize + arguments + 16,
        None => fallback_bound(func) + arguments,
    }
}

/// For code without a frame layout: its stack slots and two spill
/// slots for each value, with generous room for saved registers.
fn fallback_bound(func: &Function) -> usize {
    let slots: usize = func
        .sized_stack_slots
        .values()
        .map(|s| (s.size as usize).next_multiple_of(16))
        .sum();
    16 + 512 + slots + func.dfg.num_values() * 16 + 16
}
