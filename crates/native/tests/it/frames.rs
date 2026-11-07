//! The frame-size bound (`stitchwort_native::frames`) on both architectures,
//! whatever the host: bodies compiled for aarch64 and x86-64 (Cranelift's
//! backends for both are built into the test, `Cargo.toml`) have the
//! prologue pseudo-instructions the bound reads, and the bound covers their
//! stack slots without being far above them.

use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, InstBuilder, Signature, StackSlotData, StackSlotKind, UserFuncName, types,
};
use cranelift_codegen::isa::unwind::UnwindInst;
use cranelift_codegen::isa::{CallConv, lookup_by_name};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use stitchwort_native::frames::frame_bound;

/// A body with a stack slot of `slot` bytes, compiled for `triple` in the
/// `tail` convention with frame pointers, as `n1` does: its bound, and
/// whether its prologue allocated stack.
fn bound_for(triple: &str, slot: u32) -> (usize, bool) {
    let mut flags = settings::builder();
    flags.set("preserve_frame_pointers", "true").unwrap();
    let isa = lookup_by_name(triple)
        .unwrap()
        .finish(settings::Flags::new(flags))
        .unwrap();
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let mut func = ir::Function::with_name_signature(UserFuncName::default(), sig);
    let mut builder_context = FunctionBuilderContext::new();
    {
        let mut b = FunctionBuilder::new(&mut func, &mut builder_context);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let slot =
            b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, slot, 3));
        let x = b.block_params(entry)[0];
        b.ins().stack_store(isa.pointer_type(), x, slot, 0);
        let y = b.ins().stack_load(isa.pointer_type(), types::I64, slot, 8);
        b.ins().return_(&[y]);
        b.seal_all_blocks();
        b.finalize(isa.frontend_config());
    }
    let mut context = Context::for_function(func);
    context.compile(&*isa, &mut Default::default()).unwrap();
    let compiled = context.compiled_code().unwrap();
    let allocated = compiled
        .buffer
        .unwind_info
        .iter()
        .any(|(_, i)| matches!(i, UnwindInst::StackAlloc { .. }));
    (frame_bound(&context.func, compiled), allocated)
}

#[test]
fn the_bound_covers_the_stack_slots_on_both_architectures() {
    for triple in ["aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"] {
        for slot in [64, 1000, 20_000] {
            let (bound, allocated) = bound_for(triple, slot);
            if triple.starts_with("aarch64") {
                assert!(allocated, "{triple}: no StackAlloc for a {slot}-byte slot");
            }
            assert!(bound >= slot as usize, "{triple}: {bound} < {slot}");
            // The prologue is read (a few hundred bytes over the slot) for
            // frames under a page; a bigger frame takes the fallback.
            let over = if slot < 4096 { 300 } else { 1024 };
            assert!(
                bound < (slot + over) as usize,
                "{triple}: {bound} for {slot}"
            );
        }
    }
}
