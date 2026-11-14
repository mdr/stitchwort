//! The frame-size bound (`stitchwort_native::frames`) on both architectures,
//! whatever the host: for bodies compiled for aarch64 and x86-64
//! (Cranelift's backends for both are built into the test, `Cargo.toml`),
//! the bound covers their stack slots without being far above them, frames
//! of several pages and bodies of many values included.

use std::fmt::Write;

use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, InstBuilder, Signature, StackSlotData, StackSlotKind, UserFuncName, types,
};
use cranelift_codegen::isa::{CallConv, lookup_by_name};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use stitchwort_native::frames::frame_bound;

use crate::common::*;
use stitchwort_driver::driver::with_stack;

/// A body with a stack slot of `slot` bytes and a chain of `values` sums,
/// compiled for `triple` in the `tail` convention with frame pointers and
/// stack probes, as `n1` does: its bound.
fn bound_for(triple: &str, slot: u32, values: usize) -> usize {
    let mut flags = settings::builder();
    for (name, value) in [
        ("preserve_frame_pointers", "true"),
        ("enable_probestack", "true"),
        ("probestack_strategy", "inline"),
        ("probestack_size_log2", "12"),
    ] {
        flags.set(name, value).unwrap();
    }
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
        let mut y = b.ins().stack_load(isa.pointer_type(), types::I64, slot, 8);
        for _ in 0..values {
            y = b.ins().iadd(y, x);
        }
        b.ins().return_(&[y]);
        b.seal_all_blocks();
        b.finalize(isa.frontend_config());
    }
    let mut context = Context::for_function(func);
    context.compile(&*isa, &mut Default::default()).unwrap();
    frame_bound(&context.func, context.compiled_code().unwrap())
}

#[test]
fn the_bound_covers_the_stack_slots_on_both_architectures() {
    for triple in ["aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"] {
        for slot in [64, 1000, 4000, 20_000] {
            // A frame of a page or more is probed first, and a body of many
            // values is the shape a bound from the IR alone puts at
            // megabytes (SW-2579): neither moves the bound.
            for values in [1, 20_000] {
                let bound = bound_for(triple, slot, values);
                assert!(bound >= slot as usize, "{triple}: {bound} < {slot}");
                assert!(
                    bound < (slot + 300) as usize,
                    "{triple}: {bound} for {slot} bytes and {values} values"
                );
            }
        }
    }
}

/// A function of `v0` mapped over five numbers, its body `levels` pairs of
/// nested `if`s over `Nat` arithmetic, in the shape the effect fuzzer
/// generates.
fn nested_ifs(levels: usize) -> String {
    let mut body = "3".to_string();
    for k in 1..=levels {
        body = format!(
            "if (y * v0 + {k}) % {} == 0 then (y * {k} + v0) % 1000003 else if y % {} == 0 then v0 + {k} else {body}",
            k + 1,
            k + 2
        );
    }
    let mut source = String::from(
        "import Std (IO, List, Nat)\n\n\
         def digest (xs: List Nat): Nat := List.foldLeft xs 7 (acc x => (acc * 31 + x) % 1000003)\n\n",
    );
    let _ = write!(
        source,
        "def p0 (v0: Nat): Nat := digest (List.map (List.range 0 5) (y => {body}))\n\n\
         def main(): {{IO}} () := IO.print \"${{p0 7}}\"\n"
    );
    source
}

/// The lambda of 24 nested `if`s needs about 4.7 KB of frame on x86-64 (4.1
/// on aarch64): more than a page, which a bound once took for 1.8 MB, so
/// the frame limit's stack was over the cap and native code refused the
/// program (SW-2579). The frame grows with the nesting by about 190 bytes
/// an `if` on x86-64.
#[test]
fn a_lambda_of_nested_ifs_has_a_small_frame() {
    with_stack(STACK, || {
        let (program, limits) = lowered(&nested_ifs(12));
        let machine = on_machine(&program, limits);
        let (native, notes) = native(&program, limits, false);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(native, machine);
        let note = notes
            .iter()
            .find(|n| n.starts_with("native: running "))
            .unwrap();
        let frame: usize = note
            .split("frames of at most ")
            .nth(1)
            .and_then(|rest| rest.split(' ').next())
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no frame size in {note}"));
        assert!(frame < 16 * 1024, "{frame} bytes: {notes:#?}");
    });
}
