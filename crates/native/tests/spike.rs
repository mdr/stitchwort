//! Stage N0's spike (docs/proposals/native-compilation.md): Cranelift-compiled
//! code that counts steps and frames, calls back into Rust, tail-calls in
//! constant stack and recurses deep on a big stack.

use stitchwort_native::checks::{
    self, BIG_STACK, FRAME_LIMIT, deep_recursion, mutual_tail_calls, self_tail_loop, step_limited,
    triangle,
};
use stitchwort_native::spike::{
    Code, CodeMemory, Context, OK, OUT_OF_FRAMES, OUT_OF_STEPS, Spike, VARIANTS,
};

fn compile() -> (Spike, Code) {
    let spike = Spike::compile().expect("compiling the spike");
    let code = spike.code;
    (spike, code)
}

#[test]
fn every_variant_of_sum_adds_up() {
    let (_spike, code) = compile();
    for variant in VARIANTS {
        let mut context = Context::unlimited();
        assert_eq!(code.sum(variant, &mut context, 1000), triangle(1000));
        assert_eq!(context.error, OK);
        assert_eq!(context.frames, 0, "{variant:?}");
        let counted = if variant.counting { 1001 } else { 0 };
        assert_eq!(context.steps, counted, "{variant:?}");
        let called = if variant.callback { 1000 } else { 0 };
        assert_eq!(context.callbacks, called, "{variant:?}");
    }
}

#[test]
fn the_step_counter_stops_a_loop_on_a_cold_path() {
    let (_spike, code) = compile();
    let (result, context) = step_limited(code, 1000, 3_000_000);
    assert_eq!(result, 0);
    assert_eq!(context.error, OUT_OF_STEPS);
    assert_eq!(context.steps, 1001);
    assert_eq!(context.callbacks, 1000);
}

#[test]
fn a_self_tail_call_runs_3_000_000_steps_in_constant_stack() {
    let (_spike, code) = compile();
    let run = self_tail_loop(code, 3_000_000);
    assert_eq!(run.result, triangle(3_000_000));
    assert_eq!((run.context.error, run.context.steps), (OK, 3_000_001));
    assert_eq!(run.long_depth, run.short_depth);
}

#[test]
fn mutual_tail_calls_run_3_000_000_steps_in_constant_stack() {
    let (_spike, code) = compile();
    let run = mutual_tail_calls(code, 3_000_000);
    assert_eq!(run.result, triangle(3_000_000));
    assert_eq!((run.context.error, run.context.steps), (OK, 3_000_001));
    assert_eq!(run.context.callbacks, 3_000_000);
    assert_eq!(run.context.frames, 0);
    assert_eq!(run.long_depth, run.short_depth);
}

#[test]
fn a_million_deep_non_tail_recursion_fits_the_big_stack() {
    let (_spike, code) = compile();
    let run = deep_recursion(code, 1_000_000);
    assert_eq!(run.result, triangle(1_000_000));
    assert_eq!((run.context.error, run.context.frames), (OK, 0));
    assert_eq!(run.context.steps, 1_000_001);
    // Each pending frame really is on the native stack.
    assert!(run.bytes_per_frame() >= 16.0, "{run:?}");
}

#[test]
fn the_frame_counter_fires_before_the_native_stack_overflows() {
    let (_spike, code) = compile();
    let fits = deep_recursion(code, 1_000_000);
    let too_deep = 100_000_000;
    // Without the counter, this recursion would need more stack than the
    // thread has.
    assert!(too_deep as f64 * fits.bytes_per_frame() > BIG_STACK as f64);
    let run = deep_recursion(code, too_deep);
    assert_eq!(run.result, 0);
    assert_eq!(run.context.error, OUT_OF_FRAMES);
    assert_eq!(run.context.frames, FRAME_LIMIT + 1);
    assert!((FRAME_LIMIT + 1) as f64 * fits.bytes_per_frame() < BIG_STACK as f64);
}

#[test]
fn the_report_runs_in_each_kind_of_code_memory() {
    #[allow(unused_mut)]
    let mut kinds = vec![CodeMemory::System];
    #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
    kinds.push(CodeMemory::MapJit);
    for memory in kinds {
        let report = checks::report(memory, 1_000).unwrap();
        assert!(report.contains("OUT_OF_FRAMES"), "{report}");
    }
}
