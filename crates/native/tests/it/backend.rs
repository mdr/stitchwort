//! What `differential.rs`'s cases run on here: native code.

use stitchwort_native::n1::{Options, compile, stack_for};
use stitchwort_rt::host::NoTerminal;
use stitchwort_rt::{Limits, Program, run_main_native};

use crate::differential::{Run, STACK};

/// For messages: what the cases ran on.
pub const NAME: &str = "native code";

/// Whether this is the native copy (`stitchwort-rt`'s `backend.rs` is not).
pub const NATIVE: bool = true;

/// `program`'s `main` compiled to native code as `run --native` compiles it
/// and run with `input`: what it printed, and how it ended. A program native
/// code refuses ends in `Err` with the reason, which the reference
/// evaluator's run never matches. The machine runs nothing.
pub fn run(program: &Program, limits: Limits, input: &[u8]) -> Run {
    let options = Options {
        trace_refcounts: false,
        count_bodies: false,
        pc_map: false,
    };
    let image = stitchwort_rt::code::compile(program);
    let compiled = compile(program, image, options).and_then(|islands| {
        let stack = stack_for(limits.frames as u64, islands.max_frame, &islands.widest)?;
        Ok((islands, stack))
    });
    let (islands, stack) = match compiled {
        Ok(compiled) => compiled,
        Err(why) => {
            return (
                String::new(),
                Err(format!("native refused: {}", why.join("; "))),
            );
        }
    };
    let executed_before = stitchwort_rt::machine::instructions_executed();
    let mut output = Vec::new();
    // The thread's stack (`STACK`, from `with_stack`) is the cap.
    let result = run_main_native(
        Box::new(islands),
        limits,
        stack.min(STACK),
        &mut &input[..],
        &mut output,
        &mut NoTerminal,
    );
    assert_eq!(
        stitchwort_rt::machine::instructions_executed() - executed_before,
        0,
        "the machine ran part of a native run"
    );
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}
