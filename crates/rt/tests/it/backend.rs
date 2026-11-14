//! What `differential.rs`'s cases run on: the machine.

use stitchwort_rt::{Limits, Program};

use crate::differential::Run;

/// For messages: what the cases ran on.
pub const NAME: &str = "machine";

/// Whether this is the native copy (`stitchwort-native`'s `backend.rs`).
pub const NATIVE: bool = false;

/// `program`'s `main` on the machine with `input`: what it printed, and how
/// it ended.
pub fn run(program: &Program, limits: Limits, input: &[u8]) -> Run {
    let mut output = Vec::new();
    let result = stitchwort_rt::run_main(program, limits, &mut &input[..], &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}
