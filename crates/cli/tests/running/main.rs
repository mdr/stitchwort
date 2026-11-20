//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod common;
#[cfg(unix)]
mod pty;

mod aoc_answers;
mod build;
mod effect_runtime;
mod examples;
mod files;
mod float;
mod float_paths;
#[cfg(unix)]
mod keys_mode;
mod partial_handlers;
mod run;
mod run_js;
mod run_reference;
mod test_files;
mod walk_expand;

use stitchwort_test_alloc as _;
