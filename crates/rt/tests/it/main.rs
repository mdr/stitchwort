//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod alloc_trace;
mod arrays;
mod clause_kinds;
mod codec;
mod effect_runtime;
mod interp;
mod linked;
mod live_run;
mod lower;
mod machine;
mod partial_handlers;
mod profile;
mod tick_counts;

use stitchwort_test_alloc as _;
