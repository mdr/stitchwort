//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod alloc_trace;
mod arrays;
mod backend;
mod clause_kinds;
mod codec;
mod dispatch;
#[macro_use]
mod differential;
mod effect_runtime;
mod interp;
mod linked;
mod live_run;
mod lower;
mod machine;
mod partial_handlers;
mod profile;
mod reuse;
mod tick_counts;

use stitchwort_test_alloc as _;
