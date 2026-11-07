//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod api;
mod fuzz;
mod golden;
mod repo;
mod support;

use stitchwort_test_alloc as _;
