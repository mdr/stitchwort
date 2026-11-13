//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod common;
mod faults;
mod features;
mod memory;
mod profile;
mod rename;

use stitchwort_test_alloc as _;
