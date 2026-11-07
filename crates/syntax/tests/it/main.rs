//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod fuzz;
mod keywords;
mod layout;
mod trivia;

use stitchwort_test_alloc as _;
