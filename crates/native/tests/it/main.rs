//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod common;
mod frames;
mod n1;
mod n2b;
mod n3;
mod n4;
mod object;
mod relocatable;
mod reuse;
mod s6;
mod spike;

use stitchwort_test_alloc as _;
