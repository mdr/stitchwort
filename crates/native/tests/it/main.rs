//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod backend;
mod common;
#[macro_use]
#[path = "../../../rt/tests/it/differential.rs"]
mod differential;
mod determined_fields;
mod frames;
mod large;
mod machine_native;
mod n1;
mod n2b;
mod n3;
mod n4;
mod nat_shaped;
mod object;
mod relocatable;
mod reuse;
mod roots;
mod s6;
mod spike;

use stitchwort_test_alloc as _;
