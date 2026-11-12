//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod admission;
mod assumptions;
mod case_other_type;
mod common;
mod data_groups;
mod fuzz;
mod glue;
mod groups;
mod hash;
mod indexed;
mod inert_after_j;
mod kernel;
mod kernel_bugs_2026;
mod let_term;
mod opaque;
mod pending;
mod pretty;
mod quot;
mod rebuild;
mod record_eta;
mod sct;
mod structural;
mod termination;
mod trusted;
mod unify_index;
mod universe_levels;

use stitchwort_test_alloc as _;
