//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

// The kernel's tests read back with `value::quote_folded` directly (see
// clippy.toml: the entry guards the elaborator's read-backs).
#![allow(clippy::disallowed_methods)]

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
mod kernel;
mod kernel_bugs_2026;
mod let_term;
mod opaque;
mod pending;
mod pretty;
mod proof_marks;
mod quot;
mod rebuild;
mod record_eta;
mod rule_k;
mod sct;
mod shared_case;
mod structural;
mod termination;
mod trusted;
mod unify_index;
mod universe_levels;

use stitchwort_test_alloc as _;
