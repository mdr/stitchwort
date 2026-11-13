//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod audit;
mod auto_membership_speed;
mod axioms;
mod broken_pipe;
mod doc;
mod doc_equations;
mod fmt;
mod fmt_repo;
mod guide;
mod indexed_families;
mod lambda_shadow;
mod no_effect;
mod opcode_census;
mod open_goals;
mod project;
mod receiver_first;
mod redundant_arms;
mod scope;
mod statement_style;
mod std_dir;
mod sweep;
mod test_failures;
mod test_json;
mod timings;
mod trial_edits;

use stitchwort_test_alloc as _;
