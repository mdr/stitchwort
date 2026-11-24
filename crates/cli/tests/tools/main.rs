//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod audit;
mod auto_membership_speed;
mod axioms;
mod broken_pipe;
mod check_early;
mod dev_doc;
mod dev_tree;
mod doc;
mod doc_equations;
mod fmt;
mod guide;
mod indexed_families;
mod kernel_dump;
mod lambda_shadow;
mod no_effect;
mod opcode_census;
mod open_goals;
mod oracle;
mod project;
mod receiver_first;
mod redundant_arms;
mod scope;
mod sealed_theorems;
mod statement_style;
mod std_dir;
mod step_counts;
mod sweep;
mod test_failures;
mod test_json;
mod timings;
mod trial_edits;
mod uses;
mod warning_pins;
mod work_limit;

use stitchwort_test_alloc as _;
