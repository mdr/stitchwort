//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod call_fields;
mod common;
mod conv_shortcut;
mod counterexamples;
mod decision_search;
mod decreasing_fallback;
mod decreasing_twins;
mod differential;
mod eta_fields;
mod eta_hold;
mod function_equations;
mod function_induct;
mod generated_rows;
mod nat_add_rule;
mod nested_oracle;
mod partial;
mod partial_kernel;
mod proof_equivalence;
mod proof_masks;
mod rewrite;
mod stand_ins;
mod update_lemmas;

use stitchwort_test_alloc as _;
