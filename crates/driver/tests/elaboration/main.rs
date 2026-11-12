//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod ability_errors;
mod at;
mod bool_clash;
mod bool_props;
mod chars;
mod ctor_fields;
mod division;
mod dot_prefix;
mod empty_row_kernel;
mod erasure;
mod float;
mod indexed_families;
mod inert_params;
mod int;
mod int_patterns;
mod interfaces;
mod lambda_migration;
mod lambda_printer;
mod named_arguments;
mod natives;
mod negative_arguments;
mod nesting;
mod number_patterns;
mod operators;
mod pipe_forms;
mod postponement;
mod prelude_errors;
mod readings;
mod records;
mod signature_defaults;
mod text_interpolation;

use stitchwort_test_alloc as _;
