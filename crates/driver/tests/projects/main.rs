//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

// These tests read back with `value::quote` directly (see clippy.toml: the
// entry guards the elaborator's read-backs).
#![allow(clippy::disallowed_methods)]

mod check_cache;
mod compact_text;
mod doc_links;
mod examples_wide;
mod include;
mod multi_file;
mod namespaces;
mod navigation;
mod parallel;
mod project;
mod project_analysis;
mod references;
mod rewind;
mod run;
mod test_cache_key;
mod trial;

use stitchwort_test_alloc as _;
