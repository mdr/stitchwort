//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod check_cache;
mod compact_text;
mod doc_links;
mod include;
mod multi_file;
mod namespaces;
mod navigation;
mod project;
mod project_analysis;
mod rewind;
mod run;
mod test_cache_key;
mod trial;

use stitchwort_test_alloc as _;
