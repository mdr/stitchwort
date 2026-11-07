//! The `stitchwort` command. The pipeline itself lives in `stitchwort-driver`;
//! it's re-exported here for the tests, as is the language server
//! (`stitchwort-lsp`).

#[cfg(test)]
use stitchwort_test_alloc as _;

pub use stitchwort_lsp as lsp;
#[cfg(unix)]
pub mod node_wait;
pub mod search_log;

pub use stitchwort_driver::{counterexample, driver, nav, project, render, run};
