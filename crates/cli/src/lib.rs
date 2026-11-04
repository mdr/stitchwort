//! The `stitchwort` command. The pipeline itself lives in `stitchwort-driver`;
//! it's re-exported here for the tests. The language server is here.

pub mod lsp;
#[cfg(unix)]
pub mod node_wait;
pub mod search_log;

pub use stitchwort_driver::{counterexample, driver, nav, project, render, run};
