//! The `stitchwort` command. The pipeline itself lives in `stitchwort-driver`;
//! it's re-exported here for the tests. The language server is here.

pub mod lsp;

pub use stitchwort_driver::{driver, nav, project, render, run};
