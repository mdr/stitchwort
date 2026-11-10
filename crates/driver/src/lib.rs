//! The compiler pipeline, diagnostic rendering and the runner for `main`,
//! shared by the `stitchwort` command and the browser playground.

#[cfg(test)]
use stitchwort_test_alloc as _;

pub mod at;
pub mod audit;
pub mod axioms;
pub mod binder_sweep;
pub mod check_cache;
pub mod completion;
pub mod counterexample;
pub mod declhash;
pub mod doc;
pub mod driver;
pub mod fingerprint;
pub mod float_gate;
pub mod live;
pub mod marks;
pub mod nav;
pub mod project;
pub mod rename;
pub mod render;
pub mod rewind;
pub mod run;
pub mod search;
pub mod search_at;
pub mod test_run;
