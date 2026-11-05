//! The compiler pipeline, diagnostic rendering and the runner for `main`,
//! shared by the `stitchwort` command and the browser playground.

pub mod at;
pub mod audit;
pub mod axioms;
pub mod check_cache;
pub mod completion;
pub mod counterexample;
pub mod doc;
pub mod driver;
pub mod fingerprint;
pub mod float_gate;
pub mod live;
pub mod nav;
pub mod project;
pub mod render;
pub mod rewind;
pub mod run;
pub mod search;
pub mod search_at;
pub mod test_run;
