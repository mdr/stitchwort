//! The compiler pipeline, diagnostic rendering and the runner for `main`,
//! shared by the `stitchwort` command and the browser playground.

pub mod audit;
pub mod axioms;
pub mod check_cache;
pub mod counterexample;
pub mod driver;
pub mod fingerprint;
pub mod float_gate;
pub mod live;
pub mod nav;
pub mod project;
pub mod render;
pub mod rewind;
pub mod run;
