//! The fast runtime (docs/proposals/fast-runtime.md, D381): a separate,
//! untrusted evaluator for running programs. Like the JS backend, it can
//! only get a program's output wrong, never make a false proof check, and
//! it's checked by differential tests against the reference evaluator.
//!
//! Stage 1 is the erased IR ([`ir`]) and the lowering of checked
//! definitions to it ([`lower`]), with a pretty-printer ([`pretty`]).
//! Stage 2 is the machine that runs it: the IR compiled to register code
//! ([`code`]), run with its own frame stack ([`machine`]) on compact values
//! ([`value`]), and a runner for `main` that performs its `IO` ([`run`]).
//! The erasure decisions and native bindings are shared with the JS backend
//! ([`erasure`], [`natives`]; D389).

pub mod code;
pub mod effect;
pub mod erasure;
pub mod host;
pub mod ir;
pub mod lower;
pub mod machine;
pub mod natives;
pub mod opt;
pub mod pretty;
mod prims;
pub mod run;
pub mod specialise;
mod validate;
pub mod value;

pub use ir::Program;
pub use lower::{lower_definitions, lower_global, lower_main};
pub use machine::{Limits, Machine};
pub use run::{Outcome, Policy, RouteCounts, run_main, run_main_counting, run_main_with};
