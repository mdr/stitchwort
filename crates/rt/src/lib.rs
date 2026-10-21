//! The fast runtime (docs/proposals/fast-runtime.md, D381): a separate,
//! untrusted evaluator for running programs. Like the JS backend, it can
//! only get a program's output wrong, never make a false proof check, and
//! it's checked by differential tests against the reference evaluator.
//!
//! Stage 1 is the erased IR ([`ir`]) and the lowering of checked
//! definitions to it ([`lower`]), with a pretty-printer ([`pretty`]). The
//! erasure decisions and native bindings are shared with the JS backend
//! ([`erasure`], [`natives`]; D389).

pub mod erasure;
pub mod ir;
pub mod lower;
pub mod natives;
pub mod pretty;
mod validate;

pub use ir::Program;
pub use lower::{lower_definitions, lower_global, lower_main};
