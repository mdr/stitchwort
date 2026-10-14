//! The core language: core terms, the evaluator (normalisation by evaluation)
//! and the checker for core terms.
//!
//! The checker here is meant to become the small trusted kernel that re-checks
//! every elaborated definition (DESIGN.md §11). For now it is also the only
//! type checker: the elaborator just desugars. See `docs/core.md`.

pub mod check;
pub mod globals;
pub mod pretty;
pub mod term;
mod termination;
pub mod value;

pub use globals::Globals;
pub use term::{DataId, DefId, Icit, Name, Sort, Term};
pub use value::Value;
