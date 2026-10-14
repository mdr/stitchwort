//! The core language: core terms, the evaluator (normalisation by evaluation)
//! and the checker for core terms.
//!
//! The checker here is the small trusted kernel that re-checks every
//! definition the elaborator produces (DESIGN.md §11). See `docs/core.md`.

pub mod check;
pub mod globals;
pub mod hash;
pub mod pretty;
pub mod term;
mod termination;
pub mod value;

pub use globals::Globals;
pub use term::{DataId, DefId, Icit, Name, Sort, Term};
pub use value::Value;
