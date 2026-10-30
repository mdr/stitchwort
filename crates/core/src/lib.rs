//! The core language: core terms, the evaluator (normalisation by evaluation)
//! and the checker for core terms.
//!
//! The checker here is the small trusted kernel that re-checks every
//! definition the elaborator produces (DESIGN.md §11). See `docs/core.md`.

pub mod budget;
pub mod chars;
pub mod check;
pub mod collections;
pub mod erase;
pub mod float;
pub mod globals;
pub mod hash;
pub mod js_repr;
pub mod nat_add;
pub mod native;
pub mod partial;
pub mod pretty;
#[cfg(any(test, feature = "reference"))]
pub mod reference;
pub mod registry;
pub mod sct;
pub mod step;
pub mod term;
pub mod termination;
pub mod unify_index;
pub mod value;

pub use budget::{Limits, ResourceError};
pub use globals::Globals;
pub use num_bigint::BigUint;
pub use term::{DataId, DefId, Icit, MAX_LEVEL, Name, QuotForm, Sort, Term};
pub use value::Value;
