//! The elaborator's state, by lifetime (docs/proposals/elaborator-state.md).
//!
//! Each component holds the fields of one lifetime, and each mechanism that
//! walks the state (undoing an attempt, per-declaration cleanup, rewinding,
//! the check cache, the canonical dump) is a method that destructures its
//! component exhaustively: a new field doesn't compile until it says what
//! each mechanism does with it.
//!
//! The components planned (§4.1), of which only [`Attempt`] exists so far
//! (§7 step 1); the rest of the state is still fields of the `Elaborator`
//! and of `Globals`:
//!
//! - `Options`: settings given at construction, and the cache key;
//! - `Kernel`: the kernel's half of `Globals` (definitions, data types,
//!   builtins);
//! - `Tables`: what later units read (scope, records, instances, ...), each
//!   table of one of four kinds that says how it is marked, rewound, encoded
//!   and dumped;
//! - `Session`: project and cache bookkeeping, statistics;
//! - `Unit`: the unit being elaborated, swapped while a library file is
//!   loaded inside one;
//! - `Decl`: per-declaration scratch, rebuilt by `Default`;
//! - [`Attempt`]: the inference state a failed attempt takes back;
//! - `Caches`: tables that can be emptied at any time;
//! - `Presentation`: navigation, goals shown, logs.

mod attempt;

pub(crate) use attempt::Attempt;
pub(crate) use attempt::Mark as AttemptMark;
