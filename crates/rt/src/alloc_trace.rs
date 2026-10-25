//! The bring-up allocation trace (docs/proposals/native-compilation.md,
//! "Bring-up trace (N1 to N4)").
//!
//! With the cargo feature `alloc-trace`, the machine records every
//! `alloc`, `reuse`, `inc`, `dec` and `free` of a constructor cell (the
//! reference-counted [`Fields`](crate::value::Fields) array behind
//! `Value::Data`), so that native code can be compared with the machine
//! event by event: the first differing event points at the bug.
//!
//! - `alloc #id tag=T arity=N`: a new cell.
//! - `reuse #id tag=T arity=N`: a unique cell refilled in place by
//!   `CtorReuse` (it keeps its identity).
//! - `inc #id`, `dec #id`: a reference taken or released. The last `dec`
//!   is followed by `free #id`.
//!
//! Identities are the cells' addresses, renumbered in order of first
//! appearance; an address that is freed and later reused is a new identity.
//! Two runs of the same program give the same text.
//!
//! Not traced: closures, partial applications, delays, texts and big
//! numbers (not `Fields`). They can be added here when the native
//! bring-up needs them.
//!
//! Without the feature, every hook is an empty `#[inline(always)]`
//! function, so the compiled machine is the same as before; the release
//! `stitchwort` binary is built without it. Why a feature and not
//! `cfg(debug_assertions)`: the tests run in release mode, and a feature
//! keeps the trace out of the shipped binary without losing it from
//! optimised test runs.

#[cfg(feature = "alloc-trace")]
mod enabled;
#[cfg(feature = "alloc-trace")]
pub use enabled::{Event, Trace, finish, start};

use std::rc::Rc;

use crate::value::Value;

/// Whether this build records traces.
pub const ENABLED: bool = cfg!(feature = "alloc-trace");

/// A new cell of `tag` with `fields`.
#[inline(always)]
pub(crate) fn alloc(tag: u32, fields: &Rc<[Value]>) {
    #[cfg(feature = "alloc-trace")]
    enabled::record(
        enabled::Kind::Alloc,
        Rc::as_ptr(fields).cast(),
        tag,
        fields.len(),
    );
    #[cfg(not(feature = "alloc-trace"))]
    let _ = (tag, fields);
}

/// A cell refilled in place as `tag`.
#[inline(always)]
pub(crate) fn reuse(tag: u32, fields: &Rc<[Value]>) {
    #[cfg(feature = "alloc-trace")]
    enabled::record(
        enabled::Kind::Reuse,
        Rc::as_ptr(fields).cast(),
        tag,
        fields.len(),
    );
    #[cfg(not(feature = "alloc-trace"))]
    let _ = (tag, fields);
}

/// A reference to the cell taken.
#[inline(always)]
pub(crate) fn inc(fields: &Rc<[Value]>) {
    #[cfg(feature = "alloc-trace")]
    enabled::record(
        enabled::Kind::Inc,
        Rc::as_ptr(fields).cast(),
        0,
        fields.len(),
    );
    #[cfg(not(feature = "alloc-trace"))]
    let _ = fields;
}

/// A reference to the cell released; `last` if it was the only one, so the
/// cell is freed.
#[inline(always)]
pub(crate) fn dec(fields: &Rc<[Value]>, last: bool) {
    #[cfg(feature = "alloc-trace")]
    {
        let at = Rc::as_ptr(fields).cast();
        enabled::record(enabled::Kind::Dec, at, 0, fields.len());
        if last {
            enabled::record(enabled::Kind::Free, at, 0, fields.len());
        }
    }
    #[cfg(not(feature = "alloc-trace"))]
    let _ = (fields, last);
}
