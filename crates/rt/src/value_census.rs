//! A census of the values a run makes (docs/proposals/compact-values.md,
//! "V0"; docs/reviews/SW-2425-value-census.md): how many cells, closures and
//! other objects it allocates and of what size, what kinds of values it
//! stores into their fields, and the peak of what is live, each counted as
//! the layouts of today and of the note's options C, E and A would size it.
//! A measurement tool; it changes nothing the machine does.
//!
//! With the cargo feature `value-census`, the bytecode machine counts every
//! allocation (cells through [`crate::alloc_trace::alloc`], the rest through
//! the `new_*` constructors) and, when the environment variable
//! `STITCHWORT_VALUE_CENSUS` names a file, writes the counts there as
//! `key value` lines when the process exits. Without the feature every hook
//! is an empty `#[inline(always)]` function, so no shipped or test build pays
//! for it.
//!
//! The sizes of the four models, per object (`n` fields, `k` captures, `v`
//! the number of `Value` slots in the largest variant of an enum):
//!
//! | object | today | C | E | A |
//! |---|---|---|---|---|
//! | cell | 16 + 24n | 8 + 24n | 8 + 16n | 8 + 8n |
//! | `Fun`, `Delay`, `Handler`, `Resume`, `StateRun` (size `S`) | 16 + S | 16 + S | 16 + S - 8v | 8 + S - 16v |
//! | closure's captures | 24k | 24k | 16k | (in the closure) |
//! | closure / `Pap` under A | | | | 16 + 8k / 24 + 8k |
//! | array of `m` | 40 + 24m | 40 + 24m | 40 + 16m | 24 + 8m |
//! | text, big number | 16 + len, 40 + 8 limbs | same | same | same |
//!
//! Under A a scalar that does not fit 61 bits (a `Nat` of 2^61 or more, an
//! `Int` outside +-2^60, any `Float`) stored in a cell field or a capture is
//! a 16-byte box; those are added to A's allocated bytes.

#[cfg(feature = "value-census")]
mod enabled;

use std::rc::Rc;

use crate::effect::{Handler, StateRun};
use crate::value::{Delay, Fun, Value};

/// A cell of `tag` with these fields has been allocated.
#[inline(always)]
pub(crate) fn cell(fields: &[Value]) {
    #[cfg(feature = "value-census")]
    enabled::cell(fields);
    #[cfg(not(feature = "value-census"))]
    let _ = fields;
}

/// A cell was refilled in place (`CtorReuse`).
#[inline(always)]
pub(crate) fn cell_reuse(fields: &[Value]) {
    #[cfg(feature = "value-census")]
    enabled::cell_reuse(fields);
    #[cfg(not(feature = "value-census"))]
    let _ = fields;
}

/// A cell's last reference went.
#[inline(always)]
pub(crate) fn cell_freed(len: usize) {
    #[cfg(feature = "value-census")]
    enabled::cell_freed(len);
    #[cfg(not(feature = "value-census"))]
    let _ = len;
}

/// `Rc::new(f)`, counted.
#[inline(always)]
pub fn new_fun(f: Fun) -> Rc<Fun> {
    #[cfg(feature = "value-census")]
    enabled::fun(&f, true);
    Rc::new(f)
}

/// A `Fun` is being dropped (its last reference went).
#[inline(always)]
pub(crate) fn fun_freed(f: &Fun) {
    #[cfg(feature = "value-census")]
    enabled::fun(f, false);
    #[cfg(not(feature = "value-census"))]
    let _ = f;
}

/// `Rc::new(d)`, counted.
#[inline(always)]
pub fn new_delay(d: Delay) -> Rc<Delay> {
    #[cfg(feature = "value-census")]
    enabled::delay(&d, true);
    Rc::new(d)
}

/// A `Delay` is being dropped.
#[inline(always)]
pub(crate) fn delay_freed(d: &Delay) {
    #[cfg(feature = "value-census")]
    enabled::delay(d, false);
    #[cfg(not(feature = "value-census"))]
    let _ = d;
}

/// `Rc::new(r)`, counted.
#[inline(always)]
pub fn new_state_run(r: StateRun) -> Rc<StateRun> {
    #[cfg(feature = "value-census")]
    enabled::state_run();
    Rc::new(r)
}

/// `Rc::new(h)`, counted.
#[inline(always)]
pub fn new_handler(h: Handler) -> Rc<Handler> {
    #[cfg(feature = "value-census")]
    enabled::handler();
    Rc::new(h)
}

/// An array of `len` elements has been made.
#[inline(always)]
pub(crate) fn array(len: usize) {
    #[cfg(feature = "value-census")]
    enabled::array(len);
    #[cfg(not(feature = "value-census"))]
    let _ = len;
}

/// A text of `len` bytes has been made.
#[inline(always)]
pub(crate) fn text(len: usize) {
    #[cfg(feature = "value-census")]
    enabled::text(len);
    #[cfg(not(feature = "value-census"))]
    let _ = len;
}

/// A big number of `limbs` 64-bit digits has been made.
#[inline(always)]
pub(crate) fn big(limbs: usize) {
    #[cfg(feature = "value-census")]
    enabled::big(limbs);
    #[cfg(not(feature = "value-census"))]
    let _ = limbs;
}

/// An element was pushed onto an array in place.
#[inline(always)]
pub(crate) fn array_push() {
    #[cfg(feature = "value-census")]
    enabled::array_push();
}
