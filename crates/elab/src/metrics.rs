//! The outcome lines that `STITCHWORT_MATCH_METRICS` and
//! `STITCHWORT_REWRITE_METRICS` print to stderr, which a test can also
//! collect in-process (`-- metrics:` headers in `examples/accept`).
//!
//! A line is `<what>: <outcome> at=<position>`; the collected form drops
//! the position, so an example names an outcome without naming where.
//! Collection is per thread, matching one elaboration per thread.

use std::cell::RefCell;
use std::fmt::Display;

thread_local! {
    static COLLECTED: RefCell<Option<Vec<String>>> = const { RefCell::new(None) };
}

/// Starts collecting this thread's outcome lines (dropping any collected
/// before), whether or not the environment variables are set.
pub fn start_collecting() {
    COLLECTED.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

/// Stops collecting and returns the lines, without positions, in the order
/// they happened.
pub fn finish_collecting() -> Vec<String> {
    COLLECTED.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// Whether an outcome for `var` is wanted: the variable is set, or this
/// thread is collecting.
pub(crate) fn wanted(var: &str) -> bool {
    std::env::var_os(var).is_some() || COLLECTED.with(|c| c.borrow().is_some())
}

/// Prints `outcome at=<at>` if `var` is set, and collects `outcome` if this
/// thread is collecting.
pub(crate) fn emit(var: &str, outcome: &str, at: impl Display) {
    if std::env::var_os(var).is_some() {
        eprintln!("{outcome} at={at}");
    }
    COLLECTED.with(|c| {
        if let Some(lines) = c.borrow_mut().as_mut() {
            lines.push(outcome.to_string());
        }
    });
}
