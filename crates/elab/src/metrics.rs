//! The outcome lines that `STITCHWORT_MATCH_METRICS` and
//! `STITCHWORT_REWRITE_METRICS` print to stderr, which a test can also
//! collect in-process (`-- metrics:` headers in `examples/accept`).
//!
//! A line is `<what>: <outcome> at=<position>`; the collected form drops
//! the position, so an example names an outcome without naming where.
//! Collection is per thread, matching one elaboration per thread.
//! `STITCHWORT_TRACE_GUARDS` uses [`trace`] instead: it prints for a
//! person watching the run and is never collected.

use std::cell::RefCell;
use std::fmt::Display;
use std::sync::OnceLock;

thread_local! {
    static COLLECTED: RefCell<Option<Vec<String>>> = const { RefCell::new(None) };
}

static MATCH_METRICS: OnceLock<bool> = OnceLock::new();
static REWRITE_METRICS: OnceLock<bool> = OnceLock::new();
static TRACE_GUARDS: OnceLock<bool> = OnceLock::new();

/// Whether `var` is set, read once for the switches this module knows.
pub(crate) fn env_on(var: &str) -> bool {
    match var {
        "STITCHWORT_MATCH_METRICS" => {
            *MATCH_METRICS.get_or_init(|| std::env::var_os(var).is_some())
        }
        "STITCHWORT_REWRITE_METRICS" => {
            *REWRITE_METRICS.get_or_init(|| std::env::var_os(var).is_some())
        }
        "STITCHWORT_TRACE_GUARDS" => *TRACE_GUARDS.get_or_init(|| std::env::var_os(var).is_some()),
        _ => std::env::var_os(var).is_some(),
    }
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
    env_on(var) || COLLECTED.with(|c| c.borrow().is_some())
}

/// Prints `outcome at=<at>` if `var` is set, without collecting: a trace is
/// for someone watching this run, not a test's `-- metrics:` header.
pub(crate) fn trace(var: &str, outcome: &str, at: impl Display) {
    if env_on(var) {
        eprintln!("{outcome} at={at}");
    }
}

/// Prints `outcome at=<at>` if `var` is set, and collects `outcome` if this
/// thread is collecting.
pub(crate) fn emit(var: &str, outcome: &str, at: impl Display) {
    if env_on(var) {
        eprintln!("{outcome} at={at}");
    }
    COLLECTED.with(|c| {
        if let Some(lines) = c.borrow_mut().as_mut() {
            lines.push(outcome.to_string());
        }
    });
}
