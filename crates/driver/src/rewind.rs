//! Rewinding a session and cancelling a check
//! (docs/proposals/language-server.md §5.1 and §3.3, stages 0b and 0c).
//!
//! A language server keeps one session and checks the namespace being
//! edited again and again: it marks the session before the namespace
//! ([`Session::mark`]), and before each new check rewinds to the mark
//! ([`Session::rewind`]). A check made stale by an edit is cancelled through
//! a flag another thread sets ([`Session::cancel_flag`]); the check stops
//! within a fraction of a millisecond of evaluation, and
//! [`Session::cancellable`] then rewinds and says [`Cancelled`] instead of
//! returning what the half-finished check reported.
//!
//! Nothing here reads files or starts threads (D498): the playground's
//! worker can use it as it is. (The worker can't share a flag with the
//! page, so it cancels by ending the worker, as now.)

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::driver::Session;

/// A point a [`Session`] can be rewound to. It stays valid, and can be
/// rewound to any number of times, until the session is rewound to an
/// earlier mark.
pub struct Mark {
    sources: usize,
    warnings: usize,
    elab: stitchwort_elab::Mark,
}

/// A check stopped because the session's cancellation flag was set. What it
/// had found is gone: it is never a diagnostic, and never cached.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cancelled;

impl Session {
    /// Where the session is now. Only between loads, not during one.
    pub fn mark(&self) -> Mark {
        Mark {
            sources: self.sources.len(),
            warnings: self.warnings.len(),
            elab: self.elab.mark(),
        }
    }

    /// Puts the session back as it was at `mark`: the files, declarations,
    /// names, warnings, library files loaded and everything recorded about
    /// them since are forgotten (`stitchwort_elab::rewind`), so checking the
    /// same text again gives what a fresh session gives.
    pub fn rewind(&mut self, mark: &Mark) {
        assert!(
            mark.sources <= self.sources.len(),
            "a mark from after the point the session was rewound to"
        );
        self.sources.truncate(mark.sources);
        self.warnings.truncate(mark.warnings);
        self.elab.rewind(&mark.elab);
    }

    /// The flag that cancels this session's [`Session::cancellable`]
    /// checks: set it (from any thread) to stop the one running. Nothing
    /// else looks at it, so printing or running tests afterwards never
    /// stops; and checking outside `cancellable` costs nothing extra.
    pub fn cancel_flag(&mut self) -> Arc<AtomicBool> {
        let budget = &self.elab.globals.budget;
        if let Some(flag) = budget.cancel_flag() {
            return flag;
        }
        let flag = Arc::new(AtomicBool::new(false));
        budget.set_cancel_flag(flag.clone());
        flag
    }

    /// Runs the check `f` so that it can be cancelled: the flag is cleared
    /// first (a request made before the check began was for an older
    /// one), and if it is set while `f` runs, the session is rewound to
    /// where it was before `f` and the result is [`Cancelled`].
    pub fn cancellable<T>(&mut self, f: impl FnOnce(&mut Session) -> T) -> Result<T, Cancelled> {
        let mark = self.mark();
        self.cancellable_at(&mark, f)
    }

    /// [`Session::cancellable`], with a mark the caller has already taken
    /// (marking costs a few milliseconds in a big session): `mark` must be
    /// where the session is now, and a cancelled check rewinds to it.
    pub fn cancellable_at<T>(
        &mut self,
        mark: &Mark,
        f: impl FnOnce(&mut Session) -> T,
    ) -> Result<T, Cancelled> {
        self.cancel_flag().store(false, Ordering::Relaxed);
        self.elab.globals.budget.watch_cancel(true);
        let result = f(self);
        self.elab.globals.budget.watch_cancel(false);
        if self.elab.globals.budget.cancelled() {
            self.rewind(mark);
            return Err(Cancelled);
        }
        Ok(result)
    }

    /// Makes `flag` the one that cancels this session's checks (instead of
    /// one [`Session::cancel_flag`] makes): one flag can then stop whichever
    /// of several sessions is checking.
    pub fn share_cancel_flag(&mut self, flag: Arc<AtomicBool>) {
        self.elab.globals.budget.set_cancel_flag(flag);
    }
}
