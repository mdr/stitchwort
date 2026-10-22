//! Resource limits for one top-level operation: checking a declaration,
//! running a test, or evaluating an expression
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! Running out isn't a type error or a failed test: there's no answer. So it's
//! a separate error, [`ResourceError`], which evaluation, conversion and
//! quotation return and their callers propagate. Once an operation has run
//! out, every later check fails too, until the next operation starts.
//!
//! An operation can also be **cancelled** from another thread, through a
//! flag the host installs ([`Budget::set_cancel_flag`]) and watches while a
//! check runs ([`Budget::watch_cancel`]): a language server stops a check
//! that an edit has made stale (docs/proposals/language-server.md §3.3).
//! While watched, the flag is read when an operation starts and every
//! [`POLL`] evaluation steps, on [`Budget::step`]'s slow path, so the fast
//! path is the same comparison as without it. Once seen, cancellation is
//! sticky: every later operation fails at once with
//! [`ResourceError::Cancelled`] until [`Budget::reset`]. It's never an
//! answer, so the session layer drops whatever the cancelled check reported
//! and rewinds.

use std::cell::{Cell, RefCell};
use std::fmt;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::stack::position as stack_position;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceError {
    /// Too many evaluation steps.
    Work,
    /// Recursion too deep for the stack this operation may use.
    Depth,
    /// A term or expression nested too deeply for one of the passes that
    /// recurse over them (named here) to follow.
    Nesting(&'static str),
    /// A value too large to turn back into a term or print.
    Size,
    /// The host asked for the check to stop ([`Budget::set_cancel_flag`]).
    /// Not a result: the session layer discards the check and rewinds, so
    /// this never reaches a user or a cache.
    Cancelled,
}

impl fmt::Display for ResourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ResourceError::Work => "it took more evaluation steps than allowed",
            ResourceError::Depth => "it recursed more deeply than allowed",
            ResourceError::Nesting(pass) => {
                return write!(f, "the program is nested too deeply for the {pass}");
            }
            ResourceError::Size => "a value was too large to show",
            ResourceError::Cancelled => "the check was cancelled",
        })
    }
}

impl From<ResourceError> for Diagnostic {
    fn from(e: ResourceError) -> Diagnostic {
        Diagnostic::error("E-RESOURCE", format!("ran out of resources: {e}")).with_note(
            "this isn't a type error or a failed test: there's no answer within the limits",
        )
    }
}

pub type Result<T> = std::result::Result<T, ResourceError>;

/// Limits for one operation.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Evaluation steps.
    pub work: u64,
    /// Bytes of Rust stack the operation may use, measured from where it
    /// started. Must be comfortably less than the thread's stack.
    pub stack: usize,
    /// Nodes in a quoted term.
    pub size: u64,
    /// Frames of pending work in the evaluator: how deeply a program may
    /// recurse. A frame keeps its environment alive, so in practice each
    /// costs a few hundred bytes: `length (replicate 1000000 1)`, a million
    /// frames deep, peaks at about 750 MB.
    pub frames: usize,
}

impl Limits {
    /// For a thread with `stack_size` bytes of stack, leaving a quarter (and
    /// at least 256 KiB) for whatever runs outside the guarded functions.
    pub fn for_stack(stack_size: usize) -> Limits {
        let reserve = (stack_size / 4).max(256 * 1024);
        Limits {
            work: 10_000_000_000,
            stack: stack_size.saturating_sub(reserve),
            size: 10_000_000,
            frames: 2_000_000,
        }
    }

    /// Only `stack` bytes of stack: for passes over checked declarations
    /// (like generating JavaScript), whose only limit is how deeply they may
    /// recurse. Evaluating a checked type can't run out of anything else.
    pub fn stack_only(stack: usize) -> Limits {
        Limits {
            work: u64::MAX,
            stack,
            size: u64::MAX,
            frames: usize::MAX,
        }
    }
}

impl Default for Limits {
    /// Safe on a 2 MiB thread: Rust's default for spawned threads and tests.
    fn default() -> Limits {
        Limits::for_stack(2 * 1024 * 1024)
    }
}

/// How many evaluation steps pass between two looks at the cancellation
/// flag: a fraction of a millisecond.
pub const POLL: u64 = 1 << 14;

/// What one operation has used so far. Lives in [`crate::Globals`]; an
/// operation starts with [`Budget::operation`].
#[derive(Debug)]
pub struct Budget {
    work: Cell<u64>,
    /// Steps taken by operations that have ended, for [`Budget::total_work`].
    finished_work: Cell<u64>,
    /// Calls to [`Budget::nesting`], ever: see [`Budget::total_visits`].
    visits: Cell<u64>,
    /// Where [`Budget::step`] leaves its fast path: `limit`, or the next
    /// look at the cancellation flag if that's sooner, and 0 once the
    /// operation has run out, so that the fast path is one comparison.
    work_limit: Cell<u64>,
    /// The steps the operation may take: `u64::MAX` outside one.
    limit: Cell<u64>,
    /// The lowest stack address the operation may reach: 0 outside one.
    stack_floor: Cell<usize>,
    /// `usize::MAX` outside an operation.
    frame_limit: Cell<usize>,
    limits: Cell<Option<Limits>>,
    exhausted: Cell<Option<ResourceError>>,
    /// The host's cancellation flag, if it installed one.
    cancel: RefCell<Option<Arc<AtomicBool>>>,
    /// Whether the flag is being watched: only a check the host can cancel
    /// looks at it, so that printing or running afterwards never stops.
    watching: Cell<bool>,
    /// Whether the flag has been seen set: from then on every operation
    /// fails with [`ResourceError::Cancelled`], until [`Budget::reset`].
    cancelled: Cell<bool>,
}

impl Default for Budget {
    fn default() -> Budget {
        Budget {
            work: Cell::new(0),
            finished_work: Cell::new(0),
            visits: Cell::new(0),
            work_limit: Cell::new(u64::MAX),
            limit: Cell::new(u64::MAX),
            stack_floor: Cell::new(0),
            frame_limit: Cell::new(usize::MAX),
            limits: Cell::new(None),
            exhausted: Cell::new(None),
            cancel: RefCell::new(None),
            watching: Cell::new(false),
            cancelled: Cell::new(false),
        }
    }
}

/// While this is alive, an operation is running. Dropping it restores
/// whatever was running before (usually nothing).
#[must_use]
pub struct Operation<'b> {
    budget: &'b Budget,
    previous: Option<Saved>,
}

impl Drop for Operation<'_> {
    fn drop(&mut self) {
        if let Some(saved) = self.previous.take() {
            self.budget.restore(saved);
        }
    }
}

/// What was running before [`Budget::start`], for [`Budget::restore`].
#[must_use]
pub struct Saved {
    work: u64,
    limit: u64,
    stack_floor: usize,
    frame_limit: usize,
    limits: Option<Limits>,
    exhausted: Option<ResourceError>,
}

impl Budget {
    /// Starts an operation with fresh counters, measuring stack use from here.
    /// It ends when the guard is dropped.
    pub fn operation(&self, limits: Limits) -> Operation<'_> {
        Operation {
            budget: self,
            previous: Some(self.start(limits)),
        }
    }

    /// Like [`Budget::operation`], for callers that can't hold a borrow of
    /// the budget: the operation ends with [`Budget::restore`].
    pub fn start(&self, limits: Limits) -> Saved {
        let saved = Saved {
            work: self.work.replace(0),
            limit: self.limit.replace(limits.work),
            stack_floor: self
                .stack_floor
                .replace(stack_position().saturating_sub(limits.stack)),
            frame_limit: self.frame_limit.replace(limits.frames),
            limits: self.limits.replace(Some(limits)),
            exhausted: self.exhausted.replace(None),
        };
        if self.cancel_requested() {
            self.exhausted.set(Some(ResourceError::Cancelled));
        }
        self.arm();
        saved
    }

    pub fn restore(&self, saved: Saved) {
        self.finished_work
            .set(self.finished_work.get() + self.work.get());
        self.work.set(saved.work);
        self.limit.set(saved.limit);
        self.stack_floor.set(saved.stack_floor);
        self.frame_limit.set(saved.frame_limit);
        self.limits.set(saved.limits);
        let exhausted = if self.cancelled.get() {
            Some(ResourceError::Cancelled)
        } else {
            saved.exhausted
        };
        self.exhausted.set(exhausted);
        self.arm();
    }

    /// Sets where [`Budget::step`] next leaves its fast path, from the
    /// limit, the cancellation flag and whether the operation has run out.
    fn arm(&self) {
        let at = if self.exhausted.get().is_some() {
            0
        } else if self.watching.get() {
            self.limit.get().min(self.work.get().saturating_add(POLL))
        } else {
            self.limit.get()
        };
        self.work_limit.set(at);
    }

    /// Installs the flag that cancels operations while it's watched (see
    /// the module's comment).
    pub fn set_cancel_flag(&self, flag: Arc<AtomicBool>) {
        *self.cancel.borrow_mut() = Some(flag);
        self.arm();
    }

    /// Starts or stops watching the flag. While it's watched and another
    /// thread sets it, the operation running stops within [`POLL`] steps,
    /// and every later one at its start.
    pub fn watch_cancel(&self, on: bool) {
        self.watching.set(on && self.cancel.borrow().is_some());
        self.arm();
    }

    /// The flag installed, if any.
    pub fn cancel_flag(&self) -> Option<Arc<AtomicBool>> {
        self.cancel.borrow().clone()
    }

    /// Whether cancellation has been seen: what has been checked since
    /// isn't a result.
    pub fn cancelled(&self) -> bool {
        self.cancelled.get()
    }

    /// Whether the flag is watched and set (or was seen set), noting it if
    /// so.
    fn cancel_requested(&self) -> bool {
        if !self.cancelled.get()
            && self.watching.get()
            && self
                .cancel
                .borrow()
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Relaxed))
        {
            self.cancelled.set(true);
        }
        self.cancelled.get()
    }

    /// Back to no operation running, and not cancelled: for a session
    /// rewound after a check stopped part way (the operations it was in are
    /// gone). The totals and the flag stay; the flag's owner clears it.
    pub fn reset(&self) {
        self.work.set(0);
        self.limit.set(u64::MAX);
        self.stack_floor.set(0);
        self.frame_limit.set(usize::MAX);
        self.limits.set(None);
        self.exhausted.set(None);
        self.cancelled.set(false);
        self.arm();
    }

    /// Every evaluation step taken so far, in all operations and outside
    /// them: a measure of work that, unlike time, is the same on every run
    /// (for benchmarks). Exact between operations; while one is running, it
    /// leaves out the steps of any operation it interrupted.
    pub fn total_work(&self) -> u64 {
        self.finished_work.get() + self.work.get()
    }

    /// Every level of every recursive pass so far (each call to
    /// [`Budget::nesting`]): the work of the elaborator, type checker,
    /// printer and so on, which isn't evaluation and so isn't counted as
    /// steps. Like [`Budget::total_work`], it's for benchmarks.
    pub fn total_visits(&self) -> u64 {
        self.visits.get()
    }

    /// Runs `f` allowed at most `*remaining` more evaluation steps, and
    /// takes what it used off `*remaining`. `Ok(None)` if `f` went over:
    /// that is the caller's own limit, not the operation running out, so
    /// the operation carries on (`rewrite`'s search budget). Running out of
    /// anything else, or of the operation's own steps, is an error as usual
    /// (`f`'s own error, if it converts the resource error to one).
    pub fn limited<T, E>(
        &self,
        remaining: &mut u64,
        f: impl FnOnce() -> std::result::Result<T, E>,
    ) -> std::result::Result<Option<T>, E> {
        let before = self.work.get();
        if self.exhausted.get().is_some() {
            return f().map(Some);
        }
        let outer = self.limit.get();
        let cap = before.saturating_add(*remaining).min(outer);
        self.limit.set(cap);
        self.arm();
        let result = f();
        let used = self.work.get().saturating_sub(before);
        *remaining = remaining.saturating_sub(used);
        if cap < outer && self.exhausted.get() == Some(ResourceError::Work) && self.work.get() > cap
        {
            self.exhausted.set(None);
            self.limit.set(outer);
            self.arm();
            *remaining = 0;
            return Ok(None);
        }
        if self.exhausted.get().is_none() {
            self.limit.set(outer);
            self.arm();
        }
        result.map(Some)
    }

    /// The error the current operation ran out with, if it did.
    pub fn exhausted(&self) -> Option<ResourceError> {
        self.exhausted.get()
    }

    /// The largest term [`crate::value::quote`] may build.
    pub fn size_limit(&self) -> u64 {
        self.limits.get().map_or(u64::MAX, |l| l.size)
    }

    /// One evaluation step, at the current depth. Called at the start of every
    /// recursive evaluation, conversion and quotation function. Once an
    /// operation has run out, every later step fails too.
    #[inline]
    pub fn step(&self) -> Result<()> {
        let work = self.work.get() + 1;
        self.work.set(work);
        if work > self.work_limit.get() || stack_position() < self.stack_floor.get() {
            return self.slow_step(work);
        }
        Ok(())
    }

    /// [`Budget::step`] off its fast path: out of steps or stack, or time
    /// to look at the cancellation flag.
    #[cold]
    #[inline(never)]
    fn slow_step(&self, work: u64) -> Result<()> {
        if self.exhausted.get().is_none()
            && work <= self.limit.get()
            && stack_position() >= self.stack_floor.get()
        {
            if self.cancel_requested() {
                self.exhausted.set(Some(ResourceError::Cancelled));
                self.work_limit.set(0);
                return Err(ResourceError::Cancelled);
            }
            self.arm();
            return Ok(());
        }
        Err(self.run_out(work))
    }

    /// One level of a pass that recurses on the Rust stack over terms or
    /// syntax (the elaborator, the type checker, the printer, …): fails once
    /// the operation has used the stack it may, or has run out of anything
    /// else. Not an evaluation step, so it doesn't count as work.
    #[inline]
    pub fn nesting(&self, pass: &'static str) -> Result<()> {
        self.visits.set(self.visits.get() + 1);
        if stack_position() < self.stack_floor.get() || self.work_limit.get() == 0 {
            return Err(self.too_deep(pass));
        }
        Ok(())
    }

    /// Whether the operation has used the stack it may, without stopping it:
    /// for printing, which shows what it can't reach as `…`.
    #[inline]
    pub fn stack_exhausted(&self) -> bool {
        stack_position() < self.stack_floor.get()
    }

    /// The evaluator is about to have `frames` frames of pending work.
    #[inline]
    pub fn frames(&self, frames: usize) -> Result<()> {
        if frames > self.frame_limit.get() {
            let e = self.exhausted.get().unwrap_or(ResourceError::Depth);
            self.exhausted.set(Some(e));
            self.work_limit.set(0);
            return Err(e);
        }
        Ok(())
    }

    /// Stops the operation because `pass` can't go deeper. Returns the error
    /// to report: the first one, if the operation had already run out.
    #[cold]
    pub fn too_deep(&self, pass: &'static str) -> ResourceError {
        let e = self.exhausted.get().unwrap_or(ResourceError::Nesting(pass));
        self.exhausted.set(Some(e));
        self.work_limit.set(0);
        e
    }

    #[cold]
    fn run_out(&self, work: u64) -> ResourceError {
        let e = self.exhausted.get().unwrap_or(if work > self.limit.get() {
            ResourceError::Work
        } else {
            ResourceError::Depth
        });
        self.exhausted.set(Some(e));
        self.work_limit.set(0);
        e
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn steps(b: &Budget, n: u32) -> Result<()> {
        (0..n).try_for_each(|_| b.step())
    }

    #[test]
    fn a_limited_part_that_goes_over_ends_without_ending_the_operation() {
        let b = Budget::default();
        let _op = b.operation(Limits::default());
        let mut remaining = 5;
        assert_eq!(b.limited(&mut remaining, || steps(&b, 10)), Ok(None));
        assert_eq!(remaining, 0);
        // The operation itself is fine, and has its own limit again.
        assert_eq!(b.exhausted(), None);
        assert_eq!(steps(&b, 1000), Ok(()));
    }

    #[test]
    fn a_limited_part_that_stays_under_is_charged_what_it_used() {
        let b = Budget::default();
        let _op = b.operation(Limits::default());
        let mut remaining = 100;
        assert_eq!(b.limited(&mut remaining, || steps(&b, 10)), Ok(Some(())));
        assert_eq!(remaining, 90);
        // A second part draws on what is left.
        assert_eq!(b.limited(&mut remaining, || steps(&b, 95)), Ok(None));
        assert_eq!(remaining, 0);
    }

    #[test]
    fn a_watched_flag_stops_the_operation_within_a_poll_and_every_later_one() {
        let b = Budget::default();
        let flag = Arc::new(AtomicBool::new(false));
        b.set_cancel_flag(flag.clone());
        b.watch_cancel(true);
        {
            let _op = b.operation(Limits::default());
            assert_eq!(steps(&b, 3 * POLL as u32), Ok(()));
            flag.store(true, Ordering::Relaxed);
            let taken = (1..=POLL + 1).find(|_| b.step().is_err());
            assert!(taken.is_some(), "not stopped within a poll");
            assert_eq!(b.exhausted(), Some(ResourceError::Cancelled));
        }
        assert!(b.cancelled());
        // Sticky, even once the flag is cleared: the check is no result.
        flag.store(false, Ordering::Relaxed);
        {
            let _op = b.operation(Limits::default());
            assert_eq!(b.step(), Err(ResourceError::Cancelled));
        }
        b.reset();
        let _op = b.operation(Limits::default());
        assert_eq!(steps(&b, 3 * POLL as u32), Ok(()));
    }

    #[test]
    fn a_flag_that_isnt_watched_changes_nothing() {
        let b = Budget::default();
        let flag = Arc::new(AtomicBool::new(true));
        b.set_cancel_flag(flag);
        let _op = b.operation(Limits::default());
        assert_eq!(steps(&b, 3 * POLL as u32), Ok(()));
        assert!(!b.cancelled());
    }

    #[test]
    fn a_limited_part_still_runs_out_with_the_flag_watched() {
        let b = Budget::default();
        b.set_cancel_flag(Arc::new(AtomicBool::new(false)));
        b.watch_cancel(true);
        let _op = b.operation(Limits::default());
        let mut remaining = 3 * POLL;
        assert_eq!(
            b.limited(&mut remaining, || steps(&b, 4 * POLL as u32)),
            Ok(None)
        );
        assert_eq!(b.exhausted(), None);
        assert_eq!(steps(&b, 1000), Ok(()));
    }

    #[test]
    fn running_out_of_the_operations_own_steps_is_not_hidden() {
        let b = Budget::default();
        let _op = b.operation(Limits {
            work: 50,
            ..Limits::default()
        });
        let mut remaining = 1_000;
        // The caller's allowance is more than the operation has left.
        assert_eq!(
            b.limited(&mut remaining, || steps(&b, 100)),
            Err(ResourceError::Work)
        );
        assert_eq!(b.exhausted(), Some(ResourceError::Work));
    }
}
