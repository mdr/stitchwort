//! Resource limits for one top-level operation: checking a declaration,
//! running a test, or evaluating an expression
//! (docs/proposals/stack-safe-evaluation.md).
//!
//! Running out isn't a type error or a failed test: there's no answer. So it's
//! a separate error, [`ResourceError`], which evaluation, conversion and
//! quotation return and their callers propagate. Once an operation has run
//! out, every later check fails too, until the next operation starts.

use std::cell::Cell;
use std::fmt;

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

/// What one operation has used so far. Lives in [`crate::Globals`]; an
/// operation starts with [`Budget::operation`].
#[derive(Debug)]
pub struct Budget {
    work: Cell<u64>,
    /// Steps taken by operations that have ended, for [`Budget::total_work`].
    finished_work: Cell<u64>,
    /// Calls to [`Budget::nesting`], ever: see [`Budget::total_visits`].
    visits: Cell<u64>,
    /// `u64::MAX` outside an operation, and 0 once it has run out, so that
    /// [`Budget::step`]'s fast path is one comparison.
    work_limit: Cell<u64>,
    /// The lowest stack address the operation may reach: 0 outside one.
    stack_floor: Cell<usize>,
    /// `usize::MAX` outside an operation.
    frame_limit: Cell<usize>,
    limits: Cell<Option<Limits>>,
    exhausted: Cell<Option<ResourceError>>,
}

impl Default for Budget {
    fn default() -> Budget {
        Budget {
            work: Cell::new(0),
            finished_work: Cell::new(0),
            visits: Cell::new(0),
            work_limit: Cell::new(u64::MAX),
            stack_floor: Cell::new(0),
            frame_limit: Cell::new(usize::MAX),
            limits: Cell::new(None),
            exhausted: Cell::new(None),
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
    work_limit: u64,
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
        Saved {
            work: self.work.replace(0),
            work_limit: self.work_limit.replace(limits.work),
            stack_floor: self
                .stack_floor
                .replace(stack_position().saturating_sub(limits.stack)),
            frame_limit: self.frame_limit.replace(limits.frames),
            limits: self.limits.replace(Some(limits)),
            exhausted: self.exhausted.replace(None),
        }
    }

    pub fn restore(&self, saved: Saved) {
        self.finished_work
            .set(self.finished_work.get() + self.work.get());
        self.work.set(saved.work);
        self.work_limit.set(saved.work_limit);
        self.stack_floor.set(saved.stack_floor);
        self.frame_limit.set(saved.frame_limit);
        self.limits.set(saved.limits);
        self.exhausted.set(saved.exhausted);
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
        let outer = self.work_limit.get();
        if outer == 0 {
            return f().map(Some);
        }
        let cap = before.saturating_add(*remaining).min(outer);
        self.work_limit.set(cap);
        let result = f();
        let used = self.work.get().saturating_sub(before);
        *remaining = remaining.saturating_sub(used);
        if cap < outer && self.exhausted.get() == Some(ResourceError::Work) && self.work.get() > cap
        {
            self.exhausted.set(None);
            self.work_limit.set(outer);
            *remaining = 0;
            return Ok(None);
        }
        if self.exhausted.get().is_none() {
            self.work_limit.set(outer);
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
            return Err(self.run_out(work));
        }
        Ok(())
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
        let e = self
            .exhausted
            .get()
            .unwrap_or(if work > self.work_limit.get() {
                ResourceError::Work
            } else {
                ResourceError::Depth
            });
        self.exhausted.set(Some(e));
        self.work_limit.set(0);
        e
    }
}
