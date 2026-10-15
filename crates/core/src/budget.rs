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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceError {
    /// Too many evaluation steps.
    Work,
    /// Recursion too deep for the stack this operation may use.
    Depth,
    /// A value too large to turn back into a term or print.
    Size,
}

impl fmt::Display for ResourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ResourceError::Work => "it took more evaluation steps than allowed",
            ResourceError::Depth => "it recursed more deeply than allowed",
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
    /// `u64::MAX` outside an operation, and 0 once it has run out, so that
    /// [`Budget::step`]'s fast path is one comparison.
    work_limit: Cell<u64>,
    /// The lowest stack address the operation may reach: 0 outside one.
    stack_floor: Cell<usize>,
    limits: Cell<Option<Limits>>,
    exhausted: Cell<Option<ResourceError>>,
}

impl Default for Budget {
    fn default() -> Budget {
        Budget {
            work: Cell::new(0),
            work_limit: Cell::new(u64::MAX),
            stack_floor: Cell::new(0),
            limits: Cell::new(None),
            exhausted: Cell::new(None),
        }
    }
}

/// The address of a local variable: where the stack currently is. Stacks grow
/// downwards on every target we build for, including WebAssembly's stack in
/// linear memory.
#[inline(always)]
fn stack_position() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
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
            limits: self.limits.replace(Some(limits)),
            exhausted: self.exhausted.replace(None),
        }
    }

    pub fn restore(&self, saved: Saved) {
        self.work.set(saved.work);
        self.work_limit.set(saved.work_limit);
        self.stack_floor.set(saved.stack_floor);
        self.limits.set(saved.limits);
        self.exhausted.set(saved.exhausted);
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
