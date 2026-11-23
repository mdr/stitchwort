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
//!
//! A host can also ask to be told when an operation runs long
//! ([`Budget::set_progress`]): while it is installed, the same polling on
//! the slow path calls it once the steps taken pass [`PROGRESS_FIRST`], and
//! again each time they double. That's how `stitchwort check` says what a
//! slow declaration is computing before it finishes or runs out (SW-2009).
//! It counts steps, not time, so it says the same thing on every run, and it
//! changes neither the steps taken nor the result.

use std::cell::{Cell, RefCell};
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
/// The clock deadlines are read from: the standard one, except in the
/// browser, which has none `std` can use.
#[cfg(not(target_family = "wasm"))]
pub use std::time::Instant;
#[cfg(target_family = "wasm")]
pub use web_time::Instant;

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
    /// A value too large to turn back into a term or print: the most nodes
    /// a read-back may write ([`Limits::size`]).
    Size(u64),
    /// The wall-clock deadline the host set ([`Budget::set_deadline`]) passed
    /// while the operation was running. Like running out of stack, an
    /// attempt inside the operation passes it on rather than taking it as
    /// "no": that answer would depend on how fast the machine is.
    Deadline,
    /// The host asked for the check to stop ([`Budget::set_cancel_flag`]).
    /// Not a result: the session layer discards the check and rewinds, so
    /// this never reaches a user or a cache.
    Cancelled,
}

/// The start of [`ResourceError::Size`]'s message, which callers that
/// treat that error specially look for ([`ResourceError::is_size_message`]).
const TOO_LARGE_TO_WRITE_OUT: &str = "a value was too large to write out";

/// `n` with a comma between each group of three digits: `10,000,000,000`.
pub fn with_commas(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

impl ResourceError {
    /// Whether a diagnostic's message is that of [`ResourceError::Size`].
    pub fn is_size_message(message: &str) -> bool {
        message.contains(TOO_LARGE_TO_WRITE_OUT)
    }

    /// What ran out, in a word or two, for the header
    /// `STITCHWORT_TRACE_RESOURCE` prints (SW-4332).
    fn kind(&self) -> String {
        match self {
            ResourceError::Work => "steps".to_owned(),
            ResourceError::Depth => "depth".to_owned(),
            ResourceError::Nesting(pass) => format!("nesting ({pass})"),
            ResourceError::Size(_) => "size".to_owned(),
            ResourceError::Deadline => "deadline".to_owned(),
            ResourceError::Cancelled => "cancelled".to_owned(),
        }
    }
}

/// Whether `STITCHWORT_TRACE_RESOURCE=1`, read once so the check costs
/// nothing when the variable is unset.
fn trace_resource() -> bool {
    static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *TRACE.get_or_init(|| std::env::var("STITCHWORT_TRACE_RESOURCE").is_ok_and(|v| v == "1"))
}

/// The node count `STITCHWORT_BIG_READBACK` reports read-backs over, if it is
/// set: read once, so that an unset variable costs one relaxed load.
fn big_readback() -> Option<u64> {
    static BIG: std::sync::OnceLock<Option<u64>> = std::sync::OnceLock::new();
    *BIG.get_or_init(|| {
        std::env::var("STITCHWORT_BIG_READBACK")
            .ok()
            .and_then(|v| v.trim().parse::<u64>().ok())
    })
}

/// Whether [`Budget::note_readback`] reports, so the elaborator computes the
/// current declaration's name only when something will use it.
pub fn report_big_readbacks() -> bool {
    big_readback().is_some() || crate::proof_counts::on()
}

thread_local! {
    /// The declaration being elaborated, for `STITCHWORT_BIG_READBACK`'s
    /// report: the elaborator knows it, the budget doesn't. Unset outside a
    /// declaration (an expression typed in, say), and then the report leaves
    /// the declaration out.
    static CURRENT_DECLARATION: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Sets the declaration `STITCHWORT_BIG_READBACK` reports inside, returning
/// the previous one for a nested declaration (a library file loaded inside
/// one) to put back.
pub fn set_current_declaration(name: Option<String>) -> Option<String> {
    CURRENT_DECLARATION.with(|d| d.replace(name))
}

/// `f` of the declaration being checked on this thread, if any.
pub fn with_current_declaration<T>(f: impl FnOnce(Option<&str>) -> T) -> T {
    CURRENT_DECLARATION.with(|d| f(d.borrow().as_deref()))
}

thread_local! {
    /// The spans of the expressions being elaborated, outermost first, for
    /// `STITCHWORT_BIG_READBACK`'s report of which source line asked. Only
    /// kept when the variable is set.
    static SPAN_STACK: RefCell<Vec<stitchwort_syntax::Span>> = const { RefCell::new(Vec::new()) };
}

/// The elaborator starts on the expression at `span`. A no-op, but for one
/// cached read, unless `STITCHWORT_BIG_READBACK` is set. Pair with
/// [`pop_span`].
#[inline]
pub fn push_span(span: stitchwort_syntax::Span) {
    if big_readback().is_some() {
        SPAN_STACK.with(|s| s.borrow_mut().push(span));
    }
}

/// The elaborator is done with the expression last given to [`push_span`].
#[inline]
pub fn pop_span() {
    if big_readback().is_some() {
        SPAN_STACK.with(|s| {
            s.borrow_mut().pop();
        });
    }
}

/// The innermost spans being elaborated (up to `n`, innermost first,
/// skipping repeats of the same span), described as `file:line:col  text`.
fn current_spans(n: usize) -> Vec<String> {
    SPAN_STACK.with(|s| {
        let stack = s.borrow();
        let mut seen = Vec::new();
        for span in stack.iter().rev() {
            if seen.len() == n {
                break;
            }
            if !seen.contains(span) {
                seen.push(*span);
            }
        }
        seen.into_iter()
            .map(|span| {
                stitchwort_syntax::describe_span(span).unwrap_or_else(|| {
                    format!(
                        "file {} bytes {}..{}",
                        span.file.index(),
                        span.start,
                        span.end
                    )
                })
            })
            .collect()
    })
}

/// The elaborator phases `STITCHWORT_STEP_PHASES=1` splits a declaration's
/// steps into (`check --timings`); a step is charged to the innermost phase
/// running when it is taken.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    /// Everything not in one of the others.
    Other = 0,
    /// A walk being elaborated: its search for steps.
    Walk = 1,
    /// Unification and the comparisons it runs.
    Unify = 2,
    /// An application being checked.
    Apply = 3,
    /// A value read back into a term.
    Readback = 4,
}

/// The number of [`Phase`]s.
pub const PHASES: usize = 5;

/// Whether `STITCHWORT_STEP_PHASES=1`, read once so that an unset variable
/// costs one relaxed load per phase entry.
#[inline]
pub fn step_phases() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("STITCHWORT_STEP_PHASES").is_ok_and(|v| v == "1"))
}

/// The steps charged so far, the current phase, and the budget's
/// [`Budget::total_work`] when steps were last charged: the next charge is
/// the difference. Steps are charged when a phase starts or ends, not one
/// at a time, so the evaluator's fast path is untouched.
struct PhaseState {
    current: Cell<usize>,
    mark: Cell<u64>,
    charged: [Cell<u64>; PHASES],
}

thread_local! {
    static PHASE_STATE: PhaseState = const {
        PhaseState {
            current: Cell::new(0),
            mark: Cell::new(0),
            charged: [const { Cell::new(0) }; PHASES],
        }
    };
}

/// Charges the steps since the last charge to the current phase.
#[cold]
fn flush_phase(budget: &Budget) {
    let total = budget.total_work();
    PHASE_STATE.with(|s| {
        let c = &s.charged[s.current.get()];
        c.set(c.get() + total.saturating_sub(s.mark.get()));
        s.mark.set(total);
    });
}

/// Makes the current phase the one it was before. See [`Budget::phase`].
#[must_use]
pub struct PhaseGuard<'b> {
    budget: &'b Budget,
    previous: Option<usize>,
}

impl Drop for PhaseGuard<'_> {
    fn drop(&mut self) {
        if let Some(previous) = self.previous {
            flush_phase(self.budget);
            PHASE_STATE.with(|s| s.current.set(previous));
        }
    }
}

/// Names the resource that ran out and prints a backtrace when
/// `STITCHWORT_TRACE_RESOURCE=1` (SW-4332). Every `E-RESOURCE` passes
/// through [`Diagnostic::from`], so this shows the elaborator site that
/// gave up.
#[cold]
#[inline(never)]
fn trace_resource_error(e: &ResourceError) {
    if trace_resource() {
        eprintln!(
            "STITCHWORT_TRACE_RESOURCE: resource error ({}): {e}\n{}",
            e.kind(),
            std::backtrace::Backtrace::force_capture()
        );
    }
}

impl fmt::Display for ResourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ResourceError::Work => "it took more evaluation steps than allowed",
            ResourceError::Depth => "it recursed more deeply than allowed",
            ResourceError::Nesting(pass) => {
                return write!(f, "the program is nested too deeply for the {pass}");
            }
            ResourceError::Size(limit) => {
                return write!(
                    f,
                    "{TOO_LARGE_TO_WRITE_OUT} (over {} parts)",
                    with_commas(*limit)
                );
            }
            ResourceError::Deadline => "it took longer than the time allowed",
            ResourceError::Cancelled => "the check was cancelled",
        })
    }
}

/// The note every `E-RESOURCE` error starts with.
pub const NO_ANSWER: &str =
    "this isn't a type error or a failed test: there's no answer within the limits";

impl From<ResourceError> for Diagnostic {
    // Out of line: every `?` on a resource error in the kernel's recursive
    // passes would otherwise carry the message's formatting in its frame.
    #[cold]
    #[inline(never)]
    fn from(e: ResourceError) -> Diagnostic {
        trace_resource_error(&e);
        Diagnostic::error("E-RESOURCE", format!("ran out of resources: {e}")).with_note(NO_ANSWER)
    }
}

pub type Result<T> = std::result::Result<T, ResourceError>;

/// Limits for one operation.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Evaluation steps.
    pub work: u64,
    /// Bytes of Rust stack the operation may use, measured from where it
    /// started, and never below the floor of the operation it is started
    /// inside. Must be comfortably less than the thread's stack.
    pub stack: usize,
    /// Nodes in a quoted term. Each node a read-back writes is a heap
    /// allocation of 70 to 120 bytes, held until the error unwinds, so the
    /// limit bounds the memory a runaway read-back takes (2 million: about
    /// 0.3 GB). The largest read-back in the standard library, `aoc/` and
    /// `games/rogue` is under 400,000 nodes (SW-2681).
    pub size: u64,
    /// Frames of pending work in the evaluator: how deeply a program may
    /// recurse. A frame keeps its environment alive, so in practice each
    /// costs a few hundred bytes: `length (replicate 1000000 1)`, a million
    /// frames deep, peaks at about 750 MB.
    pub frames: usize,
    /// The most frames native code may have pending (the ceiling of its
    /// depth budget, `E-RESOURCE`): the machine keeps `frames`, since each
    /// machine frame costs heap and each native frame costs stack, which
    /// is reserved lazily and so is cheap to size generously. The limit a
    /// native run enforces is this, or less when the program's widest frame
    /// would need more stack than the cap
    /// (`stitchwort_rt::native_abi::native_frame_limit`). The one place the
    /// value is set; [`NATIVE_FRAMES`] is its default.
    pub native_frames: usize,
}

/// The default [`Limits::native_frames`]: 16 million, which runs
/// `bench/compare/const-fold` at depth 23 (SW-2471, D3450).
pub const NATIVE_FRAMES: usize = 16_000_000;

impl Limits {
    /// For a thread with `stack_size` bytes of stack, leaving a quarter (and
    /// at least 256 KiB) for whatever runs outside the guarded functions.
    pub fn for_stack(stack_size: usize) -> Limits {
        let reserve = (stack_size / 4).max(256 * 1024);
        Limits {
            work: 10_000_000_000,
            stack: stack_size.saturating_sub(reserve),
            size: 2_000_000,
            frames: 2_000_000,
            native_frames: NATIVE_FRAMES,
        }
    }

    /// These limits, with `work`, `size`, `frames` and `native_frames` raised to
    /// [`Limits::default`]'s where they are lower; `stack` as it is, since
    /// it depends on the thread. For checking what the program's limits
    /// shouldn't bound, the library.
    pub fn at_least_default_resources(self) -> Limits {
        let floor = Limits::default();
        Limits {
            work: self.work.max(floor.work),
            stack: self.stack,
            size: self.size.max(floor.size),
            frames: self.frames.max(floor.frames),
            native_frames: self.native_frames.max(floor.native_frames),
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
            native_frames: usize::MAX,
        }
    }
}

/// With the `stack-check` feature (on in the tests), for an outermost
/// operation: panics if `stack` bytes from here run past the end of this
/// thread's stack, where the guard couldn't stop the operation before the
/// thread overflowed (a hard abort). That's a session whose limits assume a
/// bigger thread than it runs on: run it on one of the size its limits were
/// made for (`stitchwort_driver::driver::with_session`).
#[cfg(feature = "stack-check")]
fn check_thread_fits(stack: usize) {
    let Some(low) = stitchwort_syntax::stack::thread_stack_low() else {
        return;
    };
    let here = stack_position();
    let room = here.saturating_sub(low);
    assert!(
        stack <= room,
        "an operation may use {stack} bytes of stack, but its thread has {room} left: \
         its session's limits assume a bigger thread than it runs on \
         (run it with stitchwort_driver::driver::with_session, docs/testing.md)"
    );
}

impl Default for Limits {
    /// Safe on a 2 MiB thread: Rust's default for spawned threads and tests.
    fn default() -> Limits {
        Limits::for_stack(2 * 1024 * 1024)
    }
}

/// The host's second way of asking for cancellation
/// ([`Budget::set_cancel_hook`]).
static CANCEL_HOOK: std::sync::OnceLock<fn() -> bool> = std::sync::OnceLock::new();

/// How many evaluation steps pass between two looks at the cancellation
/// flag: a fraction of a millisecond.
pub const POLL: u64 = 1 << 14;

/// The steps after which [`Budget::set_progress`]'s sink is first told of
/// an operation: 250 million, about 7 seconds of evaluation on a 2026
/// laptop (34 million steps a second, measured on a `countdown` loop). The
/// operation's whole budget, [`Limits::work`], is 40 times that.
pub const PROGRESS_FIRST: u64 = 250_000_000;

/// What [`Budget::set_progress`] installs: called with the number of steps
/// just passed since it was installed (its first, then twice that, and so
/// on) and the definition the evaluator last entered (its index), if
/// any.
pub type ProgressSink = Rc<dyn Fn(u64, Option<usize>)>;

/// An installed [`ProgressSink`] and when it is next due.
pub struct Progress {
    sink: ProgressSink,
    /// [`Budget::total_work`] when it was installed.
    start: u64,
    /// Steps since `start` at which the sink is next called.
    next: u64,
}

impl fmt::Debug for Progress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Progress")
            .field("start", &self.start)
            .field("next", &self.next)
            .finish_non_exhaustive()
    }
}

/// The largest read-back and deepest frames seen: [`Budget::take_peaks`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Peaks {
    /// Nodes in the largest single read-back, counted as the size limit is.
    pub readback: u64,
    /// The most frames of pending work the evaluator had at once.
    pub frames: usize,
}

/// What one operation has used so far. Lives in [`crate::machine::Machine`]; an
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
    /// Whether the operation ran out because it reached its stack floor
    /// (rather than its steps, size or frames): what [`Budget::attempt`]
    /// passes on to the operation it is part of.
    out_of_stack: Cell<bool>,
    /// When the frame limit was hit: the definitions with the most frames
    /// pending, as (definition index, frames) pairs, most first.
    deepest: RefCell<Vec<(usize, usize)>>,
    /// When a value was too large to read back ([`ResourceError::Size`]): the
    /// definition its outermost call was of, if it was one.
    too_large: Cell<Option<usize>>,
    /// The most nodes any one read-back has counted, and the most frames
    /// pending at once, since [`Budget::take_peaks`]. Kept across
    /// operations: the timings report (`STITCHWORT_TIMINGS`) reads them per
    /// declaration. Each is one comparison where the limit is already
    /// checked.
    peak_readback: Cell<u64>,
    peak_frames: Cell<usize>,
    /// The definition whose case tree the reference evaluator last entered.
    entered: Cell<usize>,
    /// The definition outside std last entered: what a message names in
    /// preference to `entered`, since a std function (`List.length`
    /// alternating with `replicate`) says nothing of what the user wrote.
    entered_user: Cell<usize>,
    /// The definition last entered when the operation ran out of steps or
    /// frames, for whoever reports it ([`Budget::take_ran_out_in`]).
    ran_out_in: Cell<Option<usize>>,
    /// The host's cancellation flag, if it installed one.
    cancel: RefCell<Option<Arc<AtomicBool>>>,
    /// Whether the flag is being watched: only a check the host can cancel
    /// looks at it, so that printing or running afterwards never stops.
    watching: Cell<bool>,
    /// Whether the flag has been seen set: from then on every operation
    /// fails with [`ResourceError::Cancelled`], until [`Budget::reset`].
    cancelled: Cell<bool>,
    /// Whether an operation on a big number costs a step per machine word
    /// it works through ([`Budget::number_words`]).
    number_words: Cell<bool>,
    /// A wall-clock deadline for the operations running, if the host set one
    /// ([`Budget::set_deadline`]), read every [`POLL`] steps like the
    /// cancellation flag.
    deadline: Cell<Option<Instant>>,
    /// Whether an operation was stopped by the deadline since
    /// [`Budget::take_timed_out`] last cleared it.
    timed_out: Cell<bool>,
    /// Who to tell when an operation runs long, if anyone
    /// ([`Budget::set_progress`]).
    progress: RefCell<Option<Progress>>,
    /// Whether `progress` is set, read by [`Budget::arm`].
    progress_on: Cell<bool>,
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
            out_of_stack: Cell::new(false),
            deepest: RefCell::new(Vec::new()),
            too_large: Cell::new(None),
            peak_readback: Cell::new(0),
            peak_frames: Cell::new(0),
            entered: Cell::new(usize::MAX),
            entered_user: Cell::new(usize::MAX),
            ran_out_in: Cell::new(None),
            cancel: RefCell::new(None),
            watching: Cell::new(false),
            cancelled: Cell::new(false),
            number_words: Cell::new(false),
            deadline: Cell::new(None),
            timed_out: Cell::new(false),
            progress: RefCell::new(None),
            progress_on: Cell::new(false),
        }
    }
}

/// While this is alive, an operation is running. Dropping it restores
/// whatever was running before (usually nothing).
#[must_use]
pub struct Operation<'b> {
    budget: &'b Budget,
    previous: Option<Saved>,
    /// Started by [`Budget::attempt`]: running out of stack is passed on.
    attempt: bool,
}

impl Drop for Operation<'_> {
    fn drop(&mut self) {
        let Some(saved) = self.previous.take() else {
            return;
        };
        let out_of_stack = self.attempt && self.budget.out_of_stack.get();
        let error = self.budget.exhausted.get();
        self.budget.restore(saved);
        if out_of_stack && let Some(error) = error {
            // The operation this attempt is part of is out of stack too: it
            // has no answer, rather than the one the attempt's "no" gives.
            self.budget.out_of_stack.set(true);
            if self.budget.exhausted.get().is_none() {
                self.budget.exhausted.set(Some(error));
            }
            self.budget.arm();
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
    out_of_stack: bool,
}

impl Budget {
    /// Starts an operation with fresh counters, measuring stack use from here.
    /// It ends when the guard is dropped.
    pub fn operation(&self, limits: Limits) -> Operation<'_> {
        Operation {
            budget: self,
            previous: Some(self.start(limits)),
            attempt: false,
        }
    }

    /// Starts an attempt inside the operation running: something tried
    /// whose failure to finish within `limits` the caller takes as "no"
    /// (a comparison, a cheap normal form). It has fresh counters for
    /// steps, size and frames, which are the same in every build, but no
    /// stack budget of its own: it may go as deep as the operation it is
    /// part of may. A budget in bytes of stack isn't the same in every
    /// build (a debug build's frames are several times larger, SW-962), so
    /// an attempt cut short by one would give a different "no", and a
    /// different elaborated term, in a debug build. If the attempt reaches
    /// the operation's stack floor, the operation has run out too, with
    /// the attempt's error: no answer, rather than a different one. Outside
    /// an operation, it may use `limits.stack` bytes from here.
    pub fn attempt(&self, limits: Limits) -> Operation<'_> {
        let floor = self.stack_floor.get();
        let saved = self.start(limits);
        if floor != 0 {
            self.stack_floor.set(floor);
        }
        Operation {
            budget: self,
            previous: Some(saved),
            attempt: true,
        }
    }

    /// Runs `f` as an [`Budget::attempt`] within `limits`, leaving no trace
    /// in what the running operation reports: where it ran out, and the
    /// definition last entered, are as they were. For a computation a
    /// message makes on the side, which may run out without saying so.
    pub fn aside<T>(&self, limits: Limits, f: impl FnOnce() -> T) -> T {
        let entered = self.entered.get();
        let entered_user = self.entered_user.get();
        let ran_out_in = self.ran_out_in.get();
        let result = {
            let _attempt = self.attempt(limits);
            f()
        };
        self.entered.set(entered);
        self.entered_user.set(entered_user);
        self.ran_out_in.set(ran_out_in);
        result
    }

    /// Charges the steps taken inside the returned guard's lifetime to
    /// `phase`, except those a phase nested in it takes. Does nothing unless
    /// `STITCHWORT_STEP_PHASES=1`.
    #[inline]
    pub fn phase(&self, phase: Phase) -> PhaseGuard<'_> {
        if !step_phases() {
            return PhaseGuard {
                budget: self,
                previous: None,
            };
        }
        self.enter_phase(phase)
    }

    #[cold]
    #[inline(never)]
    fn enter_phase(&self, phase: Phase) -> PhaseGuard<'_> {
        flush_phase(self);
        let previous = PHASE_STATE.with(|s| s.current.replace(phase as usize));
        PhaseGuard {
            budget: self,
            previous: Some(previous),
        }
    }

    /// The steps charged to each [`Phase`] on this thread so far, indexed by
    /// phase; all zero unless `STITCHWORT_STEP_PHASES=1`.
    pub fn phase_steps(&self) -> [u64; PHASES] {
        if !step_phases() {
            return [0; PHASES];
        }
        flush_phase(self);
        PHASE_STATE.with(|s| std::array::from_fn(|i| s.charged[i].get()))
    }

    /// Like [`Budget::attempt`], for callers that can't hold a borrow of the
    /// budget: the attempt ends with [`Budget::restore`].
    pub fn start_attempt(&self, limits: Limits) -> Saved {
        let floor = self.stack_floor.get();
        let saved = self.start(limits);
        if floor != 0 {
            self.stack_floor.set(floor);
        }
        saved
    }

    /// Like [`Budget::operation`], for callers that can't hold a borrow of
    /// the budget: the operation ends with [`Budget::restore`].
    pub fn start(&self, limits: Limits) -> Saved {
        #[cfg(feature = "stack-check")]
        if self.stack_floor.get() == 0 {
            check_thread_fits(limits.stack);
        }
        // Started inside an operation, this one may not reach below the
        // floor that operation was given, which was measured against the
        // thread: measured only from here, `limits.stack` bytes could run
        // past the thread's real stack.
        let outer = self.stack_floor.get();
        let floor = stack_position().saturating_sub(limits.stack).max(outer);
        // The counted total drops while an operation runs inside another
        // (the outer one's steps are set aside), so phase charging brackets
        // that.
        if step_phases() {
            flush_phase(self);
        }
        let saved = Saved {
            work: self.work.replace(0),
            limit: self.limit.replace(limits.work),
            stack_floor: self.stack_floor.replace(floor),
            frame_limit: self.frame_limit.replace(limits.frames),
            limits: self.limits.replace(Some(limits)),
            exhausted: self.exhausted.replace(None),
            out_of_stack: self.out_of_stack.replace(false),
        };
        self.entered.set(usize::MAX);
        self.entered_user.set(usize::MAX);
        if self.cancel_requested() {
            self.exhausted.set(Some(ResourceError::Cancelled));
        }
        if step_phases() {
            PHASE_STATE.with(|s| s.mark.set(self.total_work()));
        }
        self.arm();
        saved
    }

    /// Runs `f`, a check that only test builds make, as if it took no
    /// steps and visited nothing: the counts benchmarks read, the
    /// operation's remaining steps and whether it has run out are as they
    /// were. Running out inside `f` is `f`'s to handle.
    #[cfg(feature = "reference")]
    pub fn uncounted<T>(&self, f: impl FnOnce() -> T) -> T {
        let finished = self.finished_work.get();
        let work = self.work.get();
        let visits = self.visits.get();
        let exhausted = self.exhausted.get();
        let out_of_stack = self.out_of_stack.get();
        let result = f();
        self.finished_work.set(finished);
        self.work.set(work);
        self.visits.set(visits);
        self.out_of_stack.set(out_of_stack);
        self.exhausted.set(if self.cancelled.get() {
            Some(ResourceError::Cancelled)
        } else {
            exhausted
        });
        self.arm();
        result
    }

    pub fn restore(&self, saved: Saved) {
        if step_phases() {
            flush_phase(self);
        }
        self.finished_work
            .set(self.finished_work.get() + self.work.get());
        self.work.set(saved.work);
        self.limit.set(saved.limit);
        self.stack_floor.set(saved.stack_floor);
        self.frame_limit.set(saved.frame_limit);
        self.limits.set(saved.limits);
        self.out_of_stack.set(saved.out_of_stack);
        let exhausted = if self.cancelled.get() {
            Some(ResourceError::Cancelled)
        } else {
            saved.exhausted
        };
        self.exhausted.set(exhausted);
        if step_phases() {
            PHASE_STATE.with(|s| s.mark.set(self.total_work()));
        }
        self.arm();
    }

    /// Sets where [`Budget::step`] next leaves its fast path, from the
    /// limit, the cancellation flag and whether the operation has run out.
    fn arm(&self) {
        let at = if self.exhausted.get().is_some() {
            0
        } else if self.watching.get() || self.deadline.get().is_some() || self.progress_on.get() {
            self.limit.get().min(self.work.get().saturating_add(POLL))
        } else {
            self.limit.get()
        };
        self.work_limit.set(at);
    }

    /// Installs, for the whole program, a second way of asking for
    /// cancellation, read with the flag: for a host where no other thread
    /// can set the flag. In the browser it reads a counter in shared memory
    /// that the page bumps for each edit (docs/proposals/playground-editor.md
    /// §5.2.1). Only a budget with a flag installed consults it; the first
    /// hook installed stays.
    pub fn set_cancel_hook(hook: fn() -> bool) {
        let _ = CANCEL_HOOK.set(hook);
    }

    /// Installs the flag that cancels operations while it's watched (see
    /// the module's comment).
    pub fn set_cancel_flag(&self, flag: Arc<AtomicBool>) {
        *self.cancel.borrow_mut() = Some(flag);
        self.arm();
    }

    /// Sets (or clears) a wall-clock deadline: while it is set, an operation
    /// still running when it passes stops, within [`POLL`] steps, with
    /// [`ResourceError::Deadline`] (SW-1017). Unlike cancellation it isn't
    /// sticky: the next operation starts afresh, and its caller decides
    /// whether to try again. [`Budget::take_timed_out`] says whether it
    /// stopped one.
    pub fn set_deadline(&self, deadline: Option<Instant>) {
        self.deadline.set(deadline);
        self.arm();
    }

    /// Installs (or, with `None`, removes) a sink told when the work goes on
    /// long: after `first` steps from now ([`PROGRESS_FIRST`] for a check),
    /// then each time the steps double. Returns the one it replaces, for its
    /// owner to put back: a check started inside another (a library file
    /// loaded part way) installs its own. While one is installed,
    /// [`Budget::step`] leaves its fast path every [`POLL`] steps, as for a
    /// watched cancellation flag. Only the notes change: the steps taken,
    /// and where the operation runs out, are the same.
    pub fn set_progress(&self, sink: Option<ProgressSink>, first: u64) -> Option<Progress> {
        let progress = sink.map(|sink| Progress {
            sink,
            start: self.total_work(),
            next: first.max(1),
        });
        self.restore_progress(progress)
    }

    /// Puts back a sink [`Budget::set_progress`] returned, still due when it
    /// was, counting from when it was first installed. Returns the one it
    /// replaces.
    pub fn restore_progress(&self, progress: Option<Progress>) -> Option<Progress> {
        self.progress_on.set(progress.is_some());
        let old = self.progress.replace(progress);
        self.arm();
        old
    }

    /// Calls the progress sink if it is due.
    fn progress_due(&self) {
        let due = {
            let mut progress = self.progress.borrow_mut();
            let Some(p) = progress.as_mut() else {
                return;
            };
            let taken = self.total_work().saturating_sub(p.start);
            if taken < p.next {
                return;
            }
            let mut passed = p.next;
            while p.next <= taken {
                passed = p.next;
                p.next = p.next.saturating_mul(2);
            }
            (p.sink.clone(), passed)
        };
        // Not borrowed while it runs: it may look at the budget.
        (due.0)(due.1, self.last_entered());
    }

    /// Whether the deadline stopped an operation since this was last called.
    pub fn take_timed_out(&self) -> bool {
        self.timed_out.replace(false)
    }

    /// Whether the deadline has passed, noting it so if so (and, through
    /// [`Budget::attempt`], ending the operations the one running is part of).
    fn deadline_passed(&self) -> bool {
        if self.deadline.get().is_some_and(|d| Instant::now() >= d) {
            self.timed_out.set(true);
            self.out_of_stack.set(true);
            true
        } else {
            false
        }
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
            && (self
                .cancel
                .borrow()
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Relaxed))
                || CANCEL_HOOK.get().is_some_and(|hook| hook()))
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
        self.out_of_stack.set(false);
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
            self.ran_out_in.set(None);
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

    /// Turns on or off whether a native operation on big numbers (past a
    /// machine word) also costs a step per word it works through
    /// ([`crate::native::number_words`]), so that the steps bound its time
    /// and memory: the counterexample search turns it on while it runs an
    /// input (SW-907), where a number at a word's edge, used as a count of
    /// doublings or an exponent, makes numbers of gigabytes in a few steps.
    /// Otherwise a native operation is one step. Returns what it was.
    pub fn count_number_words(&self, on: bool) -> bool {
        self.number_words.replace(on)
    }

    /// Charges `words` steps for a native operation on big numbers, when
    /// they count ([`Budget::count_number_words`]).
    #[inline]
    pub fn number_words(&self, words: impl FnOnce() -> u64) -> Result<()> {
        if !self.number_words.get() {
            return Ok(());
        }
        let work = self.work.get().saturating_add(words());
        self.work.set(work);
        if work > self.work_limit.get() {
            return self.slow_step(work);
        }
        Ok(())
    }

    /// The error the current operation ran out with, if it did.
    pub fn exhausted(&self) -> Option<ResourceError> {
        self.exhausted.get()
    }

    /// The lowest stack position the running operation may reach (0 outside
    /// one): what a rewind that keeps the operation must leave alone.
    pub fn stack_floor(&self) -> usize {
        self.stack_floor.get()
    }

    /// The running operation's limits ([`Limits::default`] outside one): for
    /// an attempt that may spend as much as the operation could.
    pub fn limits(&self) -> Limits {
        self.limits.get().unwrap_or_default()
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
            if self.deadline_passed() {
                self.exhausted.set(Some(ResourceError::Deadline));
                self.work_limit.set(0);
                return Err(ResourceError::Deadline);
            }
            if self.progress_on.get() {
                self.progress_due();
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
        if stack_position() < self.stack_floor.get() {
            if self.exhausted.get().is_none() {
                self.out_of_stack.set(true);
            }
            return Err(self.too_deep(pass));
        }
        if self.work_limit.get() == 0 {
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

    /// The reference evaluator is entering definition `id`'s case tree;
    /// `std` says it is from the standard library.
    #[inline]
    pub fn enter_definition(&self, id: usize, std: bool) {
        self.entered.set(id);
        if !std {
            self.entered_user.set(id);
        }
    }

    /// The definition last entered that isn't from std, or if the operation
    /// has entered only std's, the last one; `None` if none.
    pub fn last_entered(&self) -> Option<usize> {
        let user = self.entered_user.get();
        Some(if user != usize::MAX {
            user
        } else {
            self.entered.get()
        })
        .filter(|id| *id != usize::MAX)
    }

    /// Notes the definition last entered as where the operation ran out,
    /// unless it had already run out: for whoever reports it
    /// ([`Budget::take_ran_out_in`]). Running out of steps or frames notes it
    /// here; a read-back that finds a value too large
    /// ([`ResourceError::Size`]) notes it itself, before it fails.
    pub fn note_ran_out(&self) {
        if self.exhausted.get().is_none() {
            self.ran_out_in.set(self.last_entered());
        }
    }

    /// The definition being unfolded when an operation last ran out of
    /// steps or frames, if known. Clears it.
    pub fn take_ran_out_in(&self) -> Option<usize> {
        self.ran_out_in.take()
    }

    /// Puts back what [`Budget::take_ran_out_in`] took: for a caller that
    /// tried something else after the operation ran out, and reports the
    /// first error.
    pub fn set_ran_out_in(&self, definition: Option<usize>) {
        self.ran_out_in.set(definition);
    }

    /// Records which definitions the pending frames belong to, for
    /// whoever reports the recursion limit ([`Budget::take_deepest`]).
    pub fn set_deepest(&self, deepest: Vec<(usize, usize)>) {
        *self.deepest.borrow_mut() = deepest;
    }

    /// The definitions with the most frames pending when the frame limit was
    /// hit (definition index, frames), most first; empty if it wasn't or
    /// they're not known. Clears them.
    pub fn take_deepest(&self) -> Vec<(usize, usize)> {
        std::mem::take(&mut self.deepest.borrow_mut())
    }

    /// Records the definition (by index) whose call was too large to read
    /// back, for whoever reports it ([`Budget::take_too_large`]).
    pub fn set_too_large(&self, definition: Option<usize>) {
        self.too_large.set(definition);
    }

    /// The definition whose call was last too large to read back, if the
    /// value was one. Clears it.
    pub fn take_too_large(&self) -> Option<usize> {
        self.too_large.take()
    }

    /// A read-back ([`crate::value::quote`], the unifier's `rename`) counted
    /// `nodes` nodes, whether it finished or ran over a limit. With
    /// `STITCHWORT_BIG_READBACK` set to a count, one over it also prints the
    /// count, the declaration being elaborated if known, the source
    /// position and text of the innermost expressions being elaborated, and a
    /// backtrace to standard error.
    #[inline]
    pub fn note_readback(&self, nodes: u64) {
        if nodes > self.peak_readback.get() {
            self.peak_readback.set(nodes);
        }
        if let Some(over) = big_readback()
            && nodes > over
        {
            let declaration = CURRENT_DECLARATION.with(|d| d.borrow().clone());
            let backtrace = std::backtrace::Backtrace::force_capture();
            let mut at = String::new();
            for (i, line) in current_spans(5).iter().enumerate() {
                at.push_str(if i == 0 { "  at:     " } else { "  inside: " });
                at.push_str(line);
                at.push('\n');
            }
            match declaration {
                Some(name) => eprintln!("big readback: {nodes} nodes in {name}\n{at}{backtrace}"),
                None => eprintln!("big readback: {nodes} nodes\n{at}{backtrace}"),
            }
        }
    }

    /// The largest read-back and the most frames pending since the last call
    /// (or the start), and starts counting again from zero.
    pub fn take_peaks(&self) -> Peaks {
        Peaks {
            readback: self.peak_readback.take(),
            frames: self.peak_frames.take(),
        }
    }

    /// Puts back peaks taken with [`Budget::take_peaks`], keeping any larger
    /// ones seen since.
    pub fn restore_peaks(&self, peaks: Peaks) {
        // Not a read-back itself: only record it, without reporting it.
        if peaks.readback > self.peak_readback.get() {
            self.peak_readback.set(peaks.readback);
        }
        if peaks.frames > self.peak_frames.get() {
            self.peak_frames.set(peaks.frames);
        }
    }

    /// The evaluator is about to have `frames` frames of pending work.
    #[inline]
    pub fn frames(&self, frames: usize) -> Result<()> {
        if frames > self.peak_frames.get() {
            self.peak_frames.set(frames);
        }
        if frames > self.frame_limit.get() {
            self.note_ran_out();
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
        self.note_ran_out();
        let e = self.exhausted.get().unwrap_or_else(|| {
            if work > self.limit.get() {
                ResourceError::Work
            } else {
                self.out_of_stack.set(true);
                ResourceError::Depth
            }
        });
        self.exhausted.set(Some(e));
        self.work_limit.set(0);
        e
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_size_message_names_the_limit() {
        for (limit, shown) in [(2_000_000, "2,000,000"), (100, "100"), (1_000, "1,000")] {
            let message = ResourceError::Size(limit).to_string();
            assert_eq!(
                message,
                format!("a value was too large to write out (over {shown} parts)")
            );
            assert!(ResourceError::is_size_message(&message));
        }
        assert!(!ResourceError::Work.to_string().contains("write out"));
        assert_eq!(Limits::for_stack(1 << 20).size, 2_000_000);
    }

    #[test]
    fn the_resource_kinds_are_named() {
        assert_eq!(ResourceError::Work.kind(), "steps");
        assert_eq!(ResourceError::Depth.kind(), "depth");
        assert_eq!(
            ResourceError::Nesting("elaborator").kind(),
            "nesting (elaborator)"
        );
        assert_eq!(ResourceError::Size(1).kind(), "size");
        assert_eq!(ResourceError::Deadline.kind(), "deadline");
        assert_eq!(ResourceError::Cancelled.kind(), "cancelled");
    }

    #[test]
    fn tracing_is_off_when_the_variable_is_unset() {
        assert!(!trace_resource());
    }

    fn steps(b: &Budget, n: u32) -> Result<()> {
        (0..n).try_for_each(|_| b.step())
    }

    /// Recurses `depth` levels, each a [`Budget::nesting`] check with a
    /// kilobyte of its own stack.
    #[inline(never)]
    fn nest(b: &Budget, depth: usize) -> Result<()> {
        let pad = std::hint::black_box([0u8; 1024]);
        b.nesting("test")?;
        if depth > 0 {
            nest(b, depth - 1)?;
        }
        std::hint::black_box(pad);
        Ok(())
    }

    /// SW-1446: an operation started deep inside another gets what is left
    /// of the outer one's stack, not a full allowance from where it starts.
    #[test]
    fn a_nested_operation_may_not_go_below_the_outer_floor() {
        let b = Budget::default();
        let _op = b.operation(Limits::stack_only(64 * 1024));
        // Without the clamp, 1 MiB from here would be far past the outer
        // 64 KiB; with it, the inner operation stops where the outer would.
        fn inner(b: &Budget, depth: usize) -> Result<()> {
            if depth == 0 {
                let _inner = b.operation(Limits::stack_only(1024 * 1024));
                assert_eq!(nest(b, 4096), Err(ResourceError::Nesting("test")));
                assert_eq!(b.exhausted(), Some(ResourceError::Nesting("test")));
                return Ok(());
            }
            let pad = std::hint::black_box([0u8; 1024]);
            let r = inner(b, depth - 1);
            std::hint::black_box(pad);
            r
        }
        inner(&b, 32).unwrap();
        // The outer operation, whose floor is further away, is unaffected.
        assert_eq!(b.exhausted(), None);
        assert_eq!(nest(&b, 8), Ok(()));
    }

    /// SW-962: an attempt's own stack budget (here none at all) doesn't
    /// stop it; how deep it may go is the operation's, so the same attempt
    /// gives the same answer in a debug build, whose frames are larger.
    #[test]
    fn an_attempt_may_go_as_deep_as_its_operation() {
        let b = Budget::default();
        let _op = b.operation(Limits::for_stack(1024 * 1024));
        {
            let _attempt = b.attempt(Limits {
                stack: 0,
                ..Limits::default()
            });
            assert_eq!(nest(&b, 64), Ok(()));
        }
        // An operation with its own stack budget is stopped by it.
        {
            let _inner = b.operation(Limits {
                stack: 0,
                ..Limits::default()
            });
            assert_eq!(nest(&b, 64), Err(ResourceError::Nesting("test")));
        }
        assert_eq!(b.exhausted(), None);
    }

    /// An attempt that reaches the operation's stack floor ends the
    /// operation too: it has no answer, not the one "no" would give. One
    /// that runs out of its own steps is just "no".
    #[test]
    fn an_attempt_out_of_stack_ends_its_operation() {
        let b = Budget::default();
        let _op = b.operation(Limits::for_stack(1024 * 1024));
        {
            let _attempt = b.attempt(Limits {
                work: 5,
                ..Limits::default()
            });
            assert_eq!(steps(&b, 10), Err(ResourceError::Work));
        }
        assert_eq!(b.exhausted(), None);
        assert_eq!(steps(&b, 10), Ok(()));
        {
            let _attempt = b.attempt(Limits::default());
            assert_eq!(nest(&b, 1024), Err(ResourceError::Nesting("test")));
        }
        assert_eq!(b.exhausted(), Some(ResourceError::Nesting("test")));
        assert!(b.step().is_err());
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

    /// SW-1017: a deadline that passes stops the operation running, from
    /// inside, within a few polls; an attempt it stops ends the operation it
    /// is part of (the answer would depend on the machine's speed), and the
    /// next operation is unaffected.
    #[test]
    fn a_deadline_stops_the_operation_running_and_the_attempts_in_it() {
        let b = Budget::default();
        b.set_deadline(Some(Instant::now()));
        {
            let _op = b.operation(Limits::default());
            let _attempt = b.attempt(Limits::default());
            assert_eq!(steps(&b, 4 * POLL as u32), Err(ResourceError::Deadline));
        }
        assert!(b.take_timed_out());
        assert!(!b.take_timed_out());
        // The attempt was inside an operation: that ran out too.
        {
            let _op = b.operation(Limits::default());
            {
                let _attempt = b.attempt(Limits::default());
                assert_eq!(steps(&b, 4 * POLL as u32), Err(ResourceError::Deadline));
            }
            assert_eq!(b.exhausted(), Some(ResourceError::Deadline));
        }
        assert_eq!(b.exhausted(), None);
        b.set_deadline(None);
        let _op = b.operation(Limits::default());
        assert_eq!(steps(&b, 4 * POLL as u32), Ok(()));
        // A deadline far away costs nothing.
        b.set_deadline(Some(Instant::now() + std::time::Duration::from_secs(3600)));
        assert_eq!(steps(&b, 4 * POLL as u32), Ok(()));
    }

    /// SW-2009: the sink is told when the steps pass its first count and
    /// each double of it, with the definition last entered, and taking the
    /// same steps with it installed runs out at the same point.
    #[test]
    fn a_progress_sink_is_told_at_each_doubling_and_changes_nothing() {
        let b = Budget::default();
        type Told = Rc<RefCell<Vec<(u64, Option<usize>)>>>;
        let told: Told = Rc::default();
        let sink = {
            let told = told.clone();
            Rc::new(move |steps, entered| told.borrow_mut().push((steps, entered)))
        };
        let limits = Limits {
            work: 10 * POLL,
            ..Limits::default()
        };
        let _op = b.operation(limits);
        assert!(b.set_progress(Some(sink), 2 * POLL).is_none());
        b.enter_definition(7, false);
        assert_eq!(steps(&b, 9 * POLL as u32), Ok(()));
        assert_eq!(
            *told.borrow(),
            [
                (2 * POLL, Some(7)),
                (4 * POLL, Some(7)),
                (8 * POLL, Some(7))
            ]
        );
        assert_eq!(steps(&b, POLL as u32), Ok(()));
        assert_eq!(b.step(), Err(ResourceError::Work));
        // Put back, it is due when it was; removed, it is told nothing more.
        let taken = b.set_progress(None, 0);
        assert!(taken.is_some());
        assert!(b.restore_progress(taken).is_none());
        assert!(b.set_progress(None, 0).is_some());
        assert_eq!(told.borrow().len(), 3);
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
