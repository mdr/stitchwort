//! A counting allocator and the budget hook that stops a check over its heap
//! cap (SW-2582), shared by the fuzzers (`fuzz_elab.rs`, `soundness_fuzz.rs`).
//! A fuzzer includes this with `#[path = "support/heap_cap.rs"] mod heap_cap;`
//! and installs [`Counting`] as its `#[global_allocator]`.

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;
use std::time::Instant;

/// mimalloc (as in every test binary) counting each thread's live bytes, so
/// a check that runs away in memory can be stopped ([`over_cap`]).
pub struct Counting;

thread_local! {
    /// Bytes this thread has allocated and not freed (negative if it frees
    /// what another thread allocated). Const-initialised and without a
    /// destructor, so reading it inside the allocator never allocates.
    static LIVE: Cell<i64> = const { Cell::new(0) };
    /// The most `LIVE` has been since the thread's check began.
    static PEAK: Cell<i64> = const { Cell::new(0) };
    /// The cap the budget's cancel hook applies on this thread.
    static CAP: Cell<i64> = const { Cell::new(i64::MAX) };
    /// When the thread's check is over time, if it has a time limit.
    /// Set by the hook when it stops the check.
    static TRIPPED: Cell<Tripped> = const { Cell::new(Tripped::No) };
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

fn grew(bytes: usize) {
    LIVE.with(|live| {
        let now = live.get() + bytes as i64;
        live.set(now);
        PEAK.with(|peak| peak.set(peak.get().max(now)));
    });
}

fn shrank(bytes: usize) {
    LIVE.with(|live| live.set(live.get() - bytes as i64));
}

// Why `unsafe`: counting allocations means wrapping the global allocator,
// and `GlobalAlloc` is an unsafe trait. Why it's sound: each method passes
// its arguments unchanged to the same method of `MiMalloc`, which meets the
// trait's contract, and returns what that returned; the counting touches
// only thread-locals and never allocates.
#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: our caller meets `alloc`'s contract, which is `MiMalloc`'s.
        let ptr = unsafe { mimalloc::MiMalloc.alloc(layout) };
        if !ptr.is_null() {
            grew(layout.size());
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as for `alloc`.
        let ptr = unsafe { mimalloc::MiMalloc.alloc_zeroed(layout) };
        if !ptr.is_null() {
            grew(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` came from this allocator, so from `MiMalloc`, with
        // this layout.
        unsafe { mimalloc::MiMalloc.dealloc(ptr, layout) };
        shrank(layout.size());
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as for `dealloc`, and our caller meets `realloc`'s
        // contract for `new_size`.
        let new = unsafe { mimalloc::MiMalloc.realloc(ptr, layout, new_size) };
        if !new.is_null() {
            shrank(layout.size());
            grew(new_size);
        }
        new
    }
}

/// The budget's cancel hook: whether the thread's check holds more heap than
/// its cap.
pub fn over_cap() -> bool {
    let over_memory = LIVE.with(Cell::get) > CAP.with(Cell::get);
    let over_time = !over_memory
        && DEADLINE
            .with(Cell::get)
            .is_some_and(|d| Instant::now() >= d);
    if over_memory || over_time {
        TRIPPED.with(|t| {
            t.set(if over_memory {
                Tripped::Memory
            } else {
                Tripped::Time
            })
        });
    }
    over_memory || over_time
}

/// Which cap stopped the thread's check.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Tripped {
    No,
    Memory,
    Time,
}

/// Whether the thread's check since [`start`] was stopped by a cap, and
/// which.
#[allow(dead_code)] // `fuzz_elab` doesn't ask which cap
pub fn tripped() -> Tripped {
    TRIPPED.with(Cell::get)
}

/// Starts a check on this thread: it is over its cap once it holds more
/// than `cap` bytes beyond what the thread holds now, or runs past
/// `deadline`. Returns the bytes held now, which [`peak_since`] takes.
pub fn start(cap: i64, deadline: Option<Instant>) -> i64 {
    let before = LIVE.with(Cell::get);
    CAP.with(|c| c.set(before.saturating_add(cap)));
    DEADLINE.with(|d| d.set(deadline));
    TRIPPED.with(|t| t.set(Tripped::No));
    PEAK.with(|peak| peak.set(before));
    before
}

/// The most heap the check held at once, from the value [`start`] returned.
pub fn peak_since(before: i64) -> i64 {
    PEAK.with(Cell::get) - before
}
