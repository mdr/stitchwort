//! A global allocator that counts: how many allocations a benchmark makes,
//! and the most heap it has in use at once. Both are the same on every run
//! of the same program, unlike its time.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::Relaxed};

/// The system allocator, counting as it goes.
pub struct Counting;

/// Calls to `alloc`, `alloc_zeroed` and `realloc` that succeeded.
static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
/// Bytes allocated and not yet freed.
static LIVE: AtomicUsize = AtomicUsize::new(0);
/// The most `LIVE` has been since [`start`].
static PEAK: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// Whether this thread is the one being measured. Const-initialised and
    /// without a destructor, so reading it inside the allocator never
    /// allocates.
    static MEASURING: Cell<bool> = const { Cell::new(false) };
}

/// Counts an allocation, if it's on the measured thread: other threads (the
/// test harness printing "has been running for over 60 seconds", say) would
/// make the counts differ between runs.
fn counted() {
    if MEASURING.with(Cell::get) {
        ALLOCATIONS.fetch_add(1, Relaxed);
    }
}

fn grew(bytes: usize) {
    let live = LIVE.fetch_add(bytes, Relaxed) + bytes;
    if MEASURING.with(Cell::get) {
        PEAK.fetch_max(live, Relaxed);
    }
}

// Why `unsafe`: the only way to count a program's allocations is to wrap the
// global allocator, and `GlobalAlloc` is an unsafe trait. Why it's sound:
// each method passes its arguments unchanged to the same method of `System`,
// which meets the trait's contract, and returns what that returned. The
// counting only updates atomics: it never allocates, and never touches the
// memory.
#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: our caller meets `alloc`'s contract, which is `System`'s.
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            counted();
            grew(layout.size());
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as for `alloc`.
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            counted();
            grew(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` came from this allocator, so from `System`, with
        // this layout.
        unsafe { System.dealloc(ptr, layout) };
        LIVE.fetch_sub(layout.size(), Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as for `dealloc`, and our caller meets `realloc`'s
        // contract for `new_size`.
        let new = unsafe { System.realloc(ptr, layout, new_size) };
        if !new.is_null() {
            counted();
            LIVE.fetch_sub(layout.size(), Relaxed);
            grew(new_size);
        }
        new
    }
}

/// The allocator's counters at some moment.
#[derive(Clone, Copy, Debug)]
pub struct Snapshot {
    allocations: u64,
    live: usize,
}

/// Starts measuring: the peak is measured from now.
pub fn start() -> Snapshot {
    MEASURING.with(|m| m.set(true));
    let live = LIVE.load(Relaxed);
    PEAK.store(live, Relaxed);
    Snapshot {
        allocations: ALLOCATIONS.load(Relaxed),
        live,
    }
}

/// Allocations since `start`, and the most heap in use at once since then
/// beyond what was in use at `start`.
pub fn since(start: Snapshot) -> (u64, u64) {
    MEASURING.with(|m| m.set(false));
    let allocations = ALLOCATIONS.load(Relaxed) - start.allocations;
    let peak = PEAK.load(Relaxed).saturating_sub(start.live);
    (allocations, peak as u64)
}
