//! A global allocator that counts: how many allocations a benchmark makes,
//! and the most heap it has in use at once. Both are the same on every run
//! of the same program, unlike its time.

use std::alloc::{GlobalAlloc, Layout};

use mimalloc::MiMalloc;
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

/// mimalloc (the CLI's allocator), counting as it goes.
pub struct Counting;

/// Bytes allocated and not yet freed.
static LIVE: AtomicUsize = AtomicUsize::new(0);
/// The most `LIVE` has been since [`start`].
static PEAK: AtomicUsize = AtomicUsize::new(0);

thread_local! {
    /// Whether this thread is the one being measured. Const-initialised and
    /// without a destructor, so reading it inside the allocator never
    /// allocates.
    static MEASURING: Cell<bool> = const { Cell::new(false) };
    /// Calls to `alloc`, `alloc_zeroed` and `realloc` that succeeded on this
    /// thread while it was being measured.
    /// Whether this thread's allocations update the process-wide `LIVE` and
    /// `PEAK`. Off for the worker threads of a benchmark with parts, which
    /// measure per thread (below): eight threads hammering one atomic made
    /// them several times slower.
    static GLOBAL: Cell<bool> = const { Cell::new(true) };
    static ALLOCATIONS: Cell<u64> = const { Cell::new(0) };
    /// Bytes this thread has allocated and not freed (negative if it frees
    /// what another thread allocated), and the most that has been since
    /// [`part_start`]: the figures for the parts of a benchmark that run on
    /// several threads, where the heap in use overall depends on how the
    /// threads interleave.
    static THREAD_LIVE: Cell<i64> = const { Cell::new(0) };
    static THREAD_PEAK: Cell<i64> = const { Cell::new(0) };
}

/// Counts an allocation, if it's on the measured thread: other threads (the
/// test harness printing "has been running for over 60 seconds", say) would
/// make the counts differ between runs.
fn counted() {
    if MEASURING.with(Cell::get) {
        ALLOCATIONS.with(|a| a.set(a.get() + 1));
    }
}

fn grew(bytes: usize) {
    THREAD_LIVE.with(|live| {
        let now = live.get() + bytes as i64;
        live.set(now);
        THREAD_PEAK.with(|peak| peak.set(peak.get().max(now)));
    });
    if GLOBAL.with(Cell::get) {
        let live = LIVE.fetch_add(bytes, Relaxed) + bytes;
        if MEASURING.with(Cell::get) {
            PEAK.fetch_max(live, Relaxed);
        }
    }
}

// Why `unsafe`: the only way to count a program's allocations is to wrap the
// global allocator, and `GlobalAlloc` is an unsafe trait. Why it's sound:
// each method passes its arguments unchanged to the same method of `MiMalloc`,
// which meets the trait's contract, and returns what that returned. The
// counting only updates atomics: it never allocates, and never touches the
// memory.
#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: our caller meets `alloc`'s contract, which is `MiMalloc`'s.
        let ptr = unsafe { MiMalloc.alloc(layout) };
        if !ptr.is_null() {
            counted();
            grew(layout.size());
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as for `alloc`.
        let ptr = unsafe { MiMalloc.alloc_zeroed(layout) };
        if !ptr.is_null() {
            counted();
            grew(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr` came from this allocator, so from `MiMalloc`, with
        // this layout.
        unsafe { MiMalloc.dealloc(ptr, layout) };
        THREAD_LIVE.with(|live| live.set(live.get() - layout.size() as i64));
        if GLOBAL.with(Cell::get) {
            LIVE.fetch_sub(layout.size(), Relaxed);
        }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as for `dealloc`, and our caller meets `realloc`'s
        // contract for `new_size`.
        let new = unsafe { MiMalloc.realloc(ptr, layout, new_size) };
        if !new.is_null() {
            counted();
            THREAD_LIVE.with(|live| live.set(live.get() - layout.size() as i64));
            if GLOBAL.with(Cell::get) {
                LIVE.fetch_sub(layout.size(), Relaxed);
            }
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
        allocations: allocations(),
        live,
    }
}

/// Allocations counted so far, for the difference between two moments while
/// measuring. Reading it doesn't allocate.
pub fn allocations() -> u64 {
    ALLOCATIONS.with(Cell::get)
}

/// Starts or stops counting allocations on this thread, for a worker thread
/// of a benchmark; [`start`] does it for the benchmark's own thread.
pub fn measure_this_thread(on: bool) {
    MEASURING.with(|m| m.set(on));
    GLOBAL.with(|g| g.set(!on));
}

/// Where a part of a benchmark started on this thread ([`part_start`]).
#[derive(Clone, Copy, Debug)]
pub struct PartMark {
    allocations: u64,
    live: i64,
}

/// Starts a part of a benchmark on this thread: its peak is measured from
/// now.
pub fn part_start() -> PartMark {
    let live = THREAD_LIVE.with(Cell::get);
    THREAD_PEAK.with(|p| p.set(live));
    PartMark {
        allocations: allocations(),
        live,
    }
}

/// The allocations this thread made since `mark`, and the most heap this
/// thread had in use at once beyond what it had at `mark`.
pub fn part_end(mark: PartMark) -> (u64, u64) {
    let peak = THREAD_PEAK.with(Cell::get) - mark.live;
    (allocations() - mark.allocations, peak.max(0) as u64)
}

/// Bytes allocated and not yet freed, on every thread. Reading it doesn't
/// allocate.
pub fn live() -> usize {
    LIVE.load(Relaxed)
}

/// Allocations since `start`, and the most heap in use at once since then
/// beyond what was in use at `start`.
pub fn since(start: Snapshot) -> (u64, u64) {
    MEASURING.with(|m| m.set(false));
    let allocations = allocations() - start.allocations;
    let peak = PEAK.load(Relaxed).saturating_sub(start.live);
    (allocations, peak as u64)
}
