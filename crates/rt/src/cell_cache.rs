//! A run's cache of freed cells, which native code takes from and gives
//! back to inline, in front of the global allocator (docs/proposals/cell-allocator.md,
//! option C; a trial, SW-2363).
//!
//! A cached block is the allocation of an `Rc<[Value]>` of 1 to
//! [`ARITIES`] fields that native code's `Unpack` emptied while it was
//! unique (strong and weak counts 1), and so would otherwise have freed.
//! It is never deallocated while cached, so when it's taken again it's an
//! allocation of exactly the layout an `Rc<[Value]>` of that many fields
//! frees, as [`sw_cell_new`](crate::native_abi::sw_cell_new)'s are, and any
//! Rust drop can free it. A block is in at most one list, and is either
//! cached or live, never both: only the code that held its last reference
//! caches it, and taking it removes it from the list.
//!
//! The lists are threaded through the blocks' strong-count words (the next
//! block's address, or 0); a cached block's weak count stays 1, so taking
//! a block only stores its strong count. Native code fills every field of
//! a taken cell before it's read, as it does a new one.
//!
//! The cache holds at most [`CAP`] bytes. Its room is only taken from in
//! native code, as a block is cached (a take doesn't give it back, which
//! keeps the take short); when it runs out, [`CellCache::full`] counts the
//! lists again, and cuts them to half the cap if they're fuller.
//!
//! The cache belongs to a [`NativeExecutor`](crate::native_abi::NativeExecutor),
//! which lends it to each crossing's [`Context`](crate::native_abi::Context)
//! and takes it back after; dropping it (when the run ends, or a crossing
//! fails) frees every block it holds. Code compiled with `trace_refcounts`
//! doesn't use it, and other code is lent an empty cache with no room while
//! a trace may be recording ([`CellCache::lend`]), so the allocation trace
//! sees every allocation and free.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::native_abi::{RC_VALUE_AT, STRONG_AT, WEAK_AT};
use crate::value::Value;

/// Whether native code uses the cache: the one switch. Off, the generated
/// code is as it was before the cache, and the lists stay empty.
pub const ENABLED: bool = true;

/// The most fields a cached cell has (the helpers' fixed sizes).
pub const ARITIES: u64 = 8;

/// The most bytes the cache holds, so the blocks it keeps from the
/// allocator are bounded.
pub const CAP: u64 = 64 << 20;

/// The size of a cell of `n` fields' allocation: what the cache counts
/// against [`CAP`].
pub const fn block_bytes(n: u64) -> u64 {
    RC_VALUE_AT as u64 + n * size_of::<Value>() as u64
}

/// The lists, at the offsets native code reads (`repr(C)`).
#[repr(C)]
pub struct CellCache {
    /// For cells of `n` fields, at `n - 1`: the first cached block's
    /// address (where its counts are), or 0.
    pub heads: [u64; ARITIES as usize],
    /// At most the bytes more the cache may hold: native code takes from
    /// it as it caches a block, but doesn't give back as it takes one (so
    /// a take is as short as it can be), and counts it again when it runs
    /// out ([`CellCache::full`]).
    pub room: u64,
}

impl CellCache {
    /// The offset of the list of cells of `n` fields (1 to [`ARITIES`]).
    pub const fn head_at(n: u64) -> i32 {
        assert!(n >= 1 && n <= ARITIES);
        (std::mem::offset_of!(CellCache, heads) + (n as usize - 1) * 8) as i32
    }

    pub const ROOM_AT: i32 = std::mem::offset_of!(CellCache, room) as i32;

    /// The cache for a crossing's context, taken from the run's. While an
    /// allocation trace may be recording, an empty one with no room, so
    /// native code makes and frees every cell through the runtime, which
    /// records it (the tests compare untraced code's trace with the
    /// machine's too).
    pub(crate) fn lend(&mut self) -> CellCache {
        if crate::alloc_trace::recording() {
            *self = CellCache::default();
            CellCache {
                heads: [0; ARITIES as usize],
                room: 0,
            }
        } else {
            std::mem::take(self)
        }
    }
}

impl CellCache {
    /// Native code's push of the emptied cell of `n` fields at `cell` found
    /// too little room: the room counted again from the lists, which are
    /// first cut to half the cap if they hold more (so counting again is
    /// rare), and the cell kept.
    ///
    /// # Safety
    /// `cell` is the address of a unique `Rc<[Value]>` allocation of `n`
    /// fields (1 to [`ARITIES`]), all moved out, that native code gives up.
    #[allow(unsafe_code)]
    pub(crate) unsafe fn full(&mut self, cell: u64, n: u64) {
        let mut held = 0;
        for (i, &head) in self.heads.iter().enumerate() {
            let mut block = head;
            while block != 0 {
                census(block, i as u64 + 1);
                held += block_bytes(i as u64 + 1);
                // SAFETY: a cached block's strong-count word is the next.
                block = unsafe { next(block) };
            }
        }
        let mut freed = 0;
        for (i, head) in self.heads.iter_mut().enumerate() {
            while held > CAP / 2 && *head != 0 {
                let block = *head;
                // SAFETY: as in `drop`.
                unsafe {
                    *head = next(block);
                    free_block(block, i as u64 + 1);
                }
                held -= block_bytes(i as u64 + 1);
                freed += 1;
            }
        }
        DRAINED.fetch_add(freed, Ordering::Relaxed);
        // At most half the cap is held, so the cell fits.
        let bytes = block_bytes(n);
        self.room = CAP - held - bytes;
        let head = &mut self.heads[n as usize - 1];
        // SAFETY: the caller's contract: the block is native code's to give
        // up, and nothing else refers to it.
        unsafe { (cell as *mut u64).add(STRONG_AT as usize / 8).write(*head) };
        *head = cell;
    }
}

/// The next block in the list after the cached `block`.
///
/// # Safety
/// `block` is a cached block.
#[allow(unsafe_code)]
unsafe fn next(block: u64) -> u64 {
    // SAFETY: the caller's contract; the strong-count word is the link.
    unsafe {
        (block as *const u8)
            .add(STRONG_AT as usize)
            .cast::<u64>()
            .read()
    }
}

impl Default for CellCache {
    fn default() -> CellCache {
        CellCache {
            heads: [0; ARITIES as usize],
            room: CAP,
        }
    }
}

/// Blocks freed by draining caches, in this process: for tests, to see
/// that a run cached something.
static DRAINED: AtomicU64 = AtomicU64::new(0);

/// How many cached blocks caches have freed so far, in this process.
pub fn drained() -> u64 {
    DRAINED.load(Ordering::Relaxed)
}

/// SW-2428, a measurement only: cached blocks seen when a cache is cut or
/// dropped, and how many of them are smaller than a dilated cell (cells
/// built outside `sw_cell_new`'s fixed path, which the cache's lists, keyed
/// by field count, take as well). Printed at exit with
/// `SW_DILATION_REPORT=1`.
pub static SEEN: AtomicU64 = AtomicU64::new(0);
pub static UNDILATED: AtomicU64 = AtomicU64::new(0);

#[cfg(not(target_arch = "wasm32"))]
#[allow(unsafe_code)]
unsafe extern "C" {
    fn mi_usable_size(p: *const std::ffi::c_void) -> usize;
}

/// Counts `block` (a cached cell of `n` fields) in [`SEEN`] and, if its
/// allocation is too small to hold the dilation, [`UNDILATED`].
#[allow(unsafe_code)]
fn census(block: u64, n: u64) {
    // A build of its own (`SW_DILATION_CENSUS=1` at build time): counting
    // in `full`'s walk adds about 5% to binary-trees' instructions, so the
    // timed builds leave it out.
    if crate::native_abi::DILATION == 0 || option_env!("SW_DILATION_CENSUS").is_none() {
        return;
    }
    SEEN.fetch_add(1, Ordering::Relaxed);
    #[cfg(not(target_arch = "wasm32"))]
    {
        let want = block_bytes(n) as usize + crate::native_abi::DILATION;
        // SAFETY: a cached block is a live allocation from mimalloc.
        if unsafe { mi_usable_size(block as *const std::ffi::c_void) } < want {
            UNDILATED.fetch_add(1, Ordering::Relaxed);
        }
    }
}

/// Prints [`SEEN`] and [`UNDILATED`] if `SW_DILATION_REPORT=1`.
pub fn dilation_report() {
    if std::env::var_os("SW_DILATION_REPORT").is_some_and(|v| v == "1") {
        eprintln!(
            "dilation {}: cached blocks seen {}, undilated {}",
            crate::native_abi::DILATION,
            SEEN.load(Ordering::Relaxed),
            UNDILATED.load(Ordering::Relaxed)
        );
    }
}

impl Drop for CellCache {
    #[allow(unsafe_code)]
    fn drop(&mut self) {
        let mut freed = 0;
        for (i, head) in self.heads.iter_mut().enumerate() {
            let n = i as u64 + 1;
            let mut block = std::mem::take(head);
            while block != 0 {
                census(block, n);
                // SAFETY: a cached block is an `Rc<[Value]>` allocation of
                // `n` fields that nothing else refers to (the module's
                // invariant), whose strong-count word holds the next.
                unsafe {
                    let at = block as *const u8;
                    debug_assert_eq!(at.add(WEAK_AT as usize).cast::<u64>().read(), 1);
                    let after = next(block);
                    free_block(block, n);
                    block = after;
                }
                freed += 1;
            }
        }
        self.room = CAP;
        if freed > 0 {
            DRAINED.fetch_add(freed, Ordering::Relaxed);
        }
    }
}

/// Frees the block of a cell of `n` fields at `cell`, as
/// [`sw_cell_free`](crate::native_abi::sw_cell_free) frees an emptied
/// cell, once its strong count (the list's link) is 1 again.
///
/// # Safety
/// `cell` is the address of an `Rc<[Value]>` allocation of `n` fields
/// that nothing else refers to, with a weak count of 1.
#[allow(unsafe_code)]
unsafe fn free_block(cell: u64, n: u64) {
    // SAFETY: the caller's contract.
    unsafe {
        (cell as *mut u64).add(STRONG_AT as usize / 8).write(1);
        crate::native_abi::free_emptied(cell, n);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A new cell of `n` fields, given up as `Unpack` gives one up.
    #[allow(unsafe_code)]
    fn emptied(n: u64) -> u64 {
        // SAFETY: its fields are never read: the cache frees it as
        // `MaybeUninit` values.
        unsafe { crate::native_abi::sw_cell_new(0, n) }
    }

    fn len(cache: &CellCache, n: u64) -> u64 {
        let mut block = cache.heads[n as usize - 1];
        let mut len = 0;
        while block != 0 {
            len += 1;
            // SAFETY: a cached block.
            #[allow(unsafe_code)]
            let after = unsafe { next(block) };
            block = after;
        }
        len
    }

    #[test]
    #[allow(unsafe_code)]
    fn full_counts_the_room_again_and_cuts_the_lists_to_half_the_cap() {
        let mut cache = CellCache {
            heads: [0; ARITIES as usize],
            room: 0,
        };
        // Room used up by blocks since taken: counted again, the cell kept.
        // SAFETY: an emptied cell of 2 fields.
        unsafe { cache.full(emptied(2), 2) };
        assert_eq!(len(&cache, 2), 1);
        assert_eq!(cache.room, CAP - block_bytes(2));
        // Lists holding the whole cap, as native code pushes: cut to half.
        let fill = CAP / block_bytes(3);
        for _ in 0..fill {
            let cell = emptied(3);
            // SAFETY: as native code pushes, onto the list of its size.
            unsafe { (cell as *mut u64).write(cache.heads[2]) };
            cache.heads[2] = cell;
        }
        cache.room = 0;
        let before = drained();
        // SAFETY: as above.
        unsafe { cache.full(emptied(1), 1) };
        let held = block_bytes(2) * len(&cache, 2) + block_bytes(3) * len(&cache, 3);
        assert!(held <= CAP / 2, "{held} bytes held");
        assert_eq!(len(&cache, 1), 1);
        assert_eq!(cache.room, CAP - held - block_bytes(1));
        assert!(drained() > before);
    }
}
