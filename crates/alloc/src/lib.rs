//! mimalloc as a global allocator, calling its plain entry points where the
//! alignment is one they always give. `mimalloc::MiMalloc` calls the
//! `_aligned` variants every time (mimalloc 0.1.52, `src/lib.rs`, lines
//! 48-71). In mimalloc v3 those take their fast path only when the size
//! class's page has a free block ready; otherwise they go to
//! `mi_theap_malloc_zero_aligned_at_generic`, which uses the plain path only
//! when `mi_malloc_is_naturally_aligned` (a power-of-two block size up to
//! `MI_PAGE_MAX_START_BLOCK_ALIGN2`), and else over-allocates `size +
//! alignment - 1` bytes in a larger size class (libmimalloc-sys 0.1.49,
//! `c_src/mimalloc/v3/src/alloc-aligned.c`, lines 18-28, 153-181 and
//! 185-232). Most of the checker's blocks are not powers of two (an
//! environment of n values is 16 + 56n bytes), and the cell-heavy runtime
//! profiles showed the `_aligned` calls too.
//!
//! The binaries that link this declare it themselves:
//!
//! ```ignore
//! #[global_allocator]
//! static ALLOCATOR: stitchwort_alloc::Allocator = stitchwort_alloc::Allocator;
//! ```

#![allow(unsafe_code)]

use std::alloc::{GlobalAlloc, Layout};
use std::ffi::c_void;

use libmimalloc_sys::{
    mi_free, mi_malloc, mi_malloc_aligned, mi_realloc, mi_realloc_aligned, mi_zalloc,
    mi_zalloc_aligned,
};

/// mimalloc, plain where it can be (above).
pub struct Allocator;

/// The alignment `mi_malloc`, `mi_zalloc` and `mi_realloc` give a block of
/// at least that size: `MI_MAX_ALIGN_SIZE` (`v3/include/mimalloc/types.h`,
/// line 38; asserted of every block that size or larger at
/// `v3/src/alloc.c`, line 52). A smaller block may be aligned only to its
/// size class, so the plain calls also need `align <= size`, as Rust's
/// system allocator checks before calling `malloc`.
const NATURAL_ALIGN: usize = 16;

#[inline]
fn plain(align: usize, size: usize) -> bool {
    align <= NATURAL_ALIGN && align <= size
}

// SAFETY (whole impl): each call forwards to the mimalloc entry point that
// satisfies the layout's size and alignment (`NATURAL_ALIGN` and below, with
// the size at least the alignment: the plain one; otherwise the `_aligned`
// one). `mi_free` frees a block from either, and `mi_realloc` and
// `mi_realloc_aligned` take a block from either.
unsafe impl GlobalAlloc for Allocator {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: the caller upholds `GlobalAlloc::alloc`'s contract.
        unsafe {
            if plain(layout.align(), layout.size()) {
                mi_malloc(layout.size()) as *mut u8
            } else {
                mi_malloc_aligned(layout.size(), layout.align()) as *mut u8
            }
        }
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: as for `alloc`.
        unsafe {
            if plain(layout.align(), layout.size()) {
                mi_zalloc(layout.size()) as *mut u8
            } else {
                mi_zalloc_aligned(layout.size(), layout.align()) as *mut u8
            }
        }
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        // SAFETY: `ptr` came from this allocator; `mi_free` takes either kind.
        unsafe { mi_free(ptr as *mut c_void) }
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: as for `alloc`.
        unsafe {
            if plain(layout.align(), new_size) {
                mi_realloc(ptr as *mut c_void, new_size) as *mut u8
            } else {
                mi_realloc_aligned(ptr as *mut c_void, new_size, layout.align()) as *mut u8
            }
        }
    }
}
