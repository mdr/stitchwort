//! The global allocator of the test binaries: mimalloc, as the CLI uses.
//!
//! Where the system allocator is musl's (the Linux build), many threads
//! allocating at once are several times slower than with mimalloc: the
//! elaborator fuzzer's 200 cases took 229 s, against 37.5 s. On macOS the
//! system allocator also keeps freed blocks (SW-921), so memory-bound tests
//! need mimalloc to measure what the CLI does.
//!
//! A test target opts in with `use stitchwort_test_alloc as _;` (a unit-test
//! binary: `#[cfg(test)] use stitchwort_test_alloc as _;` in `lib.rs`) and
//! the crate as a dev-dependency. The `use` is what links this crate in.
//! `dev/test-alloc-check` fails if a test target lacks it, and so does a
//! target with an allocator of its own, which would be a second
//! `#[global_allocator]`: those tests have a counting allocator that wraps
//! mimalloc or the system's.

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;
