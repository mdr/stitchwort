//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod caching;
mod check_cache;
mod goal_index;
mod live_memory;
mod lsp;
mod navigation;
mod rename;
mod repl;
mod search;
mod session;

// test-alloc: global allocator is stitchwort_bench::alloc::Counting, which wraps mimalloc.
