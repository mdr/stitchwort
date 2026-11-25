//! The crate's integration tests in one binary (docs/proposals/fewer-test-binaries.md).

mod builtins;
mod deformat;
mod derive_cost;
mod fmt_hashes;
mod hash_stability;
mod import_cost;
mod pinned_hashes;
mod reads_chain_cost;
mod search_at;
mod search_at_bench;
mod search_bench;
mod search_match;
mod std_index_cache;
mod std_library;
mod warning_pins;

// About 12% less CPU on the from-source std checks than the system allocator
// (docs/reviews/SW-1742-mimalloc.md).
use stitchwort_test_alloc as _;
