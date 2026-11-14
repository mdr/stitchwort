//! Helpers shared by the proof tests.

/// The tests' thread stack, and the session's limits are made for the same
/// size: a session built with `Session::new()` assumes a 2 MiB thread, and
/// in a debug build (whose frames are several times larger) the library's
/// deeper proofs ran out of that budget however big the thread was.
pub const STACK: usize = 64 << 20;

/// The same, for the slow (`#[ignore]`d) tests that load every library file,
/// whose proofs are deeper.
pub const BIG_STACK: usize = 256 << 20;
