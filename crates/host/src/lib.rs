//! The host of a run: what `stitchwort run` and the standalone executables
//! share (docs/proposals/standalone-executables.md, S2). The Unix terminal
//! and its restoring are in [`terminal`]; [`with_stack`] runs a closure on a
//! thread with a chosen stack.

#[cfg(unix)]
pub mod terminal;

/// The stack a natively compiled program runs on (64-bit targets only: it
/// does not fit a 32-bit usize, as in the WebAssembly build): address space reserved,
/// not memory until it's touched. Native frames are on it, and it's only a
/// safety margin behind the frame limit (sized so the default 2,000,000
/// frames of native frames up to 8 KiB fit, `stitchwort_native::frames`), which defines how deep a program
/// may go (native-compilation.md §4.3).
#[cfg(target_pointer_width = "64")]
pub const NATIVE_STACK: usize = 16 * 1024 * 1024 * 1024;

/// Runs `f` on a new thread with `stack` bytes of stack, for a session whose
/// limits are `Limits::for_stack` of the same size.
pub fn with_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(stack)
            .spawn_scoped(scope, f)
            .expect("can't start a thread")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}
