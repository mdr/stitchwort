//! The host of a run: what `stitchwort run` and the standalone executables
//! share (docs/proposals/standalone-executables.md, S2). The Unix terminal
//! and its restoring are in [`terminal`]; [`with_stack`] runs a closure on a
//! thread with a chosen stack.

#[cfg(unix)]
pub mod stack;
#[cfg(unix)]
pub mod terminal;

/// The stack `stitchwort run --native` runs on (64-bit targets only: it
/// does not fit a 32-bit usize, as in the WebAssembly build): address space
/// reserved, not memory until it's touched. It's the cap on a native run's
/// stack (`stitchwort_rt::native_abi::STACK_CAP`, D1299 of
/// docs/proposals/native-only.md), so it holds whatever stack the run sizes
/// for its frames; a built executable reserves only that.
#[cfg(target_pointer_width = "64")]
pub const NATIVE_STACK: usize = 64 * 1024 * 1024 * 1024;

/// Runs `f` on a new thread with `stack` bytes of stack, for a session whose
/// limits are `Limits::for_stack` of the same size.
pub fn with_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> T {
    try_with_stack(stack, f).expect("can't start a thread")
}

/// [`with_stack`], or the error if the thread can't be started (the
/// operating system refused the stack).
///
/// On Unix the stack is mapped here ([`stack::run_on`]) rather than by the
/// thread library, so that Linux reserves it as address space only: glibc
/// maps a thread's stack as accounted memory, which Linux's default
/// overcommit heuristic refuses past RAM plus swap (a 64 GiB stack on a
/// 16 GB machine; stage NO7 of docs/proposals/native-only.md).
#[cfg(unix)]
pub fn try_with_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> std::io::Result<T> {
    stack::run_on(stack, f)
}

/// [`with_stack`], or the error if the thread can't be started.
#[cfg(not(unix))]
pub fn try_with_stack<T: Send>(stack: usize, f: impl FnOnce() -> T + Send) -> std::io::Result<T> {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new()
            .stack_size(stack)
            .spawn_scoped(scope, f)?;
        Ok(thread
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic)))
    })
}
