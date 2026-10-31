//! Measuring how much of the native stack is in use, so that recursive passes
//! stop with an error before they overflow it
//! (docs/proposals/stack-safe-evaluation.md). Rust aborts on a stack
//! overflow; the error can't be caught.
//!
//! A pass notes where the stack is when it starts ([`StackLimit::from_here`])
//! and compares the address of a local variable with that at each level of
//! recursion. That measures the stack actually used, so the same limit in
//! bytes works for debug and release builds, whose frames differ in size.

/// Where the stack currently is: the address of a local variable. Stacks grow
/// downwards on every target we build for, including WebAssembly's stack in
/// linear memory.
#[inline(always)]
pub fn position() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

/// The lowest stack address a pass may reach.
#[derive(Clone, Copy, Debug)]
pub struct StackLimit {
    floor: usize,
}

impl StackLimit {
    /// Allows `bytes` more of the stack, from here.
    pub fn from_here(bytes: usize) -> StackLimit {
        StackLimit {
            floor: position().saturating_sub(bytes),
        }
    }

    /// Whether the stack has gone past the limit.
    #[inline]
    pub fn exceeded(&self) -> bool {
        position() < self.floor
    }
}

/// The lowest address of the current thread's stack, if the platform says
/// (Linux and macOS), with the `stack-check` feature: for the check that a
/// session runs on a thread at least as large as its limits assume
/// (`Budget::start`). Asked once per thread.
#[cfg(all(feature = "stack-check", unix))]
pub fn thread_stack_low() -> Option<usize> {
    use std::cell::Cell;
    thread_local! {
        /// 0 until asked; `usize::MAX` if the platform didn't say.
        static LOW: Cell<usize> = const { Cell::new(0) };
    }
    let low = LOW.with(|low| {
        if low.get() == 0 {
            low.set(ask_thread_stack_low().unwrap_or(usize::MAX));
        }
        low.get()
    });
    (low != usize::MAX).then_some(low)
}

/// [`thread_stack_low`] on other platforms: unknown.
#[cfg(not(all(feature = "stack-check", unix)))]
pub fn thread_stack_low() -> Option<usize> {
    None
}

// The thread library's own record of the thread's stack: `pthread_self`'s
// attributes are always valid to read, and the out-parameters are locals.
#[cfg(all(feature = "stack-check", target_os = "linux"))]
#[allow(unsafe_code)]
fn ask_thread_stack_low() -> Option<usize> {
    // SAFETY: see above; the attributes are initialised by
    // `pthread_getattr_np` and destroyed after use.
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return None;
        }
        let mut addr: *mut libc::c_void = std::ptr::null_mut();
        let mut size: libc::size_t = 0;
        let ok = libc::pthread_attr_getstack(&attr, &mut addr, &mut size) == 0;
        libc::pthread_attr_destroy(&mut attr);
        ok.then_some(addr as usize)
    }
}

#[cfg(all(feature = "stack-check", target_os = "macos"))]
#[allow(unsafe_code)]
fn ask_thread_stack_low() -> Option<usize> {
    // SAFETY: see above; both calls only read the current thread's record.
    unsafe {
        let this = libc::pthread_self();
        let top = libc::pthread_get_stackaddr_np(this) as usize;
        top.checked_sub(libc::pthread_get_stacksize_np(this))
    }
}

#[cfg(all(
    feature = "stack-check",
    unix,
    not(any(target_os = "linux", target_os = "macos"))
))]
fn ask_thread_stack_low() -> Option<usize> {
    None
}
