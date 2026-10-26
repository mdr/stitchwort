//! A thread on a stack this module maps (stage NO7 of
//! docs/proposals/native-only.md).
//!
//! A native run's stack is sized for its frame limit: 9.1 GB for the
//! roguelike, up to the 64 GiB cap (D1299), of which a run touches only what
//! it recurses into. The thread library maps a thread's stack as ordinary
//! private memory, which Linux charges against its commit limit: under the
//! default heuristic (`vm.overcommit_memory` 0) a single mapping bigger than
//! RAM plus swap is refused, so `run --native`'s 64 GiB failed on a 16 GB
//! machine, and a built executable's 9.1 GB would on a small one. Mapped
//! here with `MAP_NORESERVE`, the stack is address space only under the
//! heuristic and under "always" (mode 1). Under strict accounting (mode 2)
//! Linux ignores `MAP_NORESERVE` and a stack past the commit limit is
//! refused, which the caller reports before anything runs. macOS reserves
//! address space lazily either way, and takes the same path.
//!
//! The lowest [`GUARD`] bytes are inaccessible, as the thread library's
//! guard page is: a Rust function that overflowed the stack would fault
//! there, not write past it. Native code stops well above it (the frame
//! counter, then the stack-pointer check).

use std::ffi::c_void;
use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::ptr;

/// The inaccessible bytes below the stack (rounded up to whole pages).
pub const GUARD: usize = 64 * 1024;

// POSIX, in glibc and in macOS's libSystem; the `libc` crate binds it for
// Linux only.
#[allow(unsafe_code)]
unsafe extern "C" {
    fn pthread_attr_setstack(
        attr: *mut libc::pthread_attr_t,
        stackaddr: *mut c_void,
        stacksize: libc::size_t,
    ) -> libc::c_int;
}

/// A closure and, once the thread has run it, what it returned or how it
/// panicked.
struct Job<F, T> {
    f: Option<F>,
    result: Option<std::thread::Result<T>>,
}

/// The new thread's start: runs the job's closure, catching a panic so it
/// can be raised again in the caller, as `std::thread`'s join does.
extern "C" fn start<F: FnOnce() -> T, T>(job: *mut c_void) -> *mut c_void {
    // SAFETY: `job` is the `Job` `run_on` made, which outlives this thread
    // (it joins before returning) and which nothing else touches meanwhile.
    #[allow(unsafe_code)]
    let job = unsafe { &mut *job.cast::<Job<F, T>>() };
    if let Some(f) = job.f.take() {
        job.result = Some(catch_unwind(AssertUnwindSafe(f)));
    }
    ptr::null_mut()
}

/// An `mmap`ped region, unmapped when dropped.
struct Mapping {
    base: *mut c_void,
    len: usize,
}

impl Drop for Mapping {
    fn drop(&mut self) {
        // SAFETY: `base` and `len` are a mapping `run_on` made, whose
        // thread has ended.
        #[allow(unsafe_code)]
        unsafe {
            libc::munmap(self.base, self.len);
        }
    }
}

/// The error for a pthread function's nonzero result.
fn check(code: i32) -> io::Result<()> {
    if code == 0 {
        Ok(())
    } else {
        Err(io::Error::from_raw_os_error(code))
    }
}

/// Runs `f` on a new thread whose stack is `stack` bytes (rounded up to
/// whole pages) mapped here, and returns what it returned; a panic in `f`
/// is raised again here. An error, with nothing run, if the stack can't be
/// mapped or the thread can't be started.
#[allow(unsafe_code)]
pub fn run_on<T: Send, F: FnOnce() -> T + Send>(stack: usize, f: F) -> io::Result<T> {
    // SAFETY: `sysconf` has no preconditions.
    let page = usize::try_from(unsafe { libc::sysconf(libc::_SC_PAGESIZE) })
        .ok()
        .filter(|&page| page > 0)
        .unwrap_or(4096);
    let round = |n: usize| n.checked_next_multiple_of(page);
    let too_big = || io::Error::new(io::ErrorKind::InvalidInput, "the stack is too big");
    let size = round(stack.max(page)).ok_or_else(too_big)?;
    let guard = round(GUARD).ok_or_else(too_big)?;
    let len = size.checked_add(guard).ok_or_else(too_big)?;

    #[cfg(any(target_os = "linux", target_os = "android"))]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE | libc::MAP_STACK;
    #[cfg(not(any(target_os = "linux", target_os = "android")))]
    let flags = libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_NORESERVE;
    // SAFETY: a fresh anonymous mapping, at an address the kernel picks.
    let base = unsafe {
        libc::mmap(
            ptr::null_mut(),
            len,
            libc::PROT_READ | libc::PROT_WRITE,
            flags,
            -1,
            0,
        )
    };
    if base == libc::MAP_FAILED {
        return Err(io::Error::last_os_error());
    }
    let mapping = Mapping { base, len };
    // SAFETY: the first `guard` bytes of the mapping just made.
    if unsafe { libc::mprotect(base, guard, libc::PROT_NONE) } != 0 {
        return Err(io::Error::last_os_error());
    }

    let mut job = Job {
        f: Some(f),
        result: None,
    };
    // SAFETY: the attributes are initialised before use and destroyed
    // after; the stack is the mapping above the guard, page-aligned and a
    // whole number of pages, which outlives the thread (joined below, before
    // `mapping` is dropped); `job` outlives the thread too, and this thread
    // doesn't touch it until the join. `F` and `T` are `Send`, so running
    // the closure and returning its result on the other thread is sound, as
    // in `std::thread::scope`.
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        check(libc::pthread_attr_init(&mut attr))?;
        let started = check(pthread_attr_setstack(
            &mut attr,
            base.cast::<u8>().add(guard).cast::<c_void>(),
            size,
        ))
        .and_then(|()| {
            let mut thread: libc::pthread_t = std::mem::zeroed();
            check(libc::pthread_create(
                &mut thread,
                &attr,
                start::<F, T>,
                (&raw mut job).cast::<c_void>(),
            ))
            .map(|()| thread)
        });
        libc::pthread_attr_destroy(&mut attr);
        let thread = started?;
        // A thread that can't be joined would leave `job` and the stack in
        // use: give up rather than free them.
        if libc::pthread_join(thread, ptr::null_mut()) != 0 {
            std::process::abort();
        }
    }
    drop(mapping);
    match job.result {
        Some(Ok(value)) => Ok(value),
        Some(Err(panic)) => resume_unwind(panic),
        None => unreachable!("the thread ran its job"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_closure_runs_on_the_stack_given() {
        let outside = 0u8;
        let outside = &raw const outside as usize;
        let (inside, answer) = run_on(1024 * 1024, || {
            let marker = 0u8;
            (std::hint::black_box(&raw const marker) as usize, 42)
        })
        .expect("a thread");
        assert_eq!(answer, 42);
        assert!(inside.abs_diff(outside) > 1024 * 1024, "the caller's stack");
    }

    #[test]
    fn it_borrows_from_the_caller() {
        let mut seen = Vec::new();
        run_on(1024 * 1024, || seen.push(1)).expect("a thread");
        assert_eq!(seen, [1]);
    }

    #[test]
    fn a_deep_recursion_uses_the_whole_stack() {
        fn depth(n: u64) -> u64 {
            let pad = std::hint::black_box([n; 64]);
            if n == 0 {
                0
            } else {
                1 + depth(n - 1) + pad[0] - n
            }
        }
        // 512 bytes or more a frame, 100,000 frames: over 50 MB.
        let stack = 256 * 1024 * 1024;
        assert_eq!(run_on(stack, || depth(100_000)).expect("a thread"), 100_000);
    }

    #[test]
    fn a_panic_is_raised_in_the_caller() {
        let caught = std::panic::catch_unwind(|| {
            run_on(1024 * 1024, || panic!("inside")).expect("a thread");
        });
        let message = caught.expect_err("the panic");
        assert_eq!(message.downcast_ref::<&str>(), Some(&"inside"));
    }

    /// The cap on a native run's stack is address space: mapping it costs
    /// no memory, under Linux's default overcommit heuristic too.
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn the_cap_is_reserved_without_memory() {
        let cap = crate::NATIVE_STACK;
        assert_eq!(run_on(cap, || 7).expect("64 GiB of address space"), 7);
    }
}
