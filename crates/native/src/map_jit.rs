//! Code memory for macOS on Apple Silicon the way Apple asks JITs to get it:
//! mapped with `MAP_JIT`, written while `pthread_jit_write_protect_np(0)` lets
//! this thread write it, then made executable again with
//! `pthread_jit_write_protect_np(1)`
//! (<https://developer.apple.com/documentation/apple-silicon/porting-just-in-time-compilers-to-apple-silicon>).
//!
//! cranelift-jit 0.136's own provider (`SystemMemoryProvider`) maps code
//! memory with a plain anonymous mapping and `mprotect`s it to read+execute
//! (cranelift-jit-0.136.2/src/memory/system.rs, `PtrLen::with_size` and
//! `set_readable_and_executable` in memory/mod.rs). Under the hardened
//! runtime the kernel kills a process that runs such code unless it has the
//! `com.apple.security.cs.allow-unsigned-executable-memory` entitlement; with
//! this provider the narrower `com.apple.security.cs.allow-jit` is enough
//! (stage N0's results, in the commit that added this file).
//!
//! The write permission is per thread: compile and finalize on one thread,
//! and don't run compiled code on that thread in between. Code may run on any
//! thread after `finalize`.

use std::io;

use cranelift_jit::{BranchProtection, JITMemoryKind, JITMemoryProvider, SystemMemoryProvider};
use cranelift_module::ModuleResult;

/// How much address space each `MAP_JIT` mapping reserves; a function bigger
/// than this gets a mapping of its own size.
const CHUNK: usize = 4 * 1024 * 1024;

// The declaration matches the C header's `void sys_icache_invalidate(void
// *start, size_t len)`.
#[allow(unsafe_code)]
unsafe extern "C" {
    /// From libSystem (`<libkern/OSCacheControl.h>`); not in the libc crate.
    fn sys_icache_invalidate(start: *mut libc::c_void, len: libc::size_t);
}

/// Code in `MAP_JIT` memory; data (which the spike doesn't use) in the
/// system provider's ordinary memory.
pub struct MapJitMemoryProvider {
    data: SystemMemoryProvider,
    /// Start and length of the current mapping, and how much is used.
    chunk: *mut u8,
    chunk_len: usize,
    used: usize,
    /// The code handed out since the last `finalize`.
    pending: Vec<(*mut u8, usize)>,
    /// Whether this thread has MAP_JIT memory writable now.
    writing: bool,
}

// SAFETY: the raw pointers are addresses of mappings this provider owns and
// never frees (as cranelift-jit's own provider leaks its memory, so function
// pointers stay valid); moving the provider to another thread moves nothing
// they point to. `JITModule` requires `Send`.
#[allow(unsafe_code)]
unsafe impl Send for MapJitMemoryProvider {}

impl MapJitMemoryProvider {
    /// A provider, or why `MAP_JIT` memory can't be had: under the hardened
    /// runtime, without the `com.apple.security.cs.allow-jit` entitlement,
    /// `mmap` refuses it.
    pub fn new() -> io::Result<Self> {
        let mut provider = MapJitMemoryProvider {
            data: SystemMemoryProvider::new(),
            chunk: std::ptr::null_mut(),
            chunk_len: 0,
            used: 0,
            pending: Vec::new(),
            writing: false,
        };
        provider.new_chunk(CHUNK)?;
        Ok(provider)
    }

    #[allow(unsafe_code)]
    fn new_chunk(&mut self, size: usize) -> io::Result<()> {
        let page = 16 * 1024;
        let len = size.div_ceil(page) * page;
        // SAFETY: a fresh anonymous mapping; no existing memory is affected.
        let pointer = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC,
                libc::MAP_PRIVATE | libc::MAP_ANON | libc::MAP_JIT,
                -1,
                0,
            )
        };
        if pointer == libc::MAP_FAILED {
            let error = io::Error::last_os_error();
            return Err(io::Error::new(
                error.kind(),
                format!(
                    "mapping MAP_JIT memory: {error} (a hardened-runtime build needs the \
                     com.apple.security.cs.allow-jit entitlement)"
                ),
            ));
        }
        self.chunk = pointer.cast();
        self.chunk_len = len;
        self.used = 0;
        Ok(())
    }

    #[allow(unsafe_code)]
    fn set_writing(&mut self, writing: bool) {
        if self.writing != writing {
            // SAFETY: only changes whether this thread may write (or
            // execute) MAP_JIT memory; no compiled code runs on this thread
            // while it's writable (the module's contract above).
            unsafe { libc::pthread_jit_write_protect_np(if writing { 0 } else { 1 }) };
            self.writing = writing;
        }
    }

    #[allow(unsafe_code)]
    fn allocate_code(&mut self, size: usize, align: u64) -> io::Result<*mut u8> {
        let align = usize::try_from(align).expect("alignment fits in usize");
        let start = self.used.next_multiple_of(align);
        if start + size > self.chunk_len {
            self.new_chunk(size.max(CHUNK))?;
            return self.allocate_code(size, align as u64);
        }
        self.used = start + size;
        self.set_writing(true);
        // SAFETY: `start + size` is within the mapping, checked above.
        let pointer = unsafe { self.chunk.add(start) };
        self.pending.push((pointer, size));
        Ok(pointer)
    }
}

impl JITMemoryProvider for MapJitMemoryProvider {
    fn allocate(&mut self, size: usize, align: u64, kind: JITMemoryKind) -> io::Result<*mut u8> {
        match kind {
            JITMemoryKind::Executable => self.allocate_code(size, align),
            other => self.data.allocate(size, align, other),
        }
    }

    #[allow(unsafe_code)]
    unsafe fn free_memory(&mut self) {
        // SAFETY: passed on from the caller. The MAP_JIT mappings are leaked,
        // as cranelift-jit's own provider leaks its memory.
        unsafe { self.data.free_memory() }
    }

    #[allow(unsafe_code)]
    fn finalize(&mut self, branch_protection: BranchProtection) -> ModuleResult<()> {
        self.data.finalize(branch_protection)?;
        self.set_writing(false);
        for (start, len) in self.pending.drain(..) {
            // SAFETY: the range is code this provider handed out.
            unsafe { sys_icache_invalidate(start.cast(), len) };
        }
        Ok(())
    }
}
