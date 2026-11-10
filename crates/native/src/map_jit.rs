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
//! thread after `finalize`. The provider records which thread it made
//! writable, and panics rather than write from another (SW-1124: it is
//! `Send`, since `JITModule` needs that, but the permission isn't).

use std::io;
use std::thread::{self, ThreadId};

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

// From libSystem (`<sys/codesign.h>`); not in the libc crate.
#[allow(unsafe_code)]
unsafe extern "C" {
    fn csops(
        pid: libc::pid_t,
        ops: libc::c_uint,
        useraddr: *mut libc::c_void,
        usersize: libc::size_t,
    ) -> libc::c_int;
}

const CS_OPS_STATUS: libc::c_uint = 0;
const CS_OPS_ENTITLEMENTS_BLOB: libc::c_uint = 7;
/// The hardened runtime is on for this process.
const CS_RUNTIME: u32 = 0x0001_0000;
const ALLOW_JIT: &[u8] = b"com.apple.security.cs.allow-jit";

/// Why this process can't JIT, if it can't: it runs under the hardened
/// runtime without the `com.apple.security.cs.allow-jit` entitlement. Asking
/// the kernel for the code-signing flags and entitlements costs two system
/// calls and doesn't depend on `mmap` refusing `MAP_JIT`: a hardened binary
/// without the entitlement can be given a `MAP_JIT` mapping all the same and
/// then dies with SIGTRAP at the first `pthread_jit_write_protect_np`.
/// Anything this can't read counts as allowed, so only a process that
/// positively lacks the entitlement is refused.
#[allow(unsafe_code)]
pub fn jit_unavailable() -> Option<String> {
    let pid = std::process::id() as libc::pid_t;
    let mut flags = 0u32;
    // SAFETY: `csops` writes at most `usersize` bytes to `useraddr`.
    let status = unsafe {
        csops(
            pid,
            CS_OPS_STATUS,
            (&raw mut flags).cast(),
            size_of::<u32>(),
        )
    };
    if status != 0 || flags & CS_RUNTIME == 0 {
        return None;
    }
    // The blob starts with a big-endian magic and length. Too small a
    // buffer fails with ERANGE, but still fills in that header.
    let mut blob = vec![0u8; 8];
    // SAFETY: as above, with `blob`'s length.
    let status = unsafe {
        csops(
            pid,
            CS_OPS_ENTITLEMENTS_BLOB,
            blob.as_mut_ptr().cast(),
            blob.len(),
        )
    };
    if status != 0 {
        match io::Error::last_os_error().raw_os_error() {
            Some(libc::ENOENT) => return Some(refusal()),
            Some(libc::ERANGE) => {}
            _ => return None,
        }
        let len = u32::from_be_bytes(blob[4..8].try_into().expect("four bytes")) as usize;
        if !(8..=1 << 20).contains(&len) {
            return None;
        }
        blob = vec![0u8; len];
        // SAFETY: as above.
        let status = unsafe {
            csops(
                pid,
                CS_OPS_ENTITLEMENTS_BLOB,
                blob.as_mut_ptr().cast(),
                blob.len(),
            )
        };
        if status != 0 {
            return None;
        }
    }
    (!grants_jit(&blob)).then(refusal)
}

fn refusal() -> String {
    "this `stitchwort` runs under the hardened runtime without the \
     com.apple.security.cs.allow-jit entitlement, which macOS needs for native code"
        .to_string()
}

/// Whether an entitlements plist sets `allow-jit` to true.
fn grants_jit(plist: &[u8]) -> bool {
    let Some(at) = plist.windows(ALLOW_JIT.len()).position(|w| w == ALLOW_JIT) else {
        return false;
    };
    let rest = &plist[at + ALLOW_JIT.len()..];
    let rest = rest.strip_prefix(b"</key>").unwrap_or(rest);
    rest.iter()
        .skip_while(|b| b.is_ascii_whitespace())
        .copied()
        .take(7)
        .eq(*b"<true/>")
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
    /// The thread this provider made MAP_JIT memory writable for, until
    /// the next `finalize`, if any.
    writing: Option<ThreadId>,
}

// SAFETY: the raw pointers are addresses of mappings this provider owns and
// never frees (as cranelift-jit's own provider leaks its memory, so function
// pointers stay valid); moving the provider to another thread moves nothing
// they point to. The write permission, which is the thread's and doesn't
// move, is tracked by `writing`: from any thread but the one it made
// writable, `set_writing` panics before anything is written, so a moved
// provider never writes through a thread that can't, nor leaves a
// thread's permission to the wrong caller. `JITModule` requires `Send`.
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
            writing: None,
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

    /// Makes MAP_JIT memory writable (and not executable) for this thread,
    /// or executable again. Panics if another thread has it writable: that
    /// thread's permission can't be changed from here.
    #[allow(unsafe_code)]
    fn set_writing(&mut self, writing: bool) {
        let here = thread::current().id();
        match self.writing {
            Some(owner) if owner != here => panic!(
                "MAP_JIT code memory made writable on one thread was used on another \
                 (compile and finalize on one thread)"
            ),
            Some(_) if writing => {}
            None if !writing => {}
            _ => {
                // SAFETY: only changes whether this thread may write (or
                // execute) MAP_JIT memory; no compiled code runs on this
                // thread while it's writable (the module's contract above).
                unsafe { libc::pthread_jit_write_protect_np(if writing { 0 } else { 1 }) };
                self.writing = writing.then_some(here);
            }
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

impl Drop for MapJitMemoryProvider {
    /// A compile that failed after writing code (the module dropped before
    /// `finalize`) leaves this thread's MAP_JIT memory executable again, so
    /// code compiled later runs on it. Dropped on another thread, it can't
    /// reach the writer's permission; that thread then faults if it runs
    /// MAP_JIT code (it never runs it silently writable).
    fn drop(&mut self) {
        if self.writing == Some(thread::current().id()) {
            self.set_writing(false);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allow_jit_must_be_present_and_true() {
        let plist = |value: &str| {
            format!("<dict><key>com.apple.security.cs.allow-jit</key>\n  {value}</dict>")
                .into_bytes()
        };
        assert!(grants_jit(&plist("<true/>")));
        assert!(!grants_jit(&plist("<false/>")));
        assert!(!grants_jit(
            b"<dict><key>com.apple.security.cs.disable-library-validation</key><true/></dict>"
        ));
    }

    /// The test binary isn't hardened, so it may JIT.
    #[test]
    fn an_unhardened_process_may_jit() {
        assert_eq!(jit_unavailable(), None);
    }
}
