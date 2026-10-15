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
