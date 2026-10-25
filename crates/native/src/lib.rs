//! Native code for Stitchwort through Cranelift, JIT-compiled in-process
//! (docs/proposals/native-compilation.md, route (c)).
//!
//! Stage N0 is only a spike: hand-built functions that check Cranelift does
//! what the backend will need (`spike`), and the checks and measurements of
//! them (`checks`), which `stitchwort dev native-spike` prints.
//!
//! Cranelift is optional where it matters: the `stitchwort` binary takes this
//! crate only with its `native` feature, and the WebAssembly playground never
//! depends on it. Workspace builds (the test tiers) do build it, so its tests
//! run in the daily tier.

pub mod checks;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub mod map_jit;
pub mod spike;
