//! Native code for Stitchwort through Cranelift, JIT-compiled in-process
//! (docs/proposals/native-compilation.md, route (c)).
//!
//! - Stage N0, a spike: hand-built functions that check Cranelift does what
//!   the backend needs (`spike`), and the checks and measurements of them
//!   (`checks`), which `stitchwort dev native-spike` prints.
//! - Stage N1 (`n1`): the machine's bytecode for whole reachable islands
//!   compiled to machine code, which `stitchwort run --native` runs.
//! - Stage S5 of standalone-executables.md (`aot`): the same code in an
//!   object file, which `stitchwort build --native` links into an
//!   executable.
//!
//! Cranelift is optional where it matters: the `stitchwort` binary takes this
//! crate only with its `native` feature, and the WebAssembly playground never
//! depends on it. Workspace builds (the test tiers) do build it, so its tests
//! run in the test tiers.

pub mod aot;
pub mod checks;
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
pub mod map_jit;
pub mod n1;
pub mod spike;
