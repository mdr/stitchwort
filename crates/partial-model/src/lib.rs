//! Stage 0 of the `Partial` proposal (`docs/proposals/partial.md`): a small,
//! standalone, executable model of stage 1's runtime semantics.
//!
//! It is independent of the kernel and the evaluator, and nothing in the
//! compiler uses it. Its job is to pin down the rules before they're built:
//! exact tick counts, the higher-order request translation's boundary,
//! suspended states, operation traces, stack behaviour, and where host
//! operations run.
//!
//! - [`delay`]: `Comp`, `Delay` and the five kernel constants.
//! - [`reference`]: the stepping equations, transcribed literally (the spec).
//! - [`machine`]: a stack-safe abstract machine implementing them.
//! - [`runner`]: the runner (performs operations, counts ticks, enforces
//!   policies) and a fuel observer used only for measurement.
//! - [`typed`]: the proposal's types on top, so `rustc` checks which programs
//!   the request translation can express.

pub mod delay;
pub mod machine;
pub mod reference;
pub mod runner;
pub mod typed;
pub mod val;
