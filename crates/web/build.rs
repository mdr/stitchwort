//! The WebAssembly stack lives in linear memory and its size is fixed when
//! the module is linked (Rust's default is 1 MiB). This sets it, and tells
//! the code the size so its resource limits match
//! (docs/proposals/stack-safe-evaluation.md).

/// Stack for the WebAssembly build.
const WASM_STACK: usize = 8 * 1024 * 1024;
/// How much of that stack an operation may use before it's stopped with a
/// resource error. Far less than the stack itself: each WebAssembly call also
/// uses the engine's own call stack, which overflows first, as a `RangeError`
/// the compiler can't recover from (the playground's worker is restarted).
/// Only variables whose address is taken live on the stack in linear memory,
/// so how much of it a recursion uses before the engine's stack runs out
/// depends on the recursion.
///
/// Measured in headless Chrome 157's dedicated workers, whose V8 stack is
/// about 500 KB (SW-3128; build with `STITCHWORT_STACK_PROBE` and
/// `web/stress.html` shows how deep each case got): with the guard lifted,
/// V8 overflowed at about 500-550 KiB of this stack in the term printer, at
/// 620-680 KiB in the evaluator (forcing the thunks of
/// `Aoc.Year2024.Day22`'s proofs, measured in Node set up to match) and at
/// 790-1050 KiB in the parser and elaborator. 320 KiB leaves a margin of
/// about 1.6 below the printer's figure and 2 below the evaluator's. Safari's
/// workers on macOS get the system's 512 KiB thread stack (WebKit's
/// `Thread::create` sets none), so probably about Chrome's room or a little
/// less (not measured); Firefox's have 2 MiB. 320 KiB checks the proofs of
/// all but two AoC days (256 KiB also failed 2021 days 6 and 11, and 2024
/// day 16; 384 KiB passes no more). The two left then needed more than a
/// safe guard allows: 2024 day 13 about 500 KiB, and day 22 about 2.3 MiB.
/// Since, their deepest recursions take less stack (SW-3132, SW-3133): a
/// native build, whose frames are larger, peaks at about 200 and 290 KiB
/// on them (not yet measured in the browser).
/// Set `STITCHWORT_GUARD` (bytes) to experiment.
/// The same bytes natively are less depth (larger frames): a native release
/// build needs about 1.5 times this to check `Float.Theory`
/// (docs/proposals/playground-editor.md, SW-1456).
const WASM_GUARD: usize = 320 * 1024;
/// Native builds of this crate only run as tests, on 2 MiB test threads.
const NATIVE_STACK: usize = 2 * 1024 * 1024;

fn main() {
    let wasm = std::env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("wasm32");
    let stack = if wasm {
        println!("cargo:rustc-link-arg=-zstack-size={WASM_STACK}");
        WASM_STACK
    } else {
        NATIVE_STACK
    };
    println!("cargo:rustc-env=STITCHWORT_STACK={stack}");
    // Empty means "the default for the stack size".
    let guard = match std::env::var("STITCHWORT_GUARD") {
        Ok(bytes) => bytes,
        Err(_) if wasm => WASM_GUARD.to_string(),
        Err(_) => String::new(),
    };
    println!("cargo:rustc-env=STITCHWORT_GUARD={guard}");
    println!("cargo:rerun-if-env-changed=STITCHWORT_GUARD");
    println!("cargo:rerun-if-changed=build.rs");
}
