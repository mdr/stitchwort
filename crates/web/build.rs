//! The WebAssembly stack lives in linear memory and its size is fixed when
//! the module is linked (Rust's default is 1 MiB). This sets it, and tells
//! the code the size so its resource limits match
//! (docs/proposals/stack-safe-evaluation.md).

/// Stack for the WebAssembly build.
const WASM_STACK: usize = 8 * 1024 * 1024;
/// How much of that stack an operation may use before it's stopped with a
/// resource error. Far less than the stack itself: each WebAssembly call also
/// uses the engine's own call stack (about 1 MiB in V8), which overflows
/// first, as a `RangeError` the compiler can't recover from. Only variables
/// whose address is taken live on the stack in linear memory, so it grows
/// much more slowly. Measured in Node 22 (V8) once every recursive pass was
/// guarded: with a guard of up to 512 KiB, every deep case stopped cleanly;
/// from 640 KiB, elaborating a long sum (`1 + 1 + …`) overflowed V8's stack.
/// 128 KiB leaves a margin of 4 for engines with smaller stacks, but allows
/// little: nesting about 25 deep, list literals of about 200 elements. Check
/// with web/stress.html; set `STITCHWORT_GUARD` (bytes) to experiment.
const WASM_GUARD: usize = 128 * 1024;
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
