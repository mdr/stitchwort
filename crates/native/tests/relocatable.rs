//! Stage S4 of docs/proposals/standalone-executables.md: the code generator
//! bakes no host address into the code, so the same code can go into an
//! object file and run in another process. The check: the Cranelift IR of
//! every function is the same text when the same program is lowered twice,
//! at other addresses (any address of the image, the program, an operation
//! or a cache would differ). `n1::listing` also runs the audit of every
//! integer constant against the host's objects, which every native test
//! runs in debug builds.

mod common;

use common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_native::n1::{Options, listing};
use stitchwort_rt::Program;
use stitchwort_rt::code::{self, Image};

/// Constants in cells (big numbers), operations off the fast paths, and a
/// `NumSwitch` with a big entry.
const BIG_NUMBERS: &str = r#"import Std (IO)

def grow: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => grow n (acc * 3 + n)

def isBig (n: Nat): Nat := if 18446744073709551615 <= n then 1 else 0

def shrink: Nat → Nat
  | 0 => 100
  | 1 => 101
  | 18446744073709551616 => 102
  | Succ n => n

def run (k: Nat): Nat := grow k 1 + isBig (grow k 1) + shrink (grow 2 0) + shrink 18446744073709551616

def main(): {IO} () :=
  IO.print "${run 50}"
"#;

/// The listing of `source`'s islands, lowered afresh, and the lowering
/// (kept alive by the caller, so that the next one is elsewhere in memory).
fn listed(source: &str, trace_refcounts: bool) -> (String, Box<(Program, Image)>) {
    let (program, _) = lowered(source);
    let image = code::compile(&program);
    let options = Options {
        trace_refcounts,
        stack_size: Some(STACK),
    };
    let text = listing(&program, &image, options).unwrap_or_else(|e| panic!("{e:#?}"));
    (text, Box::new((program, image)))
}

#[test]
fn the_code_is_the_same_wherever_the_program_is() {
    let sources = [
        BIG_NUMBERS.to_string(),
        bench("set_nat.sw"),
        bench("closures.sw"),
    ];
    with_stack(STACK, move || {
        for source in &sources {
            // Counting inline and through the runtime (which has its own
            // `Unpack`), as `run --native` and the trace tests compile.
            for trace in [false, true] {
                let (first, one) = listed(source, trace);
                let (second, other) = listed(source, trace);
                assert_ne!(
                    one.1.pool.as_ptr(),
                    other.1.pool.as_ptr(),
                    "the two images are at one address"
                );
                assert!(first.contains("function"), "nothing compiled: {first}");
                if first != second {
                    let line = first
                        .lines()
                        .zip(second.lines())
                        .find(|(a, b)| a != b)
                        .map(|(a, b)| format!("{a}\n{b}"));
                    panic!("the code differs between lowerings: {line:?}");
                }
            }
        }
    });
}
