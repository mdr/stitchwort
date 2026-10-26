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

/// Everything that reaches the host's memory: constants in cells (a big
/// number, texts), operations off the fast paths, a `NumSwitch` with a big
/// entry, `Apply` sites (each with a cache), closures, and `Unpack` (which
/// traced counting does through the runtime).
const REACHES: &str = r#"import Std (IO, List, Text, Int)

def grow: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => grow n (acc * 3 + n)

def shrink: Nat → Nat
  | 0 => 100
  | 18446744073709551616 => 102
  | Succ n => n

def huge (n: Nat): Nat := n + 36893488147419103232

def sign: Int → Text
  | OfNat Zero => "zero"
  | OfNat (Succ n) => "+${n + 1}"
  | NegSucc n => "-${n + 1}"

def bump: List Nat → List Nat
  | [] => []
  | Cons x rest => Cons (x + 1) (bump rest)

def add (a: Nat) (b: Nat): Nat := a + b

def run (k: Nat): Text :=
  let xs := bump (List.map (List.range k) (x => x * k + 1))
  let total := List.foldLeft xs (huge (grow k 1)) add
  "${shrink total} ${shrink 18446744073709551616} " ++ sign (Int.OfNat k - Int.OfNat 100)

def main(): {IO} () :=
  IO.print (run 50)
"#;

/// The listing of `program`'s islands.
fn listed(program: &Program, image: &Image, trace_refcounts: bool) -> String {
    let options = Options {
        trace_refcounts,
        stack_size: Some(STACK),
    };
    listing(program, image, options).unwrap_or_else(|e| panic!("{e:#?}"))
}

#[test]
fn the_code_is_the_same_wherever_the_program_is() {
    with_stack(STACK, || {
        // Both kept alive, so the second is elsewhere in memory.
        let (one, _) = lowered(REACHES);
        let (other, _) = lowered(REACHES);
        let (one_image, other_image) = (code::compile(&one), code::compile(&other));
        assert_ne!(
            one_image.pool.as_ptr(),
            other_image.pool.as_ptr(),
            "the two images are at one address"
        );
        // Counting inline and through the runtime (which has its own
        // `Unpack`), as `run --native` and the trace tests compile.
        for trace in [false, true] {
            let first = listed(&one, &one_image, trace);
            let second = listed(&other, &other_image, trace);
            if first != second {
                let line = first
                    .lines()
                    .zip(second.lines())
                    .find(|(a, b)| a != b)
                    .map(|(a, b)| format!("{a}\n{b}"));
                panic!("the code differs between lowerings: {line:?}");
            }
        }
    });
}
