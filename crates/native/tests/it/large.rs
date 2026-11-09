//! A body too big to compile the usual way (SW-2557): a long list literal,
//! each element a call and all of them held in registers until the list
//! is built. Keeping its registers in Cranelift variables made every error
//! exit write each one out, so its code grew with elements times calls (a
//! 20,000-element list took over 100 s and 18 GB before it was stopped).
//! It now has a register file and is compiled in parts.

use std::fmt::Write;

use crate::common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_rt::{Limits, alloc_trace};

/// `[step 0, step 1, ...]`, `n` elements, printed.
fn long_list(n: usize) -> String {
    let mut items = String::new();
    for i in 0..n {
        if i > 0 {
            items.push_str(", ");
        }
        let _ = write!(items, "step {i}");
    }
    format!(
        "import Std (List, Nat, Text)\n\n\
         def step (x: Nat): Nat := x * 7 + 3\n\n\
         def results: List Nat := [{items}]\n\n\
         def main(): {{IO}} () := IO.print (results |> List.map (n => n.toText) |> Text.join ',')\n"
    )
}

/// The number after `prefix` in the note on what ran natively.
fn noted(notes: &[String], prefix: &str) -> f64 {
    let note = notes.iter().find(|n| n.contains(prefix)).expect("the note");
    let rest = &note[note.find(prefix).expect("in the note") + prefix.len()..];
    let end = rest
        .find(|c: char| !c.is_ascii_digit() && c != '.')
        .unwrap_or(rest.len());
    rest[..end].parse().expect("a number")
}

#[test]
fn a_long_list_literal_compiles_quickly_in_small_frames() {
    with_stack(STACK, || {
        let (program, limits) = lowered(&long_list(1500));
        let machine = on_machine(&program, limits);
        let (native, notes) = native(&program, limits, false);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(native, machine);
        // Kept in variables, the body's frame grew with its registers
        // (11 KB at 300 elements) and its compile time with their square
        // (0.9 s at 300); now neither depends on the list's length.
        let frame = noted(&notes, "frames of at most ");
        assert!(frame < 8192.0, "{frame} bytes: {notes:#?}");
        let ms = noted(&notes, "compiled in ");
        assert!(ms < 20_000.0, "{ms} ms: {notes:#?}");
    });
}

#[test]
fn a_long_list_literal_stops_where_the_machine_does_and_frees_everything() {
    with_stack(STACK, || {
        let (program, limits) = lowered(&long_list(700));
        for steps in [1, 40, 350, 699] {
            let limits = Limits { steps, ..limits };
            let expected = on_machine(&program, limits);
            alloc_trace::start();
            let (ran, notes) = native(&program, limits, false);
            let trace = alloc_trace::finish();
            assert!(ran_natively(&notes), "{notes:#?}");
            assert_eq!(ran, expected, "at {steps} steps");
            assert_eq!(trace.leaks(), Vec::<u32>::new(), "leaked at {steps} steps");
        }
    });
}

#[test]
fn a_long_list_literal_makes_the_machines_allocation_trace() {
    same_trace(&long_list(700));
}
