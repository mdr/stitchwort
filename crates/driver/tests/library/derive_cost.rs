//! Guards the checker steps of what a data type with many constructors
//! derives (`==`, `<`, `${…}`, …): they grow about linearly with the number
//! of constructors, since the derived tests and orders compare positions
//! first and match only the first value (docs/proposals/derived-equality.md
//! §5.6, SW-3370). Matching both values, as they did before, made them
//! quadratic: 158 M steps for 94 constructors, against 39 M for 47.
//!
//! Each type is checked on its own, with the prelude's steps taken away.

use stitchwort_driver::driver::{Session, par_map};

const STACK: usize = 64 * 1024 * 1024;

/// A type of `count` constructors, as `fields` writes each: `K0 (m: Nat) | K1
/// | …`, or each with three fields of different kinds. (Not an enumeration:
/// its derived `Finite` is still quadratic.)
fn program(count: usize, fields: &dyn Fn(usize) -> String) -> String {
    let ctors: Vec<String> = (0..count)
        .map(|i| format!("  | K{i}{}", fields(i)))
        .collect();
    format!("type Node =\n{}\n", ctors.join("\n"))
}

/// The steps `program` takes to check.
fn steps(program: &str) -> u64 {
    let mut session = Session::for_stack(STACK);
    load(&mut session, "");
    load(&mut session, program)
}

/// Loads `text` into `session`: the steps it took.
fn load(session: &mut Session, text: &str) -> u64 {
    let before = session.elab.kernel.machine.budget.total_work();
    if let Err(ds) = session.load("derive_cost.sw", text) {
        let text: String = ds
            .iter()
            .map(|d| format!("{}: {}\n", d.code, d.message))
            .collect();
        panic!("the program doesn't check:\n{text}");
    }
    session.elab.kernel.machine.budget.total_work() - before
}

#[test]
fn derived_instances_grow_linearly_with_constructors() {
    let one = |i: usize| {
        if i == 0 {
            " (m: Nat)".to_string()
        } else {
            String::new()
        }
    };
    let three = |_: usize| " (a: Nat) (b: Text) (c: List Node)".to_string();
    let kinds: [(&str, &dyn Fn(usize) -> String); 2] =
        [("one field", &one), ("three fields each", &three)];
    let cases: Vec<(&str, usize, String)> = kinds
        .iter()
        .flat_map(|(name, fields)| [47, 94].map(|n| (*name, n, program(n, *fields))))
        .collect();
    let counts = par_map(STACK, &cases, |(_, _, text)| steps(text));
    let mut failures = Vec::new();
    for pair in cases.chunks(2).zip(counts.chunks(2)) {
        let ((name, ..), [half, full]) = (&pair.0[0], pair.1) else {
            unreachable!()
        };
        println!("{name}: 47 constructors {half} steps, 94 constructors {full}");
        // Linear doubles; quadratic quadruples. Allow some way between, for
        // the parts that are linear in the fields of every constructor.
        if *full * 10 > *half * 26 {
            failures.push(format!(
                "{name}: 94 constructors took {full} steps, {:.1} times 47's {half}",
                *full as f64 / *half as f64
            ));
        }
    }
    // 1.8 M steps after SW-3370 (158 M before), about 0.2 s.
    let full = counts[1];
    if full > 5_000_000 {
        failures.push(format!(
            "one field: 94 constructors took {full} steps, over 5 M"
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
