//! The type checker computes only what it needs
//! (docs/proposals/checker-evaluation.md): checking a program whose types
//! don't need the value of a closed expression must not compute it. So the
//! deterministic counts (evaluation steps, recursive-pass visits) and the
//! size and depth of the elaborated program must be the same whatever the
//! size of that expression's input.

use stitchwort_bench::STACK;
use stitchwort_core::Term;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::render::render;

/// What checking one program took and made.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Measured {
    /// Evaluation steps (`Budget::total_work`).
    steps: u64,
    /// Levels of recursive passes (`Budget::total_visits`).
    visits: u64,
    /// Nodes in the program's elaborated definitions (types and bodies).
    size: usize,
    /// The deepest of them.
    depth: usize,
}

/// The number of nodes in `term`, and its depth.
fn size_and_depth(term: &Term) -> (usize, usize) {
    let (mut size, mut depth) = (0, 0);
    let mut pending = vec![(term, 1)];
    while let Some((t, d)) = pending.pop() {
        size += 1;
        depth = depth.max(d);
        t.for_each_child(|child, _| pending.push((child, d + 1)));
    }
    (size, depth)
}

/// Checks `program`, which must check, and measures it.
fn measure(program: String) -> Measured {
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        let g = &session.elab.globals;
        let (steps, visits) = (g.budget.total_work(), g.budget.total_visits());
        let defs = g.defs.len();
        if let Err(ds) = session.load("work.sw", &program) {
            let shown: String = ds
                .iter()
                .map(|d| render(&session.sources, d, false))
                .collect();
            panic!("{program}\ndidn't check:\n{shown}");
        }
        let g = &session.elab.globals;
        let (mut size, mut depth) = (0, 0);
        for def in &g.defs[defs..] {
            for term in std::iter::once(&def.ty).chain(def.body.as_deref()) {
                let (s, d) = size_and_depth(term);
                size += s;
                depth = depth.max(d);
            }
        }
        Measured {
            steps: g.budget.total_work() - steps,
            visits: g.budget.total_visits() - visits,
            size,
            depth,
        }
    })
}

/// `body`, after a definition `cost` whose value takes work proportional to
/// `n` to compute.
fn with_cost(n: usize, body: &str) -> String {
    format!("def cost : Nat := List.length (List.range {n})\n{body}\n")
}

/// Programs whose checking must not compute `cost`: the note's table, rows
/// 4–6 (operation calls and dot notation).
const CONSTANT: &[(&str, &str)] = &[
    ("print", "def main () : {IO} () := print (Nat.toText cost)"),
    (
        "two prints",
        "def main () : {IO} () :=\n  print (Nat.toText cost)\n  print (Nat.toText cost)",
    ),
    ("dot", "def x : Text := cost.toText"),
    ("dot, then an argument", "def x : Nat := cost.max 3"),
];

/// The same shapes where the type depends on the value: they must still
/// check, computing it.
const NEEDED: &[(&str, &str)] = &[
    (
        "an operation whose result type depends on its argument",
        "def T : Nat -> Type\n  | 0 => Nat\n  | _ => Text\n\n\
         ability Dep where\n  fetch : (n : Nat) -> {Dep} T n\n\n\
         def f () : {Dep} Text := fetch (cost + 1)",
    ),
    (
        "dot notation whose result type depends on the receiver",
        "type Box = { n : Nat }\n\ndef Box.same (b : Box) : b = b := rfl\n\n\
         def box : Box := { n = cost }\n\ndef p : box = box := box.same",
    ),
];

/// Measures each program with `cost` over 2,000 and 20,000 elements.
fn measured(cases: &[(&'static str, &str)]) -> Vec<(&'static str, Measured, Measured)> {
    cases
        .iter()
        .map(|(name, body)| {
            let small = measure(with_cost(2_000, body));
            let large = measure(with_cost(20_000, body));
            println!("{name}: {small:?} / {large:?}");
            (*name, small, large)
        })
        .collect()
}

#[test]
fn checking_does_not_compute_unneeded_values() {
    let grew: Vec<String> = measured(CONSTANT)
        .into_iter()
        .filter(|(_, small, large)| small != large)
        .map(|(name, small, large)| format!("{name}: {small:?} became {large:?}"))
        .collect();
    assert!(
        grew.is_empty(),
        "checking grew with the input:\n{}",
        grew.join("\n")
    );
}

/// Where the type needs the value, it's computed as before.
#[test]
fn checking_computes_needed_values() {
    for (name, small, large) in measured(NEEDED) {
        assert!(
            large.steps > small.steps,
            "{name}: expected checking to compute `cost`"
        );
    }
}
