//! Generated programs over rows of abilities, checked for the order of their
//! operations.
//!
//! Each program uses a random subset of four abilities, listed in a random
//! order, and performs a random sequence of their operations, some through
//! helpers whose rows are smaller. The abilities are then handled in a random
//! nesting order by "relay" handlers, each of which logs its ability's number
//! to an outer `Log` and resumes. However the rows are arranged, the log must
//! be exactly the program's sequence of operations: so the generated
//! mappings, forwarding and handler reinstatement all have to be right.

use stitchwort_driver::driver::{Cache, Outcome, Session};

const ABILITIES: usize = 4;

const PRELUDE: &str = "
def fstOf : Pair a b -> a
  | MkPair x y => x

def sndOf : Pair a b -> b
  | MkPair x y => y

def eqNats : List Nat -> List Nat -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _,         _         => False

ability Log where
  say : Nat -> {Log} ()

def collect (prog : () -> {Log | e} a) : {e} Pair (List Nat) a :=
  handle prog () with
    | return x     => MkPair Nil x
    | say n, k     =>
      let rest := k ()
      MkPair (Cons n (fstOf rest)) (sndOf rest)
";

/// A small deterministic generator, so failures are reproducible.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 33) % n as u64) as usize
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            let j = self.below(i + 1);
            items.swap(i, j);
        }
    }
}

fn ability_decls() -> String {
    let mut out = String::new();
    for i in 0..ABILITIES {
        out.push_str(&format!(
            "\n\
             ability A{i} where\n  \
             op{i} : () -> {{A{i}}} ()\n\n\
             def relay{i} (prog : () -> {{A{i}, Log | e}} a) : {{Log | e}} a :=\n  \
             handle prog () with\n    \
             | return x => x\n    \
             | op{i} (), k =>\n      \
             say {i}\n      \
             k ()\n"
        ));
    }
    out
}

/// One generated program and the test checking its log.
fn program(rng: &mut Rng, n: usize) -> String {
    // The abilities used, in a random order for the row.
    let mut used: Vec<usize> = (0..ABILITIES).filter(|_| rng.below(3) != 0).collect();
    if used.is_empty() {
        used.push(rng.below(ABILITIES));
    }
    let mut written = used.clone();
    rng.shuffle(&mut written);
    let row = written
        .iter()
        .map(|i| format!("A{i}"))
        .collect::<Vec<_>>()
        .join(", ");

    // Helpers performing two of the abilities each, with their own rows.
    let mut out = String::new();
    let mut expected = Vec::new();
    let mut lines = Vec::new();
    for step in 0..(2 + rng.below(6)) {
        let a = used[rng.below(used.len())];
        if rng.below(3) == 0 && used.len() > 1 {
            let b = used[rng.below(used.len())];
            if b != a {
                let helper = format!("help{n}_{step}");
                out.push_str(&format!(
                    "\ndef {helper} () : {{A{b}, A{a}}} () :=\n  op{a} ()\n  op{b} ()\n"
                ));
                lines.push(format!("{helper} ()"));
                expected.extend([a, b]);
                continue;
            }
        }
        lines.push(format!("op{a} ()"));
        expected.push(a);
    }
    out.push_str(&format!("\ndef prog{n} () : {{{row}}} Nat :=\n"));
    for line in &lines {
        out.push_str(&format!("  {line}\n"));
    }
    out.push_str("  0\n");

    // Handle in a random order, innermost first.
    let mut order = used.clone();
    rng.shuffle(&mut order);
    let mut call = format!("prog{n}");
    for i in &order {
        call = format!("(u => relay{i} {call})");
    }
    let expected = expected
        .iter()
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    out.push_str(&format!(
        "\ntest \"generated {n}\" := eqNats (fstOf (collect {call})) [{expected}]\n"
    ));
    out
}

#[test]
fn generated_programs_log_their_operations_in_order() {
    let mut rng = Rng(0x5711_7c40_7e57_0001);
    let mut source = PRELUDE.to_string();
    source.push_str(&ability_decls());
    let programs = 40;
    for n in 0..programs {
        source.push_str(&program(&mut rng, n));
    }
    let mut session = Session::new();
    if let Err(diagnostics) = session.load("generated.sw", &source) {
        let shown: Vec<_> = diagnostics
            .iter()
            .map(|d| format!("{}: {}", d.code, d.message))
            .collect();
        panic!(
            "generated programs don't check:\n{}\n\n{source}",
            shown.join("\n")
        );
    }
    let results = session.run_tests(&Cache::disabled());
    assert_eq!(results.len(), programs);
    let failed: Vec<_> = results
        .iter()
        .filter(|r| r.outcome != Outcome::Passed)
        .map(|r| r.name.clone())
        .collect();
    assert!(failed.is_empty(), "failed: {failed:?}\n\n{source}");
}
