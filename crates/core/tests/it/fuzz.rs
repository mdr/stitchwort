//! The kernel must never panic: whatever term it's given, it either accepts it
//! or rejects it with a diagnostic. This feeds it thousands of random, mostly
//! ill-formed terms, generated from a seed so failures are reproducible. The
//! seed defaults to a fixed one; `FUZZ_CASES` and `FUZZ_SEED` (decimal or
//! `0x...`) change the count and the seed.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;

use crate::common::*;
use stitchwort_core::check::{self, infer_closed};
use stitchwort_core::term::Branch;
use stitchwort_core::{DataId, DefId, Icit, Sort, Term};

/// xorshift64*: tiny, deterministic, good enough for generating test cases.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn icit(&mut self) -> Icit {
        if self.below(4) == 0 {
            Icit::Implicit
        } else {
            Icit::Explicit
        }
    }
}

struct Gen<'p> {
    rng: Rng,
    p: &'p Prelude,
}

impl Gen<'_> {
    fn data(&mut self) -> DataId {
        // Occasionally an id that doesn't exist.
        [self.p.nat, self.p.list, DataId(9)][self.rng.below(3)]
    }

    fn term(&mut self, depth: usize, scope: usize) -> Term {
        let leaf = depth == 0 || self.rng.below(3) == 0;
        let choice = if leaf {
            self.rng.below(6)
        } else {
            6 + self.rng.below(11)
        };
        let sub =
            |g: &mut Self, extra: usize| Rc::new(g.term(depth.saturating_sub(1), scope + extra));
        match choice {
            // Usually in scope, sometimes not.
            0 => Term::Var(self.rng.below(scope + 2)),
            1 => Term::Def([self.p.add, DefId(42)][self.rng.below(2)]),
            2 => Term::Sort([Sort::Prop, Sort::Type(0), Sort::Type(1)][self.rng.below(3)]),
            3 => self.p.num(self.rng.below(3)),
            4 => Term::Refl,
            5 => Term::Meta(0),
            6 => {
                let d = self.data();
                let args = (0..self.rng.below(3))
                    .map(|_| self.term(depth - 1, scope))
                    .collect();
                Term::data(d, args)
            }
            7 => {
                let (d, c) = (self.data(), self.rng.below(3));
                let args = (0..self.rng.below(3))
                    .map(|_| Rc::new(self.term(depth - 1, scope)))
                    .collect();
                Term::Ctor(d, c, args)
            }
            8 => Term::Pi("x".into(), self.rng.icit(), sub(self, 0), sub(self, 1)),
            9 => Term::Lam("x".into(), self.rng.icit(), sub(self, 1)),
            10 | 11 => Term::App(sub(self, 0), sub(self, 0), self.rng.icit()),
            12 => Term::Ann(sub(self, 0), sub(self, 0)),
            13 => {
                let ty = if self.rng.below(2) == 0 {
                    Some(sub(self, 0))
                } else {
                    None
                };
                Term::Eq(ty, sub(self, 0), sub(self, 0))
            }
            14 => Term::J(sub(self, 0), sub(self, 0), sub(self, 0)),
            15 => Term::Let("x".into(), sub(self, 0), sub(self, 0), sub(self, 1), false),
            _ => {
                let (ix, d) = (self.rng.below(scope + 1), self.data());
                let branches: Vec<Branch> = (0..self.rng.below(3))
                    .map(|_| {
                        let k = self.rng.below(3);
                        Branch {
                            names: (0..k).map(|_| "y".into()).collect(),
                            body: Some(Rc::new(self.term(depth - 1, scope + k))),
                        }
                    })
                    .collect();
                Term::Case(ix, d, branches.into())
            }
        }
    }
}

const CASES: u64 = 3000;
const SEED: u64 = 0x5717_c4f0_1d5e_ed42;

/// An environment number, decimal or `0x...`; unset or empty is `None`, and an
/// unparsable one fails the run rather than silently using the default.
fn env_number(name: &str) -> Option<u64> {
    let value = std::env::var(name).ok().filter(|v| !v.is_empty())?;
    let parsed = match value.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16),
        None => value.parse(),
    };
    Some(parsed.unwrap_or_else(|_| panic!("{name}={value:?} is not a number")))
}

#[test]
fn the_kernel_never_panics_on_random_terms() {
    let cases = env_number("FUZZ_CASES").unwrap_or(CASES);
    let seed = env_number("FUZZ_SEED").unwrap_or(SEED);
    eprintln!("fuzz kernel: {cases} cases, seed {seed:#x}");
    let prelude = Prelude::new();
    let mut generator = Gen {
        rng: Rng(seed),
        p: &prelude,
    };
    let mut accepted = 0;
    for case in 0..cases {
        let state = generator.rng.0;
        let ty = generator.term(4, 0);
        let body = generator.term(4, 0);
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            let mut p = Prelude::new();
            let _ = infer_closed(&p.g.ev(), &body, span());
            let id = check::declare_def(
                &mut p.g,
                &"f".into(),
                &"f".into(),
                &ty,
                false,
                false,
                span(),
            )
            .ok()?;
            check::define_def(&mut p.g, id, &body).ok()
        }));
        match outcome {
            Ok(Some(())) => accepted += 1,
            Ok(None) => {}
            Err(_) => {
                panic!(
                    "case {case} (seed {seed:#x}, rng state {state:#x}): the kernel panicked on\n  type: {ty:?}\n  body: {body:?}"
                )
            }
        }
    }
    // Sanity check that the generator isn't only producing nonsense.
    assert!(accepted > 0, "no random definitions were accepted");
}
