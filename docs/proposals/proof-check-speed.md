# Why the Day 2 and Day 4 proofs check slowly

*SW-163, 22 October 2026.* Measured on an M-series Mac, release build, with
other lanes running (load average 25 to 130), so times are the minimum of 8
runs and instruction counts (`/usr/bin/time -l`, "instructions retired",
which vary by under 0.1% between runs) are the steadier measure.

## Problem

`STITCHWORT_TIMINGS=1 stitchwort check --no-cache` in `aoc/` put
`Aoc.Day02.Proofs` (about 375 ms elaboration, 165 ms kernel, 437,000 core
term nodes) and `Aoc.Day04.Proofs` (340 ms, 135 ms, 230,000 nodes) at about
56% of all the time spent in units. Every other namespace takes under
120 ms. The question was what in them is slow, and what can be made faster
for every proof.

## Per-declaration timings

`STITCHWORT_TIMINGS` now prints a second table: declarations, slowest
first, by full name, with elaboration ms, kernel ms, evaluation steps and
core term nodes. A component of mutually recursive declarations is one row
(`Main.even, Main.odd`). Times are exclusive of library files loaded while
checking a declaration, as the unit table's are. It shows the 20 slowest;
`STITCHWORT_TIMINGS=decls` shows all. The hooks are in
`crates/elab/src/timings.rs` and around each component in
`elaborate_namespace` (`module.rs`); `crates/cli/tests/timings.rs` checks
names and ordering.

The slowest, before the changes below:

| declaration | elab ms | kernel ms | steps | nodes |
|---|---:|---:|---:|---:|
| `Aoc.Day02.Proofs.twiceTerms` | 120.0 | 44.1 | 2,950,848 | 148,682 |
| `Aoc.Day04.Proofs.passRow` | 56.3 | 17.7 | 1,275,341 | 30,313 |
| `Aoc.Day04.Proofs.mixStep` | 24.1 | 13.3 | 678,256 | 19,853 |
| `Aoc.Day04.Proofs.part2Correct` | 25.8 | 8.0 | 703,589 | 15,384 |
| `Aoc.Day04.Proofs.roundCount` | 16.4 | 10.4 | 596,810 | 26,607 |
| `Aoc.Day02.Proofs.dividesOfWritten` | 17.3 | 7.0 | 643,716 | 16,498 |

The time goes with the size of the elaborated terms: the slow declarations
are the big ones, and one declaration, `twiceTerms`, is a third of all the
nodes of Day 2's proofs.

## Causes

**1. Hidden arguments are solved to unfolded normal forms (the main
cause).** In Day 2 and Day 4's proofs, 81% of the core term nodes are
inside implicit arguments (537,018 of 666,491, counting each outermost
implicit argument's subtree; 76% across the whole AoC project, 44% in the
library and core). Example: `invalidCorrect` is written as

```
Eq.trans (Eq.cong (t => t - weighted minus r) (rangeSplit r)) (Nat.addSub …)
```

but elaborates to 20,759 nodes, because `Eq.trans`'s hidden `a`, `b`, `c`
are solved by unifying with the goal's *value*, and quoting a value gives
its normal form: `invalid r` comes back as the 7,648-node unfolding
`List.foldLeft (acc x => acc + List.foldLeft (… Decidable.elim … Nat.divFuel …))`.
The evaluator unfolds a definition as soon as it has its arguments and its
case tree can step (docs/core.md, "Unfolding policy"), and nothing remembers
the call it came from. Only dictionaries stay folded (`Def::fold`).

**2. A lifted `match`'s type is the normalised goal.** `twiceTerms` matches
on `Nat.leq (Succ k * 2) (Succ (Succ s))`. The helper `twiceTerms.%match1`
gets the goal at that point as its type, quoted from its value: 12,659
nodes, in which `repeatedSpec`, `twice` and `repeated` are unfolded. Its
body is 133,965 nodes, almost all implicit arguments of the `calc` steps
restating that goal.

**3. `Nat.pow 10 (Succ k)` unfolds into ten additions.** `Nat.pow b (Succ e)
= b * Nat.pow b e`, and multiplication recurses on its left argument, so a
literal base unfolds `10 * x` into `x + (x + …)`. About a third of
`%match1`'s type is these chains (594 occurrences of `Nat.pow 10 k + (`).
(The same trap `Nat.mod` avoids by putting the quotient on the left.)

**4. Every pass over a term costs its size, and lifting makes several.**
Sampled with macOS `sample` (1 ms) over 6 runs of checking just the two
namespaces (dependencies from the cache), inclusive shares:

| where | share |
|---|---:|
| kernel `define_group` (re-checking the big terms) | 28% |
| lifting (`resolve_batch`: captures, unrefine, parts) | 22% |
| `quote` (from zonking, the kernel's case refinement, rewrite contexts) | 21% |
| zonking (substituting solutions) | 14% |
| `calc` | 18% |
| freeing terms (`Term`'s drop) | 12% |
| malloc and free (the system allocator's own code) | about 20% (self time) |
| `effects::may_perform` | 5% |
| kernel `substitute` (case branches re-quote the whole context) | 6% |
| `rewrite` | 10% |

None of these is a mistake on its own; each walks or copies the big terms.
Zonking rebuilt every node of a term on every pass even where nothing
changed; lifting worked out each helper's type twice in a row; and
`may_perform`, asked at every level of a nested expression, re-applied each
called definition's type to fresh variables every time.

**5. The proofs themselves are fine, with one exception worth knowing.**
`twiceTerms` uses a `match` whose generalised goal mentions
`repeatedSpec r (Succ k) 2`; the `match` makes a helper whose type is that
goal unfolded. A top-level lemma with a written signature (as `E-MATCH-MOTIVE`'s
note suggests) would keep the type folded: likely most of its 148,682 nodes
would go. I didn't change it: it's what cause 1 makes expensive, and the fix
belongs there.

## What was changed

All in the elaborator and the command line; the kernel is untouched. The
elaborated terms are the same (same node counts and depths; `check_work`'s
`size` and `depth` are unchanged).

1. **Zonk shares what it doesn't change** (`unify::zonk_in`): unchanged
   subterms are returned as they are, as `refold` already did. Same steps;
   2.5% fewer instructions for the AoC project.
2. **Whether a definition's calls perform is remembered**
   (`effects::def_performs_after`, `Elaborator::performs`), for final
   definitions, keyed also by the number of abilities declared and whether a
   description's recursion is in scope (what `decode` reads). 3% fewer
   instructions; 13% fewer evaluation steps on the `check_work` programs.
3. **Lifting works out a helper's type once** (`resolve_batch`): the first
   computation (keeping the batch's metavariables) is reused when it has no
   metavariable left. 0.6% fewer instructions.
4. **`check` and `test` don't free the session before exiting**
   (`discard` in `crates/cli/src/main.rs`). 1.4% fewer instructions.
5. **The CLI uses mimalloc** as its global allocator: 28% fewer
   instructions (23.43 G → 16.84 G after changes 1–4), and less peak
   memory (104 MB, against 110–126 MB before). Only the `stitchwort`
   binary: the library crates, the web build and the benchmarks are
   unchanged.

### Before and after

`stitchwort check --no-cache` in `aoc/`, minimum of 8 interleaved runs:

| | before | after |
|---|---:|---:|
| `Aoc.Day02.Proofs` (elab + kernel) | 555 ms | 454 ms |
| `Aoc.Day04.Proofs` | 472 ms | 400 ms |
| all units | 1,572 ms | 1,286 ms |
| wall | 1,630 ms | 1,319 ms |
| instructions retired | 25.30 G | 16.84 G |
| cycles (3 runs each) | 6.21–6.33 G | 4.99–5.01 G |

The slowest declarations (minimum of 8 runs; nodes unchanged):

| declaration | ms before | ms after | steps before | steps after |
|---|---:|---:|---:|---:|
| `twiceTerms` | 162 | 131 | 2,950,848 | 2,934,637 |
| `passRow` | 74 | 61 | 1,275,341 | 1,215,049 |
| `mixStep` | 38 | 30 | 678,256 | 648,201 |
| `part2Correct` | 34 | 30 | 703,589 | 677,986 |
| `roundCount` | 27 | 23 | 596,810 | 589,908 |

`cargo test --release -p stitchwort-bench --test check_work`: every
program's steps drop by the same 157,327 + 989 (for example `print`:
1,178,181 → 1,019,865; visits 146,465 → 145,262), from changes 2 and 3
while loading the library. The differences the tests compare are unchanged
(`V cost` still computes 2,610,000 more steps at the larger input, `rfl`
2,088,000), as are sizes and depths.

## What's left

| Fix | Expected gain | Size and risk |
|---|---|---|
| **Keep calls folded** (glued values, or the cheaper "stay folded when the unfolding is stuck", docs/proposals/checker-evaluation.md §9.3): hidden arguments and helper types keep `invalid r` instead of its unfolding | Cause 1 is 81% of the nodes, and most of the profile above scales with nodes: a guess of 40–60% off these two namespaces | Large: the kernel's evaluator and conversion (and the elaborator's unifier and `rewrite`, which match on normal forms) must unfold folded calls on demand everywhere they look inside a value (numbers, `Pi`, `Eq`); a design note first |
| **`Nat.pow b (Succ e) = Nat.pow b e * b`** (cause 3) | About a third of `twiceTerms.%match1`'s type; less elsewhere | Small in the definition, but `std/Nat/Arith.sw` and `std/Nat/Digits.sw` proofs (`powAdd`, …) and the AoC proofs that use `pow` need restating: tried, and the library no longer checks without that |
| **Kernel case refinement re-quotes only what mentions the variable** (`check::substitute`) | Up to 6% here | Small, but in the kernel; a value has no cheap "mentions" test (closures capture the whole context), so it needs care |
| **`rewrite` builds the kernel context once per rewrite chain**, not per step (`kernel_context` quotes every context type) | Up to 2.5% | Small |
| **`twiceTerms` with a written helper lemma** instead of the `match` (cause 5) | Most of its 131 ms | A proof edit; only worth it if folding isn't done |

## Reproducing

```
cargo build --release -p stitchwort-cli
cd aoc
STITCHWORT_TIMINGS=1 ../target/release/stitchwort check --no-cache
STITCHWORT_TIMINGS=decls ../target/release/stitchwort check --no-cache   # every declaration
/usr/bin/time -l ../target/release/stitchwort check --no-cache          # instructions retired
```

Profiles: build with `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only` into
another target folder, then `sample <pid> 10 1 -file out.txt` while it runs,
and demangle with `llvm-cxxfilt` (`nix shell nixpkgs#llvm`).
