# Comparative speed: Stitchwort against Python and Lean

**Status:** plan, 7 November 2026 (SW-2290, epic Comparative speed, D3330).
Read only: nothing was built, run or measured for it. The questions for
Matt are D3340 to D3342, [at the end](#8-questions-for-matt).

**Matt's goal (D3330).** For the same program, using the same algorithm,
Stitchwort should run at least as fast as Python and Lean, and check
equivalent proofs about as fast as Lean. "Performance is a key part of a
practical programming language. And being competitive with industry
languages is."

Claims are marked:
- **[source]**: read in this repository, with `file:line`;
- **[measured earlier]**: a number another note or the AoC notes recorded,
  with where;
- **[web]**: read on the web, with the link;
- **[inferred]**: my reasoning, not tested.

## Summary

**Where we stand, from numbers already in the notes.** On the four days
where someone also ran a Python script, `stitchwort run` is 20 to 50 times
slower than CPython, and native code 10 to 12 times slower:

| Day | `stitchwort run` | `--native` | `--js` | Python | Where |
|---|---:|---:|---:|---:|---|
| 2020 day 15 (30M `Map` turns) | 357 s | 84 s | 127 s | 7.2 s | `aoc/NOTES-2020.md:4041-4044` |
| 2020 day 17 (383k `insertWith`s) | 8.4 s | 3.0 s | 1.4 s | 0.24 s | `aoc/NOTES-2020.md:4769-4771` |
| 2020 day 19 (rule matcher) | 6.5 s (2.3 s after SW-1636) | 3.2 s | | 0.3 s | `aoc/NOTES-2020.md:5461` |

**[measured earlier]**, on this Mac, by different people at different
times; the Python scripts were independent cross-checks, not ports of the
same algorithm. So the real gap is unknown, and that is the first thing this
plan fixes. Nobody has timed Lean on any of them.

**The plan, in one paragraph.** Ten benchmark programs, eight of them AoC
days we've solved and two Benchmarks Game classics, each ported to Python
and to Lean 4 with the same algorithm and each language's usual data
structures. Three days' proofs ported to Lean for checking speed. A
`task bench:compare` script runs them all under hyperfine on Overmind, checks
that every language prints the same answers, and writes one table. The
headline comparison is **what a user runs by default**: `stitchwort run`
against `python3`, and Stitchwort's native executable against Lean's
compiled one. The other pairs are reported, not targeted.

**Stages.** 1: harness and ports (Sonnet, about 5 h over three lanes).
2: first measurement on Overmind and a report (about 1.5 h). 3: a ranked
list of where the gaps come from, tied to the interpreter-speed, in-place
reuse and `Map` plans (Opus, about 1 h).

## 1. Which backend faces which language

Stitchwort has three ways to run a program today **[source]**
(`crates/cli/src/main.rs:147-192`):

- **the machine** (`stitchwort run`): the bytecode interpreter, the
  default;
- **`--js`**: generated JavaScript run under Node (`:150-152`);
- **`--native`**: Cranelift code for what `main` reaches, JIT-compiled at
  start, "experimental", and only in a build with the `native` feature
  (`:158-161`), which is off by default (`crates/cli/Cargo.toml:30-32`).
  `stitchwort build --native` writes a fully native executable, and fails
  rather than fall back to the machine (`docs/proposals/native-only.md`,
  D1294).

Python users run `python3 prog.py`: CPython's bytecode interpreter. Lean
users who care about speed compile (`lake build`, then run the
executable); `lean --run` interprets the file's own code but calls the
compiled code of the core library, so it is a mix **[inferred, from Lean's
design: the IR interpreter calls native code for compiled declarations]**.

**Recommendation: two headline pairs, the rest reported.**

| Stitchwort | Against | Role | Why |
|---|---|---|---|
| `stitchwort run` (machine) | CPython `python3` | **headline, targeted** | Both are "run the source": what each language's users do by default. It is the experience Matt's goal is about. |
| `build --native` executable | compiled Lean (`lake build` exe) | **headline, targeted** | Both are "compile, then run": the speed each language offers when you ask for it. Lean is the nearest language to ours (pure, functional, reference counted, dependent types), so this pair says most about our compiler and runtime. |
| `stitchwort run` | `lean --run` | reported | Interpreter against interpreter, but Lean's is helped by compiled core code, so a win or loss here is hard to read. Cheap to collect, so collect it. |
| `build --native` | CPython | reported | A compiled program should beat CPython easily. Today it doesn't (10–12×, Summary), which is worth showing, but beating it isn't a goal worth stating. |
| `run --js` | (none) | reported | It's the playground's backend. Node isn't a language users compare us with; the column shows whether `--js` regresses. |
| `run --native` (JIT) | (none) | reported, until it's the default | JIT compile time is part of the run, so it sits between the two headlines. |

**The rule behind it: the target follows the default.** The Python target
attaches to *whatever `stitchwort run` does by default*. If native code
becomes the default for `run` one day, the Python comparison moves with it,
and nothing in the harness changes but a column's meaning. This answers
Matt's open question ("our interpreter against CPython, or our native
backend?"): the interpreter today, because that is what users get, and the
native backend the day it becomes what users get. See D3340.

**PyPy** (nixpkgs has 7.3.20) is worth one extra column, not a target: it
shows what a JIT gets on the same Python source **[inferred]**.

## 2. The benchmark programs

Ten programs: eight AoC days (all solved, with committed inputs and known
answers in `crates/cli/tests/running/aoc_answers.rs:19-86`) and two
classics. Each is chosen for a different kind of work. Times are today's
machine (`stitchwort run`) on this Mac unless marked.

| # | Name | Program | What it stresses | Today (machine / native / JS) |
|---|---|---|---|---|
| 1 | `dijkstra` | 2021 day 15 | graph search with a priority queue (`Set` as the queue, `Map` of costs), 250,000 positions | 17.6 s / 4.5 s / 2.9 s (`aoc/NOTES-2021.md:3802-3803`) |
| 2 | `memory-game` | 2020 day 15, part 2 cut to 3M turns | one huge `Map` with `Nat` keys, gets and inserts in a hot loop: the Python `dict` case | 357 s / 84 s / 127 s for 30M turns (`aoc/NOTES-2020.md:4041-4043`); about 36 s machine at 3M **[inferred, 11.9 s per million]** |
| 3 | `octopus` | 2021 day 11 | a grid in a `Map` of positions, neighbour updates, 100+ steps | 4.1 s / 1.3 s (`aoc/NOTES-2021.md:2738-2739`); 6.9 s in the bench crate's dev build (`bench/baseline.toml:249-256`) |
| 4 | `disk` | 2024 day 9 | array-style work: a long sequence of cells rewritten in place, so in-place reuse shows | 0.85 s (`aoc/NOTES-2024.md:2626`); 3.6M cells, 15.6% reused (`docs/proposals/interpreter-speed.md` §4.1) |
| 5 | `expressions` | 2020 day 18, input repeated 20 times | parsing with `Std.Parse` and evaluating expression trees: recursion over a small AST | 0.68 s / 0.81 s / 0.98 s on the real input (`aoc/NOTES-2020.md:5167`), mostly startup **[inferred]** |
| 6 | `scan` | 2024 day 3, input repeated 10 times | text scanning and the effect handlers under `findAll`: per-character work | 3.6 s at 10× (`aoc/NOTES-2024.md:546`); 15.8 s with `--js` (`:548`) |
| 7 | `matcher` | 2020 day 19 | closures and backtracking: a matcher built from a `Map` of rules | 2.3 s after SW-1636 (`aoc/NOTES-2020.md:5461`); Python 0.3 s on the old matcher |
| 8 | `bridge` | 2024 day 7 | plain recursion and arithmetic: try every operator sequence, numbers up to about 2^50 | 0.44–0.70 s (`aoc/NOTES-2024.md:1940`); scale the input if startup dominates |
| 9 | `pidigits` | Benchmarks Game classic, 10,000 digits | big numbers: multiply, add and divide `Nat`s of thousands of digits. No AoC day needs numbers past 64 bits, so this fills the gap | not run **[inferred: seconds, on `BigUint`]** |
| 10 | `binary-trees` | Benchmarks Game classic, depth 18 | allocation and freeing: build and walk many short-lived trees. Also in Lean's own suite | not run |

**Why these and not others.**
- They cover the brief's kinds of work: priority-queue search (1), heavy
  `Map`/`Set` use (1, 2, 3), parsing (5), strings (6), plain recursion and
  arithmetic (8), big numbers (9), arrays and grids (3, 4), plus closures
  (7) and allocation (10).
- Three of them (1, 3, 4) are already `run-machine-aoc-*` entries in the
  bench crate (`bench/baseline.toml:240-274`), so their instruction counts
  are tracked already.
- 2 is the case where Python's mutable `dict` and our persistent `Map`
  differ most. It must be in the set, because that's where users will
  notice. Cutting it to 3M turns keeps the run under a minute.
- The two classics come from the Benchmarks Game, so anyone can compare
  them with published numbers for other languages. Lean's benchmark suite
  has `binarytrees` too, and its CI tracks it ([lean4 PR bot
  reports](https://github.com/leanprover/lean4/pull/14950)) **[web]**.

**In reserve**, if one of the ten won't port cleanly:
- 2020 day 17 (`Set` of `List Int` keys; 8.4 s, Python 0.24 s);
- 2020 day 11 (a grid with views; 19.3 s / 3.7 s / 4.1 s,
  `aoc/NOTES-2020.md:2933-2934`);
- 2021 day 16 (bit parsing).

**Program sizes.** Each program should run at least 0.3 s in the fastest
language, so startup and noise don't decide it, and at most about 60 s in
the slowest. Inputs larger than the real one are made by a generator with
a fixed seed, or by repeating the real input. Each program's README says
which **[inferred: the bounds are a judgement]**.

**Stitchwort sources.** The AoC programs run as they are, from `aoc/`.
Only two need a small entry point:
- 2020 day 15 needs a turn count from `IO.args`;
- 2024 day 7, if it is scaled.

The classics are new `.sw` files under `bench/compare/`.

## 3. Checking-speed benchmarks

**The days.** Three days' proofs, chosen for different kinds of proof:

| Day | Proofs | What kind of checking | Today (`check --no-cache …Proofs`) |
|---|---|---|---|
| 2024 day 2 | 17 theorems, 303 lines with spec and tests **[source: counted]** | small list lemmas and `Nat` arithmetic, only `Std` (`Bool, Eq, List, Nat`) | 0.60 s (`aoc/NOTES-2024.md:418`) |
| 2020 day 18 | 49 theorems, 870 lines | a parser's correctness: `Std.Parse`, `Text`, `Char`, an evaluator over trees | 4.6 s (`aoc/NOTES-2020.md:5163`) |
| 2021 day 15 | 23 theorems, 505 lines, plus `Aoc.Common.Proofs` | Dijkstra's correctness over `Map` and `Set`, with grid lemmas from `Aoc.Common` | 3.7 s with tests (`aoc/NOTES-2021.md:3804`) |

Day 2 is the quick case, where fixed costs dominate. Day 18 is
parser-heavy, which is where our checks have been slowest. Day 15 leans on
the `Map`/`Set` lemma library. **2021 day 16** (65 theorems, 14.0 s,
`aoc/NOTES-2021.md:4168`) is the slowest check we have. It's the fourth
port if Matt wants the worst case measured, and I'd include it, since
ports are cheap.

**How to port fairly.**
- **The same statements and the same proof structure.** Each theorem
  states the same fact, about definitions written the same way: lists as
  lists, a `Map` as Lean's `Std.TreeMap`.
- **The same level of automation.** Where our proof calls a decision
  procedure (`omega`, `decide`), the Lean proof uses its own. Where ours is
  a chain of rewrites, the Lean proof is too (`rw`, `simp only [named
  lemmas]`), not a bare `simp` or `grind` that replaces twenty lines.
  Otherwise we'd be timing two different proofs. A second, idiomatic Lean
  port is allowed but reported separately.
- **Lean core and `Std` only, no Mathlib, no Batteries.** Our `Std` is
  closer to Lean's core library than to Mathlib. Loading Mathlib costs
  seconds of `.olean` mapping that would swamp these files. It also needs
  network fetches through Lake, which the Nix shell shouldn't do
  **[inferred]**.

**What to time.**
- **Cold day.** Lean: `lake env lean Day.lean` for each file, in
  dependency order, with only core's `.olean`s prebuilt. Stitchwort:
  `stitchwort check --no-cache` of the day's namespaces. Both check the
  day and its project dependencies from scratch. Both start with the
  standard library ready (Lean ships `Init`/`Std` compiled).
- **Library load, separately.** An empty file importing only what the day
  imports, in each language. That's "startup", reported in its own column
  and subtracted for the main ratio, as for run time (§4).
- **Warm (no change).** Both should be near zero (Lake sees fresh
  `.olean`s; our check cache hits). Record it once as a sanity check, not
  as a benchmark.
- **One edit.** Touch the last theorem of the day and recheck. This is
  what the editor does all day, so it's worth a row, and it shows whether
  our cache's granularity costs us **[inferred]**.
- **Optional:** kernel time alone, where both can report it (Lean:
  `set_option profiler true`; ours: the checker's own counters). This
  separates "our kernel is slow" from "our elaborator is slow".

## 4. Fairness rules

**Same algorithm, plain code, usual data structures.**
- Each port follows the Stitchwort program's algorithm step by step: the
  same search order, the same data structure *role* (a priority queue, a
  map from positions to costs), the same complexity.
- Each port uses what a competent programmer in that language would reach
  for: Python `dict`, `set`, `list`, `heapq`; Lean `Std.HashMap`,
  `Std.TreeMap`, `Array`. No tuned tricks: no `numpy`, no `@[specialize]`
  sprinkled for speed, no unsafe code.
- **Python's mutable `dict` against our persistent `Map`: compare them as
  they are.** The goal is about the same program in each language, and a
  Python programmer writes a `dict`. If the persistent tree is why we're
  slow, that's the finding, and the fix is ours: arrays with in-place
  update (`docs/proposals/arrays.md`, SW-112), a `Nat`-keyed map
  (`docs/proposals/nat-map.md`), in-place reuse. A "fair" Python with a
  hand-written persistent tree would measure a program nobody writes.
  Lean is the useful control here: its `Std.HashMap` is pure but updated
  in place when unshared, which is the design we'd aim for.
- Where the Stitchwort program uses a structure only because nothing
  better exists yet (a `Map` standing in for an array), the README says so.
  The port then uses the natural structure anyway.

**Startup counted separately.** For each language, a "null" program reads
the same input and prints a constant answer, and is timed the same way.
- The table shows total time, startup, and total minus startup. Ratios use
  total minus startup.
- Startup gets its own row in the report, because for short programs it is
  what users feel. Ours is about 0.2 s warm (2021 day 1, 0.22 s user,
  `aoc/NOTES-2021.md:485`); CPython's is tens of milliseconds
  **[inferred]**.
- `stitchwort run` is timed with a warm check cache, as users run it. The
  cache is warmed by one untimed run, which hyperfine's `--warmup` does.
  `--no-cache` is not timed: that's checking, covered in §3.
- `build --native` and `lake build` times are recorded once, in their own
  column, never in the run time.

**Input sizes, repeats and warmup.**
- One input per program, fixed and committed, or generated with a fixed
  seed.
- hyperfine with `--warmup 1` and at least `--runs 5` (3 for anything over
  30 s). Report the median and the spread (min to max).
- If the spread is over 5% of the median, the row is flagged and rerun, not
  averaged away.

**One quiet machine: Overmind.**
- The published numbers come from Overmind, Matt's NixOS laptop, about 2×
  slower than this Mac (AoC 134 s there, per the notes on it).
- On mains power, with no lanes, builds or tests running, and the
  performance governor set. The report records the commit, the tool
  versions and the load average.
- The Mac is fine for development runs, but its numbers are never mixed
  with Overmind's in one table.
- Every ratio is between two runs on the same machine in the same session,
  so the 2× doesn't matter to ratios **[inferred]**.

**Versions.** Everything comes from the flake's pinned nixpkgs. Today that
is Lean 4.35.0, CPython 3.14.8, PyPy 7.3.20 and hyperfine 2.0.0 **[source:
`nix eval nixpkgs#…version` on 7 Nov 2026]**. The report states them.
Python runs with default flags: no experimental JIT, no `-O`.
