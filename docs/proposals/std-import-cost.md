# What importing the standard library costs, and who pays it (SW-4593)

**Status:** note, 22 November 2026, Opus lane SW-4593. Measurement and options only; nothing
built. One decision is Matt's (§5, option F); the rest are the orchestrator's.

Marks: **[measured]** timed or counted today on `b5c31c0b0` (release build, Speedwell, load
9-14 from other lanes, so wall times are loose); **[estimated]** my reckoning from the
measurements; **[read]** read from the code or docs, not run.

## 1. In short

**The problem as filed.** SW-4587 found that the 43 new examples importing `Std.Parse` cost
3.58 G steps between them (about 83 M each), nearly all of it checking Parse's lemma files,
and the ticket assumed the examples suite checks each file without the check cache.

**What I found.**

- **The test suites already share one std check per build.** Since SW-1761 and SW-1765
  (7 Nov), the examples sweeps, `hash_stability` and most tests that make many sessions
  replay the library from the *test std cache* (`target/test-std-cache/{stack}`,
  `Session::use_test_std_cache`), in the lane, quick and broad tiers. The library is still
  checked from source once per build: the first test to need a file after a compiler or std
  change checks it and writes it, one process at a time (`TestCacheTurn`), and
  `Session::eager_for_stack` (first at top priority: `pinned_hashes`'
  `every_binding_by_hash_applies_to_the_library`) checks all of it. Only the all tier checks
  every example from source, on purpose, as a second guard. **[read]** Measured through the
  harness, three Parse examples (`EXAMPLES=walk-two-run,continuation-abstracting-accessor,reads-named-parser`,
  `accepted_examples_check`): **14.6 s** on the first run after the build, **0.94 s** on the
  second **[measured]**. So "warm one cache per run" exists already; there was nothing small
  to build.
- **SW-4587's 3.58 G is the `examples` benchmark**, which checks the library from source in
  every example's session on purpose: "from the library's source, so that the elaborator's
  work on the library is part of what it counts" (docs/testing.md, "Benchmarks"). Its own
  description in `crates/bench/src/programs.rs` ("as the example suite does") is out of date
  since 7 Nov. In a 20-file sample, **99.6% of declaration steps were core and library**
  **[measured]**; over the whole benchmark that is about **78% of its 16.5 G steps**
  **[estimated]** (the sample's mean library steps times 1,993 files; the rest is rejected
  examples' failed declarations and tests, which the declaration table doesn't show).
- **Theorem bodies are checked on import**, because a library file is the unit of loading,
  checking and caching (std-library.md §4.2): a program that uses one lemma of
  `Parse/Reads.sw` checks all 244 declarations in it. A program that uses only Parse's
  definitions doesn't load the lemma files at all (lazy loading works: a definitions-only
  parser checks in 2.4 s, against 8.0 s for `reads-named-parser`) **[measured]**. In six
  sampled files, theorems were **31% to 90%** of the library's steps **[measured]**, by name
  against std's `theorem` declarations.
- **Every session elaborates the core**, about 100 ms and 956,007 steps, cache or not: the
  cache holds library files only **[measured, read]**. In the test harness that is now the
  largest fixed cost of a small example.
- **Normal use is fine.** A plain `stitchwort check` keeps the library in the cache:
  `reads-named-parser` checks in **0.48 s** warm against **6.0 s** cold; the library's share
  goes from 5.4 s to 0.11 s **[measured]**.

**Recommendation.** Keep what is checked on import as it is. Do B (split the benchmark: the
library counted once, the examples replayed over it), and measure C (CLI tests that pass
`--no-cache`) before building anything there. D (core in the cache) is worth a design note of
its own. E and F are not worth it now; F is Matt's if he wants it.

## 2. Measurements

### 2.1 One Parse example, cold

`stitchwort check --no-cache --timings=all examples/accept/reads-named-parser.sw`
**[measured]**:

| part | elab ms | kernel ms | declarations |
|---|---:|---:|---:|
| core | 81.5 | 22.0 | 591 |
| `std/Parse/Reads.sw` | 3,692.6 | 668.0 | 244 |
| `std/Parse/ReadsChars.sw` | 1,025.6 | 121.1 | 105 |
| other 39 library files | 1,615 | 442 | 3,385 |
| the file itself | 82.0 | 2.5 | 31 |
| total | 6,496.7 | 1,256.1 | 4,356 |

Wall 8.0 s, 236 MB peak RSS. Library steps 73.4 M, the file's own 0.22 M. The slowest
declarations are all Parse lemmas the file doesn't name: `runFromLabelWholeFromOkTree` 1.93 s
(14.4 M steps), `runFromLabelFromOkTree` 0.37 s, `runFromAttemptFromOkTree` 0.32 s,
`runFromSectionLineFromOkTree` 0.28 s, `readsNatDigits` 0.24 s. They are helpers of the
user-facing lemmas in the same files (`readsLabel`, `readsOptional`, ...), so moving them to
a file of their own would not help: the lemmas a program uses need them.

Other Parse examples, cold **[measured]**:

| example | library ms (elab + kernel) | file ms | wall s | Parse files loaded |
|---|---:|---:|---:|---|
| `accept/walk` | 5,913 | 80 | 6.4 | Reads, ReadsOperators, Gives |
| `accept/reads-nested-binds` | 6,394 | 71 | 6.9 | Reads, ReadsChars |
| `accept/continuation-abstracting-accessor` | 9,994 | 72 | 10.5 | Reads, Runs, Follows |
| `accept/walk-two-run` | 10,525 | 115 | 11.1 | Reads, Runs, Follows |
| `reject/reads-nested-binds-unknown-field` | 6,028 | 10,438 | 16.9 | Reads, ReadsChars |
| a definitions-only parser (scratch) | 2,078 | 97 | 2.4 | none (Parse, Chars) |

### 2.2 The library's share across the examples

Every 100th file of `examples/{accept,reject,soundness,extract}` (20 files), cold, steps from
the declaration table **[measured]**: library and core 128.7 M, the files' own declarations
0.51 M (99.6%). The floor, a file importing nothing, is the core's 956,007 steps; the
commonest other figures were 5.98 M (a file that loads `Std.Omega` through `rewrite` or
`arithmetic`) and 20.5 M.

### 2.3 Theorem bodies' share of the library

The library rows of the same tables, split by whether the name is declared with `theorem`
in std (short names; a definition sharing a theorem's short name would be miscounted)
**[measured]**:

| example | library steps | of which theorems |
|---|---:|---:|
| `reads-named-parser` | 73.4 M | 90% |
| `named-arguments-effects` | 20.5 M | 74% |
| `nested-member` | 19.8 M | 73% |
| `group-hole-positions` (core only) | 0.96 M | 60% |
| `io` | 8.8 M | 51% |
| `absurd-distinct-constructors` | 5.98 M | 31% |

### 2.4 Cached, for comparison

`check --cache-dir <scratch>` on `reads-named-parser`, three runs **[measured]**: 6.02 s
(writes the cache), then 0.49 s and 0.48 s. Library files 107 ms replayed (5,377 ms
checked); core, the file and process start-up make up the rest. `--no-project-cache` gives
the same 0.48 s with the file checked afresh.

## 3. Who still pays the per-program library check

| who | cache | library checked | by design? |
|---|---|---|---|
| `stitchwort check`, `test`, `run`, the language server | per project or folder | once, then replayed | yes |
| examples sweeps, `hash_stability`, most driver tests (lane, quick, broad tiers) | test std cache, per build | once per build | yes (SW-1761, SW-1765) |
| the same in the all tier | none | per session | yes: the second guard beside `hash_stability`'s `prelude` |
| `examples` benchmark (`task bench`, all tier's `baseline`) | none | per example, 1,993 times | yes (docs/testing.md), but weighted by how often each file is imported |
| CLI tests that spawn `stitchwort ... --no-cache` | none | per spawn | partly: `project.rs` says "tests don't use the check cache"; 100 call sites in 30 files **[read]**; how many import much of std is not measured |
| `check --no-cache` (Overmind's rolling whole-AoC check, timing work) | none | per run | yes: `--no-cache` is the full check |
| every session | none for the core | core every time (~0.1 s) | nobody chose it; the cache was designed around library files |

## 4. What the tests prove, and where a wrong std proof is caught

Today a wrong proof in std fails (a) the test std cache's fill in every tier after the
change (the file is checked from source before it is written; `eager_for_stack` checks every
file), (b) `hash_stability`'s `prelude`, (c) the all tier's from-source examples, (d) any
`check --no-cache` that loads the file, and (e) `check --std`. Options B, C and D keep (a),
(b), (d) and (e). Only F removes (d), and changes what `--no-cache` means.

## 5. Options

**A. Share one std check per test run.** Built already (SW-1761, SW-1765). Nothing to do.

**B. The benchmark counts the library once.** Add a `std` benchmark that checks every library
file once from source (as `eager_from_source_for_stack` does), and have `examples` replay the
library from a cache filled in its unmeasured `prepare` step, into a fresh folder so that
the counts stay deterministic.
- Saving: `examples` from 16.5 G to about 3.5 G steps (the core's 1.9 G over 1,993 sessions
  plus the examples' own work), and its run from about 232 s to about 50 s; `std` adds about
  30 s once **[estimated]** (SW-4608 measured 23.8 s for the 72 library files `tools/fmt`
  loads).
- Trade-off: a regression in how the library elaborates shows once, in `std`, instead of
  multiplied by how many examples import the file. That multiplier is noise in the signal
  rather than information: SW-4587 had to separate new Parse importers from real growth by
  hand. Example-level regressions become visible instead of being 0.4% of the figure.
- Cost: a change to `crates/bench/src/programs.rs` and a re-recorded `bench/baseline.toml`
  on a quiet machine (a whole-bench run, which is the orchestrator's or Overmind's, not a
  lane's), and the docs/testing.md paragraph. Reversible; the orchestrator's call.

**C. CLI tests replay the library.** A hidden switch (an environment variable the CLI test
helpers set, say `STITCHWORT_TEST_STD_CACHE`) making `--no-cache` use a library-only test
cache (`Session::use_library_check_cache` with the test cache's grace), except in the all
tier and in tests of `--no-cache` itself. A spawned check importing Parse would go from about
6 s to 0.5 s **[measured on the CLI]**.
- First measure how much of the `cli` binaries' time is library checking (one timing pass of
  the broad tier's `cli` tests, by the verifier or Overmind); many of these tests check tiny
  programs whose floor is the core, where C saves nothing.
- Soundness: as A. The command's own behaviour under `--no-cache` must still be tested
  somewhere, which the excepted tests do.

**D. The core goes through the cache too** (or, in the test harness, each worker keeps a
session after the core and rewinds to it for each example, `Elaborator::mark` and `rewind`).
- Saving: about 0.1 s and 0.96 M steps per session **[measured]**: about 190 s of CPU per
  all-tier examples sweep and about 50 s at the quick tier's quarter sample, and 1.9 G of B's
  remaining 3.5 G **[estimated]**.
- Risks: the core registers natives, builtins and pins as it loads (`finish_core`), which a
  replay must reproduce; rewinding keeps counters (rewind.rs: "its counters ... stay as they
  are"), so generated names in messages could differ from a fresh session's and move
  snapshots. Needs its own note; not small.

**E. Load library declarations, not files.** Check only the declarations a program reaches,
with their dependencies, so `reads-named-parser` would not check `runFromLabelWholeFromOkTree`
unless a lemma it uses needs it.
- Saving: up to the unused part of each loaded file; for the Parse examples above perhaps a
  third to two thirds of a cold check **[estimated, loosely]**: the user-facing lemmas pull in
  most of the expensive helpers.
- Soundness: unchanged; everything used is still checked.
- Cost: large. The file is the unit of the name index's edges, the cache's entries and keys,
  instances, derived instances, data groups and generated equations (std-library.md §4.2
  chose files for this reason). Not worth it while the cache answers normal use in 0.1 s.

**F. Check statements only on import** (Matt's: it changes what is checked). A library
theorem a program uses is admitted from its statement, its body left to the library's own
check (§4 (a), (b), (e)), as Lean and Rocq trust a compiled library.
- Saving: the theorem share of §2.3, 31% to 90% of a cold check's library steps
  **[measured as a share; not built]**.
- Soundness: a wrong std proof no longer fails a program's `--no-cache` check; it fails the
  library's own checks, which run in every tier after a std change. `--no-cache` stops being
  "the full check" (cache/mod.rs's doc, `trusted.rs`'s test of the trusted base).
- Cost: content hashes include proofs (`def_hash`; `proofless_hash` leaves them out), so a
  program citing an unchecked theorem could not compute its own hashes without the
  theorem's hash from elsewhere (the cache, or a hash list shipped with std). Kernel-side
  admission of an unproved statement is new trusted code.
- Recommendation: **no**. The cache already gives what F would (bodies checked once, then
  trusted) with a check behind it; F would only help `--no-cache` runs, whose point is to
  check everything.

## 6. Recommendation

1. **B**, as a Sonnet lane, with the baseline re-recorded by the orchestrator on a quiet
   machine after merging.
2. **C**: measure first (a broad-tier timing pass of the `cli` binaries, outside a lane),
   then build only if library checking is a real share of it.
3. **D**: a design note (Opus) when the test suites' CPU is next looked at; the core is the
   largest fixed cost of a small example once the library is replayed.
4. **E**, **F**: no, for now.

No decision is needed from Matt unless he wants F; I recommend against it.
