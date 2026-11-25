# What small proofs spend their checking time on (SW-4809)

**Status:** Opus lane SW-4809, 25 November 2026, 12:26-13:00, for D3743 ("Yes, profiling sounds
very sensible before we attempt optimizations"). Measurement only: no checker code changed.
Small raw data and the scripts are in [`SW-4809/`](SW-4809/). It follows
[SW-4608](SW-4608-proof-checking-speed.md) and its 25 Nov rerun (SW-4806).

Marks: **[measured]** timed or counted today; **[estimated]** my judgement from the measurements;
**[inferred]** read from the code, not timed.

## In plain words

**The question.** On three small AoC days the bench says the days' own theorems take 3.2x,
5.4x and 3.1x Lean's time once loading is subtracted. What do our small proofs spend that time
on?

**The answer: mostly not on the proofs.** When the days' own namespaces are timed on their own,
their elaboration plus kernel time is **104-124 ms, 117-123 ms and 458-496 ms**, against Lean's
93, 200 and 495 ms for the whole ported file: **1.1-1.3x, 0.6x and 0.9-1.0x** Lean
**[measured]**. The 17, 23 and 41 ported theorems alone take 86, 35 and 180 ms. On small,
ordinary proofs we are about level with Lean, not 3-5x behind.

**Where the bench's gap comes from** **[measured]**:

1. **The bench's "load" probe doesn't load all the library the day uses.** "sw net" is a
   cold check of the day minus a cold check of a probe file that imports the day's std
   modules. On day 18 the day also checks `std/Parse/ReadsChars.sw` and `RunsChars.sw`, which
   the probe never touches: **975 ms** of library proofs land in "sw net", against 123 ms for
   the day itself. On day 15, 16 std files the probe misses add **800 ms**. Day 2's probe is
   complete, and its ratio is the honest one.
2. **Each check has fixed costs that Lean doesn't have, a few hundred ms whatever the proofs
   are.** Every run parses all 133 std files (3.4 MB) to build the library's name index,
   **216-254 ms**. A project check also parses all 633 files of `aoc/` (3.0 MB) to find its
   namespaces, **175-207 ms**, whichever day is asked for. It re-elaborates the core prelude
   (585 declarations), **about 95 ms**. And it loads library entries from the cache, 150-430
   ms. Lean's whole start-up, with its library, is 262 ms, because it memory-maps precompiled
   `.olean` images (cited in section 3). The project scan is the part that lands in "sw net".
3. **The bench measures a dev build.** `task bench:compare:proofs` builds with the dev
   features, which turn on core's `reference` feature. That runs a debug check
   (`reference::validate_marks`: the kernel type-checks every declaration's type again) on
   every declaration installed, library cache loads included. It is **264 ms (23%) of a
   library-cached day 18 run**. The binary people run is 12-25% faster on library-cached
   checks (day 18 706 against 944 ms) **[measured]**. `docs/testing.md` says `reference`
   "made no difference (under 1%)". That is now wrong.

**What the proofs' own time is made of** (the days' own declarations, profiled): allocation
and copying of values 31-36% of self time, evaluation 17-20%, and read-back, unification and
kernel conversion a few percent each by self time. By inclusive time, evaluation is 27-37%,
read-back 17-28%, the kernel's check 19-24%, and `match` elaboration (`generalised_now`)
6-56% **[measured]**. Data declarations are a surprise on day 18: 43% of its own time,
including 20% deriving equality, about 40 ms. `matching::blocker`, SW-4612's target, is under
0.1% **[measured]**.

**So the gap is fixed overhead per run and per project, not per step.** The biggest wins on
these days are the library index (about 230 ms a run) and the project scan (about 190 ms a
run on `aoc/`). Both are paid by every `check`, however small the edit. Making evaluation
cheaper (SW-4650) would save perhaps 10-50 ms a day here **[estimated]**. It is worth doing for
big proofs, but it doesn't close this gap. With the index and the scan gone, a day's whole
library-cached check would be about 0.25-0.6 s against Lean's 0.36-0.76 s for the file
**[estimated]**.

## 1. Method

- **Machine:** Speedwell, M1 Pro, 10 cores, quiet: the 5-minute load was 3.4-5.2 at the start
  of every timed part (`uptime` before each), no other lanes.
- **Builds:** `lane/SW-4809` at `45d6184e0`. Profiling binary: `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only
  cargo build --release -p stitchwort-cli --features stitchwort-cli/dev --target-dir target/prof`
  (the bench's feature set, with symbols). "Plain": the worktree's `target/release/stitchwort`,
  built without the dev features (`nm` finds no `validate_marks` in it).
- **The days' theorems:** the bench's own list (`bench/compare/proofs.py`'s `ported_theorems`,
  reproduced in a few lines): 17, 23 and 41 theorems.
- **Library cached, own namespaces afresh:** from `aoc/`, after a warming `check` of the
  days, `STITCHWORT_JOBS=1 STITCHWORT_STEP_PHASES=1 check --no-project-cache --timings=all
  <namespaces> --only <theorems>`. (`--only` and `--no-project-cache` both force one job.)
- **The bench's shape:** `check --no-cache <namespaces> --only <theorems>` and `check
  --no-cache load-<day>.sw` with the bench's probe files, once with `--timings=all` and
  `STITCHWORT_STEP_PHASES=1`, and with hyperfine 2.0.0 (`-N --warmup 1`, 3 runs; 5 runs for the
  cached runs) for both binaries.
- **Profiles:** `samply record --save-only --unstable-presymbolicate -r 4000` (samply 0.13.1,
  nixpkgs), with `STITCHWORT_JOBS=1`, of the library-cached day runs, the day 2 probe and a
  fully cached day 2 run. They were summarised by [`group.py`](SW-4809/group.py) (run phases
  and self-time groups), [`subset.py`](SW-4809/subset.py) (only stacks under
  `check_project_namespace` and `check_component`, the days' own declarations) and
  [`tree.py`](SW-4809/tree.py) (the children of a frame). All three are built on SW-4608's
  `samply_summary.py`. One sample is 0.25 ms. The profiles themselves aren't kept.
- **Lean:** the "lean net" figures are SW-4806's from this morning (same machine, Lean 4.34.1,
  load 3.8). I did not rerun Lean.

## 2. The numbers

### 2.1 What "sw net" is made of (the bench's shape, dev binary)

| | 2024 day 2 | 2020 day 18 | 2021 day 15 |
|---|---:|---:|---:|
| sw check, `--no-cache --only`, hyperfine median | 2,338 ms | 8,516 ms | 5,445 ms |
| sw load (the probe), `--no-cache` | 2,072 ms | 7,490 ms | 4,187 ms |
| **sw net** | **266 ms** | **1,026 ms** | **1,258 ms** |
| SW-4806's sw net, for comparison | 293 ms | 1,080 ms | 1,550 ms |
| *from the `--timings` runs, one each:* | | | |
| std files the day checks and the probe doesn't | none | **975 ms** (`Parse/ReadsChars` 619, `Parse/RunsChars` 356) | **800 ms** (16 files: `Parse/Parse` 151, `Nat/Bits` 149, `Int/Lemmas` 144, …) |
| the day's own namespaces, elab + kernel | 104 ms | 123 ms | 458 ms |
| "outside the units" (parsing, core load, printing), day minus probe | +153 ms | +204 ms | +185 ms |
| Lean net (SW-4806) | 93 ms | 200 ms | 495 ms |
| sw net / lean net, as the bench reports it | 2.9x | 5.1x | 2.5x |
| **own namespaces / lean net** | **1.1x** | **0.6x** | **0.9x** |

All **[measured]**. The `--timings` runs are single runs, so their parts don't add exactly to
the hyperfine net. The plain binary gives nearly the same no-cache nets (225, 1,077 and
1,249 ms): with nothing cached, `validate_marks` is a small share of elaboration.

### 2.2 A library-cached run, phase by phase (profile, dev binary, ms)

| phase | probe (day 2) | day 2 | day 18 | day 15 |
|---|---:|---:|---:|---:|
| whole run, under the profiler | 490 | 812 | 1,158 | 1,348 |
| std index: `LibraryIndex::build` parses every std file and resolves its names | 231 | 227 | 254 | 216 |
| project scan: `project::analyse` (parses all 633 `aoc/` files, 2/3; finds the edges, 1/3) | - | 153 | 173 | 160 |
| project sources (reading the files) | - | 22 | 34 | 35 |
| library entries loaded from the cache (`load_needs`) | 148 | 149 | 431 | 301 |
| …of which `validate_marks` (dev builds only) | | | 264 | |
| core prelude elaborated (585 declarations) | 94 | 96 | ~114 | ~115 |
| **the day's own declarations** (`check_project_namespace` › `check_component`) | - | **121** | **100** | **416** |
| other | 17 | 44 | 52 | 105 |

All **[measured]**. Wall times without the profiler (hyperfine median, 5 runs) **[measured]**:

| | day 2 | day 18 | day 15 |
|---|---:|---:|---:|
| day, library cached, dev binary | 744 ms | 944 ms | 1,173 ms |
| probe, cached, dev binary | 465 ms | 640 ms | 547 ms |
| day, library cached, plain binary | **656 ms** | **706 ms** | **1,034 ms** |
| probe, cached, plain binary | 392 ms | 443 ms | 428 ms |
| Lean, the whole file (SW-4806) | 355 ms | 462 ms | 757 ms |
| plain day / Lean file | 1.8x | 1.5x | 1.4x |
| day 2, everything cached (project too), dev | 625 ms | | |

A fully cached day 2 check, with nothing to elaborate, still takes 625 ms. That is the fixed
cost: the index, the scan, core and the cache load.

### 2.3 The days' own declarations

From the `--timings` declaration rows of the library-cached runs **[measured]**
([`decls-*.txt`](SW-4809/)):

| | day 2 | day 18 | day 15 |
|---|---:|---:|---:|
| ported theorems: count, elab + kernel | 17, **86 ms** | 23, **35 ms** | 41, **180 ms** |
| other own declarations (program, spec, data, helpers) | 21, 11 ms | 42, 42 ms | 211, 222 ms |
| units' total less the rows (per-namespace work outside declarations) | 27 ms | 39 ms | 94 ms |
| median declaration | 0.50 ms | 0.30 ms | 0.30 ms |
| slowest | `passesDampenedAfterCorrect` 22.7 ms | data `Expression` 19.5 ms | `tiledLevelsAgree` 53.7 ms |
| read-back share of the ported theorems' steps | 39% | 24% | 38% |
| ported theorems' term nodes | 14.6 k | 9.4 k | 30.9 k |

The profile of those declarations alone ([`profile-own-decls-*.txt`](SW-4809/)) **[measured]**:

| group (self time) | day 2 | day 18 | day 15 |
|---|---:|---:|---:|
| allocation, free, drop, clone, copies (`mi_*`, `drop_glue`, `Value::clone`, `Rc<[Value]>` and `Vec<Value>` building, memmove) | 31% | 33% | 36% |
| evaluation (`value::run_on`, `resume`, `eval`, `visit`, `force`) | 21% | 17% | 19% |
| unification | 5% | 5% | 3% |
| kernel conversion | 5% | 2% | 5% |
| read-back (`quote_as_until`, `detach`) | 3% | 4% | 2% |
| hashing | 2% | 2% | 2% |
| cache I/O, diagnostics, parsing | under 1% | under 1% | under 1% |
| other (the elaborator's own code, term walks such as `Term::for_each_child`) | 35% | 37% | 32% |

| inclusive | day 2 | day 18 | day 15 |
|---|---:|---:|---:|
| evaluation (`value::run_on`) | 33% | 27% | 37% |
| read-back (`quote_as_until`) | 28% | 17% | 20% |
| kernel check (`core::check::check`) | 19% | 24% | 24% |
| conversion | 25% | 14% | 18% |
| unification | 9% | 19% | 15% |
| `match` elaboration (`matching::generalised_now`) | 56% | 6% | 17% |
| `rewrite` | 35% | 6% | 14% |
| data declarations (`data_group`) | 4% | **43%** | 26% |
| …deriving their equality (`derive_data_eq`) | 2% | 20% | 12% |
| `arithmetic` (omega) | 5% | 4% | 8% |
| `validate_marks` (dev only) | 3% | 3% | 4% |
| `matching::blocker` (SW-4612) | 0% | 0% | 0.1% |

## 3. Against Lean, theorem by theorem

What the Lean files do differently **[inferred from the files, unless marked]**:

- **Loading.** `lean Proofs/Day.lean` imports `Lib` and Lean's `Init`, both precompiled.
  Lean reads a module as a compacted region: `readModuleData (fname) : IO (ModuleData ×
  CompactedRegion)` in `src/Lean/Environment.lean`, whose `EnvironmentHeader.regions` doc says
  "Objects in compacted memory regions do no require any memory management", and
  `saveModuleDataParts` picks "an arbitrary but deterministic base address for `mmap`"
  (leanprover/lean4 `master`, read today). So Lean pays nothing per declaration of its library
  at start-up. We parse every std file for the index, elaborate core, and decode and install
  each library entry we need from the cache **[measured, section 2.2]**. Lean does no work for
  the rest of a project either: `lean` gets one file. Our project check parses all of `aoc/`.
- **Proof style.** The Lean ports close goals with `simp`, `omega`, `cases … <;>` and `decide`,
  where ours use `cases`, `rewrite … then cases`, `byComputing` and explicit `match` arms.
  Lean's automation is usually the costly part of a Lean file, and it is in Lean's 93-495 ms.
  Our explicit arms show up as `match` elaboration (56% of day 2's own time) and read-back of
  goals (24-39% of the theorems' steps). I didn't time Lean per theorem (`set_option profiler
  true` would). So "per theorem we are level" holds for each file's total, not for each
  theorem **[measured totals; per-theorem split not measured]**.
- **What each side checks.** Lean's files define cut-down programs and specs with no parser:
  day 2's port says "The parser is left out", and day 18's leaves out 26 theorems about
  `Std.Parse`. Ours checks the program namespaces too, parser included (`Day02` 27 ms,
  `Aoc.Common` and the day 15 program 222 ms of other declarations). That leans against us,
  and we are still level.
- **Data types.** Day 18's `Expression` costs us 19.5 ms, with a read-back of 10,001 nodes,
  and its data declarations 43% of the day's own time. Lean derives `DecidableEq, BEq` only for
  `Operator`. We derive equality for every data type **[inferred: `derive_data_eq` runs under
  each `data_group`]**.
- **Sharing.** None of these days reads back a large term: the largest read-back of a ported
  theorem is 4,927 nodes (day 15's `tiledLevelsAgree`). The read-back sharing problem SW-4608
  found in the formatter doesn't arise here **[measured]**.

## 4. Candidate changes, ranked

| # | what | evidence | estimated saving on these days | risk | proposed ticket |
|---|---|---|---|---|---|
| 1 | **Fix the bench.** Make the probe load every std file the day's check loads, or take "sw net" from the day's own units in `--timings`. Build without the dev features. Report the library-cached whole-file ratio beside "net". | §2.1: 975 and 800 ms of library proofs counted as the days' own; §2.2: dev build 12-25% slower than plain | none in the checker; the reported gap goes from 2.5-5.1x to 0.6-1.1x net, 1.4-1.8x whole-file **[measured]** | none: a measurement | "bench:compare:proofs: probe misses std files the days use (975 ms of day 18's net); build without dev features" (sonnet), small |
| 2 | **Don't rebuild the std index every run.** Store it in the check cache, keyed on the std files' hashes, or index only the files a check reaches. | `LibraryIndex::build` 216-254 ms of every run, 47% of a cached probe; it parses all 133 files | **~200 ms a check**, every `check` of anything, cached or not **[estimated]**; probably `run` and `test` too **[inferred]** | medium: the index decides name resolution and dot calls; must give the same answers; no kernel change | "Cache the standard library's name index (230 ms of every check)" (opus), medium |
| 3 | **Don't parse the whole project to check one namespace.** Cache each file's analysis (namespace, declared names, imports) by content hash, or read only headers until a namespace is needed. | `project::analyse` + sources 175-207 ms of every `aoc/` check, for 633 files; grows with the project | **~150-190 ms a check on `aoc/`** **[estimated]**; more on bigger projects | low-medium: a parse error in an unrelated file is then reported differently or not at all, which is a behaviour question | "Project checks: stop parsing every file of the project (190 ms of each aoc check)" (sonnet), medium |
| 4 | **Cache the core prelude** like a library file, instead of elaborating its 585 declarations every run. | ~95 ms in every profile, and the 444 `Std.*` rows that every cached run re-elaborates | ~90 ms a check **[estimated]** | medium: core is the trusted base; its cache entry must be replayed as library entries are | "Load the core prelude from the check cache (95 ms of every check)" (opus), medium |
| 5 | **`reference::validate_marks` on trusted replays.** Skip it for entries replayed from the cache, or keep it only in tests. Correct `docs/testing.md`'s "under 1%". | 264 ms of 1,158 (23%) of a cached day 18 dev run; 3-4% of own elaboration | 12-25% of every library-cached dev-build check: tests, benches, `task build` **[measured]**; nothing in shipped binaries | low: a debug check; removing it from replays loses a check of cache contents in dev builds | "Dev builds: validate_marks costs 23% of a cached check (not the 'under 1%' docs/testing.md says)" (sonnet), small |
| 6 | **Data declarations.** Find why `Expression` reads back 10,001 nodes and costs 19.5 ms, and whether deriving equality can be lazy or cheaper. | §2.3: 43% of day 18's own time, 26% of day 15's | 10-40 ms a day **[estimated]** | medium: elaborator | "Profile data declarations: day 18's `Expression` 19.5 ms, 10 k-node read-back" (opus), small, profile first |
| 7 | **SW-4650, cheaper values (steps 2-3).** | allocation and copies are 31-36% of own self time | if a third of that goes, 10% of own time: 10-50 ms a day **[estimated]** | high, kernel evaluator (as planned) | as filed; it matters for big proofs, not for this gap |
| 8 | **SW-4612, blocker without read-back.** | `matching::blocker` under 0.1% of own time on all three days | none here **[measured]** | as filed | as filed; keep for the formatter (6.6% there in SW-4608) |

Items 2-4 are about 500 ms of fixed cost in every `aoc/` check: four fifths of the 625 ms
that a fully cached day 2 check takes. Item 1 changes what we report, not how fast we are.
Items 7 and 8 work per step, and these days hardly have per-step costs to save.

## 5. Not done

- No per-theorem Lean timings (`set_option profiler true`), so section 3 compares file totals.
- No profile of a `--no-cache` day. Its extra time is the std files the probe misses, which
  SW-4608 already profiled.
- I didn't check whether `run`, `test` and the LSP also build the std index each time
  (item 2's "probably").
- I didn't rerun Lean: the figures are SW-4806's, from three hours earlier on the same machine.
