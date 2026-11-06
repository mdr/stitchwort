# Where build and test time goes (SW-1716, D2532)

Measured on 6 Nov 2026, 19:25 to 20:45 GMT, on Speedwell (10-core
Mac, 32 GB), with nothing else running, at `fd3cb58b4` (main). Profiling
only: nothing in the build or the tests was changed; the experiments used
environment variables, a timing wrapper around the linker, and one
throwaway test file, all since removed.

How it was measured:

- Builds ran without kache (`RUSTC_WRAPPER=`), in fresh target folders in
  the scratchpad, so they are a lane's build on a quiet machine with no
  cache. Where kache matters it is discussed separately (§1.6).
- The linker was wrapped by a script that timed each link and, in one run,
  linked each binary three times: with the nix ld64 the build uses now,
  with Apple's ld-prime and with lld (§1.4).
- Test binaries ran one at a time with nextest's `daily` profile
  (`STITCHWORT_TIER=daily`, `STITCHWORT_TEST_THREADS=5`, 8 test threads),
  under `dev/memguard` with its report on, and a sampler that recorded each
  test process's resident memory every 2 s. They ran from the incremental
  build of §1.3, whose code is 0 to 5% slower (§1.3), so their times are
  if anything a little high.
- Profiles are macOS `sample` (1 ms) of a running test process.

## 1. Build

### 1.1 Settings

| Setting | Value |
|---|---|
| Profile every test and the CLI build use | `release` (`cargo nextest run --release`, `task build`) |
| `opt-level`, `codegen-units`, `lto` | 3, 16, off (cargo's release defaults; `Cargo.toml` overrides only `insta` and `similar` in `dev`) |
| `incremental` | **off** (release default) |
| Debug info | none (`debug = 0`); `split-debuginfo` and `line-tables-only` therefore change nothing for these builds |
| Linker | the nix clang wrapper's `ld`: ld64-956.6 from nixpkgs (not Apple's ld-prime, which is `ld-27037.1` in the installed Command Line Tools) |
| Compiler cache | kache in lane worktrees and scratch clones; none in the main checkout |
| Feature sets | one for tests and the dev CLI, so the test build also builds `stitchwort` (a release CLI build afterwards takes 0.8 s) |

### 1.2 Clean and incremental builds, as things are

`cargo test --release --workspace --no-run --timings`, quiet machine, no kache.

| Build | Wall | CPU (user) | Units compiled | Binaries linked | Link time, summed |
|---|---|---|---|---|---|
| Clean (cold target folder) | **191 s** | 1293 s | 426 | 232 | 102 s |
| After a one-line edit in `crates/core` | **136 s** | 1024 s | 191 | 177 | 81 s |
| After a one-line edit in `crates/elab` | **131 s** | 914 s | 159 | 153 | 75 s |
| Release CLI alone, clean (`task build`'s command) | 81 s | 523 s | 214 | 2 | - |

The one-line edit was a word in an error message: any edit to a crate,
even a comment, recompiles every crate and test that depends on it, since
cargo has no early cut-off.

Where the 914 s of the `elab` edit go (rustc time per unit, link included):

| Units | Count | Seconds |
|---|---|---|
| Integration test binaries (`crates/*/tests/*.rs`) | 137 | **628** (median 4.2 s, max 13 s) |
| Library crates (`elab` 52, `driver` 32, `lsp` 22, ...) | 6 | 123 |
| Library unit tests (`elab`'s own 63 s) | 9 | 117 |
| The `stitchwort` binary and the rest | 6 | 42 |

Linking is about 8% of it. The cost is that 137 test binaries are each
compiled at `opt-level = 3` from scratch, re-optimising the generic code of
the library crates they use; with 10 cores that is the last 60 s of every
rebuild.

**Critical path** (from `--timings`; the concurrency is the number of rustc
processes running):

- Clean build: 10 wide from 0 to 45 s; then 1 to 4 wide from 50 to 90 s,
  while `elab` (65 s: 21 s front end, 44 s code generation) and
  `cranelift-codegen` (67 s) finish; 10 wide from 90 to 160 s (the test
  binaries); then **one process for the last 30 s**: `elab`'s own unit
  tests (`elab` compiled a second time with `cfg(test)`, 46 s), which
  cargo started late, at 145 s.
- `elab` edit: 2 to 5 wide for the first 60 s (`elab` itself, 52 s, then
  `driver`), then 10 wide to the end (the test binaries).
- `core` edit: the same shape; `core` is 5 s, then `elab`'s 57 s.

`elab` is 115,700 lines, more than every other crate together (core
22,700, rt 19,400, driver 16,200). It is the serial step of every build.

### 1.3 Incremental release builds

The same builds with `CARGO_PROFILE_RELEASE_INCREMENTAL=true` (cargo then
also uses 256 codegen units for the workspace crates; dependencies are
unaffected):

| Build | Wall | CPU (user) | Link time, summed | Integration tests' rustc time |
|---|---|---|---|---|
| Clean | 178 s (191 without) | 1259 s | - | - |
| One-line `elab` edit | **21 s** (131 without) | 100 s | 72 s | 132 s (median 0.95 s) |
| One-line `core` edit | **22 s** (136 without) | 118 s | 81 s | 150 s |

Cost:

| | Without | With incremental |
|---|---|---|
| `hash_stability prelude` (checks std from source: the elaborator) | 13.82 s | 13.80 s |
| `effect_runtime every_shape_runs_at_a_million_elements` (the evaluator and runtime) | 45.5 s, 45.6 s | 47.9 s (+5%) |
| Target folder after the builds above | 2.6 GB | 6.3 GB |

So a lane's edit-build-test loop goes from about 2¼ minutes of build to
about 20 s, for 5% at most on the speed of the tests' code and 3.7 GB of
disk per target folder. Linking is now 70 to 80% of the build's CPU, which
is what makes §1.4 and fix 5 matter after this one.

### 1.4 The linker

Each test binary links in about 0.3 s alone and 0.5 s with nine others
linking, so linking is cheap per binary; there are just many binaries.

| Linker | 153 binaries during a parallel rebuild, summed | Alone: `lsp`, `aoc_answers`, `rewind` |
|---|---|---|
| ld64-956.6 (nix; what the build uses) | 76.6 s | 0.38, 0.24, 0.35 s |
| ld-prime (Apple, CLT, `--ld-path`) | 80.5 s | 0.35, 0.29, 0.34 s |
| lld 21.1.8 (nix, `ld64.lld`) | **59.0 s** | 0.30, 0.20, 0.27 s |

ld-prime, Apple's fast linker, is no faster than nix's ld64 for these
binaries (it is multi-threaded, which doesn't help while nine other links
run). lld takes 23% off. On a non-incremental rebuild that is about 2 s of
wall time; with incremental builds about 2 to 3 s of 21 s. All 153 links
with each linker succeeded; nothing was run from the alternative links.

### 1.5 Concurrent builds

Four incremental-build target folders were cloned (`cp -c`) and an `elab`
edit rebuilt in all four at once. The clones lost their incremental state
(the copies' own incremental caches didn't match), so three of the four
did a full non-incremental rebuild of everything below `elab`:

| Build | Alone | Four at once |
|---|---|---|
| Incremental `elab` edit | 21 s | 66 s (3.1×) |
| Non-incremental `elab` edit (three clones) | 131 s | 368 s each (2.8×) |

The four together used 2,650 s of CPU, 265 s of wall on 10 cores if
perfectly shared; they took 368 s, so contention costs about 40% on top of
simply sharing the cores (load average 112). Builds share the cores
roughly evenly: each of N lanes building at once takes about N times as
long, and a little more. Peak memory was not the limit (each rustc stays
under 2.5 GB). Cloning a target folder does not carry incremental state,
so a new worktree's first build is a clean build either way.

### 1.6 kache

`kache stats` for the last 24 hours (as reported by kache, not measured
here):

- 54% of crate compilations were hits, but only **26% of compile time**:
  the hits are mostly third-party crates, which are quick. `stitchwort_elab`
  missed at 3 to 5 minutes a time under load.
- **5.8 h of scheduler wait** ("~1 min on a shared compile, ~5.8 h for a
  permit"): kache's daemon limits how many compiles run at once across
  all lanes, so lanes queue behind one another.
- Overhead per compile: 319 ms to compute the key, 162 ms for a dep-info
  pre-pass (an extra rustc run), 222 ms per hit.
- The store (36 GiB) is over its 23 GiB budget, and 890 GiB have been
  pruned since 2 Nov: entries are written and evicted at a high rate.

A clean build here without kache took 3 min 11 s; tonight's fresh lane
build with kache took about 6½ min with lanes running beside it. I didn't
time a kache build on a quiet machine, so how much of the difference is
kache's queueing and how much other lanes' load is not separated.

## 2. Std setup cost

A throwaway test timed the session constructors (64 MiB stack, release,
quiet machine, empty test std cache):

| Setup | Time |
|---|---|
| `Session::new()` (lazy: the core only) | 0.23 s |
| `Session::new()` and a file importing `Std (Pair, Text)` | 0.09 s |
| `Session::navigable()` | 0.09 s |
| `eager_from_source_for_stack` (every library file checked) | **13.5 s** |
| `eager_for_stack`, first after a build (checks and writes the test std cache) | **14.4 s** |
| `eager_for_stack`, from the test std cache | 0.46 s |
| The language server's own load of the library (`LiveProject::new_except`), per `lsp::features` test | 26 s with 8 at once (the fastest tests), 1.4 GB each |

The test std cache is keyed by the build fingerprint (every crate the
driver depends on), so after any edit to `core`, `elab` or the driver every
test process that starts before the first one has written the cache checks
std from source: with 8 test threads that is up to 8 × 14 s = 2 min of CPU
in the first wave, again for each stack size in use (there are seven:
8 MiB to 16 GiB).

Profile of checking std from source (`hash_stability prelude`, 6.3 s
sampled, single-threaded):

| Self time | Share |
|---|---|
| `core::value` (the evaluator: `run`, `detach`, `resume`, `visit`, `quote_as`, `push`, `Value::clone`) | 46% |
| `malloc`, `free`, `memmove` (macOS's allocator: the driver's test binaries don't use mimalloc) | 25% |
| `drop` of values | 9% |
| `core::term` (`for_each_child`, `take_children`) | 7% |
| `elab` itself | 5% |

Inclusive: `check_component` 99%, `lifted_body` 83%, `check_value` 72%,
`infer` 46%, `value::run` 43%, `matching::check_match` 30%, `quote_as` 27%,
`unify::run` 24%, `rewrite::check_rewrite` 20%. Checking std is evaluation
and allocation; the elaborator's own logic is small. Library loading is
one thread from start to end.

## 3. The ten slowest binaries, alone

Each binary alone, `daily` profile, quiet machine, after the incremental
build (so the test std cache and the check caches start cold, as after a
rebuild). "Daily" is tonight's daily run, per-binary sums under load.

| Binary | Daily test time | Alone: test time | Alone: wall | Peak memory | Slowest test alone |
|---|---|---|---|---|---|
| `lsp::features` | 1,091 s | 704 s | 109 s | **9.16 GB** | 106 s |
| `cli::lsp` | 1,030 s | 679 s | **441 s** | 4.70 GB | 220 s |
| `cli::aoc_answers` | 891 s | 488 s | 194 s | 1.84 GB | 191 s |
| `driver::rewind` | 777 s | 839 s | 312 s | 4.77 GB | 309 s |
| `driver::resources` | 615 s | 195 s | 177 s | 1.63 GB | 173 s |
| `stitchwort-web` | 536 s | 282 s | 164 s | 1.56 GB | 161 s |
| `driver::std_library` | 523 s | 338 s | 138 s | 2.34 GB | 94 s |
| `driver::check_cache` | 388 s | 323 s | 65 s | 2.08 GB | 63 s |
| `cli::extract` | 381 s | 300 s | 61 s | 5.05 GB | 58 s |
| `cli::examples` | 336 s | 200 s | 102 s | 3.50 GB | 93 s |
| **The ten** | **6,568 s** | **4,348 s** | **1,763 s** | | |

All passed. Alone they take 0.3 to 0.85 of their daily test time (rewind's
1.08 is because tonight's daily run cut some of its tests short).

Setup against the tests' own work, by binary (from the profiles, the
session timings of §2 and the tests' code; the split is measured where it
says "sampled", estimated otherwise):

| Binary | Setup | The tests' own work |
|---|---|---|
| `lsp::features` | **at least 59%**: every test loads std from source in the language server (sampled), 26 s or more per test, 16 tests | the rest: requests, and re-checks after edits |
| `cli::lsp` | the two AoC tests (430 s of the 441 s wall) are almost all AoC elaboration: `check --project` to warm, `check --index` (a miss, sampled) and the server's own check, on one core | the few requests and the comparison. Small tests take 0.3 to 0.6 s; project tests about 30 s, mostly the server loading the library |
| `cli::aoc_answers` | each per-day test runs `stitchwort run --no-cache`, so it checks std's parts, `Aoc.Common` and the day afresh: most of its 2.5 to 34 s | running the day on its input |
| `driver::rewind` | per example, small (lazy sessions, §2) | checking each example three ways; the binary's tail is **one untimed counterexample search** (sampled, 100% of the last minutes) |
| `driver::resources` | none to speak of (lazy sessions, 0.1 s) | **91% counterexample searches** on library theorems that ran out of work (sampled) |
| `stitchwort-web` | the whole AoC project checked through the playground's uncached path, then days 1 to 6 again: nearly all of its 161 s | the days' tests and runs |
| `driver::std_library` | checking std is the point of these tests | - |
| `driver::check_cache` | loading the whole library from source and from the cache is the point (35 s each) | - |
| `cli::extract` | small | `the_declarations_type_check` (58 s) runs `tsc` on the generated code |
| `cli::examples` | one eager session per worker, replayed (0.46 s) | the corpus: checking every sampled example |

The conv_shortcut sweep that the memguard killed twice tonight now peaks at
**1.38 GB** and takes 34 s alone (SW-1702, merged at 18:04, after tonight's
daily run had started).

## 4. The slowest tests

The four slowest single tests of the baseline, alone:

| Test | Daily | Alone | Why it's slow |
|---|---|---|---|
| `driver::resources running_out_at_any_point_only_ever_means_no_answer` | 582 s | 173 s | It loads a program in a new session at every 4th of 161 work limits. At limits of a few thousand, library theorems fail by running out, and each failure starts an **untimed counterexample search**: 91% of the samples. The same test took 3.8 s on 5 Nov. |
| `cli::lsp a_newer_edit_cancels_the_check_running` | 460 s | 220 s | One core at 100% throughout, 2.7 GB: AoC elaborated by `check --project`, then the language server elaborates the namespace and what it uses with the editor's entries, which the `check` cache doesn't hold. Not profiled itself; its neighbour below was. |
| `driver::rewind rewinding_changes_nothing_for_the_examples` | 372 s | 309 s | A pool over the sampled examples; for its last minutes one worker runs while the rest wait, and that worker is in an **untimed counterexample search** (sampled). |
| `cli::lsp aoc_navigation_matches_check_index` | 340 s | 210 s | `stitchwort check --index` of AoC misses the cache that `check --project` warmed (sampled: `elaborate_namespace_untimed` under `elaborate_namespace_cached`) and elaborates the project on one core, 1.7 GB; then the language server checks it again (up to 600 s allowed), 3.7 GB. |

Cheaper versions that keep the guarantee:

- `resources`: don't search after a resource failure (fix 2), which keeps
  the test's point (running out only ever means no answer) and makes it
  seconds again. Failing that, the daily tier could take every 16th limit
  and the full tier all of them; but the search cost is the real problem.
- `a_newer_edit`: its point is that an edit cancels a running check. It
  needs a check that takes a while, not the whole AoC project: a namespace
  that is slow on its own, with a warm cache for what it uses, would keep
  the guarantee in a few seconds. The AoC run could stay in the full tier.
- `rewinding_changes_nothing_for_the_examples`: bound the search (fix 2c),
  or leave the one example whose search runs long to the full tier, as
  SW-1702 did for `conv_shortcut`.
- `aoc_navigation_matches_check_index`: warm with the index flavour so
  both sides load from cache (fix 4); the comparison stays the same. The
  daily tier could also compare one of the three files, with all three in
  the full tier.

Two more found on the way:

- `aoc_answers every_day_from_the_whole_projects_cache`, 191 s alone: a
  cold check of AoC, then 55 days run one at a time (fix 8).
- `search_at_aoc search_at_on_aoc_goals` took 249 s on 5 Nov and was
  killed tonight after 1,988 s; not run here (fix 10).

## 5. Memory and concurrency

What pushed the memguard tonight: both kills were at 16.2 and 16.1 GB, and
both times `conv_shortcut every_rejected_example_gets_the_same_verdict_without_the_shortcut`
was 10.7 to 11.5 GB of it. SW-1702 fixed that (1.38 GB now, above).

The other big users, alone (memguard's peak for the binary; per-process
resident memory from the sampler):

| Binary or test | Peak |
|---|---|
| `lsp::features`, 8 tests at once | **9.16 GB** for the binary; 1.2 to 1.5 GB per test, every test |
| `cli::extract` | 5.05 GB |
| `driver::rewind` | 4.77 GB (`emptying_the_caches…` 1.8 GB) |
| `cli::lsp` | 4.70 GB; `aoc_navigation_matches_check_index` 3.7 GB, `a_newer_edit…` 2.7 GB, `check --index` child 1.7 GB, project tests 1.3 to 1.6 GB each |
| `cli::examples` | 3.50 GB |
| `driver::std_library` | 2.34 GB |
| The most resident at once over all ten runs | 12.5 GB (during `lsp::features`) |

So without `conv_shortcut`'s 11 GB the daily tier's peak is set by which of
these overlap. `lsp::features` alone is more than half the cap; with
`cli::extract` or `rewind` beside it, it passes 14 GB.

What would keep the tier under 16 GB without slowing it much:

- Fix 3 (SW-1686): `lsp::features` from 9 GB to an estimated 2 GB. This is
  the one that matters.
- Until then, a nextest test group for `lsp::features` with
  `max-threads = 4` (about 6 GB): its tests are 26 to 106 s, so four at a
  time costs about a minute of that binary's wall time, which overlaps
  other work.
- `threads-required` on the corpus sweeps (fix 6) also stops two 5-thread
  pools and 8 other tests running at once, which lowers the memory that
  overlaps as well as the load.
- A `memory-heavy` group (`max-threads = 2`) for any test that holds more
  than 2 GB: today `aoc_navigation_matches_check_index` and `a_newer_edit…`
  (already serial in `lsp-aoc-copy`).

Concurrent lanes (§1.5): N builds at once each take about N times as long
plus 10 to 40%; four lanes all rebuilding after an `elab` edit is about
6 minutes each today, about 1 minute each with fix 1. Builds didn't come
near the memory limit (rustc under 2.5 GB each). Lanes running tests
beside each other add their tests' memory: two lanes' `test:one` of
`lsp::features` would be 18 GB.

## 6. Ranked fixes

Best saving for the effort first. "Lane rebuild" is the build after an edit
in a lane; "daily" is the daily tier's wall time (test time ÷ about 8);
"test time" is summed over tests, as in the baseline.

| # | Fix | Saving | Risk | Size | Model |
|---|---|---|---|---|---|
| 1 | Incremental local release builds | ~110 s per lane rebuild (131 → 21 s) | low | one line | Sonnet |
| 2 | Bound or skip the untimed counterexample searches | 2 to 4 min of daily tail | medium | small-medium | Sonnet |
| 3 | `lsp::features` replays std (SW-1686) | 1 to 1½ min daily, 7 GB peak | low-medium | medium | Sonnet |
| 4 | LSP AoC tests: one AoC check, not three | 4 to 6 min daily tail | medium | medium | Sonnet |
| 5 | One test binary per crate | 6 to 8 s of a 21 s rebuild; 2.5 GB disk | medium | large | Sonnet (+DeepSeek) |
| 6 | `threads-required` for the sweeps, 10 slots | unclear; less thrash and memory overlap | low | small | Sonnet |
| 7 | Fill the test std cache once per build | up to 2 min CPU per run, 14 s latency | low | small | Sonnet |
| 8 | `aoc_answers`: parallel day loop, warm cache in daily | ~1½ min daily tail | low | small | Sonnet |
| 9 | Web AoC test: check once | 1 to 1½ min daily tail | low | small | Sonnet |
| 10 | Bisect `search_at_on_aoc_goals` (249 → 1,988 s) | up to 30 min of daily | - | small | Sonnet |
| 11 | lld | 2 to 3 s per rebuild | low | small | Sonnet |
| 12 | Measure kache, keep or drop | first builds; queueing | low | small | Sonnet |
| 13 | Split `elab` | 30 to 50 s of a clean build | medium | large | Opus (plan) |
| 14 | mimalloc in test binaries | maybe 10 to 20% of elaboration in tests | low | small | Sonnet |
| 15 | Prune `target/` | disk (21 GB) | none | trivial | orchestrator |

1. **Turn on incremental compilation for local release builds.**
   - *Problem.* Every test build is `--release`, where cargo's default is
     non-incremental, so a one-line edit in `core` or `elab` costs 131 to
     136 s of build (§1.2).
   - *Change.* `CARGO_PROFILE_RELEASE_INCREMENTAL=true` in the devShell (or
     `[profile.release] incremental = true` in `.cargo/config.toml`), with
     the Nix package and check builds left as they are, so the distributed
     binary is built as now.
   - *Saving.* **About 110 s of every lane rebuild** (131 → 21 s for an
     `elab` edit, 136 → 22 s for `core`), and the same for each merge's
     verifier build. No gain on a fresh worktree's first build.
   - *Risk.* Low. The tests' code is 0 to 5% slower (§1.3); each target
     folder grows by about 3.7 GB. kache probably passes incremental
     compiles through uncached (check: `kache stats` "Not cached"); its
     hits on workspace crates are already rare (§1.6).
   - *Size and model.* One line and a check that the flake's builds don't
     inherit it. Sonnet, or the orchestrator as a mechanical change.

2. **Stop untimed counterexample searches from dominating the slowest tests.**
   - *Problem.* `.cargo/config.toml` sets `STITCHWORT_UNTIMED_COUNTEREXAMPLES`
     for every test, so a search stops only at its count of inputs. Sampled:
     **91%** of `resources running_out_at_any_point_only_ever_means_no_answer`
     (173 s alone) is `search_counterexample` → `run_fast`, on library
     theorems that failed only because the work limit ran out; and the
     last 100 s or more of `rewind rewinding_changes_nothing_for_the_examples`
     (309 s alone) is one worker in `search_counterexample` on one rejected
     example while the other workers sit idle. The resources test took
     3.8 s in the 5 Nov daily run; SW-1304 (85c21f7d5, 5 Nov 04:29,
     "counterexample search reaches more hypotheses") landed in between and
     is the first suspect.
   - *Change.* (a) Bisect the regression. (b) Don't search for a
     counterexample after a theorem failed by running out of resources
     (nothing found under an exhausted budget can be trusted, and it isn't
     what the user needs to see). (c) Give an untimed search a work bound
     as well as a count, so one example can't take minutes.
   - *Saving.* About 170 s of `resources` and 150 to 250 s of `rewind`'s
     tail when alone, so **2 to 4 minutes of daily wall time** (both are
     single-threaded tails), plus whatever other sweeps hit the same
     searches (not measured).
   - *Risk.* Medium: snapshots that show a counterexample note may change;
     (b) changes what users see after `E-RESOURCE` (for the better).
   - *Size and model.* Small to medium. Sonnet.

3. **Replay std from the test cache in `lsp::features` (SW-1686, already filed).**
   - *Problem.* Every one of its 16 tests loads the whole library from
     source in the language server (`LiveProject::new_except` →
     `load_libraries_except`, sampled at 100%): 26 s at least per test with
     8 running, **1.4 to 1.5 GB each, 9.2 GB at the binary's peak**.
   - *Saving.* Test time 704 s alone (1,091 s in the daily run) → an
     estimated 100 s; **about 1 to 1½ min of daily wall time and 7 GB of
     peak memory**.
   - *Risk.* Low to medium (the language server's production path must
     stay as it is; only the tests replay).
   - *Size and model.* Medium. Sonnet.

4. **Check AoC once, not three times, in the language-server AoC tests.**
   - *Problem.* `cli::lsp`'s `a_newer_edit_cancels_the_check_running` (220 s
     alone) and `aoc_navigation_matches_check_index` (210 s) are in the
     `lsp-aoc-copy` group, so they run one after the other: **430 s, on one
     core**, nearly the whole binary's 441 s. Each warms AoC with `check
     --project`, but the editor's entries and `check --index`'s aren't the
     ones `check` writes, so `check --index` (sampled: all of it in
     `elaborate_namespace_untimed`, a cache miss) and then the language
     server each elaborate AoC again, single-threaded.
   - *Change.* Warm the copy with the flavour the editor and `check
     --index` use, so their loads are cache hits, and check whether
     `a_newer_edit` needs a whole-project check at all (it needs one
     namespace's check to be long enough to cancel).
   - *Saving.* An estimated 250 to 350 s of the binary's wall time, which
     is daily-tier tail: **4 to 6 min of daily wall time**, if the group
     stays serial.
   - *Risk.* Medium: the navigation test compares the editor with `check
     --index`, and must keep comparing two independent paths.
   - *Size and model.* Medium. Sonnet.

5. **One integration-test binary per crate.**
   - *Problem.* 166 test files are 166 binaries. Without incremental builds
     each is optimised from scratch (628 s of 914 s for an `elab` edit);
     with them, their links are 72 of 100 s of CPU. Each binary is about
     19 MB, so about 3 GB per target folder.
   - *Change.* `tests/main.rs` per crate with the files as modules (and
     `autotests = false`); a few binaries that need their own allocator
     (`resources` uses mimalloc) or process-wide state stay separate.
     `.config/nextest.toml`'s `binary(...)` filters become
     `binary(...) & test(/^module::/)`.
   - *Saving.* With fix 1: about 60 s of CPU and an estimated 6 to 8 s of
     the 21 s rebuild. Without it: an estimated 300 to 450 s of CPU
     (shared generic code compiled once per crate, not per file), 30 to
     45 s of wall. About 2.5 GB of disk per target folder.
   - *Risk.* Medium: every nextest filter and test-group override names
     binaries, and tests that rely on running alone in a binary need
     checking. Nextest still runs each test in its own process.
   - *Size and model.* Large and mechanical. Sonnet for the plan and the
     filters; the moves could go to DeepSeek.

6. **Make nextest's slots match the cores the tests use.**
   - *Problem.* The daily profile runs 8 tests at once, and two corpus
     sweeps run pools of 5 threads each beside them, plus the debug
     `builtins` run: up to 19 busy threads on 10 cores. The logged times
     are inflated by it: alone, `resources`' slowest test is 173 s against
     582 s in the daily run (3.4×), `cli::lsp`'s two AoC tests 220 and
     210 s against 460 and 340 s, `rewind`'s 309 s against 372 s.
   - *Change.* `threads-required = 5` (nextest's per-test slot count) on
     the `corpus-sweeps` override, matching `STITCHWORT_TEST_THREADS`, and
     `test-threads = 10`; a memory-heavy group (below) for the rest.
   - *Saving.* Hard to predict without a daily run: total CPU is the same,
     but thrashing (load 40 to 110) and memory overlap fall. Likely a
     modest wall-time gain, and logged times that mean something.
   - *Risk.* Low. *Size and model.* Small. Sonnet; needs one daily run to
     confirm (Matt's approval).

7. **Fill the test std cache once per build, before the tests start.**
   - *Problem.* The cache is keyed by the build fingerprint, so after any
     edit every test process in the first wave that wants an eager session
     checks std from source (14.4 s, §2) until one has written it, once
     per stack size.
   - *Change.* A step before nextest (in `test:lane`, `test:one`, merge and
     daily; or a nextest setup script) that makes one eager session for
     each stack size the tests use.
   - *Saving.* Up to 8 × 14 s = 2 min of CPU per stack size per test run
     after a rebuild, and 14 s off the first test a lane waits for.
   - *Risk.* Low. *Size and model.* Small. Sonnet.

8. **Run `aoc_answers`' whole-project day loop in parallel, and share a
   warm cache in the daily tier.**
   - *Problem.* `every_day_from_the_whole_projects_cache` (191 s alone, 391
     s in the daily run) checks AoC cold into a fresh cache, then runs 55
     days one after another, each `stitchwort run` loading the project
     from that cache. The 56 per-day tests each run `--no-cache`, so std and
     `Aoc.Common` are elaborated 56 times.
   - *Change.* The day loop on a pool (the days are independent); the
     per-day tests in daily on one shared, warm cache, keeping `--no-cache`
     in the full tier (the cold path is still covered by the whole-project
     test's own cold check).
   - *Saving.* An estimated 100 s of that test's wall time and about 150 s
     of test time for the per-day tests; **about 1½ min of daily tail**.
   - *Risk.* Low. *Size and model.* Small. Sonnet.

9. **Check AoC once in the web project test.**
   - *Problem.* `web project::tests::every_aoc_day_checks_passes_its_tests_and_runs_on_its_example`
     (161 s alone, 363 s in the daily run) checks the whole project, then
     checks and tests days 1 to 6 again from scratch, all on one thread,
     through the playground's uncached path.
   - *Change.* Check days 1 to 6 in the daily tier from the whole check's
     session (or a sample of days), all six in the full tier.
   - *Saving.* An estimated 60 to 100 s of daily tail. *Risk.* Low.
     *Size and model.* Small. Sonnet.

10. **Bisect `search_at_aoc search_at_on_aoc_goals`.** 249 s in the 5 Nov
    daily run; tonight it was killed after 1,988 s. Not run here (not in
    the brief's ten). Possibly the same counterexample searches as fix 2.
    Small investigation, Sonnet.

11. **Link with lld.** 23% less link time (§1.4): 2 to 3 s of a 21 s
    incremental rebuild, less after fix 5. ld-prime gains nothing. Low
    risk for the test binaries; `stitchwort build --native`'s own linking
    of user programs is separate and should stay as it is. Small. Sonnet.
    Worth doing only after 1 and 5.

12. **Measure kache honestly, and keep it or drop it.** Its own stats
    (§1.6): 26% of compile time served from cache, 5.8 h of queueing for
    permits in a day, a store over budget and churning. A quiet-machine
    fresh-worktree build with and without it, and with two lanes building,
    would settle whether it pays. With fix 1, a lane's rebuilds no longer
    need it; only first builds might. Small. Sonnet.

13. **Break up `elab`.** 115,700 lines, the serial step of every build: a
    40 s stretch of the clean build runs one to four processes, and
    `elab`'s own unit tests (`elab` compiled again with `cfg(test)`, 46 to
    63 s) are the last 30 s of a clean build. Splitting off parts that
    depend on little (the counterexample search, the `derive_*` modules,
    equations) would shorten clean builds by an estimated 30 to 50 s.
    Large, and the crate boundaries are a design question: Opus for the
    plan.

14. **Use mimalloc in the test binaries.** Checking std spends 25% of its
    self time in macOS's `malloc` and `free` (§2); the CLI already uses
    mimalloc, most test binaries don't. Possibly 10 to 20% off every
    elaboration-heavy test; not measured. One line per binary, or one per
    crate after fix 5. Small. Sonnet.

15. **Prune the main checkout's `target/`.** 21 GB, against 2.6 GB for one
    up-to-date build: old artifacts of earlier builds. Disk only.

## 7. What I couldn't measure

- **kache on a quiet machine.** I didn't time a fresh worktree's build
  through kache with nothing else running, nor two lanes building through
  it at once, so its share of tonight's 6½-minute lane build is inferred
  from its own statistics.
- **Whether kache caches incremental compiles.** Not tested.
- **Consolidated test binaries** (fix 5): the saving is estimated from the
  per-binary compile and link times, not measured on a prototype.
- **The daily tier's wall time after any fix.** Not run (no daily or full
  tier in this lane). In particular fix 6's effect needs one daily run.
- **The other tests of the daily tier.** Only the ten binaries and the one
  `conv_shortcut` test were run; `search_at_aoc` was not.
- **Clippy, the doctests, `web:pkg` and the debug `builtins` run** that the
  daily task runs beside nextest: not timed. `builtins` took 121 s tonight
  (its log); clippy re-checks every target.
- **`a_newer_edit_cancels_the_check_running`** was not sampled (it ended
  while I was sampling); its explanation is from its code, its one core at
  100% and its neighbour's profile.
- **mimalloc in test binaries** (fix 14): the allocator's share is
  measured, the saving is not.
- **Debug info and `split-debuginfo`:** nothing to measure, since the
  release profile has no debug info; they would matter only for the debug
  `builtins` build.
