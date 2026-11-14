# Native by default: sizing and plan (SW-2535)

*9 November 2026, after D3448 (Matt: finish native code and make it the
default for `run`, `test` and `build`; the machine stays as `--machine`
and as the fallback, including in built executables). Measured on
Speedwell (Apple M4 Pro, 10 cores, macOS) at `52a2ddc9d`, with the load
average between 30 and 100 the whole time (other lanes), so wall times are
rough; instruction counts are steady. Scratch scripts only; no code
changed.*

## Summary

- **Coverage is complete today.** Every program tried compiles every body
  `main` reaches and runs with the machine executing 0 instructions:
  bench/compare's 16 programs, all 57 AoC days that have an input, all 44
  runnable `examples/accept` programs, and `Rogue.main`. Output matches
  `run` byte for byte wherever the program is deterministic (the seeded
  rogue too). Nothing blocks at the instruction level:
  `census::n1_blocker` accepts every instruction the lowering emits.
- **The brief's picture of today is out of date**, and that matters for
  the plan. Since native-only.md's NO5 and NO6 (26 October, D1294, Matt:
  "surely a compiler doesn't hedge its bets"), `run --native` no longer
  falls back per island, and a `build --native` executable contains no
  machine at all. Both refuse with an error instead. D3448's "machine as
  the fallback inside built executables" partly reverses D1294, so its
  scope is Matt's call (D3449 below).
- **Shipping Cranelift costs 2.8 MB (+14%) stripped**, 3.6 MB as cargo
  links it. A clean release build uses 25% more CPU (397 → 496 s user);
  the wall time is about the same (the extra crates build in parallel),
  but under this load I can't put a number on the difference.
- **Native `run` costs 0.3–1.8 G instructions of compiling up front**,
  0.03–0.15 s of wall time. That is about 1–1.4× the machine's whole run
  for a short program, and pays off in seconds on a long one (2021 day
  15: 6.6 → 2.0 s).
- **`test` has no native path.** The machine runs it, and the reference
  evaluator covers whatever the machine can't do. Adding a native path is
  the largest new piece: an Opus lane of about 4 h.
- **The plan has five lanes and a broad run**, about 12–14 h of lane time
  in all, below. Two decisions for Matt: D3449 (what "fallback in built
  executables" means) and D3450 (whether the native recursion limit may
  differ from the machine's once native is the default, tied to SW-2471).

## 1. Coverage

**How measured.** I ran each target twice, with `stitchwort run --native
--verbose` and with `stitchwort run` (the release CLI with `dev` features,
`task build`), four at a time, and compared stdout and exit status. The
native report gives "running N of the M bodies `main` reaches natively"
and "the machine executed K instructions". Inputs: bench/compare programs
on their real, unscaled inputs with small arguments (coverage doesn't
depend on size); each AoC day on its committed input. Script:
`cover.py` in the lane's scratchpad (the commands are at the end).

| Programs | Tried | All bodies native | Machine ran 0 instructions | Same output and exit as `run` |
|---|---:|---:|---:|---:|
| bench/compare (`programs.toml`, 16 entries) | 16 | 16 | 16 | 16 |
| AoC days with an input (2020, 2021, 2024, 2025) | 57 | 57 | 57 | 57 |
| `examples/accept` with a `def main` | 47 | 44 | 44 | 46 (1 random) |
| `Rogue.main` (400 random keys, seeded with 12345) | 1 | 1 (258 of 258) | 1 | 1 (381,276 bytes) |

- The three accept files that don't run (`fin-eq.sw`, `mutual.sw`,
  `partial-map-main.sw`) have a `main` of the wrong type for running
  (`Bool`, `Nat`, a partial `main` not run as one). Both runners print the
  same error and exit 1, so they aren't native gaps.
- `random-seed.sw` prints a random number: different by design, and both
  exit 0. Unseeded, the rogue also differs, for the same reason.
- `task bench:aoc`'s two runs this morning (05:25, 05:56) built all 55 of
  their days with `build --native`, with every answer right. So
  `build --native` covers the same ground.

**What still blocks, by cause.** No instruction does: the N4 census's
"every instruction" still holds. What makes native code refuse a program
today is never something in the code itself:

| Cause | Where | When it fires | Seen in this sample |
|---|---|---|---|
| The sized stack passes the 64 GiB cap: 2,000,000 frames × the widest frame | `n1::stack_for` | A body with very many live values (the test uses 400 arguments: 77 KB a frame) | never (widest: rogue 4,760 bytes, so 9.5 GB) |
| Unsupported target | `n1::check_target` | Not one of the four macOS and Linux targets | never |
| Layout probe fails | `native_abi::probe_layout` | A std `Rc` or slice layout change (a bug, caught) | never |
| The 64 GiB stack can't be reserved | `stitchwort_host::try_with_stack` | Linux in strict overcommit mode (SW-605) | not tried (Linux) |
| A `TailPrim` of `Text.fold` | `n1_blocker`'s last arm | The lowering doesn't emit it today (`Text.fold` is never a tail primitive) | never |

Features of `run` that native code doesn't cover, as against programs it
can't compile:
- `run --profile` is the machine's sampler; `task profile:native` is
  native code's profiler.
- `run --alloc-trace` works natively only in an `alloc-trace` build.
- The counterexample search counts big-number words (`Limits::number_words`);
  only the machine counts them. That search runs inside the checker, which
  keeps the machine, so it's unaffected.

## 2. What shipping Cranelift costs

**The binary** (`cargo build --release --locked -p stitchwort-cli -p
stitchwort-standalone`, with and without `--features stitchwort-cli/native`,
as `stitchwort-bin` and `stitchwort-native-bin` build it, without kache and
non-incremental, as crane builds; each into a fresh target folder):

| | Without native | With native | Difference |
|---|---:|---:|---:|
| `stitchwort` as linked (release has no debug info, so `strip -S`, which Nix's fixup does, changes nothing) | 24,584,944 | 28,135,792 | +3,550,848 (+14.4%) |
| `strip` (all symbols) | 19,820,128 | 22,636,592 | +2,816,464 (+14.2%) |
| `libstitchwort_standalone.a` (shipped beside it) | 28,081,344 | 28,080,232 | 0 |
| Crates compiled | 114 | 147 | +33 |

**A clean build** (same commands, one after the other):

| | Wall | User CPU | Sys | Peak RSS | Load average at the start → end |
|---|---:|---:|---:|---:|---|
| Without native | 145.7 s | 396.8 s | 16.9 s | 2.43 GB | 56 → 83 |
| With native | 140.1 s | 496.3 s | 21.6 s | 2.37 GB | 83 → 87 |

The CPU time is the reliable number: +100 s (+25%). The wall times are
equal within the noise of a load of 55–87 on 10 cores. Cranelift's crates
build beside the workspace's, whose critical path (elab, then cli) is
unchanged, so a quiet machine should also show little wall-time difference
**[inferred]**. In the flake, these crates go into `cargoArtifacts` (the
dependencies' derivation, built once per `Cargo.lock` change), so day to
day only `stitchwort-native` itself is new work.

**Built executables** (the clean native CLI; `build` and `build --native`;
bytes):

| Program | Machine: linked / stripped | Native: linked / stripped | Build time, machine / native |
|---|---:|---:|---:|
| `Rogue.main` (seeded) | 1,587,504 / 1,204,480 | 2,504,784 / 2,129,584 | 1.52 / 2.28 s |
| AoC 2024 day 9 | 1,570,992 / 1,187,968 | 2,121,264 / 1,749,648 | 1.27 / 1.84 s |
| bench/compare binary-trees | 1,537,960 / 1,154,944 | 1,463,896 / 1,105,104 | 0.55 / 0.63 s |

A native executable is the program's machine code plus the runtime
without the machine (NO6). A big program is larger natively (the rogue by
0.9 MB); a small one is smaller than a machine executable. The rogue's
stripped native binary was 1.85 MB at NO6; it has grown with the game.
The 2024 day 9 executables give the same answers, 0.68 s on the machine
against 0.24 s natively.

**What native `run` costs a short program** (best of 3 by instructions
retired, `/usr/bin/time -l`; the whole `stitchwort run`, checking
included):

| Program | Machine: instructions, wall | Native: instructions, wall |
|---|---:|---:|
| `examples/accept/abilities.sw` | 2.01 G, 0.21 s | 2.01 G, 0.20 s |
| binary-trees, depth 6 | 2.34 G, 0.24 s | 2.70 G, 0.27 s |
| AoC 2020 day 1 (114 bodies) | 5.05 G, 0.49 s | 6.81 G, 0.64 s |
| AoC 2024 day 9 | 9.18 G, 0.77 s | 9.08 G, 0.81 s |
| AoC 2021 day 15 | 89.6 G, 6.63 s | 26.1 G, 1.98 s |
| Rogue, 400 keys (258 bodies) | 9.07 G, 0.72 s | 10.29 G, 0.85 s |

Compiling costs about 5–15 M instructions a body (Cranelift at
`opt_level = speed`, one body at a time). For the small and medium
programs here, that is 0.36–1.76 G instructions up front. Making native
the default makes the quickest runs up to about 30% slower in wall time
(tens of milliseconds) and the long ones several times faster. Section 4
has a lane that could win this back.

**JIT on macOS with the hardened runtime [ran].** I copied the native
CLI three times and ran `run --native` on binary-trees with each copy:
- **linker-signed ad hoc** (as cargo and Nix leave it, with flags
  `adhoc,linker-signed`): runs;
- **ad hoc with `--options runtime`** (hardened), with only
  `disable-library-validation` (needed to load the Nix store's libiconv):
  the process is killed with SIGTRAP (status 133), with no message;
- **hardened with `com.apple.security.cs.allow-jit` as well**: runs.

`run` on the machine works in all three. So `MAP_JIT` (map_jit.rs) does
its job, and `allow-jit` is enough. The shipped binary isn't hardened.
Built executables are compiled ahead of time and never JIT.

## 3. `test` and native code

**Today [source].** `stitchwort test` calls `Session::run_tests_fast_where`
(crates/driver/src/test_run.rs). It lowers every uncached test together
into one `Program` (`lower_definitions`, roots without an entry) and runs
each on one `Machine`. A test that runs partial code is stepped as a
`Delay`. A test the machine can't lower, or that runs out of resources,
goes to the reference evaluator, which also explains failures. Results
are cached per runner (`modes` + `m`). There is no native path. The
driver crate doesn't depend on `stitchwort-native` and mustn't, because
the playground's wasm build uses it.

**What a native path needs** (an Opus lane, about 4 h):
1. **Several roots in one compile.** `n1::compile` compiles what
   `program`'s entry reaches. Tests have roots and no entry, so the
   islands must be the union of the tests' reaches, compiled once per
   `test` run, as they are lowered once now.
2. **Calling a global from outside.** The `NativeExecutor` (or
   `Crossing`) needs an entry that evaluates a nullary global and gives
   back its `Value` (`Bool`). For partial tests it needs the `Delay`
   stepping `run` uses. NO4 drives a `Delay` through the executor already,
   so this is plumbing.
3. **A hook so the driver stays free of Cranelift.** The CLI, built with
   `native`, passes a runner object into `run_selected`. `Runner::Machine`
   stays as it is, and what native code can't run (out of resources, a
   refusal) falls to the machine and then to the reference evaluator, as
   now.
4. **The stack.** `test` would run on the `NATIVE_STACK` thread, as
   `run --native` does (main.rs ~597). The session's limits stay
   `for_stack(STACK)`, so checking doesn't change.
5. **The cache.** Either native results share the machine's mode key
   (they're tested to agree), or they get their own (`n`). I recommend
   their own key until N5 has passed and the same key afterwards; that's
   the orchestrator's call, as it changes no result.
6. **Its cost.** Uncached tests on real inputs take seconds on the
   machine: AoC 2024 day 9's 32 tests took about 3.7 s, 2021 day 15's 18
   took about 15.7 s (the uncached run less the cached one). There native
   code wins by its usual 2–3×. A file of small tests would pay a compile
   of 0.1–1 s for a few milliseconds of running. A threshold (machine
   below N uncached tests, or below N reachable bodies) avoids that; or
   accept it.

The LSP's test runs and the playground stay on the machine. They are not
`stitchwort test`.

## 4. The plan

Each item is one lane unless it says otherwise. Estimates are lane wall
time.

### N5a: a native runner in the differential harnesses (Sonnet, 2.5 h)

**The problem.** None of the differential suites runs Cranelift code
today. Their "native" is the old name for the machine (`effect_differential.rs`'s
`BACKENDS = ["reference", "native", "js"]`; `run_js.rs`'s "natively"). Only
`crates/native/tests` and `crates/cli/tests/running/build.rs` exercise
Cranelift, on chosen programs.

**The change.**
- One switch in the CLI test helpers (`crates/cli/tests/*/common`),
  `STITCHWORT_TEST_RUN=native|machine`, adds `--native` (later
  `--machine`) to every `run` and `build` they spawn. The suites that
  spawn the CLI then cover native code without per-test edits.
- `effect_differential.rs` gets a fourth backend that compiles in
  process, as `compile_native` does.
- `crates/rt/tests/it/machine.rs` is in `stitchwort-rt`, which
  `stitchwort-native` depends on (a dev-dependency back would build `rt`
  twice, with types that don't match). So its differential cases get a
  copy in `crates/native/tests/it` that runs them natively, sharing the
  program list.
- `crates/driver/tests/proofs/differential.rs` runs its evaluators in
  process, so the switch doesn't reach it. Its native half is T's.
- Rename the old "native" (machine) labels in these harnesses to
  "machine", so the reports say what ran.

**Done when:** each suite below runs under the switch on a few targeted
tests.

### N5b: the broad run (orchestrator, compute mode; about 15 min wall)

Matt agreed the broader suite for N5 (D3448). Run under
`STITCHWORT_TEST_RUN=native`:

| Suite | File | Tests | Summed test time in the daily tier |
|---|---|---:|---:|
| Machine against the reference | `crates/rt/tests/it/machine.rs` (and N5a's copy) | 26 | 187 s |
| `run` against `run --reference` | `crates/cli/tests/running/run_reference.rs` | 13 | 150 s |
| `run` against `run --js` | `crates/cli/tests/running/run_js.rs` | 28 | 343 s |
| Random effectful programs, three or four ways | `crates/cli/tests/extraction/effect_differential.rs` | 3 | 51 s |
| Evaluators on the prelude and every example | `crates/driver/tests/proofs/differential.rs` | 6 | 162 s (needs the native `test` path for its test half) |
| AoC answers | `crates/cli/tests/running/aoc_answers.rs` | 57 | 1,024 s (machine; less natively) |
| Examples' `-- run:` lines | `crates/cli/tests/running/examples.rs` | 11 | 385 s |
| `run`, effects, partial handlers | `running/run.rs`, `effect_runtime.rs`, `partial_handlers.rs`; `crates/rt/tests/it/effect_runtime.rs`, `partial_handlers.rs` | 61 | 385 s |

The times are from `target/test-timings.json` (daily tier, so measured
under nextest's parallel load). Summed, they come to about 2,700 s. Under
nextest on 10 cores the wall time is set by the slowest few tests (444 s
for one AoC test), so about 8–12 min plus the build **[inferred]**. Set
the stop point at 25 min. Each spawned `run` pays its compile (0.03–0.15 s);
the heavy ones get faster.

**Then:** fix lanes for whatever it finds. Native code already agrees on
every program I tried, so I expect 0–3 small fixes (Sonnet, or Opus for a
runtime bug), about 1–3 h **[inferred]**.

### F: the machine fallback, in `run` and in built executables (Sonnet, 1.5 h; scope per D3449)

**The problem.** With native code as the default, a program it refuses
would stop running at all. Today that's a 400-argument function, an
unsupported target, a layout bug, or a host that won't reserve 64 GiB
(SW-605).

**The change (recommended scope, whole program):**
- When the compile refuses, `run` warns and runs the whole program on the
  machine (`Runner::Machine`). So does a failure to reserve the native
  stack (fixes SW-605's refusal).
- `build` writes the machine's object (`program_object`, as plain `build`
  does today), and the executable runs on the machine.
- One warning names the reason, and `--verbose` says it in full.
- `--native` (if kept) means "native or fail", for the tests and
  `bench:*`.

**Not recommended: a per-body hybrid**, where an executable runs the
bodies that compile natively and the rest on the machine. That rebuilds
what NO5 and NO6 deleted: crossings into the machine, `NEST_ROOM`, the
encoded program and the machine in every native binary (+233 KB). With
nothing refusing per body today, it buys nothing: an Opus job of about 2
days, plus its agreement tests.

### C: Cranelift in the default binary (Sonnet, 1 h)

- `crates/cli/Cargo.toml`: `default = ["native"]`. Keep the
  `#[cfg(not(feature = "native"))]` paths, so
  `--no-default-features` still builds without native code (for a
  target Cranelift lacks), and make them fall back to the machine rather
  than error.
- `flake.nix`: `stitchwort-bin` gets native code; `stitchwort-native-bin`
  becomes an alias, or goes; clippy is unchanged (it already lints with
  native code).
- `dev/features-check`: `build -p stitchwort-cli` now has `native`
  without `dev`. Check that the unit graphs still agree, and that the
  shipped binary still has none of the dev features.
- The wasm build stays without native code by construction: `crates/web`
  depends on `driver`, `lsp`, `rt` and `js`, never on `cli` or `native`.
  Add a check to `dev/features-check` that `stitchwort-web`'s unit graph
  has no `cranelift-*` crate.
- `nix flake check` builds once (the daily tier, with Matt's go-ahead):
  this lane changes the flake.

### N6: the defaults, `--machine`, docs (Sonnet, 3 h; after C, F and N5)

- `run`, `test` and `build` default to native code, and `--machine` picks
  the machine. Whether `--native` stays as "native or fail", or goes, is
  a user-visible language choice; I recommend keeping it as "native or
  fail", which `bench:*` and the tests need.
- `--verbose` works without `--native`. `--profile` and `--alloc-trace`
  imply `--machine`, with a note pointing to `task profile:native`.
- Update the stale help text ("where they and everything they reach
  compile (stage N1; experimental)") and the `build --native` doc comment
  at main.rs ~435.
- Tests that mean the machine when they say `run` (alloc traces,
  profiles, "the machine executed" notes, machine-only `build`) get
  `--machine`.
- bench/compare's `run` runner (the machine column, compare.py
  `RUNNERS`) becomes `run --machine`; Taskfile tasks that time `run` do
  the same.
- Docs:
  - the guide's running page (`docs/guide/`);
  - README;
  - `docs/testing.md`;
  - native-compilation.md's stage table (N5, N6 done);
  - native-only.md (D1294 as amended by D3449);
  - a feature-tour line (`web/guide/`): "programs run as machine code".
- `docs/syntax.md` doesn't change: this is no syntax.

### T: `test` natively (Opus, 4 h; parallel with N5a)

As in §3. Done when `stitchwort test` runs the AoC and examples tests
natively with the same outcomes (N5b's differential.rs run covers that),
and the machine-only path stays under `--machine`.

### J: compile time (optional, Opus perf lane, 2–3 h after a profile)

The 0.3–1.8 G instructions of compiling (§2) are what native-by-default
costs short runs. Profile first (the "profile before optimising" rule).
The candidates:
- cache the compiled object per program hash under `.stitchwort/cache`,
  as `build` already writes one, so a second run loads it;
- compile at `opt_level = none` below a size;
- compile bodies on several threads.

### Order and totals

```
N5a (Sonnet 2.5 h) ─┐
T   (Opus 4 h) ─────┼─> N5b (broad run, ~15 min) -> fixes (0–3 h) ─┐
C   (Sonnet 1 h) ───┤                                              ├─> N6 (Sonnet 3 h)
F   (Sonnet 1.5 h) ─┘                                              │
J   (optional, any time after a profile) ──────────────────────────┘
```

N5a, T, C and F can run at once. F and C touch `main.rs` and `build.rs`
near each other, which is moderate conflict risk, acceptable. In all:
about 12 h of lanes without J, 14–15 h with it, and one broad run.

## 5. Risks

- **JIT under the hardened runtime (§2.10 of the note).** Measured above:
  without `allow-jit` a hardened `stitchwort` dies silently (SIGTRAP) on
  the first native run. Today nothing ships hardened. If it ever ships
  notarised (Homebrew bottle, Developer ID), the entitlement must go with
  it, and `disable-library-validation` too while it links Nix store
  libraries. A cheap guard for N6: at start-up, if the process is hardened
  (`csops` code-signing flags) and lacks `allow-jit`, run on the machine
  with a note rather than crash.
- **Recursion limits (SW-2471, in review).** Both runners stop at
  2,000,000 frames today, so a deep recursion fails identically. SW-2471
  proposes a native-only 16M limit. Once native code is the default, that
  makes `run` and `run --machine` disagree on how deep a program may go,
  and a program that recurses 3M deep would work natively and fail on the
  machine (and in the playground). The fallback can't save a run that
  fails midway, because it chooses before the run. D3450 below.
- **Resource-limit parity.** Steps and frames are counted by the
  machine's rules (N4), and N2b's and N4's sweeps check every step and
  frame limit up to the least that finishes. Two differences remain: the
  machine-only `number_words` (the counterexample search, unaffected),
  and the stack-pointer backstop, which fires only if the frame bound is
  wrong (a bug, reported cleanly). N5b's `E-RESOURCE` tests under
  `--native` are the check.
- **The 64 GiB reservation on every `run`** (SW-605): on Linux in strict
  overcommit mode, native `run` can't start. F's fallback to the machine
  covers it.
- **First-run latency.** Short runs get up to about 30% slower (§2). The
  playground and LSP are unaffected. J is the remedy if it matters.
- **Coverage of what ships.** Until N5b, only chosen programs test
  native code against the machine. Making native the default before N5b
  would put untested code in front of every `run`. Hence the order.

## Decisions for Matt

**D3449: what does "the machine as the fallback inside built executables"
mean? [rec: the whole program]** If native code refuses a program,
`build` makes a machine executable (with a warning) rather than failing,
and `run` runs it on the machine. Native executables stay machine-free, as
NO6 made them. The alternative is a per-body hybrid: about 2 days of Opus
work, undoing D1294 and NO5–NO6, for a case that has no instance today.
Either way this amends D1294 ("build fails rather than fall back").

**D3450: once native code is the default, may it allow deeper recursion
than the machine? [rec: no, keep one limit for now]** Keeping both at
2,000,000 frames keeps `run`, `run --machine` and built executables
failing at the same depth, which the fallback relies on. SW-2471's 16M
then waits, or applies to both runners together, which needs the
machine's heap-allocated frames measured at that depth.

## Commands run

All in `/Users/agent/repos/mdr/stitchwort/.claude/worktrees/SW-2535`
unless noted; `S` is the lane's scratchpad folder.

| Command | Result |
|---|---|
| `nix develop -c task build` | 30.5 s through kache |
| `S/clean.sh` (two clean release builds, `CARGO_BUILD_RUSTC_WRAPPER=` and `CARGO_PROFILE_RELEASE_INCREMENTAL=false`, fresh target folders) | both exit 0; §2 |
| `python3 -I S/cover.py S/cover.json` (`run --native --verbose` and `run` on 121 targets, 4 at a time) | §1's table |
| seeded rogue copy, 400 random keys, `run` and `run --native` | identical, 381,276 bytes, both exit 0 |
| `codesign -s - -f --options runtime [--entitlements …]` on copies, then `run --native` | exit 0 / 133 / 0 (§2) |
| `build` and `build --native` for the rogue, 2024 day 9 and binary-trees; `strip` copies | §2's table |
| `S/cost.sh` (best of 3, `/usr/bin/time -l`) | §2's short-run table |
| `test Aoc.Year2024.Day09`, `test Aoc.Year2021.Day15`, uncached then cached; `--verify-cache` on three days | §3 |
| bench-aoc JSON from `target/bench-aoc/` in the main checkout | 55 of 55 days `ok` natively |
| `target/test-timings.json` summed by suite | §4's N5b table |
