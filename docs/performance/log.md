# Performance log

A paper trail of every optimisation: what was done, why, the reasoning, the
measurements, and what was rejected or dropped, so an attempt that failed
isn't tried again unknowingly (D3444, Matt, 9 Nov 2026). Speed lanes add an
entry as part of the work ("Speed work" in
[workflow.md](../workflow.md#writing-a-brief)); the orchestrator checks it in
review. Newest first. Dropped attempts and accepted regressions are entries
too.

## How things are measured

- **Instructions retired are the primary measure.** They are far more repeatable
  than time, which is noisier (about 0.5% on a quiet machine, more under load) and can move with no change in instructions (see
  SW-2523).
- `task bench:instructions` builds the `bench/compare` programs natively and
  runs each several times (default 5), checks the output, and prints
  min/max instructions and the change against a saved run (`--save`,
  `--against`). The core ten steer the work; the wide set adds Lean's own
  programs (`rbmap`, `rbmap-ck`, `const-fold`), `spectral-norm` and
  `mapops`.
- `task bench:aoc` runs every AoC day natively, checks its answer, counts
  instructions and diffs them against the previous run. Entries quote its
  **geomean** change and the number of days that moved more than 3%.
- Both build non-incrementally into `target/bench`. An incremental release
  build runs native code about 3% slower, so only like-for-like builds
  compare (SW-2474, below).
- **Overmind comparison runs** (native against CPython and Lean, instructions
  and counters) are written up in
  [../reviews/SW-2295-comparative-speed.md](../reviews/SW-2295-comparative-speed.md);
  the headline ratios per run are in
  [../../bench/compare/history.toml](../../bench/compare/history.toml).
- Each entry says whether a figure was **measured** or **estimated**.
  "Instructions" means native instructions retired. Merge-commit hashes are on
  `main`; `keep/...` branches hold work that was not merged.

Earlier work, recorded elsewhere: the first evaluator and Map fixes in
[../evaluator-speed.md](../evaluator-speed.md) and
[../proposals/interpreter-speed.md](../proposals/interpreter-speed.md); the
effect runtime's allocation counters and the plan these entries execute in
[../proposals/effect-runtime-allocation.md](../proposals/effect-runtime-allocation.md);
the 8 Nov wins listed at the end of this file. The design notes' own status is
in [../proposals/README.md](../proposals/README.md).

---

## 14 Nov 2026

### SW-3212: parsing goes through the lowering, 1.57x slower until L6 (accepted regression)

- **Status:** accepted, temporary regression (Opus). Step 3's switch, lane
  L5 of [syntax-tree-lowering.md](../proposals/syntax-tree-lowering.md#6-performance).
- **Problem.** The compiler's tree is now built from the lossless tree by the
  lowering (`crates/syntax/src/lower/`), but until L6 removes the parser's
  direct construction, every public parse function (`parse_module*`,
  `parse_expression*`, `parse_module_and_tree`, `parse_namespace_line`)
  does three jobs: the parser builds the compiler's tree (thrown away) and
  the marks, the tree builder builds the lossless tree (with trivia), and
  the lowering builds the compiler's tree again.
- **Why results stay the same.** The two routes are compared exactly, as
  `Debug` text with spans plus the diagnostics, by `stitchwort dev tree
  --lower` (`lower::oracle`): over all 2,983 `.sw` files in the repo,
  30,713 declarations and 34,376 one-line bodies and types parsed as
  expressions, 0 differences and 0 not lowered. The hash snapshots (`binary(library) &
  test(/hash_stability/)`) are unchanged.
- **Measured** (release CLI, `dev tree --time 5`, best of 5, `nice -n 15`,
  load average 3-4; two runs agreed within 0.1 ms):

  | | the parser alone (before) | with the lossless tree | through the lowering (after) |
  |---|---|---|---|
  | std, 2.12 MB | 54.1 ms | 63.4 ms | 85.0 ms (1.57x) |
  | std, `aoc/src`, `games`, `examples`, 6.88 MB | 163.9 ms | 191.4 ms | 256.3 ms (1.56x) |

  The design estimated 1.3-1.5x; the lowering itself is about 21 ms of
  std's 85. A `check` that loads std parses it once (`library.rs`), so a
  trivial check is about 30 ms slower [estimated from the table].
- **Bench.** _The orchestrator adds stitchwort-bench's numbers from the
  verifier's run on `main` here: both nesting programs' times and
  allocation counts, which change since the lowering allocates the
  compiler's tree a second time._
- **Not optimised.** Speed work is paused (D3465) and most of the cost goes
  with L6, which deletes the parser's own construction (end state about
  1.1-1.3x, [estimated] in the design). If trivia proves a noticeable part
  then, the compiler's route can build the tree without comments.
- **Stack.** The lowering takes the parser's stack limit and reports its
  `E-RESOURCE` if it runs out. Its frames per level of nesting are 5-43% of
  the parser's in release (measured per shape, `(` to `(.f `), after making
  the application and method-section path out of line and marking
  `function_type` and `effect` `#[inline(never)]`: inlined into
  `node_expr`, they had grown it from 96 to 816 bytes, so nested sections
  ran out before the parser did. The test
  `deep_nesting_lowers_within_the_parsers_stack` lowers each shape's
  deepest parse with a third of the stack to spare.

## 10 Nov 2026

### SW-2609: `ignorable_arguments` profiled in real proofs: not a hotspot (no change)

- **Problem.** SW-2606's profile of a soundness-fuzzer mutant (a bare
  `cases` in place of a proof, 64 contexts with huge hypotheses) found
  `ignorable_arguments` (`crates/elab/src/check.rs`), which reads back the goal
  and every hypothesis type at each `auto` argument, taking most of the CPU.
  The question was whether it costs anything in unmutated proofs.
- **Method** (measured). Release build (non-incremental), `stitchwort check
  --no-cache` of eight AoC proof namespaces picked by how often they use
  `cases` (Day16 `Sound.sw` most), sampled with macOS `sample` at 1 ms;
  inclusive samples of the checking thread, outermost frame only.
- **Result.** `ignorable_arguments` is 0.2% to 1.9% of the checking thread:
  Aoc.Year2021.Day16.Proofs 69 of 7,329 samples (0.9%, 12.2 s wall),
  Aoc.Common.Proofs 67 / 4,161 (1.6%, 5.7 s), Aoc.Year2021.Day05.Proofs
  77 / 4,125 (1.9%, 5.3 s), Aoc.Year2024.Day04.Proofs 7 / 3,372 (0.2%,
  4.3 s), Aoc.Year2024.Day24.Proofs 68 / 5,046 (1.3%), Aoc.Year2024.Day06.Proofs
  67 / 4,708 (1.4%), Aoc.Year2024.Day15.Proofs 84 / 5,441 (1.5%),
  Aoc.Year2021.Day18.Proofs 11 / 1,373 (0.8%). `cases` itself (all of
  `elab::cases`) is under 1% except Day04 (329, 10%). Most of the calls come
  from ordinary implicit `auto` arguments, not from `cases`.
- **Decision.** Not changed: at most about 2% to win, and the mutant case it
  was found in is already stopped by SW-2606's `E-CASES-BUDGET`. If it is
  ever worth doing, the cheap form is to cache the hypotheses' mention marks
  per context, reused while `cx.types` is unchanged (a case split refines
  earlier types, so the key must be the types, not the level), so each
  argument reads back only the goal.
### SW-2607: native compile time of nested `if`s is linear in instructions; no change (dropped)

- **Status:** measured, no code change. Sonnet.
- **Question.** SW-2579 found nested `if`s making the IR's value count grow
  faster than linearly (2.8k values at 1 `if`, 44k at 12, 77k at 20) and
  guessed that every register was carried into every join. Is native
  compile time a cost, and would passing only live registers to joins cut it?
- **Measured** (release CLI, `build --native --verbose`, Mac, the "compiled
  ... in N ms" figure; the programs are SW-2579's `nested_ifs`):

  | nesting | 1 | 4 | 8 | 12 | 16 | 20 | 24 |
  |---|---|---|---|---|---|---|---|
  | native compile, ms | 12.5 | 20.7 | 40.2 | 66.0 | 54.6 | 67.9 | 85.2 |

  Past about 12 levels a body is compiled in parts (SW-2557), so the time
  stops climbing steeply. At depth 20 it is 68 ms, under the 100 ms bar.
- **Real programs.** AoC 2024 day 15: 322 bodies, 477 ms of native
  compile of a 1.18 s `build --native`; day 24: 332 bodies, 465 ms; 2024
  day 21: 246 ms; 2021 day 18: 250 ms. So native compile is a visible share
  of a build, but it is not the nested `if`s. With a temporary timer around
  `define_function`: Cranelift's `define_function` is 89% of it (426 ms of
  477), at about 2 us an instruction in the real days (215,000 instructions)
  and in the depth-12 and depth-20 programs alike. Block parameters are
  27,000 of day 15's 315,000 values (9%); the depth-12 body has 5,766 of
  104,775. The rest of the value count is not live data: Cranelift's SSA
  builder creates a parameter for every variable at every join, then removes
  the redundant ones, leaving the value as an alias in the table. So the
  growth in values is dead entries, not extra work for the compiler:
  time follows instructions and blocks, which grow linearly with nesting.
- **Why no change.** Passing only live registers would remove at most the
  9% of values that are block parameters, and the redundant ones are already
  removed by the builder; no measurable gain on compile time, and it would
  touch every join in the lowering. Dropped. Any compile-time gain in real
  programs lies in the instruction count per body (the largest bodies,
  `lambda #34` of day 15 at 13,000 values and 17 ms, and `Warehouse.move`'s
  match), not in the joins.

### SW-2578: bench baseline re-recorded after 9 Nov's runtime work (four flagged regressions explained, accepted)

- **Problem.** The daily and full tiers flagged `run-machine-calls`
  allocations 247 to 441, `run-machine-loop` allocations 205 to 332 and
  peak heap 4 to 5 kB, `run-machine-aoc-2021-15-part1` peak heap 5.1 to 10.3
  MB, and `check-number-columns` steps 669,003 to 755,301 (+12.9%), while
  gains of up to -77% machine instructions weren't in the baseline. No code
  changed: the baseline was re-recorded (`--update`, release build, 10 Nov;
  `examples` and `extract-js` inputs changed too, 1498 to 1542 files and 56
  to 57).
- **Method** (measured). Bench of the two `run-machine` programs at chosen
  commits, in a scratch worktree, release build, counts only; the same for
  `check-number-columns` and `run-machine-aoc-2021-15`. Counts are
  deterministic, so one run each is exact.
- **`run-machine-calls`/`-loop` allocations: borrow inference (SW-2565 B1,
  `e687be8bf`), a per-run constant.** Calls 276 to 441 (+165), loop 214 to
  332 (+118) at that commit alone; nothing else moved by more than a few
  allocations. The benchmarks' counted region is `run_main_on`, which builds
  the image, and B1's `borrow::apply` (inference over every reachable body,
  a state vector and a pending map per body per pass, then the rewrite and
  check) now runs in it. The cost grows with the number of bodies in the
  image, not with iterations: the programs run 200,000 outer calls and 4
  million tail calls, and a total of 441 or 332 allocations can't scale with
  either.
  The few smaller steps before it are also constants: calls 247 to 255
  (8 Nov, before `3de6c1834`), +19 with SW-2405's sum loops (`96bf4836a`:
  the program's `1 + down n` becomes a loop, so machine instructions fell
  12.6% and peak heap 10 to 6 kB in the same step), +2 with SW-2531's inlining
  (`748dc58a3`). Loop 205 to 212 is also before 9 Nov. Not removed: 100 to
  170 allocations once per run is under 0.001% of a typical run's
  allocations (AoC days: 1 to 10 million) and well under a
  millisecond, and trimming them means restructuring B1's analysis (reusing
  `forward`'s buffers across passes) for no measurable gain. Accepted.
- **`run-machine-loop` peak heap 3.8 to 5.2 kB.** The inference's working
  set (the same constant, at its peak), nothing a run keeps. Accepted.
- **`run-machine-aoc-2021-15-part1` peak heap 5.1 to 10.3 MB: SW-2396
  (`3496aee5f`), intended.** `Graph.distances (index := ...)` keeps the
  costs in arrays: 5.3 to 9.6 MB at that merge, with allocations -44% and
  machine instructions -71% (54.0 M to 22.5 M). The cell cache (SW-2363) was
  the suspect and is not the cause: with `cell_cache::ENABLED` false the
  peak is unchanged at 10.3 MB. Accepted: a dense table is the point of
  the change.
- **`check-number-columns` steps 669,003 to 755,301: SW-2481 (merge
  `11ed0d905`), intended.** Case refinement now rebuilds substituted values
  keeping sharing and charges the steps for the rebuild. The lane's first
  version ran 959,829 steps and 1,575,835 allocations here; its review fixes
  (`e8fbef207`: keep unchanged calls, share spines, charge steps) cut that
  to 755,301 steps and 1,170,115 allocations (allocations +1.0% against the
  old baseline). The rest is the charge, which is the budget doing its job
  (a 256-arm Fin table went 86 s to 12 s, and a 200-arm unknown bound from
  out of memory to 15 s). `check-number-dependent` rose 6.6% in the same
  merge, under the threshold. Accepted.
- **Baseline changes** (new / old): `run-machine-calls` allocations 441 /
  247, peak 7 kB / 10 kB, instructions 26.8 M / 30.2 M; `run-machine-loop`
  allocations 332 / 205, peak 5 kB / 4 kB; `run-machine-set` allocations
  213,575 / 1,719,446 (-87.6%), instructions -12.3%; `aoc-2020-19`
  allocations -47.8%, instructions -20.6%; `aoc-2021-11` allocations
  -67.1%, instructions 173.4 M / 567.2 M (-69.4%); `aoc-2024-09`
  allocations -64.0%, instructions -23.1%; `aoc-2021-15-part1`
  allocations 1.30 M / 4.38 M (-70.3%), instructions 17.8 M / 78.7 M
  (-77.3%), peak 10.3 / 5.1 MB; `check-number-columns` steps as above; the
  new `examples` and `extract-js` fingerprints. Times (`time_ms`) in this
  file were recorded while other lanes were running tests, so they are
  rougher than usual (they are only compared by hand); re-record on a quiet
  machine when timing matters.

### SW-2572: `*` on a long run of `Succ`s around an unknown is linear, not quadratic

- **Cause** (profiled with macOS `sample` on the effect fuzzer's seed
  1794200310, the program shrunk by hand). All the time was in the
  elaborator's obligations loop evaluating `if v % 2 == 0`, inside
  `native::as_nat_with` forcing calls that were already unfolded
  (`force_now`, `Unfolding::get`, `Value::clone`). `(x + k) % 2` is
  `(x + k) - ((x + k) / 2) * 2`; the quotient is `k / 2` `Succ`s around a
  stuck division step, and `*` recurses on its left side one `Succ` at a
  time. At each step `native::run` walked the rest of the chain to see
  whether it was a number before falling back to the case tree: quadratic
  in `k`. The fuzzer's constants are near a million.
- **Change** (`crates/core/src/native.rs`; the evaluators' shared natives, so
  the kernel computes this way too; docs/core.md updated). (1) `Nat.mul`'s
  shortcut for unknowns: `(k + m) * n` for a number `n` is
  `k·n + m * n` in one step, stuck on `m`, which is what `k` steps of the
  definition give. (2) `native::run` forces every number argument's head
  first and stops when one is plainly no number, before walking a `Succ`
  chain in another, so `(k + m) * y` with `y` unknown doesn't walk the chain
  at each of the case tree's steps. Equal values are unchanged; a value
  stuck under `*` keeps its argument unforced, as the case tree does.
- **Measured** (release `stitchwort check --no-cache`, user time, machine
  shared with other lanes). `if (x + 16000) % 2 == 0 …` 10.1 s to 0.46 s;
  `((x + 16000) / 2) * 2` 11.6 s to 0.47 s; `((x + 16000) / 2) * y` 9.2 s
  to 0.56 s; the fuzzer's `let a := if (x + 16000) % 2 == 0 then 4 else 4;
  if a % 2 == 0 …` 16.9 s to 0.70 s. Seed 1794200310's module: over 10 min
  (its slow program alone over 20 s, stopped) to 4.3 s; seeds 1794200346,
  1794201674, 1794200163 and 43: 1.0 to 1.5 s each. The fuzzer's 200
  batches from 1794200000 (three of the slow seeds among them): 51 s, none
  out of resources. What's left grows
  linearly, about 13 µs a unit of `k` (`(x + 500000) % 2` forced fully
  takes 7 s): `Nat.divFuel` builds the quotient one `Succ` a step, as its
  definition does (see "Not done").
- **Not done.** A `Nat.divFuel` shortcut for unknowns (take `d` off `n`
  `q` times at once) would remove the linear part; it would be a new kernel
  shortcut with its own proof obligations, so it's proposed as a follow-up,
  not done here.
### SW-2579: native frame bounds from Cranelift's frame layout (x86-64 frames of 4 KB were put at 2 MB)

- **Status:** on branch `lane/SW-2579`. Opus.
- **Problem.** On Overmind (x86-64), five effect-fuzz batches were refused
  by native code: a lambda of about 20 nested `if`s had a "frame" of
  1.1-2.2 MB, and 2,000,000 frames of that pass the 64 GiB cap. Under
  `run --native` the same bound would not refuse but cut the frame limit
  to 30,000-57,000 frames (`native_frame_limit`).
- **Cause.** Not the frames: the measurement. `frames::frame_bound` read
  the frame from the prologue, and on x86-64 a frame of a page or more
  starts with stack probes, which the reader didn't know, so it took the
  IR fallback (stack slots plus 16 bytes for every SSA value). Nested
  `if`s make many values (each bytecode register is three variables, and
  each join block takes them as parameters: 77,000 values at 20 ifs), so
  the fallback grew with values while the real frame grew by about 160
  bytes an `if`. On aarch64 the reader used the unwind pseudo-instructions
  and was right, so the Mac never saw it.
- **Change.** The bound is Cranelift's own frame layout,
  `MachBufferFinalized::frame_layout().frame_to_fp_offset` plus the saved
  frame pointer and return address, on both architectures; the prologue
  readers are gone. The generated code is unchanged. On aarch64 the bound
  is the same except where a tail call to a wider callee grew the frame:
  the reader counted that growth twice (in `StackAlloc` and in the
  arguments term), so stubs' bounds drop by up to 48 bytes.
- **Measured** (widest body's bound in bytes; x86-64 compiled from the same
  IR by a cross-compiling ISA on the Mac; "before" on aarch64 equals after):

  | program | x86-64 before | x86-64 after | aarch64 |
  |---|---|---|---|
  | 1 nested if | 752 | 752 | 752 |
  | 4 | 944 | 944 | 944 |
  | 8 | 1,136 | 1,136 | 1,152 |
  | 12 | 1,328 | 1,328 | 1,344 |
  | 16 | 2,880 | 2,880 | 2,640 |
  | 20 | 3,520 | 3,520 | 3,136 |
  | 24 (heavier branches, the regression test) | 1,802,480 | 4,672 | 4,112 |
  | 28 (heavier) | 2,376,672 | 5,424 | 5,024 |
  | fuzz seed 1794200320 | 1,331,136 | 4,192 | 3,712 |
  | fuzz seed 1794201291 | 1,731,904 | 4,176 | 3,952 |
  | fuzz seed 1794201473 | 1,187,616 | 4,672 | 4,288 |
  | fuzz seed 1794300165 | 2,198,864 | 4,208 | 3,872 |
  | fuzz seed 1794301295 | 2,092,160 | 6,080 | 4,928 |

  The real frame grows linearly with nesting; past about 40 `if`s a body
  is compiled in parts (SW-2557) and the frame falls to about 1 KB.
  `task native:bench` (macOS, load average 12-18, best of 3, wall):
  set_nat 1.216 s, set_keys 0.310, micro_call 0.242, micro_tail 0.262,
  closures 0.336, effects 0.884; geomean 0.438 s. No earlier entry has
  these numbers to compare with; the code is the same, so no change is
  expected **[estimated]**.
- **Fuzzer.** A native refusal stays a failure, not a skip: generated
  programs' frames are a few KB, far from the 34 KB at which 2,000,000
  frames would pass the cap, so a refusal is a bug in native code, as
  here.

## 9 Nov 2026

### SW-2559: the cell cache's room is exact, so `full` doesn't walk

- **Cause.** `CellCache::full` recounted the held bytes by walking every
  cached block (a pointer chase over up to 64 MB) whenever the room ran
  out, because a take didn't give room back. Overmind (Linux, job 41):
  15% of cycles in binary-trees, 4.4% in rbmap after SW-2511 (LLC load
  misses 0.55 M to 3.8 M).
- **Change.** Native code's cache take adds the block's bytes back to
  `room` (load, add, store on the take's hit path, `n1.rs` `cached_cell`),
  so `room` is exactly `CAP` less the bytes cached. A full cache is then
  just a failed comparison: `full` frees the cell and walks nothing; the
  cut to half the cap is gone.
- **Measured (macOS, instructions, median of 3).** binary-trees +0.34%,
  rbmap +0.25%, rbmap-ck +0.21%, memory-game +0.31%, mapops -0.01%
  (the extra take work; no walk to save on this machine's runs). Wall
  time, best of 10, machine loaded by other lanes (so noisy, +-10%):
  binary-trees 1.37 s to 1.19 s, rbmap 1.54 to 1.35, rbmap-ck 0.86 to 0.82,
  memory-game 1.88 to 1.95, mapops 0.87 to 1.01. The time effect is the
  cache misses, which Overmind's counters should confirm.
- **Rejected.** (b) per-arity counts or a bound: still a walk or more
  state on the free path, for no gain over an exact count. (c) cutting
  lists at a counted point: needs the same walk to find the point, and
  throws away blocks the program will want again. Keeping the recount but
  rarer (cutting deeper) was not tried: the exact count removes the cause.
### SW-2565: borrowed parameters, stage B1 (mapops -6.4%, memory-game -19.3%, AoC geomean -2.3%)

- **Status:** on branch `lane/SW-2565`. Opus. D3441 (build it), D3442 (the machine checks
  borrows), D3443 (step and frame counts unchanged); O6 dropped (orchestrator's call from B0).
- **Problem.** A read-only walk over a structure the program keeps (a `Map` lookup, a list
  summed twice) incremented and decremented every node it passed: the caller's copy of the
  argument, then each field taken from a shared cell.
- **Change.** An inference over each global's bytecode (`crates/rt/src/borrow.rs`) marks the
  parameters a function only reads as borrowed; callers lend them (no count), and a rewrite
  makes each lent value's life explicit (`Peek`, `Lend`, `Forget`, `Own`), checked at compile
  time. Native code copies lent words with no counting; the machine keeps checked, untraced
  clones. Details and rules: docs/proposals/borrow-inference.md §12.
- **Measured** (`task bench:instructions --runs 3` against main at fdde41179, after the review's
  fixes and the rebase onto SW-2559): mapops -6.40%, memory-game -19.31%, expressions -3.10%,
  disk -2.42%, rbmap-ck -2.13%, dijkstra -1.49%, rbmap -0.26%, binary-trees +0.01%; geomean
  -4.59%. `task bench:aoc`: geomean -2.32% over 56 days, 11 days over 3% (2021/17 -11.7%,
  2024/06 -11.3%, 2020/08 -5.0%), none worse (worst 2021/07 -0.05%). Before the rebase, against
  d5bd2f09d: geomean -3.77%, AoC -0.96%, 2021/01 +1.16%. Peak memory unchanged on all eight
  programs (within 0.1 MB, measured before the rebase).
- **Rejected along the way** (measured, one run each; geomean of the eight):
  - The note's rules plus *merge*, without *fresh*: binary-trees +83% (its fresh tree, lent,
    was dropped whole by the runtime instead of freed into the cell cache as walked); +4.49%.
  - Plus *fresh*, with O1-O3 owning as written: expressions +1.30%; -3.52%.
  - O1-O3 owning only when some caller hands over an owned value at its last use: expressions
    +1.27%; -3.58%.
  - Any owned value handed over at its last use owning the parameter: mapops only -1.75% (the
    lookup walk's node, a field of a live tree, counted as handed over); -3.11%.
  - Fields of a fresh value counted as fresh through `Unpack`: rbmap-ck +1.65%, expressions
    +1.42%; -3.18%.
  - Kept: the last but one, except that a copy or a field of a value that stays live doesn't
    count as handed over (*fed*); -3.77% (3 runs, before the rebase).
- **Not done.** B2 (owned copies for O7/O8), B3 (lent reads of owned values), the JS backend.

### SW-2471: native recursion limit 16 million frames (const-fold depth 23 runs)

- **Status:** on branch `lane/SW-2471`. Sonnet. D3450 (Matt, 9 Nov 2026: limits may differ by
  runner).
- **Problem.** The frame limit was a fixed 2,000,000, shared by the machine and native code, so
  `bench/compare/const-fold` stopped with `E-RESOURCE` at depth 21 where Lean's original runs
  depth 23 on a 4 GB stack, and ran at depth 20 in the comparison.
- **Change.** Native code has its own ceiling, `Limits::native_frames` (16,000,000), and a run
  enforces `min(ceiling, (64 GiB cap - rooms) / widest frame - 1)`
  (`native_abi::native_frame_limit`, `Limits::for_native`). The machine keeps 2,000,000. The
  native stack was already mapped lazily, and the limit is a runtime value the frame check
  compares against, so the generated code is unchanged. A program with wide frames is no longer
  refused: it gets the most frames the cap holds. The same program on the same build still fails
  at the same depth.
- **Measured** (release CLI, `run --native`, one run each; time wall, memory peak resident set):

  | const-fold depth | time | peak memory |
  |---|---|---|
  | 21 | 0.86 s | 1.08 GB |
  | 22 | 1.54 s | 2.06 GB |
  | 23 | 2.87 s | 4.00 GB |

  Runaway recursion (`count n = 2 * count (n - 1)` from 20,000,000, 380-byte frames): native
  fails with `E-RESOURCE` at 15,999,999 frames pending after 1.4 s with a 6.1 GB peak; the
  machine fails at 2,000,000 after 0.3 s with 0.58 GB. Instructions are unchanged **[estimated]**
  (the earlier experiment, a patch with the same limit, measured no instruction cost; this
  change did not re-measure instructions).
- **Cost.** A runaway native recursion now uses up to about 8 times the memory before failing
  (6 GB here; a program with wide frames can use more, up to the 64 GiB address space the
  limit allows, and the machine's memory then decides). The roguelike's widest frame is 4,776
  bytes, so its limit is 14.4 million.
- **Rejected.** A byte cap beside the frame limit (the earlier lane's option): not built; the
  frame counter stays exact and deterministic, and SW-2558 adds a flag to lower the ceiling.

### SW-2543: `stitchwort test --native` (tests as native code; 2021 day 15's tests 3.7x faster)

- **Status:** on branch `lane/SW-2543`, behind a flag (`test --native`); the default flips in
  N6 (docs/reviews/SW-2535-native-default-plan.md). Opus.
- **Problem.** `stitchwort test` ran every test on the machine. Native code runs AoC days 2-3x
  faster, but `test` had no native path.
- **Change.** The tests lowered together are compiled once, with each test constant a root
  (`n1::compile_roots`, an entry trampoline per root), and each test's value is computed by
  `NativeExecutor::global` as the machine's `Machine::global` computes it. A test native code
  can't run goes to the machine. Results are cached under native code's own key (not the
  machine's): its recursion limit is deeper (SW-2471), so outcomes at the limit differ.
- **Measured** (release CLI with `dev` features, best of 3 by instructions; `test X
  --verify-cache`, which reruns every test with the check cache warm, less a fully cached `test
  X`; load average 4-10):

  | Tests | Machine: instructions, wall | Native: instructions, wall | Compile (in native) |
  |---|---:|---:|---:|
  | AoC 2021 day 15 (18 tests, real input) | 85.9 G, 5.89 s | 22.3 G, 1.61 s | 259 bodies, 0.43 s |
  | AoC 2024 day 9 (32 tests, real input) | 14.1 G, 1.00 s | 8.4 G, 0.68 s | 321 bodies, 0.48 s |
  | AoC 2020 day 21 (10 tests, real input) | 10.7 G, 0.70 s | 6.6 G, 0.48 s | |
  | `examples/accept/text.sw` (58 small tests) | under 0.01 G, under 0.01 s | 0.44 G, 0.04 s | 69 bodies, 0.035 s |

  So 3.7x on a day whose tests compute a lot, about 1.5x on a typical day, where compiling is
  most of what native code spends, and 30-40 ms more on a file of small tests (the whole
  command: 2.36 G, 0.23 s -> 2.80 G, 0.27 s). Uncached (`--no-cache`, checking included) 2021 day 15 went from
  12.6-13.2 s to 8.0-8.7 s, and 2024 day 9 from 5.6-5.8 s to 5.3-5.5 s.
- **Not done.** No threshold below which small test files stay on the machine (§3.6 of the
  plan): 30-40 ms didn't seem worth a rule. Compile time is now the larger part for a typical
  day (lane J of the plan).
- **Links.** SW-2543, SW-2535.

### SW-2557: native compile time and memory on very large bodies

- **Status:** on `lane/SW-2557`, for review. Opus.
- **Problem.** `run --native` on float_paths' generated program (484 KB, one constant
  `results` that is a 20,161-element list literal) ran over 100 s and reached 17.9 GB before
  it was stopped; the machine runs it in 1.9 s at 260 MB.
- **Profile** (macOS `sample`, measured). At 250 elements: 10 s and 1.9 GB, three quarters of
  it in Cranelift's `seal_all_blocks` (`remove_block_param`), the rest in `define_function`.
  The body's Cranelift IR grew with the square of the list: 60 K, 224 K, 850 K lines at 25, 50,
  100 elements. Cause: `Gen::exit_now_untagged` (`crates/native/src/n1.rs`) writes every
  register that may hold a value to the spill slot at each error exit, and a call has three
  (`count_step`, `push_frame`, `call_result`); a list literal holds every element in its own
  register until the list is built, so each element's call wrote out all the elements before
  it, and each such use of a register variable made the SSA builder thread it through every
  block. The frame grew with the registers too (75 KB at 250 elements, over the 64 GiB stack
  cap at the 2 M frame limit). `maybe_full` would also have needed registers times
  instructions bits (about 0.7 GB at full size).
- **Change.** A body with more than 128 registers or 512 instructions keeps its registers in
  a heap register file laid out as the machine's register vector (`sw_regs_new`); an exit
  hands the whole file to `sw_unwind` and a release drops it whole (`sw_release_down`), the
  registers holding nothing being `Erased`. That alone made the IR linear but Cranelift's
  register allocator still grew faster than the function (5,000 elements: 14.5 s, 2.5 GB),
  so such a body is also compiled in parts of at most 512 instructions, each a function that
  tail-calls the next with the frame's state. Then, within such a body, exits holding nothing
  outside the registers are shared per error (5.2 s to 3.5 s at 5,000 elements) and a write
  skips dropping the old value when no earlier instruction fills the register (`first_fills`;
  IR 230 K to 170 K lines at 500 elements, little time). Part sizes of 128 and 512 measured
  the same (2.74 s, 2.80 s at 5,000 elements); 2,048 took 4.8 s.
- **Measured** (wall time and peak RSS of `run --native --no-cache`, one run each, a shared
  machine; before stopped at 6 GB):

  | program | before | after |
  |---|---|---|
  | float paths, 250 elements | 16.4 s, 1.9 GB, refused (stack over the cap) | 2.4 s, 142 MB (compile 0.40 s) |
  | 2,000 elements | stopped at 6 GB after 7.4 s | 3.4 s, 178 MB (compile 1.2 s) |
  | 20,161 elements (the repro) | stopped at 6 GB after 5.4 s | 13.7 s, 316 MB (compile 11.5 s) |

  Compile time is now linear: about 0.55 ms per element. Of what is left, Cranelift's
  register allocator is about half and its IR verifier about a quarter.
- **Normal programs unchanged.** No body of dijkstra (2021 day 15, 196 bodies) or Rogue (259)
  passes either bound (the largest have 41 registers and 168 instructions), and their machine
  code is byte for byte the same before and after (`STITCHWORT_NATIVE_DUMP`); compile times
  (0.33-0.37 s and 0.45-0.48 s before) were within the machine's noise after.
- **Links.** SW-2557; test `crates/native/tests/it/large.rs` (fails on the old code: 109 s, then
  the frame check).

### SW-2524: skipping the live heap's free at exit (dropped: under 0.3%)

- **Status:** dropped, no code merged. Sonnet.
- **Problem.** About 32-38% of `rbmap-ck`'s cycles are in `value::free` (SW-2523). The suspicion
  was that much of it tears down the heap that is still live when the process ends, which Lean
  doesn't do.
- **Change tried.** A process-wide switch (`leak_live_heap_at_exit`, set by the standalone
  executable's `main` and by `run --native`, never by the tests or the `alloc-trace` and
  `value-census` builds, and overridden by `STITCHWORT_FREE_AT_EXIT`) that `run_on` consults to
  `forget` the runner, and with it the executor's globals, constants, cell cache and tables,
  instead of dropping them. The same binary then runs both ways, so the exit share is the
  difference between the two.
- **Measured** (instructions, 3 runs, native; freeing at exit against skipping it):
  `rbmap-ck` 10.48 G -> 10.45 G (**-0.21%**), `rbmap` -0.08%, `binary-trees` -0.01%, `mapops`
  +0.03% (noise), `const-fold` -0.25%; AoC 2024/05 -0.02%, 2024/10 -0.07%. Wall time and peak
  RSS for `rbmap-ck` (1.82 s, 1.26 GB) and `binary-trees` (1.38 s) were identical to the
  hundredth of a second with the switch on or off. All under the 3% bar.
- **Why it is small** (inferred, not separately measured). What `main` returns is a unit and its locals, including `rbmap-ck`'s
  kept versions, die when `main`'s own native frame ends: those frees run inside the program, so
  they are not teardown and Lean's `main` would do them too. What is left to drop afterwards
  (globals, constants, the cell cache, the closure tables) is small.
- **Therefore** the `value::free` share in `rbmap-ck` is the program's own frees (SW-2523's cold
  child loads), not exit teardown. Skipping it would need a different change: freeing the kept
  versions would have to be dropped from the program's end of `main` itself, which is a trick that
  doesn't generalise (a program's locals dying at `main`'s end is ordinary semantics).
- **Links.** SW-2524, SW-2523; no commits kept beyond this entry.

### SW-2511: a handler's step is one dispatch closure (compiled handler dispatch, stage 1)

- **Status:** on branch `lane/SW-2511`, not yet merged (commits `52da722ff`, the dispatch, on the
  cherry-picked SW-2507 spike `10aa4bf6d`; `200f2d6d9`, the `Unpack` change). Opus.
- **Problem.** Every operation a handler answered went through two partial applications
  (`handlePlus (A.%elim c₁ … cₙ) forward`); applying one copies everything it holds, so each
  operation copied all the clauses and dropped all but one, and a fused state clause was then
  partially applied once more. Profile (SW-2493, `tick`): about a third of an operation's 5.7 K
  instructions, plus 0.47 K more for an eight-operation ability. Each handler start built a
  closure per clause and the two partial applications.
- **Change.** `crates/rt/src/dispatch.rs`: in the runtime's lowering, the step becomes one closure
  of `o, k` (and `jump, s` for a fused state handler) whose body is `handlePlus`'s and `%elim`'s
  case trees with the clauses inlined in the arms; the forward, whatever its variant, is inlined in
  the `R` arm. Named `Owner/dispatchN` in profiles.
  Second commit: an `Unpack` names the fields its arm doesn't use, so native code frees a unique
  cell inline into the cell cache instead of out of line; the dispatch had exposed this (a clause's
  unused argument), and any `match` arm that ignores a field gains from it.
- **Why results stay the same.** The rewrite is β/η on the checked term in `crates/rt` only: kernel
  terms, hashes, the elaborator and JS are untouched; the effect loop does what it did. Machine
  steps (frames entered) fall by two per operation answered (D3440). The `Unpack` change frees
  the same values in the same order. Checked by rt (66), native (70), js (14), the effect/handler
  tests (80, both runtimes' allocation traces agreeing, with rebuilds checked too),
  `every_example_lowers`, the million-element shapes, and the hash tests (14).
- **Measured** (instructions, against `2cce80c5b`; dispatch alone, then both): expressions
  −23.8% / **−25.5%**, scan −29.7% / **−30.4%**, bridge −20.3% / **−21.2%**, disk −11.9% /
  **−13.8%**, matcher −4.1% / **−3.9%**, binary-trees and mapops (no handlers) −0.0% / −0.4%;
  geomean −13.6% / **−14.4%**. `bench:aoc` geomean −10.0% / **−11.0%**, 36 / 38 days moved over
  3%, 22 over 10% (up to −30.6%), none up more than 0.24%. The `Unpack` change alone is −1.2%
  geomean on AoC, between −9.8% and +2.3% per day. §6's estimate was −11.5% / −14.5% on the two
  parsers; the spike's call counts explain the difference (the new apply is the cache's fast path).
- **Not done / rejected.** JS keeps its lowering (D3440's third question; it copies nothing per
  operation). The runtime clause table and an elaborator change were rejected in the note (§2.7).
  Stages 2 (the loop calls the dispatch's code directly) and 3 (a jump as a return) are still open.
- **Links.** SW-2498, SW-2507, SW-2511, SW-2525;
  [../proposals/compiled-handler-dispatch.md](../proposals/compiled-handler-dispatch.md) ("Stage 1b
  results").

### SW-2531: inline a function for its context (a selector's result taken apart at once)

- **Status:** merged 9 Nov 2026 (748dc58a3). Opus.
- **Problem.** SW-2513 target 2 (and SW-2371's "cause 2"): `Map.Tree.balance`
  is `rebuild (shape l r) l key value r`. `shape` (65 IR nodes) and
  `rebuild` (38) were too big for the inliner's 24-node limit, so every
  level of an insert made two calls: `shape` worked out the sizes and
  returned a `Shape` constant, and `rebuild` tested it and worked the sizes
  out again to build the node. The brief's premise, that the old node's cell
  was not reused because the `Bin` is built in another body, no longer holds:
  SW-2391's reuse across calls already passes the token down to
  `rebuild[reuse]`, and an alloc trace of the pattern allocates no more than
  the fused version, before and after this change. What was left was the
  calls and the `Shape` round trip: in the SW-2513 profile (after the record
  fix) `shape` and `rebuild` are 1.7 G + 1.4 G of 12.6 G instructions. A
  hand-fused `insertWith` measured 9.39 G (SW-2513).
- **Change.** `opt.rs`, GHC's "interesting context" discount, in two rules
  with their own caps (`CONTEXT_SIZE` 80 nodes for the function,
  `KNOWN_PUSH_SIZE` 96 for what case of case copies):
  - a non-recursive function whose leaves are all constructors of trivial
    fields (a *selector*, like `shape` or a `compare`) is inlined where its
    result is bound and taken apart at once, if the arms its leaves would
    take come to at most 96 nodes;
  - a non-recursive function whose body is a match on a parameter (like
    `rebuild`) is inlined where that argument's constructor is known, or is
    a call of such a selector, or an inlined one;
  - case of case into leaves that are all constructors is costed by the arm
    each leaf takes (the copy keeps only that arm), not by the whole match
    times the leaves.
  `balance` becomes one 126-node body that tests the sizes once and builds
  the unrotated node itself (and gets a reuse copy, `balance[reuse]`); the
  rotations stay calls. No std source changed.
- **Why results stay the same.** Inlining and case of case are the
  simplifier's existing rules, applied in more places; everything they move
  is pure and total. Kernel terms are untouched (hash tests pass). Checked by
  every `bench:instructions` and `bench:aoc` answer (all ok), rt and native
  lane tiers, `alloc_trace`/`reuse::`, `every_example_lowers`; a new IR test
  (`reuse::balance_builds_its_node_itself`, fails before) and an alloc-trace
  test against a hand-fused tree.
- **Measured.** `bench:instructions --runs 3`: mapops 12.66 -> 9.67 G
  (-23.6%; the hand-fused version is 9.39 G), dijkstra -4.7%, disk -3.6%,
  rbmap -0.2%, binary-trees -0.2%, bridge -0.1%, expressions -0.05%; geomean
  -5.0% over the seven. `bench:aoc`: geomean -1.30% over 55 days, all ok; 9
  days moved more than 3%, all down: 2020/08 -17.5%, 2020/14 -9.9%, 2020/01
  -7.8%, 2021/05 -6.3%, 2020/09 -5.5%, 2024/06 -4.7%, 2021/14 -4.4%, 2021/15
  -4.2%, 2024/05 -4.0%. The largest rise is +0.63% (2025/06, whose IR is
  unchanged: noise).
- **Code size (measured, IR nodes after reuse copies).** +2.09% over the 55
  AoC days and three bench programs (397,316 -> 405,621); most programs
  unchanged, the largest 2021/15 +11.9%, 2024/16 +8.9%, 2024/09 +6.0%,
  mapops +5.3%.
- **Not done.** `balance` itself (126 nodes) is still a call from
  `insertWith`; inlining it there too would take mapops towards the fused
  9.39 G (estimated a further 2-3%) at about 250 more nodes per Map
  instance, and needs a rule of its own (inlining a big function into a body
  that holds a reuse token it would use). Not tried.
- **Links.** SW-2531, SW-2513 target 2, SW-2371 cause 2, SW-2391 (reuse
  across calls).

### SW-2530: borrow inference stage B0, measured (dry run, no behaviour change)

- **Status:** merged pending review (`lane/SW-2530`). Sonnet. Measurement only.
- **Problem.** The note [../proposals/borrow-inference.md](../proposals/borrow-inference.md)
  estimated 3.5-5.5% of mapops and 5-12% of dijkstra from borrowed parameters, from earlier
  profiles; D3441 made building B1 depend on a measurement (gate: 3% on mapops or
  dijkstra, or 1% median on bench:aoc).
- **Change.** A dry-run inference over the bytecode (`crates/rt/src/borrow.rs`) and a machine
  counter behind cargo feature `borrow-counts` that counts the increments and decrements
  borrowing would remove or add (`borrow/shadow.rs`); `dev/borrow-counts` and
  `dev/borrow-counts-report` run and tabulate. Off in every shipped and test build.
- **Why results stay the same.** The counter only observes; answers of all runs matched.
- **Measured** (counts exact, instruction conversion estimated from a native micro-benchmark:
  13.5 per counted inc/dec, 5 per plain; counts validated at 2 increments per lookup level):
  mapops 6.75% (rules as written), 9.1% (O6 dropped); dijkstra 2.5%; disk 2.0/3.2%;
  memory-game 0/13.8%; const-fold 1.7%; binary-trees 1.8%; the rest under 0.6%. bench:aoc
  sample of 27 days: median 0.74% (b1), 0.87% (O6 dropped), 1.51% (with owned copies), max 21-29%.
  No geomean change measured (nothing changed in the compiler).
- **Verdict.** Gate passes on mapops: build B1, with O6 dropped. dijkstra is below 3% alone.
  Rejected finding: O6 as written leaves the specialised `get` walk's tree owned, because the
  optimiser lifts the `match` on `compare` into a function taking the node's value as an owned
  parameter.
- **Links.** SW-2530, SW-2518; note section 11.

### SW-2514: a record update takes a unique record's fields apart first

- **Status:** merged (`44beef6e9`). Opus.
- **Problem.** `{ w | f = g w.f }` on a uniquely held record read the field and
  kept `w` alive while `g` ran, so `w.f` was shared and every in-place reuse
  inside `g` was lost. Profile (SW-2513,
  [../reviews/SW-2513-mapops-profile.md](../reviews/SW-2513-mapops-profile.md)):
  `mapops` (Std.Map, 24.2 G instructions, 2.38 s against Lean's 0.31 s) is 48%
  too slow for this alone; measured by rewriting the program without the
  update. It affects every program that keeps state in records, which is AoC's
  house style.
- **Change.** `opt.rs` `take_apart`: an expression that reads a field of a
  one-constructor variable and uses the variable again gets one `match`
  around it, so a unique record gives up its fields unshared and its cell is
  reused.
- **Why results stay the same.** Only sharing changes: the match binds the same
  fields the projections read, and a shared record takes the same path as
  before. Checked by rt (66), native (70), hash snapshots,
  `every_example_lowers`, the million-element shapes and extraction (80).
- **Measured.** mapops 24.23 -> 12.65 G (-47.8%); bridge -4.5%, disk -1.9%,
  expressions -1.8%. `bench:aoc` geomean -2.59%, 14 days over 3% (up to
  -18.7%), none up more than 0.38%.
- **Not done.** The SW-2513 profile also found a fused balance worth a further
  -25.6% of mapops (measured by hand): filed as SW-2515 (inline balance into
  insertWith/remove so the old node's cell is reused). Read-only walks
  (SW-2516) stopped at design: no library-only fix, since an accessor fails
  the termination check and a nested match folds back into one unpack; the
  answer is borrow inference
  ([../proposals/borrow-inference.md](../proposals/borrow-inference.md), est.
  4-5% of mapops).
- **Links.** SW-2513, SW-2514; [../reviews/SW-2513-mapops-profile.md](../reviews/SW-2513-mapops-profile.md).

### SW-2523: rbmap-ck got 16% slower at unchanged instructions (accepted regression)

- **Status:** accepted regression, investigated, not fixed. The cause is
  SW-2502's side effect below; SW-2502 stays.
- **Evidence.** Overmind job 36: `rbmap-ck` native 1.55 -> 1.80 s (+16.2%)
  between `7d137b9d7` and `11f9f73ca`, instructions identical, `rbmap`
  unchanged. Bisect (job 37): first bad merge `0fdc931a7` (SW-2502). Cycles
  4.68 -> 5.11 G (+9%), IPC 2.27 -> 2.08, LLC misses flat, L1 misses +3%.
  `perf record` (job 38): about 80% of the extra cycles are one load in
  `value::free` (the child cell's count, before freeing it). `free`'s code is
  identical and `sw_static_closure` has no samples, so it is not the shared
  closure path.
- **Reading (orchestrator).** A data-layout effect: closures are no longer
  allocated per call, so the allocator hands out a different block pattern, and
  freeing the kept versions walks colder cells. About 30-38% of
  `rbmap-ck`'s cycles are in `value::free`, much of it the final teardown.
- **Decision.** Accept: SW-2502 is a net win everywhere else. Follow-up
  SW-2524 (skip freeing the live heap at process exit, as Lean does) addresses
  the cause for any program that ends with a big structure; l2 counters not
  yet taken.
- **Lesson (orchestrator's reading).** Instruction counts can hide a time regression when allocation
  patterns change; check the wide set's time on Overmind after allocation
  changes.
- **Links.** SW-2523, SW-2524; job 36 in docs/reviews/SW-2295-comparative-speed.md; the job 37 bisect and job 38 profile are on SW-2523.

### SW-2512 and SW-2481: checking speed (elaborator, not native code)

- **Status:** both merged (`11ed0d905`, `c0a70bcff`). Opus.
- **SW-2481 problem.** Deep `Fin` case chains cost about k^3-k^4 to check:
  `families::enter` substituted through the whole context at each `FSucc` step
  (k=20 0.3 s, 64 about 2 s, 100 about 9 s, 200 over 3 GB with an unknown
  bound).
- **Change.** `check::Rebuild` rebuilds substituted values keeping sharing
  (nodes stay identical), with a memo for spines and budget steps.
- **Why safe.** It touches trusted code (`check.rs` substitute,
  `unify_index::solve`), so an independent Opus review
  ([../reviews/SW-2481-rebuild-review.md](../reviews/SW-2481-rebuild-review.md))
  found no soundness bug and asked for fixes F1 (unchanged parts kept, which
  would otherwise undo SW-1106), F2 (spine memo, else exponential on shared
  spines), F3 (budget steps), F5 (tests, including a memo-off failure
  check); all merged. Values are node-identical, hashes unchanged.
- **Measured.** 256-arm `Fin` table 86 s -> 12 s (known bound), 200 arms with
  an unknown bound out-of-memory -> 15 s (36 s for 256). Ordinary code within
  1%.
- **SW-2512 problem.** A chain of shared lets followed by a `match` was
  exponential, on `main` before SW-2481 too: the equation generator
  (`equations.rs` `find_rhs`/`read_leaf`) substituted lets into a right side of
  about 2^n nodes before its size rule turned it down.
- **Change.** `zeta_size` counts first; `READ_CAP` of 65,536 nodes (and 10x the
  arm) skips before building, with a new skip reason (`docs/syntax.md`).
  Not trusted code.
- **Measured.** 16 lets 1.1-1.8 s -> 0.21 s; 20 and 40 lets (OOM) -> 0.21 and
  0.26 s.
- **Accepted loss.** Rows with a small branch of a huge let body (13-15 lets)
  lose their equation; keeping them needs lets kept through branch steps
  (filed, SW-2520).
- **Dropped: SW-2505.** `check_case` builds the scrutinee's display string for
  every case (about 8% of a deep table's time per a profile). Made lazy on
  `keep/SW-2505-lazy-scrutinee` (`503b8bcb3`): no measurable gain on a 64-arm
  table (0.36 s both), and printing after `enter` could show a solved
  metavariable differently. Dropped for no measured benefit.

### SW-2510: R7 merged; reusing the moved resumption's cell not merged

- **Status:** R7 merged (`6475d6c5d`, commit `bffe9030c`); cell reuse not
  merged.
- **Problem and change.** After SW-2499, forwarding an operation through a
  handler rebuilt a new operation cell each level (R7 in
  [effect-runtime-allocation.md](../proposals/effect-runtime-allocation.md)).
  Rebuilt forwarded operations now reuse the cells of the one they rebuild.
- **Why safe.** Only allocation changes; rt (65), native (70), effect/handler/
  resumption tests (79) pass; allocation traces agree.
- **Measured.** expressions -0.90%, scan -0.32% (estimate was -1.2 to -1.5%
  expressions: under the bar).
- **Not merged.** Reuse of the moved resumption's own cell (R3-style), commit
  `080bdf710` on `keep/SW-2510-cell-reuse`: -0.1 to -0.4%, native-only, and it
  needs a thread-local holding an emptied cell. Complexity for a gain inside
  the noise.

### SW-2502: capture-free lambdas built once

- **Status:** merged (`0fdc931a7`). Stage 1a of
  [../proposals/constant-hoisting.md](../proposals/constant-hoisting.md).
- **Problem.** A lambda with no captures was rebuilt at every use: `optional`
  builds nine per start, at 159 instructions each. Every program pays.
- **Change.** `Instr::StaticClosure`: a capture-free lambda is built on first
  use and shared for the run. The statics table holds a reference, so
  in-place reuse never touches the shared closure.
- **Why safe.** A capture-free closure is a pure value; sharing it changes only
  allocation counts (the orchestrator's call: stage 1a cannot change results,
  effects or step counts, so it did not wait on D3438/D3439). rt (65), native
  (70), hashes (14). JS unchanged.
- **Measured.** expressions -5.25%, scan -4.89%, bridge -5.31%, disk -3.61%
  (estimate expressions -3.5 to -3.9%); `bench:aoc` geomean -2.07%, 17 days
  over 3%, none slower than 0.08%.
- **Cost.** rbmap-ck time +16% at equal instructions (SW-2523 above,
  accepted).
- **Later stages** (1b literal folds, 2 floating pass, 4 unrolling `pick`)
  wait for Matt's D3438/D3439.

### SW-2499: a resumption nothing else holds has its fields moved

- **Status:** merged (`4dd2beaa8`). From SW-2493.
- **Problem.** `sw_resume_begin` copied the fields of a resumption even when
  nothing else held it. SW-2493
  ([../reviews/SW-2493-parse-operation-cost.md](../reviews/SW-2493-parse-operation-cost.md))
  accounts one Parse operation at 12-17 K instructions and 17-24 objects
  (5.7 K floor at depth 0, forwards +1.4-2.1 K each) and ranked this cut.
- **Change.** `Resume::take_unique` moves an unshared eager resumption's fields
  (the cell is left as `DoneK`), in native `sw_resume_begin` and in the
  machine, whose allocation traces must agree. The unsafe read was checked in
  review: fields are inline and the cell is forgotten.
- **Why safe.** Uniqueness is the same test every in-place reuse uses; shared
  resumptions still copy. rt (65), native (70), effects (79).
- **Measured.** expressions -3.36%, scan -2.59%, bridge -1.24%, disk -0.68%
  (estimate -3 to -5% and -2 to -4%).
- **Follow-up.** SW-2509: the value census counted a moved resumption as
  allocated `Fun::Resume` but freed as `Fun::DoneK`; per-kind balance fixed.
- **Not done here.** R7 and cell reuse (SW-2510, above).

### SW-2507: compiled handler dispatch spike (held for Matt)

- **Status:** measurement only, not merged. Prototype on
  `keep/SW-2507-dispatch-spike`; the measurement section is in
  [../proposals/compiled-handler-dispatch.md](../proposals/compiled-handler-dispatch.md).
  Stage 1b (SW-2511) waits for Matt's decision (D3440): shipping lowers step
  counts, which is user-visible.
- **Problem.** SW-2493: reaching a clause through `handlePlus` + `%elim` of 8
  clauses costs 1.85 K of the 5.7 K instruction floor per operation.
- **Spike.** Compile dispatch to a direct jump on SW-2493's scratch loops.
  Go criterion: Tick <= 5,080 instructions per operation and the eight-
  operation ability within 100 of Tick.
- **Measured.** Tick 5,671 -> 3,458; eight-operation ability within 17 of
  Tick; forward levels unchanged; outputs match. On the real programs:
  expressions 235.80 -> 177.99 G (-24.5%), scan 263.47 -> 186.92 G (-29.1%).
- **Open.** The prototype lacks tests, snapshots, profile names, machine/native
  agreement and the extra cell per route (SW-2511). A prior-art review is
  running (SW-2525).

### SW-2495: `pick` notes all its words in one operation

- **Status:** merged (`1486073cb`). Library-only. From SW-2492 target 3
  ([../reviews/SW-2492-expressions-scan-profiles.md](../reviews/SW-2492-expressions-scan-profiles.md)).
- **Problem.** `pick` noted its failure words one operation each.
- **Change.** One `Literals` note with all the words. The new internal
  constructor `Parse.Problem.Literals` is deliberately not user-facing API
  (nothing outside `Parse.sw` matches on `Problem`).
- **Why messages stay identical.** `shown` returns a list; the order was
  checked in review (expected is reversed then concat-mapped). 171 tests
  (hashes, std self-test, parse) and 4 `pick`-using AoC namespaces.
- **Measured.** scan -5.69%, expressions -0.88%, disk and bridge about 0.
  `bench:aoc` geomean -0.27% (2020/04 -4.3%, 2024/03 -5.7%), none slower.
  Estimate was scan -7 to -13.6%, expressions -3 to -6%: under it.

### SW-2494 (dropped) and SW-2497: literal character lists built once

- **Status:** SW-2494 dropped; its general form is SW-2497, a design note
  (`a1ab95d71`) and then SW-2502 above.
- **Problem.** `Parse.text`/`pick`/`literal` run `Text.toList` on a literal per
  try (3.28 M times on scan, 6.02 M on expressions). Hoisting by hand at the
  call site measured scan -5.8%, expressions -3.9%.
- **Tried.** The lane first stopped at 5 min: a library-only fix is
  impossible, since `text`/`pick` are plain calls with no per-parser value to
  hold the list. Option A (a new Parse operation `literalText` that walks the
  `Text` with `uncons`): expressions +0.92%, scan -3.23%; the walk costs about
  2 K per call, about what `toList` did. Net loss, dropped; diff in the
  orchestrator scratchpad.
- **Left.** Option B (native `Text.stripPrefix`) not tried. Option C, a
  compiler that lifts closed constant subterms (SW-2497), is the general fix
  and helps all code; stage 1b of the note.

### SW-2491 and SW-2487: `many` reuses marks and builds no closures per round

- **Status:** merged (`940382185`, `5707dc374`). Library-only.
- **Problem.** SW-2484 (disk and bridge profiles,
  [../reviews/SW-2484-disk-bridge-profiles.md](../reviews/SW-2484-disk-bridge-profiles.md),
  target 5): each round of `many` set a mark, then `optional` set another at
  the same state. SW-2491 swept every Parse combinator for the same kind of
  redundant operation.
- **Change.** SW-2487: `manyFuel` passes its round's mark to `optionalFrom`
  (`optional p = optionalFrom mark() p`, same state). SW-2491: each round's
  closing mark is the next round's opening mark, and a round's `rest`/`end`
  are arguments, not closures.
- **Why safe.** Statements `readsMany`/`runsMany` unchanged; helper lemmas
  replaced (`manyFrom` versions, `runsFromBindAt`); statements checked by the
  orchestrator (D2436). Audit Std.Parse 297/297, std self-test, 130
  parser-using AoC namespaces checked.
- **Measured.** SW-2487: disk 78.46 -> 72.66 G (-7.38%), bridge 102.23 ->
  96.20 G (-5.90%). SW-2491 on top: disk -12.2%, bridge -9.4% (both totals);
  `bench:aoc` geomean -4.12%, 22 days over 3% (up to -21.7%), none slower than
  1.2%.

### SW-2488 (dropped): `replicate k x ++ rest` without the copy

- **Status:** dropped before building (stopped at the bar as briefed).
- **Why.** Profiled after SW-2485: `List.append` is 1.0% of disk (2.1% before
  minOr) and `replicate` 1.3%, and disk's `blocksFrom` proofs rewrite against
  the `replicate ++` shape, so a std function would cost proofs and docs for
  at most 1%. Estimate had been -2 to -3%.
- **Revisit with** a general append-fusion rule, which gets it for free.

### SW-2486: a fused `natToken` operation (held for Matt)

- **Status:** built, not merged (`lane/SW-2486`, `da350645d`, worktree kept).
- **Problem.** SW-2484 target 2: bridge is 83% parsing, and a `token nat` is
  three marks and three spans.
- **Change.** A Parse operation `spacedNat` (one pass: spaces, digits, spaces)
  and public `Parse.natToken`; 22 proof arms (Reads 9, Runs 13), state-level
  theorem `spacedNatBySpans`, 16 hash snapshots; statements unchanged.
- **Measured.** Bridge 102.18 -> 80.56 G (-21.2%); disk +0.56% (the longer
  operation table).
- **Why held.** New user-visible std API, and the gain needs every `token nat`
  call site rewritten to `natToken`, including bridge's own source (2024 day
  7): a benchmark sped up by editing it, the over-fitting Matt warned about.
- **Recommendation.** Keep the operation and make `token nat` itself use it
  (specialise `token` on `nat`) so unchanged code gets the gain, plus
  Reads/Runs lemmas. Rebase on SW-2487/SW-2491 and regenerate snapshots
  (`task snap:hashes`) if it goes ahead.

### SW-814 (dropped): fused Map balance

- **Status:** dropped. Attempt on `keep/SW-814-fused-balance` (`69e17c6b2`).
- **Idea.** A fused `balanceL`/`balanceR` as in Data.Map, estimated about 30%
  fewer instructions per level. Scope: fused balance only; an Int/Nat-keyed
  IntMap not now.
- **Measured.** Statements unchanged. `bench:aoc` geomean -0.17% (best -2.9%),
  dijkstra -0.66%, the rest noise.
- **Why dropped.** Eight new definitions and lemmas for about 0.2%, and shapes
  can differ on unbalanced input. Revisit only with native `Map.Tree`
  `get`/`insertWith` (SW-1825) or a Std.Map benchmark. The `mapops` benchmark
  (SW-2503) now exists, and SW-2513 measured a fused balance at -25.6% of it
  *after* the SW-2514 record fix: that is SW-2515, so the verdict depends on
  the benchmark and should be re-judged there.

### SW-2485: `Map.Tree.minOr`/`maxOr` build the result once

- **Status:** merged (`aee351720`). Library-only. SW-2484 target 1.
- **Problem.** Each level of the walk built `Some (k, v)`; disk's profile
  showed 105.5 M cells.
- **Change.** `minFrom`/`maxFrom` carry key and value as two arguments, with
  `rfl` lemmas `minFromOr`/`maxFromOr`; `minOnto`/`maxOnto` statements
  unchanged.
- **Why safe.** The new function computes the same value (rfl lemmas); hash,
  pinned and prelude-bound tests (14) and the 35 AoC namespaces using min/max
  check clean.
- **Measured.** Disk 95.98 -> 78.19 G (-18.53%; wall 6.42 -> 5.28 s). Cells
  105.5 M -> 53.9 M.
- **Left.** `nearestBelow`/`nearestAbove` have the same pattern on one branch.

### SW-2474: timing builds were not like-for-like (finding, merged)

- **Status:** merged (`ba85fc928`).
- **Problem.** The same commit ran `expressions` in 320.5 G instructions built
  plainly and 310.7 G built in a lane worktree through kache (-3.1%), so lanes'
  numbers and Overmind's could differ for identical source.
- **Cause.** The devShell's `CARGO_PROFILE_RELEASE_INCREMENTAL=true`
  (`flake.nix`) builds `libstitchwort_standalone.a` in 256 codegen units
  without cross-unit inlining; kache strips the flag.
- **Change.** `bench:compare`, `bench:compare:check`, `native:bench` and
  `profile:native` build non-incrementally into `target/bench`. History in
  `history.toml` notes a one-off step of about 3%.
- **Open.** Overmind (job 32) showed no step even with the flag, so why only
  macOS builds differ is unexplained (musl target? linker? kache?).

### SW-2463 and SW-2462: effect-runtime allocation stages 1-3 (R1-R3)

- **Status:** merged (`f4c31a30b`, `37ad36ae5`). Stages of
  [../proposals/effect-runtime-allocation.md](../proposals/effect-runtime-allocation.md)
  (SW-2444: about 14 runtime objects per operation); each kept only if it
  delivered at least 60% of its estimate.
- **R1 (SW-2462).** A resumption is one object, its fields inside the `Fun`, not
  an `Rc<Resume>` plus a wrapper. Measured expressions -1.68%, scan -1.59%,
  matcher -0.36%, bridge -0.75% (5 runs, like-for-like builds); it cleared the
  bar. About 100 instructions saved per object, not the 140 assumed; later
  estimates use 100. `translate` gets `Fun::TranslateK` (two objects). Tests:
  rt 65, native 70, 113 effect/handler/resume.
- **R2 (SW-2463).** The loop reuses the `Bind` node as the pending cell.
  Measured expressions -3.40%, scan -3.20%, bridge -2.87%, matcher -0.69%.
  Pending cells 46.4 M -> 0.5 M.
- **R3.** A skipped forward reuses its `Call` cell: -1.81%, -1.45%, -0.67%,
  -0.39%; skip Calls 29.1 M -> 0. R2 + R3 together: expressions -5.15%, scan
  -4.61%, bridge -3.52%, matcher -1.07%. About 200 instructions saved per
  cell.
- **Why safe.** Only object counts and reuse change; counts of steps, effects
  and results are unchanged (the tickets are labelled "changes no counts").
- **Consequence.** R4 now saves one cell per perform, not two (re-estimate in
  the note, section 4.3). Later stages (R4 onward) are not done.

### SW-2452, SW-2468, SW-2482: freeing a deep value no longer overflows the stack

- **Status:** merged (`68c3a81aa`, `c417f0dc5`, `8674d0437`). Found by the
  elaborator fuzzer (`fuzz:elab`) in compute mode.
- **Problem.** Dropping a very deep `Value` chain recursed (drop glue): case
  531 of seed 0x2451 (a ~10M-deep `Rc<Unfolding>` chain) and case 2415 of seed
  0x246f (a stuck `Spine`), then every other type owning values.
- **Change.** `Drop for Unfolding` and `Spine` go through the iterative
  `free_iteratively` (SW-2452, SW-2468); `DataArgs`, `Shared` (Pi domain,
  NatAdd base, Eq parts) and `Unfolding.base` chains free by ordinary
  recursion down to `NESTING_LIMIT = 128` levels (about 64 KB), then
  iteratively (SW-2482). Six million-deep tests run on a 256 KB thread.
- **Rejected.** The first SW-2482 version always freed iteratively: +1.3-1.6%
  on `check --no-cache`. The depth-counter version is +0.2-0.6% on two files,
  level on one (noise about 0.5%); accepted as the orchestrator's call.
- **Not covered.** `Value::Resumption(Rc<Capture>)`.

### SW-2441: compact values, register dilation experiment (E not built)

- **Status:** experiment done on Overmind, never merged (patch `b28667004` on
  `origin/lane/SW-2441`).
- **Question.** Whether option E of
  [../proposals/compact-values.md](../proposals/compact-values.md) (an 8-byte
  header then two-word values) clears its gate: 1.10x decision-set geomean and
  1.25x on binary-trees. The cost model (SW-2429) predicted 1.088x and 1.21x,
  just under, so the experiment carried a fourth unused word per value
  register to mirror the spill cost.
- **Result.** Mirror reading 1.165x binary-trees, 1.090x decision set: misses
  the gate (clears only with every input at its high value).
- **Decision.** D3435 (Matt, 8 Nov): proceed to C then E only if E clears.
  E is not built; C alone is worth about 1% and waits with E. Related
  measurements: [../reviews/SW-2295-comparative-speed.md](../reviews/SW-2295-comparative-speed.md)
  and the V0-V4 notes in the proposal (E removes 7.0% of native instructions
  on the decision set; the parsers' low IPC is store-buffer and store-
  forwarding stalls, V2).

---

## 8 Nov 2026 and earlier (pointers)

Merged before this log began; figures are from the merge commits and tickets.

- **SW-2443**: freeing a cell with no deep fields skips the worklist
  (`d73ad4e06`): expressions -2.2%, scan -2.1%, octopus -2.3%. The one-slot
  pending variant measured +2.1 to +3.3% and was rejected (as was a
  thread-local and a `SmallVec` in SW-2421's A/B).
- **SW-2440**: native uniqueness tests compare the strong count only
  (`01fa1938c`): binary-trees -1.9%, octopus -1.3%, expressions -0.4%.
- **SW-2433**: one shared `JumpK` per thread (`bcf91079d`): expressions -0.8%,
  scan -1.0%.
- **SW-2398 and SW-2399**: Nat-shaped types, `Fin` as machine numbers and
  `Fin.toNat`/`Fin.ofNatLt` as pinned identities (`8fdfdf30d`, `a3261c779`):
  2025 day 3 -4.0% then -6.0% more, 2021 day 9 -4.3% then -4.1% more; steps
  and results unchanged.
- **Allocation by cause, census and counters** (SW-2422, SW-2425, SW-2461,
  SW-2475, SW-2479) in [../reviews/](../reviews/): the data these entries are
  chosen from.

### SW-2559 confirmed on Overmind (job 44, 9 Nov 2026)

Time on Linux x86-64, median of 5, against 9cc3fa3b8 (before SW-2511):
rbmap -7.0% (SW-2511 alone had been +1.2%), binary-trees -14.5%,
rbmap-ck -13.9%, memory-game -1.3%, mapops -20.6%. `CellCache::full`, 15.3%
of binary-trees' cycles before, is gone from every profile; LLC load misses
fell 54% on binary-trees and from 3.8 M to 0.89 M on rbmap. The 0.3% more
instructions measured on macOS buy this. Data on Overmind, job 44.
