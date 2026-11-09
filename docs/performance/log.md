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

## 9 Nov 2026

### SW-2531: inline a function for its context (a selector's result taken apart at once)

- **Status:** on `lane/SW-2531`, for review. Opus.
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
