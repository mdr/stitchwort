# Parallel checking: how much would it help? (SW-1170, D2296)

The question (elaborator-state.md §4.9, globals-split.md §5): is it worth
checking a project's independent namespaces in parallel, and is the cheap
design, a separate `stitchwort check` process per namespace that replays its
imports from the check cache, good enough to start with?

**Answer.** For a **cold full check** of `aoc` the namespace graph allows at
most **5.9x** on 8 or more cores (67 s of work, an 11.5 s critical path).
Process per namespace would get about **3.4x on 10 cores** (67 s to 20 s),
and process per day group about **4.0x** (17 s), **at 1.6-2.7 times the
CPU**, because every process pays about 0.45 s to start, load the core,
parse the project and replay its imports. The prototype agrees with the
model (below). For a **typical edit** (one `Proofs` or `Tests` namespace)
parallelism gains **nothing**: one namespace is re-checked, and there is
nothing to run beside it. An edit to `Aoc.Common` (59 namespaces re-checked)
gains 1.7x. `games/rogue` gains at most **1.76x** (three namespaces, and the
library is 42% of its work) and the process design loses time there. The
standard library on its own allows at most **2.2x** (it is a deep chain).

**Recommendation: deprioritise.** The gain is real only for cold full
checks of `aoc`. On this machine cold checks happen after a compiler change,
mostly inside lanes and test tiers that already run several processes at
once, and the machine is often saturated (load 40-150 throughout these
measurements). There, a check that takes 2.5 times the CPU to finish sooner
mostly takes cores from other lanes. Section 6 gives the cheapest first step
if it's wanted anyway, and section 7 a cheaper sequential win the
measurements turned up for edits.

## 1. Method

- Build: release CLI at `6842c02e` (the lane's base), `cargo build --release
  -p stitchwort-cli`. Machine: Speedwell, 10 cores, 48 GB. 4 Nov 2026,
  08:35-09:25 GMT.
- **Load.** Another lane's tests and builds ran throughout: load average 14
  at the start, then 30-150. So: work is measured in **CPU time** (user +
  sys, `/usr/bin/time -l`), or from a run where wall time and CPU time
  agreed. `aoc`'s cold run (load 14) had 67.5 s wall and 66.0 s CPU, so its
  per-unit `STITCHWORT_TIMINGS` times are taken as CPU. `rogue`'s first
  cold run (load ~120) had 40 s wall for 6.3 s CPU and was discarded; the
  repeat had 5.25 s wall, 5.05 s user. Wall-clock numbers from the
  prototype were taken under load 40-100 and say so.
- **Per-unit work**: `STITCHWORT_TIMINGS=1 stitchwort check --no-cache`,
  elaboration plus kernel time of each namespace and library file. Times
  are exclusive (a library file loaded inside a namespace counts against
  the file), and the units sum to the run's wall time within 0.5%.
- **The graphs**: `crates/driver/examples/ns_graph.rs` (new, an example, not
  part of the CLI) prints a project's namespaces with their direct edges
  (`Analysis::namespaces[..].edges`, what `check` orders by), and with
  `--std` the library files with the files each needs
  (`LibraryIndex::files[..].edges`). Which library files a namespace needs
  comes from checking it alone (next item).
- **What a worker process costs**: `dev/parallel-check/warm-each` checks
  every namespace alone (`check NS`) against a warm cache, so everything is
  a hit: CPU, peak RSS, and the library files its closure loads. That is
  the process start, the core, parsing the project and replaying NS's
  closure. A job's overhead is that, less NS's own replay.
- **The model**: `dev/parallel-check/model.py` builds the DAG (namespaces
  and library files), finds the critical path, and simulates a greedy list
  schedule (the ready job with the longest path to the end first) on N
  workers. "Ideal" ignores all overheads.
- **The prototype**: `dev/parallel-check/sched.py` runs one `stitchwort
  check --cache-dir C NS` process per namespace, at most N at once, each
  started when its namespaces are done, all sharing one cache (writes are
  temp-and-rename, `check_cache.rs:130`). It records each job's CPU and peak
  RSS (`wait4`).
- Edits are emulated by deleting the cache entries of the edited namespace
  and everything that uses it, directly or not.

Commands (`S` a scratch folder, run from the worktree):

```
cargo run --release -p stitchwort-driver --example ns_graph -- aoc > $S/aoc-graph.tsv
cargo run --release -p stitchwort-driver --example ns_graph -- --std > $S/std-graph.tsv
(cd aoc && STITCHWORT_TIMINGS=1 stitchwort check --no-cache 2> $S/aoc-cold.err)
(cd aoc && stitchwort check --cache-dir $S/cache-aoc)            # fill
(cd aoc && STITCHWORT_TIMINGS=1 stitchwort check --cache-dir $S/cache-aoc 2> $S/aoc-warm.err)
dev/parallel-check/warm-each aoc $S/aoc-graph.tsv $S/cache-aoc $S/aoc
python3 dev/parallel-check/model.py $S/aoc-cold.err $S/aoc-warm.err \
  $S/aoc-graph.tsv $S/std-graph.tsv $S/aoc/warm-each.tsv [EDITED_NS...]
python3 dev/parallel-check/sched.py target/release/stitchwort aoc \
  $S/aoc-graph.tsv $S/cache 8 --cost $S/aoc-cold.err [--only NS,...]
```

## 2. The graphs

**aoc**: 207 namespaces, 318 direct edges, and 59 of the library's 66
files. It is wide and shallow: 52 days, each a code namespace with `Spec`,
`Proofs` and `Tests` under it, 57 namespaces using `Aoc.Common`
directly and the library. The longest chain of namespaces is four deep
(`Aoc.Common` → `Day15` → `Day15.Spec` → `Day15.Proofs`, and others).

Where the work is (cold, measured):

| | CPU s | share |
|---|---:|---:|
| whole check | 67.4 | 100% |
| library files (59) | 7.3 | 11% |
| the 6 slowest namespaces (all `Proofs`) | 39.9 | 59% |
| `Aoc.Year2021.Day16.Proofs` | 7.9 | 12% |
| `Aoc.Year2024.Day06.Proofs` | 7.6 | 11% |
| `Aoc.Year2024.Day13.Proofs` | 6.5 | 10% |
| `Aoc.Year2024.Day22.Proofs` (5.6 s of it in the kernel) | 6.4 | 9% |
| `Aoc.Year2024.Day23.Proofs` | 5.8 | 9% |
| `Aoc.Year2021.Day08.Proofs` | 5.7 | 8% |

**The library**: a deep chain. Of the 7.3 s, 3.4 s is one path
(`Bool` → `Nat/Arith` → `Int` → `Omega/Sound` → `List/Lemmas` → ... →
`Map/Spec` → `Map/Map` → `Set/Set` → `Set/Spec` → `Graph/Search`), so the
library alone allows at most 2.2x (measured times, the 59 files `aoc` uses).

**games/rogue**: three namespaces, `Rogue` → {`Rogue.Proofs`,
`Rogue.Tests`}, and 29 library files. Cold: 5.2 s, of which the library is
2.2 s, `Rogue` 0.3 s, `Proofs` 1.4 s, `Tests` 1.1 s.

## 3. The critical path and the ideal speedup (no overheads)

`aoc`, cold full check, from measured per-unit times; the schedule is
simulated:

| cores | makespan | speedup |
|---:|---:|---:|
| 1 | 67.4 s | 1.00x |
| 2 | 34.0 s | 1.98x |
| 4 | 17.4 s | 3.88x |
| 8 | 11.5 s | 5.86x |
| 10 | 11.5 s | 5.86x |

The critical path is 11.5 s: the library chain to `Graph/Search` (3.4 s),
`Aoc.Common`, `Day06`, `Day06.Spec`, then `Day06.Proofs` (7.6 s). 8 cores
already reach it; more cores add nothing. Two single namespaces of about
8 s each bound it, and one of them is mostly one declaration group
(`Day16.Proofs`' `stepComplete`/`countComplete`/`fillComplete`, 6.4 s). Going
past about 6x needs parallelism inside a namespace, and past about 10x
inside a declaration.

`rogue`: the bound is **1.76x** (critical path 3.0 s of 5.2 s), reached at 2
cores. `std` alone: **2.2x**.

## 4. What the process design pays

Measured, CPU (warm cache, every entry a hit, `warm-each`):

| | CPU | peak RSS |
|---|---:|---:|
| `check` of a one-line file (core only), quiet | 0.18-0.20 s | |
| `check NS` warm, the cheapest namespace | 0.30 s | 130 MB |
| `check NS` warm, median over aoc's 207 | 0.47 s | 153 MB |
| `check NS` warm, the dearest (`Day22.Proofs`, whose own replay is large) | 1.96 s | 210 MB |
| warm `check` of all of aoc (one process, everything replayed) | 3.2 s (3.8 s wall at load 34) | 704 MB |
| cold `check` of all of aoc (one process) | 66.0 s | 1.61 GB |

So a job's fixed cost is about 0.3 s: process start (nil), elaborating the
core (about 80 ms: it isn't cached), parsing every file of the project
(about 0.1-0.15 s; a worker needs only its closure's), and replaying the
library files its closure needs (median 30 files). Over 207 namespaces and
59 library files that is **112 s of CPU, more than the 67 s of work**.

Memory: a worker holds 130-190 MB once its imports are replayed (median 153
MB), and a few grow far beyond that while checking: `Day06.Proofs` alone
peaks at 1.25 GB, `Day13.Proofs` at 0.82 GB, `Day22.Proofs` at 0.6 GB
(measured: a worker checking only that namespace, its imports cached). With
8 workers the prototype's summed peak (each job's peak held for its whole
run, an upper bound) was **4.1 GB**, against 1.6 GB for the sequential
check. Not a problem against 48 GB, but 2.5 times what `check` uses now, at
the moment the test tiers are already at 10 GB.

The model with these overheads, `aoc` cold full check (CPU-time model,
simulated):

| design | jobs | CPU | crit. path | N=4 | N=8 | N=10 |
|---|---:|---:|---:|---:|---:|---:|
| ideal (no overheads) | 266 | 67 s | 11.5 s | 3.9x | 5.9x | 5.9x |
| A. a process per namespace and per library file | 266 | 179 s | 17.5 s | 1.5x | 2.8x | **3.4x** |
| B. the library first in one process, then a process per namespace | 208 | 160 s | 17.4 s | 1.5x | 2.5x | 2.9x |
| C. a process per day group (a namespace with its `Spec`, `Proofs`, `Tests`), library as in A | 111 | 111 s | 16.9 s | 2.4x | 4.0x | **4.0x** |
| D. long-lived workers (a pool, or threads): each job replays its closure, no start, core or parsing | 266 | 100 s | 12.4 s | 2.7x | 5.2x | 5.5x |

D's CPU is an upper bound: a worker that keeps what it loaded replays less.

## 5. The prototype against the model

`sched.py`, 8 processes, aoc. Wall times were taken under load 40-100 (the
other lane's tests), so they are inflated and the comparisons between runs
are rough; the CPU figures are the reliable ones.

| scenario | sequential (`check`, 1 process) | prototype, N=8 | model |
|---|---|---|---|
| library cached, every namespace cold | 112.0 s wall, 65.6 s CPU (load 60-80) | **34.9 s** wall, **160 s CPU** (load 40-60) | 59.7 s work → 19.2 s at N=8, 153 s CPU |
| empty cache (cold full check) | 259 s wall, 81 s CPU (load 65) | **64.7 s** wall, **179 s CPU** (load 45-70) | 67.4 s → 20-24 s at N=8 (A/B), 179 s CPU (A) |
| `Aoc.Common` edited (59 namespaces cold, the rest cached) | whole project: 62.5 s wall, 21.1 s CPU; only the 59: 56.7 s wall, 18.6 s CPU | **16.1 s** wall, **46 s CPU** | today 19.1 s, one process 16.2 s, 10 processes 9.7 s |

- **CPU matches the model** (160 vs 153 s, 179 vs 179 s), so the overhead
  model is right: the process design spends 2.4-2.7 times the CPU of one
  process.
- In the library-cached case the sequential run's wall/CPU inflation (1.7x)
  applied to the model's 19.2 s gives 33 s; the prototype took 34.9 s.
  Quiet-machine wall times were not measured: the load never fell below 40
  after 08:40 (to rerun when quiet: the commands in §1; each pair takes
  about two minutes).
- On a loaded machine the speedups in the wall column look better than
  they would on a quiet one (259 s → 65 s is 4x), because 8 processes get 8
  shares of the CPU where one gets one. That is the "steals cores from other
  lanes" effect, not a speedup.
- In the cold run all 8 first-wave processes checked the library files they
  needed themselves (nothing was cached yet): `Aoc.Common`'s job took 4.75 s
  of CPU against 0.6 s with the library cached. A real scheduler checks the
  library files first, as jobs (A) or in one process (B).
- No job failed; concurrent writers to one cache were fine.

**Edits** (model, CPU, mean over the namespaces of each kind; `today` is
`check` of the whole project, which replays every namespace the edit didn't
touch; `one` is one process checking only the affected namespaces; `par10`
is a process per affected namespace, 10 at once):

| edited | namespaces re-checked | today | one | par10 | par10 vs one |
|---|---:|---:|---:|---:|---:|
| a `Tests` namespace (52) | 1.0 | 3.8 s | 0.5 s | 0.5 s | 1.00x |
| a `Proofs` namespace (52) | 1.4 | 5.0 s | 1.7 s | 1.6 s | 0.99x |
| a `Spec` namespace (51) | 2.9 | 4.9 s | 1.6 s | 2.1 s | 0.66x |
| a day's code (52) | 4.9 | 5.2 s | 1.9 s | 2.6 s | 0.56x |
| `Aoc.Common` | 59 | 19.1 s | 16.2 s | 9.7 s | 1.68x |
| `Aoc.Common.Proofs` | 15 | 10.2 s | 7.1 s | 3.1 s | 2.30x |
| `Rogue` (rogue) | 3 | 3.7 s | 3.2 s | 2.2 s | 1.46x |
| `Rogue.Proofs` (rogue) | 1 | 2.4 s | 1.7 s | 1.7 s | 1.00x |

For the edits users make most, the namespace and what uses it form a short
chain, so there is nothing to run side by side, and a process per namespace
is slower than one process. The language server is in process already and
doesn't replay (`LiveProject`; state-step6 measured 0.2-1.8 s per edit), so
these CLI numbers are an upper bound on what an editor would see.

## 6. Threads in one process, briefly (reasoning, not built)

What the Globals split and a frozen base (elaborator-state.md §4.9 step 9)
would allow: workers share the library and the namespaces they depend on,
read-only, so a job pays no process start, no core, no parsing and no
replay of its imports; merging a worker's namespace is replaying its entry
in the main session (1-5% of its check time, from the warm replays above).
That is design D without its replay, so close to the ideal: **about 5.5-5.9x
on 8-10 cores for aoc cold, at about the sequential CPU**, and one copy of
the shared base in memory instead of one per worker. It needs `Arc` for core
terms and values (166 `Rc<` sites in `crates/core`; the cost of an atomic
increment per clone everywhere is unmeasured) and `Send` state throughout
the elaborator: a large change, for the same ceiling, because the critical
path (two 8 s namespaces) bounds threads as much as processes. Neither
helps the typical edit; that needs parallelism inside a namespace
(declarations that don't depend on each other), which neither design gives.

**If parallel checking is wanted anyway, the cheapest first step** is design
C behind a flag: `check --jobs N` in the driver, spawning `stitchwort check
NS...` children per day group along `Analysis`'s graph, after one process
has checked (or replayed) the library files the project needs, all sharing
the project's check cache, and the parent replaying the result from the
cache as today's warm `check` does (about 3 s). Estimate: about 4x on aoc
cold on a quiet 10-core machine, a day or two of work, no change to the
elaborator. Then cut the fixed cost per process (parse only the closure's
files) before considering a worker pool.

## 7. Findings on the way

- **A warm `check` after an edit replays every namespace the edit didn't
  touch.** For a leaf edit in aoc that is most of the time: 3.8 s against
  0.5-1.7 s for checking just what changed (§5's `today` against `one`).
  A sequential fix (decide that an untouched namespace's entry is still
  good from the keys, without replaying it, when nothing later needs its
  terms) would do more for the CLI edit loop than parallelism. Unclear:
  whether `check` must replay a hit to report its diagnostics or build
  `--index`.
- **Every process elaborates the core and parses the whole project**
  (about 0.3 s of CPU before any work). It matters for anything that runs
  `stitchwort` many times: the per-namespace audit, the tests that start
  the CLI.
- **The work is concentrated**: six `Proofs` namespaces are 59% of a cold
  aoc check, and one declaration group is 6.4 s. Speeding those up (the
  proof-check-speed work) shortens the sequential check and the critical
  path at once.

## 8. Measured, estimated, unsure

- **Measured**: per-unit cold times (aoc, rogue), the graphs, per-namespace
  warm CPU and RSS (all 207 aoc namespaces), the heavy workers' peak RSS,
  the prototype's CPU, wall (under load) and summed RSS.
- **Simulated from measurements**: every speedup in §3-§5's model columns
  and the edit table. The schedule is greedy, not optimal, but it reaches
  the critical path at N=8, so it can't be far off.
- **Estimated**: the thread design's numbers (§6), the cost of `--jobs`,
  the split of the 0.3 s fixed cost.
- **Unsure**: quiet-machine wall times for the prototype (CPU was measured
  under load, which inflates CPU time a little too); the model treats a
  library file's job as the cheapest process plus its replays, which needs a
  way to check one library file into the cache that the CLI doesn't have;
  the warm per-unit replay times were taken at load 34.
