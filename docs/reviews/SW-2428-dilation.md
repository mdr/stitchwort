# SW-2428: the dilation experiment (compact values, step V3)

Step V3 of [`docs/proposals/compact-values.md`](../proposals/compact-values.md) (§5): give every cell on native code's fixed-size path K spare bytes that nothing reads or writes, and measure what the bigger footprint costs with the instructions unchanged. Measured on Overmind (i7-6700HQ) on 8 Nov 2026, 19:37 to 19:54 GMT, on the branch `lane/SW-2428`, which starts from `a5974cd7d`. **A measurement branch: never merged.**

## The reading

**Go/no-go: the geometric-mean cost at +40 B on the decision set is over 3%:** +5.65% of cycles and +8.68% of wall time. By the note's rule, footprint is worth more than 3% to A, and A needn't rest on V2's instructions alone.

**But it is almost all binary-trees.** Without it, the other five decision programs' geometric mean is **+0.6% of cycles and +0.5% of wall time** at +40 B.

| Decision program | Δ cycles +40 B | Δ wall +40 B | note's estimate (+40 B) |
|---|---:|---:|---|
| binary-trees | **+35.0%** | **+61.1%** | 8–20% |
| memory-game | +2.2% | +1.3% | (none given) |
| matcher | +0.8% | +0.8% | 2–6% |
| dijkstra | +0.3% | +0.6% | 2–6% |
| octopus | −0.2% | −0.5% | 2–6% |
| expressions | −0.1% | +0.1% | 1–4% |
| **geometric mean** | **+5.65%** | **+8.68%** | |
| geometric mean without binary-trees | +0.6% | +0.5% | |

Against the note's estimates, the footprint matters *more* than expected on binary-trees and *less* than expected everywhere else.
- **binary-trees:** 35% of cycles is nearly twice the top of the 8–20% estimate. Its wall time grows by more still (61%), because kernel time isn't in the `:u` cycles: page faults and zeroing for the larger heap (see "Cycles and wall time").
- **Elsewhere:** matcher, dijkstra and octopus are under 1%, against 2–6%, and expressions is flat, against 1–4%.

This agrees with SW-2426: binary-trees had the only large memory-stall share among the decision programs (23.1%). The others' sat near Lean's.

A suggested reading for V4 (the orchestrator's or Matt's call): count the footprint in V4's model for binary-trees, and take it as zero, within ±1%, for the rest of the decision set. Smaller cells then pay off in time mostly through instructions (V2), except on allocation-heavy programs like binary-trees.

## Results

Each row is the mean of two rounds. Within each round, the three K values ran one after another for each program, so drift affects them alike. Cycles and instructions are user space only, at `perf_event_paranoid` 2. Wall time is perf's whole command, from `time.monotonic` around it.

| Program | cycles K=0 | K=24 | K=40 | Δ cycles 24 | Δ cycles 40 | time K=0 | K=24 | K=40 | Δ time 24 | Δ time 40 | Δ instr 40 | linear? |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| pidigits | 4.44 G | 4.44 G | 4.43 G | +0.2% | -0.1% | 1.34 s | 1.33 s | 1.31 s | -1.2% | -2.4% | +0.0% | flat (<1%) |
| binary-trees * | 8.45 G | 10.16 G | 11.41 G | +20.2% | +35.0% | 2.81 s | 3.88 s | 4.52 s | +38.3% | +61.1% | +0.0% | yes (0.58 of +40's at +24; 0.60 is linear) |
| memory-game * | 14.06 G | 14.12 G | 14.37 G | +0.4% | +2.2% | 4.42 s | 4.42 s | 4.48 s | -0.1% | +1.3% | +0.1% | no (0.19 of +40's at +24; 0.60 is linear) |
| dijkstra * | 8.78 G | 8.89 G | 8.81 G | +1.2% | +0.3% | 2.71 s | 2.77 s | 2.73 s | +2.1% | +0.6% | +0.3% | flat (<1%) |
| octopus * | 11.18 G | 11.18 G | 11.15 G | -0.0% | -0.2% | 3.27 s | 3.26 s | 3.25 s | -0.3% | -0.5% | +0.2% | flat (<1%) |
| disk | 47.02 G | 47.65 G | 47.72 G | +1.3% | +1.5% | 14.10 s | 14.40 s | 14.43 s | +2.2% | +2.4% | +0.2% | no (0.90 of +40's at +24; 0.60 is linear) |
| expressions * | 168.99 G | 170.20 G | 168.83 G | +0.7% | -0.1% | 49.29 s | 49.72 s | 49.33 s | +0.9% | +0.1% | +0.2% | flat (<1%) |
| scan | 155.72 G | 155.67 G | 157.05 G | -0.0% | +0.8% | 45.20 s | 45.19 s | 45.61 s | -0.0% | +0.9% | -0.1% | flat (<1%) |
| matcher * | 30.22 G | 30.43 G | 30.47 G | +0.7% | +0.8% | 8.79 s | 8.85 s | 8.86 s | +0.7% | +0.8% | -0.0% | flat (<1%) |
| bridge | 54.69 G | 54.78 G | 55.06 G | +0.2% | +0.7% | 16.01 s | 16.05 s | 16.13 s | +0.2% | +0.8% | +0.4% | flat (<1%) |

`*` marks the decision set. In "linear?", the +24 B change as a fraction of the +40 B change is 0.60 if the cost is linear in K. "flat" means the +40 B change is under 1%.

| Program | dTLB misses K=0 | K=40 | LLC misses K=0 | K=40 | Δ instructions +24 | Δ instructions +40 | worst spread between rounds |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 0.00 M | 0.00 M | 0.01 M | 0.00 M | +0.0% | +0.0% | 3.9% |
| binary-trees | 1.55 M | 1.33 M | 10.64 M | 36.52 M | +0.0% | +0.0% | 2.9% |
| memory-game | 0.73 M | 1.31 M | 10.89 M | 10.95 M | +0.4% | +0.1% | 1.5% |
| dijkstra | 0.21 M | 0.22 M | 1.42 M | 1.71 M | +0.1% | +0.3% | 0.6% |
| octopus | 0.03 M | 0.03 M | 0.01 M | 0.00 M | +0.2% | +0.2% | 0.3% |
| disk | 3.63 M | 3.65 M | 7.60 M | 14.48 M | +0.3% | +0.2% | 0.4% |
| expressions | 6.97 M | 7.16 M | 5.96 M | 7.38 M | +0.0% | +0.2% | 0.2% |
| scan | 2.79 M | 3.12 M | 1.26 M | 1.60 M | +0.0% | -0.1% | 1.4% |
| matcher | 0.57 M | 0.62 M | 0.25 M | 0.40 M | +0.2% | -0.0% | 0.7% |
| bridge | 1.40 M | 1.58 M | 2.53 M | 2.70 M | +0.1% | +0.4% | 0.6% |

| Geometric mean | decision set | all ten |
|---|---:|---:|
| Δ cycles, +24 B | +3.62% | +2.33% |
| Δ cycles, +40 B | +5.65% | +3.66% |
| Δ wall, +24 B | +6.14% | +3.76% |
| Δ wall, +40 B | +8.68% | +5.29% |

**Instructions moved under 1% everywhere:** the largest change against K = 0 is +0.39% (bridge), so the code is the same and only the footprint differs. Every one of the 60 timed runs printed the expected answer.

**Is it linear in K?**
- Only binary-trees has a cost large enough to tell, and it is linear: its +24 B change is 0.58 of the +40 B change, where linear is 0.60.
- disk's 1.3% and 1.5% look like a step rather than a slope. memory-game's 0.4% and 2.2% are too small to read.
- One reason not to expect linearity is that mimalloc rounds each allocation up to a size class. A two-field cell (64 B) becomes 88 B at +24 and 104 B at +40, which take the 96 B and 112 B classes: +50% and +75% of its memory, not +38% and +63%. A one-field cell (40 B) becomes 64 B and 80 B, classes of the same sizes. So the real step in footprint differs per arity.

### Cycles and wall time

binary-trees' wall time grows more than its cycles: +61% against +35%.
- At K = 40 it takes 4.52 s, against about 3.7 s for 11.41 G user cycles at its clock.
- The rest is kernel time, which the `:u` counters at paranoid 2 don't see: page faults and zeroing for a heap that, at peak, is about 1.75× the size (estimated: two-field nodes go from the 64 B class to the 112 B one; not measured).
- The wall figure is the one a user sees, so I'd take +61% as binary-trees' cost and +35% as the cost of the instructions waiting on memory in user space. LLC misses rise 3.4× (10.6 M to 36.5 M); dTLB misses don't rise.

## The change

Every native-built cell on the fixed-size path (1 to 8 fields) goes through `sw_cell_new`, or through the cell cache, whose blocks were themselves made by `sw_cell_new`. `n1.rs`'s `new_cell` takes a cached block, or calls the `cell_new` helper, and nothing else.

- **`crates/rt/src/native_abi.rs`:** `DILATION` is a build-time constant from `option_env!("SW_CELL_DILATION")`: decimal, a multiple of 8, 0 when unset.
  - With it above 0, `cell_new`'s fixed path allocates an `Rc<Dilated<N>>`, a `repr(C)` struct of the `N` fields followed by `DILATION` spare bytes. The fields are at the same offset (`RC_VALUE_AT`), and the value's length word stays `n`, so no instruction changes.
  - With it at 0, the code is the original's.
  - Every free path frees with the layout of `n` fields. That is sound only because the standalone runtime's global allocator frees with `mi_free`, which ignores the size; that's why the branch is never merged.
- **`crates/rt/src/cell_cache.rs`: the cache's size classes.** The lists are keyed by field count. A padded cell is cached only on its own count's list and taken again only as a cell of that count, so padded cells are reused only as padded cells.
  - The risk was the reverse: a cell of the same count built *outside* `sw_cell_new`, by `sw_ctor_reuse`'s fallback or by the runtime, emptied by native `Unpack` while unique, would enter the list unpadded and be handed out as a "padded" cell.
  - To measure that, a census counts the cached blocks seen when the cache is cut (`full`) or dropped, and how many are smaller than a padded cell by `mi_usable_size`. It prints with `SW_DILATION_REPORT=1`.
  - The census is a build of its own (`SW_DILATION_CENSUS=1` at build time). In the timed builds it added 5.1% to binary-trees' instructions, the walk in `full` seeing 55 M blocks, so the timed builds leave it out. The first, discarded round of runs had it in.
  - Result at K = 40: **essentially no unpadded blocks.** binary-trees 0 of 54.9 M seen, disk 0 of 4.0 M, expressions 5 of 5.8 M, scan 2 of 22, bridge 0 of 112 k, and the rest 0 of fewer than 400.
  - The cache saw no blocks at all for memory-game.
  - The counts are cumulative over every walk, so a block can be counted more than once; they are a sample, not a census of cells.
- **`crates/standalone/src/lib.rs`:** prints the census when the native run ends.

The patch is the branch's code commit; `git show` it for the diff.

## How it was run

- **Builds:** for each K, `SW_CELL_DILATION=K cargo build --release -p stitchwort-cli -p stitchwort-standalone --features stitchwort-cli/dev`, then `compare.sh --check --runners native`, which rebuilt the ten native binaries and passed all eleven answer checks (11 ok each time). The binaries were then copied aside per K, and their hashes differ per K.
- **Runs:** `perf stat -x , -e cycles,instructions,dTLB-load-misses,LLC-load-misses -- sh -c <the harness's native command>`, with the program's scaled input on stdin. Four events fit the counters, so none is multiplexed.
  - Two rounds were run, each of all ten programs at K = 0, 24 and 40.
  - Load was 0.9 to 1.0, and nothing else ran.
- **Spread:** cycles and wall agree within 0.2–3.9% between rounds, under 1.5% on most programs, and the per-program figure is in the second table. So changes under about 1% are noise; on disk, the 1.3% and 1.5% are just above it.

Scripts (not committed; in the Overmind session's scratchpad): `build.sh K` builds and copies the binaries, `collect.py` runs the rounds and the census, and `analyse.py` makes the tables.
