# Comparative speed, first headline table (SW-2295)

Run time only (Matt, 7 Nov 2026: run time first, proofs later). Overmind (NixOS, i7-6700HQ,
quiet), 8 Nov 2026 00:25, commit `e8e9acd1e`: before SW-2302 (big numbers by reference),
SW-2320 (octopus grid), SW-2323 (one-pass `flatMap`) and SW-2328. Inputs scaled at run
time (SW-2307), binary-trees' Lean port fixed (SW-2319).
`task bench:compare -- --runners native,cpython,pypy,lean`, 5 hyperfine runs each,
startup subtracted; every answer checked (44 ok). The interpreter (`run`) isn't in this
table: it comes later from a quiet Speedwell.

Ratios are native time over the other runner's: above 1, Stitchwort is slower.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean |
|---|---:|---:|---:|---:|---:|---:|
| pidigits | 1.55 s | 3.77 s | 3.28 s | 2.02 s | 0.41 | 0.77 |
| binary-trees | 4.31 s | 10.17 s | 1.57 s | 992 ms | 0.42 | 4.34 |
| memory-game | 8.27 s | 8.16 s | 5.15 s | 777 ms | 1.01 | 10.64 |
| dijkstra | 12.97 s | 836 ms | 507 ms | 203 ms | 15.52 | 63.85 |
| octopus | 15.94 s | 1.52 s | 466 ms | 219 ms | 10.51 | 72.66 |
| disk | 21.06 s | 2.24 s | 1.91 s | 757 ms | 9.41 | 27.83 |
| expressions | 86.30 s | 2.14 s | 1.76 s | 659 ms | 40.39 | 130.97 |
| scan | 81.85 s | 827 ms | 131 ms | 586 ms | 99.03 | 139.69 |
| matcher | 15.73 s | 4.61 s | 2.82 s | 850 ms | 3.41 | 18.50 |
| bridge | 22.53 s | 3.48 s | 1.20 s | 822 ms | 6.47 | 27.42 |
| startup | 1 ms | 21 ms | 102 ms | 5 ms | | |

Geometric means over the ten programs: native / CPython **5.5**, native / Lean **23**.

**What it says.**
- Native beats CPython on the two Benchmarks Game classics (pidigits, binary-trees), ties on
  memory-game, and is slower on every AoC day, by 3-15x on most and 40-100x on the two parsing
  programs.
- Against Lean it is level only on pidigits.
- The causes are measured in docs/reviews/SW-2296-native-profiles.md: `Std.Parse`'s effect
  machinery (expressions, scan; docs/proposals/parse-runtime.md), the grid code (octopus), list
  cell filling and `flatMap` (matcher), comparisons and arrays (memory-game), allocation
  (binary-trees), closures and `Ord` dictionaries (dijkstra).

**Noise.** Hyperfine warned on null/native (under 5 ms, expected), matcher/pypy (slow first
run) and bridge/lean (outliers). The raw JSON is Overmind's
`target/compare/2026-11-08-overmind.json`.

The next run, on `main` after tonight's fixes, goes in a new section below with what changed.

## After the first fixes (Overmind, 8 Nov 2026 00:59, `53c59e6be`)

Same command and machine; adds SW-2302 (big numbers by reference), SW-2320 (octopus grid) and
SW-2323 (one-pass `flatMap`). Not yet SW-2328 (native hole operations inline). 44 answers ok;
CPython, PyPy and Lean within about 1% of the first run, so the two are comparable.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native change |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 1.32 s | 3.77 s | 3.29 s | 2.00 s | 0.35 | 0.66 | 1.55 → 1.32 s (SW-2302) |
| binary-trees | 4.29 s | 10.08 s | 1.56 s | 998 ms | 0.43 | 4.30 | |
| memory-game | 8.26 s | 8.10 s | 5.18 s | 782 ms | 1.02 | 10.56 | |
| dijkstra | 13.00 s | 836 ms | 504 ms | 204 ms | 15.54 | 63.75 | |
| octopus | 5.13 s | 1.52 s | 465 ms | 219 ms | 3.38 | 23.46 | 15.94 → 5.13 s (SW-2320) |
| disk | 21.08 s | 2.25 s | 1.90 s | 754 ms | 9.39 | 27.94 | |
| expressions | 86.51 s | 2.13 s | 1.76 s | 658 ms | 40.54 | 131.54 | |
| scan | 81.94 s | 825 ms | 135 ms | 581 ms | 99.32 | 141.01 | |
| matcher | 12.57 s | 4.61 s | 2.83 s | 857 ms | 2.72 | 14.66 | 15.73 → 12.57 s (SW-2323) |
| bridge | 22.36 s | 3.46 s | 1.21 s | 823 ms | 6.46 | 27.17 | |

Geometric means: native / CPython **5.5 → 4.7**, native / Lean **23 → 20**. Unchanged programs
moved under 1%. expressions and scan wait for the operations-in-place work
(docs/proposals/operations-in-place.md).

## After the native fixes (Overmind, 8 Nov 2026 04:38, `2541bba88`)

Same command and machine; adds SW-2328 (hole operations inline), SW-2329 (comparisons and
array access inline), SW-2321 (cells built and freed through fixed-size helpers). 44 answers
ok; CPython, PyPy and Lean within about 2% of the previous run.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native change |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 1.31 s | 3.78 s | 3.28 s | 2.02 s | 0.35 | 0.65 | |
| binary-trees | 3.09 s | 10.07 s | 1.53 s | 990 ms | 0.31 | 3.12 | 4.29 → 3.09 s |
| memory-game | 4.67 s | 8.27 s | 5.17 s | 777 ms | 0.56 | 6.01 | 8.26 → 4.67 s |
| dijkstra | 11.76 s | 836 ms | 493 ms | 204 ms | 14.07 | 57.62 | 13.00 → 11.76 s |
| octopus | 3.47 s | 1.51 s | 462 ms | 221 ms | 2.29 | 15.75 | 5.13 → 3.47 s |
| disk | 17.46 s | 2.24 s | 1.91 s | 757 ms | 7.80 | 23.05 | 21.08 → 17.46 s |
| expressions | 82.20 s | 2.14 s | 1.75 s | 660 ms | 38.39 | 124.54 | 86.51 → 82.20 s |
| scan | 77.85 s | 825 ms | 126 ms | 585 ms | 94.34 | 133.14 | 81.94 → 77.85 s |
| matcher | 10.83 s | 4.61 s | 2.82 s | 853 ms | 2.35 | 12.69 | 12.57 → 10.83 s |
| bridge | 20.77 s | 3.47 s | 1.20 s | 822 ms | 5.98 | 25.25 | 22.36 → 20.77 s |

Geometric means: native / CPython **5.5 → 4.7 → 3.9**, native / Lean **23 → 20 → 16** over
tonight's three runs. Native now beats CPython on pidigits, binary-trees and memory-game (and
PyPy on memory-game). The two parsing programs (expressions, scan) remain the outliers at 38x
and 94x CPython; their cost is the effect machinery, which operations in place
(docs/proposals/operations-in-place.md, stages B-D) addresses.

## After the Dijkstra and reuse fixes (Overmind, 8 Nov 2026 10:43, `a3d786138`)

`task bench:compare -- --instructions --runners native,cpython,pypy,lean`, same machine, 44
answers ok, 33.7 min. Adds SW-2370 (queue a neighbour only when its cost improves), SW-2382
(the search takes the popped pair), SW-2376 (`reachable` by breadth-first search) and SW-2388
(a call argument's last read is a move). Not yet SW-2394 (cost table), SW-2349 (operations in
place stage B) or SW-2391 (reuse across calls). Noisier than the previous run: the reference
runners moved up to 20% (PyPy on pidigits), so read native changes under 10% from the
instruction counts.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native change |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 1.35 s | 3.84 s | 3.95 s | 2.24 s | 0.35 | 0.60 | |
| binary-trees | 3.35 s | 10.48 s | 1.71 s | 1.03 s | 0.32 | 3.26 | noise (first run slow) |
| memory-game | 5.11 s | 8.78 s | 5.30 s | 809 ms | 0.58 | 6.32 | noise |
| dijkstra | 5.85 s | 834 ms | 504 ms | 203 ms | 7.02 | 28.91 | 11.76 → 5.85 s |
| octopus | 3.33 s | 1.51 s | 465 ms | 219 ms | 2.21 | 15.23 | |
| disk | 15.96 s | 2.24 s | 1.93 s | 758 ms | 7.11 | 21.07 | 17.46 → 15.96 s |
| expressions | 77.82 s | 2.12 s | 1.76 s | 661 ms | 36.65 | 117.82 | 82.20 → 77.82 s |
| scan | 74.42 s | 828 ms | 126 ms | 582 ms | 89.85 | 127.80 | 77.85 → 74.42 s |
| matcher | 10.52 s | 4.62 s | 2.81 s | 854 ms | 2.28 | 12.32 | |
| bridge | 20.22 s | 3.47 s | 1.19 s | 822 ms | 5.83 | 24.60 | |

Instructions retired (Linux `perf stat`), the steadier measure:

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean |
|---|---:|---:|---:|---:|---:|---:|
| pidigits | 9.45 G | 44.45 G | 32.92 G | 13.28 G | 0.21 | 0.71 |
| binary-trees | 29.39 G | 91.50 G | 8.73 G | 9.82 G | 0.32 | 2.99 |
| memory-game | 35.30 G | 37.93 G | 13.06 G | 2.26 G | 0.93 | 15.65 |
| dijkstra | 46.68 G | 7.23 G | 3.39 G | 1.50 G | 6.46 | 31.21 |
| octopus | 29.88 G | 15.15 G | 3.28 G | 2.47 G | 1.97 | 12.09 |
| disk | 127.40 G | 18.70 G | 10.12 G | 6.36 G | 6.81 | 20.04 |
| expressions | 566.08 G | 20.35 G | 11.15 G | 6.09 G | 27.81 | 92.97 |
| scan | 532.90 G | 7.90 G | 956.77 M | 5.99 G | 67.43 | 88.91 |
| matcher | 86.61 G | 42.64 G | 15.27 G | 8.07 G | 2.03 | 10.73 |
| bridge | 151.05 G | 32.65 G | 6.78 G | 7.05 G | 4.63 | 21.43 |

Geometric means of the time ratios: native / CPython **5.5 → 4.7 → 3.9 → 3.5**, native / Lean
**23 → 20 → 16 → 14.9**. Raw files: Overmind's `target/compare/2026-11-08T104311-overmind.{json,md}`.
On Speedwell since then (instructions, macOS): SW-2394 dijkstra −5%, SW-2349 expressions 1.44×
and scan 1.32× fewer, SW-2391 dijkstra −11%; these go in the next Overmind run.

## After this morning's runtime work (Overmind, 8 Nov 2026 13:28, `663bd9c53`)

Same command and machine as the previous run, 44 answers ok, 27.3 min, load about 1 while
timing. Adds SW-2394 and SW-2396 (Dijkstra over a cost table; day 15 passes a grid index, so
costs live in an array), SW-2349 (operations in place stage B: forwarding clauses skipped),
SW-2391 (reuse across calls) and SW-2336 (apply fast paths). Reference runners within about 2%
of the previous run.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native change |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 1.32 s | 3.77 s | 3.30 s | 2.01 s | 0.35 | 0.65 | |
| binary-trees | 3.10 s | 10.15 s | 1.57 s | 1.01 s | 0.31 | 3.07 | |
| memory-game | 4.62 s | 8.30 s | 5.38 s | 821 ms | 0.56 | 5.63 | |
| dijkstra | 2.82 s | 842 ms | 510 ms | 204 ms | 3.35 | 13.85 | 5.85 → 2.82 s |
| octopus | 3.25 s | 1.52 s | 470 ms | 221 ms | 2.15 | 14.76 | |
| disk | 14.07 s | 2.24 s | 1.91 s | 753 ms | 6.29 | 18.68 | 15.96 → 14.07 s |
| expressions | 51.30 s | 2.14 s | 1.77 s | 660 ms | 24.03 | 77.75 | 77.82 → 51.30 s |
| scan | 50.62 s | 827 ms | 136 ms | 581 ms | 61.23 | 87.15 | 74.42 → 50.62 s |
| matcher | 9.02 s | 4.58 s | 2.86 s | 849 ms | 1.97 | 10.62 | 10.52 → 9.02 s |
| bridge | 16.33 s | 3.47 s | 1.21 s | 825 ms | 4.71 | 19.80 | 20.22 → 16.33 s |

Instructions retired:

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native change |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 9.44 G | 44.45 G | 32.92 G | 13.28 G | 0.21 | 0.71 | |
| binary-trees | 29.39 G | 91.50 G | 8.73 G | 9.82 G | 0.32 | 2.99 | |
| memory-game | 35.37 G | 37.93 G | 13.06 G | 2.26 G | 0.93 | 15.68 | |
| dijkstra | 20.00 G | 7.23 G | 3.39 G | 1.50 G | 2.77 | 13.37 | −57% |
| octopus | 29.56 G | 15.15 G | 3.28 G | 2.47 G | 1.95 | 11.96 | |
| disk | 114.47 G | 18.70 G | 10.12 G | 6.36 G | 6.12 | 18.00 | −10% |
| expressions | 356.01 G | 20.35 G | 11.15 G | 6.09 G | 17.49 | 58.47 | −37% |
| scan | 362.03 G | 7.90 G | 956.77 M | 5.99 G | 45.81 | 60.40 | −32% |
| matcher | 76.01 G | 42.64 G | 15.27 G | 8.07 G | 1.78 | 9.42 | −12% |
| bridge | 121.98 G | 32.65 G | 6.78 G | 7.05 G | 3.74 | 17.31 | −19% |

Geometric means of the time ratios: native / CPython **5.5 → 4.7 → 3.9 → 3.5 → 2.9**, native /
Lean **23 → 20 → 16 → 14.9 → 12.0**. memory-game, binary-trees and pidigits fell in time only
(the previous run's noise going away; instructions unchanged). Raw files: Overmind's
`target/compare/2026-11-08T132842-overmind.{json,md}`.

## After the afternoon's work (Overmind, 8 Nov 2026 17:58, `e11c7b3c2`)

Same command and machine, 44 answers ok, 27.8 min. Adds SW-2363 (per-run cell cache), SW-2337
(Parse stage 2), SW-2405 (calls plus a number as loops) and SW-2415 (determined fields not
stored). Reference runners within about 1% of the previous run.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native instructions vs previous |
|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 1.32 s | 3.77 s | 3.29 s | 2.03 s | 0.35 | 0.65 | 0 |
| binary-trees | 2.88 s | 10.11 s | 1.58 s | 1.01 s | 0.29 | 2.85 | −26% (cell cache) |
| memory-game | 4.63 s | 8.39 s | 5.21 s | 782 ms | 0.55 | 5.93 | +0.7% |
| dijkstra | 2.67 s | 838 ms | 502 ms | 204 ms | 3.19 | 13.12 | −2% |
| octopus | 3.22 s | 1.51 s | 467 ms | 219 ms | 2.13 | 14.70 | −2% |
| disk | 14.17 s | 2.24 s | 1.91 s | 755 ms | 6.32 | 18.76 | −2% |
| expressions | 49.80 s | 2.13 s | 1.77 s | 660 ms | 23.36 | 75.42 | −3% |
| scan | 45.25 s | 825 ms | 135 ms | 585 ms | 54.86 | 77.30 | −9% (Parse stage 2) |
| matcher | 8.79 s | 4.62 s | 2.81 s | 853 ms | 1.90 | 10.30 | −2% |
| bridge | 16.12 s | 3.47 s | 1.20 s | 832 ms | 4.65 | 19.38 | −2% |

Instructions: pidigits 9.44 G, binary-trees 21.64 G, memory-game 35.61 G, dijkstra 19.59 G,
octopus 28.92 G, disk 112.39 G, expressions 344.68 G, scan 330.73 G, matcher 74.45 G, bridge
119.42 G (reference runners' counts unchanged from the previous run).

Geometric means of the time ratios: native / CPython **5.5 → 4.7 → 3.9 → 3.5 → 2.9 → 2.8**,
native / Lean **23 → 20 → 16 → 14.9 → 12.0 → 11.7**. binary-trees' time fell 7% for 26% fewer
instructions: the cell cache removed cheap instructions (SW-2363's report). What's left on
expressions and scan is mostly allocation and freeing (SW-2417; D3430). Raw files: Overmind's
`target/compare/2026-11-08T175841-overmind.{json,md}`.

## After the evening's small fixes (Overmind, 8 Nov 2026 22:59, `610279d59`)

Same command and machine, 1619 s. Adds SW-2433 (shared JumpK), SW-2440 (strong count only), SW-2443
(freeing cells with no deep fields), SW-2398/SW-2399 (Fin as numbers; AoC only). The reference runners
drifted 0–4% faster over the same interval, so about 2–3% of each native time change is common drift.

| Program | native | CPython | PyPy | Lean | native / CPython | native / Lean | native time vs previous | native instructions vs previous |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 1.29 s | 3.71 s | 3.22 s | 1.97 s | 0.35 | 0.65 | −2.3% | −0.1% |
| binary-trees | 2.66 s | 9.81 s | 1.46 s | 969 ms | 0.27 | 2.74 | −7.6% | −1.7% |
| memory-game | 4.34 s | 8.09 s | 5.20 s | 785 ms | 0.54 | 5.53 | −6.3% | +0.5% |
| dijkstra | 2.63 s | 840 ms | 507 ms | 204 ms | 3.13 | 12.88 | −1.5% | −3.8% |
| octopus | 3.09 s | 1.51 s | 474 ms | 220 ms | 2.04 | 14.07 | −4.0% | −5.1% |
| disk | 13.31 s | 2.24 s | 1.92 s | 754 ms | 5.95 | 17.64 | −6.1% | −7.4% |
| expressions | 47.61 s | 2.13 s | 1.76 s | 657 ms | 22.35 | 72.49 | −4.4% | −5.1% |
| scan | 43.94 s | 826 ms | 141 ms | 584 ms | 53.21 | 75.22 | −2.9% | −5.1% |
| matcher | 8.66 s | 4.61 s | 2.84 s | 853 ms | 1.88 | 10.15 | −1.5% | −2.5% |
| bridge | 15.47 s | 3.46 s | 1.21 s | 820 ms | 4.47 | 18.88 | −4.0% | −5.1% |

Geometric means: native / CPython **… → 2.8 → 2.7** (2.68), native / Lean **… → 11.7 → 11.3** (11.26).
Raw files: Overmind's `target/compare/2026-11-08T225859-overmind.{json,md}`.

**Build-mode step (SW-2474, 9 Nov 2026).** Every comparison above built `stitchwort` and its runtime
library in the devShell's incremental release mode (256 codegen units, no cross-unit inlining), which
makes native executables run about 3% more instructions (expressions 320.4 G vs 310.6 G) than the
distributed non-incremental build. From SW-2474 on, the timing tasks build non-incrementally into
`target/bench`, so the next run was expected to show a one-off step of about 3%. Correction (9 Nov 04:05): that 3% was measured on Speedwell (macOS); Overmind's next run (job 32, below) showed no step (instructions identical to job 26 wherever no code changed), so the earlier Overmind comparisons stand as they are. Why Linux builds don't show the difference is open (SW-2474).

## Job 32: the wide set, and R1 (Overmind, 9 Nov 2026 04:01, `096a27327`)

Same command, now built non-incrementally into `target/bench` (SW-2474), 2659 s. Adds SW-2462 (R1:
a resumption is one object) and the four wide programs (SW-2454, SW-2455). Not yet: SW-2463 (R2, R3).

| Program | set | native | CPython | PyPy | Lean | native / CPython | native / Lean | native instructions vs job 26 |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits | core | 1.24 s | 3.71 s | 3.22 s | 1.98 s | 0.33 | 0.63 | 0.0% |
| binary-trees | core | 2.67 s | 9.80 s | 1.48 s | 974 ms | 0.27 | 2.74 | 0.0% |
| memory-game | core | 4.29 s | 8.13 s | 5.24 s | 791 ms | 0.53 | 5.42 | 0.0% |
| dijkstra | core | 2.63 s | 843 ms | 506 ms | 204 ms | 3.13 | 12.94 | 0.0% |
| octopus | core | 3.09 s | 1.52 s | 477 ms | 220 ms | 2.03 | 14.05 | 0.0% |
| disk | core | 13.27 s | 2.23 s | 1.90 s | 754 ms | 5.94 | 17.59 | −0.4% |
| expressions | core | 47.39 s | 2.14 s | 1.78 s | 661 ms | 22.15 | 71.74 | −1.9% |
| scan | core | 43.30 s | 830 ms | 136 ms | 582 ms | 52.17 | 74.35 | −1.7% |
| matcher | core | 8.69 s | 4.61 s | 2.82 s | 857 ms | 1.89 | 10.14 | −0.4% |
| bridge | core | 15.51 s | 3.48 s | 1.21 s | 822 ms | 4.46 | 18.87 | −0.8% |
| spectral-norm | wide | 6.54 s | 9.43 s | 690 ms | 4.49 s | 0.69 | 1.46 | |
| const-fold | wide | 2.86 s | 23.83 s | 20.95 s | 1.13 s | 0.12 | 2.54 | |
| rbmap | wide | 2.83 s | 12.79 s | 5.07 s | 1.21 s | 0.22 | 2.34 | |
| rbmap-ck | wide | 1.56 s | 19.61 s | 3.06 s | 427 ms | 0.08 | 3.65 | |

Geometric means by time (native / CPython, native / Lean): core **2.66, 11.17**; wide **0.20, 2.37**;
all **1.26, 7.18**. By instructions: core 2.31, 10.80; wide 0.26, 3.04; all 1.25, 7.52.

On the programs Lean's developers chose (const-fold, rbmap, rbmap-ck) native is 2.3–3.7× Lean in time
and 5–12× faster than CPython; the core ten's 11× is dominated by the effect- and text-heavy programs
(expressions, scan at 72–74×). Raw files: Overmind's `target/compare/2026-11-09T040121-overmind.{json,md}`.

## Job 34: R2 and R3 (Overmind, 9 Nov 2026 05:42, `3f3ba9e6c`)

Same command as job 32, 2548 s. Adds SW-2463 (R2: the `Bind` node becomes the pending cell; R3: a
skipped forward reuses its `Call` cell). Not yet: SW-2485 (`Map.Tree.minOr`, disk −18.5% on Speedwell).

| Program | native time | native / CPython | native / Lean | native instructions vs job 32 |
|---|---:|---:|---:|---:|
| disk | 12.97 s | 5.78 | 17.21 | −2.1% |
| expressions | 45.07 s | 21.11 | 68.25 | −4.8% |
| scan | 42.23 s | 50.77 | 72.43 | −4.4% |
| matcher | 8.60 s | 1.87 | 10.09 | −1.0% |
| bridge | 15.05 s | 4.34 | 18.29 | −3.3% |
| (the other nine) | | | | within 0.1% |

Geometric means by time (native / CPython, native / Lean): core **2.62, 11.05**; wide **0.19, 2.42**;
all **1.25, 7.16**. By instructions: core 2.28, 10.63; wide 0.26, 3.04; all 1.23, 7.43.
Raw files: Overmind's `target/compare/2026-11-09T054222-overmind.{json,md}`.

## Over-fitting check with bench:aoc (Speedwell, 9 Nov 2026 05:55)

The first full `task bench:aoc` sweep (SW-2453) ran at 05:25 on main after SW-2485 (55/55 days
correct). Re-run at 05:55 after SW-2487 (`many` reuses its round's mark), which was found on the
disk and bridge profiles (SW-2484): 38 of the 55 days moved by more than 3%, every one faster, up to
−13.3% (2025/07), −11.9% (2020/06), −11.8% (2020/03); geometric mean of new/old instructions −2.54%;
no day slower by more than 1%. So the parser change generalises beyond the two benchmarks it came from.

## Job 35: parser library and minOr (Overmind, 9 Nov 2026 07:23, `7d137b9d7`)

Same command as job 34, 2351 s. New since job 34: SW-2485 (`Map.Tree.minOr`), SW-2487 and SW-2491
(`many` reuses its marks, no closures per round), SW-2495 (`pick` notes in one operation). Not yet:
SW-2499 (resumptions moved), SW-2502 (capture-free closures shared), compiled handler dispatch.

| Program | native time | native / CPython | native / Lean | native instructions vs job 34 |
|---|---:|---:|---:|---:|
| disk | 9.18 s | 4.07 | 12.05 | −33.2% |
| expressions | 37.29 s | 17.49 | 56.80 | −18.6% |
| scan | 39.92 s | 48.41 | 68.49 | −5.7% |
| matcher | 7.77 s | 1.69 | 9.07 | −8.2% |
| bridge | 12.75 s | 3.68 | 15.58 | −14.5% |
| dijkstra | 2.61 s | 3.10 | 12.86 | −1.2% |
| (the other eight) | | | | 0.0% |

Geometric means by time (native / CPython, native / Lean): core **2.41, 10.15**; wide **0.20, 2.43**;
all **1.18, 6.75**. By instructions: core 2.08, 9.69; wide 0.26, 3.04; all 1.15, 6.96. The library
changes behind these also cut the AoC sweep (`bench:aoc`) by 2.5% and 4.1% geomean, so they are not
specific to these programs. Raw files: Overmind's `target/compare/2026-11-09T072334-overmind.{json,md}`.

## Job 36: moved resumptions and shared closures (Overmind, 9 Nov 2026 08:06, `11f9f73ca`)

Same command as job 35, 2392 s. New since job 35: SW-2499 (an unshared resumption's fields moved),
SW-2502 (capture-free closures built once), SW-2481 and SW-2512 (checking only). Native instructions
against job 35: expressions −8.7%, scan −7.6%, bridge −6.7%, disk −4.2%, matcher −1.5%; others ≤ 0.5%.
Native time: expressions 52.9× Lean, scan 64.6×, bridge 14.8×, disk 11.8×.

Geometric means by time (native / CPython, native / Lean): core **2.36, 9.88**; wide **0.20, 2.45**;
all **1.17, 6.64**. By instructions: core 2.01, 9.41; wide 0.26, 3.04; all 1.13, 6.81.

**Regression:** rbmap-ck native time 1.55 s → 1.80 s (+16.2%) at unchanged instructions (10.65 G),
confirmed by a rerun at low load; rbmap unchanged. Under investigation (see the board).
Raw files: Overmind's `target/compare/2026-11-09T080649-overmind.{json,md}`.

## Job 39: record updates, R7 and mapops (Overmind, 9 Nov 2026 09:22, `9cc3fa3b8`)

Check 64 ok; 2372 s; peak memory 2.16 GB (const-fold). Report:
`target/compare/2026-11-09T092248-overmind.md` on Overmind.

| Program | native | CPython | Lean | native/CPython | native/Lean |
|---|---:|---:|---:|---:|---:|
| pidigits | 1.24 s | 3.71 s | 1.96 s | 0.33x | 0.63x |
| binary-trees | 2.65 s | 9.79 s | 972 ms | 0.27x | 2.73x |
| memory-game | 2.73 s | 8.15 s | 784 ms | 0.34x | 3.49x |
| dijkstra | 2.52 s | 843 ms | 204 ms | 2.99x | 12.34x |
| octopus | 2.61 s | 1.52 s | 219 ms | 1.72x | 11.93x |
| disk | 8.68 s | 2.23 s | 757 ms | 3.89x | 11.47x |
| expressions | 34.23 s | 2.13 s | 661 ms | 16.04x | 51.77x |
| scan | 37.09 s | 829 ms | 585 ms | 44.72x | 63.38x |
| matcher | 7.68 s | 4.60 s | 858 ms | 1.67x | 8.95x |
| bridge | 11.66 s | 3.47 s | 820 ms | 3.36x | 14.21x |
| spectral-norm | 6.40 s | 9.43 s | 4.48 s | 0.68x | 1.43x |
| const-fold | 2.90 s | 24.05 s | 1.05 s | 0.12x | 2.76x |
| rbmap | 2.82 s | 12.81 s | 1.21 s | 0.22x | 2.32x |
| rbmap-ck | 1.80 s | 19.65 s | 425 ms | 0.09x | 4.23x |
| mapops | 2.24 s | 827 ms | 451 ms | 2.71x | 4.97x |

Geomeans by time: core 2.18x CPython, 9.18x Lean (job 36: 2.36x, 9.88x);
wide, now with mapops, 0.34x and 2.86x (not comparable with job 36's four).
Instructions: core 1.84x and 8.58x.

Against job 36 (native, time; instructions): memory-game -37.9%; -45.6%,
octopus -13.6%; -14.6%, bridge -4.0%; -4.6%, disk -2.7%; -1.7%,
expressions -1.8%; -2.7%, scan -1.7%; -2.2%; others within 1%. Geomean
-5.2%; -6.3%. Most of it is SW-2514 (record updates take unique records
apart): it matches Speedwell's bridge and disk numbers, and memory-game and
octopus are record-update loops too. rbmap-ck is unchanged at 1.80 s
(SW-2523's layout regression remains, accepted).

## Job 40: compiled handler dispatch and context inlining (Overmind, 9 Nov 2026 10:17, `f9d2d8320`)

SW-2511 (compiled handler dispatch, with the Unpack unused-field change) and
SW-2531 (context inlining). Check 64 ok; 2245 s. Report:
`target/compare/2026-11-09T101739-overmind.md` on Overmind.

Geomeans by time: core 1.90x CPython, 7.99x Lean (job 39: 2.18x, 9.18x);
wide 0.32x and 2.68x (job 39: 0.34x, 2.86x); all 15: 1.04x and 5.55x.
Instructions: core 1.63x and 7.59x.

Against job 39 (native, time; instructions): scan -35.7%; -31.1%,
expressions -30.9%; -25.9%, bridge -25.3%; -21.3%, mapops -21.1%; -24.6%,
disk -18.8%; -17.2%, rbmap-ck -10.8%; -4.4%, matcher -5.2%; -3.9%,
dijkstra -5.0%; -7.3%. Geomean over 15: -10.7%; -10.4%. Instruction drops
match Speedwell's predictions within a point (disk and dijkstra a little
better).

Time worse than instructions: rbmap +1.5% time at -8.5% instructions (a
10-point gap, tight runs), memory-game +4.0% at -1.1%, binary-trees +2.2% at
0%. Suspected: the Unpack change (cells returned to the cache) altering
locality, as in SW-2523. Overmind is comparing perf counters of jobs 39 and
40. rbmap-ck recovered about two thirds of SW-2523's 16%.

## Closing record (10 Nov 2026)

Matt wound the speed work down on 10 Nov (D3465). The epics performance,
comparative-speed and dev-loop-speed are paused and their backlog tickets carry
the `parked` label. This section is for whoever restarts it. Every figure is
marked **measured** (a run or a counter) or **estimated** (a profile-based
guess or an extrapolation).

### Final comparison (measured)

Overmind (Linux, 8 threads), commit `292a85385`, runners native, cpython, pypy
and lean. All 64 answers checked correct; 2,018 s. Geomeans of time, native
relative to the other runner, lower is better; job 40 (`f9d2d8320`) in brackets.

| Set | native / CPython | native / Lean |
|---|---:|---:|
| Core (10 programs) | 1.82x (1.90x) | 7.67x (7.99x) |
| Wide (5 programs) | 0.31x (0.32x) | 2.60x (2.68x) |
| All 15 | 1.01x (1.04x) | 5.35x (5.55x) |

Moved more than 10% since job 40: binary-trees 2.70 -> 2.14 s (-21%),
memory-game 2.85 -> 2.42 s (-15%). Most likely borrowed parameters (SW-2565, below) and the
cell cache's exact count (SW-2559), both merged after job 40 (an attribution
from the merge order and the instruction counts, not a separate run).

Not covered: no instruction counts this run, and the JavaScript backend wasn't
timed. AoC 2021 day 15 under `run --js` grows roughly as n^4 with the grid
width and doesn't finish on the full input (SW-2636, parked). The raw report is
on Overmind: `target/compare/2026-11-10T095143-overmind.md`.

### 1. Where it started and where it ended (measured)

Core ten, geomean of time, first comparison against last:

| | 8 Nov 00:25, `e8e9acd1e` | 10 Nov, `292a85385` |
|---|---:|---:|
| native / CPython | 5.46x | 1.82x |
| native / Lean | 23.06x | 7.67x |

That is 3.0x closer to both. Per program, start against job 39 (9 Nov 09:22;
all measured, native seconds):

| Program | start | job 39 |
|---|---:|---:|
| pidigits | 1.55 | 1.24 |
| binary-trees | 4.31 | 2.65 |
| memory-game | 8.27 | 2.73 |
| dijkstra | 12.97 | 2.52 |
| octopus | 15.94 | 2.61 |
| disk | 21.06 | 8.68 |
| expressions | 86.30 | 34.23 |
| scan | 81.85 | 37.09 |
| matcher | 15.73 | 7.68 |
| bridge | 22.53 | 11.66 |

(Job 40 then took scan, expressions and bridge down another 25-36% in
instructions; the last run's per-program table is in Overmind's report.) The
wide set joined on 9 Nov, so it has no start: its four first programs were 0.20x
CPython and 2.37x Lean at job 32; with mapops added the five are 0.31x and
2.60x now. The two sets aren't comparable.

Where it stands: native beats CPython overall (1.01x over all 15, 0.31x on the
wide set) and on pidigits, binary-trees, memory-game and the Lean programs. It
is still 5-8x Lean's compiled code, and slow against CPython on the parsing
programs (expressions and scan were 16x and 45x CPython at job 39).

### 2. What moved the numbers

Core geomean against CPython went 5.46 -> 4.71 -> 3.88 -> 3.55 -> 2.87 -> 2.78
-> 2.68 -> 2.66 (job 32) -> 2.41 -> 2.18 -> 1.90 -> 1.82 (all measured, in
`history.toml`). The changes that mattered most:

1. **Inline operations and cheaper cells (8 Nov night).** Hole operations
   (SW-2328), comparisons and arrays (SW-2329), cells through fixed-size helpers
   (SW-2321). memory-game 8.26 -> 4.67 s, binary-trees 4.29 -> 3.09 s,
   geomean 4.7 -> 3.9x CPython (measured).
2. **Data-structure fixes for specific programs.** Octopus's O(1) grid
   (SW-2320): 15.9 -> 5.1 s. Dijkstra over a cost table (SW-2394, SW-2396) and
   reuse across calls (SW-2391): 11.8 -> 2.6 s. One-pass `flatMap` (SW-2323):
   matcher 15.7 -> 12.6 s. Big numbers by reference (SW-2302): pidigits
   1.55 -> 1.32 s (all measured).
3. **Handlers and the effect loop.** Operations in place stage B (forwarding
   skipped, SW-2349), effect-runtime allocation R1-R3 and R7 (resumption one
   object, bind node reused: SW-2462 -1.7%, SW-2463 -3.4% on expressions),
   resumptions moved and closures shared, then compiled handler dispatch plus
   context inlining (SW-2511, SW-2531): job 40 took scan -35.7%,
   expressions -30.9%, bridge -25.3% in time (measured).
4. **Record updates take a unique record apart (SW-2514).** AoC's house style;
   memory-game -37.9%, octopus -13.6% (time, measured at job 39).
5. **Borrowed parameters, stage B1 (SW-2565).** Read-only walks stop counting
   every node. mapops -6.4%, memory-game -19.3% (instructions, measured); the
   final run shows binary-trees -21% and memory-game -15% in time.
6. **Method.** Instructions retired as the primary measure, non-incremental
   builds (SW-2474), the wide set, `bench:aoc` as an over-fitting check.

What caps it: allocation and freeing are about half of native time on the
parsing programs, the effect machinery about a fifth (SW-2417, estimated from a
profile).

### 3. What didn't work (or was held)

All of these have entries in [docs/performance/log.md](../performance/log.md).

- **SW-2593** (search hole typing): typed 98.6% of proof variables, but recall
  is unchanged and the full-tier search benchmark is 14% slower (257 -> 293 s,
  measured). Not merged; branch `lane/SW-2593` kept. Merge only with a recall
  gain or no slowdown.
- **SW-1734** (nextest threads for the heavy sweeps): no measured benefit under
  load; closed unmerged.
- **SW-1776** (elab unit tests in their own binary): clean test build 164 ->
  144 s (measured, one run), but every new elab unit test needs three edits
  (D2565 never taken up). Closed unmerged.
- **SW-2486** (fused `token nat`): bridge -21% in instructions (measured), but
  every call site must be rewritten, including the benchmark's own source:
  over-fitting. Dropped; the clean form is SW-2625.
- **SW-2350** (operations in place stage C): effect-loop steps 3-26x fewer but
  machine time only 1.04-1.11x (measured), against an expected 2-3x. Matt
  stopped operations in place after stage B (D3430); branch `lane/SW-2350` kept
  as the record.
- **SW-2441** (compact values, option E): the experiment gave 1.09x on the
  decision set and 1.165x on binary-trees, below the 1.10x and 1.25x gate
  (measured). Not built (D3435).
- **SW-814** (fused Map balance): -0.17% on `bench:aoc` (measured); dropped. It
  looks better on mapops (SW-2515, below), so judge it again there.
- **SW-2488, SW-2494:** `replicate ++` without the copy (at most 1%) and a
  `literalText` operation (expressions +0.9%, scan -3.2%) dropped.
- **SW-2523:** rbmap-ck +16% in time at equal instructions; mostly recovered by
  job 40, cause never found (SW-2538 and SW-2560 are the same kind of
  mystery).

### 4. Remaining ideas, best first

Gains are per program and **estimated** unless said otherwise.

1. **SW-2625**, fuse `token nat` inside the parser: bridge -14 to -23%
   (extrapolated from the measured -21% of SW-2486), no new API.
2. **SW-2515**, inline Map balance/rebuild into `insertWith` (a further
   -25.6% on mapops by hand; SW-2539 adds 2-3%). Retest SW-814 there.
3. **SW-2464, SW-2465, SW-2496, SW-2500**, effect-runtime allocation R4/R5 and
   state clauses without a Jumped object: expressions -2.9 to -5.0% and scan
   -4.0 to -6.9% for R4, -1.2 to -2.4% for R5, -2.3 to -4.4% for SW-2500.
4. **SW-2431**, huge pages for native's heap. dTLB misses are 580-1100x Lean's
   on memory-game and binary-trees (measured, SW-2426); the gain is unknown.
5. **SW-2437**, store forwarding in value copies: expressions and scan spend
   5.9-6.2% of cycles on a full store buffer against Lean's 0.05-0.09%
   (measured); the gain is unestimated.
6. **SW-2577, SW-2521, SW-2528**, borrow inference follow-ups (lambda captures
   counted as owned, closures borrowing their function, the effect loop
   borrowing the step function: 60-100 instructions per operation).
7. **SW-2322**, a cheaper call protocol (limits and error flag in registers),
   no estimate.
8. **SW-2441's option E** (compact values) stays at about 1.09x; not worth it
   unless the gate changes.

Also parked: SW-2636 (`--js` day 15 at n^4), SW-2501 (`labelWhole` is
exponential in nesting depth), SW-2411 (the bench baseline is out of date).

### 5. How to restart

Read first: this file's job 40 and final sections, then
[docs/performance/log.md](../performance/log.md) ("How things are measured" and
the 9-10 Nov entries), then the parked tickets (`board/board epic
comparative-speed`). Matt's rule from the work: profile first, change only a
measured hotspot, and don't edit a benchmark's source to speed it up.

```
task bench:instructions            # instructions retired for the 15 programs; --save, --against
task bench:aoc                     # every AoC day, answer-checked, geomean (over-fitting check)
task bench:compare -- --runners native,cpython,pypy,lean   # on a quiet machine (Overmind)
```

Run the comparison on a quiet machine with nothing else running; it takes about
35 min with the wide set (2,018 s last time). The last run had no instruction
counts; `task bench:instructions` gives them separately. Then add the entry to `bench/compare/history.toml`
(still by hand, SW-2469) and a section here. Re-record the bench baseline
(`task bench:update`, which writes `bench/baseline.toml`; checked by `task
bench`) before judging any regression. Reference runners drift 0-4% between
runs, so only trust a native change larger than that.
