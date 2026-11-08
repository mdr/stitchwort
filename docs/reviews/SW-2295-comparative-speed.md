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
