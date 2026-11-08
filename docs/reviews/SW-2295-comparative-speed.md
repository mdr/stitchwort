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
