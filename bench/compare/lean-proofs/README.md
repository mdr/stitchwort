# Lean ports of three days' proofs

For the checking-speed comparison (docs/proposals/comparative-speed.md section 3).
Lean 4.34.1, core and `Std` only. `lake build` must print no `sorry` warning;
`task bench:compare:proofs` checks that before it times anything.

| File | Stitchwort source | Ported | Left out |
|---|---|---|---|
| `Proofs/Day2024_02.lean` | `Aoc/Year2024/Day02` | all 17 theorems | the parser |
| `Proofs/Day2020_18.lean` | `Aoc/Year2020/Day18` | 23 of 49: the grammar's own combinatorics (`chainOf`, `Exact`, `Stop`, `GoodSteps`) and the answer's arithmetic | the other 26 are about `Std.Parse`'s `Reads`/`Runs` (about 5,600 lines of library) |
| `Proofs/Day2021_15.lean` | `Aoc/Year2021/Day15` and the `Aoc.Common` grid lemmas it uses | 20 of 23, plus about 25 `Aoc.Common.Proofs` lemmas | `parseRectangle`, `part1FromInput`, `part2FromInput` (parser) |

`Lib.lean` holds the list lemmas Stitchwort's standard library already
provides (`chain`, `count` congruences, `any_or`), built before the days and
not counted in a day's `lean` time (it is in the cold `lake build`).

Differences from the Stitchwort side, which the numbers must be read with:

- Stitchwort's side checks `stitchwort check --only` the theorems whose names
  the day's Lean file also has (and what those use), so it does the same
  theorems' work as Lean does; the other theorems of the namespaces are not
  checked. A namespace's remaining definitions are still all checked.
- Std's Dijkstra (`Graph.distancesShortest`) is a hypothesis (`Dijkstra`), and
  its result map is a function `Position -> Option Nat`, not a `TreeMap`.
- `Nat.iterate` is defined in the file (core has none).

## How `task bench:compare:proofs` measures

Medians of `--runs N` hyperfine runs (default 5; hyperfine 2.0, one untimed
warmup each). Run it on a quiet machine and record `uptime` first.

- **The build.** `cargo build --release -p stitchwort-cli`, without
  `{{.DEV_FEATURES}}`: the dev features turn on core's `reference` feature,
  whose `validate_marks` re-checks every installed declaration and costs
  12-25% of a library-cached run (SW-4809). The binary people run has none.
- **No probe file.** An earlier version subtracted a cold check of a
  hand-written file that imported the day's std modules. It never loaded
  every std file the day does (day 18 also checks `Parse/ReadsChars` and
  `RunsChars`, 975 ms), so those landed in "sw net" (SW-4809, SW-4810).
  "sw net" is now read from the day's own run: the elaboration plus kernel
  time of the `--timings=all` unit table's rows that are neither `core` nor
  `std/...`, i.e. the day's namespaces. It excludes parsing, the library
  index and project scan, which are fixed costs and show in the other columns.
- **Columns.**
  - `sw check (cold)`: wall time of `check --no-cache <namespaces> --only
    <the theorems this folder's file also has>` from `aoc/`: library and
    day all rechecked from source.
  - `sw net`: the day's own units, as above.
  - `lean file`, `lean load`, `lean net`: `lean` on the day's file, on a file
    that only imports `Lib`, and their difference.
  - `sw net / lean net`: the like-for-like ratio of proof work.
  - `sw check (library cached)`: wall time of `check --no-project-cache` of
    the same namespaces with the library cache warm (the warmup run fills it):
    the whole run including startup, index and scan, our counterpart of Lean's
    precompiled `.olean`. Its ratio to `lean file` is the end-to-end figure.
  - `lake build (cold)`: Lib plus the day, `.lake` deleted first.
- hyperfine's JSON is read by `measurements[].time_wall_clock.value`; a
  missing key or a wrong number of runs stops the bench.
