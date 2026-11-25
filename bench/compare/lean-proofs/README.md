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

`--runs N` hyperfine runs of each command (default 5; hyperfine 1.21 from the
flake, or 2.0; one untimed warmup each). Run it on a quiet machine and record
`uptime` first (the bench saves the load averages at its start in its JSON).
Every figure is a median with the range of its runs in brackets, and every
ratio is a range, never one number: the median over the middle of the
extremes, `smallest top / largest bottom` to `largest top / smallest bottom`
(SW-4816 finding 3; the ranges are wide on purpose).

- **The build.** `cargo build --release -p stitchwort-cli`, without
  `{{.DEV_FEATURES}}`: the dev features turn on core's `reference` feature,
  whose `validate_marks` re-checks every installed declaration and costs
  12-25% of a library-cached run (SW-4809). The binary people run has none.
- **No probe file.** An earlier version subtracted a cold check of a
  hand-written file that imported the day's std modules. It never loaded
  every std file the day does (day 18 also checks `Parse/ReadsChars` and
  `RunsChars`, 975 ms), so those landed in "sw net" (SW-4809, SW-4810).
  "sw net" is read from the day's own runs: the elaboration plus kernel
  time of the `--timings=all` unit table's rows that are neither `core` nor
  `std/...`, i.e. the day's namespaces. It excludes parsing, the library
  index and project scan, which are fixed costs and show in the other columns.
  It is a median over N separate `--timings=all` runs (SW-4818).
- **Columns.**
  - `sw check (cold)`: wall time of `check --no-cache <namespaces> --only
    <the theorems this folder's file also has>` from `aoc/`: library and
    day all rechecked from source.
  - `sw net`: the day's own units, as above; "of it Aoc.Common" is the part
    of it in `Aoc.Common...` units (day 15 only).
  - `lean file`, `lean load`, `lean net`: `lean` on the day's file, on a file
    that only imports `Lib`, and their difference (its range: the file's
    smallest less the load's largest, to the file's largest less the load's
    smallest).
  - `sw net / lean net`: the ratio of proof work, as a range.
  - `sw cached, one job`: wall time of `check --no-project-cache` of the
    same namespaces and `--only` theorems with the library cache warm (the
    warmup run fills it): the whole run including startup, index and scan,
    our counterpart of Lean's precompiled `.olean`. Its ratio to `lean file`
    is the end-to-end figure (as a range). `--only` and `--no-project-cache`
    each force one job, so this row is always one job.
  - `sw floor, one job` / `default jobs`: `check <namespaces>` (no `--only`,
    all theorems) with every cache warm and nothing changed, with
    `STITCHWORT_JOBS=1` and with it unset (the default `auto` jobs). This is
    the floor every check after an unrelated edit pays, and the only way to
    time default jobs, since the like-for-like command is forced to one job. It
    does not check the same set of theorems as the other rows (it reads them all
    from the cache).
  - `lake build (cold)`: Lib plus the day, `.lake` deleted first.
- **CPU time.** A third table gives hyperfine's user + system time next to
  the wall time for `sw cached`, `lean file`, `lean load` and the default-jobs
  floor. They are means over the runs (hyperfine 1.x gives only the mean; 2.0's
  per-run values are averaged too). Lean elaborates and kernel-checks on several
  threads, so its CPU time can exceed its wall time; ours with one job cannot.
  Net CPU, if wanted, is the file's less the load's.
- hyperfine's JSON is read in 2.0's format (`measurements[].time_wall_clock.value`) or 1.x's (`times`; the flake has 1.21);
  a missing key or a wrong number of runs stops the bench.

## What each side's net leaves out

- **`sw net` leaves out** parsing, the library index, the project scan, core's
  elaboration and loading library entries: per-process fixed costs that appear
  in `sw cached` and the floor rows. It is the sum of unit timers (CPU-like, on
  one job), the Lean figure is wall time.
- **`sw net` includes** all declarations of the namespaces it names that the
  `--only` set needs, and, for day 15, all of `Aoc.Common`: `--only` trims
  only the named namespaces, so the whole shared `Aoc.Common` unit (about
  700 declarations: bit readers, life, planes, prefix sums) is checked, while
  the Lean port covers only the grid parts, about 25 `Aoc.Common.Proofs`
  lemmas (SW-4816 finding 8). The "of it Aoc.Common" column says how much of
  day 15's net that is; the truth for the ratio is between the figure with and
  without it, since Lean ports some of it.
- **`lean net` leaves out** Lean's start-up and the import of `Lib` (the
  empty file is exactly `import Lib`, and every day file imports only `Lib`,
  so the subtraction removes the same load the day file does; what remains is
  the day file's elaboration, definitions and theorems, plus any variation of
  the load between the two runs, which is why its range is wide). It also
  leaves out the 3 theorems of day 15 and the 26 of day 18 not ported, and
  the parsers. Lean's net includes its own definitions' compilation (a
  `def` is compiled to IR; Stitchwort's checker has no equivalent step).
- Both leave out the other side's cost of the unported parts: Stitchwort checks
  the day's definitions that no ported theorem needs; Lean has none of them.
