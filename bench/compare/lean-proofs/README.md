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
