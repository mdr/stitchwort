# AoC programs: where forward chains read better (SW-1291, stage 1)

Survey of the AoC program code (`aoc/src/Aoc/Year*/Day*/Day*.sw` and
`aoc/src/Aoc/Common/*.sw`; not Spec, Proofs or Tests) for the style Matt
chose on day 5, `passes.map .seatId |> .sort |> gap` instead of
`(passes.map (.seatId)).sort |> gap` (4 Nov 2026), plus two related rules
from the same day: name positional runs of numbers and booleans at a call
site (D2367), and print an `Option` answer in `main` with
`answer |> .orFail "<what's missing>"`.

Everything below was found by pattern greps over all 60 program files
(6,544 lines) and then read site by site. **Every `rewrite` and `optional`
`after` below was applied to a copy of the file and checked with
`../target/release/stitchwort check <namespace>` from `aoc/`, on the day's
namespace and its `.Proofs` and `.Tests` namespaces where they exist; all of
them elaborate** (a script did one site at a time and reverted each; the few
multi-line sites were checked by hand the same way, on the day's namespace only). Nothing in the tree is
changed by this survey.

## Summary

| Pattern | Sites | rewrite | optional | leave |
|---|---:|---:|---:|---:|
| F. bracketed receiver of `orFail` / `Fail.need` | 11 | 8 | 3 | 0 |
| G. `main` prints an `Option` with `fold` / `getOrElse` / `match` | 10 | 9 | 1 | 0 |
| C. `(.field)` in brackets where bare `.field` works | 3 | 3 | 0 | 0 |
| A. `(f x).method` | 49 | 9 | 19 | 21 |
| B. `f (xs.chain)` (wrapper around a chain) | 18 | 1 | 8 | 9 |
| D. lambda that is a section (`x => x.f …`, `x => x op …`) | 29 | 22 | 0 | 7 |
| E. lambda that is a partial application (`x => f a x`) | 7 | 7 | 0 | 0 |
| H. positional runs of number literals | 15 | 13 | 0 | 2 |
| I. a lone bool or number flag | 5 | 1 | 2 | 2 |
| **Total** | **147** | **73** | **33** | **41** |

`rewrite` = clearly better (a chain replaces brackets, or a section/name
replaces a lambda or a bare number). `optional` = correct but marginal: a
single `(f x).g` becomes `f x |> .g`, or `f (xs.map g)` becomes
`xs.map g |> f`, with the same number of steps and one pair of brackets fewer.
`leave` = the brackets stay, with the reason in the table. Sites of one
pattern in one definition are listed separately (one row per line).

Counted but not listed, all `leave`:

- 43 lines with a tuple-pattern lambda, `(((a, b)) => …)`. The three
  brackets there are the pattern's, not nesting. A section (`.snd`) would
  lose the names, and std has no `uncurry`.
- 8 lambdas that are the identity, `(found => found)` / `(bit => bit)` /
  `(tile => tile)` (2021 day 3:49, 2024 days 4:40, 4:67, 9:43, 10:44, 24:202,
  24:239, 2025 day 7:107). std has no `id`, no `Option.flatten`, no
  `List.catOptions`, so there is nothing shorter to write (a finding below).
- About 40 more bracket-depth-3 lines that are constructor nesting,
  arithmetic inside brackets, or proof terms.

## What the language accepts and rejects

Checked on real sites (the survey table marks each); nothing needed a
language change except as noted.

Accepted:

- `x |> .f` in every place a bracketed receiver was: a `let`, a function body,
  before `else`/`then` (`then graph.breadthFirst [low] |> .size else 0`), in
  an `if` condition, in a record field, in `${…}` interpolation, and on the
  left of `==` (`|>` binds tighter than `==` and `∧`, so
  `segments.map wiring.at |> .sort == segments` is `(…|> .sort) == segments`).
- `|>` into a plain function, `rules.map f |> Map.fromList`, and
  `lines.flatMap g |> Map.counts |> .count (…)`.
- A bare section as an argument, including as the last argument after
  other arguments: `Parse.satisfy "a letter" .isAsciiLetter`,
  `.map .fst`, `tiles.map .x`, `.sumBy .testValue`.
- A section chaining fields: `.map .fst.position` (replacing
  `entry => entry.fst.position`).
- Sections with arguments or operators, in brackets: `(.remove span.start)`,
  `(.step horizontal)`, `(.startsWith "t")`, `(.start < before)`,
  `(.snd != Wall)`, and operator sections `(!= 9)`, `(≠ 9)`, `(9 !=)`,
  `(* file.id)`.
- Partial application where a lambda only forwards its argument:
  `.filter warehouse.boxes.contains`, `.flatMap (Instruction.decode opcode)`,
  `.sumBy (Nat.iterate 2000 nextSecret)`, `.map (tokens aPresses)`, `.all not`.
- Named arguments: on functions (`between (low := 150) (high := 193) …`),
  on `def`s with `auto` parameters (`Space.of (width := 101) (height := 103)`),
  on constructors (`Continue unvisited (spare := False)`), on std functions
  (`Parse.repeat (atLeast := 7) (atMost := 7) p`, `natDigits (atLeast := 1)
  (atMost := 3)`, `List.range (from := 2) (until := n)`, `hit.shiftRight (fill :=
  False)`), and before a pipe (`maze.graph (backwards := False) |> .distances …`).

Rejected, or not available:

- `x |> f a` passes `x` as the **first** argument only. Where the chain is
  the *last* argument, `addAll Map.empty (polymer.zipWithNext.map …)`,
  `Nat.iterate steps f seed`, the pipe form is `E-TYPE-MISMATCH`. Such sites
  stay bracketed (2021 day 14: 90, 94, 120).
- Parameters declared with arrow types have no names: `Nat.iterate (count :=
  2000) …` is `E-UNKNOWN-NAME` ("its parameters are `[a]`"). Affected:
  `Nat.iterate`, `List.rangeFrom` (used with two numbers in `Common/Range.sw:26`,
  2020 day 3:45, 2024 day 9:129), `Vec.shiftRight`'s first parameter. The
  fix is in std, not in the programs (a finding below).
- A section with arguments as an argument needs brackets (as documented):
  `buyers.sumBy .iterate 2000 nextSecret` is `E-NOT-A-FUNCTION`.
- A dot call needs the function in the receiver's namespace:
  `passages.paths (spare := False)` is `E-UNKNOWN-FIELD`, because `paths` is
  a day-level function, not `List.paths`. The after is
  `paths passages (spare := False) |> .length`.

## Sites

"Proofs mention it?" is a `git grep -w` of the **enclosing definition's
name** in the day's `Proofs/` (all `Proofs/` trees for `Common/`); a hit
means a proof names that definition, not that it unfolds the changed line.
Because `|>` and sections are plain application and lambda sugar, the
elaborated terms should not change, and every listed namespace (including
`.Proofs`) still checked after the edit. Where a proof states a body
literally and Matt cares about the text, the hit is the place to look. `main`
is `n/a`.

### F. A bracketed receiver of `orFail` / `Fail.need`

11 sites: 8 rewrite, 3 optional, 0 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2020/Day01/Day01.sw:24` (`main`) | `(solvePart1 entries).orFail "no two entries sum to 2020"` | `solvePart1 entries \|> .orFail "no two entries sum to 2020"` | rewrite | n/a | elaborates |
| `Year2020/Day01/Day01.sw:25` (`main`) | `(solvePart2 entries).orFail "no three entries sum to 2020"` | `solvePart2 entries \|> .orFail "no three entries sum to 2020"` | rewrite | n/a | elaborates |
| `Year2021/Day03/Day03.sw:30` (`main`) | `Fail.need (solvePart2 numbers) "the filtering didn't end with one number"` | `solvePart2 numbers \|> .orFail "the filtering didn't end with one number"` | rewrite | n/a | elaborates |
| `Year2021/Day04/Day04.sw:27` (`main`) | `Fail.need (solvePart1 game) "no board wins"` | `solvePart1 game \|> .orFail "no board wins"` | rewrite | n/a | elaborates |
| `Year2021/Day04/Day04.sw:28` (`main`) | `Fail.need (solvePart2 game) "no board wins"` | `solvePart2 game \|> .orFail "no board wins"` | rewrite | n/a | elaborates |
| `Year2024/Day16/Day16.sw:228` (`bestScore`) | `Fail.need (maze.lowestScore fromStart) "no path from the start to the end"` | `maze.lowestScore fromStart \|> .orFail "no path from the start to the end"` | optional | none | not in main: a helper that turns None into a failure; elaborates |
| `Year2024/Day18/Day18.sw:33` (`sizesFrom`) | `(Fail.need sizeText.toNat usage, Fail.need fallenText.toNat usage)` | `(sizeText.toNat \|> .orFail usage, fallenText.toNat \|> .orFail usage)` | optional | none | elaborates |
| `Year2024/Day20/Day20.sw:29` (`thresholdFrom`) | `Fail.need saving.toNat usage` | `saving.toNat \|> .orFail usage` | optional | none | elaborates |
| `Year2025/Day04/Day04.sw:40` (`main`) | `(parseGrid IO.readAllLines()).orFail` | `parseGrid IO.readAllLines() \|> .orFail` | rewrite | n/a | Result.orFail; elaborates |
| `Year2025/Day06/Day06.sw:28` (`main`) | `(checkWorksheet IO.readAllLines()).orFail` | `checkWorksheet IO.readAllLines() \|> .orFail` | rewrite | n/a | Result.orFail; elaborates |
| `Year2025/Day07/Day07.sw:34` (`main`) | `(checkManifold IO.readAllLines()).orFail` | `checkManifold IO.readAllLines() \|> .orFail` | rewrite | n/a | Result.orFail; elaborates |

### G. `main` prints an `Option` with `fold`, `getOrElse` or `match`

10 sites: 9 rewrite, 1 optional, 0 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2024/Day14/Day14.sw:39` (`solveIn`) | `${solvePart2 space robots \|> .fold "none" Nat.toText}` | `${solvePart2 space robots \|> .orFail "no second shows a picture"}` | rewrite | none | Behaviour change: None now fails `main` instead of printing `none`; Tests/Examples.sw:234 (`main with no picture`) expects `Part 2: none` and must change to `MkPair ["Part 1: 3564"] (Err "…")`.; elaborates |
| `Year2024/Day18/Day18.sw:26` (`main`) | `${solvePart1 size fallen bytes \|> .fold "none" Nat.toText}` | `${solvePart1 size fallen bytes \|> .orFail "the exit is cut off even before the first byte falls"}` | rewrite | n/a | wording to be fixed in stage 2 from the puzzle text; elaborates |
| `Year2024/Day18/Day18.sw:27` (`main`) | `IO.print "Part 2: ${solvePart2 size bytes \|> .fold "none" (byte => "${byte.column},${byte.row}")}"` | `let blocker := solvePart2 size bytes \|> .orFail "no byte cuts the exit off" ⏎ IO.print "Part 2: ${blocker.column},${blocker.row}"` | rewrite | n/a | the payload is a Position, so it needs a `let`; no `Position.toText` in Aoc.Common; elaborates (hand-checked) |
| `Year2024/Day24/Day24.sw:19` (`main`) | `${solvePart1 device \|> .fold "none: a wire starting with z gets no value" (number => "${number}")}` | `${solvePart1 device \|> .orFail "a wire starting with z gets no value"}` | rewrite | n/a | elaborates |
| `Year2024/Day24/Day24.sw:20` (`main`) | `${solvePart2 device \|> .getOrElse "the repair search found no four swaps that make an adder"}` | `${solvePart2 device \|> .orFail "the repair search found no four swaps that make an adder"}` | rewrite | n/a | same shape; the message is the fallback text today (`Option Text`); elaborates |
| `Year2024/Day17/Day17.sw:18` (`main`) | `let lowest := match solvePart2 debugger with \| Some a => "${a}" \| None => "none: no initial value of A outputs the program" ⏎ IO.print "Part 2: ${lowest}"` | `IO.print "Part 2: ${solvePart2 debugger \|> .orFail "no initial value of A outputs the program"}"` | rewrite | n/a | lines 18-22; elaborates (hand-checked) |
| `Year2021/Day17/Day17.sw:27` (`main`) | `match solvePart1 target with \| Some height => IO.print "Part 1: ${height}" \| None => IO.print "Part 1: no velocity hits"` | `IO.print "Part 1: ${solvePart1 target \|> .orFail "no velocity hits the target"}"` | rewrite | n/a | lines 27-30; elaborates (hand-checked) |
| `Year2021/Day18/Day18.sw:30` (`main`) | `match solvePart1 numbers with … \| None => IO.print "Part 1: no answer" (and the same for part 2, lines 34-36)` | `IO.print "Part 1: ${solvePart1 numbers \|> .orFail "no numbers to add"}" ⏎ IO.print "Part 2: ${solvePart2 numbers \|> .orFail "fewer than two numbers"}"` | rewrite | n/a | lines 30-36; elaborates (hand-checked) |
| `Year2021/Day11/Day11.sw:28` (`main`) | `${describe (solvePart2 levels)}  (describe, lines 92-95, matches Some/None)` | `${solvePart2 levels \|> .orFail "no step within ${syncLimit} has every octopus flash"}` | rewrite | n/a | `describe` (lines 92-95) goes; nothing else uses it; elaborates (hand-checked) |
| `Year2025/Day08/Day08.sw:27` (`main`) | `match solvePart2 boxes with \| None => IO.print "Part 2: the boxes are already in one circuit." \| Some answer => IO.print "Part 2: ${answer}"` | `IO.print "Part 2: ${solvePart2 boxes \|> .orFail "the boxes are already in one circuit"}"` | optional | n/a | None is a legitimate outcome (the input is already one circuit), not a missing answer: ask Matt; lines 27-29; elaborates (hand-checked) |

### C. `(.field)`: a bare section in brackets

3 sites: 3 rewrite, 0 optional, 0 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2024/Day24/Day24.sw:121` (`Device.wires`) | `List.append (device.initial.map (.fst)) (device.gates.flatMap (gate => […]))` | `device.initial.map .fst \|> .append (device.gates.flatMap (gate => […]))` | rewrite | Proofs/Adder.sw, Proofs/Complete.sw, Proofs/Lemmas.sw, Proofs/Part1.sw, Proofs/P | elaborates (hand-checked) |
| `Year2024/Day24/Day24.sw:169` (`outputOf`) | `\|> .map (.output)` | `\|> .map .output` | rewrite | Proofs/Adder.sw | elaborates |
| `Year2024/Day24/Day24.sw:251` (`wellWired`) | `gates.map (.output) \|> .allDistinct` | `gates.map .output \|> .allDistinct` | rewrite | Proofs/Part2.sw | elaborates |

### A. `(f x).method`: a bracketed receiver that `|>` removes

49 sites: 9 rewrite, 19 optional, 21 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Common/Grid.sw:184` (`Grid.lookup`) | `(table.getOr position.row Map.empty).getOr position.column None` | `table.getOr position.row Map.empty \|> .getOr position.column None` | rewrite | 3 files | two-step lookup; elaborates |
| `Common/Grid.sw:191` (`Grid.lookupOr`) | `(table.getOr position.row Map.empty).getOr position.column fallback` | `table.getOr position.row Map.empty \|> .getOr position.column fallback` | rewrite | 2 files | elaborates |
| `Common/GridGraph.sw:71` (`cellsGraph`) | `((cells rows).map Pair.fst)` | `(cells rows \|> .map Pair.fst)` | leave | – | already inside an argument bracket: no bracket saved |
| `Common/GridGraph.sw:81` (`cellsEnterListed`) | `position ∈ (cells rows).map Pair.fst` | `—` | leave | – | theorem statement (`∈` reads better with the brackets) |
| `Common/GridGraph.sw:92` (`memCellsOfCellAt`) | `(List.memGridCells rows row column x).backward (…)` | `—` | leave | – | inside a proof term |
| `Common/Offset.sw:48` (`Position.offset`) | `match (position.row.toInt + offset.rows).toNatChecked with` | `—` | leave | – | arithmetic receiver: a pipe would need the same brackets |
| `Common/Offset.sw:51` (`Position.offset`) | `match (position.column.toInt + offset.columns).toNatChecked with` | `—` | leave | – | arithmetic receiver |
| `Year2021/Day02/Day02.sw:67` (`solvePart1`) | `(horizontal commands).toInt * commands.sumBy .down` | `—` | leave | – | operand of `*`: `\|>` is looser than `*`, so brackets stay |
| `Year2021/Day02/Day02.sw:73` (`solvePart2`) | `(horizontal commands).toInt * aimedDepth 0 commands` | `—` | leave | – | same |
| `Year2021/Day03/Day03.sw:40` (`parseReport`) | `let width := (numbers.headOr []).length` | `let width := numbers.headOr [] \|> .length` | optional | none | elaborates |
| `Year2021/Day03/Day03.sw:75` (`solvePart2`) | `let width := (numbers.headOr []).length` | `let width := numbers.headOr [] \|> .length` | optional | Proofs/Proofs.sw | elaborates |
| `Year2021/Day04/Day04.sw:78` (`solvePart1`) | `(winningScores game).head` | `winningScores game \|> .head` | optional | Proofs/Proofs.sw | elaborates |
| `Year2021/Day04/Day04.sw:81` (`solvePart2`) | `(winningScores game).last` | `winningScores game \|> .last` | optional | Proofs/Proofs.sw | elaborates |
| `Year2021/Day08/Day08.sw:126` (`showsRead`) | `== (digitPattern digit).has (wiring.at wire)` | `—` | leave | – | right of `==`: the pipe form is correct but reads worse |
| `Year2021/Day08/Day08.sw:133` (`Entry.wired`) | `(segments.map wiring.at).sort == segments` | `segments.map wiring.at \|> .sort == segments` | rewrite | Proofs/Parse.sw, Proofs/Proofs.sw | `\|>` binds tighter than `==`, `∧`; elaborates |
| `Year2021/Day08/Day08.sw:134` (`Entry.wired`) | `(entry.patterns.map (decodeDigit entry.patterns)).sort == List.range 10` | `entry.patterns.map (decodeDigit entry.patterns) \|> .sort == List.range 10` | rewrite | Proofs/Parse.sw, Proofs/Proofs.sw | elaborates |
| `Year2021/Day08/Day08.sw:135` (`Entry.wired`) | `(entry.patterns ++ entry.outputs).all (showsRead wiring entry.patterns)` | `entry.patterns ++ entry.outputs \|> .all (showsRead wiring entry.patterns)` | rewrite | Proofs/Parse.sw, Proofs/Proofs.sw | done with 133-134 so the three conjuncts match; elaborates |
| `Year2021/Day09/Day09.sw:70` (`HeightMap.basinSize`) | `then (graph.breadthFirst [low]).size else 0` | `then graph.breadthFirst [low] \|> .size else 0` | optional | Proofs/Part2.sw | `\|>` is fine before `else`; elaborates |
| `Year2021/Day11/Day11.sw:59` (`flashers`) | `(cells levels).length` | `—` | leave | – | last argument of a call; the pipe would need the same brackets |
| `Year2021/Day11/Day11.sw:68` (`zeros`) | `(cells levels).count (((_, level)) => level == 0)` | `cells levels \|> .count (((_, level)) => level == 0)` | optional | Proofs/Parts.sw, Proofs/Step.sw | elaborates |
| `Year2021/Day11/Day11.sw:88` (`firstSync`) | `if (cells next).all (((_, level)) => level == 0) then` | `if cells next \|> .all (((_, level)) => level == 0) then` | optional | Proofs/Parts.sw | elaborates |
| `Year2021/Day12/Day12.sw:125` (`solvePart1`) | `(paths passages False).length` | `paths passages (spare := False) \|> .length` | rewrite | Proofs/Parts.sw | with the named flag (pattern I); elaborates |
| `Year2021/Day12/Day12.sw:127` (`solvePart2`) | `(paths passages True).length` | `paths passages (spare := True) \|> .length` | rewrite | Proofs/Parts.sw | elaborates |
| `Year2021/Day13/Day13.sw:108` (`solvePart1`) | `(foldAll (paper.folds.take 1) paper.dots).length` | `foldAll (paper.folds.take 1) paper.dots \|> .length` | optional | Proofs/Parse.sw, Proofs/Parts.sw | elaborates |
| `Year2021/Day15/Day15.sw:75` (`Cave.levels`) | `(cave.grid.map (_ digit => digit.toNat)).lookupOr 0` | `cave.grid.map (_ digit => digit.toNat) \|> .lookupOr 0` | optional | Proofs/Answers.sw, Proofs/Levels.sw, Proofs/Parse.sw, Proofs/Search.sw | elaborates |
| `Year2021/Day16/Day16.sw:88` (`hexDigit`) | `(char => (hexValue char).isSome)` | `—` | leave | – | inside a lambda body, one step: no gain |
| `Year2021/Day17/Day17.sw:114` (`solvePart1`) | `(hitting target).maximumOf peak` | `hitting target \|> .maximumOf peak` | optional | Proofs/Answers.sw, Proofs/Parse.sw | elaborates |
| `Year2021/Day17/Day17.sw:116` (`solvePart2`) | `(hitting target).length` | `hitting target \|> .length` | optional | Proofs/Answers.sw, Proofs/Parse.sw | elaborates |
| `Year2021/Day18/Day18.sw:111` (`solvePart1`) | `(addAll first rest).map magnitude` | `addAll first rest \|> .map magnitude` | optional | Proofs/Answers.sw, Proofs/Parse.sw | elaborates |
| `Year2024/Day08/Day08.sw:61` (`antinodesOf`) | `[difference, (divideBy difference 3).negate]` | `—` | leave | – | list element; brackets keep the element obvious |
| `Year2024/Day08/Day08.sw:68` (`divideBy`) | `let divisor := (Succ below).toInt` | `—` | leave | – | constructor receiver |
| `Year2024/Day08/Day08.sw:84` (`City.harmonics`) | `[step.times count.toInt, (step.times count.toInt).negate]` | `—` | leave | – | list element |
| `Year2024/Day12/Day12.sw:65` (`Garden.unvisitedInsert`) | `!(visited.insert position).contains other` | `—` | leave | – | under a prefix `!` |
| `Year2024/Day13/Day13.sw:111` (`Machine.collinearTokens`) | `(fewerA ++ fewerB).minimum` | `—` | leave | – | operator receiver |
| `Year2024/Day16/Day16.sw:46` (`parseMaze`) | `cells (parseGrid input tile).rows` | `—` | leave | – | field of a call as an argument |
| `Year2024/Day16/Day16.sw:201` (`Maze.fromStart`) | `(maze.graph False).distances [(maze.startReindeer, 0)]` | `maze.graph (backwards := False) \|> .distances [(maze.startReindeer, 0)]` | rewrite | Proofs/Part1.sw, Proofs/Part2.sw | with the named flag; elaborates |
| `Year2024/Day16/Day16.sw:204` (`Maze.toEnd`) | `(maze.graph True).distances (maze.endReindeer \|> .map (reindeer => (reindeer, 0)))` | `maze.graph (backwards := True) \|> .distances (maze.endReindeer \|> .map (reindeer => (reindeer, 0)))` | rewrite | Proofs/Part2.sw | with the named flag; elaborates |
| `Year2024/Day16/Day16.sw:234` (`part2From`) | `(maze.bestTilesFrom fromStart).size` | `maze.bestTilesFrom fromStart \|> .size` | optional | none | elaborates |
| `Year2024/Day17/Day17.sw:159` (`outcome`) | `({ registers, pointer = 0 }: Machine).run program [] (fuelFor registers program)` | `—` | leave | – | record literal receiver |
| `Year2024/Day18/Day18.sw:86` (`reachable`) | `(MemorySpace.after size bytes fallen).fewestSteps.isSome` | `MemorySpace.after size bytes fallen \|> .fewestSteps \|> .isSome` | optional | Proofs/Part1.sw, Proofs/Part2.sw | elaborates |
| `Year2024/Day18/Day18.sw:88` (`solvePart1`) | `(MemorySpace.after size bytes fallen).fewestSteps` | `MemorySpace.after size bytes fallen \|> .fewestSteps` | optional | Proofs/Part1.sw | elaborates |
| `Year2024/Day22/Day22.sw:32` (`nextSecret`) | `(secret * 64 % modulus).xor (secret % modulus)` | `—` | leave | – | arithmetic receiver (also lines 33, 34) |
| `Year2024/Day24/Day24.sw:104` (`Gate.ready`) | `(gate.fire values).isSome` | `gate.fire values \|> .isSome` | optional | Proofs/Complete.sw, Proofs/Part1.sw | elaborates |
| `Year2024/Day24/Day24.sw:108` (`fireAll`) | `((gate.fire values).getOrElse False)` | `—` | leave | – | argument of `insert`: no bracket saved |
| `Year2024/Day24/Day24.sw:277` (`repair`) | `(swapsToTry fixes suspects).findMap (fix => …)` | `swapsToTry fixes suspects \|> .findMap (fix => …)` | optional | Proofs/Part2.sw, Proofs/Proofs.sw | elaborates (hand-checked) |
| `Year2025/Day02/Day02.sw:71` (`sumOfIdsWrittenTwice`) | `List.between 1 (Nat.digits range.to).length` | `—` | leave | – | field of a call as an argument |
| `Year2025/Day07/Day07.sw:74` (`parseManifold`) | `rows = (lines.drop (rowIndex + 1)).map (splitterRow width)` | `rows = lines.drop (rowIndex + 1) \|> .map (splitterRow width)` | optional | none | elaborates |
| `Year2025/Day07/Day07.sw:78` (`findStart`) | `(line.toList.findIndex (== 'S')).map (columnIndex => (rowIndex, columnIndex))` | `line.toList.findIndex (== 'S') \|> .map (columnIndex => (rowIndex, columnIndex))` | optional | none | elaborates |
| `Year2025/Day08/Day08.sw:135` (`solvePart2`) | `(boxes.points.getOr first Point.origin).x * (…).x` | `—` | leave | – | operands of `*` |

### B. `f (xs.chain)`: a wrapper around a chain, which `|> f` reorders

18 sites: 1 rewrite, 8 optional, 9 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2020/Day04/Day04.sw:51` (`field`) | `Parse.pick (keys.map (key => (key.code, key)))` | `keys.map (key => (key.code, key)) \|> Parse.pick` | optional | Proofs/Parse.sw, Proofs/Proofs.sw, Proofs/Rules.sw | elaborates |
| `Year2021/Day05/Day05.sw:81` (`overlaps`) | `Map.counts (lines.flatMap Line.points) \|> .count (_ times => 2 ≤ times)` | `lines.flatMap Line.points \|> Map.counts \|> .count (_ times => 2 ≤ times)` | rewrite | Proofs/Proofs.sw | the whole body becomes one pipeline; elaborates |
| `Year2021/Day05/Day05.sw:84` (`solvePart1`) | `overlaps (lines.filter Line.isStraight)` | `lines.filter Line.isStraight \|> overlaps` | optional | Proofs/Proofs.sw | elaborates |
| `Year2021/Day10/Day10.sw:56` (`bracket`) | `Parse.pick (allTokens.map (token => (Text.fromList [token.char], token)))` | `allTokens.map (token => (Text.fromList [token.char], token)) \|> Parse.pick` | optional | Proofs/Parse.sw, Proofs/Part1.sw, Proofs/Part2.sw, Proofs/Scan.sw | elaborates |
| `Year2021/Day10/Day10.sw:107` (`solvePart2`) | `middle (lines.filterMap autocompleteScore)` | `lines.filterMap autocompleteScore \|> middle` | optional | Proofs/Part2.sw | elaborates |
| `Year2021/Day14/Day14.sw:74` (`ruleTable`) | `Map.fromList (rules.map (rule => (rule.pair, rule.insert)))` | `rules.map (rule => (rule.pair, rule.insert)) \|> Map.fromList` | optional | Proofs/Counts.sw, Proofs/Spread.sw, Proofs/Table.sw | elaborates |
| `Year2021/Day14/Day14.sw:90` (`countPairs`) | `addAll Map.empty (polymer.zipWithNext.map (pair => (pair, 1)))` | `—` | leave | – | the list is addAll's last argument and `\|>` supplies the first: REJECTED, `E-TYPE-MISMATCH` (verified) |
| `Year2021/Day14/Day14.sw:94` (`stepCounts`) | `addAll Map.empty (counts.toList.flatMap (entry => …))` | `—` | leave | – | same: last-argument position |
| `Year2021/Day14/Day14.sw:120` (`spreadAfter`) | `spread manual.template (Nat.iterate steps (stepCounts (ruleTable manual.rules)) (countPairs manual.template))` | `—` | leave | – | f (g (h x)) where the seed is `Nat.iterate`'s last argument, so it cannot be piped |
| `Year2024/Day21/Day21.sw:176` (`routeKeys`) | `List.append (route.map Arrow) [Activate]` | `route.map Arrow ++ [Activate]` | optional | Proofs/Direct.sw, Proofs/Lower.sw, Proofs/Presses.sw | `++` instead of a pipe; elaborates |
| `Year2025/Day09/Day09.sw:102` (`Floor.of`) | `keyLines (tiles.map .x)` | `tiles.map .x \|> keyLines` | optional | Proofs/Compress.sw, Proofs/Floor.sw, Proofs/Part1.sw, Proofs/Part2.sw | elaborates |
| `Year2025/Day09/Day09.sw:103` (`Floor.of`) | `keyLines (tiles.map .y)` | `tiles.map .y \|> keyLines` | optional | Proofs/Compress.sw, Proofs/Floor.sw, Proofs/Part1.sw, Proofs/Part2.sw | elaborates |
| `Year2025/Day09/Day09.sw:64` (`loopLines`) | `tiles.zip (tiles.drop 1 \|> .append (tiles.take 1))` | `—` | leave | – | the argument is the second of two; reads fine |
| `Year2025/Day09/Day09.sw:110` (`Floor.outsideCells`) | `Floor.outsideRow (lines.filter (touchesRow y)) columns y` | `—` | leave | – | middle argument |
| `Year2021/Day03/Day03.sw:70` (`rating`) | `rating choose later (numbers.filterMap (afterBit bit)) \|> .map (Cons bit)` | `—` | leave | – | middle argument |
| `Year2021/Day12/Day12.sw:115` (`reach`) | `Bool.toNat (not (isBig cave))` | `—` | leave | – | term in arithmetic |
| `Year2021/Day18/Day18.sw:71` (`split`) | `Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2)))` | `—` | leave | – | constructor nesting |
| `Year2024/Day12/Day12.sw:100` (`Garden.regionsFrom`) | `Cons region (garden.regionsFrom rest (region.foldLeft seen Set.insert))` | `—` | leave | – | constructor nesting |

### D. A lambda that is a section (`x => x.f …`, `x => x op …`)

29 sites: 22 rewrite, 0 optional, 7 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Common/Grid.sw:150` (`Grid.isRectangle`) | `grid.rows.all (row => row.length == grid.width)` | `grid.rows.all (.length == grid.width)` | rewrite | 2 files | elaborates |
| `Year2020/Day04/Day04.sw:62` (`Passport.has`) | `passport.fields.any (field => field.key == key)` | `passport.fields.any (.key == key)` | rewrite | Proofs/Proofs.sw | elaborates |
| `Year2021/Day04/Day04.sw:49` (`isFiveByFive`) | `board.all (row => row.length == 5)` | `board.all (.length == 5)` | rewrite | none | elaborates |
| `Year2021/Day08/Day08.sw:75` (`litIn`) | `patterns.count (pattern => pattern.has wire)` | `patterns.count (.has wire)` | rewrite | Proofs/Proofs.sw | elaborates |
| `Year2021/Day09/Day09.sw:57` (`HeightMap.isOpen`) | `.any (height => height != 9)` | `.any (!= 9)` | rewrite | Proofs/Part2.sw | operator section; elaborates |
| `Year2021/Day11/Day11.sw:34` (`numbers`) | `grid.rows.map (row => row.map Fin.toNat)` | `grid.rows.map (.map Fin.toNat)` | leave | – | two nested `map`s read clearer with the named `row`; elaborates (hand-checked) |
| `Year2024/Day06/Day06.sw:52` (`parseLab`) | `cells.filter (cell => cell.snd == wanted) \|> .map (cell => cell.fst)` | `cells.filter (.snd == wanted) \|> .map .fst` | rewrite | none | elaborates |
| `Year2024/Day07/Day07.sw:70` (`calibrationResult`) | `\|> .sumBy (equation => equation.testValue)` | `\|> .sumBy .testValue` | rewrite | Proofs/Proofs.sw | elaborates |
| `Year2024/Day09/Day09.sw:101` (`FreeSpace.remove`) | `(starts => starts.remove span.start)` | `(.remove span.start)` | rewrite | none | elaborates |
| `Year2024/Day09/Day09.sw:109` (`FreeSpace.leftmostFit`) | `\|> .minBy (span => span.start)` | `\|> .minBy .start` | rewrite | Proofs/Part2.sw | elaborates |
| `Year2024/Day09/Day09.sw:110` (`FreeSpace.leftmostFit`) | `\|> .filter (span => span.start < before)` | `\|> .filter (.start < before)` | rewrite | Proofs/Part2.sw | elaborates |
| `Year2024/Day09/Day09.sw:129` (`File.checksum`) | `\|> .sumBy (position => position * file.id)` | `\|> .sumBy (* file.id)` | rewrite | Proofs/Part1.sw, Proofs/Part2.sw | operator section; elaborates |
| `Year2024/Day12/Day12.sw:24` (`plantLetter`) | `Parse.satisfy "a letter" (char => char.isAsciiLetter)` | `Parse.satisfy "a letter" .isAsciiLetter` | rewrite | none | a bare section works as the last argument; elaborates |
| `Year2024/Day12/Day12.sw:115` (`Position.diagonal`) | `\|> .flatMap (next => next.step horizontal)` | `\|> .flatMap (.step horizontal)` | rewrite | Proofs/Corners.sw, Proofs/Sides.sw | elaborates |
| `Year2024/Day15/Day15.sw:142` (`Warehouse.moveWide`) | `group.map (box => box.step direction)` | `group.map (.step direction)` | rewrite | Proofs/Part2.sw | elaborates |
| `Year2024/Day16/Day16.sw:38` (`onlyTile`) | `tiles.filter (entry => entry.snd == wanted) \|> .map (entry => entry.fst)` | `tiles.filter (.snd == wanted) \|> .map .fst` | rewrite | none | elaborates |
| `Year2024/Day16/Day16.sw:48` (`parseMaze`) | `tiles.filter (entry => entry.snd != Wall) \|> .map (entry => entry.fst) \|> Set.fromList` | `tiles.filter (.snd != Wall) \|> .map .fst \|> Set.fromList` | rewrite | none | elaborates |
| `Year2024/Day16/Day16.sw:214` (`tilesScoring`) | `\|> .map (entry => entry.fst.position)` | `\|> .map .fst.position` | rewrite | Proofs/Part2.sw | a section may chain fields; elaborates |
| `Year2024/Day20/Day20.sw:45` (`onlyTile`) | `tiles.filter (entry => entry.snd == wanted) \|> .map (entry => entry.fst)` | `tiles.filter (.snd == wanted) \|> .map .fst` | rewrite | none | elaborates |
| `Year2024/Day20/Day20.sw:57` (`parseRacetrack`) | `tiles.filter (entry => entry.snd != Wall) \|> .map (entry => entry.fst) \|> Set.fromList` | `tiles.filter (.snd != Wall) \|> .map .fst \|> Set.fromList` | rewrite | none | elaborates |
| `Year2024/Day23/Day23.sw:61` (`Links.setsOfThree`) | `\|> .filter (set => set.size == 3)` | `\|> .filter (.size == 3)` | rewrite | Proofs/Part1.sw | elaborates |
| `Year2024/Day23/Day23.sw:64` (`mightBeChiefs`) | `set.any (computer => computer.startsWith "t")` | `set.any (.startsWith "t")` | rewrite | Proofs/Part1.sw | elaborates |
| `Year2024/Day24/Day24.sw:117` (`settle`) | `waiting.filter (gate => gate.ready values)` | `waiting.filter (.ready values)` | rewrite | Proofs/Complete.sw, Proofs/Part1.sw | elaborates |
| `Year2021/Day08/Day08.sw:94` (`solvePart1`) | `entry.outputs.count (output => [2, 3, 4, 7].contains output.size)` | `—` | leave | – | the parameter is not at the start of the body |
| `Year2021/Day04/Day04.sw:62` (`winningTurn`) | `line.foldLeft 0 (latest number => …)` | `—` | leave | – | a section would need the lambda inside it |
| `Year2024/Day13/Day13.sw:124` (`solvePart1`) | `machines.sumBy (machine => machine.fewestTokensWithin 100 \|> .getOrElse 0)` | `—` | leave | – | lambda body is a pipeline; the lambda is clearer |
| `Year2024/Day23/Day23.sw:49` (`Network.links`) | `.map (pairs => pairs.map Pair.snd \|> Set.fromList)` | `—` | leave | – | lambda body is a pipeline |
| `Year2024/Day24/Day24.sw:260` (`zWithin`) | `[gate.left, gate.right, gate.output].all (wire => wire.zBit.all (bit => bit ≤ bits))` | `—` | leave | – | nested quantifiers; the names say what they are |
| `Year2025/Day06/Day06.sw:124` (`blockError`) | `block.count (indexed => indexed.snd.last.flatMap Operator.parse \|> .isSome)` | `—` | leave | – | pipeline in the lambda body |

### E. A lambda that is a partial application (`x => f a x`)

7 sites: 7 rewrite, 0 optional, 0 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2021/Day16/Day16.sw:196` (`zeroBits`) | `bits.all (bit => not bit)` | `bits.all not` | rewrite | Proofs/Decode.sw | elaborates |
| `Year2024/Day13/Day13.sw:75` (`Machine.searchTokens`) | `\|> .filter (bPresses => machine.wins aPresses bPresses) \|> .map (bPresses => tokens aPresses bPresses)` | `\|> .filter (machine.wins aPresses) \|> .map (tokens aPresses)` | rewrite | Proofs/Part1.sw | elaborates |
| `Year2024/Day15/Day15.sw:118` (`Warehouse.boxesAt`) | `\|> .filter (box => warehouse.boxes.contains box)` | `\|> .filter warehouse.boxes.contains` | rewrite | Proofs/Part2.sw | elaborates |
| `Year2024/Day17/Day17.sw:140` (`Machine.step`) | `\|> .flatMap (operand => Instruction.decode opcode operand)` | `\|> .flatMap (Instruction.decode opcode)` | rewrite | Proofs/Proofs.sw, Proofs/Run.sw, Proofs/Step.sw, Proofs/Unique.sw | elaborates |
| `Year2024/Day21/Day21.sw:199` (`Costs.tabulate`) | `directionKeys.map (to => costs from to)` | `directionKeys.map (costs from)` | rewrite | Proofs/Presses.sw | elaborates |
| `Year2024/Day22/Day22.sw:41` (`solvePart1`) | `buyers.sumBy (buyer => Nat.iterate 2000 nextSecret buyer)` | `buyers.sumBy (Nat.iterate 2000 nextSecret)` | rewrite | Proofs/Step.sw | elaborates |
| `Year2024/Day24/Day24.sw:201` (`bitOutputs`) | `passed.flatMap (kept => outputOf gates Or made kept)` | `passed.flatMap (outputOf gates Or made)` | rewrite | none | elaborates |

### H. Positional runs of number literals

15 sites: 13 rewrite, 0 optional, 2 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2020/Day04/Day04.sw:76` (`heightValid`) | `between 150 193 number.toNat` | `between (low := 150) (high := 193) number.toNat` | rewrite | Proofs/Rules.sw | elaborates |
| `Year2020/Day04/Day04.sw:79` (`heightValid`) | `between 59 76 number.toNat` | `between (low := 59) (high := 76) number.toNat` | rewrite | Proofs/Rules.sw | elaborates |
| `Year2020/Day04/Day04.sw:93` (`Key.valid`) | `yearBetween 1920 2002 value` | `yearBetween (low := 1920) (high := 2002) value` | rewrite | Proofs/Rules.sw | elaborates |
| `Year2020/Day04/Day04.sw:94` (`Key.valid`) | `yearBetween 2010 2020 value` | `yearBetween (low := 2010) (high := 2020) value` | rewrite | Proofs/Rules.sw | elaborates |
| `Year2020/Day04/Day04.sw:95` (`Key.valid`) | `yearBetween 2020 2030 value` | `yearBetween (low := 2020) (high := 2030) value` | rewrite | Proofs/Rules.sw | elaborates |
| `Year2020/Day05/Day05.sw:39` (`pass`) | `Parse.repeat 7 7 frontBack` | `Parse.repeat (atLeast := 7) (atMost := 7) frontBack` | rewrite | Proofs/Parse.sw, Proofs/Proofs.sw, Proofs/Seat.sw | elaborates |
| `Year2020/Day05/Day05.sw:40` (`pass`) | `Parse.repeat 3 3 leftRight` | `Parse.repeat (atLeast := 3) (atMost := 3) leftRight` | rewrite | Proofs/Parse.sw, Proofs/Proofs.sw, Proofs/Seat.sw | elaborates |
| `Year2021/Day08/Day08.sw:139` (`Entry.parse`) | `Parse.repeat 10 10 (() =>` | `Parse.repeat (atLeast := 10) (atMost := 10) (() =>` | rewrite | none | elaborates |
| `Year2021/Day08/Day08.sw:144` (`Entry.parse`) | `Parse.repeat 4 4 (() =>` | `Parse.repeat (atLeast := 4) (atMost := 4) (() =>` | rewrite | none | elaborates |
| `Year2024/Day03/Day03.sw:27` (`shortNumber`) | `natDigits 1 3` | `natDigits (atLeast := 1) (atMost := 3)` | rewrite | none | elaborates |
| `Year2024/Day17/Day17.sw:66` (`threeBit`) | `natDigits 1 1` | `natDigits (atLeast := 1) (atMost := 1)` | rewrite | none | elaborates |
| `Year2024/Day09/Day09.sw:125` (`compactFiles`) | `layoutFrom 0 0 diskMap` | `layoutFrom (id := 0) (position := 0) diskMap` | rewrite | Proofs/Part2.sw | elaborates |
| `Year2024/Day14/Day14.sw:25` (`Space.fromArgs`) | `Space.of 101 103` | `Space.of (width := 101) (height := 103)` | rewrite | none | has `auto` parameters; still fine; elaborates |
| `Year2025/Day02/Day02.sw:61` (`allTemplatesForRange`) | `each (List.between 1 maxDigits)` | `—` | leave | – | one literal and one name, and `between 1 n` reads as a range |
| `Year2025/Day02/Day02.sw:94` (`copiesWeight`) | `List.between 2 (copies - 1)` | `List.between (lo := 2) (hi := copies - 1)` | leave | – | works (verified) but reads as a range; Matt's call; elaborates |

### I. A lone bool or number flag at a call site

5 sites: 1 rewrite, 2 optional, 2 leave.

| Site | Before | After | Verdict | Proofs mention it? | Notes |
|---|---|---|---|---|---|
| `Year2021/Day12/Day12.sw:89` (`step`) | `else if spare then Continue unvisited False` | `else if spare then Continue unvisited (spare := False)` | optional | Proofs/Routes.sw, Proofs/Rules.sw, Proofs/Steps.sw | constructor fields can be named; elaborates |
| `Year2025/Day07/Day07.sw:114` (`fall`) | `(hit.shiftRight False) (hit.shiftLeft False)` | `(hit.shiftRight (fill := False)) (hit.shiftLeft (fill := False))` | optional | Proofs/Part1.sw | elaborates |
| `Year2025/Day08/Day08.sw:26` (`main`) | `solvePart1 1000 boxes` | `solvePart1 (connections := 1000) boxes` | rewrite | n/a | a bare 1000 in `main` says nothing; elaborates |
| `Year2024/Day14/Day14.sw:99` (`solvePart1`) | `space.positionsAfter 100 robots` | `—` | leave | – | `positionsAfter` is already named for the quantity |
| `Year2024/Day22/Day22.sw:41` (`solvePart1`) | `Nat.iterate 2000 nextSecret` | `—` | leave | – | `Nat.iterate` is declared with arrow types, so its parameters have no names to give (verified: E-UNKNOWN-NAME) |
## Stage 2: the mechanical rewrite

Scope: the 73 `rewrite` sites, plus the 33 `optional` ones if Matt wants
them (decision below). All sites are listed with exact before and after, so
this is application plus checking, not design, except batch 1.

**Decisions for Matt** (for the orchestrator to bring):

1. Do the `optional` class (33 sites: a single `(f x).g` to `f x |> .g`, a
   single `f (xs.map g)` to `xs.map g |> f`)? Recommendation: no, in line
   with "neither is absolute": the gain is one pair of brackets and the
   steps are the same. Cases that extend an existing pipeline or sit in
   `main` are already marked `rewrite`. If Matt wants the uniform style it
   is cheap (they all elaborate), and batches 2 to 4 take them as given.
2. `main` and a `None` that is a legitimate result (2021 day 17, 18; 2025
   day 8 "the boxes are already in one circuit"): `orFail` turns it into a
   failed run (non-zero exit) instead of a printed line. Recommendation:
   yes for 2021 days 11, 17, 18 and 2024 days 14, 17, 18, 24 (a missing
   answer is a problem with the input); ask for 2025 day 8 (`optional`).
3. 2024 day 14's `main with no picture` test expects `Part 2: none` and an
   `Ok`; the rewrite changes it to the failure with the new message
   (`MkPair ["Part 1: 3564"] (Err "…")`).

**Batches** (each: apply the table, `stitchwort fmt` on the touched `.sw`,
`stitchwort check` on the day's namespace, `.Proofs` and `.Tests`, then
`task test:one` for any test touched; no wider run):

| Batch | Scope | Sites | Model | Estimate |
|---|---|---:|---|---|
| 1 | every `main` change (patterns F and G, all years), the 2024 day 14 test update, messages worded from the puzzle texts | 21 | Sonnet (wording, behaviour change, one test) | 35 min |
| 2 | 2020, 2021 and `Common` programs, everything else in the tables (A, B, C, D, E, H, I), one commit per year | 23 (+18 optional) | DeepSeek, from this table; the diff reviewed line by line | 30 min |
| 3 | 2024 programs, everything else in the tables, one commit per day group | 32 (+6 optional) | DeepSeek | 40 min |
| 4 | 2025 programs | 1 (+5 optional) | DeepSeek | 10 min |

Batches 2 to 4 touch different years and can run side by side (a
`Common` edit is checked with `Aoc.Common.Proofs`, which every year's proofs
import). Batch 1 touches `main` only, so it conflicts with them only on the
same files' neighbouring lines: run it first, or merge it last. If DeepSeek
fails a check on a site it leaves the site as it was and says so; nothing
is guessed. Total about 115 lane-minutes, about 45 minutes of wall time.

## Findings worth a ticket

- **std has no `id`, `Option.flatten`, `List.catOptions`, `uncurry`.** 8
  identity lambdas and 43 tuple-pattern lambdas in the programs would be
  shorter with them. (Adding `Pair.uncurry`-like helpers is a design choice:
  the tuple pattern names its parts, which is often clearer.)
- **Arrow-typed std definitions give no parameter names**, so D2367's named
  arguments can't be used: `Nat.iterate`, `List.rangeFrom`, and any other
  `def f: A → B → C` form. Declaring these with named parameters
  (`def Nat.iterate (count: Nat) (step: a → a) (seed: a): a`) keeps `iterate
  n f x` and lets `iterate (count := 2000) …` work.
- **`|>` can't feed the last argument.** Several sites (`addAll counts xs`,
  `Nat.iterate n f seed`) would chain if their list or seed came first. A
  convention for new functions ("main value first", already in the guide),
  not a language change; `Nat.iterate` is the one std function that breaks
  it.
- **`Position` has no `toText`** in `Aoc.Common`; 2024 day 18's part 2 prints
  `"${byte.column},${byte.row}"` by hand. A `let` is needed after the
  rewrite. Not worth more than that.
- **2024 day 18's `sizesFrom` returns an anonymous `(Nat, Nat)`** (`(71,
  1024)`) that is then destructured as `(size, fallen)`: a positional run of
  numbers of the kind D2367 targets, outside the call-site cases above.
  A small record would name them.
