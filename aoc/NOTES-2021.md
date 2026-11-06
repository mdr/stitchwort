# Friction report: Advent of Code 2021 in Stitchwort

What was awkward, missing or surprising while writing 2021's days (in
`aoc/src/Aoc/Year2021/`), day by day, in the format of
[NOTES-2024.md](NOTES-2024.md). The inputs are Matt's, from his Scala
repository (github.com/mdr/aoc, `src/main/resources/aoc2021/`), committed in
`aoc/inputs/2021/`; the expected answers are his Scala solution's.

## Parser guarantees (D2108)

From day 5 on, a day whose correctness theorems assume something the
puzzle promises (every line at one of three angles, every timer at most 8)
also proves that its parser guarantees it, and states the answers'
theorems about the parsed input with no hypothesis left. Days 5, 6, 8,
12, 13, 14, 15, 16, 17 and 18 do (day 15's is a rectangle with a digit; day 17's is a target right of the start and below it; day 18's is that every number is already reduced; day 12's promise, that no passage joins two big caves, is
one the puzzle leaves unsaid; day 13's parser folds the paper to check
each fold's promise; day 14's is one rule per pair; day 16's is that a
minimum or maximum has a sub-packet and a comparison exactly two); day 9's answers need no promise at all, and
its parser's guarantees (digits, a rectangle) are proved anyway. The
pattern:

- **"A successful parse"** is `Fail.toResult (() => parse input) = Ok xs`:
  the parser is `{Fail}` code, and `Fail.toResult` is std's handler that
  turns it into a `Result`. The theorem is about every `input` and `xs`
  for which that holds:

  ```stitchwort
  theorem parseTimersBounded (input: Text) (fish: List Nat) (parsed: Fail.toResult (() => parseTimers input) = Ok fish):
      fish.all (t => t ≤ 8) = True
  theorem part2FromInput (input: Text) (fish: List Nat) (parsed: Fail.toResult (() => parseTimers input) = Ok fish):
      solvePart2 fish = fishCount 256 fish
  ```

- **Write the parser as a read and a check**, `parse input := check
  (Parse.eachLine input item)`, with the check a `{Fail}` function of the
  values read and its test a pure function (`firstBent lines`, `firstAbove8
  timers`: the first offender, as an `Option`). Two reasons. A `match` on
  an effect-polymorphic call written inside `{Fail}` code (`timers.withIndex.find
  …` straight in the `match`) is translated with `Effect.bind`, and a
  `match e:` on the pure call then doesn't refine the hypothesis; the pure
  helper's call does. And the check can be proved for *any* read:

  ```stitchwort
  theorem checkedBounded (read: () → {Fail} (List Nat)) (fish: List Nat) (parsed: Fail.toResult (() => checkTimers (read ())) = Ok fish):
      fish.all (t => t ≤ 8) = True :=
    let split := rewrite Fail.toResultThen read checkTimers at parsed
    Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkTimers x)) fish split
      (u _ checked => checkTimersOk u fish checked)
  ```

  `Fail.toResultThen` splits the read from the check, `Result.flatMapEqOk`
  takes the read's `Ok` apart, and the parser's own theorem is
  `checkedBounded _ fish parsed` (the `_` is the read, found by
  unification). Nothing about `Std.Parse` is needed.
- **When the promise is in what is read** (every character a bracket,
  every digit hexadecimal), std's lemmas on what parsers read give it
  (SW-998, `crates/elab/src/std/Parse/Reads.sw`): `Parse.Reads parser
  spec` says what a successful run read and gave, each piece has one
  (`readsNat`, `readsPick`, `readsMany`, `readsLabel`, …), and
  `Parse.eachLineReads`, `lineReads` and `allReads` turn it into a fact
  about the input. Days 10 and 16 prove their guarantees this way.
- **The check's lemma** matches on the pure test: the offender's case is
  `Result.errNotOk`, and in the other the `Ok` gives the checked values
  back (`Result.okInjective`) and the test's `None` gives the property
  (`findIndexedNone`: a `find` over `withIndexFrom i xs` that found
  nothing means no element is bad, by induction on the list).
- A promise that is cheap to check at run time can move into the parser
  too: day 8's parser works out each display's wiring and fails unless it
  decodes the display, so its end-to-end theorems have no hypothesis.
  What a parser can't check stays a hypothesis, and the day's notes say
  so.

## Shared grid code (SW-984)

Grid code is AoC's, not std's (Matt, 1 November 2026), so it lives in
`Aoc.Common` beside `Range`: `Common/Grid.sw` and `GridGraph.sw`, proofs
in `Common/Proofs/Grid*.sw`, tests in `Common/Tests/Grid.sw`. Days 9, 11
and 15 here, and 2024's days 6, 12 and 20, use it; their own copies are
gone (days 9, 11 and 15 lost 142, 215 and 187 lines net).

- **Positions and steps.** `Position = { row, column }` (`Nat`s),
  `Direction` (`Up`, `Right`, `Down`, `Left`; `directions`, `turnRight`,
  `turnLeft`, `opposite`), `Position.step` (`None` above row 0 or left of
  column 0), `Grid.step` (also `None` off the grid). `neighbours` (the
  four, `directions.filterMap step`) and `around` (the eight). The spec
  words: `adjacent` (up, down, left or right), `touching` (diagonals too),
  `isPath allowed from steps to`. Proved: a neighbour is exactly an
  adjacent position (`neighbourAdjacent`, `adjacentNeighbour`) and exactly
  a step away (`memNeighbours`), around is exactly the touching positions
  (`aroundTouching`, `touchingAround`), each without repeats and at most 4
  and 8 (`neighboursDistinct`, `neighboursAtMost4`, `aroundDistinct`,
  `aroundAtMost8`), and the turning laws.
- **Grids.** On rows of any lengths: `cells` (each cell with its
  `Position`), `cellAt`, `mapCells`, with `memCells` (a cell is the cell at
  its position), `cellAtMapCells`, `cellsMapCells`, `mapCellsCong`,
  `cellPositionsDistinct`. `Grid a = { rows }` adds `height`, `width` (the
  first row's), `Rectangle` (every row as long as the first), `at`,
  `positions`, `contains`, `map`, and `lookup`/`lookupOr`, built once and
  O(log n) per lookup (`lookupAt`, `lookupOrAt`). On a rectangle a
  position has a cell exactly when it is within it (`atOfWithin`,
  `withinOfAt`).
- **The parser.** `parseGrid input cell`: a line per row, one or more
  cells each, every row as long as the first, at least one cell. In the
  D2108 style, `Fail.toResult (() => parseGrid input cell) = Ok grid`
  gives `grid.Rectangle ∧ 0 < grid.width ∧ 0 < grid.height`
  (`parseGridRectangle`); a day's parser that wraps it
  (`HeightMap.ofGrid (parseGrid input digit)`) gets it through
  `Fail.toResultThen`. Its errors say "cells", not the day's word.
- **The graph.** `stepGraph enter states complete` is std's `Graph` of
  steps to neighbours, entering a position costing `enter position`
  (`None`: it can't be entered); `cellsGraph rows enter`, `Grid.graph` and
  `boxGraph height width cost` fill in the `states`. Proved once: a walk
  is an `isPath` through the positions that can be entered and costs the
  sum of their costs (`walkPath`), and back (`pathWalk`, `pathWalkCost`),
  plus `isPathCong`, `isPathAppend`, `isPathEnd` and a `route` along the
  top row and down the last column (`routePath`). With
  `Graph.breadthFirstShortest` or `Graph.distancesShortest` that is all a
  day needs to say its search finds the cheapest paths.

**`Nat`, not `Int`.** A grid's cells are rows of a list, so a position is
two list indices, and a step off the top or left is `None` rather than a
negative index that every lookup would have to refuse.

**Offsets (SW-992).** How far to move is an `Offset = { rows, columns }`
of `Int`s (`Common/Offset.sw`; not `Vec`, std's sized lists). `zero`,
`plus`, `negate`, `times`, `Direction.offset`, `Offset.step`;
`Position.minus a b` is the offset from `b` to `a`, `position.offset o`
moves by one (`None` above row 0 or left of column 0), `Grid.offset` also
`None` off the grid, and `Position.wrap position offset height width`
moves on a board whose edges wrap round. Proved (`Proofs/Offset.sw`):
where an offset lands, in `Int`s (`offsetSome`, `offsetOf`,
`offsetNone`, `offsetNoneOf`), a step is an offset by its direction's
(`stepOffset`), `offsetZero`, `offsetMinus` (from `b` by `a.minus b` is
`a`), `minusOffset` (and back), `offsetPlus` (offsets compose while the
middle is on the board), `gridOffsetSome`/`gridOffsetOf`; `wrapWithin`,
`wrapZero`, `wrapPlus` (wrapping twice is wrapping by the sum),
`wrapIterate`; and the step laws of offsets. 2024's days 8 (antinodes
`near.offset (near.minus far)`), 14 (a velocity is an `Offset`, the
position after `t` seconds a `wrap`) and 15 (its cells are `Offset`s
from the corner, so a step is always defined) use them.

- **2024's day 8.** Antennas and antinodes are the shared `Position`; an
  antinode is `near.offset (near.minus far)` or the offset a third of the
  way back, and `harmonics` offsets `start` by whole multiples of the
  reduced step either way. `offset` gives `None` above or left of the map,
  and `locations` drops those past it, as before. The spec's cross product
  and squared distance are over offsets, its locations
  `Aoc.Common.positions`. The proofs work in `Int` coordinates through
  `offsetSome`/`offsetOf`; `place`, `positionEq` and `containsElim` are
  gone. Statements as before: part 2 still needs the antennas on the map
  (a test: rows 100 and 101 below a 1 by 1 map).
- **2024's day 14.** A tile is a `Position` (`x` its column, `y` its row,
  said once in the spec), a velocity an `Offset`, and `positionAfter` is
  `wrap` by the velocity times the seconds. `afterCorrect` is one spec
  second per `wrap` (`secondWrap`) and the shared `wrapIterate`.
- **2024's day 15** keeps `Int` cells: its proofs hold for every
  warehouse, walled in or not, because a step is always a cell. The
  walls keep the robot inside, but nothing in the types says so; with a
  `Nat` `Position` a step up from row 0 is `None`, and every move and
  theorem would need an off-the-map rule or a walled-in hypothesis. So a
  cell is an `Offset` from the top left corner (`def Cell: Type :=
  Offset`), with the shared `Direction` and `Offset.step`; its step laws
  are the shared `offsetStepInjective`, `offsetStepComm` and
  `offsetStepOpposite`.

**Lists of rows, with a table for lookups.** The grid is its rows, so
`cells`, `mapCells` and the proofs are list induction, and nothing has to
keep a map in step with a list. `lookup`/`lookupOr` build day 15's old
`Map.byPosition` table once, behind a function, with a lemma that it is
`at`. Day 15's run is unchanged: on a busy machine, three alternating
runs each took 22.5, 23.5 and 24.4 s before and 22.5, 23.1 and 25.6 s
after (user time).

**What changed in the days' statements.**
- Day 9: the spec's `adjacent` is `Aoc.Common.adjacent` (the same
  definition, moved), and its `isPath map` is `Aoc.Common.isPath
  (inSomeBasin map)`. `parseRectangular` says `row.length = firstWidth
  map.rows` (the day's `width` was the same function). The program's
  `neighbours` list is in clockwise order (up, right, down, left), so the
  neighbour tests changed. Every theorem still holds for every height map,
  ragged or not.
- Day 11: positions are `Position`s, not `(Nat, Nat)` pairs, in the spec
  as in the program: `Flashers levels (flashed: Position → Bool)`, cells
  are `cells levels` instead of `levels.gridCells`, and the spec's
  `adjacent` is `touching`. The theorems are otherwise as they were, for
  every grid. The counterexample search no longer met the hypotheses of
  `grows` and `stableOfCount` (it now meets `onGridAfter`'s); a test
  theorem (`stableAfterOneRound`) shows they can hold.
- Day 15: the spec's `isPath` is `Aoc.Common.isPath`, and `Rectangle`
  reads as before. `part1Correct`, `part2Correct` and the `FromInput`
  theorems are unchanged.
- The parsers' message for a short row says "cells" instead of "digits",
  and an empty input fails ("expected a grid, got no cells") on days 9
  and 11 too.

**2024.** Days 6, 12 and 20 import `Position`, `Direction` (and day 6
`turnRight`, days 12 and 20 `directions` and `step`) instead of defining
their own: their proofs needed only `directions` in its new order (day
12's `countDirections`, day 20's `directionsComplete`), and day 20's
diamond `Position.around length` is now `Position.diamond`. Not migrated:
day 8 (`Int` vector arithmetic), days 14 and 15 (`Int` positions; day
14's are `{ x, y }` on a torus).

**2024, days 10, 16 and 18 (SW-991).** Matt: aim for the best end state,
in the puzzle's words.
- Day 10: positions, `neighbours`, `cells` and `parseGrid` are shared;
  its `above`, `leftOf` and `rightAndBelow` and the proofs about them
  are gone. `memUphill` uses `neighbourAdjacent` and `adjacentNeighbour`,
  `uphillDistinct` uses `neighboursDistinct`, and `positions` (now the
  cells' positions) gets `positionsComplete` from `memCellsOfCellAt` and
  `positionsDistinct` from `cellPositionsDistinct`. The spec's
  `isOrthogonalStep` is the shared `adjacent` (the same definition).
  Statements unchanged otherwise; 154 lines out, 41 in.
- Day 16: the spec's compass stays: a day-local `Heading` (`East`,
  `South`, `West`, `North`) with `clockwise` and `counterclockwise`, and
  `Heading.toDirection` onto the shared `Direction` (north up: east is a
  column on, south a row on). Proofs/Headings.sw shows it is a bijection
  (`headingOf` is its inverse) and turns as the heading does
  (`clockwiseTurnsRight`, `counterclockwiseTurnsLeft`). Steps are the
  shared `Position.step` through it, so the spec's forward move is
  `position.step facing.toDirection`; its old `stepBack` is the shared
  `stepOpposite`. The graph stays the day's own: its states are a
  position and a heading, with turns, which `stepGraph` (positions only)
  doesn't model. 105 lines out, 95 in (27 of them Headings.sw).
- Day 18: a byte at `X,Y` is read as `{ row = Y, column = X }`, and the
  spec says once that X is the column and Y the row. The graph is
  `stepGraph` (entering a safe position costs 1). The spec's path is now
  the shared `isPath` (the positions entered, each adjacent to the one
  before and safe, from `{ row = 0, column = 0 }` to the bottom right
  corner) instead of a list of directions walked; `IsFewestSteps` counts
  its positions. The proofs use `walkPath`, `pathWalk` and
  `Graph.breadthFirstShortest` instead of their own walk lemmas. 277
  lines out, 144 in.
- Added to `Aoc.Common.Proofs`: `stepOpposite` (a step back the opposite
  way returns, for day 16's backward moves), `isPathWeaken` (a path by one
  test is a path by any test that allows its positions too: day 18's
  "more bytes fallen, fewer paths"), and `unitPathCost` with
  `unitEnterCost` (where entering costs 1, a path costs its number of
  steps: for `breadthFirst`).

**Friction.**
- `Up.turnRight` is `E-UNKNOWN-NAME`; dot calls don't reach a
  constructor's type. `Direction.turnRight Up` works.
- `if h: b then` needs a proposition; for a `Bool` it says to drop the
  `h:`, but the proof was wanted. `if h: b = True` would do.
- `rewrite DecEq.refl at.row, …` failed to parse: `at` is a keyword
  after a rewrite rule, so a variable named `at` can't be used there.
- A record has no eta: `at ∈ aroundBlock at.row at.column` needed a
  pattern `{ row, column }`, as pairs did on day 9.
- Std candidates proved locally (in `Aoc.Common.Proofs`):
  `distinctOfMap` (a list whose keys are distinct is), `lengthFilterMapLe`,
  `mapConcat` (std has no `filterMap` length lemma, nor `filterMap` as
  `map` of `filter`, to derive `lengthFilterMapLe` from), and a
  `Map.byPosition` `get` lemma (`lookupAt` avoids it by storing
  `Some`s). The parser uses std's `List.findWithIndexFromNone`,
  `List.findNoneAll` and `DecEq.neFalse`.

## Day 1: Sonar Sweep

A list of sea-floor depths, one per line. Part 1 counts the measurements
deeper than the one just before. Part 2 adds up every run of three
consecutive measurements (a sliding window) and counts the sums larger than
the sum before. Answers on Matt's input: 1616 and 1645 (his Scala
solution's); the puzzle's example gives 7 and 5. Compiler built from `main`
at 0eb53617, 31 October 2026.

### The program

Part 2 doesn't add the windows up. Two neighbouring windows share all but
one measurement each, so the later sum is larger exactly when the
measurement it gains is deeper than the one it loses, three places earlier.
Both parts are then one function:

```stitchwort
def solvePart1 (depths: List Nat): Nat := increasesOver 1 depths

def solvePart2 (depths: List Nat): Nat := increasesOver 3 depths

-- How many measurements are deeper than the one `gap` places before them.
def increasesOver (gap: Nat) (depths: List Nat): Nat :=
  depths.zip (depths.drop gap) |> .count (pair => pair.fst < pair.snd)
```

The parser is `Parse.eachLine input (() => token nat)`, and its errors
("line 2, column 2: expected the end of the line, got 'x'") came out as
the tests guessed them, first time.

The spec (`Spec/Spec.sw`) is the puzzle's way: pair each measurement with
the next and count the pairs that go deeper; build the windows from the
list's suffixes and add each one up.

```stitchwort
def increases (measurements: List Nat): Nat :=
  measurements.zipWithNext |> .count (pair => pair.fst < pair.snd)

def slidingWindows (size: Nat) (measurements: List Nat): List (List Nat) :=
  measurements.tails
    |> .map (.take size)
    |> .filter (window => window.length == size)

def windowIncreases (size: Nat) (measurements: List Nat): Nat :=
  slidingWindows size measurements |> .map .sum |> increases
```

### Proved, for every list of depths

In `Aoc.Year2021.Day01.Proofs` (`Proofs/Proofs.sw`, 118 lines):

- `part1Correct`: `solvePart1 depths = increases depths`.
- `windowsCorrect`: for windows of any size `Succ m`,
  `increasesOver (Succ m) depths = windowIncreases (Succ m) depths`. The
  shortcut holds for every window size, not just three.
- `part2Correct`: `solvePart2 depths = windowIncreases 3 depths`, an
  instance of the above.
- The example's answers as `rfl` theorems (`examplePart1`,
  `examplePart2`, in `Tests/Examples.sw`).

Nothing is left unproved, no hypothesis was added, and nothing is opaque.
`stitchwort audit Aoc.Year2021.Day01`: `audited 14 theorems: 0 failed, 0
with warnings, 14 passed`.

Breaking the program breaks the proofs, with a counterexample each time:
`pair.fst <= pair.snd` in `increasesOver` makes `part1Correct` and
`windowsCorrect` fail; `increasesOver 2` in `solvePart2` makes
`part2Correct` fail with `depths = [0, 0, 1]` (left 1, right 0).

The proof is the induction you'd write on paper: if there is an element
at `m` in `rest`, the first window of `Cons x rest` is `x` plus the
`shared` sum of `take rest m`, the second is `shared` plus that element,
and `x + shared < shared + gained` is `x < gained`. `cases` proved that
last step on its own:

```stitchwort
theorem slideCompare (x: Nat) (shared: Nat) (y: Nat):
    Bool.toNat (x + shared < shared + y) = Bool.toNat (x < y) :=
  cases
```

### 1. Std.Parse: none

`Parse.eachLine` with `token nat` was all it took.

### 2. Missing std

- **No sliding windows.** Scala has `sliding(3)`, Kotlin `windowed(3)`, Rust
  `slice::windows(3)`, Haskell `divvy` (split). Std has `zipWithNext` (pairs)
  and `chunksOf` (non-overlapping), not overlapping windows. The spec built
  them from `tails`, and the proofs needed two lemmas about it,
  `windowsLong` and `windowsShort`. Std candidate: `List.windows (size:
  Nat) (xs: List a): List (List a)` with those two lemmas, and
  `List.windows 2 xs` related to `zipWithNext`.
- **`List.drop` lemmas are thin, and some live in the wrong place.** Std
  has `List.takeSucc` (`take xs (Succ k)` is `take xs k` plus the element
  at `k`) and `List.takeAll` (taking past the end is the whole list), but
  not their `drop` counterparts, which this day proved:

  ```stitchwort
  theorem dropAt (d: Nat): (xs: List Nat) → (m: Nat) → m < List.length xs →
      List.drop xs m = Cons (List.getOr xs m d) (List.drop xs (Succ m))
  theorem dropPast: (xs: List Nat) → (m: Nat) → List.length xs ≤ m → List.drop xs m = Nil
  ```

  The search for `List.drop _ (Succ _)` found `List.drop [] n = []`,
  `drop xs (n + m) = drop (drop xs n) m` and `drop xs (length xs) = []`,
  all three in `Std.Map.Tree` (std/Map/Spec.sw:1278–1287), so a program
  needs `import Std (Map)` for a list lemma. `Nat.equal a b = Nat.equal b a`
  is `Std.Float.Theory.equalSwap` (std/Float/Theory.sw:1255). Std
  candidates: `List.dropAt`, `List.dropPast`, and the `Map.Tree` three
  moved to `List`, generic in the element type.
- **No Bool identity.** Counting the `True`s of a `List Bool` wanted
  `.count id` or `.countTrue`; std has neither, so it would be
  `.count (b => b)`.

### 3. Confusing errors

- **`(<)` gives a `Prop`, and the error points at the wrong place.** The
  first program was

  ```stitchwort
  depths.zipWith (depths.drop gap) (<) |> .count (deeper => deeper)
  ```

  ```text
  [E-AUTO-NONE] Error: no way to decide `deeper`
   41 │   depths.zipWith (depths.drop gap) (<) |> .count (deeper => deeper)
      │                                                             ───┬──
      │                                                                ╰──── this is a proposition, and nothing decides it
      │ Note: a `Bool` is expected here, and a proposition is turned into one only if it has a decision procedure: an `instance` returning `Decidable …`
  ```

  `(<)` on `Nat` is `a b => a < b` with a `Prop` result, so the list is a
  `List Prop`, and `deeper` is one of its elements: a variable with no
  decision procedure. The message is true but names the symptom. `x < y`
  written where a `Bool` is expected becomes a `Bool`; `(<)` passed to a
  generic `zipWith` doesn't, since nothing says `c` is `Bool`. A note when
  the undecidable proposition is a variable whose type came from an
  operator section (or the section elaborated as `Bool` when the target
  type is a type variable) would have saved the detour. The program now
  zips and compares inside `count`'s lambda.
- **`if h:` on a proof.** `if h: m < List.length rest then calc … else calc …`
  inside a theorem is `E-UNIVERSE`, "`if` can't choose between proofs yet …
  use `match b with | True => … | False => …`". Matching on a `Bool` loses
  `h`. What works is matching on the decision procedure,
  `match Nat.decLessThan m (List.length rest) with | Yes h => … | No h => …`,
  and its name was found by searching for its type,
  `stitchwort search '(a: Nat) → (b: Nat) → Decidable (a < b)'`. The note
  should suggest that form (and name the procedure when `auto` can find
  it).
- **Goals show `==` as the decision procedure's insides.** A
  `filterKeep` premise showed as
  `Std.Decidable.toBool (Nat.decEqFrom (Succ m) (Succ m) (Nat.equal m m) rfl)`
  and `True` aren't equal, not as `(Succ m == Succ m) = True`. Rewriting
  `Nat.equalRefl m` in it is `E-REWRITE-MOTIVE` (the `rfl` is a proof
  about `Nat.equal m m`). `DecEq.refl (Succ m)` closes it, but finding that
  meant reading the unfolded term back into `==`. Showing a goal with
  `Decidable.toBool (DecEq.decide a b)` folded back to `a == b` would make
  it findable.

### 4. Inference

- **Holes in a lemma aren't solved before its proof argument (2024's day 1
  item 4 again).** In `windowsShort`,
  `Eq.trans (List.filterSkip _ _ _ (rewrite List.takeAll rest m … in …)) …`
  fails with `E-REWRITE-NOTHING`, goal `?6 m h x rest (?7 m h x rest) =
  False`: the `rewrite` is checked before the list and the predicate are
  known. Writing them out works but repeats the spec's lambdas:

  ```stitchwort
  List.filterSkip (List.map (List.tails rest) (.take (Succ m))) (window => window.length == Succ m) (Cons x (List.take rest m))
    (rewrite List.takeAll rest m (omega [h]) in Decidable.toBoolOfNot _ (same => omega [same, h]))
  ```

  The same holes in `windowsLong` (`List.filterKeep _ _ _ (rewrite …)`)
  were fine, because there the call is the whole proof and its type is
  known; inside `Eq.trans` the middle term isn't.

  Fixed (SW-931): the holes were filled; the message was wrong. The
  failing try was a different proof, `rewrite List.takeAll …,
  equalBelow … in rfl`, which fails with the holes written out too
  (`E-REWRITE-MOTIVE`); the rewrite that worked came with the written-out
  arguments. `Eq.trans`'s type is compared with the goal first, so the
  `rewrite` is checked against `(… == Succ m) = False`. When that fails,
  the call is elaborated again without the goal to keep old messages, and
  that second error (the goal of unknowns) was the one shown. Now the
  first is shown when both are inside the same argument, as it already
  was for a lambda. `windowsShort` writes `List.filterSkip _ _ _ (…)`.

### 5. Performance

Nothing to report: `stitchwort check --no-cache` of the day's four
namespaces takes 2.2 s, the proofs among them.

### 6. Proofs, and the lemma search

`stitchwort search` found most of what the proofs use, by shape, with the
import to add: `List.countCons` (`--rewrite 'List.count (Cons _ _) _'`),
`List.sumCons`, `List.sumAppend`, `List.takeSucc`
(`--rewrite 'List.take _ (Succ _)'`), `List.takeAll`, `List.lengthTake`,
`List.filterKeep` and `List.filterSkip` (`--rewrite 'List.filter (Cons _ _) _'`),
`Nat.decLessThan`, `Nat.equalRefl` and `DecEq.refl` (`'(x == x) = True'`).
None was written again. What didn't work:

- `stitchwort search --rewrite 'List.sum (_ ++ _)'` is `E-TYPE-MISMATCH`,
  "`++` joins two texts or two lists … this is a `?2`": with both sides
  holes, `++` can't tell which. `List.sum (List.append _ _)` finds
  `List.sumAppend`. The pattern could take `++` on holes as `List.append`
  when its context (here `List.sum`) wants a list.
- A pattern with premises, `'(xs: List _) → List.length xs ≤ _ → List.drop xs _ = _'`,
  went to the relaxed pass and listed `Exists.map`, `Quot.funext` and the
  like: nothing like it exists (above), but the results read as if
  something did. `'⊢ (_ == _) = False'` listed `DecEq.sound`, whose
  conclusion `x = y` is an instance only because `x` swallows the whole
  `_ == _`.
- While the project doesn't check (a proof with an error), every search
  prints those errors again before its results.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day01` | 0.75 s user (1.5 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day01.Proofs Aoc.Year2021.Day01.Tests` | 1.1 s user (2.2 s) |
| `stitchwort run Aoc.Year2021.Day01.main` on the input (2000 lines) | 0.22 s user (0.43 s), warm |

41 lines of program, 23 of spec, 118 of proofs, 54 of tests.

### Ranked

1. `(<)` passed to a generic function gives a `Prop`, and the error lands
   on a later lambda's variable (item 3). Fix: a note naming the operator
   section the `Prop` came from, or elaborate a comparison section as
   `Bool` when nothing asks for a `Prop`.
2. Holes in a lemma call aren't solved before its proof argument is
   checked, inside `Eq.trans` (item 4; NOTES-2024 day 1 item 4). Fix:
   postpone a `rewrite`/lambda argument until the call's other arguments
   are known. Fixed (SW-931): they were solved; the error shown came from
   a second try without the goal (item 4).
3. No `List.windows`, and no `List.dropAt`/`List.dropPast`; three list
   lemmas live in `Std.Map.Tree` (item 2). Fix: add them to `List`, move
   the three.
4. `if h:` in a proof says to match on a `Bool`, which loses `h` (item 3).
   Fix: suggest `match Nat.decLessThan a b with | Yes h => … | No h => …`.
5. Goals print `==` as `Decidable.toBool (Nat.decEqFrom …)` (item 3). Fix:
   fold it back to `a == b` when showing a goal.
6. The search: `++` on holes doesn't elaborate; premise patterns fall to a
   relaxed pass of unrelated results; project errors repeat on every
   search (item 6).

## Day 2: Dive!

A list of submarine commands, one per line: `forward X`, `down X`, `up X`.
Part 1 reads forward as moving ahead and down and up as changing the
depth; part 2 reads down and up as changing an aim, and forward as moving
ahead and sinking by the aim times X. Each answer is the final horizontal
position times the final depth. Answers on Matt's input: 1635930 and
1781819478 (his Scala solution's); the puzzle's example gives 150 and 900.
Compiler built from `main` at 61b4e4ca, 31 October 2026.

### The program

The program doesn't steer the submarine command by command. The horizontal
position is the sum of the forward moves; part 1's depth is the sum of the
downs less the ups; part 2's aim before each command is a running sum of
the same thing, so its depth is the sum of each forward move times the aim
it is made at:

```stitchwort
def horizontal (commands: List Command): Nat := commands.sumBy .ahead

def solvePart1 (commands: List Command): Int :=
  (horizontal commands).toInt * commands.sumBy .down

def solvePart2 (commands: List Command): Int :=
  (horizontal commands).toInt * aimedDepth 0 commands

def aimedDepth (aim: Int) (commands: List Command): Int :=
  commands
    |> .scanLeft aim (aimSoFar command => aimSoFar + command.down)
    |> .zipWith commands (aimThen command => aimThen * command.ahead.toInt)
    |> .sum
```

`Command.ahead` is X for `forward X` and 0 otherwise; `Command.down` is X
for `down X`, -X for `up X` and 0 for forward. The parser is
`pick [("forward", Forward), ("down", Down), ("up", Up)]` under a `label`,
then `spaces1` and `nat`. All four error messages the tests guessed
("line 2, column 1: expected forward, down or up, got 'b'", "expected a
space", "expected a number, got the end of the line", "got '-'") came out
as written, first time. The program gave both answers on its first run.

**`Int` or `Nat`.** Depth and aim are `Int`. The puzzle never says the
submarine stops at the surface, and Matt's input never goes above it, so
`Nat` would be right on the input. But with `Nat`, `up` past 0 would
truncate, and the spec would then either model a rule the puzzle doesn't
have or need a hypothesis ("the commands never go above the surface") on
every theorem. With `Int` the spec follows `up` as written, there is no
hypothesis, and a test pins what happens past the surface
(`solvePart1 [Up 3, Forward 2] == -6`, and the spec agrees). The
horizontal position stays a `Nat`: only forward moves it. `ring` reads
`x.toInt` as arithmetic, so the casts cost nothing in the proofs.

The spec (`Spec/Spec.sw`) is the puzzle's way: a `Submarine` record
(`horizontal`, `depth`, and `aim` for part 2), a `follow` function per
part with one case per command in the puzzle's words, and
`commands.foldLeft surface follow`.

### Proved, for every list of commands

In `Aoc.Year2021.Day02.Proofs` (`Proofs/Proofs.sw`, 63 lines):

- `part1Correct`: `solvePart1 commands = part1 commands`.
- `part2Correct`: `solvePart2 commands = part2 commands`.
- On the way, from any starting submarine: the horizontal position grows
  by `horizontal commands` (`horizontalAfter`, `aimedHorizontalAfter`),
  part 1's depth by the sum of `Command.down` (`depthAfter`), part 2's aim
  by the same sum (`aimAfter`, not needed by `part2Correct`), and part 2's
  depth by `aimedDepth` at the starting aim (`aimedDepthAfter`).
- The example's answers as `rfl` theorems (`examplePart1`,
  `examplePart2`, in `Tests/Examples.sw`).

Nothing is left unproved, no hypothesis was added, and nothing is opaque.
`stitchwort audit Aoc.Year2021.Day02`: `audited 13 theorems: 0 failed, 0
with warnings, 13 passed`.

Every induction step is the same line, and `cases` did the rest, splitting
the command and closing each case with `omega` (horizontal and depth are
the IH plus one term):

```stitchwort
theorem aimedDepthAfter (start: AimedSubmarine): (commands: List Command) →
    (List.foldLeft commands start AimedSubmarine.follow).depth = start.depth + aimedDepth start.aim commands
  | Nil => omega
  | Cons command rest =>
    rewrite aimedDepthAfter (start.follow command) rest, aimedDepthCons start.aim command rest in cases
```

The final theorems are `rewrite` with two of these lemmas, `in ring`. Every
proof checked the first time it was written.

Breaking the program breaks the proofs, with a counterexample each time:
`Up units => units.toInt` in `Command.down` makes `depthAfter` and
`aimAfter` fail with `commands = [Up 1]` (left -1, right 1) and
`aimedDepthAfter` with `commands = [Up 1, Forward 1]`;
`aimedDepth 1` in `solvePart2` makes `part2Correct` fail with
`commands = [Forward 1]` (left 1, right 0); zipping with `commands.drop 1`
makes `aimedDepthCons` fail with `command = Forward 1`. One attempted
break wasn't one: using the aim *after* each command,
`(aimThen + command.down) * command.ahead.toInt`, gives the same answers,
since a command that moves ahead doesn't change the aim. Only
`aimedDepthCons`'s proof (`List.sumCons _ _`) stopped checking, with no
counterexample, which is right.

### 1. Std.Parse: none

`pick`, `label`, `spaces1` and `nat` did it.

### 2. Missing std: none

`List.sumBy`, `List.scanLeft`, `List.zipWith`, `List.sumByCons` and
`List.sumCons` were all there.

### 3. Confusing errors

- **A false `cases` goal over `Int` shows `Int`'s insides, and runs out of
  cases.** With `up` broken (above), `depthAfter`'s open case reads

  ```text
  [E-CASES] Error: `cases` can't close the case command = Up units✝, start.depth = OfNat n✝, Int.neg (OfNat units✝) = NegSucc n✝, Int.subNatNatFrom n✝ (Succ n✝) (Succ n✝ - n✝) = OfNat n✝, List.foldLeft rest 0 (acc x => acc + Command.down x) = OfNat n✝
    Note 1: goal: OfNat (n✝ + n✝) = OfNat (n✝ + (units✝ + n✝))
  ```

  and `aimedDepthAfter`'s is `E-CASES-BUDGET` ("made more than 64 cases
  without closing them all"), its first open case splitting
  `Int.subNatNatFrom` and `Int.neg (OfNat (n✝ * 0))`. `cases`, finding
  nothing that closes the case, falls back to splitting the `Int`s
  themselves (`OfNat`/`NegSucc`) and the helpers they compute to. The
  counterexample note under each was right and is what pointed at the
  bug; the case description didn't help. A `cases` that stops splitting
  at `Int` (it isn't a finite type, and `omega` already knows it), and
  reports the case as `command = Up units` with the goal in `+` and `-`,
  would read better.
- **A goal shows `List.sumBy []` over `Int` but not over `Nat`.** The
  `Nil` cases printed `⊢ start.horizontal = start.horizontal` for the
  `Nat` field and `⊢ start.depth = start.depth + List.sumBy [] Command.down`
  for the `Int` one. `omega` closed the second, so it computes, but the
  printed goal made it look stuck. Speculation, not checked: `Int`'s `+`
  doesn't compute on an unknown left side, so the goal printer keeps the
  form as written.
- **Importing constructors is refused, helpfully.**
  `import Aoc.Year2021.Day02 (Command, Forward, Down, Up)` is
  `E-IMPORT-UNKNOWN` with "`Forward` is a constructor of `Command`, and
  constructors come with their type: import `Command` instead". Not
  friction: the note said the fix.

### 4. Inference: none

### 5. Performance

Nothing to report: `stitchwort check --no-cache` of the proofs and tests
takes 1.9 s.

### 6. Proofs, and the lemma search

`stitchwort search --rewrite 'List.sumBy (Cons _ _) _'` gave
`List.sumByCons` first, and `--rewrite 'List.sum (Cons (_: Int) _)'`
gave `List.sumCons`. Both were used, and nothing was proved again. What
didn't work:

- `--rewrite 'List.sum (Cons (_: Int) _)'` ranked `List.sumInts`
  (`List.sum [3, -5, 1] = -1`, a closed example) above `List.sumCons`.
  `--rewrite 'List.scanLeft (Cons _ _) _ _'` gave `List.scanLeftSums`
  (`List.scanLeft [1, 2, 3] 0 … = [0, 1, 3, 6]`) first. The search hides
  examples only when their name ends in `Example`; these two don't. Fix:
  rename them, or rank a closed statement (no variables) last.
- `--rewrite 'List.sumBy [] _'` found 36 results, none about `[]` (there
  is no `List.sumByNil`; it computes, so none was needed). An `instance`
  match whose left side is any list ranks the same as one for `[]`.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day02` | 0.71 s user (1.3 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day02.Proofs Aoc.Year2021.Day02.Tests` | 1.2 s user (1.9 s) |
| `stitchwort run Aoc.Year2021.Day02.main` on the input (1000 lines) | 0.24 s user (0.53 s), warm |

80 lines of program, 45 of spec, 63 of proofs, 50 of tests.

### Ranked

1. A failed `cases` over `Int` describes the case by `Int`'s
   constructors and helpers (`Int.subNatNatFrom …`), and can run out of
   its 64 cases (item 3). Fix: don't split `Int`s in the fallback; show
   the case in the program's terms.
2. The search ranks closed examples (`List.sumInts`,
   `List.scanLeftSums`) above the general lemma (item 6). Fix: hide or
   rank last theorems with no variables, or rename them `…Example`.
3. The goal printer shows `List.sumBy [] f` unreduced over `Int` (item 3;
   cause not established).

## Day 3: Binary Diagnostic

A diagnostic report: a list of binary numbers, one per line, all with the
same number of bits. Part 1 builds the gamma rate from each column's most
common bit and the epsilon rate from each column's least common bit, and
multiplies them. Part 2 filters the report one column at a time, keeping
the numbers with the column's most common bit (the oxygen generator
rating; a tie keeps 1s) or its least common bit (the CO2 scrubber rating;
a tie keeps 0s), until one number is left, and multiplies the two
ratings. Answers on Matt's input: 4191876 and 3414905 (his Scala
solution's); the puzzle's example gives gamma 22 and epsilon 9 (198),
oxygen 23 and CO2 10 (230). Compiler built from `main` at 45960bff, 31
October 2026.

### The program

A number is `type Bits = List Bool`, most significant bit first, and its
value is `bits.foldLeft 0 (high bit => high * 2 + bit.toNat)`. A column's
most common bit is 1 when at least half its bits are:

```stitchwort
def mostCommon (column: List Bool): Bool := column.length ≤ 2 * column.count (bit => bit)

def solvePart1 (numbers: List Bits): Nat :=
  let gamma: Bits := numbers.transpose |> .map mostCommon
  gamma.value * (Nat.pow 2 gamma.length - 1 - gamma.value)
```

Part 1 works out only the gamma rate. The least common bit of a column is
the one the most common bit isn't, so the epsilon rate is the gamma rate
with its bits flipped, `2^width - 1 - gamma`. Part 2 never looks a column
up by position: it keeps, of each number whose first bit is the chosen
one, the bits after it, so the next column is always the first, and puts
the chosen bits back on the front of the one number left:

```stitchwort
def rating (choose: List Bool → Bool): (columns: Nat) → List Bits → Option Bits
  | _, [number] => Some number
  | Zero, _ => None
  | Succ later, numbers =>
    let bit := choose (numbers.filterMap .head)
    rating choose later (numbers.filterMap (afterBit bit)) |> .map (Cons bit)
```

`choose` is `mostCommon` for oxygen and `not (mostCommon column)` for
CO2. The parser is `Parse.eachLine input (() => many1 bit)`, with `bit` a
`pick` of `"0"` and `"1"` under a `label`, then a check that every line
has the first line's number of bits ("line 2: 3 bits, but the first line
has 4"). Both answers were right on the program's first run.

**What the puzzle leaves open, and the spec decides.** The spec
(`Spec/Spec.sw`) reads the puzzle's way: `howMany numbers position bit`
counts the numbers with that bit at that position, the rates read
`List.range width` through `mostCommonAt` and `leastCommonAt`, and
`findRating` goes through the positions in turn, stopping when one number
is left and otherwise keeping the numbers with the criterion's bit there.
Three things needed deciding, and the spec's header says each:

- **Ties in part 1.** The puzzle gives tie rules only in part 2, and its
  part 1 inputs have no ties (Matt's has no tied column). Part 1 takes
  part 2's rules: a tie's most common bit is 1, its least common bit 0.
- **A bit no number has.** "The least common value (0 or 1)" counts both
  values, so in a column where every number left has a 1, 0 is the least
  common (0 times), and keeping the numbers with a 0 keeps none. The
  other reading, the least common of the values present, would keep the
  filter from ever emptying, but the puzzle doesn't say it, and it would
  make part 1's least common bit differ from part 2's. Matt's input can't
  tell the two apart: the CO2 filter never meets a column that is all one
  bit (the oxygen filter does, at the 11th bit with two numbers left,
  where both readings agree).
- **Where it stops.** "If you only have one number left, stop", and
  otherwise go on to the next bit. If no bit is left (the same number
  twice) or no number is (above), the puzzle has no rating. The spec's
  ratings are `Option Nat`, `None` there, and `lifeSupportRating` is
  `None` unless both exist. So the spec is total, and part 2's theorem
  needs no hypothesis (no "the numbers are distinct", no "exactly one is
  left").

The spec takes the width from the first number, and a number too short to
have a bit at a position counts as neither a 0 nor a 1 there. The parser
rejects such input, but the spec is defined for it, and so is the
program: `List.transpose` also takes the first row's width and leaves a
short row out of a column. With that, the theorems hold for every
`List Bits`.

### Proved, for every list of numbers

In `Aoc.Year2021.Day03.Proofs` (`Proofs/Proofs.sw`, 250 lines):

- `part1Correct`: `solvePart1 report = powerConsumption report`.
- `part2Correct`: `solvePart2 report = lifeSupportRating report`: the
  same answer, or `None` on both sides.
- `epsilonComplement`: `gammaRate report + epsilonRate report + 1 =
  Nat.pow 2 (width report)`, in the spec's terms: the epsilon rate is the
  gamma rate's complement within the width. `part1Correct` rests on it.
- On the way: column i of `transposeN` is the bit at i of every number
  that has one (`columnsFrom`, `columns`); the program's `mostCommon` of a
  column is the spec's comparison of counts (`mostCommonColumn`); the
  least common bit is `not` the most common, ties included
  (`leastIsNotMost`); a number plus its bits flipped is `2^length - 1`
  (`valueFlipped`); and, for numbers that share a prefix, the spec's
  filtering from the position after it is the program's rating of their
  rests (`ratingAfterPrefix`, for any criterion that agrees with the
  program's `choose`; `ratingCorrect` from the empty prefix).
- The example's answers as `rfl` theorems (`examplePart1`,
  `examplePart2`, in `Tests/Examples.sw`).

Nothing is left unproved, no hypothesis was added, and nothing is opaque.
`stitchwort audit Aoc.Year2021.Day03` (with the counterexample search):
`audited 28 theorems: 0 failed, 0 with warnings, 28 passed`.

Not attempted: that the oxygen generator rating exists when the numbers
are distinct, there is at least one, and all have the same width. It
should hold (the most common bit is always one some number has), but
neither answer needs it. The CO2 rating has no such theorem under the
spec's reading: `[10, 11]` has no CO2 rating (a test pins it).

Breaking the program breaks the proofs: dropping the `- 1` in
`solvePart1` makes `part1Correct` fail with `report = [[True]]` (left 1,
right 0); `rating mostCommon` for CO2 makes `part2Correct` fail with
`report = [[False], []]` (left `Some 0`, right `None`); an `afterBit` that
keeps a number whatever its first bit makes `keepAfterPrefix` fail with
`prefix = [], bit = False, rests = [[True]]`. `<` for `≤` in `mostCommon`
makes `mostCommonColumn` fail with an open case but no counterexample (it
is stated for any `bitOf` function, which the search doesn't make);
`| Zero, numbers => numbers.head` in `rating` makes a `rfl` in
`ratingAfterPrefix` fail, with no counterexample for the same reason.

Most proofs are a `rewrite` with std lemmas, then `rfl`, `cases` or
`omega`. Rewriting under a binder, with the bound variable left as `_`,
worked every time, for example in `columnsFrom`:

```stitchwort
rewrite List.filterMapMap numbers (x => List.get x 0) (number => List.drop number p),
  List.mapMap numbers (x => List.drop x 1) (number => List.drop number p), List.getDrop _ p 0, Nat.addZero p,
  <- List.dropAdd p 1 in
  Eq.cong (later => Cons (List.filterMap numbers (number => List.get number p)) later) (columnsFrom numbers k (p + 1))
```

and the induction's `p + 1` met the goal's `Succ p` with no lemma. Part
2's one idea is to generalise over the prefix the numbers share, so that
the spec's "bit at position `length prefix`" is the program's "first bit
of the rest" (`getAfterPrefix`). Every proof checked as first written
(after adding `import Std (Eq)`) except two, `getAfterPrefix` and
`keepAfterPrefix` (item 3).

### 1. Std.Parse: none

`many1`, `pick` and `label` did it. The message for a bad bit
("expected 0 or 1 or the end of the line, got '2'") was better than the
one the test first guessed.

### 2. Missing std

- **No binary numbers.** `Nat.fromDigits` is base 10 only, and nothing
  reads a `List Bool` as a number. The day wrote `Bits.value` and proved
  `valueFrom`, `valueCons` and `valueFlipped` for it. Std candidate:
  `Nat.fromBits (bits: List Bool): Nat` with those three lemmas.
- **No lemma for what `transpose`'s columns are.** Std has
  `transposeNLength`, `transposeTwice` and the like. Std candidate:
  `List.transposeNColumns`, this day's `columnsFrom`: column i of
  `transposeN k (rows.map (.drop p))` is `rows.filterMap (.get i)`, for
  i from p.
- **No `Option.mapCong` or `Option.mapId`.** `List` has both. The day
  proved them for `Option Bits` (`optionMapCong`, `optionMapId`). At
  `Option.map o (x => x) = o` (in a scratch file), `search --at` offered
  `Option.orElseNone o`, `Map.orElseNone o` and `Map.Tree.orElseNone o`,
  which the kernel accepts because `orElse o None` and `map o (x => x)`
  compute to the same match. True, but nobody would look for it under
  that name.

  Added to std (SW-940): `Nat.fromBits` with `Nat.fromBitsFrom`,
  `Nat.fromBitsCons` and `Nat.fromBitsFlipped`;
  `List.transposeNColumnsFrom`, `List.transposeNColumns` and
  `List.transposeColumns`; `Option.mapCong` and `Option.mapId`. The day
  now uses them in place of `Bits.value` and its own lemmas.
- **Nothing about `List.count` with `List.filterMap`.** How many of a
  column's bits are 1s, and its length, as counts over the numbers
  (`onesInColumn`, `columnLength`). Std candidates: `List.lengthFilterMap`
  (the count of `Some`s) and `List.countFilterMap`.

### 3. Confusing errors

- **`cases` splits calls instead of the variable under them, and loses
  what ties them together.** `getAfterPrefix`'s `Nil` case is
  `List.get t 0 = List.head t`, and `cases` failed with

  ```text
  [E-CASES] Error: `cases` can't close the case List.get t 0 = None, List.head t = Some False, value✝ = False (fallback)
    Note 1: goal: None = Some False
  ```

  It split `List.get t 0` and `List.head t` as two separate `Option`s,
  making cases that can't happen (one `None`, the other `Some`), instead
  of splitting `t`, which both are stuck on. `keepAfterPrefix` did the
  same with `List.head rest` and `afterBit False rest`, then said the goal
  was stuck on `others`. `match t with | Nil => rfl | Cons … => rfl`
  proved it. When the stuck calls are stuck on the same variable,
  splitting it would close them all.
  Fixed (SW-939): `cases` now splits `t` first; both proofs are `cases`.
- **Goals show `List.count` as its insides, and `==` on an `Option` as a
  decision procedure.** With `mostCommon` broken, the open case read
  `List.foldLeft numbers 0 (n x => Nat.succIf n (Std.Decidable.toBool
  (Option.decEq (x y => …) (bitOf x) (Some …))))` where the source says
  `List.count numbers (number => bitOf number == Some True)`. Day 1 item 3
  again, now for `count` as well as `==`.
- **A `match` on a tuple loses structural recursion, and the message
  doesn't say so.** The first `rating` was `match (numbers, columns) with
  | ([number], _) => … | (_, Succ later) => … rating choose later …`,
  which is `E-TERMINATION`, "the 1st argument stays the same", though
  `later` comes from matching `columns`. Clauses on the parameters
  (`| _, [number] => …`, `| Succ later, numbers => …`) checked. A note
  that matching a tuple of the parameters hides their pieces, with the
  clause form as the fix, would have saved the guess.
  Fixed (SW-941): the error now has a note saying the tuple match is why,
  suggesting `match numbers, columns with` (no brackets) or `decreasing`.

### 4. Inference: none

### 5. Performance

Nothing to report: `stitchwort check --no-cache` of the proofs and tests
takes 3.0 s (0.9 s user).

### 6. Proofs, and the lemma search

`stitchwort search --rewrite` found every std lemma the proofs use, first
or nearly first, each from its left side (`'List.get (List.drop _ _) _'`,
`'List.count (List.map _ _) _'`, …): `List.countCons`, `List.countMap`,
`List.filterMapMap`, `List.mapMap`, `List.mapId`, `List.mapCong`,
`List.getDrop`, `List.dropAdd`, `List.appendAssoc`, `List.lengthMap`,
`List.lengthRangeFrom` and `Option.mapMap`. None was written again. What
didn't work:

- `stitchwort search --at` on the project's proof file is
  `E-FILE-MODE` ("searched as a single file, so it can use only the
  standard library"), as syntax.md says it is for now. Five goals copied
  into a scratch file with std types only: it closed
  `List.get (List.drop xs p) 0 = List.get xs p` (`rewrite List.getDrop xs
  p 0 in rfl`) and `List.append prefix (Cons bit rest) = List.append
  (List.append prefix [bit]) rest` (`rewrite List.appendAssoc prefix [bit]
  rest in rfl`), both checked by the kernel, and offered
  `List.getAppendRight` as a first rewrite for `getAfterPrefix`'s goal.
  For `(a < b) = ¬(b ≤ a)` it found nothing and named no tactic, though
  `cases` proves it (`leastIsNotMost`): `cases` isn't among the closers
  it tries.
- Every `search --at` run warned "3 comparisons ran out of steps: a match
  may have been missed", whatever the goal.
- `search --rewrite 'List.drop _ 0'` is `E-SEARCH-PATTERN`, "this pattern
  is a hole on its own", pointing at the whole pattern. It is one, once
  computed: `List.drop xs 0` computes to `xs`. The message should say the
  pattern computes to a hole (so the equation holds by `rfl`).
- `search '(?a < ?b) = not (?b ≤ ?a)'` went to the relaxed pass and
  listed `Eq.sym` and `Option.someInjective`.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day03` | 0.73 s user (2.8 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day03.Proofs Aoc.Year2021.Day03.Tests` | 0.93 s user (3.0 s) |
| `stitchwort run Aoc.Year2021.Day03.main` on the input (1000 lines) | 0.34 s user (0.39 s), warm |
| `stitchwort audit Aoc.Year2021.Day03` (with the search) | 4.4 s user (6.2 s) |

82 lines of program, 81 of spec, 250 of proofs, 68 of tests.

### Ranked

1. `cases` splits stuck calls as separate values instead of the variable
   they are stuck on, making cases that can't happen (item 3). Fix: split
   the variable when the stuck calls share it.
2. `search --at` doesn't work in a project's files, so each goal has to
   be copied into a scratch file with std types (item 6). Fix: the next
   stage of SW-915's search.
3. No binary numbers, no lemma for `transpose`'s columns, no
   `Option.mapCong` or `Option.mapId` in std (item 2). Fix:
   `Nat.fromBits`, `List.transposeNColumns`, the two `Option` lemmas.
4. A `match` on a tuple of parameters hides structural recursion, with no
   hint (item 3). Fix: a note suggesting clauses on the parameters.
5. The search: a pattern that computes to a hole says only "a hole on its
   own"; `search --at` doesn't try `cases`, and warns about comparisons
   out of steps on every goal (item 6).

## Day 4: Giant Squid

Bingo. The input is the numbers to be drawn, in order, on one line, then
5 by 5 boards separated by blank lines. A drawn number is marked on every
board that has it, and a board wins once every number of one of its rows
or columns is marked (diagonals don't count). A board's score is the sum
of its unmarked numbers times the number just drawn. Part 1 is the score
of the first board to win, part 2 of the last. Answers on Matt's input:
49860 and 24628 (his Scala solution's); the puzzle's example gives 4512
and 1924. Compiler built from `main` at fcab7cf9, 31 October 2026.

### The program

The program doesn't play the game draw by draw. A number is drawn on the
turn of its first place among the draws (`List.indexOf`, which gives the
list's length for a number never drawn); a row or column is complete on
the turn its last number is drawn, and a board wins on the turn its first
row or column is:

```stitchwort
def Board.lines (board: Board): List (List Nat) := board ++ board.transpose

def winningTurn (draws: List Nat) (board: Board): Nat :=
  board.lines
    |> .map (line => line.foldLeft 0 (latest number => Nat.max latest (draws.indexOf number)))
    |> .foldLeft draws.length Nat.min
```

The score on that turn adds up the board's numbers drawn after it. The
boards are then taken turn by turn, `List.range draws.length |> .flatMap
(turn => …)`, each turn's winners in the order they are listed; part 1 is
the first score of that list, part 2 the last. The parser is `sepBy1 nat
(() => char ',')`, `blankLine`, then `sections (() => lines (() => many1
(() => token nat)))`, and a check that each board is 5 by 5 ("board 1
isn't 5 by 5"). All 16 tests, the real input's answers among them, passed
on the first run.

**What the puzzle leaves open, and the spec decides.** The spec
(`Spec/Spec.sw`) plays the game: draw the next number, then the boards
still playing that now have a row or column all marked leave the game, in
the order they are listed, each with its score. The result is the list of
scores in the order the boards win, and the answers are its first and last
elements. The spec's header says each decision:

- **Several boards winning on the same draw** win in the order they are
  listed: the first to win is the earliest listed of those that win first,
  the last to win the latest listed of those that win last. Matt's input
  doesn't test it: one board wins first (on the 12th draw) and one last
  (on the 86th), counted with a scratch script.
- **Boards that never win** take no part: the last board to win is the
  last of those that do. With no winner at all both answers are `None`,
  so the spec is total and the theorems need no hypothesis. (Every board
  of Matt's input wins.)
- **Draws after a board has won** don't change its score (it has left the
  game), and draws after every board has won change nothing.
- **A number drawn twice** is marked once; "the number that was just
  called" is the draw that completed the line.

The spec is defined for boards of any shape (its columns are
`List.transpose`'s), so the theorems hold for every `Game`, not only 5 by
5 ones.

### Proved, for every input

In `Aoc.Year2021.Day04.Proofs` (`Proofs/Proofs.sw`, 143 lines):

- `part1Correct`: `solvePart1 game = firstWinnerScore game`.
- `part2Correct`: `solvePart2 game = lastWinnerScore game`.
- Both from `winningScoresPlay`: the program's scores in winning order are
  the game's, `winningScores game = play [] game.boards game.draws`.
- On the way: a number is marked after the draws `drawn` exactly when its
  first place among all the draws is before `List.length drawn`
  (`markedBefore`); a line is complete then when the latest of its
  numbers' places is (`latestBefore`), and a board has won when the
  earliest of its lines is (`earliestBefore`), so `wins drawn board` is
  `winningTurn (drawn ++ rest) board < List.length drawn` once a number is
  drawn (`winsBefore`); the spec's score is the program's (`scoreAt`); and
  the game from any point, with the boards that haven't won yet, gives the
  boards turn by turn from there (`playFrom`, the induction).
- The example's answers as `rfl` theorems (`examplePart1`,
  `examplePart2`, in `Tests/Examples.sw`).

Nothing is left unproved, no hypothesis was added, and nothing is opaque.
`stitchwort audit Aoc.Year2021.Day04` (with the counterexample search):
`audited 21 theorems: 0 failed, 0 with warnings, 21 passed`.

Breaking the program breaks the proofs, with a counterexample each time:
rows only in `Board.lines` makes `winsBefore` fail with `drawn = [0]`,
`board = [[0, 1]]` (a column wins); `turn <= draws.indexOf number` in
`score` makes `scoreAt` fail with `drawn = []`, `number = 1`, `board =
[[1]]`; `won <= turn` in `winningScores` makes `winningScoresPlay` fail
with `game = { draws = [0, 0], boards = [[[]]] }` (left `[0, 0]`, right
`[0]`).

The one idea is `playFrom`'s invariant: the boards still playing after
the draws `drawn` are those whose winning turn isn't before `List.length
drawn`, so the boards the next draw removes are exactly those whose turn
it is. Stated over `drawn ++ rest` (the draws made and to come), the
induction step rewrites its hypothesis with `List.appendAssoc` to move
the next draw into `drawn`:

```stitchwort
rewrite List.appendAssoc drawn [number] later, List.lengthSnoc drawn number at playFrom playing later (drawn ++ [number])
```

and the step is then `rewrite wonNow, stillPlaying, afterNow, List.mapCong
_ _ _ (scoreAt drawn number later) in rfl`. Every proof checked as first
written apart from two statements and one `let` (item 3). The small
`Bool` facts (`thisTurn`, `laterTurn`, `pastTheEnd`, and the fold
lemmas' steps) were all `cases`.

### 1. Std.Parse: none

`sepBy1`, `blankLine`, `sections`, `lines`, `many1` and `token` read the
input as written; `token nat` takes the boards' leading spaces. The error
the test guessed for a bad draw ("line 1, column 3: expected a number, got
'x'") came out as written.

### 2. Missing std

- **No `List.filterFilter`.** Filtering twice is filtering once by both
  conditions. `search --rewrite 'List.filter (List.filter _ _) _'` found
  only `filterAll`, `filterNone`, `filterSkip` and `filterCongMem`, and
  `search --at` on the goal in a scratch file found nothing. The day
  proved it (`filterFilter`, 4 lines). Std candidate:
  `List.filterFilter: List.filter (List.filter xs p) q = List.filter xs
  (x => p x ∧ q x)`.
- **Nothing ties `List.contains` to `List.indexOf`.** Std has two
  `indexOf` theorems (`indexOfLt`, `getOrIndexOf`). The day proved
  `markedBefore`: `List.contains drawn x = (List.indexOf (drawn ++ rest) x
  < List.length drawn)`. Std candidate: `List.containsIndexOf`,
  `xs.contains x = (xs.indexOf x < xs.length)`, and the `append` form.
- **No lemmas about a fold of `Nat.max` or `Nat.min`.** `List.maximum`
  and `List.minimum` give `Option`s and have no lemmas either. The day
  proved `latestBefore` (the fold of `max` is below `k` when everything
  is) and `earliestBefore` (the fold of `min` is when something is). Std
  candidates: the two, for `foldLeft` with `Nat.max` and `Nat.min`.
- **`List.getOr (xs ++ Cons y ys) (List.length xs) d = y`.** `search --at`
  offered `List.getOrAppendRight`, which leaves `List.length drawn -
  List.length drawn` to clear with `Nat.subSelf`; a three-line induction
  (`drawOn`) was shorter.

### 3. Confusing errors

- **`∧` between a comparison and a `Bool` in a statement.** The fold
  lemma, written as it reads,

  ```stitchwort
  (List.foldLeft line latest (latest number => Nat.max latest (drawnAt number)) < k)
    = (latest < k ∧ List.all line (number => drawnAt number < k))
  ```

  is `E-NOT-A-TYPE`, "this has type `Bool`, so it isn't a type", at
  `List.all …`, with the note "`&&` here is on propositions". The left
  side, a comparison, made the equation one between propositions. Writing
  the left side as `((… < k): Bool)` fixed it. `markedBefore`, with a
  `Bool` on the left (`marked drawn number = (… < …)`), was fine as
  written. The note could suggest the ascription, or the comparison could
  be a `Bool` when the other side of `=` can only be one.
- **`b ∨ False` shows as `b && True`.** `earliestBefore`'s `Nil` case
  (`List.any []` is `False`) printed `⊢ (earliest < k) = (earliest < k &&
  True)`. On a scratch file, `theorem t (b: Bool): b = (b ∨ False) := ?`
  shows `⊢ b = (b && True)`. True, but it reads as a typo for `||`.
  Speculation, not checked: `b || c` computes to an `if`, and the printer
  folds `if b then c else False` back into `&&`.
- **`Decidable.toBoolOfNot _` with the procedure left as `_`.** For
  `((List.length (drawn ++ rest) < List.length drawn): Bool) = False`,
  `Decidable.toBoolOfNot _ (after => omega [after, List.lengthAppend
  drawn rest])` failed in `omega`, whose facts didn't include `after`;
  with `after` annotated it was `E-TYPE-MISMATCH`, "expected `(… < …) =
  False`, but this has type `Decidable.toBool (?48 drawn rest someDrawn
  board) = False`": the procedure wasn't solved from the expected type.
  A lemma, `pastTheEnd (n m: Nat): ((n + m < n): Bool) = False := cases`,
  and `rewrite List.lengthAppend` replaced it.
- **A calc step's note shows lambdas applied, not reduced.** With rows
  only in `Board.lines`, the note read `the line says
  Std.Bool.ifThenElse ((x x1 => …) (List.length …) (List.length drawn))
  (_ => True) (_ => List.any … …) = (x x1 => … < …) (winningTurn …) …`
  where the source says `… < …`. The counterexample under it was right,
  and was what mattered.

### 4. Inference

- **A record literal inside `Parse.all`'s lambda, and the error a line
  later.** `let game := Parse.all input (() => … { draws, boards })`,
  then `game.boards.withIndex.find …`, was `E-UNSOLVED`, "can't work out
  an implicit argument", pointing at the whole `game.boards.withIndex.find
  (…)` call on the next line. The literal's type wasn't known where
  `.boards` needed it. `let game: Game := …` fixed it. A note naming the
  record literal that is waiting would have pointed straight at it.

### 5. Performance

Nothing to report: `stitchwort check --no-cache` of the proofs and tests
takes 1.2 s.

### 6. Proofs, and the lemma search

`stitchwort search --rewrite` found the std lemmas the proofs use:
`List.anyAppend`, `List.anyMap`, `List.anyCong`, `List.allCong`,
`List.filterOfMap`, `List.mapMap`, `List.filterAll`, `List.filterCongMem`,
`List.appendAssoc`, `List.lengthSnoc` and `List.lengthAppend`. None was
written again. Rewriting inside a function argument worked again:
`rewrite onTurn game.draws _ game.boards in rfl` rewrote under `flatMap`'s
lambda, with `_` for the turn. What didn't work:

- `search --at` on the project's proof file is `E-FILE-MODE`, as on day 3.
  Six goals copied into scratch files with std types: two were
  `E-SEARCH-AT`, "its statement doesn't elaborate on its own" (`(latest <
  k) = (latest < k && True)` and `(n + m < n) = False`: the goal as
  printed has a comparison where a `Bool` is meant, item 3). For `(j ≤ t
  ∧ t < Succ j) = (t == j)` and a fold step it listed only rewrites
  (`Std.Float.Theory.andSwap` among them, a `Bool` lemma living in
  `Float.Theory`), and `cases` closes both. For `filterFilter` it found
  nothing, rightly; for `drawOn` it offered `List.getOrAppendRight` and
  `List.getOrOfGet` as next steps. It closed none of the six. Every run
  warned "3 comparisons ran out of steps", as on day 3.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day04` | 0.84 s user (0.88 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day04.Proofs Aoc.Year2021.Day04.Tests` | 1.16 s user (1.2 s) |
| `stitchwort run Aoc.Year2021.Day04.main` on the input (100 boards) | 0.35 s user (0.42 s), warm |
| `stitchwort audit Aoc.Year2021.Day04` (with the search) | 3.8 s user (3.9 s) |

81 lines of program, 57 of spec, 143 of proofs, 78 of tests.

### Ranked

1. A comparison next to a `Bool` connective in a statement makes the
   equation one between propositions, and `E-NOT-A-TYPE` doesn't suggest
   `((…): Bool)`; goals printed in that form can't then be pasted into
   `search --at` (items 3 and 6). Fix: elaborate the comparison as a
   `Bool` when the other side of `=` is one, or suggest the ascription.
2. No `List.filterFilter`, nothing tying `contains` to `indexOf`, no
   lemmas for folds of `max` and `min` (item 2). Fix: add them to std.
3. `search --at` still doesn't work in a project's files, doesn't try
   `cases`, and closed none of six goals here (item 6). Fix: the next
   stage of SW-915's search, and `cases` among its closers.
4. A waiting record literal's `E-UNSOLVED` lands on a later line (item 4).
   Fix: name the literal.
5. Goal printing: `b ∨ False` as `b && True`; lambdas left applied in a
   calc step's note (item 3).
6. `Decidable.toBoolOfNot _`'s procedure isn't solved from the expected
   type (item 3).

## Day 5: Hydrothermal Venture

Each line of the input is a line of vents, `x1,y1 -> x2,y2`, which covers
the grid points from one end to the other, both included. Every line is
horizontal, vertical or diagonal at exactly 45 degrees. Part 1 takes only
the horizontal and vertical lines and counts the points where at least two
of them overlap; part 2 counts the same with every line. Answers on Matt's
input (500 lines on a grid about 1000 by 1000): 8060 and 21577 (his Scala
solution's); the puzzle's example gives 5 and 12. Compiler built from
`main` at a093f9e9, 31 October 2026.

### The program

A line's points are `List.range (steps + 1)` mapped to the point `step`
steps along, where `steps` is the larger of the line's two extents and
`towards start stop step` moves one coordinate a step at a time (up, down,
or not at all). Then:

```stitchwort
def overlaps (lines: List Line): Nat :=
  Map.counts (lines.flatMap Line.points) |> .filter (_ times => 2 ≤ times) |> .size
```

with part 1 `overlaps (lines.filter Line.isStraight)` and part 2
`overlaps lines`. The parser is `Parse.eachLine` with `nat`, `char ','`
and `text " -> "`, and it rejects a line at any other angle ("line 1 isn't
horizontal, vertical or diagonal"). Both answers were right on the first
run; all 20 tests passed on the first run.

**What the spec decides.** The spec (`Spec/Spec.sw`) says which points a
line covers as geometry, not as a recipe: a point is on the segment when
it is within the rectangle the two ends span and its distances across and
down from the first end are in the segment's proportion,

```stitchwort
between line.x1 x line.x2 ∧ between line.y1 y line.y2
  ∧ Nat.absDiff line.x1 x * Nat.absDiff line.y1 line.y2 == Nat.absDiff line.y1 y * Nat.absDiff line.x1 line.x2
```

which holds for a segment at any angle. "The number of points where at
least two lines overlap" is the size of a set, so the spec says it with a
list: `NumberOfPoints n wanted` is that some list of points without
repeats has exactly the points `p` with `wanted p`, and `n` elements. A
test checks the spec against the program point by point on seven lines
over an 11 by 11 grid, and that the spec gives a 30-degree line its grid
points ((0, 0), (2, 1), (4, 2)), which the program's step-at-a-time
listing wouldn't.

### Proved, for every input

In `Aoc.Year2021.Day05.Proofs` (`Proofs/Proofs.sw`, 270 lines):

- `part1Correct`: for every list of lines, `solvePart1 lines` is the
  number of points where at least two of the horizontal and vertical
  lines overlap (`Part1Answer lines (solvePart1 lines)`). No hypothesis.
- `part2Correct`: for every list of lines in which every line is
  horizontal (`y1 = y2`), vertical (`x1 = x2`) or diagonal at 45 degrees
  (`|x1 - x2| = |y1 - y2|`), stated as `lines.all (line =>
  horizontalOrVertical line ∨ diagonal line) = True`, `solvePart2 lines` is
  the number of points where at least two lines overlap. The hypothesis is
  needed: on `0,0 -> 4,2` the program lists (0, 0) to (4, 4) along the
  diagonal, which mostly aren't on the line, and misses (2, 1) and (4, 2)
  (a test checks this). The puzzle promises it, and the
  parser checks it: `parseLinesShapes` proves every line of a successful
  parse satisfies it, and `part2FromInput` gives part 2 for the parsed
  input with no hypothesis (see "Parser guarantees" below).
- `numberOfPointsUnique`: two lists that witness `NumberOfPoints` for the
  same points have the same length, so the spec names one number
  (`List.permOfSameMembers` and `List.permLength`).
- On the way: the map's keys with a count of at least 2 are exactly the
  points listed at least twice (`countedTwice`, from `Map.getOrCounts`,
  `Map.getFilter`, `Map.memKeys` and `Map.keysDistinct`); a horizontal,
  vertical or diagonal line lists a point once if it covers it and not at
  all otherwise (`pointsCount`); so all the lines' points list a point
  once per line covering it (`listedCoveredBy`). Under the shape
  hypothesis the spec's proportion is linear (`coversLinear`: on a
  horizontal or vertical line every point of the rectangle is on it, on a
  diagonal those as far across as down, cancelling the common factor with
  `Nat.mulSuccCancel`), and the line's `i`th point is `(x, y)` exactly
  when the line covers `(x, y)` and `i` is its distance from the first end
  (`pointLinear`, by the line's shape).
- The example's answers as `rfl` theorems (`examplePart1`,
  `examplePart2`, in `Tests/Examples.sw`).

Nothing is left unproved; the one hypothesis is part 2's, above; nothing is
opaque. `stitchwort audit Aoc.Year2021.Day05` (with the counterexample
search): `audited 40 theorems: 0 failed, 0 with warnings, 40 passed`. The
answers' theorems are "not applicable" to the search (their conclusions
are `∃`); the lemmas under them had none found in 5,000 to 10,000 cases.

Breaking the program breaks the proofs: `start + step` for `start - step`
in `towards` makes `towardsEq` fail with a counterexample (`a = 1`, `b =
0`); `1 ≤ times` for `2 ≤ times` in `overlaps` makes `overlapsCorrect`
fail.

### 1. Std.Parse: none

`eachLine`, `nat`, `char` and `text` read the input as written, and the
error for a bad number ("line 1, column 3: expected a number, got 'x'")
came out as the test guessed.

### 2. Missing std

- **No cancellation of a nonzero factor.** `stitchwort search '(?a: Nat) *
  ?c = ?b * ?c → _'` found nothing; grep found `Nat.mulSuccCancel` (`b *
  Succ m = v * Succ m → b = v`) and `Nat.mulCancelLeft` (`1 ≤ n`, on the
  left). The day proved the `Bool` form, `productDiagonal: d ≠ 0 → (ax * d
  == ay * d) = (ax == ay)`. Std candidates: `Nat.mulRightCancel` with `c ≠
  0`, and that `Bool` form.
- **Counting one index of a range.** `count (range n) (i => c ∧ i == k) =
  toNat c` when `k < n` (`countRangeOnce`) took `List.countOccurrences`,
  `List.occurrencesOnce`, `List.distinctRangeFrom` and
  `List.memRangeFromIntro`. Std candidate: `List.countRangeEq: (List.range
  n).count (== k) = Bool.toNat (k < n)`.
- **No size of a set of points that isn't a `Set`.** The spec defines
  `NumberOfPoints` itself (a list without repeats with exactly those
  points). A std notion of "the number of `x` with `p x`" for a `p` true
  of finitely many, with the uniqueness lemma, would have saved the
  definition and `numberOfPointsUnique`.

### 3. Confusing errors

- **A tuple pattern as a `def` parameter.** `def covers (line: Line) ((x,
  y): Point): Bool` is `E-PARSE`, "expected a parameter's name, but found
  `(`". A theorem in equation style takes `| (x, y) =>`, and `let (x, y)
  := point` works in the body; the note could say so.
- **An argument on its own line, indented like the call.** In
  `pointStep`, `Eq.trans (Pair.mkBeqMk …)` then `(Eq.trans …)` on the next
  line at the same indentation gave `E-TYPE-MISMATCH` on the second line,
  as if it were the whole proof, and only after it `W-NO-EFFECT`, "this
  line does nothing … it's a function missing its arguments", on the first.
  The warning was the real cause. Reporting it first, or noting in the
  error that the line before is a call missing its arguments, would point
  at it.
- **`cases` doesn't use implications.** With `hx: bx = True → ax ≤ d` in
  scope, `cases` split `bx` but didn't apply `hx` in the case `bx = True`,
  and couldn't close it ("goal: False = True"). Matching on `bx` by hand
  and writing `let fx := hx rfl` in that case fixed it (`combineDiagonal`).
- `if h: x1 = x2` with proofs as branches was `E-UNIVERSE`, whose note
  gave the fix (`match Nat.decEq x1 x2 with | Yes h => … | No h => …`).

### 4. Inference

- `combineHorizontal _ _ i _ rfl …`, with the `Bool` `e` left `_` and its
  proof `e = True` given as `rfl`, was `E-UNSOLVED` at the `_`: `rfl` was
  checked before the goal fixed `e`. Stating the lemma with `True` in
  place of `e` (the goal computes to it) avoided it.

### 5. Performance

`stitchwort run Aoc.Year2021.Day05.main` on the input takes 3.0 s (2.9 s
user): `Map.counts` over all the lines' points. `check --no-cache` of the
proofs and tests takes 2.1 s, and the audit with the search 2.4 s.

### 6. Proofs, and the lemma search

`stitchwort search` found `List.countFlatMap`, `List.countAppend`,
`List.countMap` and `List.countCongMem`, and `search --rewrite
'((_, _) == (_, _))'` found `Pair.mkBeqMk`, which the proof needed because
`==` on pairs computes to `Pair.decMk …`, not to a conjunction. The `Map`
and `Distinct` lemmas were found by grep. `cases` did most of the
arithmetic: `towardsEq` (one coordinate, four `Nat`s, three `if`s, `min`,
`max` and `absDiff`) closed with one `cases`. Both coordinates at once
went over the 64-case budget (21 splits), so the proof splits by the
line's shape (`match Nat.decEq x1 x2`, then `y1 y2`) and combines the
coordinates with lemmas over abstract `Bool`s (`combineVertical`,
`combineHorizontal`, `combineDiagonal`).

- `search --at` on the project's proof file is `E-IMPORT-UNKNOWN` (it
  reads the file on its own, as on days 3 and 4). In a scratch copy of the
  lemmas it was `E-SEARCH-AT` at the goal `i ≤ Nat.absDiff y1 y2`: inside
  `match Nat.decEq x1 x2`, the refined hypothesis `shape` leaves a
  shadowed `shape✝`, which can't be written ("E-PARSE: unexpected
  character `✝`"). It closed no goal this day.
- `rewrite <- (p => listedCoveredBy lines shapes p) in counted`, to
  rewrite under the spec's `(p: Point) → …` binder, was
  `E-REWRITE-NOTHING`; a small congruence lemma (`numberOfPointsCong`) did
  it.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day05.Proofs Aoc.Year2021.Day05.Tests` | 2.0 s user (2.1 s) |
| `stitchwort run Aoc.Year2021.Day05.main` on the input (500 lines) | 2.9 s user (3.0 s) |
| `stitchwort audit Aoc.Year2021.Day05` (with the search) | 2.3 s user (2.4 s) |

76 lines of program, 62 of spec, 270 of proofs, 75 of tests.

### Ranked

1. `search --at` can't be used in a project's files, and in a scratch file
   a `match` on a decision leaves shadowed hypotheses (`shape✝`) that make
   the goal unwritable (item 6). Fix: project files (in progress
   elsewhere), and skip or rename shadowed hypotheses.
2. `cases` doesn't apply implication hypotheses (`b = True → fact`) in the
   case that makes their premise hold (item 3). Fix: in each case, apply
   such hypotheses whose premise the case fixed.
3. No `Nat` cancellation by a nonzero factor, no count of one index of a
   range, no "number of points with `p`" notion (item 2). Fix: add them to
   std.
4. An argument on the next line at the call's indentation reads as a new
   statement; the error lands on the argument, the real clue is a warning
   after it (item 3). Fix: report the warning first, or mention it in the
   error.
5. Tuple patterns aren't allowed as `def` parameters, and the parse error
   doesn't suggest `let (x, y) := …` (item 3).
6. A proof argument (`rfl`) is checked before a later `_` it depends on is
   solved from the goal (item 4).

## Day 6: Lanternfish

Each fish has a timer. Every day each timer goes down by one, except that
a fish at 0 goes back to 6 and spawns a new fish with a timer of 8. The
input is the starting timers, separated by commas. Part 1 counts the fish
after 80 days, part 2 after 256. Answers on Matt's input (300 fish): 380243
and 1708791884591 (his Scala solution's); the puzzle's example gives 5934
and 26984457539. Compiler built from `main` at 27a6367d, 31 October 2026.

### The program

Fish with the same timer behave alike, so the program keeps only how many
fish have each timer, a record of nine counts (`Counts`, fields `t0` to
`t8`), and moves them along a day at a time:

```stitchwort
def Counts.nextDay (counts: Counts): Counts := {
  t0 = counts.t1, …, t5 = counts.t6,
  t6 = counts.t7 + counts.t0,
  t7 = counts.t8,
  t8 = counts.t0
}

def fishAfter (days: Nat) (timers: List Nat): Nat :=
  Nat.iterate days Counts.nextDay (Counts.ofTimers timers) |> .total
```

`Counts.ofTimers` counts the timers equal to each of 0 to 8. The parser is
`Parse.line` with `sepBy1 nat (char ',')`, and it rejects a timer above 8
("timer 2 is above 8"). Both answers were right on the first run. One of
the 15 tests was wrong on the first run (it had a new fish spawn a day
late); the program was right.

**What the spec decides.** The spec (`Spec/Spec.sw`) is the puzzle's list
of every fish: a day maps each timer to the next (`nextTimer`: down by one,
or 0 to 6) and adds a fish at 8 at the end for each fish that was at 0, so
the example's lists come out in the puzzle's order (`2,3,2,0,1`, then
`1,2,1,6,0,8`, then 26 fish after 18 days, all checked by tests). The
answer is that list's length after `days` days (`fishCount`). After 256
days on the real input that list would have about 1.7 trillion elements,
so only the proof can connect the two there.

### Proved, for every input

In `Aoc.Year2021.Day06.Proofs` (`Proofs/Proofs.sw`, 143 lines):

- `fishAfterCorrect`: for every number of days and every list of timers
  in which every timer is at most 8 (`fish.all (t => t ≤ 8) = True`),
  `fishAfter days fish = fishCount days fish`: the program's count is the
  length of the puzzle's list of every fish.
- `part1Correct` and `part2Correct`: the same for 80 and 256 days, so
  `solvePart1` and `solvePart2` are the puzzle's answers for every such
  input.
- The hypothesis is needed: a fish at 9 has no count, so `fishAfter 0 [9]`
  is 0 where the puzzle's list has one fish. The puzzle's fish never start
  above 8 (the input's are 1 to 5), and the parser rejects one above 8;
  `parseTimersBounded` proves every timer of a successful parse is at
  most 8, so `part1FromInput` and `part2FromInput` need no hypothesis
  (see "Parser guarantees" below).
- On the way: a day keeps every timer at most 8 (`nextDayBounded`); the
  counts of the puzzle's list the next day are the program's next day of
  today's counts (`countsNextDay`, timer by timer through the generated
  `Counts.ext`: a fish is at `v` the next day if it was at `v + 1`, at 7
  or 0 for `v = 6`, plus the new fish for `v = 8`); so after any number
  of days the program's counts are those of the puzzle's list
  (`iterateCounts`, by induction on the days); and the counts add up to
  the list's length (`totalCounts`, using that a timer of at most 8 is one
  of 0 to 8, `oneTimer`).
- The example after 18 and 80 days as `rfl` theorems (`exampleAfter18`,
  `examplePart1`, in `Tests/Examples.sw`).

Nothing is left unproved; the one hypothesis is above; nothing is opaque.
`stitchwort audit Aoc.Year2021.Day06` (with the counterexample search):
`audited 21 theorems: 0 failed, 0 with warnings, 21 passed`. The search is
"not applicable" to most lemmas, because they take `Bounded fish`, a
`List.All` proposition nothing decides, and to `part1Correct` and
`part2Correct` (their normal forms are too large); `fishAfterCorrect`, with
the `Bool` hypothesis, had none found in 2,651 cases.

Breaking the program breaks the proofs: `t6 = counts.t7` for `t6 =
counts.t7 + counts.t0` in `Counts.nextDay` makes `countsNextDay` fail
(`E-OMEGA` at the `v = 6` field).

### 1. Std.Parse: none

`Parse.line` with `sepBy1 nat (() => char ',')` read the line, and the
errors came out as the tests guessed.

### 2. Missing std

- **Counting copies.** `List.count (List.replicate n x) p = n *
  Bool.toNat (p x)` (`countReplicate`) isn't in std. Std candidate.
- **Counting by a predicate that is two others.** If at every element
  `Bool.toNat (p t) = Bool.toNat (q t) + Bool.toNat (r t)`, then `count xs
  p = count xs q + count xs r` (`countSum`). Std candidate.
- **A simulation through `Nat.iterate`.** `iterateCounts` is the general
  fact that if `f (h x) = g (f x)` for every `x` in an invariant `I` that
  `h` keeps, then `Nat.iterate n g (f x) = f (Nat.iterate n h x)`. Std
  candidate (`Nat.iterateCommute`); here it was four lines.

### 3. Confusing errors

- **A tuple for `And`.** `Both rfl rest` builds `List.All p (Cons x xs)`;
  `(rfl, rest)` is `E-CANNOT-INFER`, "can't work out what `rfl` proves
  here … add a type annotation", though the expected type (an `And`) was
  known. The note could say that an `And` is built with `Both`.
- **`omega` shows what it was given unfolded.** Its facts and atoms print
  `List.count fish (== 7)` as `List.foldLeft fish 0 (n x => Nat.succIf n
  (Std.Decidable.toBool (Nat.decEq x 7)))`, so a failing `omega` over nine
  counts is hard to read. Printing the atoms as written would help.

### 4. Inference: none

`Counts.ext _ _` with the two records given and the nine field equations
by `omega` checked as written, the record fields of `Counts.ofTimers` and
`Counts.nextDay` computed by projection.

### 5. Performance

`stitchwort run Aoc.Year2021.Day06.main` on the input takes 0.24 s (0.19 s
user). `check --no-cache` of the proofs and tests takes 0.9 s, and the
audit with the search 1.6 s.

### 6. Proofs, and the lemma search

- **`cases` can't close "x ≤ 8, so x is one of 0 to 8".** `oneTimer`
  (`Bool.toNat (x == 0) + … + Bool.toNat (x == 8) = 1` given `x ≤ 8`) was
  `E-CASES-BUDGET`: it split all nine `Nat.decEq x k`, and the open case
  it showed had `Nat.decEq x 0 = Yes` and `Nat.decEq x 1 = Yes` together,
  which it didn't see as contradictory. A `match` on `x` with patterns
  `0` to `8` did it, but a last case `_ => omega` failed: the wildcard
  doesn't tell `omega` that `x ≥ 9`. The last case had to be written
  `Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ above))))))))`.
- `cases` did the rest of the per-timer facts in one word each:
  `nextTimer t == v` is `t == v + 1` when `v ≠ 6`, the three-way split at
  6, and `nextTimer t ≤ 8`.
- `stitchwort search '(_: Counts) = _'` found the compiler-made
  `Counts.ext`, after I had written the same lemma by hand (`countsMk`,
  over 18 `Nat`s); it replaced it.
- **`search --at` now works in a project's file.** At the `?` in
  `agedSix` it gave the closing proof, `countSum … cases fish`, checked by
  the kernel. At `noneAtNine` it listed `List.countNone fish (== 9) ?` first
  among those that apply, leaving `(x: Nat) → x ∈ fish → (x == 9) = False`,
  which is how the proof goes. It also listed lemmas from other days'
  proofs (`Aoc.Year2024.Day08.Proofs.natMulSelfZero`) and warned that 8
  comparisons with `Std.Float.Theory` lemmas ran out of steps: noise, but
  harmless.
## Day 7: The Treachery of Whales

The input is one line of crab positions, comma-separated. The crabs all
move to one position, each paying fuel for its own distance, and the answer
is the least total fuel. In part 1 a step costs 1; in part 2 a crab's `n`th
step costs `n`, so `n` steps cost 1 + 2 + … + n. Answers on Matt's input
(1000 crabs between 0 and 1986): 340052 and 92948968 (his Scala
solution's); the puzzle's example gives 37 (at position 2) and 168 (at 5).
Compiler built from `main` at 27a6367d, 31 October 2026.

### The program

A scan: every position from the leftmost crab to the rightmost, keeping the
least total.

```stitchwort
def leastFuel (fuel: Nat → Nat) (crabs: List Nat): Nat :=
  match List.between (leftmost crabs) (rightmost crabs) |> .map (fuelAt fuel crabs) |> .minimum with
    | Some least => least
    | None => 0
```

`fuelAt fuel crabs position` is `crabs.sumBy (crab => fuel (Nat.absDiff
crab position))`; part 1's fuel is `steps`, part 2's `Nat.sumBetween 1
steps` (Gauss's closed form, in std). `rightmost` folds `Nat.max` from 0,
`leftmost` folds `Nat.min` from the rightmost, so with no crabs both are 0
and the answer is 0 with no special case. The parser is `Parse.all` with
`sepBy1 nat (() => char ',')`. Both answers were right on the first run,
and all 18 tests passed on the first run, including the three parse error
messages the tests guessed.

**What the spec decides.** The spec (`Spec/Spec.sw`) takes every `Nat` as a
candidate position, not just the crabs' range, and says "the least fuel" as
`LeastFuel fuel crabs answer`: some position costs `answer` in total, and
no position costs less. Distance is written with an `if` (not
`Nat.absDiff`), part 2's fuel as `(List.between 1 steps).sum`, and the
total as `crabs.map … |> .sum`, so each differs from the program's form and
the proofs bridge them. Negative positions are left out: a position left of
0 is further than 0 from every crab.

### Proved, for every input

In `Aoc.Year2021.Day07.Proofs` (`Proofs/Proofs.sw`, 121 lines), with no
hypotheses (so D2108's parser theorem has nothing to cover):

- `part1Correct`: for every list of crabs, `solvePart1 crabs` is the least
  total fuel over every position, with a step costing 1
  (`Part1Answer crabs (solvePart1 crabs)`).
- `part2Correct`: the same for part 2, with `n` steps costing 1 + … + n.
- `leastFuelUnique`: two numbers that are each the least total fuel are
  equal, so the spec names one number.
- On the way, for any fuel that never falls as the distance grows
  (`leastFuelMeetsSpec`, `programLeast`): every position costs at least as
  much as the nearest one in the scan, `min (max position lo) hi`, since it
  is at least as far from every crab (`scannedNoWorse`, one `omega` with
  `Nat.absDiff` unfolded by `rfl` equations); a sum is at most another when
  each term is, on the list's members (`sumByLeMember`); part 2's fuel
  never falls (`growingFuelMonotone`, through `Nat.leDivOfMulLe`).
- The example's answers as `rfl` theorems (`examplePart1`, `examplePart2`,
  in `Tests/Examples.sw`).

Nothing is left unproved; nothing is opaque. `stitchwort audit
Aoc.Year2021.Day07` (with the counterexample search): `audited 19 theorems:
0 failed, 0 with warnings, 19 passed`. Most lemmas take a fuel function, so
the search is "not applicable" to them; the rest had none found in 10,000
cases.

Breaking the program breaks the proofs: folding `Nat.min` for `Nat.max` in
`rightmost` makes `rightmostGe` fail with a counterexample;
`Nat.sumBetween 2 steps` for `1` makes `part2Correct` fail.

### 1. Std.Parse: none

`Parse.all` with `sepBy1` read the line and its final line break, and its
errors ("line 1, column 3: expected a number, got ','") were as guessed.

### 2. Missing std

- **`Nat.min` folds.** Std has `List.foldMaxGe` and `List.leFoldMax` for
  `Nat.max`, but for the minimum only the `Ord.min` ones
  (`List.foldMinLeStart`, `List.foldMinLeMember`). The day proved
  `foldMinLe` and `foldMinLeMember` for `Nat.min`. Std candidates.
- **A sum is at most another, termwise on the members.** `List.sumByLe`
  needs `g x ≤ f x` for every `x`, not only the list's. The day proved
  `sumByLeMember` (for `Nat → Nat`). Std candidate: `List.sumByLeMem` for
  any element type.
- **Division is monotone** (`a ≤ b → a / d ≤ b / d`), and so
  `Nat.sumBetween` in its upper bound: neither is in std;
  `growingFuelMonotone` did it with `Nat.leDivOfMulLe` and `Nat.divMulLe`.
- **`List.maximum`** has no lemmas (`List.minimum` has `minimumSome` and
  `minimumExists`), which is why the program folds `Nat.max` itself.

### 3. Confusing errors: none

The one error was mine (`(by omega)`, from Lean: `E-UNKNOWN-NAME`, "unknown
name `by`", clear enough). Proving `2 ≠ 0` for `Nat.divMulLe` took a grep
to find `Nat.succNotZero 1`.

### 4. Inference: none

### 5. Performance

`stitchwort run Aoc.Year2021.Day07.main` on the input takes 0.86 s (0.80 s
user): 1987 positions times 1000 crabs, twice. `check --no-cache` of the
proofs and tests takes 0.95 s, and the audit with the search 0.6 s.

### 6. Proofs, and the lemma search

Every proof checked on its first full try except the `by` slip. `search
--at` now works in the project's files (2 to 3 s a goal warm; the first
run, on a cold cache with the machine under load, took 71 s). Three goals:

- `distanceIs` (the spec's `if` distance is `Nat.absDiff`): "cases alone
  closes it". Used.
- `growingFuelMonotone`: nothing closed it, but its 6th "applicable"
  result, `Nat.leDivOfMulLe ((a + (a * a)) / 2) (b + (b * b)) 2 ?`, was
  the proof's first step; `omega` with four facts closed what it left.
- A `foldMaxGe` of my own: its first "applicable" result named std's
  `List.leFoldMax`, which led to `List.foldMaxGe`; both replaced my lemmas.

So it closed one goal of three, and each of the three proofs used what it
suggested. The pattern search `'?a ≤ ?b → ?a / ?c ≤ ?b / ?c'` took 52 s
(cold cache) and found nothing relevant (std has no such lemma).

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day06.Proofs Aoc.Year2021.Day06.Tests` | 0.8 s user (0.9 s) |
| `stitchwort run Aoc.Year2021.Day06.main` on the input (300 fish) | 0.19 s user (0.24 s) |
| `stitchwort audit --no-cache Aoc.Year2021.Day06` (with the search) | 1.5 s user (1.6 s) |

74 lines of program, 22 of spec, 143 of proofs, 44 of tests.

### Ranked

1. `cases` doesn't see that `x == 0` and `x == 1` can't both hold, so
   "`x ≤ 8` means `x` is 0 to 8" goes over the budget, and a `match` with
   literal patterns gives its wildcard no `x ≥ 9` for `omega` (item 6).
   Fix: substitute `x = k` after a `Yes` split, and give a wildcard after
   literal patterns the fact that it is above them.
2. `omega`'s messages print counts and `==` unfolded (item 3). Fix: print
   atoms as written.
3. No `List.countReplicate`, no count by a sum of predicates, no
   `Nat.iterate` simulation lemma (item 2). Fix: add them to std.
4. `(proof, proof)` for an `And` gives a "type annotation" note instead of
   naming `Both` (item 3).
5. `search --at` lists other days' lemmas and Float comparisons that ran
   out of steps (item 6). Fix: rank the project's other namespaces lower,
   or leave out unimported ones.
| `stitchwort check --no-cache Aoc.Year2021.Day07.Proofs Aoc.Year2021.Day07.Tests` | 0.90 s user (0.95 s) |
| `stitchwort run Aoc.Year2021.Day07.main` on the input (1000 crabs) | 0.80 s user (0.86 s) |
| `stitchwort audit Aoc.Year2021.Day07` (with the search) | 0.53 s user (0.59 s) |

58 lines of program, 44 of spec, 121 of proofs, 51 of tests.

### Ranked

1. No `Nat.min` fold lemmas to match the `Nat.max` ones, no membership
   form of `List.sumByLe`, no `List.maximum` lemmas, no monotone division
   (item 2). Fix: add them to std.
2. A first `search` or `search --at` on a cold cache is slow (52 s and
   71 s, under load); warm, 2 to 3 s (item 6).
3. `Nat.divMulLe` takes `d ≠ 0` explicitly, where `Nat.leDivOfMulLe` takes
   it as `[auto]`; a literal `2` needed `Nat.succNotZero 1`, found by grep
   (item 3). Fix: make it `[auto]` there too.


## Day 8: Seven Segment Search

Each line of the input is one seven-segment display whose signal wires
are connected to the segments in a scrambled order: the patterns of wires
lit by its ten digits, in no order, then the four patterns of its output.
Part 1 counts the output digits that are 1, 4, 7 or 8 (the digits whose
number of segments no other digit has); part 2 works out each display's
wiring, reads its four-digit output and adds the outputs up. Answers on
Matt's input (200 displays): 445 and 1043101 (his Scala solution's); the
puzzle's ten-line example gives 26 and 61229, and its single display reads
5353. Compiler: the installed release build, on `main` at d574a248, 31
October 2026.

### The program

A pattern is a record of seven `Bool`s, one per wire, so the order the
letters come in doesn't matter. The program never searches the 5040
wirings. It reads each pattern by a score that renaming the wires can't
change: for each wire the pattern has on, the number of the display's ten
patterns that have it on, added up.

```stitchwort
def score (patterns: List Pattern) (pattern: Pattern): Nat :=
  segments.sumBy (wire => if pattern.has wire then litIn patterns wire else 0)

def decodeDigit (patterns: List Pattern) (pattern: Pattern): Nat := digitScores.indexOf (score patterns pattern)
```

`digitScores` is the scores of the display as drawn (42 for 0, 17 for 1,
34, 39, 30, 37, 41, 25, 49, 45), computed from the drawing, and no two are
the same. Part 1 counts the outputs with 2, 3, 4 or 7 wires on. Part 2
reads each output's digits in base 10 and adds the values.

The parser (`Parse.eachLine` with `Parse.repeat 10 10` and `repeat 4 4`
of `takeWhile1` letters from a to g) also checks the puzzle's promise for
every display (D2108): from the digits read it works out the wiring
(`Entry.wiring`: wire `x` drives the segment that is on in the digits of
exactly the patterns with `x` on) and fails unless that wiring is a
permutation of the segments (its seven segments, sorted, are A to G), the
ten patterns read as 0 to 9 once each (sorted, they are `List.range 10`),
and every pattern, outputs too, has exactly the wires on that drive its
digit's segments (`Entry.wired`). Both answers were right on the first
run, and every test passed on its first run except one placeholder
written to learn an error message.

**What the spec decides.** The spec (`Spec/Spec.sw`) is the puzzle's
picture: `digitSegments` lists each digit's segments as drawn; a wiring is
any function from wires to segments that is a permutation (`IsWiring
wiring := List.Perm (segments.map wiring) segments`); a pattern shows a
digit under it when each wire is on exactly when the segment it drives is
one the digit lights (`Shows`); a wiring decodes a display when the ten
patterns show the ten digits, each once (`List.Perm (patterns.map (shown
wiring)) (digits.map Some)`), and each output shows a digit
(`Decodes`). The answers read the outputs through a decoding wiring
chosen for each display (`Part1Answer`, `Part2Answer`, an `∃` over the
choice). The puzzle promises exactly one decoding wiring per display; the
spec needs only one, since any two give the same answers (proved).

### Proved, for every input

In `Aoc.Year2021.Day08.Proofs` (`Proofs/Facts.sw`, `Proofs.sw`,
`Parse.sw`, 324 lines):

- `part1FromInput` and `part2FromInput`: if `parseEntries` reads `input`
  as `entries` (`Fail.toResult (() => parseEntries input) = Ok
  entries`), then `Part1Answer entries (solvePart1 entries)` and
  `Part2Answer entries (solvePart2 entries)`. No other hypothesis: the
  wiring each display needs is the one the parser checked
  (`parsedDecode`, from `wiredDecodes`: an entry that passes the check is
  decoded by its own wiring).
- `part1Correct` and `part2Correct`: for every list of displays and every
  choice `wiringOf` of a wiring for each, if `wiringOf entry` decodes
  `entry` for every `entry` in the list, `solvePart1 entries` is the sum
  of each display's 1s, 4s, 7s and 8s read through it, and `solvePart2
  entries` the sum of its output values read through it.
- `part1AnswerUnique`, `part2AnswerUnique`, `decodedValueUnique`: the
  answers don't depend on which decoding wirings are chosen.
- On the way: under a decoding wiring, the number of patterns with a wire
  on is the number of digits lighting the segment it drives (`litDrawn`,
  through the `Perm` of the digits shown), so a pattern's score is the
  drawn score of the digit it shows (`scoreDrawn`, reindexing the sum
  over the wires by the permutation, `sumRewired`), which reads back as
  that digit (`decodeDrawn`); a pattern's size is its digit's number of
  segments (`sizeDrawn`); under a wiring a pattern shows at most one
  digit (`sameDigit`, as no two digits light the same segments). The
  facts about the drawing (`displayDrawn`, `decodeDrawn`, `digitsDiffer`,
  `easyDrawn`) are each a `Bool` over the ten digits, by `rfl`.
- Tests: both examples, the single display's digits and wiring as the
  puzzle draws them, the spec on that display (each pattern shows its
  digit, it reads 5353), and the parser's errors.

Nothing is left unproved, and no hypothesis was added beyond the parse.
One definition is opaque: `Entry.wiring`, the wiring the parser works
out. The proofs need only its name, because `Entry.wired` checks
everything they use of it. Transparent, its body (a `find` over the
decoded patterns) was computed on an unknown entry: checking
`Proofs/Parse.sw` ran past two minutes, and 19 s for a `match` with two
`?` arms. Opaque, the whole day checks in 7 s cold.
`stitchwort audit Aoc.Year2021.Day08` (with the counterexample search):
`audited 39 theorems: 0 failed, 0 with warnings, 39 passed`. The search
is "not applicable" to most theorems (a wiring is a function); `notNone`
gave up because its hypotheses contradict each other, which is its point.

Breaking the program breaks the proofs: `else 1` for `else 0` in `score`
makes `decodeDrawn`'s `rfl` and a `scoreDrawn` `calc` step fail; dropping
the wiring's sort check from `Entry.wired` makes `wiredDecodes` fail.

### 1. Std.Parse: none

`repeat 10 10`, `takeWhile1` and `text "| "` read the lines as written. A
letter past g gives "expected ' '" at the letter (the pattern stops before
it), not "expected a letter from a to g"; fine for this input.

### 2. Missing std

- **`all` of a mapped list.** `List.all (xs.map f) q = List.all xs (x =>
  q (f x))` (`allMapped`): `stitchwort search 'List.all (List.map _ _) _
  = _'` finds only project lemmas. Std has the `count`, `sumBy` and
  `List.All` forms. Std candidate.
- **A member of a `Bool` `all`.** `xs.all p = True → x ∈ xs → p x =
  True` (`allElim`) takes `List.allToAll` then `List.allMem`. Std
  candidate.
- **Reindexing by a permutation.** For `List.Perm (xs.map f) xs`, the
  count, sum and `all` over `xs` of `h ∘ f` are those of `h`
  (`countRewired`, `sumRewired`, `allRewired`): two lines each from
  `countMap`/`sumByMap` and `countPerm`/`sumByPerm`. Std candidates.
- **`find` over `withIndex` found nothing** (`findIndexedNone`), now on
  days 5, 6 and 8. Std candidate.

### 3. Confusing errors

- **`_` for a `Perm`'s lists.** `List.memPerm _ _ perm …` and
  `List.countPerm _ _ wired h` were `E-TYPE-MISMATCH`: the expected type
  showed `List.Perm` unfolded to its `occurrences` equation, with the
  right-hand list already computed (`digits.map Some` as a sum of ten
  `Bool.toNat (p (Some k))`), so unification couldn't recover the list.
  Writing the lists out fixed it. The note could say to give them.
- **`_` for a `Bool` predicate.** `eachDigit _ all digit below`, with `all:
  digits.all (d => …) = True`, was `E-TYPE-MISMATCH` against `?9 digit
  below segment`: the predicate isn't found from the argument. Naming it
  with `let q := …` fixed it.
- **`rewrite … at (term) in`** needs a name (`E-REWRITE-TARGET`); the note
  says so.

### 4. Inference: none beyond the two above

### 5. Performance

`stitchwort run Aoc.Year2021.Day08.main` on the input takes 0.39 s (0.34
s user). `check --no-cache` of the proofs and tests takes 7.1 s, and the
audit with the search 8.9 s cold. Two traps:

- `rewrite e1, e2, <- part1Correct …` in `part1AnswerUnique` was
  `E-REWRITE-BUDGET`: the rule's sides compute to the whole decoding. An
  `Eq.trans` chain did it at once.
- `Entry.wiring` transparent (above, under "Proved").

### 6. Proofs, and the lemma search

Most lemmas checked as first written; the fixes were the `_`s and
rewrites above. `search --at` closed nothing this day. At
`countRewired`'s goal (`List.count segments (wire => h (wiring wire)) =
List.count segments h`, with `wired: IsWiring wiring` in scope) it took 44
s and offered only `List.countCongMem`, leaving `h (wiring x) = h x`,
which is false; the proof is `List.countMap` then `List.countPerm`. At
`hasDrawn` (one wire of a `Bool` `all`) it found nothing in 7.5 s; the
proof is `List.allToAll` then `List.allMem`. Both warned about `Float`
comparisons that ran out of steps. Grep and `stitchwort search` by
pattern found std's `sumByPerm`, `countPerm`, `findRangeSome`,
`memMapElim` and `foldLeftCongMem`, which carried the proof.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day08.Proofs Aoc.Year2021.Day08.Tests` | 7.0 s user (7.1 s) |
| `stitchwort run Aoc.Year2021.Day08.main` on the input (200 displays) | 0.34 s user (0.39 s) |
| `stitchwort audit --no-cache Aoc.Year2021.Day08` (with the search) | 8.8 s user (8.9 s) |

162 lines of program, 79 of spec, 324 of proofs, 79 of tests.

### Ranked

1. A transparent definition computed on an unknown argument made a small
   proof file take minutes, with no message saying what was unfolding
   (item 5). Fix: report the definition being unfolded when a check runs
   long, as `E-RESOURCE` does.
2. `_` for a `List.Perm`'s lists or a `Bool` predicate doesn't infer
   (item 3). Fix: unify against the folded `Perm` before unfolding it, or
   say in the note to give the arguments.
3. `search --at` missed two two-lemma proofs, took 44 s on one, and its
   one suggestion left a false goal (item 6). Fix: don't list an
   applicable lemma whose leftover goal the counterexample search refutes.
4. No `List.all` of a map, no member of a `Bool` `all`, no reindexing by a
   permutation, no `find` over `withIndex` (item 2). Fix: add them to std.
5. `rewrite` with an equation whose sides compute to large terms runs out
   of budget (item 5); `Eq.trans` works. The note could suggest it.

## Day 9: Smoke Basin

The input is a height map of a cave floor, one digit per location. Part 1
finds the low points, the locations lower than every location up, down,
left and right of them, and adds up their heights plus 1. Part 2 finds
the basins, the areas that drain to each low point, walled in by 9s, and
multiplies the sizes of the three largest. Answers on Matt's input (100 by
100): 494 and 1048128 (his Scala solution's); the puzzle's 5 by 10
example gives 15 and 1134. Compiler: the installed release build, on
`main` at e2f43e35, 1 November 2026.

### The program

The map is `{ rows: List (List (Fin 10)) }`: `Parse.digit` gives a `Fin
10`, so "digits 0 to 9" is the type. `heightAt` reads a position with
`getOr`/`get`, `None` off the map, and `cells` is std's
`List.gridCells` with each position as a `Position` record. A low point
is a cell whose four `neighbours` (none above row 0 or left of column 0;
the ones past the far edges have no height) are all higher where they
have a height.

Part 2 uses std's breadth-first search, `Graph.breadthFirst`, as the
flood fill, on a graph whose edges step to the neighbours that aren't 9s
(`HeightMap.graph`). A basin's size is the size of the map the search
returns. The `Graph` record needs a `states` list that every edge leads
into, which is what makes the search end; here it is every cell's
position, and `edgesListed` (in the program's own `Steps.sw`) proves the
edges stay in it. A low point that is a 9 (only possible on a map of one
location) gets 0. The three largest sizes are `sort [ord := Ord.reverse]
|> .take 3 |> .product`.

The parser reads each line with `many1 digit` (`Parse.eachLine`) and then
checks (`checkRows`, a pure test `firstRagged`, as in the D2108 pattern)
that every row is as long as the first.

Both answers were right on the first run. The run took 3.0 s at first:
`HeightMap.graph` was built once per low point, and building it computes
its `states` list, all 10,000 positions, each time (about 2.3 s for 240
low points). Built once (`basinSizes`), the run takes 0.8 s.

**What the spec decides.** `Spec/Spec.sw` works over the program's map
(its `cells` and `heightAt`, as 2024's day 10 does) and says the rest in
the puzzle's words. Two locations are `adjacent` when they are one column
apart in a row or one row apart in a column. A low point is a cell lower
than every cell adjacent to it (`lowPoints`: every cell of the map is
compared, not four neighbours). Part 1 is the sum of `1 + height`. A
location is in the basin of a low point (`InBasin`) when it isn't a 9 and
some path of steps between adjacent locations that aren't 9s leads to it
from the low point (`isPath`): the low point's connected area of non-9
locations under orthogonal adjacency. `BasinSize map low n` says a list
of `n` positions, without repeats, holds exactly the basin's locations.
`Part2Answer` asks for a size for each low point's basin and the product
of the three largest.

The puzzle also promises that every location that isn't a 9 is in
exactly one basin. The spec states this as `EachInOneBasin` but the
theorems don't assume it: they are about each low point's basin, and the
promise is what makes the list of those the same as the list of the
connected areas. A test checks it on the example and on the input
(`eachInOneBasin`: the basins' locations cover every non-9 location, and
their sizes add up to the number of them), and another that a map with
two low points in one area breaks it.

### Proved, for every height map

In `Aoc.Year2021.Day09.Proofs` (`Proofs/Facts.sw`, `Part1.sw`,
`Part2.sw`, `Parse.sw`, 338 lines) and `Steps.sw`:

- `part1Correct`: for every `map`, `solvePart1 map = part1 map`. The
  program's test on four neighbours is the spec's test on every adjacent
  cell (`lowAgrees`): every neighbour is adjacent (`neighboursAdjacent`,
  four cases on whether the row and column are 0), every adjacent position
  is a neighbour (`adjacentNeighbour`), and a neighbour with no height
  doesn't count. So the program's low points are the spec's
  (`lowPointsAgree`).
- `part2Correct`: for every `map`, `Part2Answer map (solvePart2 map)`, with
  each low point's size the program's `basinSize`. No hypothesis.
- `basinSizeOpen`: for a low point that isn't a 9, the keys of the
  search's result are exactly its basin (`foundInBasin` and
  `inBasinFound`, from std's `Graph.breadthFirstShortest`: whatever the
  search settles is reached by a walk from the source, and whatever a walk
  reaches is settled). A walk in the graph is a spec path and back
  (`walkPath`, `pathWalk`), and a map's keys have no repeats
  (`Map.keysDistinct`). The termination of the flood fill is std's: each
  round settles a new state of the `states` list, or stops.
- `basinSizeClosed`: a low point that is a 9 has an empty basin, because
  any neighbour on the map would be a digit above 9.
- `parseRectangular`: if `parseHeightMap` reads `input` as `map`, every
  row of `map` is as long as the first. Heights are digits by their type
  (`heightBelow10`, used by `basinSizeClosed`). Neither is needed by the
  answers' theorems; they say what the parser promises.
- Tests: the example's low points, basins (3, 9, 14, 9) and answers, both
  ways for part 1; neighbours in a corner and inside; a map of one 9, a
  flat map, fewer than three basins; the parser's errors; the promise.

Nothing is left unproved, and no hypothesis was added. The puzzle's
promise (`EachInOneBasin`) is stated and tested, not proved: the theorems
don't need it, and proving it of the input would be a proof about the
input, not the program. No opaque definitions.
`stitchwort audit Aoc.Year2021.Day09` (with the counterexample search):
`audited 44 theorems: 0 failed, 0 with warnings, 44 passed`.

Breaking the program breaks the proofs: `height <= other` for `height <
other` in `isLowPoint` makes `lowerThanAdjacent` fail with a
counterexample (`map = { rows = [[0]] }`); `height != 8` for `height != 9`
in `isOpen` makes `edgeStep`, `stepEdge` and three more in `Part2.sw`
fail.

### 1. Std.Parse: none

`Parse.eachLine` with `many1 digit` read the input as written. A letter
in a row says "expected a digit or the end of the line, got 'x'", which
is right.

### 2. Missing std

- **A map's keys are as many as its size.** `List.length (Map.keys m) =
  Map.size m` took `List.lengthMap` and `Map.sizeToList`; `search --at`
  found neither (item 6). Std candidate, small.
- **`find` over `withIndex` found nothing** (`findIndexedNone`), now on
  days 5, 6, 8 and 9. Std candidate, small.
- **Grid neighbours.** Days 9 here and 10, 12, 16, 18 and 20 of 2024 each
  write their own up/left/right/down with their own adjacency lemmas
  (`neighboursAdjacent`, `adjacentNeighbour`: 60 lines here). A std
  `Grid` of `(row, column)` positions with `neighbours4` and the
  membership lemma would save each day that. Medium.
- **`not (a != b)` is `a = b`** (`sameOfNotDiffer`, and `nineOfClosed`
  for `(h != 9) = False`): `!=` is `Decidable.toBool (Decidable.not
  …)`, and no lemma turns it back into an equation. Std candidates
  (`DecEq.ofNotDiffer`, `DecEq.notOfDiffer`), small.

### 3. Confusing errors

- **`cases` on a `Bool` with `==` on variables** (`adjacent { row = Succ
  row, column } { row, column } = True := cases`) was `E-MATCH-MOTIVE`,
  "this `match` can't be given a type", with the kernel's reason "`rfl`
  can't prove this" and a note to write a top-level helper. There is no
  `match` in the source; the `cases` built it. The message could say
  `cases` couldn't split the goal, and what it tried. Small to medium.
- **`Decidable.toBoolSound` on a `Bool` `<`.** With `lower: (height <
  other) = True`, `Decidable.toBoolSound _ lower` was `E-TYPE-MISMATCH`:
  "expected `Decidable.toBool (?29 …) = True`, but this has type `height <
  other`". A `Bool` `<` on `Nat` is `Nat.leq (Succ a) b`, not
  `Decidable.toBool`, and `lower` already is the proposition (syntax.md
  says so, under "Anywhere a `Bool` is expected"). The message shows the
  `Bool` as `height < other`, the same text as the proposition, so it
  reads as a contradiction. A note saying "`a < b` as a `Bool` on `Nat` is
  `Nat.leq`; it is the proposition already" would fix it. Small.
- **`==` versus `Nat.equal`.** `Nat.equalRefl column` for `column ==
  column` was a mismatch: `==` is `Decidable.toBool (Nat.decEq …)`, and
  the lemmas are `DecEq.refl`, `DecEq.sound`. The mismatch showed both
  sides half-unified with holes, which didn't help. Small (a note when
  the expected side has `Nat.decEq` and the term `Nat.equal`).
- **Membership goals print unfolded.** A goal `next ∈ map.cells.map
  Pair.fst` printed as `List.Any (y => y = next) (List.map …)`; other
  goals kept `∈`. Small.
- **A pair is not its projections.** `lowAgrees map entry.fst entry.snd
  member` with `member: entry ∈ map.cells` was a mismatch against
  `(entry.fst, entry.snd) ∈ …` (no eta for pairs); a `match entry with
  | (position, height)` fixed it. The message could suggest it. Small.

### 4. Inference

- `List.memMap _ _ inGrid _`, with the function a hole, didn't infer
  against `(position, height) ∈ map.cells`: unification met the `map`'s
  lambda computed into projections. Writing the lambda out fixed it.

### 5. Performance

`stitchwort run Aoc.Year2021.Day09.main` on the input takes 0.8 s (0.77 s
user). `check --no-cache` of the proofs and tests takes 3.1 s. One trap:

- **A `Graph` record computes its `states` at run time.** The `states`
  list only serves termination, but building the record builds it: a
  helper that made the graph per low point spent 2.3 s of a 3.0 s run
  making the list of all 10,000 positions 240 times. Fix: build it once
  (done), or have std say so at `Graph`; better, erase fields used only
  in proofs. Small (doc) to large (erasure).

### 6. Proofs, and the lemma search

Every lemma checked within two or three tries; most fixes were the `==`
and `Bool` `<` forms (item 3) and `&&` grouping to the right (my
`Bool.andIntro` nesting assumed the left). `search --at` closed nothing
this day:

- At `memCellsOfHeight` (membership in `cells` from a height) and
  `heightOfMemCells` it took 41 s and 42 s, and offered only unrelated
  project lemmas (day 24's `lookupLastMem`, `List.lastMem`), with the
  namespace not checking or with other `?`s open. Both proofs needed
  `List.memGridCells`, which a `search` pattern would find but the goal
  doesn't mention.
- At `List.length (Map.keys r) = Map.size r` it took 2.3 s and found
  nothing, though `stitchwort search --rewrite 'Map.size _'` lists
  `Map.sizeToList` first. Fix: offer rewrites by equations about a
  function in the goal even when the result isn't closed. Medium.
- `stitchwort search '(a: Position) = b'` and `search 'Position.ext'
  --definitions` in the project were `E-AMBIGUOUS`: eleven days have a
  `Position`. With the full name, `--definitions` found 0 results for
  the generated `Position.ext` (it exists; syntax.md describes it). Fix:
  resolve names in a given namespace (`--in NS`), and index generated
  `T.ext`. Small each.

Std's `Graph.breadthFirstShortest` carried part 2: the flood fill's
termination and its "finds exactly what is reachable" came for free, and
the day's own part was relating the graph's walks to the spec's paths.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2021.Day09.Proofs Aoc.Year2021.Day09.Tests` | 3.1 s user (3.2 s) |
| `stitchwort run Aoc.Year2021.Day09.main` on the input (100 by 100) | 0.77 s user (0.83 s) |
| `stitchwort audit Aoc.Year2021.Day09` (with the search) | 4.5 s user (4.6 s) |

110 lines of program and 32 of its graph lemma, 71 of spec, 338 of proofs,
63 of tests.

### Ranked

1. A `Graph`'s `states`, needed only for termination, is computed every
   time the record is built (item 5): an innocent helper made the run 4
   times slower. Fix: document it at `Graph`, or erase proof-only data.
2. `cases` failed with `E-MATCH-MOTIVE` about a `match` the source doesn't
   have (item 3). Fix: report it as `cases`' failure.
3. `Bool` forms of `<`, `==` and `!=` each need different lemmas
   (`Nat.leq` is the proposition, `DecEq.sound`, `Decidable.toBoolSound`),
   and mismatches print the `Bool` and the proposition alike (item 3).
   Fix: a note naming the form and its lemma; `DecEq` lemmas for `!=`.
4. `search --at` took 41 s on goals in an unfinished namespace and found
   nothing in three goals, missing a rewrite `search --rewrite` lists
   first (item 6).
5. Every grid day writes its neighbours and their adjacency lemmas (item
   2). Fix: a std grid module.

## Day 10: Syntax Scoring

Each line is a string of brackets from four pairs. A line is corrupted
when a closer doesn't match the innermost bracket still open, and
incomplete when it isn't corrupted but leaves brackets open. Part 1 adds
up a score for each corrupted line's first wrong closer. Part 2 scores
the closers that would complete each incomplete line (times 5, plus the
closer's points, closer by closer) and takes the middle score. Answers on
Matt's input (94 lines): 364389 and 2870201088 (his Scala solution's);
the puzzle's 10-line example gives 26397 and 288957. Compiler: the
installed release build (main checkout, built 31 October 23:38), on
`main` at a937906d, 1 November 2026.

### The program

`Token` is `Opener Bracket` or `Closer Bracket`. One function, `scan`,
does both parts: it reads the tokens with a stack of the brackets still
open, innermost first, and ends as `Corrupted illegal` at the first
closer that doesn't match the top (or has nothing open), or as
`Unclosed open` with the stack. Read top first, the stack is the
completion. The middle score is `sort` at index `length / 2`. Both
answers were right on the first run.

The parser was first written by hand: `tokenOf` mapped the eight
characters to tokens, and each line was `withIndex.map` of `Fail.need
(tokenOf char) …`, because no lemma said what `many1`/`pick` read (item
1 below). Since SW-998 it is `Parse.eachLine input (() => many token)`,
with `token` a `label "a bracket"` of a `pick` from a table built from
`Token.char`, and `parseReadsLines` follows from std's lemmas on what
parsers read (`Std/Parse/Reads.sw`).

**The spec** (Spec/Spec.sw) has no stack. `Balanced` is a grammar
(inductive): empty, two balanced lines one after the other, or a
balanced line between an opener and its closer. A start of a line is
`Legal` if some ending makes it balanced. `FirstIllegal line token`:
`line = before ++ token :: after`, `before` is legal and `before ++
[token]` isn't. Part 1 (`Part1Answer`, inductive over the lines) adds
each line's `ErrorScore`: the points of its first illegal closer, or 0
for a legal line. A line is `Incomplete` if it is legal and not
balanced; `Completes line closers` if `line ++ closers` is balanced.
`CompletionScores lines scores` lists the incomplete lines' completion
scores in order (the formula is the puzzle's, `completionTotal`). The
middle (`Middle scores m`): `m` is a score, and at most half the scores
are below it and at most half above (`2 * count ≤ length`). That is
defined for any list; with an odd count it is the one middle element,
with an even count either of the two middle ones. `Part2Answer lines m`:
some `CompletionScores lines scores` with `Middle scores m`.

### Proved

In `Aoc.Year2021.Day10.Proofs` (Proofs/Scan.sw, Part1.sw, Part2.sw,
Middle.sw, Parse.sw, 494 lines):

- `part1Correct (lines)`: `Part1Answer lines (solvePart1 lines)`. No
  hypothesis.
- `part1Unique`: two `Part1Answer`s of the same lines are equal, so the
  spec's answer is a function of the lines, and the program's is it. It
  rests on `firstIllegalUnique` (a line has one first illegal character)
  and on corrupted and legal lines being disjoint.
- `part2Correct (lines) (line) (member: line ∈ lines) (incomplete:
  Incomplete line)`: `Part2Answer lines (solvePart2 lines)`. Hypothesis:
  at least one line is incomplete (with none, no number is a middle of
  the empty list).
- `part2Unique (lines) (a) (b) (odd: (scores: List Nat) →
  CompletionScores lines scores → scores.length % 2 = 1)`: two
  `Part2Answer`s are equal, when every list of the lines' completion
  scores has odd length (that list is unique, `completionScoresUnique`, so
  this says: an odd number of incomplete lines, the puzzle's promise). A
  test checks the promise on the input.
- The bridge between the stack and the grammar: `balancedScan` (a
  balanced piece leaves any stack as it was) and `scanBalanced` (a line
  whose scan from nothing open ends with nothing open is balanced; by
  induction over the line with the read tokens kept as balanced pieces
  between the open brackets, `framesBalanced`). From them: a start is
  legal exactly when the scan doesn't stop in it (`legalOfUnclosed`,
  `notCorruptedOfLegal`); the scan stops exactly at the first illegal
  character (`firstIllegalOfScan`, `scanOfFirstIllegal`); an opener is
  never illegal (`legalOpener`); every start of a legal start is legal
  (`legalOfLonger`); a line has at most one completion, the closed stack
  (`completionUnique`, `closersExact`).
- `middleIsMiddle`: the program's `middle` is a `Middle` of any nonempty
  list (sorted, at most k elements are below index k and at most n − 1 − k
  above); `middleUnique`: with an odd count, two middles are equal.
- `parseReadsLines`: if `parseLines` reads `input` as `lines`, then
  `lines.map (tokens => tokens.map Token.char) = input.lines.map
  Text.toList`: every character of every line was one of the eight
  brackets, read as its token, nothing dropped or added (D2108). The
  answers' theorems hold for every list of token lines, so they need
  nothing from it.
- Tests: the example's answers, first illegal closers, completion scores
  and one completion; a stray character, an empty line, a balanced line,
  a closer with nothing open; and four example theorems through the spec
  (`exampleIllegalCurly`, `exampleIllegalRound`, `exampleBalanced`,
  `exampleCompletion`).

Not proved: nothing left open. Hypotheses: `part2Correct` needs one
incomplete line, `part2Unique` an odd count, both stated above. No
opaque definitions. `stitchwort audit Aoc.Year2021.Day10` (with the
counterexample search): `audited 59 theorems: 0 failed, 0 with
warnings, 59 passed`. The search is "not applicable" to most of them
(`Legal` is an `exists`).

Breaking the program breaks the proofs: a closer with nothing open
skipped instead of corrupted makes `scanAppend`, `firstIllegalFrom` and
others fail (with a counterexample); `length / 3` for `length / 2` in
`middle` fails `middleIsMiddle` (counterexample); a wrong point
(`Round => 2`) fails `completionPointsAgree`; `']'` read as `Closer
Round` fails `tokenOfChar`.

Most proofs checked first time or second; the scan/grammar bridge took
about ten tries in all, mostly over list shapes (item 6).

**Completeness (SW-1626).** `Proofs/Complete.sw`, 70 lines, about 5 minutes
(the CLI was already built). Of the 2021 days' `Proofs/Parse.sw` files, only
this one and day 16's state what the parser read of the text (the others
prove properties of the parsed value: shapes, bounds, distinct rules, a
rectangle); so these were the two in scope. `runsToken` (8 arms, one per
token) is `Parse.runsLabel` over `Parse.runsPick`, with the earlier tokens'
characters as the `WordsAbsent` proof, `rfl` for each since they are literals;
`declinesTokenEnd` is `declinesPick` at the end; a line's rounds are
`tokenSteps`, one `([char], token)` per token, so `runsLine` is
`Parse.runsMany`, and `parseComplete` and `writtenUnique` follow as on 2020
day 2. The hypothesis is `parseReadsLines`'s conclusion (`lines.map (tokens =>
tokens.map Token.char) = input.lines.map Text.toList`) and the spec is tight
enough: a line's characters fix its tokens. Friction: a lemma parameter named
`token` hid the parser `token` (`E-TYPE-MISMATCH` pointing at the type, with
the right note); a `rewrite <- …` of the goal went wrong where rewriting the
`Runs` hypothesis with `rewrite … at runs` did not. Dropping the first token
from the parser's table fails `runsToken`.

### 1. Std.Parse can't be reasoned about

The natural parser, `Parse.eachLine input (() => many1 (() => pick
tokenTable))`, gave the right answers, but proving it reads exactly the
line's characters needs lemmas about `many1` (`manyFuel`, marks),
`pick` and `eachLine`, and std has only the handler steps
(`runFromPure`, …). Workaround: the parser by hand with `Fail.need` over
`withIndex`, proved with `Fail.toResultMap` and a lemma about
`Result.traverse` (`traverseMap`, 10 lines). Fix: std lemmas saying
`eachLine` is a traverse of `whole` per line, and that `many1 (pick
words)` reads a line exactly when it is a string of the words. Medium
to large. Also, `pick` of eight one-character words says "expected '('
or '[' or '{' or '<' or ')' or ']' or '}' or '>' or the end of the
line": a comma list ("one of '(', '[', …") would read better. Small.

**Fixed (SW-998, 1 November 2026).** Std now states what each piece and
combinator reads when it succeeds (`Parse.Reads`, in
`crates/elab/src/std/Parse/Reads.sw`): `eachLineReads` gives one value
per line, each its parser's spec of the whole line; `readsMany` one part
per value; `readsPickBy` that a `pick` from a printer's table reads the
value's own word; `readsLabel` that a label reads what its parser read.
The parser is back to `eachLine`/`many`/`pick` (with `label "a
bracket"`, so a stray character is "expected a bracket or the end of
the line"), and `parseReadsLines`, its statement unchanged, is one
theorem of seven lines: Proofs/Parse.sw went from 63 lines (five lemmas)
to 26, Day10.sw from 114 to 107. Day 16's `readDigits`, the other
parser written by hand only to be proved, is now `Parse.line input.trim
(() => many hexDigit)` (Day 16's notes).

### 2. Missing std

- `List.getOrMem` (index below the length → `getOr` is a member),
  `List.countLeLength` (`count p ≤ length`), `List.countNotAdd`
  (`count (not p) + count p = length`). `stitchwort search` with the
  shapes found none in std. Small each.
- **The middle of a sorted list**: at most k elements below index k,
  at most n − 1 − k above (`countBelowSorted`, `countAboveSorted`, 25
  lines), and a median that is unique for odd counts (`middleUnique`).
  Day 7 of 2021 had a median too. Std candidate `List.median` with these.
  Medium.
- **`Result.traverse` gave `Ok`**: each output is its input's
  (`traverseMap`), and `withIndexFrom` mapped back by `snd`
  (`mapSndWithIndex`). Small each.
- **Constructor injectivity.** `Corrupted a = Corrupted b → a = b` took a
  helper function with a fallback and `Eq.cong`, twice
  (`corruptedInjective`, `unclosedInjective`). `cases` closes a
  constructor clash, but nothing gives injectivity. Fix: generated
  `T.C.injective` lemmas, or `cases` doing injection on a hypothesis.
  Medium.

### 3. Confusing errors

- **`foldl`**: `List has no field or function foldl`, with no "did you
  mean `foldLeft`". Small (a list of common other-language names).
- **`()` (absurd) in a multi-column arm** (`| Cons (b, piece) frames, ok,
  Nil, ()`) was `E-NOT-EMPTY`, showing `h`'s type with `line`, not the
  `Nil` the third column matched, so the clash wasn't seen. And two
  later, unrelated arms got `W-REDUNDANT` ("the earlier arms together
  cover it"), as if the failing arm matched everything. In a nested
  `match h with | ()`, the parser wanted `=>` and blamed the next outer
  arm. Workaround: `h => cases`. Fix: refine a column's type by the
  earlier columns' patterns before checking `()`, don't count an arm
  that failed toward coverage, and say "an absurd arm needs a top-level
  function arm" if that is the rule. Medium.
- **`rfl` under a hole** (`firstIllegalOfScan _ Curly rfl`, with `_` the
  line, fixed only by the expected type) was `E-REFL`: "computing the
  left side gives `scan [] […, …, …]`". With the line written out it
  checks, and `scan [] (tokens "[<>]") = Unclosed [] := rfl` checks too.
  My reading (not verified in the elaborator): `rfl` was checked before
  `_` was solved, and the message then printed the solved hole. The
  `…`s also hid every element, so nothing showed what was stuck. Fix:
  postpone `rfl` while its sides have unsolved holes, or say they do;
  print a stuck term's head at least. Medium.
- **An implicit not found through a definition.** `Scored (…)
  (completesOfUnclosed line (Cons top below) e) rest` was a mismatch:
  expected `Balanced (line ++ List.map (?14 …) Closer)`, has `Completes
  line (Cons top below)`, which the note unfolds to `Balanced (line ++
  Cons (Closer top) (List.map below …))`: the map was computed one step,
  so `?closers` wasn't solved. Workaround: `Scored [closers := Cons top
  below]`. Fix: unify the folded forms (`Completes line ?c` against
  `Completes line (Cons …)`) before computing. Medium.
- **A lambda argument checked before the arguments that fix its type.**
  In `traverseMap _ g h (each) xs ys hyp`, `each`'s hypothesis came in as
  `?8 row line tokens read (column, char) = Ok token`, so a `rewrite` in
  it found nothing (`E-REWRITE-NOTHING`, which did show the `?8`).
  Workaround: put the lambda parameter last. Fix: postpone lambda
  arguments until the others are checked (Lean's postponement; relevant
  to the postponement work in progress). Medium.
- Goals print definitions unfolded: `Legal before` as `∃ (ending: …) =>
  Balanced (…)`. And `search` printed `countBelowSorted`'s type with an
  unreduced redex, `(score => (x => score < x) (List.getOr sorted k 0))`.
  Small.

Good: `match e:` on `top == closer` refines hypotheses, and when I
rewrote `h` anyway the note said "`h` is already refined: use it as it
is". The import error for a constructor said to import its type.
Indexed `Prop` families (`Balanced`, `FirstIllegal`, `ErrorScore`) and
matching on them with named implicits (`Concat [xs := a] [ys := b] …`)
worked first time.

### 4. Search

- `search --at` at `tokenOfChar` (a `Char` match, while the namespace
  had an unrelated error) took 41 s and found nothing; with the
  namespace checking, the other goals took 3.3 s.
- At `notBelow` (`(y < x) = False` from `x ≤ y`) it said omega alone
  closes it and listed std's `Nat.leqFalseOfLess`; I had written a
  `match` and omega, and now use `omega`.
- At `count p ≤ length` nothing closes it (std lacks it), and the six
  "applicable" results were noise: `Finite.check`, day 8's `eachDigit`
  (leaves `length ≤ 9`), and `Bool.canonicalTrue`, which leaves the goal
  itself. Fix: drop an applicable result whose leftover goal is the goal.
  Small.
- `search '⊢ List.getOr ?xs _ _ ∈ ?xs'` and `'⊢ List.count ?xs _ ≤
  List.length ?xs'` found only my own lemmas: the right answer, quickly.
- `search --rewrite 'List.map ?xs (x => x)'` found `List.mapId` first.

### 5. Proof engineering

- **Append shapes.** The grammar's pieces are joined with `++`, and every
  step of the bridge restates a list: `closeShape` needed three
  `appendAssoc` rewrites to say `(s ++ o :: p) ++ c :: r = (s ++ o :: (p
  ++ [c])) ++ r`. A normaliser for `++` (as `ring` is for `+` and `*`)
  would remove these. Medium.
- **The converse needed a ghost.** "Scan ends empty → balanced" isn't a
  direct induction: inserting a matched pair inside a balanced line is
  awkward with this grammar. Keeping the read tokens as balanced pieces
  between the open brackets (`flatten`, `AllBalanced`) made each step
  local: close the innermost piece, wrap it, and append it to the one
  outside. Worth a line in the proving guide's "small lemmas" advice.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day10.main` on the input | 0.30 s user (0.36 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day10.Proofs Aoc.Year2021.Day10.Tests` | 0.90 s user |
| `stitchwort audit Aoc.Year2021.Day10` (with the search) | 1.9 s user |

114 lines of program, 84 of spec, 494 of proofs, 61 of tests.

### Ranked

1. Std.Parse has no lemmas for what a parser reads, so the parser
   guarantee meant dropping `Parse.eachLine`/`pick` for a hand-written
   one (item 1).
2. Elaboration order: a lambda argument, and an `rfl`, checked before the
   holes that fix their types were solved; the messages showed solved
   holes or `?8` (item 3). Fix: postponement.
3. The absurd pattern `()` in a multi-column arm doesn't see the other
   columns, and a failed arm causes false `W-REDUNDANT` warnings (item 3).
4. Missing std: `getOrMem`, `countLeLength`, a sorted-list median,
   `traverse` lemmas, constructor injectivity (item 2).
5. No normaliser for `++`: list-shape lemmas by hand (item 5).

## Day 11: Dumbo Octopus

A grid of octopuses, each with an energy level from 0 to 9. In a step
every level goes up by 1; each octopus above 9 then flashes, giving 1 to
each of the eight around it (diagonals too), which can set others off;
none flashes twice in a step, and every one that flashed ends it at 0.
Part 1 counts the flashes in 100 steps, part 2 finds the first step in
which every octopus flashes. Answers on Matt's input (10 by 10): 1773
and 494 (his Scala solution's); the puzzle's 10 by 10 example gives 204
flashes in 10 steps, 1656 and 195, and its 5 by 5 example is checked
step by step. Compiler: release build of `main` at 9ae31b2a, 1 November
2026.

### The program

The grid is `List (List Nat)`, row by row. `mapCells` maps every cell
with its (row, column), `cellAt` reads one (`None` off the grid), and a
step's flashers are a grid of `Bool`s of the same shape. `around` is the
eight positions around a cell: `List.between (r - 1) (r + 1)` by
`List.between (c - 1) (c + 1)`, less the cell itself (positions are
`Nat`s, so nothing is above row 0; past the far edges nothing has
flashed). A cell's `energy` is its level, plus 1, plus the flashers
around it.

The cascade is worked out in rounds, not with a worklist: a round marks
every octopus whose energy, counting the flashers so far, is above 9
(`flashRound`), and the rounds stop when one changes nothing
(`next == flashed`), or after as many rounds as there are octopuses
(`cascade`, `flashers`). Each round recounts every cell's neighbours,
which is simple to reason about (it is the Kleene iteration of "above 9
flashes") and fast enough. The step sets the flashers to 0 and the rest
to their energy. Part 1 adds up the 0s after each of 100 steps; part 2
looks for a step after which every cell is 0, up to `syncLimit` (10,000)
steps, and returns an `Option`. Both answers were right on the first
run.

The parser is day 9's: `many1 digit` per line (`Fin 10`), a pure
`firstRagged` check, then the digits as numbers (`numbers`).

**The spec** (Spec/Spec.sw) has no rounds. Two positions are `adjacent`
when they are different and at most one row and one column apart. For a
set of flashers `f` (a `(Nat, Nat) → Bool`), an octopus's `energyIn` is
its level, plus 1, plus the adjacent octopuses in `f`, counted over the
whole grid (`gridCells`). `f` is `Closed` if every octopus whose energy
is above 9 is in it, and the step's `Flashers` are the least closed set:
closed, and inside every closed set. Least matters: with two adjacent 8s,
"both flash" is closed (each would be at 10), but neither starts the
other, and nothing flashes (`eightsClosed`, `eightsNotFlashers` in the
tests). `after levels f` is the levels after the step, `flashCount` the
number in `f`. A `Run levels steps final total` is a chain of such
steps; `Part1Answer levels a` is a run of 100 steps with `a` flashes;
`AllFlashIn levels n` says step n (from 1) has every octopus in its
flashers, and `Part2Answer levels n` that step n is the first such.

### Proved, for every grid

In `Aoc.Year2021.Day11.Proofs` (Proofs/Grid.sw, Around.sw, Rounds.sw,
Cascade.sw, Step.sw, Parts.sw, Parse.sw, 679 lines), with no hypotheses
on the grid (ragged or empty grids, levels above 9, all included):

- `flashersCorrect`: `Flashers levels (flashedAt (flashers levels))`:
  the program's cascade reaches exactly the least closed set. The rounds
  from nobody grow (`grows`), stay inside every closed set
  (`belowClosed`), and once a round adds nobody the flashers are closed
  (`closedOfStable`) and stay put (`staysStable`). A round that adds
  somebody adds an octopus of the grid (`stableOfCount`, by
  `List.countLtMem` over the grid's positions), so the round after as
  many rounds as there are octopuses adds nobody (`stableAtSize`); the
  program stops at the first round that adds nobody or after that many
  rounds (`cascadeAfter`), so it stops at a stable round either way. This
  is the termination argument: the cascade's bound is proved enough.
- `flashersUnique`: two `Flashers` of the same levels are equal, so the
  spec's step is a function.
- `stepCorrect (spec: Flashers levels f)`: `step levels = after levels
  f`. `zerosCorrect`: the step's 0s are `flashCount levels f`.
  `allZeroCorrect`: the step is all 0s exactly when every octopus is in
  `f`.
- Underneath: the program's `around` is the spec's adjacency
  (`adjacentOfAround`, `aroundOfAdjacent`; the six arithmetic facts are
  each closed by `cases`), and counting flashers over `around` counts
  them over the grid (`countAround`: both filtered lists are distinct
  and have the same members, so `List.permOfSameMembers` makes them the
  same length). The grid's positions are distinct (`positionsDistinct`),
  and `gridCells` after `mapCells` is `gridCells` mapped
  (`gridCellsMapCells`).
- `part1Correct`: `Part1Answer levels (solvePart1 levels)`, and
  `part1Unique`: any `Part1Answer` is `solvePart1 levels` (every `Run`
  is the program's, `runIsProgram`).
- `part2Correct (found: solvePart2 levels = Some n)`: `Part2Answer
  levels n`: every octopus flashes in step n and in no step before it.
  `part2None (none: solvePart2 levels = None) (high: n ≤ syncLimit)`:
  `Not (AllFlashIn levels n)`. The search is bounded. The puzzle
  promises a step in which all flash, and on Matt's input the program
  finds 494 within the bound (a test); nothing proves that every grid
  has such a step, so part 2 is proved as "if it answers, the answer is
  the first such step; if not, there is none up to 10,000".
- `parseDigits`, `parseRectangular` (D2108): every level of a
  successful parse is at most 9, and every row is as long as the first.
  The answers' theorems need neither.
- Tests: both examples (one and two steps of the 5 by 5, 10 and 100
  steps of the 10 by 10, part 2), the spec's `after` on the program's
  flashers, `around` in a corner and inside, two 8s, a 9 next to an 8, an
  empty grid, a ragged one, the parser's errors.

Not proved: nothing left open, no hypothesis added, no opaque
definitions. `stitchwort audit Aoc.Year2021.Day11` (with the
counterexample search): `audited 75 theorems: 0 failed, 1 with
warnings, 74 passed`. The warning is `onGridAfter` (an octopus that has
flashed after k rounds is on the grid): random grids rarely flash, so
the search met no case; the hypothesis can hold (`flashedAfterOneRound`,
a test theorem, has one).

Breaking the program breaks the proofs: one round fewer
(`levels.gridCells.length - 1`) fails `flashersStable` (omega's model:
one octopus, no rounds); `9 <= energy` for `9 < energy` fails
`roundIntro` and `roundElim`; dropping the "not the cell itself" filter
from `around` fails `adjacentOfAround`, `aroundDistinct` and
`countAround`; answering `Some (Succ number)` in `firstSync` fails
`syncFound` and `syncNone`.

Most proofs checked first or second time. The first version of the
program allowed one more round than there are octopuses; the proof
showed that as many rounds as octopuses is enough, and the program now
uses that.

### 1. Std.Parse: none

Day 9's parser, unchanged in shape.

### 2. Missing std

- **Grids.** `mapCells` (map a grid with each cell's position),
  `cellAt`, `gridCells` after `mapCells` (`gridCellsMapCells`, with
  `withIndexFromMap` and `mapConcat` under it), `gridCells` membership as
  `cellAt` (`memGridCellsAt`), distinct positions (`positionsDistinct`,
  `rowsDistinct`, `columnsDistinct`), a `mapCells` congruence
  (`mapCellsCong`), and the eight positions around a cell with their
  membership, distinctness and count lemmas (Around.sw): 210 lines a
  std grid module would hold. Day 9 here and days 10, 12, 16, 18 and 20
  of 2024 wrote their own four neighbours; this is the first with eight.
  Std candidate, extending SW-960's grid module. Medium.
- **Already in the project, written again.** `countLeLength` (day 10's
  `countAtMostLength`) and `allMapBool` (`(xs.map f).all p = xs.all (x
  => p (f x))`, day 8's `allMapped`): `stitchwort search` finds both,
  but I searched only after writing them (item 4). Std candidates,
  small.
- **Least fixed points on a finite set.** Cascade.sw is 160 lines, most
  of it generic: iterate a monotone operator on `Bool` predicates from
  nothing; each iterate is inside every closed set; once it stops
  growing it is closed; it stops within as many rounds as the set has
  elements. A std toolkit for this would make "least set closed under a
  rule" specs (flood fills, cascades, reachability) cheap. Medium.
- **No O(1) array.** Each neighbour lookup is `get` on a list of rows
  and a row, O(row + column). The run takes 4.1 s interpreted (1.3 s
  with `--native`); with the neighbour count removed, 10,000 steps take
  2.8 s, so most of the time is counting. A one-pass stencil for list
  grids (std's `Vec.around` is one for a single row) or an array would
  fix it. Medium (stencil) to large (array).

### 3. Confusing errors

- **A `match` on a bounded search ran out of resources.** `match
  solvePart2 levels with | Some step => … | None => …` in `main` was
  `E-RESOURCE`, "a value was too large to show", "the value being shown
  was a call of `solvePart2`, computed far enough to be very large".
  Nothing is being shown: checking the `match` computes its scrutinee,
  and `firstSync levels 1 10000` unfolds through 10,000 `if`s stuck on
  the unknown grid. A 13-line repro (file mode): `search xs number
  steps` recursing as `if xs.all (x => x == 0) then Some number else
  search (xs.map (x => x - 1)) (Succ number) more`, called as `search xs
  1 10000`, and `match answer xs with …` in any function, pure or not:
  with 100 steps it checks in 0.11 s, with 1000 in 0.68 s, with 10,000
  it runs out. Workaround: pass the `Option` to a helper (`describe
  (solvePart2 levels)`). Fix: don't compute a `match` scrutinee past a
  head stuck on a variable, and say in the message that the `match`
  caused it. Medium.
- **A pure `map` at the end of `{Fail}` code runs in `Fail`.** `| None =>
  rows.map (row => row.map Fin.toNat)` as the last arm of `checkRows`
  elaborated `map` (effect-polymorphic) in `Fail`, so `Fail.toResult (()
  => checkRows rows)` computed to `Effect.foldComp … (List.map rows (row
  => Done (…)))`, not `Ok (List.map …)`, and `Result.okInjective` didn't
  fit. Workaround: a pure helper, `numbers rows`. Fix: give a call whose
  arguments are all pure the empty effect, or a std lemma for
  `Fail.toResult` of a pure `map`. Small to medium. (The D2108 notes
  cover a `match` on such a call; this is the same effect inference in
  another place.)
- **`rewrite` against an unfolded goal**, the known kind: in the goal
  `flashedAt (flashRound levels flashed) (a, b) = True`, `rewrite
  cellAtMapCells levels (at level => 9 < energy …) a b` found nothing,
  though the same rule with a variable function worked in another
  lemma; and `9 < energy …` had computed to `9 ≤ level + …`, so `rewrite
  energyAgrees …` found nothing either. The notes showed both computed
  forms, which made the fix quick: `Eq.trans` with a lemma stated in the
  folded form (`flashedAtMapCells`), and `Eq.cong (Nat.leq 10)`.
- Good: `if same: a ≤ b then (proof) else (proof)` was `E-UNIVERSE`
  ("`if` can't choose between proofs yet") with the exact `match
  Nat.decLessEq … with | Yes … | No …` to write instead. A theorem whose
  result is a `def` that unfolds to a function type (`OnGrid`, `Stable`)
  got `E-ARITY` naming the parameters to add. `rewrite e at found` after
  `match e:` said "`found` is already refined: use it as it is". `cases`
  closed all six adjacency facts (`&&` of `==`, `≤` and saturating `-`)
  on its own, where day 9 met `E-MATCH-MOTIVE`.

### 4. Search

- `search --at` at `neighboursMono` (more flashers, more flashing
  neighbours; another goal of the file was open) took 44 s and missed
  `List.countLeMem`, which closes it: the goal was searched with
  `flashingNeighbours` unfolded to `List.foldLeft … Nat.succIf`, so
  nothing about `List.count` matched. The ten results were noise
  (`Bool.canonicalTrue` leaving the goal itself, day 8's `eachDigit`,
  2025 day 9's `outsideFlagZero`, `Finite.check`). Fix: search the goal
  with `List.count` folded. Medium.
- At `allMapBool`'s step (the namespace otherwise checking) it took 2.2 s
  and offered two `andComm` rewrites and `Bool.ifThenElseCong …
  Std.byDecision ?` "leaving `Unit → False = False`", with `byDecision`
  standing for an equation of two `List.all`s on variables, which it
  can't decide. I didn't check whether the kernel accepts it; if not, it
  shouldn't be listed. Small.
- `search --rewrite 'List.all (List.map _ _) _'` (1.9 s) and `search '⊢
  List.count ?xs _ ≤ List.length ?xs'` find day 8's `allMapped` and day
  10's `countAtMostLength` first; I ran them only after writing my own
  (item 2).

### 5. Proof engineering

- The spec counts flashing neighbours over the whole grid, the program
  over eight positions; the bridge is "two distinct lists with the same
  members have the same length" (`List.permOfSameMembers`,
  `List.permLength`), which needs both lists distinct. Std's
  `distinctFlatMap`, `distinctFilter` and `distinctBetween` did it for
  `around`; `gridCells`' positions needed their own induction (45
  lines), as `distinctFlatMap`'s key must give back the whole outer
  element, `(row, cells)`, not just the row.
- Pair lambdas like `((at, x)) => (at, f at x)` elaborate to
  projections (`arg.fst`), which compute on pairs, so no `match` was
  needed in `mapCong` callbacks. Statements quantified over a position
  `q` needed a `| (a, b), …` arm to reach lemmas stated on `(a, b)`.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day11.main` on the input | 4.1 s user (4.2 s) |
| `stitchwort run --native Aoc.Year2021.Day11.main` | 1.3 s user |
| `stitchwort check --no-cache Aoc.Year2021.Day11.Proofs Aoc.Year2021.Day11.Tests` | 3.2 s user |
| `stitchwort audit Aoc.Year2021.Day11` (with the search) | 5.4 s user |

128 lines of program, 65 of spec, 679 of proofs, 60 of tests.

### Ranked

1. A `match` on a call of a bounded search (`firstSync … 10000`) makes
   checking compute the whole search and fail with `E-RESOURCE` about "a
   value too large to show" (item 3). Fix: don't compute a stuck
   scrutinee; name the `match` in the message.
2. Grid simulations are slow on lists (4.1 s), and every grid day writes
   its own `mapCells`, `cellAt`, neighbours and their lemmas, here 210
   lines (item 2). Fix: a std grid module with positions, eight and four
   neighbours, and a stencil.
3. `search --at` searches the unfolded goal, missing `List.countLeMem`,
   and took 44 s (item 4).
4. A pure `map` in tail position of `{Fail}` code is elaborated in
   `Fail`, hiding `Ok (map …)` from proofs (item 3).
5. A reusable least-fixed-point toolkit would cover most of Cascade.sw
   (item 2).

## Day 12: Passage Pathing

A map of caves joined by passages, one per line (`start-A`). Caves named
in capitals are big, the others small. Part 1 counts the paths from
`start` to `end` that visit no small cave more than once; big caves may be
visited any number of times. Part 2 lets one small cave (not `start` or
`end`) be visited twice. Answers on Matt's input (24 passages): 3510 and
122880 (his Scala solution's); the puzzle's first example gives 10 and 36,
and its ten part 1 paths are a test. Compiler: the installed release
build of `main`, 1 November 2026.

### The program

Passages are `(Text, Text)` pairs. `isBig` says a name starts with a
capital. The program builds a table of each cave's neighbours once
(`neighbourTable`, a list of pairs looked up with `List.lookup`), then
lists the routes from `start` by a depth-first search (`routesFrom`) and
counts them. The search state is the small caves not yet visited
(`start` and `end` aside) and whether the second visit is still spare
(part 1 starts without it, part 2 with it). One step is a pure function,
`step`, which says whether moving to a neighbour ends the path (`end`),
is not allowed (`start`; a small cave already visited with no spare
visit; a big cave from a big cave), or goes on with the new state. Both
answers were right on the first run.

The search is bounded: it goes at most `3 * (small caves) + 4` steps
deep, and the proofs show that is enough (`reach` goes down by at least 1
each step). It was first written with `decreasing` on the same measure;
item 4 says why it isn't. It also counted instead of listing (1.3 s
instead of 2.0 s for both parts); item 4 again.

The parser reads `name-name` with `takeWhile1` on letters, then checks
(`checkPassages`, with a pure `firstBigPair`, as in the D2108 pattern)
that no passage joins two big caves, failing with "line 2: A-BC joins two
big caves, so a path could cross it back and forth forever and there would
be infinitely many paths".

**The spec** (Spec/Spec.sw) uses the program's `isBig` and says the rest
in the puzzle's terms. Two caves are `connected` when a line names them,
either way round. A path is a list of caves, each `connected` to the
next (`followsPassages`, over `zipWithNext`), whose first is `start` and
last is `end` (`startToEnd`). `visits path cave` counts a cave in a path.
Part 1's rule (`SmallOnce`): every small cave is visited at most once.
Part 2's (`OneSmallTwice`): every small cave at most twice, no two small
caves twice or more, and `start` and `end` exactly once each. The answer
is `PathCount isPath n`: a list of `n` paths, without repeats, holding
exactly the paths that satisfy `isPath`.

**The assumption.** The count is finite only if no passage joins two big
caves; otherwise a path can walk between them for ever. The puzzle never
says so. In full, `NoBigNeighbours passages` is: for all caves `a` and
`b`, if `connected passages a b = True` and `isBig a = True`, then
`isBig b = False` (so also no passage from a big cave to itself). The
answers' theorems take it as a hypothesis, the parser checks it, and the
theorems from the input have no hypothesis but the successful parse.

### Proved

In `Aoc.Year2021.Day12.Proofs` (Proofs/Steps.sw, Neighbours.sw,
Routes.sw, Rules.sw, Parts.sw, Parse.sw, 807 lines):

- `part1Correct (passages) (promise: NoBigNeighbours passages)`:
  `PathCount (Part1Path passages) (solvePart1 passages)`, where
  `Part1Path passages path` is `startToEnd path = True ∧
  followsPassages passages path = True ∧ SmallOnce path`.
- `part2Correct (passages) (promise: NoBigNeighbours passages)`:
  `PathCount (Part2Path passages) (solvePart2 passages)`, the same with
  `OneSmallTwice path`.
- `parseNoBigNeighbours (input) (passages) (parsed: Fail.toResult (() =>
  parsePassages input) = Ok passages)`: `NoBigNeighbours passages`.
- `part1FromInput`, `part2FromInput (input) (passages) (parsed:
  Fail.toResult (() => parsePassages input) = Ok passages)`: the two
  answers' `PathCount`, with no other hypothesis.
- Underneath: the neighbour table gives exactly the connected caves,
  each once (`tableMem`, `tableDistinct`); a route is listed if and only
  if it `Follows` the steps (`routesFollow`; `followRoutes`, given a
  depth above `reach`, which each step lowers, `stepDecreases`); routes
  are listed once (`routesDistinct`, by `List.distinctFlatMap` keyed on
  the first cave). `Tracks` says what the search's state means for the
  path so far (which small caves it has visited, `start` once, `end` not
  yet, the rule kept so far, whether a cave was visited twice), and each
  kind of step keeps it (`tracksBig`, `tracksFresh`, `tracksAgain`).
  `followsCompletes` and `completesFollows` then show, by induction on
  the rest of the path, that the routes the steps allow are exactly the
  ways to finish a path by the rule; `completesFollows` is where the
  promise is used (a step from a big cave to a big one is never taken,
  and no path by the rules takes one).
- Tests: the example's ten paths and both answers, a passage between two
  big caves, a missing dash, `isBig`, `start-end` alone, no passages,
  neighbours of a cave with a passage to itself and a passage listed
  twice, and both answers on the input.

Not proved: nothing left open. One hypothesis, `NoBigNeighbours`, on
`part1Correct` and `part2Correct`; without it the statements are false
whenever two big caves are joined and reachable (there is no finite
list of all the paths). The parser checks it, and `part1FromInput` and
`part2FromInput` drop it. No opaque definitions.

`stitchwort audit Aoc.Year2021.Day12` (with the counterexample search):
`audited 64 theorems: 0 failed, 2 with warnings, 62 passed`. The two
warnings are `parseNoBigNeighbours` and `endsVisited`: random texts
never parse and random lists never start at `start`, so the search met
no case. Neither hypothesis is contradictory: `smallParses` and
`shortPath` (test theorems, `rfl`) satisfy them.

Breaking the program breaks the proofs: `Continue unvisited spare` for
`Continue unvisited False` (the spare visit never used up) fails
`stepDecreases` with a counterexample, and `followsCompletes` and
`completesFollows`; searching `3 * unvisited.length + 3` steps deep
instead of `+ 4` fails `pathsCorrect` (omega: `3 * len + 2 * toNat
twice ≤ 3 * len + 1`); dropping the `start` check fails `followsCompletes`.

### 1. Std.Parse: none

`takeWhile1 "a cave name" Char.isAsciiLetter`, `char '-'`, and
`Parse.eachLine` did it; the missing dash says "line 2, column 3:
expected '-', got the end of the line".

### 2. Missing std

- **Constructor injectivity and disjointness.** To use `step … = Continue
  left spare` I wrote `Step.goesOn`, `Step.leftOr`, `Step.spareOr` and
  four lemmas through `Eq.cong` (`Finish ≠ Continue …`, `Continue a s =
  Continue b t → b = a`, …). Fix: generate `T.C.injective` and
  constructor-disjointness lemmas for each data type, or let `match` on
  an equation of constructors take them apart. Medium.
- **Looking up a table built by `map`.** `List.lookup (cs.map (c => (c, f
  c))) cave` is `Some (f cave)` for a member, `None` otherwise
  (`lookupBuilt`, `lookupMissing`). Std candidates, small.
- **Lists and counts**, each small: `(xs.filter p).length ≤ xs.length`
  (2024 day 24's `filterNoLonger`, imported) and `<` when a member fails
  `p` (`filterDropsShorter`); `Bool.toNat b ≤ 1`, now written three
  times (day 10's `toNatAtMostOne`, imported; 2024 day 24's
  `toNatSmall`); a member is counted at least once (`visitsMember`, over
  `List.occurrences`); counts grow along `++` (`visitsGrow`); membership
  in a filtered-out list (`withoutMem`).
- **No `List.flatMapCong`**, so a `decreasing` call inside `flatMap`'s
  function has no congruence lemma; `List.concat (List.map …)` works.
  Small.
- **Path enumeration.** Routes.sw (`Follows`, membership both ways,
  distinctness) is generic in the step function. A std "walks of a
  graph under a state machine" module, listing walks and characterising
  them one step at a time, would make counting-paths puzzles a matter of
  the visit rule (Rules.sw). Medium.

### 3. Confusing errors and displays

- **The goal shown after `match e:` wasn't the refined one.** In
  `routesFollow`, after `match e: step unvisited spare cave other with |
  Finish => ?`, the `[GOAL]` showed `⊢ other ∈ next cave ∧
  Aoc.Year2021.Day12.Proofs.Follows.%match1 next other tail (step
  unvisited spare cave other)`, unrefined; `rewrite e in …` at the same
  place then said "found no `step unvisited spare cave other` in the goal
  … goal: `List.Any (y => y = other) (next cave) ∧ tail = []`": the goal
  was already refined. I added a `rewrite` that wasn't needed. Small.
- **Printed goals capture variables.** `y ∈ neighboursOf passages cave`
  printed as `⊢ List.Any (y => y = y) (neighboursOf passages cave)`, and
  `search --at` printed `omega closes ⊢ List.occurrences sofar (c => c ==
  c) ≤ …` for `visits sofar c`. Fix: rename a bound variable that shadows
  a free one when printing. Small.
- Good: `if bigOther: isBig other then` was `E-NOT-A-TYPE` with "for a
  `Bool`, write …"; `(x != x) = False` in a statement said `!=` is the
  proposition there and how to ascribe the `Bool`; `if same: c = y then
  (proof) else (proof)` gave the `match Std.Text.decEq c y with | Yes …`
  to write. `cases` closed 48 of the 56 cases of `stepDecreases` on its
  own, and said the rest were stuck on `left`, a `List`.

### 4. Termination, and proving things about the search

The worst friction of the day. The search's natural measure has three
parts (small caves left; the spare visit; whether we stand in a small
cave), and `decreasing` takes at most two, so I folded the last two into
one number. Then:

- **A lambda in a recursive call's argument, inside `sumBy`'s callback,
  becomes an unknown `x`.** `pathsOnFrom next (unvisited.filter (c => not
  (c == other))) spare other [decreasing := …]` inside `next cave |>
  .sumBy (other => …)` had the goal `Nat.LexLess (List.length x) … `, and
  the proof about the filter was a mismatch ("expected `List.length x <
  List.length unvisited`, but this has type `List.length (List.filter
  unvisited (c => …)) < …`"). A `let left := …` before the call was as
  opaque ("expected `List.length left < …`"). Three-line repro (file
  mode): `def g (xs: List Nat) (k: Nat): Nat decreasing xs.length := [1,
  2] |> .sumBy (other => if k == 0 then 0 else g (xs.filter (c => c ==
  other)) k [decreasing := ?])` shows `⊢ List.length x < List.length
  xs`; outside a callback, or with `xs.drop 1`, the goal shows the real
  argument. Workaround: a top-level `without caves cave`. Fix: keep the
  argument's term in the obligation. Medium (a bug).
- **`match e:` in a `decreasing` definition blocks proofs about it.** The
  recursive call needed `e: step … = Continue left spare` for its
  decrease, so the program read `match e: step unvisited spare cave other
  with …`. The compiler lifts that `match` to a function taking the
  scrutinee and `rfl`. In a proof, `match e: step unvisited spare cave
  other` with a hypothesis mentioning the lifted `match` was
  `E-MATCH-MOTIVE`: "generalising this `match`'s scrutinee makes its type
  ill-formed … checking the type it would have: `rfl` can't prove this".
  The note's advice, "a top-level helper with a written signature", can't
  be followed: the lifted `match` has no name. Workaround: a depth bound
  instead of `decreasing`, with no `e:`, and `stepDecreases` proving the
  bound enough. Fix: generalise the `rfl` with the scrutinee (as Lean's
  `match h : e with` does), or let source name the lifted `match`.
  Medium to large.
- **Count and list couldn't be related.** I meant to keep the counting
  program and prove `pathsOnFrom … = (walksOnFrom …).length` pointwise
  under `sumBy`. `List.sumByCong (next cave) _ _ (other => match …)` left
  both functions as holes (the callback's goal was `?14 … = ?14 …`), and
  writing them out makes new lifted `match`es, which syntax.md says are
  different functions. Workaround: the program lists the paths and
  counts the list (2.0 s rather than 1.3 s). Fix: elaborate a
  congruence lemma's function arguments from the expected type before
  the callback (close to SW-963's lambda-before-later-argument). Medium.
- `walksOnFrom.unfold` showed the body as `walksOnFrom.%step next … (… =>
  walksOnFrom …)`, not unfolded further; harmless, but the goal was hard
  to read.

With the depth bound, the rest went smoothly: `match e:` on `step`
refines the hypotheses (`inTail: [] = tail ∨ Void` in the `Finish`
case), and matching on `other == "end"`, `isBig other` and the rest one
by one, as `stepDecreases` does, refines `step`'s computed `if` chain in
every hypothesis. Rules.sw (359 lines) is mostly bookkeeping of visit
counts; most lemmas checked first or second time, the misses being
`Bool.trueNotFalse` against `Bool.falseNotTrue`, and `let`-bound
lambdas, which have no expected type, so a `rewrite` inside was
`E-REWRITE-NO-GOAL` and an `Exists.elim` inside had a hole for its goal
until the `let` had a type.

### 5. Inference

- `List.distinctNil` after a `rewrite` was `E-UNSOLVED` ("can't work out
  an implicit argument"); `List.distinctNil [a := Text]` fixed it.
- `routesFollow … _ rest listed`, with the depth a hole, was a mismatch:
  `listed` showed `routesFrom` one step unfolded, the depth as `… + 3`,
  and the hole wasn't solved from it. Writing the depth out fixed it.

### 6. Search

- `search --at` (2 to 7 s a goal) closed four of the five goals I tried
  it on, but I ran it only after writing those lemmas by hand: `differ`
  (`(x == y) = False` from `x ≠ y`) by `Decidable.toBoolOfNot`;
  `appendStep` by `rewrite List.appendAssoc sofar [y] more in rfl`;
  `Bool.toNat b ≤ 1` by day 10's `toNatAtMostOne` and 2024 day 24's
  `toNatSmall` (and "`cases` alone closes it"); `visitsGrow` by exactly
  my proof. `visitsMember` (an induction) got nothing that closed it.
  Pattern search found `filterNoLonger` in 2024 day 24.
- Noise in `applies`: `Bool.canonicalTrue … ?` leaving the goal itself,
  2025 day 9's `outsideFlagZero`, `Finite.check`, as on day 11; and the
  first closing proof for `differ` was `Nat.untilStableDecNo`, a
  `Nat.Iterate` lemma, ahead of `Decidable.toBoolOfNot`. Fix: drop
  results that leave the goal unchanged; rank by how specific the lemma
  is. Small.
- `stitchwort search '(?b: Bool) ≠ True → ?b = False'` and `'Not ((?b:
  Bool) = True) → ?b = False'` return one result, `List.findKeySome` (a
  premise match), and miss `Bool.falseOfNotTrue: (x: Bool) → Not (x =
  True) → x = False`; `'⊢ (_: Bool) = False'` lists it third. Why isn't
  established (perhaps `True` in the pattern isn't read as the `Bool`).
  Small to medium.
- `stitchwort audit` warns on any theorem about a successful parse,
  since random texts never parse. A test theorem showing the hypothesis
  can hold silences the doubt but not the warning. Fix: let the
  counterexample search try the namespace's test inputs, or say "a test
  theorem satisfies the hypotheses". Small to medium.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day12.main` on the input | 2.0 s user (2.1 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day12.Proofs Aoc.Year2021.Day12.Tests` | 4.1 s user (4.2 s) |
| `stitchwort audit Aoc.Year2021.Day12` (with the search) | 3.3 s user (3.4 s) |

127 lines of program, 53 of spec, 807 of proofs, 55 of tests.

### Ranked

1. Proofs about a `decreasing` search were out of reach: `match e:` in
   the definition makes proofs `E-MATCH-MOTIVE` on an unnamable lifted
   `match`, and a lambda in a recursive call's argument inside `sumBy`
   shows as an unknown `x` (item 4). Workaround: a depth bound proved
   enough. Fix: generalise the `rfl` with the scrutinee; keep argument
   terms in the obligation.
2. A count couldn't be proved equal to the length of a list built by the
   same search, as `sumByCong`'s functions weren't inferred from the goal
   (item 4). Workaround: list and count (50% slower).
3. The goal display after `match e:` showed the unrefined goal, and
   printed goals capture variables (`y => y = y`) (item 3).
4. No generated constructor injectivity or disjointness lemmas (item 2).
5. `Bool.toNat b ≤ 1` is now in three days; `List.lookup` of a mapped
   table, filter lengths, counts of members belong in std (item 2).

## Day 13: Transparent Origami

Dots on a sheet of transparent paper, one `x,y` per line (x across, y
down), a blank line, then folds, `fold along y=7` or `fold along x=5`.
Folding along a line reflects each dot beyond it onto the near half, and
dots that land together are one dot. Part 1 counts the dots after the
first fold; part 2 makes every fold, and the dots spell eight capital
letters: the answer is the picture. Answers on Matt's input (796 dots, 12
folds): 666, and a picture reading CJHAZHKU, row for row the same as his
Scala solution's (39 columns, 6 rows). The puzzle's example gives 17 and
a 5 by 5 square outline. Compiler: the installed release build of
`main`, 1 November 2026.

### The program

A `Dot` is a record `{ x, y }`, ordered through `Ord.byKey` on `(x, y)`
so a list of dots can drop repeats with `List.distinct`. A `Fold` is
`AlongX line` or `AlongY line`. `foldDot` reflects a dot beyond the line
(`2 * line - dot.x`) and leaves the others; `foldOnce dots fold` is
`dots.map (foldDot fold) |> .distinct`, and `foldAll` folds from
`dots.distinct`, one fold after another. Part 1 is the length of
`foldAll (folds.take 1) dots`; part 2 renders `foldAll folds dots` as
rows of `#` and `.` (`render`), from the top left corner to the
rightmost column and lowest row that hold a dot, so nothing is trimmed
or padded: the real picture is 39 wide, the last letter's right-hand
column of space being outside it. `main` prints `Part 2:` and the
picture on the lines after it, and `crates/cli/tests/aoc_answers.rs` now
takes an answer of several lines (one branch in `check_with`). Both
answers were right on the first run, in 0.35 s.

The parser is `Parse.all input readPaper`: `section readDot` (one dot a
line, then a blank line), then `lines readFold`, the axis read with
`pick [("x=", AlongX), ("y=", AlongY)]`. It then checks the puzzle's
promise (`checkPaper`, with a pure `firstBlocked`, the D2108 pattern): it
makes the folds itself, and before each one fails if some dot is on the
line or further beyond it than the line is from the near edge: "fold 2:
the dot at 2,0 is on its line, or further beyond it than the sheet
reaches on the near side". Parsing errors read well unaided ("line 3,
column 12: expected 'x=' or 'y=', got 'z='"; "line 2, column 1: expected
a number or a blank line, got 'f'").

**The spec** (Spec/Spec.sw) treats the sheet's dots as a set, a
proposition `Dot → Prop`. `Lands fold dot spot` says where a dot goes:
along `y = line`, a dot above the line stays put, and one below lands at
the same `x` with `spot.y + dot.y = 2 * line` (the line halfway between,
with no subtraction). A dot on the line, or one so far below it that its
mirror image would be above the top edge, lands nowhere. `AfterFold fold
marked spot` is `∃ dot, marked dot ∧ Lands fold dot spot`, the image of
the set; `AfterFolds` applies the folds in order, starting from `Listed
dots` (`spot ∈ dots`). Part 1's answer is `DotCount set n`: a list of
`n` dots without repeats whose members are exactly the set's. Part 2's is
`Shows picture set`, with `cellAt picture spot` the character at row
`spot.y`, column `spot.x`: every dot of the set is a `#`; every `#` is a
dot of the set; every character is `#` or `.`; and all the rows are as
wide as each other.

**The assumption.** In full, `Promise folds marked` says: for the first
fold, every dot of `marked` is clear of it, that is, for `AlongY line`,
`dot.y ≠ line ∧ dot.y ≤ 2 * line` (for `AlongX`, the same of `dot.x`);
and `Promise` holds for the remaining folds of the dots after the first
fold. The puzzle says the first half (no dot on a fold line); the second
it leaves unsaid, but its folds are at the middle of the sheet, and a
dot further out would land off the top or left edge, where `Nat`
subtraction would put it at 0. Without the promise the program and the
spec disagree (the program keeps a dot on the line; the spec drops it),
so the theorems take it as a hypothesis, and the parser checks it.

### Proved

In `Aoc.Year2021.Day13.Proofs` (Proofs/Fold.sw, Parts.sw, Picture.sw,
Parse.sw, 241 lines):

- `part1Correct (paper) (promise: Promise (paper.folds.take 1) (Listed
  paper.dots))`: `DotCount (AfterFolds (paper.folds.take 1) (Listed
  paper.dots)) (solvePart1 paper)`.
- `part2Correct (paper) (promise: Promise paper.folds (Listed
  paper.dots))`: `Shows (solvePart2 paper) (AfterFolds paper.folds
  (Listed paper.dots))`.
- `parsePromise (input) (paper) (parsed: Fail.toResult (() => parsePaper
  input) = Ok paper)`: `Promise paper.folds (Listed paper.dots)`.
- `part1FromInput`, `part2FromInput (input) (paper) (parsed: …)`: the two
  answers' statements with no other hypothesis.
- Underneath: `landsFoldDot` (a clear dot lands where `foldDot` puts it)
  and `landsOnly` (and nowhere else, with no hypothesis), both by `cases`
  after splitting the fold and `Lands`'s `∨`; `foldOnceHolds` (if a list's
  members are exactly a set's, and every dot is clear of the fold,
  `foldOnce`'s members are exactly the image); `foldsHold` and
  `foldsDistinct` by induction on the folds; `renderShows` (`render`
  shows exactly the list's dots) from `cellInside`, `cellOutside`,
  `widthCovers`, `heightCovers` and `rowWidth`.
- Tests: the example (parse, 17, the picture after one fold and after
  both), three promise failures (on the line; too far beyond; on the
  second fold's line only once the first is made), a bad axis, a missing
  blank line, a dot listed twice, no folds, and both answers on the
  input; part 2 is compared as the whole picture, and a test helper
  (`readLetters`, a table of 14 letters of the puzzle's font) reads it as
  CJHAZHKU.

Not proved: nothing left open. One hypothesis, `Promise`, on
`part1Correct` and `part2Correct`, needed as said above; the parser
checks it and the `FromInput` theorems drop it. Reading the letters is
not proved. Not stated: that the picture is no larger than it needs to
be (its last row and column hold a `#`); it is true of `render`. No
opaque definitions.

`stitchwort audit Aoc.Year2021.Day13` (with the counterexample search):
`audited 37 theorems: 0 failed, 2 with warnings, 35 passed`. The
warnings are `cellSomeInside` (`cellAt (render dots) spot = Some c`) and
`rowWidth` (`row ∈ render dots`): random inputs never hit a rendered
cell or row. Neither hypothesis is contradictory: the test theorems
`oneDotShown` and `oneDotRow` satisfy them.

Breaking the program breaks the proofs: reflecting to `2 * line + 1 -
dot.y` fails `landsFoldDot` and `landsOnly` (`E-CASES`); dropping the
`.distinct` from `foldOnce` fails `foldsDistinct` (and `foldOnceHolds`);
a width of `dot.x` instead of `dot.x + 1` fails `widthCons` with a
counterexample.

The proofs went quickly: most lemmas checked first time, and `cases`
did the arithmetic of the reflection on its own (splitting `line <
dot.y` inside a record update and closing each case by `omega`).

### 1. `search --at`

- **It refuses goals after a `match` on a constructor with fields.** In
  `landsFoldDot`, after `match fold with | AlongY line => ?`, `search
  --at` said `E-SEARCH-AT … can't be written as a statement of its own
  here … note: E-UNKNOWN-NAME: unknown name 'line'` (after 40 s, with
  `?`s open in the namespace). The goal's context lists `clear: dot.y ≠
  line ∧ …` before `line: Nat`: the hypothesis refined by the match comes
  before the pattern variable it now mentions, and the statement search
  writes from it has `line` used before it is bound. The same with an
  equation-style theorem (`| Cons dot rest, spot, member => ?`, with
  `member: spot ∈ Cons dot rest` before `dot`). A 13-line repro, file
  mode, 4 s:

  ```stitchwort
  type Fold =
    | AlongX (line: Nat)
    | AlongY (line: Nat)

  def lineOf (fold: Fold): Nat :=
    match fold with
      | AlongX line => line
      | AlongY line => line

  theorem small (fold: Fold) (h: lineOf fold < 3): lineOf fold < 4 :=
    match fold with
      | AlongX line => ?
      | AlongY line => omega
  ```

  The `[GOAL]` shows `h: line < 3` above `line: Nat`. Fix: order the
  context by dependency (pattern variables first) in the goal display and
  in `search --at`'s statement. Small to medium. Both goals I tried
  in such a place failed so; on this day `search --at` was only useful on
  goals with no pattern variables.
- Where it could run (2 s a goal), it was good: on `width (Cons dot rest)
  = Nat.max (dot.x + 1) (width rest)` it gave `List.foldRightCons _ _ _ _`
  (exact), and "`cases` alone closes it" on `clearsClear`. On `List.get
  (List.map (List.range n) f) i = Some (f i)` its first rewrite,
  `List.getMap`, was the right step, though std has no `List.get` of a
  range to finish with.
- Pattern search: `List.find _ _ = None → _` didn't list
  `List.findNoneNotMem`, whose `find` premise is its second (`x ∈ xs →
  List.find xs p = None → Void`); `List.find (?xs: List _) ?p = None`
  alone listed it second. A premise pattern seems to match only the
  first premise. Small.

### 2. Inference

- **`cases` as an argument solved the holes before the expected type
  did.** `Dot.ext _ _ cases cases`, expected `spot = foldDot fold dot`,
  was a mismatch: "expected `spot = (if line < dot.y then …)`, but this
  has type `spot = spot`". The first `cases` proved `?a.x = ?b.x` by
  making `?b` be `?a`. Writing the two dots out (`Dot.ext spot (foldDot
  (AlongY line) dot) cases cases`) checked. Repro (file mode):

  ```stitchwort
  type P = { x: Nat, y: Nat }

  def shift (b: Bool) (p: P): P := if b then { p | x = p.x + 1 } else p

  theorem holesExt (b: Bool) (p: P) (q: P) (sameX: q.x = (shift b p).x) (sameY: q.y = p.y): q = shift b p :=
    P.ext _ _ cases cases
  ```

  says "expected `q = shift b p`, but this has type `q = q`". Fix: unify
  the result type with the expected one before checking proof arguments,
  or don't let `cases`/`rfl` solve the goal's own holes. Medium.
- No eta for records: `{ x = spot.x, y = spot.y }` and `spot` aren't
  equal by `rfl`; `Dot.ext … rfl rfl` rewrote one into the other (SW-960
  item 4 is the same for pairs).

### 3. Std

- `List.foldRight` is a `foldLeft` over the reversed list, so `width
  (Cons dot rest)` doesn't compute to `Nat.max (dot.x + 1) (width rest)`,
  and `omega` saw `List.foldLeft (List.reverseOnto rest [dot]) …`. Two
  one-line lemmas (`widthCons`, `heightCons`) from `List.foldRightCons`
  fixed it. A note at `foldRight` would have saved the try. Small.
- Std candidates, small each: `List.get (List.map (List.range n) f) i =
  Some (f i)` for `i < n` and `= None` past it (`getMapRange`,
  `getMapRangePast`; std has `getOr` forms only); `List.get (List.range
  n) i`; a `List.maximumBy`-style "every member is below the fold's
  maximum" (`widthCovers`).
- Std has no image of a set: `Set.map` exists, but no lemma relates its
  members to `f`'s; the proofs used lists with `List.memDistinct`,
  `List.memMapElim` and `List.memMap`, which were all there and found by
  `search`.

### 4. Smaller things

- A recursive definition or theorem whose result is a defined function
  type takes a pattern per argument of it: `AfterFolds: List Fold → (Dot
  → Prop) → Dot → Prop` needed `| Nil, marked, spot => …`, and
  `foldsHold`, whose conclusion `Holds …` is defined as a `(spot: Dot) →
  …`, needed a `spot` pattern too. The `E-ARITY` note said exactly that
  ("the result … unfolds to a function type, since `Holds` is defined as
  one"). Fine once known; surprising for `Holds`.
- Printed cases name two variables alike: `cases` on `landsOnly`
  reported "the case spot = { x = x✝, y = y✝ }, …, dot = { x = x✝, y =
  y✝ }", with `spot`'s and `dot`'s fields printed the same; and its note
  `lands: x✝ = x✝ ∧ …` looked like an equation of one variable with
  itself. Fix: number the daggered names. Small.
- `stitchwort audit` warns on `rowWidth` and `cellSomeInside`, whose
  hypotheses are membership in a function's output, as it does on
  parse hypotheses (SW-967 item 8): the same fix (try the namespace's
  test values) would cover both.
- Good: `cases` closed all four reflection goals (`landsFoldDot` on its
  own, `landsOnly` per component); `rewrite getMapRange _ (height dots)
  spot.y inY in …` found the function for its `_`; the `E-UNIVERSE`
  message for `if lt:` between proofs gave the `match
  Nat.decLessThan …` to write; `pick` with functions as values
  (`AlongX`, `AlongY`) read the axis in one line.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day13.main` on the input | 0.35 s user (0.38 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day13.Proofs Aoc.Year2021.Day13.Tests` | 2.6 s user (2.7 s) |
| `stitchwort audit Aoc.Year2021.Day13` (with the search) | 2.6 s |

123 lines of program, 63 of spec, 241 of proofs, 92 of tests.

### Ranked

1. `search --at` can't state a goal whose hypotheses mention a pattern
   variable listed after them, which is every goal after a `match` on a
   constructor with fields or in an equation-style induction (item 1).
2. A proof argument (`cases`) solved its call's holes before the
   expected type did, giving `spot = spot` (item 2).
3. `List.foldRight` doesn't compute on `Cons` (item 3).
4. Std has no `List.get` of a mapped range (item 3).

## Day 14: Extended Polymerization

A polymer template (a line of capital letters, each an element), a blank
line, then pair insertion rules `AB -> C`. A step puts, between every two
neighbouring elements whose pair has a rule, that rule's element; all
pairs are taken from the polymer before the step. Part 1 is the count of
the most common element less that of the least common after 10 steps;
part 2 the same after 40, when the polymer has about 20 trillion
elements. Answers on Matt's input (20 elements, 100 rules): 2712 and
8336623059567 (his Scala solution's); the puzzle's example gives 1588
and 2188189693529. Compiler: the installed release build of `main`,
1 November 2026.

### The program

Both parts count pairs. `countPairs` puts the template's neighbouring
pairs in a `Map (Char, Char) Nat`; a step (`stepCounts`) sends each
pair's count to the pairs it `becomes` (`a c` and `c b` if the rule
table, a `Map.fromList` of the rules, has `c` for it; itself if not), and
adds them up with `insertWith … Nat.add` (`addAll`). Every element but
the first ends exactly one pair, and a step never changes the first, so
an element's count is whether the first element is it plus the counts of
the pairs ending with it (`elementCount`). The answer (`spread`) is the
largest less the smallest of those counts, over the first element and
the second element of every counted pair, leaving out a count of 0 (none
is 0, but the filter saves proving it). Both answers were right on the
first run; all 15 tests passed on the first run, including the three
parse error messages, which came out as guessed.

The parser is `Parse.all input readManual`: `takeWhile1` of capital
letters, `blankLine`, then `lines readRule` (two `satisfy`s, `text " ->
"`, a `satisfy`). It then checks the one promise the proofs need
(`checkManual`, with a pure `firstRepeated`, the D2108 pattern): no two
rules are for the same pair ("two rules for the pair AB").

**The spec** (Spec/Spec.sw) builds the polymer. `insertionFor rules a b`
is what the rule for `a b` inserts (the first rule with that pair, via
`find`); `step` is

```stitchwort
def step (rules: List Rule): List Char → List Char
  | Cons a (Cons b rest) => Cons a (between rules a b ++ step rules (Cons b rest))
  | polymer => polymer
```

`afterSteps n manual` iterates it, and `answer n manual` is `spreadOf`
the result: over `polymer.distinct`, the largest `polymer.count (==
element)` less the smallest (`List.maximum`/`List.minimum`, 0 for an
empty polymer). Tests check the puzzle's polymers after 1, 2 and 4
steps, the length 3073 and the counts of B, C, H and N after 10 steps
by the spec, and the spec's own part 1 answer on the example (1588).

**The assumption.** `OneRulePerPair rules` is `List.Distinct (rules.map
(rule => (rule.left, rule.right)))`: no two rules are for the same pair.
It is needed: the program's table keeps the last rule for a pair
(`Map.fromList`), the spec the first, so `AB -> C` then `AB -> D`
disagree. The puzzle's inputs have one rule per pair; the parser checks
it. Not assumed: that every pair that turns up has a rule (the puzzle's
input does give one for all 100 pairs of its 10 letters). A pair with
no rule stays as it is, in the spec and the program alike, and a test
covers it. No assumption on the template either: an empty one gives 0 in
both.

### Proved, for every number of steps

In `Aoc.Year2021.Day14.Proofs` (Proofs/, 8 files, 512 lines):

- `spreadAfterCorrect (steps) (manual) (one: OneRulePerPair
  manual.rules)`: `spreadAfter steps manual = answer steps manual`.
  `part1Correct` and `part2Correct` are it at 10 and 40.
- `parseOneRulePerPair (input) (manual) (parsed: Fail.toResult (() =>
  parseManual input) = Ok manual)`: `OneRulePerPair manual.rules`; and
  `part1FromInput`, `part2FromInput`: `solvePart1 manual = answer 10
  manual` (and 40) with no hypothesis but the successful parse.
- **The pair abstraction commutes with a step.** `pairsStep`: the pairs
  of `step rules polymer` are the pairs of `polymer`, each replaced by
  what its rule makes of it: `List.zipWithNext (step rules polymer) =
  List.flatMap (List.zipWithNext polymer) (expand rules)`, a list
  equation, by induction (`expand` is the puzzle's side of `becomes`,
  stated with `insertionFor`).
- **The counts stand for the pairs.** `Represents counts polymer` says
  that for every `f: (Char, Char) → Nat`, the sum of each count times
  `f` of its pair (`weight counts f`, over `Map.toList`) is the sum of
  `f` over the polymer's pairs. Counting all functions at once makes
  the step a chain of equations (`stepRepresents`, a `calc` of five
  lines): the new counts' weight of `f` is the old counts' weight of
  `pair => sum of f over becomes pair` (`stepWeight`, from
  `weightAddAll`), which is that sum over the polymer's pairs
  (`Represents`), which is the sum of `f` over the flatMap
  (`List.sumByFlatMap`), which is over the stepped polymer's pairs
  (`pairsStep`). `becomesExpand` needs `OneRulePerPair`: `lookupRules`
  shows `Map.lookupLast` on distinct keys is `find`. `weightAddAll`
  rests on `specInsertWithWeight`, about `Map.Spec.insertWith`, which
  `Map.toListInsertWith` relates to the real map. `iterateRepresents`
  carries it through any number of steps.
- **Element counts come back.** `stepsKeepFirst` (any number of steps
  keeps the first element), `countByPairs` (an element's count in
  `Cons a rest` is `Bool.toNat (a == c)` plus the pairs ending with
  `c`), so `elementCountQuantity`: the program's `elementCount` is the
  element's count in the polymer the counts stand for.
- **Same counts, same answer.** `quantitiesInto` and `quantitiesBack`:
  the program's list of counts and the spec's have the same members (an
  element of the polymer ends a pair, `memAfterFirst`, which has a
  positive count and so is a key of the map, `pairCounted`); then
  `maximumSame` and `minimumSame` give the same largest and smallest.

Not proved: nothing left open. One hypothesis, `OneRulePerPair`, on the
`Correct` theorems, needed as said; the parser checks it and the
`FromInput` theorems drop it. No opaque definitions.

`stitchwort audit Aoc.Year2021.Day14` (with the counterexample search):
`audited 54 theorems: 0 failed, 2 with warnings, 52 passed`. The two
warnings are `part1FromInput` and `part2FromInput` (random texts never
parse; SW-967 item 8); the test theorem `smallParses` shows a parse
that succeeds. The search is "not applicable" to 30 theorems, among them
every one with `OneRulePerPair` (nothing decides `List.Distinct`), and
to those taking an `f`.

Breaking the program breaks the proofs: `becomes` giving `(c, pair.fst)`
for `(c, pair.snd)` fails `becomesExpand` (`E-REFL`, `[(a, c), (c, a)]`
against `[(a, c), (c, b)]`); `elementCount` testing `entry.fst.fst`
fails `elementCountWeight` with a counterexample (`first = 'a'`, `counts
= Map.fromList [(('a', 'b'), 1)]`, `c = 'a'`: left 2).

The proofs went quickly: most lemmas checked the first time they were
written out, `cases` proved `Ord.max` of two numbers is one of them, and
`omega` took the weighted sums as atoms.

### 1. `search --at`

Used on 5 goals. It closed none; once its "applies" list had the right
step (`List.sumByCong`, with the goal it leaves).

- **It missed a lemma used backwards.** On `List.sumBy xs (pair =>
  List.sumBy (expand rules pair) f) = List.sumBy (List.flatMap xs
  (expand rules)) f`, `Eq.sym (List.sumByFlatMap …)` closes it, and
  `stitchwort search 'List.sumBy (List.flatMap _ _) _'` lists
  `List.sumByFlatMap` first, but `search --at` offered only four
  rewrites (`zipWithNextZip`, `sumByReverse`, …). Fix: try each closing
  candidate's symmetric form too. Small-medium.
- **Lifted matches print by their internal names.** Goals and its
  "leaves" lines show `Aoc.Year2021.Day14.Proofs.expand.%match1 x
  (Std.Option.map …)`, `Map.lookupLast.%match1 (Char, Char) Char
  Std.Pair.instOrd key …`, `Ord.%compare ord key kk`, `Add.%zero`,
  `DecEq.%decide`: a definition whose body is a `match` is shown half
  unfolded, as a call of a lifted function no source names. The plain
  `check` goals do the same. Fix: print such a call folded back as the
  definition (`expand rules x`), or as the `match`. Small-medium.
- The first `search --at` took 41 s; the next ones 2 to 4.5 s (as SW-960
  item 8). It can't offer the induction hypothesis: on `pairsStep`'s
  inductive case, the closing proof was `rewrite pairsStepCons …,
  pairsStep rules (Cons b rest) in rfl`, and the recursive call isn't a
  candidate. Medium.
- Pattern search: `Ord.compare ?x ?y = Equal → ?x = ?y` found nothing
  (relaxed pass, one unrelated result): the law is the field `equal` of
  the `Ord` record, reached as `ord.equal x y e`, and fields of a class
  aren't searched. Fix: index class laws as lemmas (`Ord.equal`).
  Small-medium.

### 2. Inference: holes that don't say so

Both are the elaboration-order family (SW-963 item 2, SW-969 item 2),
with a new symptom: no error at the hole, only a failing `omega` whose
atom contains it.

- `sumByPositive (entry => entry.snd * Bool.toNat (entry.fst == pair))
  (Map.toList counts) (omega […])`: the lambda comes before the list
  that fixes its parameter's type, and `entry.snd` became a hole: the
  `omega` goal read `?15 counts polymer represents pair member x * …`.
  No `E-CANNOT-INFER`. Workaround: `(entry: ((Char, Char), Nat)) => …`.
- `positiveMember c (Cons first tail) (omega [equal, same, positive])`,
  where `positiveMember` takes `[auto eq: DecEq a]`: `omega` ran before
  the instance was found, so its goal had `DecEq.%decide (… first tail
  counts represents v member c left✝ same) first c` where the facts had
  `Std.Char.decEq first c`, and failed. Workaround: `let counted: 0 <
  List.count (Cons first tail) (== c) := omega […]` first. Fix: solve
  `auto` arguments before checking later explicit ones, or report an
  unsolved hole in an `omega` goal as such. Medium.

### 3. Std

- **`List.maximum` has no lemmas**; `List.minimum` has `minimumSome`,
  `minimumExists`, `minimumEmpty`. `Maximum.sw` here (60 lines) copies
  them for `Nat` (`maximumSome`, `foldMaxGeStart`, `foldMaxGeMember`,
  `foldMaxMember`, `maximumNone`). Std candidate: the `Ord` versions.
  Small.
- **No decision procedure for `List.Distinct`.** With `DecEq` it is
  decidable, but the counterexample search says "nothing decides
  `Std.List.Distinct …`: no way to decide `Std.List.Distinct …`" (the
  same text twice) for every theorem taking `OneRulePerPair`, so the
  main theorems got no search, and breaking `becomes` gave no
  counterexample. Fix: a `Decidable (List.Distinct xs)` instance for
  `DecEq a`; say the reason once. Small.
- Std candidates, small each: `countPositive`/`positiveMember` (`c ∈ xs
  ↔ 0 < List.count xs (== c)`; `search '(?x: _) ∈ ?xs → 0 < List.count
  ?xs _'` found nothing); `sumByPositive` (a positive `sumBy` has a
  member with a positive term); `Map.lookupLast` on distinct keys is
  `find` (`lookupRules`, generalised); the weight of `Map.insertWith …
  Nat.add` (`specInsertWithWeight`, `weightInsertWith`: a sum over a
  map's entries gains `n * f key`); `compareEqual` (`Ord.compare x y =
  Equal → x = y` as a named theorem); `countByPairs` (an element count
  from `zipWithNext`).
- Good: `List.sumByFlatMap`, `List.sumByMap`, `List.sumByMulLeft`,
  `List.sumByCong`, `List.countSumBy`, `List.countLtMem`,
  `Map.getFromList`, `Map.toListInsertWith`, `List.memDistinct`,
  `List.memMapElim`, `List.memFilter(Intro)` were all there.

### 4. Messages and smaller things

- Good: `Some { left = 'C', … }` in a test said "`Some` has no field
  `left` … to build the `Rule` it holds, write `Some ({ … })`".
  `rewrite none in earlier` (meant for the hypothesis) said "`earlier`
  has … name it with `at`". `rewrite t at gives` after `match t:` said
  "`gives` is already refined: use it as it is". `if h:` between proofs
  gave the `match Nat.decLessThan 0 (f x)` to write.
- Seen again: the context lists `e: insertionFor rules a b = Some c`
  above `c: Char` (SW-969 item 1); `cases` printed `a` and `b` both as
  `MkChar code✝ valid✝` (SW-969 item 5); `∃ (x: a) => x ∈ Cons x rest`
  for a bound `x` beside the pattern's `x` (SW-967 item 5); `Represents`
  being a function type needed an `f` pattern in `iterateRepresents`
  (SW-969 item 6, the message said exactly what to add).
- No eta for pairs (SW-960 item 4): `tableInsertion` is stated for `(a,
  b)` and `becomesExpand` matches `pair` as `(a, b)` first, since
  `insertionFor rules pair.fst pair.snd` looks for `(pair.fst,
  pair.snd)`, not `pair`.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day14.main` on the input | 0.30 s user (0.36 s) |
| `stitchwort check --no-cache Aoc.Year2021.Day14.Proofs Aoc.Year2021.Day14.Tests` | 2.8 s user |
| `stitchwort audit Aoc.Year2021.Day14` (with the search) | 3.6 s |

124 lines of program, 42 of spec, 512 of proofs, 69 of tests.

### Ranked

1. Holes from elaboration order show up only inside a failing `omega`
   goal, not as an error at the hole (item 2).
2. `search --at` doesn't try a lemma backwards (`Eq.sym`), and prints
   lifted matches by internal names (item 1).
3. No `Decidable (List.Distinct xs)`: the counterexample search skips
   every theorem with that hypothesis (item 3).
4. No `List.maximum` lemmas (item 3).

## Day 15: Chiton

The input is a map of a cave, one digit per position: its risk level. A
path moves up, down, left or right from the top left to the bottom right,
and its total risk adds up the levels of the positions it enters (not the
start). Part 1 asks for the lowest total risk. Part 2 asks the same of the
full cave: the map repeated as 5 by 5 tiles, each tile's levels the first
tile's raised by the tile's row plus its column, with levels past 9
wrapping round to 1. Answers on Matt's input (100 by 100, so 500 by 500
for part 2): 656 and 2979 (his Scala solution's); the puzzle's 10 by 10
example gives 40 and 315. Compiler: the installed release build, on
`main` at 8ee89482, 1 November 2026.

### The program

Both parts are std's Dijkstra search, `Graph.distances`, on one kind of
map: `RiskMap = { height, width, level: Position → Nat }`. Its graph's
edges step to each neighbour on the map, costing the neighbour's level;
its `states` are every position (`edgesListed` in `Steps.sw` proves the
edges stay in them). The search starts at the top left for 0, and the
answer is what it finds for the bottom right. Part 1's map reads the
cave; part 2's computes each level from the first tile's, at the
position's row and column modulo the cave's height and width, raised by
the quotients and wrapped once (`wrap`: past 9, take 9 away). The full
cave is never built. Levels are looked up in a `Map Nat (Map Nat Nat)`
built with `Map.byPosition`, since `List.getOr` is linear.

`Position` and its four `neighbours` are day 9's
(`import Aoc.Year2021.Day09 (Position)`), as are the spec's `adjacent`
and its lemmas (`adjacentNeighbour`, `neighbourAdjacent`,
`rightAdjacent`, `downAdjacent`).

The parser reads each line with `many1 digit` and then checks (`checkCave`,
the D2108 pattern) that the first row has a digit and every row is as
long as the first.

Both answers were right on the first run.

**The spec** (`Spec/Spec.sw`). `levelAt cave position` is the digit there,
`None` off the map. A path (`isPath levels from steps to`) is the list of
positions entered, each `adjacent` to the one before and on the map;
`totalRisk` adds their levels. `LowestRisk levels target answer` says some
path from the top left to `target` has total risk `answer`, and every such
path has at least that. Part 1 is `LowestRisk (levelAt cave)
(bottomRight height width)`. Part 2's levels are `tiledLevelAt`, a
function of the position: off the 5h by 5w map, none; otherwise the
level at the remainders, raised `row / height + column / width` times by
`raise` (9 goes to 1, anything else up 1), as the puzzle says it, one tile
at a time. `Rectangle cave` is the puzzle's promise: a digit, and every
row as long as the first.

### Proved

In `Aoc.Year2021.Day15.Proofs` (`Search.sw`, `Levels.sw`, `Answers.sw`,
`Parse.sw`, 370 lines) and `Steps.sw`:

- `lowestRiskCorrect`: for every `RiskMap` with `0 < height` and `0 <
  width`, `LowestRisk risks.levelAt (bottomRight height width)
  risks.lowestRisk`. A walk in the graph is a spec path costing its total
  risk (`walkPath`), and a path is a walk (`pathWalk`, `pathWalkCost`).
  `Graph.distancesShortest` gives the rest: what it finds for the target
  is some walk's cost (`cheapestPath`), and no walk costs less
  (`noCheaperPath`). The target is found at all because a path reaches it
  (`routePath`: along the top row, then down the last column).
- `levelsAgree` and `tiledLevelsAgree`: on a `Rectangle`, the program's
  maps have the spec's levels at every position. The tiled one rests on
  `iterateRaise`: raising a level `count` times is `wrap (level +
  count)` while `level ≤ 9` and `level + count ≤ 17` (a tile is at most
  4 + 4 away), plus `Nat.modLess` and `Nat.divLeOfLtMul`.
- `part1Correct (cave) (rectangle: Rectangle cave): Part1Answer cave
  (solvePart1 cave)` and `part2Correct (cave) (rectangle: Rectangle
  cave): Part2Answer cave (solvePart2 cave)`. The level functions are
  moved across with `Quot.funext` and `J`.
- `parseRectangle`: if `parseCave` reads `input` as `cave`, `Rectangle
  cave`. So `part1FromInput` and `part2FromInput` hold for every input
  the parser accepts, with no hypothesis.
- **Whether 0 must be excluded: no.** The puzzle's levels are 1 to 9, and
  the parser accepts 0. The theorems don't need it excluded: a 0 is a
  step that costs nothing, and `iterateRaise` needs only `level ≤ 9`,
  which `Fin 10` gives (`levelBelow10`); `raise` from 0 never passes 9 in
  8 steps.
- Tests: the example's answers; the program's levels against the spec's
  over the example and its full cave (52 by 52, past the edges); the full
  example's first row from the puzzle; the puzzle's single-8 tiling;
  paths and their risk in spec terms; one position, zeros, a cheaper path
  round a wall; the parser's errors; the real input.

Nothing is left unproved, and no hypothesis was added beyond the
puzzle's promise, which the parser is proved to keep. No opaque
definitions. `Quot.sound` is the only axiom (through `Map`, which is a
quotient, and `Quot.funext`). `stitchwort audit Aoc.Year2021.Day15`:
`audited 35 theorems: 0 failed, 0 with warnings, 35 passed`; but the
counterexample search ran on none of the main theorems (item 5).

Breaking the program breaks the proofs: `wrap` taking 8 for 9 fails
`wrapLarge` with a counterexample (`level = 10`); starting the search at
1 for 0 fails `lowestRiskCorrect` (`E-REWRITE-NOTHING` at its `rewrite
got`: the found cost isn't the program's answer any more).

### 1. Performance

`stitchwort run Aoc.Year2021.Day15.main` takes 17.6 s (user), 20.3 s with
`--no-cache` (as the answer test runs it), 4.5 s with `--native` and
2.9 s with `--js`. Part 1 searches 10,000 positions, part 2 250,000.
Where part 2's time goes, measured with throwaway `main`s on the input:

- **Std's `Map` and `Set` in the interpreter.** Inserting 250,000 `Nat`
  keys, in order, into a `Map Nat Nat` took about 1.7 s (about 7 µs an
  insert); with `Position` keys (a record of two `Nat`s), about 3.8 s.
  The search does about a million `Set (Nat, Position)` inserts and
  `popMin`s and 250,000 `Map` inserts, so most of the 15 s is there.
  Computing every position's edges, with their levels, takes 1.6 s. Fix:
  a priority queue in std for Dijkstra (a pairing or binary heap, with
  the same `SearchResult` proof) (medium); runtime-backed `Map`/`Set`
  (large). A `Graph.distancesTo target` that stops when the target is
  settled wouldn't help here (it is the farthest position) but would
  elsewhere (small-medium).
- **A field read in a closure is recomputed on each call.** `Cave.tiles`
  first wrote `position.row % cave.height` inside the `level` lambda:
  `cave.height` is `cave.rows.length`, so every level computed the
  length of a 100-element list four times. The run took 31.7 s; with
  `let height := cave.height` outside the lambda, 17.6 s. The proofs
  didn't change (the `let` computes away). Nothing warns about this.
  Fix: a line in the performance notes (small); hoist closed
  subexpressions out of lambdas when compiling (medium).
- The answer test (`year2021_day15` in `aoc_answers.rs`) took 23 s in
  `task test:one`, about a third of the merge tier's 60 s, more than any
  other day. Proposal (not done): run this day with `--js` or `--native`
  in the merge tier and interpreted in the daily one, or move it to the
  daily tier. `Tests/Input.sw`'s part 2 test takes about 17 s under
  `stitchwort test` (cached after).

### 2. Std's `Graph` fitted well

`Graph.distancesShortest` is exactly the puzzle's "lowest total risk"
once a walk is related to a path: the day's own proofs are the
walk/path correspondence (40 lines), the levels (100) and a path to the
target. Smaller things:

- A record field only for termination (`states`, every position) is
  built at run time (SW-960 item 1): 250,000 positions here, 0.1 s.
- Std candidate: "a walk reaches the target, so the search finds it, for
  no more" is `And.right (Graph.distancesShortest …)` applied to seven
  arguments then taken apart; a named `Graph.distancesReach` (the
  target's `get` is `Some d`, `d` a walk's cost and at most any walk's)
  would say it. Small.
- Std candidate: a grid graph. Days 9 and 15 each build `positions`
  (every row and column), prove each edge stays in it (`edgesListed`,
  30 lines each) and relate neighbours to adjacency, and this day
  imports day 9's `Position` type to reuse its lemmas. A std grid module
  (positions, four neighbours, adjacency, a `Graph` of a grid with a cost
  per cell) would serve both (as SW-960 and SW-965 ask). Medium.

### 3. Division needs a proof, everywhere

`/` and `%` need `d ≠ 0`, so the program's full cave is `if tall:
cave.height != 0 then if wide: cave.width != 0 then cave.tiles else …`
with `Cave.tiles` taking `[auto tall] [auto wide]`, and the spec's
`tiledLevelAt` has the same two `if`s. Each proof about them matches on
`Nat.decEq cave.height 0` and `Nat.decEq cave.width 0` first, which
refines both sides well. A cave without a row has no tiles, so this is
only noise. Fix: total `Nat.div`/`Nat.mod` with `x / 0 = 0` (Lean's),
or variants (`Nat.divOr`) for code that knows nothing better; a design
question. Small to medium.

### 4. `rewrite` with an equation between functions

`part1Correct` first was `rewrite same in lowestRiskCorrect …`, with
`same: levelAt cave = cave.risks.levelAt` (from `Quot.funext`). It
failed `E-TYPE-MISMATCH`, with both sides printed as `(∃ (steps: List
Position) => isPath … … steps … = True ∧ Std.List.foldLeft steps 0 … =
Option.getOrElse … 0) ∧ …`: the difference is somewhere inside a `…`. The
same with an ascribed `let found: LowestRisk cave.risks.levelAt … :=
…` then `rewrite same in found`. `J (levels _ => LowestRisk levels …)
found (Eq.sym same)` checked at once. Rewriting `<- height` (`cave.tiled.height
= 5 * cave.height`) in part 2 failed the same way, and `J` over the
target worked. Why `rewrite` failed is a guess (speculative): the goal
is searched as it computes, so `5 * cave.height` also occurs inside the
unfolded `solvePart2`, and a function's occurrences inside lambdas may
be rewritten unevenly. Fix: when a mismatch's two sides print the same,
print the first differing subterm instead of `…` (small-medium; as
SW-963 item 2's "the … hid what was stuck").

### 5. The counterexample search ran on none of the main theorems

`stitchwort audit --verbose`: every theorem about a `RiskMap` says "not
applicable: no inputs for `risks`" (a record with a function field), and
every one with `Rectangle cave` says "nothing decides `1 ≤
Std.List.length (Std.List.headOr cave.rows []) ∧ ((row: List (Std.Fin
10)) → Std.List.Any (y => y = row) cave.rows → …`". So breaking the
program got no counterexample except in `wrapLarge`. Fix: decide `(x) →
x ∈ xs → P x` as `xs.all` (small-medium); make inputs for a function
field from a finite table (medium).

### 6. `search --at`

- Used on four goals. It closed the two that one std lemma closes:
  `n / d ≤ 4` from `n < 5 * d` (`Nat.divLeOfLtMul n 4 d omega`,
  `afterObligations`), and `n % d < d` (`Nat.modLt`). A plain search
  `(?n: Nat) < ?k * ?d → ?n / ?d < ?k` had missed the first: the lemma
  says `Succ b * d` and `≤ b`.
- At `position ∈ risks.positions` (a `flatMap` of `range`s) it listed
  `List.lastMem`, `List.memDedupElim` and two other days' lemmas, not
  `List.memFlatMapIntro`: the goal shows `flatMap` unfolded into
  `List.concat (List.map …)` (as SW-965 item 3). At `found ≤ totalRisk
  …` (the minimality, which `Graph.distancesShortest` gives) it listed
  `Bool.canonicalTrue`, 2025 day 9's `outsideFlagZero` and day 13's
  `shownHash`: a theorem whose conclusion is a defined `Prop`
  (`Graph.Shortest`, an `And` of two `∀`s) isn't a candidate for either
  half. Fix: index the conjuncts of such conclusions (medium).
- The first query on a file took 41 to 44 s each time, the next one on
  the same file 4.5 s (as SW-960 item 8).

### 7. Messages

- Good: the `match`-refinement notes. `rewrite onMap at found` after
  `match onMap:` said "`found` is already refined: use it as it is";
  `inRows below` after `match below:` said "both sides of what's expected
  are `True`, so `rfl` proves it"; a mismatch in `pathWalk` said the goal
  had been refined and pointed at the inner `match` of day 9's
  `neighbours`. `Cons { row, … } (…)` said to bracket the record.
  `E-ARITY` on `heightNotZero` said that `Not` adds an argument.
- **But not every error says it.** `Bool.andLeft _ _ rest2`, with `rest2`
  refined by the `match` to `False = True`, was `E-UNSOLVED` "can't work
  out an implicit argument" at the first `_`, with no word of the
  refinement. Fix: the same note when an argument's type was refined.
  Small.
- After `match h: Nat.decEq cave.height 0`, the goal printed the
  `Map.byPosition` table computed into `Map.Raw.fromListChecked …
  Map.Spec.isAscending …` and `Quot.mk { tree = Tip, … }` three times
  over (several thousand characters), and `levelAt` as
  `Aoc.Year2021.Day15.Spec.levelAt.%match1 …` (SW-971 item 3). The two
  `No` patterns' proofs both printed as `refutation✝` (SW-969 item 5).
- Errors are printed twice when a namespace fails to load
  (`E-UNKNOWN-NAME` for `Position` in `Steps.sw`, each error twice).
  Small.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day15.main` on the input | 17.6 s user (20.3 s with `--no-cache`) |
| the same with `--native` / `--js` | 4.5 s / 2.9 s |
| `stitchwort check --no-cache Aoc.Year2021.Day15.Proofs Aoc.Year2021.Day15.Tests` | 3.7 s user |
| `stitchwort audit --no-cache Aoc.Year2021.Day15` (with the search) | 4.2 s |

130 lines of program and 34 of its graph lemmas, 75 of spec, 370 of
proofs, 68 of tests.

### Ranked

1. Part 2 takes 17.6 s interpreted, mostly in std's `Map` and `Set`
   (about 7 µs an insert, twice that with record keys); its answer test
   takes a third of the merge tier (item 1). Fix: a heap for Dijkstra;
   tier the test.
2. A field read inside a closure (`cave.height`, a list length) was
   recomputed per call and doubled the run (item 1). Fix: document it;
   hoist when compiling.
3. The counterexample search ran on none of the main theorems: no inputs
   for records with function fields, nothing decides a `∀` over a list's
   members (item 5).
4. `rewrite` with an equation between functions failed with a mismatch
   whose two sides print alike; `J` worked (item 4).
5. `/` and `%` need a proof, so the tiling carries two `if`s through the
   program, the spec and two proofs (item 3).
6. A std grid module, now evidenced by a type imported across days
   (item 2).

## Day 16: Packet Decoder

The input is one line of hexadecimal: a transmission, four bits a digit,
holding one packet. A packet starts with a three-bit version and a
three-bit type id. Type 4 is a literal number, written as groups of four
bits, each after a bit saying whether another group follows. Every other
type is an operator holding sub-packets: a length type bit, then either
the sub-packets' total length in bits (15 bits) or their number (11
bits), then the sub-packets. Bits after the outermost packet are padding.
Part 1 adds up the versions of every packet in the tree; part 2 evaluates
it (types 0 to 3: sum, product, minimum, maximum; 5 to 7: greater than,
less than, equal to, as 1 or 0). Answers on Matt's input (1,350 digits):
901 and 110434737925 (his Scala solution's). Compiler: the installed
release build of `main`, 1 November 2026.

### The program

`readBits` turns each digit into its four bits (`hexValue`, then
`Nat.testBit`), and `readPackets` reads packets from the bits into a tree:

```stitchwort
type Packet =
  | Literal (version: Nat) (groups: List Nat)
  | Operator (version: Nat) (operation: Operation) (lengthType: LengthType) (subPackets: List Packet)
```

The tree keeps what the bits say: a literal's groups (not just its
value) and an operator's length type, so that the bits of a packet are a
function of it. Both parts are folds: `versionSum` and `evaluate` (with
`apply` for each operation; a comparison looks at the first two values).

`readPackets (wanted: Wanted) (bits)` reads `Packets n` (that many
packets) or `Filling` (packets until no bits are left; a total-length
operator's sub-packets are read this way from exactly that many bits).
One function does all of it, since `decreasing` takes no mutual
definitions; its measure is `bits.length`, and each recursive call is
guarded by `if shorter: rest.length < bits.length`, checked at run time
(item 6). `parsePacket` then checks the puzzle's promise
(`checkOperators`, the D2108 pattern with a pure `badOperator`): a
minimum or maximum has a sub-packet, a comparison exactly two.

Both answers were right on the first run, as were all the tests.

**The spec** (Spec/Spec.sw) writes a packet out as the puzzle describes:
`bitsOf width n` is a number in a field (the last bit is whether it is
odd, the bits before it are its half), `groupBits` flags each group with
1 except the last, and `encode`/`encodeAll` lay out a packet: version,
type id, then the groups, or the length type bit, the length or count
field and the sub-packets. `wellFormed` says the numbers fit their
fields (version below 8, groups below 16 and at least one, the
sub-packets' length below 2^15 or their number below 2^11): only those
packets have this encoding. `transmissionBits` reads the input's digits
by the puzzle's table. Part 1 is `versionTotal`: the sum of `versionOf`
over `packetsIn` (the packet and every packet inside it, as a list).
Part 2 is a relation, `HasValue packet value`, with `Values` for a list
of sub-packets and `Computes operation values value` for each operation
(a minimum is one of the values with none below it; a comparison takes
exactly two values). `promised` is the puzzle's promise.

Why an encoding function and not a relation: with the tree keeping the
groups and the length type, a packet has exactly one encoding, so
soundness is an equation (`bits = encode packet ++ rest`), and soundness
with completeness make the decoder exactly the encoding's inverse on
well-formed packets. A relation over a tree without those details (any
groups for the value, either length type) would say the same less
directly.

### Proved, for every input

In `Aoc.Year2021.Day16.Proofs` (Proofs/, 7 files, 758 lines, 68
theorems):

- **Soundness**, `readPacketsSound (wanted) (bits) (packets) (rest)
  (read: readPackets wanted bits = Some (packets, rest))`: `bits =
  encodeAll packets ++ rest ∧ allWellFormed packets = True ∧ Done wanted
  packets rest` (`Done`: that many packets, or no bits left). By
  recursion on `bits.length`, through every branch of the decoder:
  `readNumberSome`, `splitFieldSome`, `readGroupsSome` and
  `operationOfSome` say what each piece read. For one packet,
  `readPacketSound`: `bits = encode packet ++ rest ∧ wellFormed packet =
  True`.
- **Completeness**, `readPacketComplete (packet) (formed: wellFormed
  packet = True) (rest)`: `readPacket (encode packet ++ rest) = Some
  (packet, rest)`, whatever `rest` is. `stepComplete`, `countComplete`
  and `fillComplete` are defined together, recursing structurally
  through the tree and its nested `List Packet`. Each decoder step is a
  lemma over variables (`literalStep`, `totalStep`, `countStep`), so the
  big bit patterns are only instantiated, never rewritten.
- **The packet is unique**, `encodingUnique`: if `encode first ++ rest1
  = encode second ++ rest2` with both well formed, then `first = second
  ∧ rest1 = rest2`.
- **The parser's guarantee**, `parsePacketReads (input) (packet) (parsed:
  Fail.toResult (() => parsePacket input) = Ok packet)`: there are
  `bits` and `rest` with `transmissionBits input.trim.toList = Some
  bits` (every character is a hexadecimal digit, and the bits are
  theirs), `bits = encode packet ++ rest`, `rest.all (bit => not bit) = True` (only
  zero padding follows the packet; `decodeTransmission` rejects anything
  else with "the bits after the packet aren't all zero padding", SW-1022),
  `wellFormed packet = True` and `promised packet = True`.
- **Part 1**, `part1Correct (packet)`: `solvePart1 packet = versionTotal
  packet`, for every packet, with no hypothesis.
- **Part 2**, `part2Correct (packet) (formed: wellFormed packet = True)
  (kept: promised packet = True)`: `HasValue packet (solvePart2
  packet)`. `wellFormed` is needed for literals (the program reads groups
  as base 16, the spec as four bits each, which agree only below 16);
  `promised` for minimum, maximum and the comparisons, whose spec value
  doesn't exist otherwise. `part2FromInput` drops both through
  `parsePacketReads`: for every input the parser accepts, the answer is
  the spec's value of the transmission's packet.
- Tests: the puzzle's examples (the literal 2021's bits and tree, both
  operator examples as trees, all of part 1's and part 2's examples, by
  the program and the spec), the spec's encoding of each example packet
  is its bits up to the padding, the digits against the puzzle's table,
  the parser's errors, and the real input.

Not proved: nothing left open. No hypothesis beyond `wellFormed` and
`promised`, which the parser is proved to give. No opaque definitions.
Day 14's `maximumSome` is imported (std has no `List.maximum` lemmas,
SW-971 item 7).

**The proof found a bug.** The first decoder read a total-length
operator's sub-packets from `after.take length`, which is shorter than
`length` when the transmission ends early, and accepted the result. The
tests all passed. Soundness couldn't hold (the encoding writes the
sub-packets' real length), and `3801934528B` (an operator claiming 100
bits, holding 22) was read as a packet. Now `splitField` fails unless
the whole field is there, and a test covers it.

`stitchwort audit Aoc.Year2021.Day16`: `audited 77 theorems: 0 failed, 6
with warnings, 71 passed`. The warnings are narrow hypotheses, not
contradictory ones: `part1FromInput` and `readPacketSound` (random texts
and bits never parse; SW-967 item 8; `smallParses` and `literalPacket`
in the tests show both can hold), `literalStep`, `totalStep` and
`countStep` (a decoder step's pieces all read; completeness instantiates
them), and `soundStep` (two list equations, which `bits := encode packet
++ (encodeAll more ++ left)` satisfies).

Breaking the program breaks the proofs: `nextWanted` keeping the count
(`Packets (Succ count)` for `Packets count`) fails `doneNext` and
`countComplete` (`E-REFL`); a literal's value as `value * 10 + group`
fails `evaluateCorrect` (`E-REWRITE-NOTHING`: the program's fold isn't
the spec's any more). Two other breaks crashed the compiler (item 1).

**The digit reader (SW-998, 1 November 2026).** `readDigits` was
written by hand (`withIndex.map` of `Fail.need (hexValue char)`) so that
`readDigitsBits` could be proved. It is now `Parse.line input.trim (() =>
many hexDigit)`, `hexDigit` a `satisfy` then `need (hexValue char)`, and
`readDigitsBits` (statement unchanged) follows from std's
`Parse.lineReads`, `readsMany`, `readsSatisfy` and `readsNeed`. `line`
allows a final line break, which a trimmed text can't end with: std's
`Text.trimLast` says so. Proofs/Parse.sw's parser part went from 29
lines to 27; Day16.sw from 274 to 278. A bad digit now says "column 4:
expected a hexadecimal digit or the end of the line, got 'G'".

**Completeness (SW-1626).** `Proofs/ReadsBack.sw` (`Complete.sw` was taken by
the decoder's), 81 lines, about 6 minutes. The parser's soundness theorem is
`readBitsHex`: what `readBits` reads has the puzzle's `transmissionBits`. Its
converse, `parseComplete`, takes `transmissionBits input.trim.toList = Some
bits` and gives `readBits input = Ok bits`. `hexValueOf` (16 arms, like
`hexAgree`) turns a character the puzzle's table knows into one the program's
`hexValue` reads, with the same bits; `runsHexDigit` and `declinesHexDigitEnd`
are the digit parser's pieces (`runsBind` over `runsSatisfy` and a `need` on
`Some`); `runsDigits` builds the steps of `many hexDigit` by recursion on the
characters; `runsWithFinalLineBreakNone` and `Parse.runsLine` finish it.
`writtenUnique` is two `parseComplete`s and `okInjective`: the spec
(`transmissionBits`) is already a function of the text, so uniqueness was never
in doubt, and it holds. The values `readDigits` gives are not in the spec (only
their bits are), so nothing is said of them beyond that. The six audit warnings
are earlier theorems' (`readGroups*`, `soundStep`, `literalHere`, `countHere`),
not new. Dropping the `trim` from `readDigits` fails `Parse.sw`'s `readDigitsBits`.

### 1. BUG: `cases` panics

Flipping `if more then` to `if not more then` in `readGroups`, or
reading the length field with `readNumber 14`, and checking the proofs
gives no error but

```
thread '<unnamed>' panicked at crates/core/src/value.rs:1011:31:
index out of bounds: the len is 1 but the index is 18446744073709551615
```

(exit 101), from `stitchwort_elab::cases::take_apart` → `value::eval` →
`value::quick`: a `Term::Var` index past the environment. Each `cases`
whose hypothesis `read` no longer matches the program panics: with
`readNumber 14`, any one of the six `cases` under `match l: readNumber
15 fields` in `readPacketsSound`; with `if not more`, the `| None =>
cases` in `readGroupsSome`. A standalone file of 74 lines reproduces it
(the day's `readGroups` with `if not more`, `bitsOf`, `groupBits`, five
`Bits.sw` lemmas and `readGroupsSome`); the `let written: bitsOf 4
(Nat.fromBits [a, b, c, d]) = [a, b, c, d]` before the `match` is needed
(without it, an ordinary `E-CASES`). Smaller attempts didn't panic. To
reproduce in the repo: make the `readGroups` change and run `stitchwort
check Aoc.Year2021.Day16.Proofs`. Fix: find the unscoped variable
(perhaps a `let`-bound hypothesis evaluated in the wrong environment;
speculative) (small-medium). High value: rule 6 of the proving guide
(break the program) is where it shows.

### 2. Checking `bitsOf` on an unknown number is exponential in the width

Comparing `bitsOf w n ++ …` for an unknown `n` by computing takes time
that doubles with each bit. On a scratch file,

```stitchwort
def bitsOf: Nat → Nat → List Bool
  | 0, _ => Nil
  | Succ width, n => bitsOf width (n / 2) ++ [n % 2 == 1]

def wrap (w: Nat) (n: Nat) (xs: List Bool): List Bool := Cons False (bitsOf w n ++ xs)

theorem t (n: Nat) (xs: List Bool) (ys: List Bool): wrap 15 n xs ++ ys = Cons False (bitsOf 15 n ++ (xs ++ ys)) := rfl
```

checks in 0.15 s with 9 for 15, 0.26 s with 13, 0.63 s with 15, 2.4 s
with 17 and 10.1 s with 19. A guess at the cause (speculative): the
nested `n / 2 / 2 / …`, each `/` or `%` copying its numerator as it
computes. The day's proofs hit it with the 15-bit length field:
`Aoc.Year2021.Day16.Proofs` takes 14 s to check cold (`Sound.sw` about
7 s, 6 s of it the total-length branch of `readPacketsSound`;
`Complete.sw` about 4 s; the rest 3 s), and it caused item 3's errors.
Workarounds used: state each step over variables (`fieldsCong`,
`totalStep`) and give lemmas their arguments. A `bitsOf` with one
division per bit (`n / Nat.pow 2 k % 2`) might avoid it (not tried: the
round-trip lemmas would need redoing). Fix: keep terms shared while
comparing, or compute `/` and `%` on unknowns without copying (medium).

### 3. Errors that hid the real problem

- **`rewrite` ran out of budget comparing a term with itself**:
  `E-REWRITE-BUDGET`, "the part of the goal, as it computes: `fields`;
  the rule's left side: `fields`" (also `rest` against `rest`, and
  `List.length (encodeAll subPackets)` against itself), in a goal
  holding `bitsOf 15` of an unknown length (item 2). The note ("about
  cost, not truth") is right, but identical terms shouldn't need
  computing. Fix: compare syntactically first (small). Workaround: a
  lemma over variables (`fieldsCong`).
- **`E-RESOURCE` "a value was too large to show … a call of `Eq.trans`",
  pointing at the whole theorem**, in place of a type mismatch, when a
  lemma's arguments were holes to be found from an expected type that
  had been computed (`consAppendCong False _ _ _ _ …` and `appendCong3 _
  _ _ _ _ _ …` against `bitsOf 15 …`). Found by replacing pieces with
  `?` one at a time (with a `?` open the error vanished, so the culprit
  was the piece whose `?` made it go). Workaround: write the arguments,
  and a typed `let` for each step. Also `soundStep _ after left _ more
  here …`: the packet hole wasn't solved before `here` was checked
  against `encode ?46 ++ after` (`E-TYPE-MISMATCH` with the computed
  side). The elaboration-order family (SW-963 item 2, SW-969 item 2,
  SW-971 item 1) with a new symptom: no location at all. Fix: unify with
  the expected type before computing it; print a mismatch without
  computing the term (medium).
- `rewrite halfOfDouble acc bit, parityOfDouble acc bit` (`(acc * 2 + b)
  / 2 = acc`, then `((acc * 2 + b) % 2 == 1) = b`) failed: the first
  rule had also rewritten the `/ 2` inside the `% 2` (as it computes,
  `x - x / 2 * 2`), leaving `x - acc * 2`. The message showed the goal.
  Workaround: the `%` rule first. Fix: a line in the `rewrite` docs
  (small).

### 4. `search --at`

Used on six goals. It closed one: `Nat.fromBits bits < Nat.pow 2
bits.length`, with `rewrite <- Nat.fromBitsFlipped bits in omega` (I
had found the lemma by grep). At `lengthBitsOf` its first rewrite
(`List.lengthSnoc`) was the right step.

- **Refused after a `_` pattern**: at `| Cons _ rest => ?` it said
  `E-SEARCH-AT` "can't be written as a statement of its own here", with
  "E-PARSE: unexpected character `✝`": the unnamed pattern variable.
  Fix: give such variables fresh names when writing the goal out
  (small). At `groupsValue`'s `Cons group rest` case: "unknown name
  `group`"; the goal has a lambda `(value group => …)` whose binder is
  also the pattern's name (the printer's capture, SW-967 item 5).
- **Hypotheses aren't tried as rewrite rules**: at `takeAppendLength`
  (`(xs ++ ys).take k = xs` with `h: xs.length = k`) and `soundStep`
  (`here: bits = encode packet ++ after`, `later: after = …`) it found
  nothing; `rewrite <- h in List.takeAppend xs ys` and `rewrite here,
  later in …` close them. Fix: try the context's equations as rewrites
  (small-medium).
- Each query took 14 s (27 s the first), mostly checking the namespace
  (item 2).

### 5. Lemma search and std

- `stitchwort search 'Nat.fromBits (_ ++ _) = _'` listed
  `Nat.fromBitsFrom` and `List.foldLeftAppend` first (62 s, cold, while
  a build ran). Std's `Nat.fromBits`, `Nat.fromBitsFrom` and
  `Nat.fromBitsFlipped` were all used.
- Std candidates: a fixed-width `Nat.toBits width n` with its round
  trips (`fromBitsOf`: `n < 2^width → fromBits (bitsOf width n) = n`;
  `bitsOfFromBits`: `bitsOf bits.length (fromBits bits) = bits`;
  `fromBitsSnoc`; `fromBitsBelow`), small; `List.takeAppend` and
  `List.dropAppend` with a length hypothesis (`takeAppendLength`),
  small; `Some (a, b) = Some (c, d) → a = c ∧ b = d`
  (`somePairInjective`), small; `List.maximum` lemmas (again).
- Seen again (SW-960 item 3): a `Bool` `if second < first` on `Nat` isn't
  `Decidable.toBool (Nat.decLessThan second first)`, so `match
  Nat.decLessThan second first` didn't refine the goal
  (`E-TYPE-MISMATCH`, "expected `… (if second < first then 1 else 0)`,
  but this has type `… 1`"). `match h: (second < first: Bool)` with
  `omega [h]` worked. `==` on `Nat` is `Nat.decEq`, and matching on that
  worked.

### 6. Writing the decoder

- **A later call's decrease can't come from an earlier recursive call.**
  After reading an operator's sub-packets, `readPackets later following`
  needs `following` shorter than `bits`: a fact about `readPackets`
  itself, which its own definition can't use. Lean would return a
  subtype (`{ rest // rest.length ≤ bits.length }`) or use fuel. Here
  each call has a run-time guard, `if shorter: following.length <
  bits.length` (three in a branch, each linear; the run is still 0.22
  s), and completeness discharges each with `match Nat.decLessThan … with
  | No longer => Void.exfalso (longer shorter)`, which worked well. Fix:
  this pattern as a worked example in the `decreasing` docs (small);
  results that carry their own decrease (large).
- **The wildcard after numeric patterns learns nothing**: in `match n
  with | 0 => … | 7 => … | _ => omega`, `omega`'s model was `n = 5`.
  Workaround: `| Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ k)))))))
  => omega`. Fix: give the wildcard arm `8 ≤ n` (or `n ≠ k` for each
  number above it) as a fact (small-medium).
- Good: `match e:` refined the `read` hypothesis through every branch of
  the unfolded decoder, so soundness was a walk down the program's
  matches; mutual inductive propositions (`HasValue`, `Values`) and
  theorems defined together over the nested `Packet` (`stepComplete`,
  `countComplete`, `fillComplete`) worked the first time; the three step
  lemmas checked as first written; `omega` proved `Bool` goals such as
  `(group <= 15) = True`; `rewrite … at (term) in` explained itself
  ("drop `in …` to use the rewritten term directly").
- Small: after each `match`, the context lists every superseded version
  of the matched hypothesis (`read✝` five times, with the decoder's
  lifted `%match` functions), which buries the current one. Fix: hide
  hypotheses a `match` replaced (small).

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day16.main` on the input | 0.22 s user (0.69 s with `--no-cache`) |
| `stitchwort check --no-cache Aoc.Year2021.Day16.Proofs Aoc.Year2021.Day16.Tests` | 14.0 s user |
| `stitchwort audit Aoc.Year2021.Day16` (with the search) | 8.5 s |

274 lines of program, 153 of spec, 758 of proofs, 91 of tests.

### Ranked

1. `cases` panics (index out of bounds in `value.rs`) when a proof stops
   matching the program: breaking the program crashed the compiler twice
   (item 1).
2. Computing `bitsOf w n` on an unknown `n` doubles with each bit; the
   proofs take 14 s to check, and it surfaced as budget and resource
   errors (items 2, 3).
3. `E-RESOURCE` "too large to show … `Eq.trans`" for the whole theorem
   in place of a located mismatch (item 3).
4. `search --at` refuses goals with an unnamed pattern variable (`✝`),
   and doesn't try hypotheses as rewrites (item 4).
5. A recursive call's result can't justify the next call's decrease, so
   run-time guards stand in (item 6).

## Day 17: Trick Shot

One line names a target area: a range of x and a range of y, ends
included. A probe starts at (0, 0) with a whole-number velocity. Each
step it moves by its velocity, drag moves its x velocity one toward 0,
and gravity lowers its y velocity by one. A velocity hits if the probe is
in the area after some step. Part 1 is the highest y any hitting velocity
reaches; part 2 counts the hitting velocities. Answers on Matt's input
(`x=155..182, y=-117..-67`): 6786 and 2313 (his Scala solution's); the
puzzle's example (`x=20..30, y=-10..-5`) gives 45 and 112. Compiler: the
installed release build of `main`, 1 November 2026.

### The program

It tries every velocity in a box and simulates each for a bounded number
of steps (`hitsWithin`), stopping early once the probe is `past` the
target for good: right of it and not moving left (`overshot`), left of it
and not moving right (`short`), or below it and falling (`fallen`). The
box is `1 ≤ dx ≤ right` and `bottom ≤ dy < -bottom`, the bound `-2 *
bottom` steps (`candidates`, `aimed`, `steps`). Part 2 is the length of
the hitting list; part 1 the largest `peak` over it, `peak` being
`triangle dy` (1 + 2 + … + dy, or 0 for `dy ≤ 0`). `solvePart1` is an
`Option`: `None` if nothing hits. The parser (`text`, `int`) fails unless
`0 < left` and `top < 0` (`placed`): the box depends on both. Both
answers and every test were right on the first run.

**The spec** (Spec/Spec.sw) is the puzzle's rules over every velocity and
every number of steps: `drag` (one toward 0, stays at 0), `move`, `after
n velocity` (`Nat.iterate`), `Within`, and `Hits target velocity := ∃ n,
Within target (after n velocity)`. Part 1 is `Highest target height`:
some hitting velocity reaches `height` at some step, and no hitting
velocity is higher at any step. Part 2 is `HittingCount target count`:
there is a list of `count` distinct velocities, and a velocity hits
exactly when it is in the list.

### Proved, for every target the parser accepts

In `Aoc.Year2021.Day17.Proofs` (Proofs/, 6 files, 317 lines, 44
theorems):

- **The step is the puzzle's**: `stepIsMove` (the program's `dx - sign
  dx` is `drag`), so `flightIsAfter`: the program's `flight n v` is the
  spec's `after n v`.
- **Closed form**: `yAfter`, `2 * y = 2 * y0 + n * (2 * dy + 1 - n)`
  after `n` steps (by `ring` with the induction hypothesis), and `dyAfter`.
- **Past is for good**: `pastStays` (each of the three ways lasts a
  step) and `pastNever`: a probe past the target is never in it again.
- **The simulation decides hitting within its bound**:
  `hitsWithinSound` (`hitsWithin target k probe = True` gives an `n ≤ k`
  with the probe in the target after `n` steps) and `hitsWithinComplete`
  (the converse), for any target: stopping early is safe.
- **The box and the bound**, for a target with `0 < left` and `top < 0`,
  and a velocity whose probe is in the target after `n` steps:
  `dxAtLeastOne` (else `short` at the launch), `dxAtMostRight` (else
  `overshot` after one step), `dyAtLeastBottom` (else `fallen` after one
  step), and `hitLate`: `2 * dy + 2 ≤ n ≤ -2 * bottom`. For `hitLate`,
  `n * (2 * dy + 1 - n)` is not negative while `n ≤ 2 * dy + 1` (the
  probe is at y ≥ 0, above the target), and at most `-n` after
  (`Int.mulNonneg` and a `ring` identity each). So `hitsCandidate`: every
  hitting velocity is one of `candidates`.
- **Peak**: `peakAbove` (no step is above `peak`; `consecutiveNonneg`,
  `0 ≤ d * (d + 1)`, is the key fact) and `peakReached` (after `dy`
  steps the probe is at `peak`).
- **Answers**, each assuming `0 < target.left` and `target.top < 0`:
  `hittingCorrect` (`Hits target v ↔ v ∈ hitting target`, for every
  velocity `v`), `hittingDistinct`, `part2Correct` (`HittingCount target
  (solvePart2 target)`), `part1Correct` (`solvePart1 target = Some h →
  Highest target h`) and `part1None` (`solvePart1 target = None →
  ¬Hits target v` for every `v`).
- **The parser's guarantee**, `parseTargetPlaced`: a target `parseTarget`
  reads has `0 < left` and `top < 0`. `part1FromInput`,
  `part1NoneFromInput` and `part2FromInput` state the answers for every
  input the parser accepts, with no hypothesis left.
- Tests: the example's answers (also as `rfl` theorems), the puzzle's
  worked velocities by the spec (7,2, 6,3, 9,0 and 6,9 hit after 7, 9, 4
  and 20 steps; 17,-4 misses) and by the program, 6,9's peak of 45, the
  box's size, `drag`, the parser's errors, and the real input.

Not proved: nothing left open. The two hypotheses, `0 < left` and `top
< 0`, are what the box needs (a target left of the start needs negative
`dx`; for one above the start this argument gives no upper bound on
`dy`), and the parser checks both. Nothing else is assumed, not even
`left ≤ right` or `bottom ≤ top`. No opaque definitions. Day 14's
`maximumSome` and `maximumNone` are imported.

`stitchwort audit Aoc.Year2021.Day17`: `audited 50 theorems: 0 failed, 2
with warnings, 48 passed`. Both warnings are narrow hypotheses:
`parseTargetPlaced` (random texts never parse; SW-967 item 8) and
`hitsCandidate` (random velocities never hit the random target). The
test theorem `exampleHitIsCandidate` applies `hitsCandidate` to 7,2 on
the example, so its hypotheses can hold.

Breaking the program breaks the proofs: `steps` one smaller fails
`hitsCandidate` and `hittingCorrect` (`E-OMEGA`, with the model `bottom =
-1`, `dy = 0`, `n = 2`: the bound is tight); `short` with `x ≤ left`
fails `pastOutside` with a counterexample (a probe at `left`, in the
target).

### 1. `omega` can't see through `i.toInt + 1 - 1`

On a scratch file, `theorem a (i: Nat): 0 ≤ i.toInt + 1 - 1 := omega`
and `theorem c (i: Nat): i.toInt + 1 - 1 = i.toInt := omega` both fail:
"`omega` can't prove `0 ≤ Std.Int.subNatNatFrom (i + 1) 1 (0 - i)`",
with that call as its only atom. The goal computes (`OfNat i + 1` to
`OfNat (i + 1)`, then the subtraction into `Int.subNatNatFrom`) before
`omega` reads it, and `omega` knows nothing about the call it computes
to. `0 ≤ i.toInt - 1 + 1` checks. It came up in `candidatesDistinct`
(`Int.toNat ((aimed target i j).dx - 1) = i`). Workaround: `ring` proves
the equation, and a lemma over a variable (`toNatBack z i (h: z =
i.toInt)`) keeps the computed form out. Fix: let `omega` read the
arithmetic as written, or teach it `Int.subNatNatFrom` (small-medium).

Fixed since SW-997: `omega` reads `i.toInt + 1 - 1` as written. `candidatesDistinct`
uses `omega` where it used `ring`; the variable-lemma workaround was never kept there.

### 2. `omega` has no `(p || q) = True`

`past` is three conditions joined by `∨`, and `cases` on `pastStays`
hit `E-CASES-BUDGET` (12 splits, 4 of them fallbacks on `probe` and its
fields; the note's advice, a fact deciding several cases, was right).
`omega` takes `(p && q) = True` as a goal and as a fact, and `(p || q) =
False`, but not `(p || q) = True` either way. Workaround: name the three
parts (`overshot`, `short`, `fallen`), prove each lasts by `omega`, and
put them together with `Bool.orElim`, `Bool.orLeft` and `Bool.orRight`;
a three-way `signCases` lemma took `Int.sign` apart. Fix: `omega` splits
a `(p || q) = True` fact and tries each side of such a goal (small).

Fixed since SW-997: `omega` settles a disjunction with one side refuted at once,
and `pastStays` is one `omega [signCases probe.dx]`. `overshotStays`,
`shortStays`, `fallenStays` and `dragKeepsSign` are gone (Box.sw's `fast`
takes the same `signCases` fact).

### 3. `search --at` and lemma search

Used on four goals. At `dyAfter`'s base case it said `omega`, `cases`
or `byDecision` closes it. At its step it offered three rewrites, the
first (`Nat.iterateSucc`) leaving the goal as it was (SW-963 item 6),
and not the induction hypothesis (SW-971 item 5). At `hittingDistinct`
its one `applies` result, `List.distinctFilter`, was the right step. At
the goal that leaves, `List.Distinct (candidates target)`, it found
nothing: `candidates` is a `flatMap`, the goal computes to `List.concat
(List.map …)`, and `List.distinctFlatMap` (which closed it) no longer
matches (SW-965 item 3, new evidence). The first query took 56 s
(building the index), the others 2 s.

I wrote `iterateCong` without searching first; 2024 day 22 has the same
lemma (`stitchwort search 'Nat.iterate _ _ _ = Nat.iterate _ _ _'`
lists both). Search found the rest of what I looked for
(`Bool.falseNotTrue` for `False = True → Void`).

Std candidates: `Nat.iterateCong` (two copies now) and `Nat.iterateKeeps`
(a property every step keeps holds after `n` steps), small;
`Int.toNat` lemmas (`0 ≤ z → (Int.toNat z).toInt = z`, `z = i.toInt →
Int.toNat z = i`), small; `Int.signCases` (`sign` is 1, 0 or -1 with the
sign of its argument), small; `0 ≤ d * (d + 1)` on `Int`, small;
`2 * Nat.sumBetween 1 k = k * (k + 1)` (with it the program could use
std's `sumBetween` for the triangle in place of its own `triangle`),
small.

### 4. Messages and smaller things

- **A negative number in a list whose type comes later**: in a test,
  `[(7, 2), …, (17, -4)].map (((dx, dy)) => … { dx, dy } …)` is
  `E-TYPE-MISMATCH` "a `Nat` can't be negative" at `-4`, though the same
  list without `-4` checks, its numbers becoming `Int` from the record
  the lambda builds. The negative check is made before the literal's type
  is known. Workaround: `([…]: List (Int, Int))`. The elaboration-order
  family (SW-963 item 2, SW-971 item 1) with a new symptom. Fix: postpone
  the check with the literal (small-medium).
- **A record literal right after a theorem's `:`** is read as an
  ability row: `theorem t: { dx = 7, dy = 2 } ∈ xs := …` is `E-PARSE`
  "expected `}`, but found `=`", with no hint. syntax.md says this for
  arrows. Workaround: `({ dx = 7, dy = 2 }: Velocity)`. Fix: a note
  suggesting the brackets when `=` follows a name there (small).
  Fixed (SW-1015): braces there are a row only when a type follows them,
  so the statement is now written `{ dx = 7, dy = 2 } ∈ …`.
- `cases`' open-case line in the break test listed fallback splits as
  `top = n✝.toInt` and a vacuous `n✝ ≤ n✝`, which made the case hard to
  read; the counterexample note under it was clear (small).
- Good: `ring [yAfter n (step probe)]` proved the closed form's step on
  `Int` with `Nat` casts first time, and `ring` the identities for
  `hitLate` and `twiceBelowPeak`; `omega` moved between `Nat` and `Int`
  through `.toInt` everywhere it was asked (`n ≤ steps target` from
  `n.toInt ≤ -2 * bottom` and `(Int.toNat (-2 * bottom)).toInt = -2 *
  bottom`); `Velocity.ext` and `rewrite same at (term)` built the
  candidate membership; `match e: Int.leq …` split on a comparison (and
  without `e:` it turned the goal `1 ≤ dx` into `True = True` and `False
  = True`, which is right but surprised me at first). Every proof file
  checked on its first or second try.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day17.main` on the input | 0.41 s user (0.97 s with `--no-cache`) |
| `stitchwort check --no-cache Aoc.Year2021.Day17.Proofs Aoc.Year2021.Day17.Tests` | 3.9 s user |

117 lines of program, 38 of spec, 317 of proofs, 60 of tests.

### Ranked

1. `omega` fails on `i.toInt + 1 - 1`: the goal computes into
   `Int.subNatNatFrom` first (item 1). Fixed since SW-997.
2. `search --at` misses `List.distinctFlatMap` once `flatMap` has
   computed (item 3; SW-965 item 3).
3. `omega` has no `(p || q) = True`, as a goal or a fact (item 2).
   Fixed since SW-997.
4. A negative literal is rejected as a `Nat` before its type is known
   (item 4).
5. Std lacks `Nat.iterate` congruence and invariant lemmas, `Int.toNat`
   lemmas and a `sumBetween` closed form (item 3).

### Moved onto the plane library (SW-1484, 6 Nov 2026)

`Target` is `Box YUp`, `Velocity` is `Coords YUp`, and `Probe` is
`{ position, velocity }` of those, instead of the flat `x, y, dx, dy`;
`inTarget` is `Box.contains` and the program's `step` adds with
`Coords.plus`. The answers are unchanged (6786 and 2313). Every proof moved
by renaming (`probe.dx` to `probe.velocity.x`, `velocity.dy` to
`velocity.y`, `(flight n v).y` to `.position.y`); no `omega` or `ring` call
changed, and `omega` reads `target.top` and `target.bottom` (which ask the
frame) without help. The spec's `Within` reads the box's `low` and `high`
corners directly, so it doesn't lean on the library's `top`/`bottom`. Gravity
being `y - 1` is now the type's doing (`YUp`), not a comment's.

## Day 18: Snailfish

Each line is a snailfish number: a pair whose two elements are regular
numbers or snailfish numbers. Adding two makes the pair of them, then
reduces it: while some pair is nested inside four pairs, the leftmost such
explodes (its left value goes to the nearest regular number on its left,
its right value to the nearest on its right, and it becomes 0); when none
can, the leftmost regular number of 10 or more splits into a pair of its
halves, rounded down and up; reducing stops when neither applies. A
number's magnitude is 3 times its left's plus 2 times its right's. Part 1
adds the lines in order and gives the total's magnitude; part 2 the
largest magnitude of `x + y` over two different lines, in either order.
Answers on Matt's input (100 lines): 4391 and 4626 (his Scala
solution's); the homework example gives 4140 and 3993. Compiler: the
installed release build of `main`, 1 November 2026.

### The program

`type Number = | Regular (value: Nat) | Pair (left: Number) (right:
Number)`, worked on as a tree. `explode depth number` walks down to the
leftmost pair of two regular numbers inside at least four pairs and hands
an `Explosion` back up: the number with that pair replaced by 0, and the
pair's two values while no regular number has taken them yet. A pair's
explosion comes from its parts' (`explodeIn left right inLeft inRight`):
the left part's if it has one, its right value then going to the leftmost
regular number of the right part (`addLeftmost`), else the right part's,
its left value going to the rightmost of the left part. `split` is the
same walk for the leftmost regular number of 10 or more. `reduce budget`
explodes while it can, else splits, and gives `None` if that takes more
than `budget` steps (`steps`, 1000 per sum); so `add`, `solvePart1` and
`solvePart2` are `Option`s, and `main` says "no answer" for `None`.
`orderedPairs` lists every ordered pair of lines at different indices
(`withIndex`, `flatMap`, `filterMap`); `sumMagnitudes` adds each. The
parser reads each line with a recursive `Parse` function bounded by the
line's length (`number room`: a `{Parse}` function needs a structural
argument to recurse), and `checkNumbers` fails unless every number is
reduced (`reduced`, `firstUnreduced`, the D2108 pattern). Both answers and
every example were right on the first run.

**The spec** (Spec/Spec.sw). The puzzle's rules say "the first regular
number to the left" and "the leftmost such pair": they are about reading
order. So the spec reads a number as its regular numbers from left to
right, each with how many pairs it is inside (`leaves`, a `List Leaf`),
and states each step on that list, where "to the left" is "earlier in the
list". `firstDeep` finds the first leaf inside more than four pairs and
the leaf after it (`Exploding`: the leaves before, the two, the leaves
after); `explodeLeaves` adds the left value to the last leaf before
(`addToLast`), the right value to the first leaf after (`addToFirst`), and
puts a 0 one pair shallower in their place; `splitLeaves` splits the first
leaf of 10 or more into two leaves one pair deeper. In a number with
nothing inside more than five pairs, the first leaf inside more than four
is the left value of the leftmost pair nested inside four, whose elements
can't be pairs, so the next leaf is its right value; the spec's comment
says so, and the theorems carry that hypothesis (the puzzle only explodes
such numbers). `reduceStep` explodes if it can, else splits;
`ReducesTo start final` steps until no step applies; `IsSum x y sum` is
`ReducesTo (leaves 0 (Pair x y)) (leaves 0 sum)`; `AddsUpTo` adds a list
in order; `IsReduced` is "every leaf inside at most four pairs and below
10". Part 1 is `Part1 numbers answer` (the first line plus the rest in
order adds up to a number of magnitude `answer`); part 2 is `Part2 numbers
answer` (some `x + y` of lines `i ≠ j` has magnitude `answer`, and every
such sum has magnitude at most `answer`). The tree type is the program's;
nothing else is shared.

Why the leaf list: on a tree, "the first regular number to the left" of a
pair is a zipper walk up and down, which is what the program does;
writing it again as the spec would prove the program equals a copy of
itself. On the list it is the leaf before. The price is the tree ↔ list
correspondence, which is most of the proofs.

### Proved

In `Aoc.Year2021.Day18.Proofs` (Proofs/, 9 files, 694 lines, 60
theorems). `height` is how many pairs deep a number's deepest regular
number is (`height n ≤ 5` is "nothing inside more than five pairs").

- **Explode is the spec's**: `explodeSome (number) (exploded) (some:
  explode 0 number = Some exploded) (fits: height number ≤ 5)`:
  `explodeLeaves (leaves 0 number) = Some (leaves 0 exploded.number)`;
  `explodeNone (number) (none: explode 0 number = None) (fits: height
  number ≤ 5)`: `height number ≤ 4 ∧ explodeLeaves (leaves 0 number) =
  None`. Under them, `explodeFound`: for a subtree at any depth, `firstDeep`
  finds the pair `explode` found whatever leaves follow, and the leaves of
  the result, with the values handed on added to whatever leaves lie on
  each side, are the spec's explosion (`Found`, quantified over the leaves
  before and after, which makes the induction go through), and
  `explodeNoneShallow` (nothing explodes: the subtree's leaves are all
  shallow, and `firstDeep` passes over them).
- **Split is the spec's**, with no depth hypothesis: `splitSome (number)
  (split2) (some: split number = Some split2)`: `splitLeaves (leaves 0
  number) = Some (leaves 0 split2)`; `splitNone (number) (none: split
  number = None)`: `splitLeaves (leaves 0 number) = None`.
- **Reduce**: `reduceSound (budget) (number) (final) (done: reduce budget
  number = Some final) (fits: height number ≤ 5)`: `ReducesTo (leaves 0
  number) (leaves 0 final) ∧ height final ≤ 4 ∧ split final = None`
  (explosions make nothing deeper, `explodeHeight`; a split from a number
  at most four deep makes it at most five, `splitHeight`). And
  `reduceComplete (final) (start) (reduces: ReducesTo start final)
  (number) (is: leaves 0 number = start) (fits: height number ≤ 5)`:
  there are a `budget` and a `result` with `reduce budget number = Some
  result ∧ leaves 0 result = final`. So the budget is the only gap between
  the program and the spec: whenever the spec's reduction ends, a big
  enough budget finishes there.
- **A finished sum is reduced**: `addSound (x) (y) (sum) (reducedX:
  IsReduced x) (reducedY: IsReduced y) (added: add x y = Some sum)`:
  `IsSum x y sum ∧ IsReduced sum` (`leavesSmall`: no pair nested inside
  four, no regular number of 10 or more).
- **Sums are well defined**: `reducesToUnique` (reducing ends in one
  place), `leavesInjective` (a number is fixed by its leaves, via
  `leavesPrefix`: a number's leaves start a list in one way only), so
  `sumUnique`: `IsSum x y sum1 → IsSum x y sum2 → sum1 = sum2`;
  `addsUpToUnique`, and `part1Unique` (two answers to `Part1` are equal).
- **Answers**: `part1Correct (numbers) (reduced: List.All IsReduced
  numbers) (answer) (solved: solvePart1 numbers = Some answer)`: `Part1
  numbers answer`; `part2Correct`, the same for `solvePart2` and `Part2`
  (through `memberPairs`/`pairsMember`: `orderedPairs` lists exactly the
  pairs of lines at different indices; `sumMagnitudesSound`; day 14's
  `maximumSome`; and `sumUnique`, since `Part2`'s bound is over every
  `sum` with `IsSum x y sum`). `magnitudeSame`: the program's magnitude is
  the spec's.
- **The parser's guarantee**, `parseNumbersReduced (input) (numbers)
  (parsed: Fail.toResult (() => parseNumbers input) = Ok numbers)`:
  `List.All IsReduced numbers`. `part1FromInput` and `part2FromInput`
  state both answers for every input the parser accepts, with no
  hypothesis but the answer being `Some`.
- Tests: every worked example of the puzzle (four explosions, two splits,
  one sum, a magnitude of 3488, the homework's 4140 and 3993), the spec's
  explode and split on example leaves, the parser's refusals (a deep pair,
  a number above 9, junk), the real input, and six example theorems
  instantiating the lemmas the audit warns about.

**Not proved**: that reduction always ends (termination). The spec's
`ReducesTo` is a relation, and the program has a step budget;
`reduceComplete` says the budget is the only gap, and on the real input
and every example each sum finishes well within 1000 steps (the tests).
So the answers' theorems say "if the program gives an answer, it is the
puzzle's", not "the program gives an answer". I didn't attempt a
termination proof: no simple weight works, since a split moves value one
pair deeper and an explosion moves it shallower or sideways, and an
explosion's right neighbour can itself be part of a pair inside four, so
values can grow and split again. No opaque definitions. Day 14's
`maximumSome` is imported again (SW-971 item 7).

`stitchwort audit Aoc.Year2021.Day18`: `audited 67 theorems: 0 failed, 6
with warnings, 61 passed`. All six are narrow hypotheses of the form
`f x = Some y` with `y` free (`splitSome`, `splitSomeLeaves`,
`splitHeight`, `explodeSome`, `reduceExplodes`, `reduceSplits`): a random
`y` is never what `f x` gives. The example theorems in Tests
(`exampleSplits`, `exampleExplodes`, …) show each can hold (item 6).

Breaking the program breaks the proofs: splitting into `value / 2` twice
(not rounding up) fails `splitSomeLeaves` (`E-REFL`, the two leaves
differ); handing the left part's right value to `addRightmost` of the right
part fails `explodeInFound` and `explodeInHeight` (`E-REWRITE-NOTHING`:
no `addLeftmost` to rewrite).

### 1. `search --at` refused four of the five goals I tried

- **Record literals print as named construction**: goals containing
  `Cons ({ value = …, depth = … }) rest` print without the brackets, as
  `Cons { value = leaf.value, depth = leaf.depth } rest`, and `search
  --at` re-reads the printed goal: `E-SEARCH-AT … E-PARSE: braces after
  \`Cons\` name its fields, and take no further arguments`
  (Proofs/Leaves.sw, `addToFirstZero`, 55 s with the index build). Same
  for a record update inside `Some`: `Some { found | before = … }` gives
  `E-PARSE: braces after \`Some\` name its fields; an update isn't one of
  them` (Proofs/Explode.sw, `shiftAppend`). The printed goals aren't valid
  source. Fix: print a record literal or update that is a constructor's
  argument in brackets (small).
- **A lifted match's name** in the goal (`Aoc.Year2021.Day18.split.%match1
  left right (split left) = None` in a hypothesis) gives `E-PARSE:
  expected a field name after \`.\`` (Proofs/Reduced.sw, `leavesSmall`).
  New consequence of SW-971 item 3.
- **Context order** (SW-969 item 1, seen again): `small: (depth ≤ 4 ∧
  value ≤ 9) ∧ Unit` listed before `value`, "unknown name \`value\`"
  (`leavesShallow`).
- The one it read, `(if i == j then None else Some (x, y)) = Some (x, y)`
  in `memberPairs`, it closed: "cases alone closes it", 2.2 s.

### 2. A definition with an overlapping arm had to be reshaped to prove it

`explode` had `| Pair (Regular a) (Regular b) => if 4 ≤ depth then … else
None` before `| Pair left right => match explode (depth + 1) left with …`.
To use the last arm for every pair but two regular numbers, I wrote its
body as a proof-side function and tried `rfl` per shape. `| Regular a,
Pair x y => rfl` checked; `| Pair x y, _ => rfl` failed `E-REFL`, with
notes explaining that the two written `match`es are different hidden
functions, equal only if neither calls its own definition (the program's
does), and suggesting a named `def` used in both places. That worked:
the arm became `explodeIn left right (explode (depth + 1) left) (explode
(depth + 1) right)`, and `explodeUnfold` states it for every pair but two
regular numbers nested four deep. The price: `explodeIn` takes both parts'
explosions, so the right part is now walked even when the left exploded
(run time 0.98 s → 1.1 s). Fix: generate an equation per arm, with the
earlier arms' failure as a hypothesis, as Lean's `f.eq_3` (medium). The
notes on the `E-REFL` were good: they said exactly what to do.

### 3. Messages and printing

- **Stale names in a goal**: in `leavesPrefix`'s last arm (`| depth, Pair
  left1 right1, Pair left2 right2, rest1, rest2, same`), the goal printed
  `same: List.append (List.append (leaves (Succ depth) left) (leaves (Succ
  depth) right)) rest1 = …` and `⊢ Pair left right = Pair left2 right2`,
  while the context listed `left1` and `right1`: the names of the previous
  arm's pattern. A printer bug; near SW-967 item 5's capture (small-medium).
- **One `if`, two forms**: in `explode`'s hypotheses `if 4 ≤ depth` stays
  `(if 4 <= depth then … else None)`, a `Bool` `if`; `match
  Nat.decLessEq 4 depth with` didn't refine it (E-TYPE-MISMATCH, the
  hypothesis unchanged) and `match deep: Nat.leq 4 depth with | True |
  False` did. In `split`, `if 10 ≤ value` shows as
  `Std.Decidable.elim (Nat.decLessThan 9 value) …` and `match
  Nat.decLessThan 9 value` refines it. You have to read each goal to know
  which to split on. Cause not established (speculative: the `if` inside
  a nested-pattern arm is compiled differently). Fix: one form, or a line
  in the proving guide (small).
- `Leaf.ext _ _ (Nat.addZero leaf.value) rfl` solved its holes as `leaf
  leaf` from the proof arguments, then "expected `{ value = leaf.value,
  depth = leaf.depth } = leaf`, but this has type `leaf = leaf`"; writing
  the two records out checks. The holes-before-expected-type family
  (SW-969 item 2), seen again. Record eta isn't definitional (`Cons {
  value = leaf.value, depth = leaf.depth } rest = Cons leaf rest` is
  `E-REFL`; SW-960 item 4), so `addToFirst 0` needed `Leaf.ext`.
- `import Std (Pair)` shadows a constructor of my own named `Pair`:
  `E-NOT-A-CONSTRUCTOR "\`Pair\` isn't a constructor"`, with a note
  naming `Aoc.Year2021.Day18.Number.Pair`. Clear; workaround
  `Std.Pair.fst` in full (small: maybe prefer a constructor in pattern
  position).
- Braces after a constructor (`Some { toLeft = … }`, `Cons { value = … }
  rest`, `Witness { value, depth } …`) bit three times, in program, spec
  and proofs; each message said exactly what to write (`Some ({ … })`).
  An LSP quick fix would save the round trip (small).
- No multi-line string literal: the 10-line homework example is a
  `Text.join` of a list (`E-PARSE: this string isn't closed with \`"\``)
  (small-medium, a design question).
- Good: after `match el: explode (depth + 1) left`, an induction hypothesis
  passed in as a function had its type refined, and the `E-TYPE-MISMATCH`
  said so and that `rfl` proves the refined premise. `omega` read
  `Nat.max` (printed as `if a <= b then b else a`) in every height bound;
  `cases` closed every goal stuck on an `if` with a contradictory or
  arithmetic hypothesis. Most proof files checked on the first try.

### 4. Lemma search, the audit and std

- `stitchwort search '((?a: Nat) == ?b) = False → ?a ≠ ?b'` and `'(?a:
  Nat) ≠ ?b → (?a == ?b) = False'` list `Exists.notNone` and `ByKey`
  lemmas, not `DecEq.soundFalse` or `Nat.equalFalse` (grep found them).
  New evidence for SW-960 item 3.
- **The audit warns on every `f x = Some y` hypothesis** with `y` free
  (six theorems): random inputs never make `y` what `f x` is. Workaround:
  example theorems in Tests. Fix: when a hypothesis is `f args = Some y`
  (or `= y`) and `y` is free, compute `y` from it instead of drawing it
  (small-medium; a different fix from SW-967 item 8's test inputs).
- `List.consInjective` needs the same head on both sides; for `Cons a r =
  Cons b s → a = b` I used `Eq.cong (xs => List.get xs 0)` and helper
  `headValue`/`headDepth` functions (generated injectivity, SW-963).
- Std candidates: `xs ≠ Nil → xs ++ ys ≠ Nil` and `ys ≠ Nil → xs ++ ys ≠
  Nil` (small); `List.findIndexFrom i p xs = None → List.All (x => p x =
  False) xs` (the `findIndexedNone` family, SW-960; small); List.maximum
  lemmas (day 14's again, SW-971 item 7).

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort run Aoc.Year2021.Day18.main` on the input | 1.1 s user |
| `stitchwort check --no-cache Aoc.Year2021.Day18.Proofs Aoc.Year2021.Day18.Tests` | 2.9 s user |
| `stitchwort audit Aoc.Year2021.Day18` (with the search) | 4.3 s |

170 lines of program, 112 of spec, 694 of proofs, 106 of tests.

### Ranked

1. `search --at` couldn't read four of five goals: printed goals with a
   record literal or update as a constructor's argument, or a lifted
   match's name, aren't valid source (item 1).
2. Proving about a definition with an overlapping arm meant reshaping the
   program around a named helper; per-arm equation lemmas would avoid it
   (item 2).
3. The audit can't satisfy `f x = Some y` hypotheses with `y` free (item
   4).
4. A goal printed the previous arm's variable names (item 3).
5. The same surface `if c ≤ x` computes to a `Bool` `if` in one place and
   `Decidable.elim` in another (item 3).
