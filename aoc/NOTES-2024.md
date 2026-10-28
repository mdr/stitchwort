# Friction report: Advent of Code 2024 in Stitchwort

What was awkward, missing or surprising while writing 2024's days (now in
`aoc/src/Aoc/Year2024/`), day by day, then ranked at the end. Compiler built
from `main` at 8af684cb, 27 October 2026.

## Day 1: Historian Hysteria

Two columns of location ids. Part 1 sorts both lists, pairs them up and adds
the distances; part 2 adds up each left id times how often it appears in the
right list. Answers on Matt's input: 2066446 and 24931009 (cross-checked with
a Python one-liner; the example gives 11 and 31).

The program came out short and read as intended on the first try:

```stitchwort
def solvePart1 (lists: LocationLists): Nat :=
  lists.left.sort
    |> .zipWith lists.right.sort Nat.absDiff
    |> .sum

def solvePart2 (lists: LocationLists): Nat :=
  let rightCounts := Map.counts lists.right
  lists.left.sumBy (id => id * rightCounts.getOr id 0)
```

`List.sort`, `zipWith`, `Nat.absDiff`, `Map.counts`, `Map.getOr`, `sumBy`,
`Text.words`, `mapWithIndex`, `unzip`, `let (left, right) := …` and record
punning (`{ left, right }`) were all there. Scala's
`left.sorted.zip(right.sorted).map((l, r) => (l - r).abs).sum` is no shorter.

Proved for every pair of lists (`Aoc.Year2024.Day01.Proofs`):

- `part1Correct`: part 1 is the total distance between the lists "lined up"
  (`LinedUp`: sorted and the same ids), for any way of lining them up, so the
  spec doesn't mention `sort`.
- `part1AnyOrder`, `part2AnyOrder`: reordering either list changes neither
  answer.
- `part2Correct`: the count-map lookups are the puzzle's "number of times that
  number appears in the right list" (`lists.right.count (== id)`).

### 1. No code shared between projects

`aoc/` has `Aoc.Common.parseLines` (number the lines, name the bad one in the
failure), which day 1 wanted. A project reads only its own `sources`, and
`sources: [src, ../aoc/src]` would pull in all of 2025's days too, so
the line numbering is written again in `parseLocationLists`:

```stitchwort
lines
  |> .mapWithIndex (index line => Fail.context "line ${index + 1}" (() => parseIdPair line))
  |> .unzip
```

Short, but it will be copied into every 2024 day. Scala (sbt `dependsOn`),
Haskell (cabal `build-depends` on a local package) and Lean (Lake `require`
with a path) all let one project use another. Either a path dependency in
`stitchwort.yaml`, or a std `Fail.eachLine`, would do.

Fixed: the years are one project, `aoc/`, with 2024 in `Aoc.Year2024`, 2025
in `Aoc.Year2025` and the shared helpers in `Aoc.Common`; day 1 uses
`Aoc.Common.parseLines`.

### 2. No `List.sumByPerm`: a sum is the same in any order

`List.Perm` is defined by counting (`occurrences xs p = occurrences ys p` for
every `p`), and std proves `sortPerm`, `permMap`, `permLength`, `memPerm`, but
nothing about `sumBy`, `count` or `foldLeft` over permuted lists. Part 2's
order theorem needed it, so `Proofs/Perm.sw` has a `removeFirst` and three
lemmas (`sumByRemoveFirst`, `occurrencesRemoveFirst`, `sumByPerm`; 40 lines,
about 20 minutes). They belong in `List/Sort.sw` beside `sortPerm`, with
`removeFirst` as a std program function (Haskell's `Data.List.delete`).

They also can't be dot-called: `List` is a std namespace a program can't add
to (`E-STD-NAMESPACE`, rogue's NOTES item 3), so it's
`sumByPerm f xs ys same`, not `xs.sumByPerm …`.

Fixed: std has `List.removeFirst` with its lemmas, `List.sumByPerm` (any
`Add`), `List.sumPerm` and `List.countPerm`; `Proofs/Perm.sw` is gone.

### 3. No "same elements, same sort" lemma

Showing that a list lines up only one way took `List.sortedPermEq`, which
wants `Nat.leq`'s transitivity and antisymmetry as Bool-valued lemmas that std
doesn't have, so they're written out (`leqTrans`, `leqAntisymm`, `omega`
one-liners; 2025's day 8 has the same pair under other names). What callers
want is

```stitchwort
theorem List.sortEqOfPerm [auto ord: Ord a] (xs ys: List a) (same: List.Perm xs ys): xs.sort = ys.sort
theorem List.sortUnique (xs ys: List Nat) (sorted: List.Sorted Nat.leq ys) (same: List.Perm ys xs): ys = xs.sort
```

Mathlib's [`List.eq_of_perm_of_sorted`](https://florisvandoorn.com/LeanCourse25/docs/Mathlib/Data/List/Sort.html)
takes the order's antisymmetry as an instance (`IsAntisymm`), so the caller
passes no lemmas; `sortedPermEq` takes them as arguments every time.

Fixed: std has `List.sortEqOfPerm`, `List.sortOfSorted` (and
`List.sortOfSortedNat` for `Nat.leq`), which take the laws from the `Ord`
instance, and `Ord.reverse` for largest-first sorts (2025's day 8).

### 4. Holes in a congruence lemma aren't filled before its proof argument

```stitchwort
List.sumByCong left _ _ (id => rewrite List.countOccurrences right (== id), … in rfl)
```

```text
[E-REWRITE-NOTHING] Error: `rewrite` found no `List.count right (%section => Decidable.toBool (Nat.decEq %section id))` in the goal
  Note 1: goal: `?18 lists left right sameLeft sameRight id = ?19 lists left right sameLeft sameRight id`
```

The two functions are fixed by the expected type of the whole call (it's the
step of a `calc`), but the lambda is checked first, against unsolved
metavariables. Writing both functions out works and doubles the line. The
fix is to unify the call's result type with the expected type before
checking a lambda argument, or to postpone the lambda until its type is
known. The note at least shows the goal, which made the cause clear.

### 5. Operator sections print as `%section` in errors

The same message spells `(== id)` as
`%section => Decidable.toBool (Nat.decEq %section id)`: an internal name and
the desugared `DecEq` call. It should print as written, `(== id)`, or at
least `x => x == id`.

### 6. `Map.getOrCounts` is stated with `Map.Spec.sameKey`

`Map.getOr (Map.counts xs) key 0 = List.count xs (x => Map.Spec.sameKey key x)`
needs a second rewrite, `Map.Spec.sameKeyDecide`, to reach `xs.count (== key)`,
which is how a spec says it. 2025's day 8 does the same two-step. A
companion `Map.getOrCountsEq: … = xs.count (== key)` would make part 2's proof
one rewrite.

Fixed: `Map.getOrCounts` is now stated as
`(Map.counts xs).getOr key 0 = xs.count (== key)`.

### 7. `Ok { … }` reads the braces as `Ok`'s own fields

```stitchwort
test "no lines" := parsed [] == Ok { left = [], right = [] }
```

```text
[E-UNKNOWN-FIELD] Error: `Ok` has no field `left`
  Note 1: `Ok`'s fields are `value`
  Note 2: braces right after a constructor name its own fields; to build the `Aoc.Year2024.Day01.LocationLists` it holds, write `Ok ({ … })`
```

A clear message, and the fix it suggests works. Scala's `Ok(LocationLists(…))`
has no such ambiguity, but this costs seconds.

### 8. The cache folder isn't ignored outside the repository root

`stitchwort check` writes `.stitchwort/` in the project's folder, and
`.gitignore` only ignored `/.stitchwort` at the root, so it showed up as
untracked. Changed the pattern to `.stitchwort/`.

### Not attempted: a remove-the-minimum spec for part 1

The puzzle's wording ("the smallest …, then the second-smallest …") could be a
recursion that takes the minimum out of each list. `LinedUp` (sorted, same
ids) says the same thing without fixing an algorithm, and needs no lemmas
about `List.minimum`, which std doesn't have.

### Size and time

Release build, warm cache unless noted:

| command | time |
| --- | --- |
| `stitchwort check` (cold, `--no-cache`) | 2.3 s (std dominates) |
| `stitchwort check` | 0.40 s |
| `stitchwort test` (12 tests, two on the real input) | 0.43 s |
| `stitchwort run Aoc.Year2024.Day01.main` on the input (1,000 lines) | 0.43 s |
| the same on 10,000 synthetic lines | 0.78 s |
| the same on 100,000 synthetic lines | 3.1 s |
| `stitchwort build` executable on the input | 0.03 s |

Nothing slow. `check --counterexamples` found no false theorems.

## Ranked

1. Missing permutation lemmas (`sumByPerm`, `countPerm`, `sortEqOfPerm`):
   every "order doesn't matter" theorem rebuilds them (items 2 and 3).
2. No code shared between projects (item 1): each AoC year copies its
   helpers (fixed).
3. Holes in a congruence lemma checked too early (item 4).
4. `%section` in error messages (item 5).
5. `Map.getOrCounts` in `sameKey` form (item 6).
6. `Ok { … }` (item 7): clear message, small cost.

## Day 2: Red-Nosed Reports

One report of levels per line. A report is safe if its levels are all
increasing or all decreasing, and adjacent levels differ by one to three.
Part 1 counts the safe reports; part 2 also counts those that one removed
level makes safe (the "Problem Dampener"; part 2's wording from the public
copy at <https://github.com/romellem/advent-of-code/blob/master/2024/2/README.md>).
Answers on Matt's input: 534 and 577 (cross-checked with a Python one-liner;
the example gives 2 and 4).

The program checked and passed its tests on the first try:

```stitchwort
def steps (levels: List Nat): List (Nat, Nat) := levels.zip levels.tailOf

def risesGently (lower: Nat) (higher: Nat): Bool := lower < higher && higher <= lower + 3

def isSafe (report: Report): Bool :=
  let reportSteps := steps report.levels
  reportSteps.all (step => risesGently step.fst step.snd) || reportSteps.all (step => risesGently step.snd step.fst)

def withoutOneLevel (report: Report): List Report :=
  List.range report.levels.length |> .map (index => { levels = report.levels.removeAt index })

def isSafeWithDampener (report: Report): Bool := isSafe report || (withoutOneLevel report |> .any isSafe)
```

The spec (`Spec/Spec.sw`) says it the puzzle's way: `allIncreasing`,
`allDecreasing` and `adjacentDifferByOneToThree` (with `Nat.absDiff`) over
every adjacent pair, and "safe, or some `removeAt index` is safe" for part 2.
Proved for every list of reports (`Aoc.Year2024.Day02.Proofs`, about 120
lines, no axioms):

- `part1Correct`, `part2Correct`: both parts count the reports the spec
  calls safe (through `isSafeCorrect`: one "rises gently" check per direction
  is the spec's monotonic-and-small-steps pair of rules).
- `safeWithoutFirst`, `safeWithoutLast`: removing the first or the last level
  of a safe report leaves it safe.
- `dampenerAloneSuffices`: so for a report with any levels, "safe, or safe
  with one level removed" is just "safe with one level removed".
- `part2AtLeastPart1`.

Nothing attempted was left unproved. `cases` closed every Boolean and
arithmetic step, `absDiff` included, which made this much cheaper than
expected.

### 1. Recursion on a nested pattern isn't seen as smaller

```stitchwort
theorem adjacentWithoutLast (holds: Nat → Nat → Bool): (levels: List Nat) → …
  | Cons level (Cons next (Cons after more)), all =>
    let kept := adjacentWithoutLast holds (Cons next (Cons after more)) (Bool.andRight _ _ all)
```

```text
[E-TERMINATION] Error: can't show that `Aoc.Year2024.Day02.Proofs.adjacentWithoutLast` terminates
  this call to `Aoc.Year2024.Day02.Proofs.adjacentWithoutLast` might not terminate: the 1st argument stays the same
  Note 1: however the recursive calls are repeated, some argument must get smaller (a part of a pattern-matched constructor); an argument passed on unchanged, or rebuilt from its own pattern, is no smaller
```

`Cons next (Cons after more)` is exactly the tail of the matched list, but
it's rebuilt, so it doesn't count; and the message talks only about the 1st
argument (`holds`, which never changes), not the list. Moving the inner match
into a nested `match rest with` gave a longer and harder message ("going
round `adjacentWithoutLastOf` → this `match` → this `match` → …: the 1st
argument stays the same, so no argument keeps getting smaller", although the
3rd argument shrinks each time). What worked: a second lemma that takes
`level`, `next` and `more` separately and recurses on `more`. Lean and
Haskell have as-patterns, which name the sub-term so the call passes it
unchanged: `| a :: rest@(b :: c :: more) => … f rest`
([Lean reference](https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching):
"`x@e` … matches the pattern `e` and binds its value to the identifier
`x`"). Fix: treat a constructor rebuilt from exactly a sub-pattern's parts as
that sub-term, or add as-patterns; and name the argument that fails to
shrink, not the first one that stays the same.

Fixed: a constructor rebuilt from exactly a nested pattern's parts is that
part, at any depth, also inside a lifted `match` (which `cases` makes), so
the lemma above checks as written (`examples/accept/structural-rebuilt-pattern.sw`
has its shape; day 2 itself now uses std's `List.chainInit`). When no argument gets smaller, the error
names the ones matched on: "the 2nd argument, `Cons y (Cons x more)`, isn't
seen as smaller than `levels`".

### 2. Goals print `&&` and `<` desugared

The goal for one step of `allRiseGently`:

```text
⊢ List.all (Aoc.Year2024.Day02.steps (Cons level (Cons next rest))) (step => if Nat.leq (Succ step.fst) step.snd then Nat.leq step.snd (step.fst + 3) else False) = (if if Nat.leq (Succ level) next then Aoc.Year2024.Day02.Spec.allIncreasing (Cons next rest) else False then if if Nat.leq 1 (level - next + (next - level)) then …
```

`a && b` shows as `if a then b else False`, `a < b` as `Nat.leq (Succ a) b`,
`absDiff` inlined, and names in full (`Aoc.Year2024.Day02.Spec.`). It took a
minute to see the source in it each time. Lean prints `a && b`, `a < b` and
short names. Fix: print `Bool.and`/`or` and `Nat.leq (Succ a) b` back in
source form, and names relative to the open namespace.

### 3. `rewrite` misses a lemma once the goal has unfolded it

Part 2's proof first said `rewrite …, isSafeCorrect _`, to turn
`isSafe { levels = report.levels.removeAt index }` into `safe { … }` inside
the `any`:

```text
[E-REWRITE-CONG] Error: `rewrite` can't go inside the function passed to `List.all`: there is no `List.allCong`
  looking for `Aoc.Year2024.Day02.isSafe ?18`, which is in the goal only inside a function passed to `List.all`, where it uses the function's variable
```

The proof never mentions `List.all`: the goal had already unfolded `isSafe`
to its body (`List.all (List.zip …)`), so the only `isSafe` left was one the
error invented. What worked: `List.anyCongMem` written out, with the two
functions spelled in full. Lean's `rw` works on the goal as written and
unfolds only when asked (`unfold`, `simp only [isSafe]`). Fix: keep a
definition folded in the goal until a rewrite or `cases` needs it unfolded;
and add `List.anyCong`/`List.allCong` beside `anyCongMem`.

Fixed: std has `List.anyCong`, `List.allCong`, `List.allCongMem` and
`List.allCongRange`, so `rewrite` goes inside `List.all` as it does inside
`List.any`; part 2's proof is now `rewrite …, isSafeCorrect (removed _)`,
with no congruence lemma written out. Still open: `isSafeCorrect _` (the
whole record left to `rewrite`) reports `E-REWRITE-NOTHING`, since the
search looks for `isSafe`'s body.

### 4. A name in the error that isn't in scope

An intermediate attempt (a `match rest with` under `| Cons level rest`)
failed with

```text
`Aoc.Year2024.Day02.Spec.everyAdjacentPair holds (Cons level (List.removeAt [next] (List.length tail)))` and `True` aren't equal
```

and a `cases` failure listing `holds level head = True`. Neither `tail` nor
`head` is a name in the proof: the match had refined `rest` but the length
computed from it kept a variable from somewhere else (`List.length`'s own
pattern?). Didn't dig: the restructured lemma (item 1) avoided it. Worth a
look: either goals keep unrefined copies of a matched variable, or the
printer shows internal binder names.

### 5. No `List.removeAt`

Removing the level at an index had no std function: Lean has
[`List.eraseIdx`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.eraseIdx),
Scala `xs.patch(i, Nil, 1)`. Added `List.removeAt` to `List/Toolkit.sw`
(recursive, so proofs about it compute; the prelude hash snapshot gains one
line).

### 6. No count monotonicity lemma

`part2AtLeastPart1` needed "counting with a weaker test counts at least as
many", which std doesn't have (`countAtLeast`, 8 lines, induction with
`List.countCons` and `omega`). Lean has
[`List.countP_mono_left`](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Count.html)
(`(∀ x ∈ l, p x → q x) → countP p l ≤ countP q l`).
It belongs beside `List.countCongMem`.

Fixed: std has `List.countLeMem` (beside `List.countCongMem`, named like
`List.sumByLe`); `countAtLeast` is gone.

### 7. No adjacent-pairs function or predicate

The program pairs each level with the next by `levels.zip levels.tailOf`
(finding `tailOf`, not `tail`, took a grep), and the spec wrote its own
`everyAdjacentPair` recursion, with its own drop-first and drop-last lemmas.
Kotlin has `zipWithNext`, Scala `sliding(2)`, and Lean `List.IsChain`, with
[`IsChain.tail` and `IsChain.dropLast`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Chain.html),
exactly the two lemmas written here; `List.Sorted le` is this predicate
already, for an order. Fix: std `List.zipWithNext` and a Bool
`List.chain holds xs` with those lemmas, which `Sorted` could then be.

Fixed: std has `List.zipWithNext` (with `List.lengthZipWithNext` and
`List.zipWithNextZip`, its relation to `zip` with `tailOf`) and the Bool
`xs.chain holds`, with `List.chainTail`, `List.chainInit`,
`List.chainEmpty`, `List.chainSingle`, `List.chainZipWithNext`,
`List.chainCong` and `List.chainAnd`; `List.sortedOfChain` and
`List.chainOfSorted` relate it to `List.Sorted`. The program is
`report.levels.chain risesGently || …`, the spec's `allIncreasing` is
`levels.chain (level next => level < next)`, and `steps`,
`everyAdjacentPair` and the three drop-first and drop-last lemmas are gone.

### 8. Small ones

- `report.withoutOneLevel` with `withoutOneLevel` defined beside `Report`:

  ```text
  [E-UNKNOWN-FIELD] Error: `Aoc.Year2024.Day02.Report` has no field or function `withoutOneLevel`
    Note: its fields are `levels`
  ```

  Dot calls look in `Report`'s own namespace only (as in Lean). The note
  could add "`withoutOneLevel report` is in scope". Wrote the plain call.
- `levels |> everyAdjacentPair (level next => level < next)` fails: `|>`
  passes the first argument (as in Elixir; F# and Elm pass the last). The
  message says so clearly. Wrote the plain call.
- `keeps (…) levels cases` at the end of a line, before a line `cases`, gave
  "`[E-PARSE] Error: a block must end with an expression, not let`" pointing
  at the `let`; `(cases)` in brackets works. The message didn't say the
  `cases` was the problem.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache` (whole project) | 5.0 s |
| `stitchwort check` (warm) | 1.15 s |
| `stitchwort check --no-cache Aoc.Year2024.Day02.Proofs` | 0.60 s |
| `stitchwort test Aoc.Year2024.Day02 --no-cache` (26 tests) | 0.64 s |
| `stitchwort run Aoc.Year2024.Day02.main` on the input (1,000 lines) | 0.24 s |
| the same on 10,000 lines (input repeated) | 0.38 s |
| the same on 100,000 lines | 2.0 s |

Nothing slow.

### Ranked

1. Nested-pattern recursion and its message (item 1): cost the most time.
2. Desugared goals (item 2): every goal read was slower for it.
3. `rewrite` against an unfolded goal (item 3).
4. Stray names in goals (item 4): possibly a bug.
5. No adjacent-pairs function or `Chain` (item 7).
6. No count monotonicity lemma (item 6).
7. `List.removeAt` (item 5): added.
8. The small ones (item 8).

## Day 4: Ceres Search

A word search. Part 1 counts every XMAS, "horizontal, vertical, diagonal,
written backwards, or even overlapping other words". Part 2 counts the X-MAS:
"two `MAS` in the shape of an `X` ... Within the `X`, each `MAS` can be
written forwards or backwards" (part 2's wording is from the public copy at
<https://github.com/romellem/advent-of-code/blob/master/2024/4/README.md>).
Answers on Matt's input: 2524 and 1873, cross-checked with a Python script
that tries every position and direction. The example gives 18 and 9, and so
do the puzzle's two dotted diagrams, which are tests too.

The grid is `{ rows: List (List Char) }`. Any character is a letter, so the
puzzle's diagrams (with `.` for irrelevant letters) parse as they are, and
rows may differ in length. Every line of four cells is four lists read side by
side, and `zipWith4` stops at the shortest, so a line that would leave the grid
is never read:

```stitchwort
def countXmas (first: List Char) (second: List Char) (third: List Char) (fourth: List Char): Nat :=
  List.zipWith4 first second third fourth spellsXmas |> .count (found => found)

def countAcross (row: List Char): Nat := countXmas row (row.drop 1) (row.drop 2) (row.drop 3)

def countThrough (first: List Char) (second: List Char) (third: List Char) (fourth: List Char): Nat :=
  countXmas first second third fourth
    + countXmas first (second.drop 1) (third.drop 2) (fourth.drop 3)
    + countXmas (first.drop 3) (second.drop 2) (third.drop 1) fourth

def solvePart1 (grid: Grid): Nat :=
  let rows := grid.rows
  let through := List.zipWith4 rows (rows.drop 1) (rows.drop 2) (rows.drop 3) countThrough |> .sum
  rows.sumBy countAcross + through

def countCrosses (above: List Char) (middle: List Char) (below: List Char): Nat :=
  let downRight := List.zipWith3 above (middle.drop 1) (below.drop 2) spellsMas
  let downLeft := List.zipWith3 (above.drop 2) (middle.drop 1) below spellsMas
  List.zipWith downRight downLeft (one other => one ∧ other) |> .count (found => found)
```

The program checked, and passed its tests on the first run, apart from one
test that was wrong itself.

The spec (`Spec/Spec.sw`) states it the puzzle's way, position by position:
`letterAt grid r c: Option Char`; a `Direction` is a `Step` (`Back`, `Stay`,
`Ahead`) down and one across, and `directions` lists the eight; `moved start
step distance` is `None` before 0; part 1 counts the (position, direction)
pairs whose letters `spells ['X', 'M', 'A', 'S']`, and part 2 counts the
positions where `[letter one step towards the start corner, centre, letter one
step towards the end corner]` is MAS or SAM on both diagonals. Proved for
every grid, ragged ones included (`Aoc.Year2024.Day04.Proofs`, no axioms):

- `part1Correct`: `solvePart1 grid = part1Spec grid`. The program's side
  (`programLines`) turns each `zipWith4` into a sum over indices; the spec's
  side (`specDirections`) widens both ranges by 3 and swaps the sums to put
  the directions outside; then the eight directions (`rightward`, `leftward`,
  ..., `upRight`) each equal one of the program's eight readings, the four
  backward ones three rows or columns on (`sumShift`).
- `part2Correct`: `solvePart2 grid = part2Spec grid`, the same way, shifted
  by one row and one column to the centre.

Lines: program 72, spec 85, `Proofs/` 642 (68 theorems: 28 in
`Proofs/Lists.sw` are general list and sum lemmas, 26 for part 1, 14 for part
2), tests 100. Most of the effort was the part 1 assembly.
Sabotage: `fourth == 'S'` for `'X'` in `spellsXmas`, and `'S'` for `'M'` in
`spellsMas`, each fail the proofs (in `at4Spells` and `masOrNone`).

The symmetry theorems (the count is the same with the word reversed, or the
grid transposed) weren't attempted: the direct proof against the spec was
done first, and makes them unnecessary for correctness.

### 1. The proof found a bug the tests had written down as right

The first part 2 program took the columns of three rows and then three
columns at a time:

```stitchwort
let columns := List.zipWith3 above middle below (top centre bottom => (top, centre, bottom))
List.zipWith3 columns (columns.drop 1) (columns.drop 2) isCross |> .count (found => found)
```

`zipWith3` stops at the shortest row, so in rows `M.S`, `.A`, `M.S` the cross
centred on the `A` is lost: its block includes the missing cell at the end of
the middle row, which isn't one of the cross's letters. I had written that as
a test, `part2 ["M.S", ".A", "M.S"] == 0` ("a cross cut short"). The spec
says 1, and setting up the proof made that plain: the program read nine cells
and the spec five. The program now zips just the five cells of the X (the two
diagonals of three), which reads more like the puzzle, and the test says 1.
Puzzle inputs are rectangular, so the answers were never affected. This
isn't reshaping the program for the proof: on the grids that parsing accepts,
the two programs differed.

### 2. `+` recurses on its first argument, so `c + 1` doesn't compute

`Nat.add` is `| Zero, n => n | Succ m, n => Succ (Nat.add m n)`, so `1 + c`
computes to `Succ c` and `c + 1` doesn't. The spec's `Ahead => Some (start +
distance)` is the natural way to write it, but every proof about an `Ahead`
direction then needs `rewrite Nat.addZero c, Nat.addComm c 1, Nat.addComm c 2,
Nat.addComm c 3` (five of the eight directions, and part 2's corners) before
`cases` can finish. `getDrop` (below) is stated as `k + j` for the same
reason. Lean's `Nat.add` recurses on the second argument
([Prelude](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean):
`| a, Nat.succ b => Nat.succ (Nat.add a b)`), so `n + 1` computes there.
Fix: recurse on the second argument (`x + 1` is far more common in specs
than `1 + x`), or let conversion use `Nat.addComm` for literals.

### 3. `rfl` errors that print both sides the same

A wrong offset in `throughSum` (`… 1 1 0 1` for `… 1 1 0 0`) gave

```text
[E-REFL] Error: `rfl` can't prove this
  `List.foldLeft (List.rangeFrom n 0) 0 (acc x => acc + (… + …)) + List.foldLeft (List.rangeFrom n 0) 0 (acc x => acc + (… + …)) + List.foldLeft (List.rangeFrom n 0) 0 (acc x => acc + (Bool.toNat … + Bool.toNat …))` and `List.foldLeft (List.rangeFrom n 0) 0 (acc x => acc + (… + …)) + List.foldLeft (List.rangeFrom n 0) 0 (acc x => acc + (… + …)) + List.foldLeft (List.rangeFrom n 0) 0 (acc x => acc + (Bool.toNat … + Bool.toNat …))` aren't equal
```

The two strings are identical: the difference is inside an `…`. The first try
at `rightward` (item 4) was nearly as bad (one more `&& …` on one side), and `programLines`' row step gave

```text
Note 1: the two sides differ only in arguments the compiler fills in, shown here in `[brackets]` (an implicit argument, or a proof such as `d != 0`; proofs of the same statement aren't interchangeable)
```

when they differed in `Option.getOrElse (List.get grid.rows (Succ x)) []`
against `List.getOr grid.rows (Succ x) []` (item 6), visible further along the
same printed line. What worked: proving the step as a separate pointwise
lemma, whose smaller terms printed in full. Fix: elide only what the two sides
share, and print the first subterm where they differ, as Lean's `rfl` failure
shows the two goals and `decide`/`simp` failures name the subterm; and check
that the "differ only in arguments the compiler fills in" note is true before
giving it.

### 4. `xs.all p` over a literal list isn't the `&&` of its elements

The spec's `List.range 4 |> .all (distance => …)` computes to
`p 0 && p 1 && p 2 && p 3 && True` (the `True` of `all`'s `Nil` case), and
`d && True` is `if d then True else False`, which isn't `d` by computation.
So `spells … = (p 0 ∧ p 1 ∧ p 2 ∧ p 3)` is not `rfl`; the error was item 3's,
with the extra `&& …` the only difference. `cases` proves it. Fix: a better
message (item 3) would have made this a minute's work; std could also state
`List.allCons`-style lemmas so a proof can avoid relying on computation.

### 5. `rewrite` with a hole can't solve an instance argument

```stitchwort
rewrite acrossSum grid _ wide (rowFits grid _), List.sumByAdd (List.range wide) _ _, …
```

```text
[E-REWRITE-NOTHING] Error: `rewrite` found no `List.sumBy (List.range (width grid + 3)) (x => Add.%add ?58 ?59 ?60)` in the goal
```

`List.sumByAdd` is generic in `[auto add: Add c]`, and with both functions
left as `_` the `Add` instance stays a hole (`?58`), so nothing matches. It
also prints `Add.%add`, an internal name. What worked: a Nat-only lemma for
double sums (`sumBy2Add`), applied with explicit functions. Fix: unify the
rule's pattern with the goal before resolving `auto` instances (the goal's
`+` fixes `c = Nat`).

### 6. `rewrite` with `_` rewrites one instance

`rewrite <- List.getOrGet rows _ []` turned `Option.getOrElse (List.get rows r) []`
back into `List.getOr rows r []` for `r` but not for `1 + r`, `2 + r` and
`3 + r`: the hole is filled by the first match, then only that instance is
rewritten. Writing the rule four times worked. This is how Lean's `rw`
behaves too, but Lean has `simp only [List.getOr_eq]` for "every instance";
here the symptom was item 3's misleading note. Fix: a `rewrite all` (or
`simp`-like) form, or a note when a rule with holes matched once and other
instances remain.

### 7. Missing list lemmas

Written in `Proofs/Lists.sw` (228 lines), all general:

- `getDrop`: `(xs.drop k).get j = xs.get (k + j)`. Lean has
  [`List.getElem?_drop`](https://lean-lang.org/doc/api/Init/Data/List/Nat/TakeDrop.html)
  (`@[simp]`).
- `getZipWith3` in `Option` form (std's `getOrZipWith3` needs equal lengths),
  `lengthZipWith3Le`, and `zipWith3`/`zipWith4` with an empty list.
- `sumByZipWith`, `sumByZipWith3`, `sumByZipWith4`: a sum over lists zipped
  in step is a sum over indices up to any bound (with `at2`/`at3`/`at4`, 0
  where an element is missing). These are what every grid-by-lists proof
  needs; 2025's day 4 has the `Vec` versions.
- `sumRangeExtend` (a sum over a longer range whose extra terms are 0) and
  `sumShift` (a sum over `n + k` indices whose first k terms are 0 is a sum
  from k), each a few lines on top of `List.sumByRangeSplit`,
  `List.sumByZeroIntro` and `List.sumByRangeOffset`.
- `someEq`: `(Some x == Some y) = (x == y)` doesn't hold by computation
  (`Option.decEq` wraps the answer in `Option.decSome`), so it needs a
  two-line lemma about `Option.decSome`.

Fix: move these to `List/Index.sw` and `List/Toolkit.sw`; make
`Option.decSome`'s `toBool` reduce (or add `Option.someEq`).

### 8. A `let` inside parentheses doesn't parse

```stitchwort
(c early => spellsShort grid r c { … } (let short: Nat.leq 3 c = False := omega in rewrite short in rfl))
```

```text
[E-PARSE] Error: expected an expression, but found `let`
```

A `let` is only allowed at the start of a block, so a one-off fact for an
argument needs the argument on its own indented lines (as in `specCrosses`'
`c early =>` arguments). Lean writes `(have h : … := by omega; …)` inline.
Fix: allow `let … in …` (or `let …; …`) as an expression. In the end `cases`
did these steps with no fact at all.

### 9. Goals show the proof terms of `let`s

The goal shown for a `?` lists every `let` in scope with its value, and for
a proof that is the whole term:

```text
tallSplit: height grid + 3 = height grid + 2 + 1 := Omega.proveEq (MkEnv [List.length grid.rows] []) [] (NAdd (NV 0) (NLit 3)) (NAdd (NAdd (NV 0) (NLit 2)) (NLit 1)) (Then NegGoal (Close 0)) (Then NegGoal (Close 0)) rfl rfl Trivial
```

and `across` in `programLines` printed as a 40-line `J`/`Eq.trans` term. One
step's message also showed `Effect.doneD (?83 grid) (?82 grid) (countThrough …)`,
an internal wrapper. Lean shows a `have`'s type only. Fix: print the type,
not the value, of a `let` whose type is a proposition.

### 10. What went well

`cases` did most of the work. It closed every pointwise fact about letters
(`at4Spells`, `masOrNone`, `crossAtTop`, the "no XMAS starts in the first
three columns" steps) by splitting on `Option`s, `Nat.leq` and the
characters' `Nat.decEq`, without help. A `Back` step from `3 + c` computes
(`(3 + c) - 1` is `2 + c`), so each backward direction was a three-line
`sumShift`. `rewrite` under `List.sumBy`'s binder (`rewrite acrossSum grid _
wide (rowFits grid _)`) worked first time. The proof time was in finding the
right statements, not in fighting the checker, except for items 3 to 6.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache` (whole project) | 6.0 s (5.0 s before day 4) |
| `stitchwort check` (warm) | 1.4 s |
| `stitchwort check --no-cache Aoc.Year2024.Day04.Proofs` | 1.7 s |
| `stitchwort check --no-cache Aoc.Year2024.Day04` | 0.32 s |
| `stitchwort test --no-cache Aoc.Year2024.Day04` (33 tests) | 1.8 s |
| `stitchwort test Aoc.Year2024.Day04` (warm) | 0.53 s |
| `stitchwort run Aoc.Year2024.Day04.main` on the input (140 by 140) | 0.23 s |
| the same on a random 443 by 443 grid (10 times the cells) | 0.57 s |
| the same on a random 1,400 by 1,400 grid (100 times) | 3.9 s |

The large grids' answers match the Python script. The spec run on the real
input as a test took about 0.5 s more (not kept: the proofs cover it).

### Ranked

1. The proof caught a real difference between program and spec (item 1):
   worth recording as the payoff, not a gap.
2. `rfl` errors that print both sides the same, and the wrong
   "compiler fills in" note (item 3): cost the most time.
3. `c + 1` doesn't compute (item 2): rewrites in every `Ahead` proof.
4. Holes and instances in `rewrite` (items 5 and 6).
5. Missing list lemmas: `getDrop`, sums over zipped lists, range shifts,
   `Some x == Some y` (item 7).
6. `xs.all p` ends in `&& True` (item 4).
7. Proof terms in goals (item 9).
8. No inline `let` (item 8).
9. `List.zipWith4` was missing; added to `List/Toolkit.sw` beside
   `zipWith3` (Haskell's `Data.List` has
   [`zipWith4` to `zipWith7`](https://hackage.haskell.org/package/base/docs/Data-List.html)).
   The prelude hash snapshot gains one line.
