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

## Day 6: Guard Gallivant

A guard walks a grid, turning right at each obstruction directly ahead,
until she steps off the map. Part 1 counts the distinct positions she visits;
part 2 counts the positions where one new obstruction (not at her start)
traps her in a loop (part 2's wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-06/README.txt>).
Answers on Matt's input: 4967 and 1789 (cross-checked with an independent
Python walk; the example gives 41 and 6).

The interesting part for a total language: a walk need not end, and part 2 is
about walks that don't.

### Termination

Every walk carries a step budget, `stateCount = height * width * 4`: the
guard has at most that many states (a position on the map and a facing).
The program is ordinary structural recursion on the budget:

```stitchwort
def Lab.patrolFrom (lab: Lab) (guard: Guard) (visited: Set Position): (budget: Nat) → Option (Set Position)
  | Zero => None
  | Succ budget =>
    let visitedNow := visited.insert guard.position
    match lab.step guard with
      | None => Some visitedNow
      | Some next => lab.patrolFrom next visitedNow budget
```

Running out of budget is not a guess. `budgetEnough` proves, for a guard who
starts on the map, that still being on the map after `stateCount` steps
means she never leaves (`Loops`, the spec's "stuck in a loop": there's no
step count at which she has left). The proof is the pigeonhole principle
over the first `stateCount + 1` states (numbered
`(row * width + column) * 4 + facing`, which is injective on the map), then
"a repeated state repeats forever", by induction on a bound (`repeatFrom`).
The answers are `Option`s, `None` exactly when she loops (`part1Loops`,
`part2Loops`); `main` fails then.

Part 2's loop test jumps from turn to turn (below), remembering the states
it has seen. A repeat is a loop (`repeatLoops`), and running out of budget is
`budgetEnough` again, since each jump takes at least one step.

`decreasing` (recursion on a measure) exists but wasn't the tool: nothing
gets smaller along a walk unless the program carries a proof that its
seen-set grows towards a bound, which is the same pigeonhole argument moved
into the program. A budget plus a separate theorem kept the program plain.

### The program

```stitchwort
def Lab.step (lab: Lab) (guard: Guard): Option Guard :=
  lab.ahead guard
    |> .map (next =>
      if lab.obstructions.contains next then { guard | facing = guard.facing.turnRight } else { guard | position = next })

def Sightlines.loopsFrom (sightlines: Sightlines) (guard: Guard) (seen: Set Guard): (budget: Nat) → Bool
  | Zero => True
  | Succ budget =>
    match sightlines.nextTurn guard with
      | None => False
      | Some next => seen.contains next || sightlines.loopsFrom next (seen.insert next) budget

def solvePart1 (lab: Lab): Option Nat := lab.patrol |> .map .size

def solvePart2 (lab: Lab): Option Nat :=
  let sightlines := Sightlines.of lab.obstructions
  lab.patrol
    |> .map (visited => visited.filter (position => position != lab.start && lab.loopsWith (sightlines.add position)) |> .size)
```

`Sightlines` holds the obstructions' columns for each row and rows for each
column; `nextTurn` goes straight to the nearest one ahead with
`Set.below`/`Set.above`. Only positions on the original route are tried.

### Proved, for every lab whose guard starts on the map

The spec (`Spec/Spec.sw`) is over the program's `Lab.step`, which is the
protocol as the puzzle words it: `walk`, `after`, `Loops`, `route` (her
positions over the first steps), `distinctPositions` (the size of the set of
the route), and `trapPositions` (positions on the map, not the start, not
already obstructed, where `trapped` holds, for any `trapped` that decides
`Loops` for the lab with that obstruction, so the spec has no budget in it).

- `budgetEnough`: the budget catches every loop (above).
- `part1Correct`: for any step count by which she has left, part 1 is
  `distinctPositions`. `part1Loops`: `None` when she loops.
- `loopsWithCorrect`: the jumping loop test decides `Loops`, for sightlines
  that `Simulates` the walk (each next turn is her state some steps on, and
  no next turn means she leaves).
- `offRouteFree`: a new obstruction off the route of a guard who leaves
  never traps her, so part 2 needs only the route's positions.
- `routeSettled`: the route's positions are on the map and free, except the
  start.
- `part2Correct`: part 2 is the size of `trapPositions`, given `Simulates`
  for the sightlines with each new obstruction. `part2Loops`: `None` when
  she loops.

About 650 lines of proof, with no axioms.

Not proved: `Simulates` for the program's sightlines, that is, that
`Set.below`/`Set.above` on `(Sightlines.of …).add p` find the nearest
obstruction ahead, and that walking there step by step ends in the same
state. It needs spec lemmas for `Set.below`/`Set.above` that std doesn't have
(item 1), plus a lemma for the `Sightlines.of` fold. `part2Correct` takes it
as a hypothesis. A test runs the jumping test against the step-by-step walk
for every obstruction position in the example. The parser (a rectangular
map, exactly one `^`, so the start is on the map) is tested, not proved.

### 1. No spec for `Set.below` / `Set.above`

`Map.below m key` is specified only as `List.last (List.filter (Map.toList m)
(e => Map.Spec.isLess e.fst key))` (`Map.belowToList`). What a caller needs
is "the largest key below, and nothing in between":

```stitchwort
theorem Set.belowSome (s: Set k) (key: k) (found: k) (h: s.below key = Some found):
  s.contains found = True ∧ found < key ∧ ((other: k) → found < other → other < key → s.contains other = False)
theorem Set.belowNone (s: Set k) (key: k) (h: s.below key = None) (other: k) (less: other < key): s.contains other = False
```

and the same for `above`. Getting there from `belowToList` means the
sortedness of `toList`, `last` of a filter and `Map.Spec.Ascending`, all in
`Ord.compare` terms. That is what left `Simulates` unproved. Fix: these four
lemmas in `Set/Spec.sw`.

### 2. No pigeonhole principle, and no finite-type enumeration

The budget theorem needed "`n + 1` values below `n` repeat" (`pigeonhole`,
with a bounded search `lastHit`, 50 lines) and an injection of guard states
into `Nat` (`stateCode`; `rowOfCell` by `Nat.divAddMul` and `Nat.divSmall`;
an inverse for `directionIndex` to show it injective). Mathlib has the
pigeonhole principle as `Fintype.not_injective_of_card_lt` and
`List.Nodup.length_le_card`
(<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Card.html>),
over `Fintype` instances for finite types, so the states of
`Fin h × Fin w × Direction` are counted rather than encoded by hand. Fix: a
std `Nat.pigeonhole` (stated as in `Proofs/Bound.sw`); later, a `Finite`
interface derived for enums and records of finite fields.

Also missing: "an iteration that revisits a state never ends"
(`repeatFrom`, `repeatLoops`). A std `Nat.iterate` lemma would serve any
cycle-finding day.

### 3. `ran out of resources: a value was too large to show`

```text
[E-RESOURCE] Error: ran out of resources: a value was too large to show
  Note 1: this isn't a type error or a failed test: there's no answer within the limits
  Note 2: it happened while checking `stepA2`
```

from a plain application of a std lemma:

```stitchwort
theorem stepA2 (lab: Lab) (visited: Set Position) (position: Position):
    Set.contains (visited.filter (keeps lab (Sightlines.of lab.obstructions))) position
      = (Set.contains visited position && keeps lab (Sightlines.of lab.obstructions) position) :=
  Set.containsFilter visited position (keeps lab (Sightlines.of lab.obstructions))
```

The same with an arbitrary `keep: Position → Bool` checks. `keeps` unfolds
to `loopsFrom` with a budget of `height * width * 4` and a `Set.singleton`
that computes to a tree; something unfolds it and then can't print it. A `?`
hole there failed the same way, and `rewrite` there gave `E-REWRITE-BUDGET`.
What worked: a lemma over any `keep` (`filterSame`), then instantiated, and
`Eq.trans`/`Eq.cong` chains instead of `rewrite`. Fix: compare `keeps lab s`
with itself before unfolding it; and an error should never fail to print
(shorten the term, as other messages do).

### 4. Goals unfold too far

- `(lab.withObstruction blocker).ahead guard = lab.ahead guard` isn't `rfl`:
  `ahead`'s inner `match` is lifted with `lab` as an argument, so the sides
  are two different stuck calls. `cases` (on the facing) proves it.
- `match patrolled: lab.patrol with` against the goal `solvePart2 lab = None`
  ran out of resources (item 3). Proving `lab.patrol = None` first, then
  `Eq.cong`, worked.
- `rewrite onRoute` (unfold a definition by name) is `E-REWRITE-RULE`
  ("this has type `Lab → Option Guard → Nat → Position → Bool`, which isn't
  an equation"). Lean's `rw [onRoute]` and `unfold` do this. Wrote `Eq.cong`
  with the body spelled out.

Day 2's item 3 (keep definitions folded until asked) is the common fix.

### 5. Confusing errors in the program

- Calling a `let`-bound lambda in a `{Fail}` body:

  ```stitchwort
  let positionsOf := (wanted: Cell) => cells.filter (cell => cell.snd == wanted) |> .map (cell => cell.fst)
  match positionsOf GuardStart with
    | [start] => { height = lines.length, width, obstructions = Set.fromList (positionsOf Obstruction), start }
  ```

  ```text
  [E-EFFECT-ESCAPE] Error: the result's type depends on the result of an operation
    Note: return the value together with what its type depends on, as a dependent pair
  ```

  No type depends on anything here. The same with a top-level
  `positionsOf` checks, as does a `match` on an inline `xs.map (…)`; the
  lambda's call seems to count as an operation. Fix: treat a `let` lambda
  that performs nothing as pure, and don't suggest a dependent pair unless a
  type really mentions the result.
- A lambda with a return type, `(wanted: Cell): List Position => …`, is
  "`a block must end with an expression, not let`", pointing at the `let`.
  Fix: say lambdas don't take a return type (or allow one, as Scala and Lean
  do).
- `Some { row = row - 1, column }` (day 1's item 7): six times today.

### 6. `cases` gaps

- It doesn't substitute an equation `record = variable` that it has found
  (`%fact1: { guard.position | row = … } = position`), so `aheadOnMap` (the
  position ahead is on the map) failed on the goal `False = True`. Stated
  about the `Option` instead (`onMapIfAny`), `cases` closed every case.
- It doesn't split plain variables: `directionIndex one = directionIndex
  other → one = other` is "found nothing to split on". Proved with an
  inverse (`directionOfIndex`) instead.
- Record eta isn't definitional: `{ row = p.row, column = p.column } = p`
  needs a `match` (`positionEta`, `guardExt`).

Fix: substitute equations with a variable side; split enum variables in the
goal; record eta in conversion.

### 7. Smaller

- A spec module can't add dot functions to the program's types
  (`E-FOREIGN-NAMESPACE`, a clear message), so the spec has `walk lab`, not
  `lab.walk`.
- A theorem whose result unfolds to a function type
  (`Loops lab := (steps: Nat) → Not …`) needs those arguments as patterns in
  every arm (`E-ARITY … takes more arguments after the colon`). Clear, but
  surprising for a named proposition.
- `at` can't be a variable's name in a `rewrite` rule (clear message).
- `x != y` is `Decidable.toBool (Decidable.not d)`, not `!(x == y)`, so a
  Boolean lemma about it has to talk about `Decidable` (`shapeOnRoute`).

What went well: `omega` took `row * width` as an atom and closed the code's
bounds; the pigeonhole proof and the loop-test proofs checked on the first
try; `Exists` and `Witness` were easy; `cases` did the Boolean case splits.

### Performance

The first part 2 (step by step from the start, remembering the turning
states, for each of the 4967 route positions) took 35 s on `stitchwort run`,
against 3.0 s for the same algorithm in CPython: about 12 times slower.
Jumping to the next obstruction with `Set.below`/`Set.above` per row and
column brought it to 3.3 s. Haskell and Scala would write the same loops,
and neither asks why the walk ends. Lean would take a `partial def`, which
proofs can't see into ("Functions marked `partial` are treated as opaque
constants by the kernel and are neither unfolded nor reduced",
<https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>),
or a budget like this one.

### Size and time

Release build:

| command | time |
| --- | --- |
| `stitchwort check --no-cache` (whole project) | 11.1 s (5.0 s before day 6) |
| `stitchwort check` (warm) | 1.6 s |
| `stitchwort check --no-cache Aoc.Year2024.Day06.Proofs` | 7.4 s |
| `stitchwort test --no-cache Aoc.Year2024.Day06` (27 tests) | 10.3 s |
| `stitchwort run Aoc.Year2024.Day06.main` on the example | 0.44 s |
| the same on the input (130 by 130) | 3.4 s |
| `stitchwort build` executable on the input | 3.1 s |
| the machine (`aoc_agrees`, full tier) on the input | 8.5 s |
| `aoc_answers year2024_day06` (with `--no-cache`) | 14.9 s |

The day is in `machine.rs`'s list but, at its place, not in the daily sample
(`aoc_agrees` stays at 49 s); at the full tier it runs, and the whole test took
285 s, most of it the reference evaluator on this day. Native and JS weren't
measured (this build has no `native` feature).

### Ranked

1. No `Set.below`/`Set.above` spec (item 1): left the jumping walk
   unproved.
2. A resource blow-up on a plain lemma application, with an unprintable
   error (item 3): cost the most time.
3. No pigeonhole principle or finite enumeration (item 2): 120 lines of
   encoding and counting for a one-line fact.
4. Goals unfolding (item 4).
5. `E-EFFECT-ESCAPE` on a pure `let` lambda (item 5).
6. `cases` gaps and record eta (item 6).
7. The small ones (item 7).
