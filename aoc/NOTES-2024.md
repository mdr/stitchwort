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
`Aoc.Common.parseLines`. Since 28 October the days with one record per line
read them with `Std.Parse`'s `Parse.eachLine`, and `parseLines` is gone.

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

## Day 3: Mull It Over

Corrupted memory: instructions like `mul(44,46)`, with one to three digits
per number, scattered through noise. Part 1 adds up the products of every
well-formed `mul`; part 2 also obeys `do()` and `don't()`, where "only the
most recent `do()` or `don't()` instruction applies" and `mul` starts
enabled (part 2's wording from the public copy at
<https://github.com/romellem/advent-of-code/blob/master/2024/3/README.md>).
Answers on Matt's input: 174960292 and 56275602 (cross-checked with Python's
`re.finditer` over `mul\((\d{1,3}),(\d{1,3})\)|do\(\)|don't\(\)`; part 1's
example gives 161, and part 2's own example gives 161 and 48).

The first program to use `Std.Parse`. Parsing produces a list of
`Mul left right | Do | Dont`, and both parts work from it:

```stitchwort
def findAll (parser: () → {Parse} a): {Parse} (List a) :=
  many (() =>
    oneOf [
      () => Some (parser()),
      () =>
        let skipped := satisfy "any character" (char => True)
        None
    ])
    |> .filterMap (found => found)

def shortNumber(): {Parse} Nat :=
  let start := Parse.mark()
  let number := nat()
  let finish := Parse.mark()
  Parse.ensure (finish.offset - start.offset ≤ 3) "expected at most three digits"
  number

def instruction(): {Parse} Instruction :=
  oneOf [
    () =>
      text "mul("
      let left := shortNumber()
      char ','
      let right := shortNumber()
      char ')'
      Mul left right,
    () => pick [("do()", Do), ("don't()", Dont)]
  ]

def parseInstructions (memory: Text): {Fail} (List Instruction) := Parse.all memory (() => findAll instruction)

def solvePart1 (instructions: List Instruction): Nat := instructions.sumBy result

def solvePart2 (instructions: List Instruction): Nat :=
  instructions.foldLeft ({ enabled = True, total = 0 }: Tally) step |> .total
```

The grammar reads exactly as the puzzle states it, and the backtracking was
right without any thought: `mul(1,2` fails without consuming anything, and
the next round skips one character and finds whatever starts inside it
(`mul(mul(2,3))` gives `Mul 2 3`). The edge cases (`mul(1234,5)`,
`mul(0012,5)`, `mul ( 1,2)`, `mul(-1,2)`, nested, across lines) all behaved
like the regex on the first run.

The spec (`Spec/Spec.sw`) states part 2 the way the puzzle does. `enabledAfter
earlier` is the last `do()`/`don't()` among the instructions before
(`filterMap setting |> .last`), or enabled if there is none.
`enabledResults` adds each instruction's result when `enabledAfter
(instructions.take index)` holds, over `withIndex`. Proved for every list of
instructions (`Aoc.Year2024.Day03.Proofs`, about 130 lines, no axioms):

- `part2Correct`: the fold is the spec. It goes through `tallyAfter`: after
  the first k instructions, the fold's tally is `{ enabled = enabledAfter
  (take k), total = the spec's terms below k, added up }`. The proof is by
  induction on k with std's `List.foldLeftTakeSucc` and `List.sumRangeLast`.
- `part2WithoutDont`: with no `don't()` (`instructions.any isDont = False`),
  part 2 is part 1.
- `part2AtMostPart1`: part 2 is never more than part 1 (`omega` from the
  fold's bound, `foldAtMost`).

Nothing attempted was left unproved. Part 1 has no separate spec, because it
is already `sumBy result`. Parsing isn't proved; see Std.Parse item 6.

### Std.Parse

#### 1. No `findAll`: "skip until the next match" is written by hand

The library has no combinator for "every match, anywhere in noise", and
that is the whole of this puzzle. The local `findAll` above is six lines.
Getting a faster version right took two tries (item 2), and every scanning
puzzle would repeat the `Option` plus `filterMap` round trip. Python's
`re.findall` is the model: "Return all non-overlapping matches of pattern in
string … The string is scanned left-to-right"
(<https://docs.python.org/3/library/re.html#re.findall>). Haskell's
replace-megaparsec has `sepCap`, which finds "all of the leftmost
non-overlapping occurrences of the pattern parser `sep`" and "will always
consume its entire input and can never fail"; the unmatched sections come
back as `Left`
(<https://hackage.haskell.org/package/replace-megaparsec/docs/Replace-Megaparsec.html>).
What I did: wrote `findAll` in Day03.sw. Fix: a std `Parse.findAll parser`
that never fails and reads everything, and perhaps a `Parse.sepCap`
returning the noise too.

#### 2. Scanning one character at a time is slow and uses a lot of memory

The generic `findAll` makes a few handler operations per character of
noise. Release build, on the machine, on the 18 KB input and on that input
repeated:

| variant | input | time | peak memory |
| --- | --- | --- | --- |
| `findAll` (the program) | 18 KB (real) | 0.63 s | 195 MB |
| `findAll` (the program) | 180 KB (×10) | 3.6 s | 1.23 GB |
| `findAll`, `--js` | 180 KB | 15.8 s | 2.07 GB |
| skip ahead with `span` to an `m` or `d` | 18 KB | 0.36 s | 100 MB |
| skip ahead | 180 KB | 0.90 s | 306 MB |
| skip ahead | 1.8 MB (×100) | 6.6 s | 2.26 GB |

`--native` wasn't measured, because this build lacks the `native` feature.
Startup is about 0.2 s, so on the real input the parse takes about 0.4 s,
which is fine. Memory, though, grows by about 6.5 KB per character of input
for the generic scan, and by 1.2 KB per character even when skipping ahead,
so a few MB of noise would not fit. Speculative: the handler in
`Parse.runFrom` resumes `k` inside the state-passing function, so frames
pile up with each operation. The proposal's §7.1 measured 1.3 GB for 1.77 MB
when parsing the whole input at once, which fits that. What I did: kept the
generic `findAll`, since it's what a user writes first and the input is
small. Fix: a std `findAll` that skips to the next character that could
start a match with one `span` operation, and a look at the per-operation
memory of `runFrom`.

The skip-ahead version first failed on the real input:

```text
error: line 7, column 1: expected 'mul(' or 'do()' or 'don't()' or any character
```

The skip (`span`) came before the `oneOf`. The last round fails at the end
of the input, and when it backed up it undid the skip over the trailing
noise too, so `Parse.all` then wanted the end. Moving the `span` into the
skip alternative fixed it. The message was accurate but didn't point at the
cause: `many` backs up the whole of a failed round, including what it read
before choosing. That is another reason for a std `findAll`.

#### 3. No bounded repetition: "one to three digits" goes through offsets

`nat()` reads any number of digits, and there is no `count`, `atMost` or
`between` to read a digit one to three times, so `shortNumber` compares
`Parse.mark()` offsets before and after `nat()`. Haskell's parser-combinators
has `count' m n p`, which "parses from m to n occurrences of p"
(<https://hackage.haskell.org/package/parser-combinators/docs/Control-Monad-Combinators.html>).
`many1 digit` with a length check would also work, but costs one operation
per digit. Fix: `Parse.natDigits (atLeast: Nat) (atMost: Nat)`, or a
general `Parse.repeat atLeast atMost parser`.

#### 4. Error messages are good

Parsing one instruction with `Parse.line` (Tests/Examples.sw):

```text
"mul(1234,5)" → column 9: expected at most three digits
"mul(1,2"     → column 8: expected ')'
"mul ( 1,2)"  → column 1: expected 'mul(' or 'do()' or 'don't()'
"mul(32,64]"  → column 10: expected ')'
```

All of them point at the right place and say the right thing. One
wrinkle: the `Parse.ensure` message is reported after the digits (column
9), not where the number starts (column 5), and `label` can't move it. What
I did: nothing. Fix (small): an `ensureAt mark ok message` that reports at a
mark.

#### 5. A comparison on `Parse.mark()` inside an argument doesn't elaborate

```stitchwort
Parse.ensure (Parse.mark().offset - start.offset ≤ 3) "expected at most three digits"
```

```text
[E-AUTO-NONE] Error: no way to decide `%3`
  this is a proposition, and nothing decides it
  Note: a `Bool` is expected here, and a proposition is turned into one only if it has a decision procedure: an `instance` returning `Decidable …`
```

`Parse.ensure (Parse.mark().offset ≤ 3) "x"` fails the same way. But
`def b(): {Parse} Bool := Parse.mark().offset ≤ 3` checks, and so does the
comparison once `Parse.mark()` is bound by `let`. So an ability call inside
a comparison passed as an argument loses its operand's type. The message
names a metavariable (`%3`) and talks about propositions, and the code
mentions neither. What I did: `let finish := Parse.mark()`. Fix: elaborate
the effectful operand before choosing `≤`'s instance, and never print `%n`
in a user-facing error.

#### 6. Per-operation lemmas: concrete runs are free, general ones need the continuation spelled out

`Parse.run "mul(2,4)".toList instruction = Ok (Mul 2 4) := rfl` checks, but
that is only a unit test. A lemma for every input that starts with `do()`
also holds in one line with `Parse.runFromLiteralThere`. It worked only
after I wrote the continuation `k` as the body of `Parse.text`, inlined:

```stitchwort
theorem readDoThere (rest: List Char) (state: Parse.State) (starts: state.at.rest = List.append "do()".toList rest):
    Parse.runFrom state readDo = Ok Do :=
  Parse.runFromLiteralThere state "do()".toList rest (found =>
    let checked: () := if found then () else Parse.expected "'do()'"
    Do) starts
```

When `k` didn't exactly match the elaborated term, `rewrite` printed the
handler's internals (`%arg0 => Call (L (%literal ['d', 'o'])) …`). There
are no lemmas for `oneOf`, `optional` or `many`, which run nested handlers,
so nothing about `findAll` is cheap to prove. What I did: proved over the
parsed list, as planned. Fix: lemmas at the level of the pieces
(`runFromText`, and `runFromNat` for a digit prefix), plus lemmas for the
success and backtrack cases of `optional` and `oneOf`.

### General

#### 7. A record literal as `foldLeft`'s initial value needs its type

```text
[E-CANNOT-INFER] Error: can't tell which record type this record literal is
 79 │   instructions.foldLeft { enabled = True, total = 0 } step |> .total
    │                                       ╰──────────────── its type isn't known here
    │ Note: add a type annotation, as in `(p: Person)`
```

`step: Tally → Instruction → Tally` is the next argument and fixes `b`, but
arguments are elaborated left to right. The note is clear. What I did:
`({ enabled = True, total = 0 }: Tally)`. Fix: when a record literal's type
is unknown, postpone it until the other arguments are elaborated.

#### 8. `rewrite` again meets goals whose definitions are already unfolded

As in day 2's item 3: after `rewrite List.withIndexRange …`, the goal had
`sumBy` unfolded to `List.foldLeft … 0 (acc x => acc + …)`, so
`List.sumByMap … _ _` didn't fit:

```text
expected `List.foldLeft (List.map (List.range (List.length instructions)) (i => (i, …))) 0 (acc x => acc + (if … then … else 0)) = …`,
but this has type `List.sumBy (List.map (List.range (List.length instructions)) (x => (x, List.getOr instructions x Do))) (?9 instructions) = …`
```

What I did: `Eq.trans (Eq.cong (pairs => List.sumBy pairs counted) …)
(List.sumByMap … counted …)`, with `counted` being the spec's pattern lambda
written out again. The checker accepted the second copy of
`((index, instruction)) => …` as equal to the spec's. Fix: the same as day
2, keep definitions folded.

#### 9. `x + 0` isn't `x` by computation, and `cases` says it's "stuck on `total`"

`{ enabled = False, total = total } = { enabled = False, total = total + 0 }`
needed `rewrite Nat.addZero total` every time; `cases` said it "doesn't
take apart" `total`. Also, after `rewrite enabledAfterDo`, the term
`if enabledAfter earlier then 0 else 0` was left over, and it needed a
`match` on `enabledAfter earlier` before `Nat.addZero` applied. Lean's
`simp` closes both. What I did: `match enabled: enabledAfter earlier with`,
then `rewrite Nat.addZero total in cases` in each arm. Fix: have `cases` and
`rfl` normalise `n + 0` and `if c then a else a`, or add a small `simp`.

#### 10. No `take`-snoc or `last`-of-append lemma

Std had `foldLeftTakeSucc` (the fold of `take (k + 1)`), but not the list
fact behind it, `take (k + 1) = take k ++ [getOr k]`. It also had no lemma
that `last (xs ++ [x]) = Some x`. Lean has `List.take_add_one`, "take (i +
1) l = take i l ++ l[i]?.toList" (formerly `List.take_succ`,
<https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/TakeDrop.html>),
and `List.getLast?_concat`
(<https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Lemmas.html>).
What I did: wrote `takeSucc` and `lastSnoc` in the proofs, three lines each.
Fix: add both beside `List.takeAll` and `List.lastMap`.

Fixed: std has `List.takeSucc` (List/Index.sw) and `List.lastSnoc`
(List/Toolkit.sw); the proofs use them.

#### 11. Small ones

- `|>` isn't allowed in a `calc` step: `_ = List.range all |> .sumBy f :=
  …` gives "expected the end of the declaration, but found `|>`". I wrote
  `List.sumBy (List.range all) f` instead.
- `import Std.Parse (text)` doesn't bring `Parse.line` into scope: "unknown
  name `Parse.line` … Note: `Parse` is `Std.Parse`; add `import Std
  (Parse)`". The note is exactly right.

### Size and time

Release build, wall-clock times, with other work running on the machine:

| command | time |
| --- | --- |
| `stitchwort check --no-cache` (whole project) | 5.5 s |
| `stitchwort check` (warm) | 2.3 s |
| `stitchwort check --no-cache Aoc.Year2024.Day03.Proofs` | 1.3 s |
| `stitchwort test Aoc.Year2024.Day03 --no-cache` (32 tests) | 2.2 s |
| `stitchwort run Aoc.Year2024.Day03.main` on the input (18 KB) | 0.63 s |

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

Fixed: std has `List.allCons` and `List.anyCons` (`List.all (Cons x xs) p = (p x ∧
List.all xs p)`, and `∨` for `any`), and `Bool.andTrue` for the last step.

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

Fixed: when a rule with holes matches nothing, an occurrence's type fixes
the carrier, the instances it determines are found, and the rule is
searched for again, also inside functions. The original line now checks,
and `programLines` splits its sums with `List.sumByAdd (List.range tall) _
_` and `List.sumByNestedAdd … _ _` instead of writing the functions out.
Errors print `Add.%add d x y` and `Mul.%mul d x y` as `x + y` and `x * y`.

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

Fixed: std has them, and `Proofs/Lists.sw` is gone. `List.getDrop`,
`List.getZip`, `List.getZipWith3`/`4` (as `Option.map2`/`3`/`4` of the
elements), `List.lengthZipWithLe`/`3Le`/`4Le` and the `zipWith3`/`zipWith4`
empty-list lemmas are in List/Toolkit.sw; `List.sumByGet`,
`List.sumByZipWith`/`3`/`4`, `List.sumByRangeZero`, `List.sumByRangeExtend`
and `List.sumByRangeSkipZeros` in List/Index.sw; `List.sumByNestedAdd` in
List/Sort.sw; `Option.map2`/`3`/`4` with `Option.getOrElseMap2`/`3`/`4` (the
`at4OrElse` step) and `Option.someBeqSome` in Option/Option.sw.

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

## Day 5: Print Queue

Page ordering rules, one per line (`47|53`: if an update has both pages, 47
must be printed before 53), a blank line, then updates, one per line, each a
list of pages (`75,47,61,53,29`). Part 1 adds up the middle pages of the
updates already in the right order. Part 2 puts each of the others in the
right order and adds up their middle pages (part 2's wording from the public
copy at <https://github.com/romellem/advent-of-code/blob/master/2024/5/README.md>).
Answers on Matt's input: 4569 and 6456, cross-checked with a Python script
(`/usr/bin/python3 -I`, using `functools.cmp_to_key`); the example gives 143
and 123. Compiler built from `main` at 7fe3bba8, 28 October 2026.

The first parser with `Std.Parse` read the input, and the program printed
the right answers on the first run:

```stitchwort
def rule(): {Parse} Rule :=
  let before := nat()
  char '|'
  let after := nat()
  { before, after }

def update(): {Parse} Update := { pages = sepBy1 nat (() => char ',') }

def printQueue(): {Parse} PrintQueue :=
  let rules := lines rule
  blankLine()
  let updates := lines update
  { rules, updates }

def parsePrintQueue (input: Text): {Fail} PrintQueue := Parse.all input printQueue

def solvePart1 (queue: PrintQueue): Nat :=
  let precedes := mustPrecede (ruleSet queue.rules)
  queue.updates.filter (update => inOrder precedes update.pages) |> .sumBy middlePage

def solvePart2 (queue: PrintQueue): Nat :=
  let precedes := mustPrecede (ruleSet queue.rules)
  queue.updates.filter (update => !(inOrder precedes update.pages))
    |> .map (reorder precedes)
    |> .sumBy middlePage
```

`inOrder` checks each page against the pages after it, and `reorder` sorts
with `List.sortWith` and the test "may come before unless a rule says the
next page goes first", `page next => !(precedes next page)`. The rules are a
`Set (Nat, Nat)`.

**The assumption for part 2.** On each update's pages, the rules are a strict
total order: no two pages are ordered both ways, any two different pages are
ordered one way, and the order is transitive (`Spec.StrictTotalOrderOn`). It
isn't a lawful order on all pages: the real input has rules X|Y and Y|Z with
no X|Z (a test says so), so no `Ord` instance fits, and `Ord.reverse` doesn't
help. The test "real input, the rules order each update's pages" checks the
assumption on all 197 updates: their pages are different, any two are
ordered by exactly one rule, and the sorted update is in order (which, with
the first two, makes the order transitive on those pages).

Proved, for every print queue (`Aoc.Year2024.Day05.Proofs`, 280 lines, no
axioms), against a spec (`Spec/Spec.sw`) in the puzzle's words, where a rule
X|Y is followed "if both page number X and page number Y are … part of an
update, page number X must be printed at some point before page number Y" (no
copy of Y comes before a copy of X):

- `inOrderCorrect`: the program's pairwise check, through the rule set, is
  "every rule is followed". On the way, `followsRuleIsPrintedBefore`: the
  puzzle's "if both pages are in the update" adds nothing, and
  `mustPrecedeCorrect`: looking a pair up in the set is asking whether some
  rule says so.
- `part1Correct`: part 1 adds up the middle pages of the updates in the right
  order.
- `reorderCorrect` (under the assumption): the reordered update has the same
  pages (`List.Perm`) and is in the right order.
- `correctOrderingUnique` (under the assumption): any two correct orderings
  of an update are the same, so "the" correct order the puzzle speaks of is
  well defined.
- `part2Correct`: given the assumption for every update, part 2 adds up the
  middle pages of the updates not in the right order, after any correct
  ordering of each.

The spec reuses the program's `middlePage` (index `length / 2`), which is the
puzzle's "middle page number" for the odd-length updates of the input (a test
checks all are odd).

Not proved: that the parser reads the text it's given correctly (house rule:
theorems are over the parsed model), and that the assumption holds for the
real input, which is a run-time test, not a theorem. Proving it would need
the transitivity check as a theorem about a concrete 1,176-rule input, which
evaluation in the kernel won't do in reasonable time.

The proofs went much better than the size suggests. `std` already had the
right sort theorems: `List.sortWithSortedOn` and `List.pairwiseOfSortedOn`
need the test total and transitive only on the values being sorted, which is
exactly the per-update assumption. Lean's `List.pairwise_mergeSort` needs
`trans` and `total` for all values
([Init.Data.List.Sort.Lemmas](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Sort/Lemmas.html)),
so it wouldn't apply directly here; C++'s `std::sort` requires a strict weak
order on all values ([Compare](https://en.cppreference.com/w/cpp/named_req/Compare)).
The uniqueness proof copies `List.sortedPermEq`'s shape, with totality only
on the update's pages.

### Std.Parse

The parser was the easiest part of the day: four short functions, each
reading like the input. Error messages, from the tests (`Parse.all`):

| Input | Message |
| --- | --- |
| a bad rule, `3x4` on line 2 | `line 2, column 2: expected '\|'` |
| a rule with no second page, `3\|` | `line 2, column 3: expected a number` |
| a bad update, `3,x` on line 4 | `line 4, column 3: expected a number` |
| a bad separator in an update, `3;4` | `line 4, column 2: expected ',' or a line break or the end` |
| a rule among the updates, `3\|4` | `line 4, column 2: expected ',' or a line break or the end` |
| no blank line between the sections | `line 2, column 2: expected '\|'` |
| no updates after the blank line | `line 3, column 1: expected a number` |
| two blank lines between the sections | `line 3, column 1: expected a number` |
| a blank line at the end of the input | `line 4, column 1: expected a number or the end` |

All point at the right place. The friction:

1. **A blank line at the end of the input is an error, and the message is
   confusing.** `Parse.all` allows one final line break; a file ending in
   `\n\n` fails with "line 4, column 1: expected a number or the end" when
   the cursor *is* at the end but for one line break. Editors and
   copy-pasting add these. aoc-parse's `section` reads lines "followed by
   either a blank line or the end of input"
   ([aoc-parse README](https://github.com/jorendorff/aoc-parse)). What I did:
   nothing; Matt's input has no final line break at all. Fix: let `Parse.all`
   allow any trailing blank lines (or whitespace).
2. **A missing blank line between sections is reported as a bad rule.**
   `1|2\n1,2` gives "expected '|'" at the update's comma, not "expected a
   blank line": the furthest failure wins, and the rule parser got further
   than `blankLine` did. Correct by the furthest-failure rule, but the hint
   the reader needs is the other one. What I did: a test pins the message.
   Fix: `Parse.label "a rule like 47|53"` on the rule would make it "expected
   a rule like 47|53"; or a combinator for a section, `section rule`, that
   reports "expected a blank line or a rule" from the line start.
3. **`sections` is for repeated sections of one kind only.** The brief
   suggests `sections` for this input, but its two sections hold different
   things (rules, then updates), so `sections` (one parser for every block)
   doesn't fit; `lines rule`, `blankLine()`, `lines update` does, as in
   `examples/accept/parse-aoc-day05.sw`. aoc-parse writes this
   `section(p1) section(p2)` (README, above). Fix: document the
   two-different-sections shape next to `sections` in the guide; a
   `section p` (lines of `p`, then a blank line or the end) would make it one
   word per section.
4. **Parser names collide with value names.** The parser for an update is
   naturally `update()`, and then a lambda parameter `update` (the natural
   name for an update in `solvePart1`) warns
   `W-LAMBDA-SHADOW: this lambda's first parameter `update` hides the function `update``
   in the proofs. The program's lambdas didn't warn, only the proofs' (which
   import the namespace with `(..)`). What I did: called the parameters
   `queued` in the proofs. Fix: suggest a naming convention for parsers in
   the guide (`updateLine`, or a `Parsers` sub-namespace).
5. **`Parse.all` is slow and large on big inputs**, as §7.4 of the proposal
   says: see the next section. Not a problem at AoC sizes.

### Performance

Release build, Apple silicon, other work on the machine; user time:

| command | time | peak memory |
| --- | --- | --- |
| `stitchwort check --no-cache` (whole project) | 5.0 s | |
| `stitchwort check` (warm) | 1.2 s | |
| `stitchwort check --no-cache Aoc.Year2024.Day05.Proofs` | 1.6 s | |
| `stitchwort test Aoc.Year2024.Day05 --no-cache` (34 tests) | 2.1 s | |
| `run Aoc.Year2024.Day05.main` on the input (1,373 lines, 15 KB) | 0.58 s | 130 MB |
| the same, parsing only | 0.50 s | 129 MB |
| `main` on the updates repeated 10 times (3,148 lines) | 1.6 s | 240 MB |
| `main` on the updates repeated 100 times (20,876 lines) | 14.0 s | 1,388 MB |
| the same, parsing only | 6.1 s | 1,387 MB |

On the real input, parsing is most of the run (about 0.3 s after start-up),
and the peak memory is the parser's: it holds the whole input as a
`List Char`. At 100 times the input (0.9 MB) the parse takes 6 s and 1.4 GB,
about 1,500 bytes a character: more than the 420 bytes a character the
proposal measured for the list alone (`parser-combinators.md` §7.2), so the
parse itself holds a good deal more. I didn't find what. The solving is cheap: `Set` lookups and a merge sort of at most 23
pages. Nothing to change for AoC; for large sectioned input the proposal's
native text cursor (§7.3) is the fix. `machine aoc_agrees` samples every
other day by default, and 2024 day 5 falls between samples; its tests other
than the real-input ones ran there and agree.

### 1. `a || b` with an effectful `b` elaborates differently inside a lambda

The proof of `noRuleBroken` stated
`rules.all (rule => !(page == rule.after) || !(later.any (== rule.before)))`
in a theorem, and `allAnd rules (rule => …same text…) …` in its proof; they
didn't match:

```text
expected `List.all later (laterPage => not (ruleSays rules laterPage page)) = List.all rules (rule => not (Decidable.toBool (Nat.decEq page rule.after)) || not (List.any later (== rule.before)) && True)`, but this has type `… = List.all rules (rule => not (Decidable.toBool (Nat.decEq page rule.after)) || not (List.any later (== rule.before)))`
```

The `&& True` is the clue. A smaller case, `xs.all (x => !(p == x) || !(ys.any (== x))) = True := rfl`, shows the elaborated lambda:

```text
`List.all xs (x => if not (Decidable.toBool (Nat.decEq p x)) then True else Effect.bindDv Total Empty (Effect.bindDv Total Empty (List.any ys (== x)) (%5 => not %5)) (%cond => if %cond then True else False))` and `True` aren't equal
```

`List.all`'s test is effect-polymorphic (`a → {e} Bool`), so the lambda is
elaborated as an effectful computation, and `||` with a right side that calls
another effect-polymorphic function (`List.any`) becomes
`if b then True else False`, which isn't `b` by computing when `b` is a
variable. The same text written where the lambda is known to be pure
elaborates to plain `a || b`. So two copies of one expression aren't equal by
`rfl`, and the message doesn't say why. What I did: a named `def keptBy` for the test,
used in both places. Fix: elaborate `||`/`&&` to `Bool.or`/`Bool.and` of the
two results when the row turns out to be `Total`, or normalise
`if b then True else False` to `b` in conversion.

Fixed: in a computation, `a || b` and `a && b` no longer wrap `b` in
`if b then True else False`. A left side that performs runs first and its
result is the left operand of the rest; a pure left side is the condition of
the plain `Bool` reading, with the same choice of `if` or `Decidable.elim`
as outside a computation. Once the row is empty the lambda computes to the
plain form, so the same text in a statement and a proof is equal by `rfl`
(`examples/accept/effect-logic-in-lambdas.sw`). Day 5 writes the test inline
again; `keptBy` is gone.

### 2. No eta for records

`Eq.cong (pages => ({ pages }: Update)) same` doesn't prove `first = second`
for a one-field record:

```text
expected `first = second`, but this has type `{ pages = first.pages } = { pages = second.pages }`
```

Lean 4 has eta for structures by definition, so `p = { x := p.x, y := p.y }`
holds by `rfl` (an example in
[Multiple-inheritance hazards in dependently-typed algebraic hierarchies](https://arxiv.org/pdf/2306.00617)).
What I did: `updateExt` by record patterns,
`| { pages = firstPages }, { pages = secondPages }, same => rewrite same in rfl`.
Microtypes get an `.ext` theorem (syntax.md); a one-field record like
`Update` doesn't. Fix: generate `T.ext` for every record, or add record eta
to conversion.

### 3. No pair equality lemma

`Set.containsFromList` and `Map.Spec.sameKeyDecide` turn set membership into
`(a, b) == (c, d)`, and nothing in std says that is
`a == c && b == d`. `rfl` fails on it:

```text
`Decidable.toBool (Pair.decMk rule.before x rule.after y (Nat.decEq rule.before x) (Nat.decEq rule.after y))` and `Decidable.toBool (Nat.decEq rule.before x) && Decidable.toBool (Nat.decEq rule.after y)` aren't equal
```

What I did: `pairEqual`, a `match` on the two `Nat.decEq`s, `rfl` in each arm.
Fix: `Pair.eqAnd` in std.

Fixed: std has `Pair.mkBeqMk`, `((x1, y1) == (x2, y2)) = (x1 == x2 ∧ y1 == y2)`
for any types with `DecEq` (Option/Option.sw); the proofs use it.

### 4. Missing `List.all`/`any` lemmas

Proved locally, each a few lines: `allTrue` (every element passes), `anyFalse`,
`allAnd` (`xs.all (x => p x && q x) = (xs.all p && xs.all q)`), and
`noneRelated` (`xs.all (x => !(ys.any (related x)))` is the same read with
`ys` outside). Fix: move them to std's toolkit.

Fixed: std has `List.allTrue`, `List.anyFalse`, `List.allAnd` (List/Toolkit.sw)
and `List.allNotAnyComm` (List/Sort.sw); the proofs use them.

### 5. `test` can't be a parameter name

`(test => Nat.addCancelLeft (Bool.toNat (test x)) …)` (copied from
`List.sortedPermEq`'s `q`, renamed for readability) gives

```text
[E-PARSE] Error: expected an expression, but found `test`
```

`test` is a keyword. What I did: `property`. Fix: say "`test` is a keyword"
in the message.

### Ranked

Std.Parse:

1. No `findAll` (item 1): the core of the puzzle had to be hand-written.
2. Scanning speed and memory (item 2): 1.2 GB for 180 KB.
3. No bounded repetition (item 3).
4. `Parse.mark()` inside a comparison passed as an argument (item 5).
5. The per-operation lemmas need the continuation spelled out (item 6).
6. `ensure` reports after the digits, not at the number (item 4).

General:

1. `rewrite` against unfolded goals (item 8), again.
2. `n + 0` and `if c then a else a` (item 9).
3. A record literal before the argument that fixes its type (item 7).
4. Missing `take`-snoc and `last`-of-append lemmas (item 10).
5. `|>` in `calc` steps (item 11).

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
"a repeated state repeats forever" (std's `Nat.pigeonhole` and
`Nat.iterateRepeatNeverNone`, since `walk` is the step iterated).
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
- `programSimulates` (`Proofs/Sightlines.sw`): the program's sightlines with
  any new obstruction on the map simulate the walk, when the lab's
  obstructions are on the map. Each row's and column's set holds exactly the
  obstructions on that line (`ofRepresents`, through the `Sightlines.of`
  fold), `Set.below`/`Set.above` find the nearest one ahead, and the walk
  there, one direction at a time, ends where `nextTurn` jumps to.
- `offRouteFree`: a new obstruction off the route of a guard who leaves
  never traps her, so part 2 needs only the route's positions.
- `routeSettled`: the route's positions are on the map and free, except the
  start.
- `part2Correct`: part 2 is the size of `trapPositions`, for a lab whose
  obstructions are on the map. `part2Loops`: `None` when she loops.

About 950 lines of proof, using no axiom but std's `Quot.sound`.

`part2Correct` needs the obstructions on the map: one off it to the right
or below would give the jump a turn the walk never makes, since she leaves
first. The parser guarantees it, and the parser (a rectangular map, exactly
one `^`, so the start is on the map) is tested, not proved. A test also runs
the jumping test against the step-by-step walk for every obstruction position
in the example.

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

Fixed: std has `Set.belowSome`, `Set.belowNone`, `Set.aboveSome` and
`Set.aboveNone` as above (`Set/Spec.sw`), from `Map.belowSome`,
`Map.belowNone`, `Map.aboveSome` and `Map.aboveNone` (`Map/Map.sw`, the entry
found and its value), which rest on list lemmas over sorted entries
(`Map.Spec.lastBelowGreatest`, `Map.Spec.findAboveLeast` and others in
`Map/Spec.sw`). Day 6 uses them to prove `Simulates` (`programSimulates`),
so `part2Correct` no longer takes it as a hypothesis.

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

Fixed: std has `Nat.pigeonhole` (`Nat/Pigeonhole.sw`; `n + 1` values below
`n` at `0, …, n` have a repeat, stated as day 6 had it, proved with
`List.any` over `List.range` instead of a search function), and
`Nat/IterateRepeat.sw`: `Nat.iterateAdd`, `Nat.iterateFixedLater` (a fixed
point, once reached, stays), `Nat.iterateRepeats` (after a value repeats at
`first < second`, every value is one of the first `second`) and
`Nat.iterateRepeatNeverNone` (a partial step, `Option.flatMap step`
iterated, that repeats a state still there at the repeat never reaches
`None`). Day 6's `pigeonhole`, `lastHit` and `repeatFrom` are gone, and
`repeatLoops` and `walkLater` are applications of these. The `Finite`
interface is still to do.

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

Fixed: neither conversion nor printing was the cause. After the
application, the search for `auto` dictionaries read the result type back
as a normal form, unfolding `keeps` into millions of nodes. It now reads back
at most 100,000 nodes of a normal form and otherwise keeps calls as calls
(`interfaces.rs`, `scanned`). Conversion already compares two calls of
the same definition by their arguments first, and messages already
shorten what they show. `stepA2` checks, and `filterSame` is gone:
`trapSetsSame` applies `Set.containsFilter` to the program's filter.
`rewrite` there, and `match patrolled: lab.patrol` against
`solvePart2 lab = None`, still run out: both work on the goal's normal form
by design (the `match` has to find `lab.patrol` inside `solvePart2`), which
is Day 2's item 3.

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

  Fixed: a `let` lambda whose body performs nothing (its calls of
  `filter`/`map` take pure callbacks) is a pure function, so its calls are
  plain calls. The error came from `Set.fromList`'s unfilled `Ord` argument,
  made while the call's result was in scope: an unknown is no longer taken
  to depend on that result, and the dependent-pair note is only given when
  the type itself mentions it. `parseLab` uses the `let` lambda again.
- A lambda with a return type, `(wanted: Cell): List Position => …`, is
  "`a block must end with an expression, not let`", pointing at the `let`.
  Fix: say lambdas don't take a return type (or allow one, as Scala and Lean
  do).

  Fixed: it's now "a lambda doesn't take a result type", at the `:`, with a
  note to annotate the body, `(x: A) => (body: B)`, or the `let`.
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

1. A trailing blank line is an error with a misleading message (item 1).
   Fix: let `Parse.all` allow trailing blank lines.
2. A missing section break reports the wrong thing (item 2). Fix: a
   `section` combinator, or label the line parsers in the guide's example.
3. `sections` doesn't fit two kinds of section (item 3). Fix: document the
   `lines`/`blankLine`/`lines` shape beside it, or add `section p`.
4. Parser names shadow value names (item 4). Fix: a naming convention in the
   guide.
5. Whole-input parsing is the run time and memory (Performance). Fix: the
   proposal's native text cursor, only if big inputs matter.

General:

1. `||` elaborating to `if b then True else False` inside effect-polymorphic
   lambdas (item 1): the most time lost, and the message gives no hint.
   Fix: plain `Bool.or` when the row is `Total`.
2. No record eta or `T.ext` (item 2). Fix: generate `T.ext` for records.
3. No pair equality lemma (item 3). Fix: `Pair.eqAnd` in std.
4. Missing `all`/`any` lemmas (item 4). Fix: add the four to std.
5. `test` as a name (item 5). Fix: name the keyword in the error.

## Day 7: Bridge Repair

Calibration equations, one per line: a test value, a colon, then numbers
(`3267: 81 40 27`). Part 1 adds up the test values of the equations that
some choice of `+` and `*` between the numbers, "always evaluated
left-to-right, not according to precedence rules", makes true. Part 2 adds
concatenation, "`12 || 345` would become `12345`" (part 2's wording from the
public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-07/README.txt>).
Answers on Matt's input: 66343330034722 and 637696070419031 (cross-checked
with a Python script, `/usr/bin/python3 -I`, that tries every operator
sequence with `itertools.product`; the example gives 3749 and 11387).
Compiler built from `main` at fd5e6bfd, 28 October 2026.

The input has 850 equations of 2 to 12 numbers, none of them 0 (a test
checks this), and test values of up to 15 digits.

### The program

The parser and the solver:

```stitchwort
def equationLine(): {Parse} Equation :=
  let testValue := nat()
  char ':'
  let numbers := many1 spacedNat
  { testValue, numbers }

def parseEquations (input: Text): {Fail} (List Equation) := Parse.eachLine input equationLine

def canMake (operators: List Operator) (first: Nat) (target: Nat): List Nat → Bool
  | Nil => target == first
  | Cons last earlier =>
    operators.any (operator =>
      match operator with
        | Add => last <= target && canMake operators first (target - last) earlier
        | Multiply =>
          if last != 0 then
            target % last == 0 && canMake operators first (target / last) earlier
          -- Anything times 0 is 0.
          else target == 0
        | Concatenate =>
          let place := placeValue last
          target % place == last && canMake operators first (target / place) earlier)

def couldBeTrue (operators: List Operator) (equation: Equation): Bool :=
  match equation.numbers with
    | Nil => False
    | Cons first rest => canMake operators first equation.testValue rest.reverse

def calibrationResult (operators: List Operator) (equations: List Equation): Nat :=
  equations.filter (couldBeTrue operators) |> .sumBy (equation => equation.testValue)

def solvePart1 (equations: List Equation): Nat := calibrationResult [Add, Multiply] equations

def solvePart2 (equations: List Equation): Nat := calibrationResult [Add, Multiply, Concatenate] equations
```

`canMake` works backwards from the test value: the last operator is undone,
which prunes almost every branch (a subtraction that would go below 0, a
division with a remainder, a value that doesn't end in the last number's
digits). `placeValue n` is `Nat.pow 10 (Nat.digitCount n)`. It printed
the right answers on the first run.

Because `%` and `/` need a proof that the divisor isn't 0, the program had to
say what multiplying by 0 means (anything times 0 is 0), so it is right for
every input, not only for inputs without 0, and no theorem needs the
assumption.

### Proved, for every list of equations

The spec (`Spec/Spec.sw`) is in the puzzle's words: `concatenate` is
`Nat.fromDigits` of the two numbers' digits appended ("combines the
digits"), `evaluate` folds the operators over the numbers from the left,
`combinations operators count` is every list of `count` operators, and an
equation `couldPossiblyBeTrue` when some combination evaluates to its test
value. `totalCalibrationResult` sums the test values of those equations.

- `part1Correct`, `part2Correct`: `solvePart1 equations = part1 equations`
  and the same for part 2, from `calibrationResultCorrect` and
  `couldBeTrueCorrect`, which hold for any list of operators.
- `part2AtLeastPart1`: `solvePart1 equations ≤ solvePart2 equations`, from
  `couldBeTrueMore` (more operators can make at least as much true) and
  `sumFilterMore` (a filter that keeps more sums to at least as much).
- `canMakeReaches`: the backwards search is the forwards search over every
  operator choice (`reaches`), so the pruning is sound and complete. Each
  operator is undone exactly: `undoAdd`; and `divModMatch`,
  `v * d + r = target` (for `r < d`) exactly when `target % d = r` and
  `target / d = v`, which is multiplication with `r = 0` and concatenation
  with `d` the place value.
- `combinationsReach`: `any` over all combinations is the forwards search.
- `combinationsComplete`, `combinationsSound`: `combinations` is exactly the
  lists of the right length made of allowed operators, so the spec's
  enumeration is "any combination".
- `concatenateArithmetic`: `concatenate a b = a * placeValue b + b`, by
  std's `Nat.fromDigitsAppend` and `Nat.fromDigitsDigits`;
  `belowPlaceValue`: `b < placeValue b`; `concatenateAtLeast`: both sides are
  at most the result.

About 290 lines of proof with no axioms, most of it checked on the first
try. Changing the program's `last <= target` to
`last < target` makes `canMakeReaches` fail with a counterexample
(`operators = [Add]`, `first = 0`, `reversed = [0]`, `target = 0`).

Not proved: the parser (tested, as on other days); that concatenation is
associative, which it isn't when the middle number is 0 (`(5 || 0) || 5` is
505, `5 || (0 || 5)` is 55); nothing needed it.

### 1. Std.Parse: no friction

`Parse.eachLine` with a four-line grammar and `Aoc.Common.spacedNat` read the
input, and every error message in the tests was the one I guessed before
running them (`line 1, column 4: expected ':'`, `line 2, column 6: expected a
number or the end`). One clash: the parser was first called `equation`, and
a lambda parameter `equation` in the proofs got

```text
[W-LAMBDA-SHADOW] Warning: this lambda's first parameter `equation` hides the function `equation`
```

(day 5's item 4 again). Renamed to `equationLine`, as day 2 has
`reportLine`. Fix: the guide's convention of a `Line` suffix for line
grammars.

### 2. `%` by a computed number: `auto` doesn't find the proof

```stitchwort
let place := placeValue last
target % place == last && …
```

```text
[E-AUTO-STUCK] Error: can't decide `placeValue last ≠ 0` here
  Note: establish it first, with `if h: … then … else …`
```

With `let positive := Nat.powSuccPos 9 (Nat.digits last).length` (a proof of
`0 < Nat.pow 10 …`) in scope, the same error: `auto` neither unfolds
`placeValue` nor turns `0 < d` into `d ≠ 0`. The note's suggestion, an `if`
whose `else` can never happen, would leave dead code. What worked: a theorem
saying exactly `placeValue number ≠ 0` next to `placeValue`, and
`let nonzero := placeValueNonzero last` before the `%`. For `last`, which can
be 0, `if last != 0 then` gave the fact, as the guide says.

Lean makes `a % 0 = a` and `a / 0 = 0` (`Nat.mod_zero`,
<https://lean-lang.org/doc/api/Init/Data/Nat/Div/Basic.html>), so no proof
is needed and none of this comes up; Scala and Haskell throw at run time.
Stitchwort's way paid off here: it made the program handle a 0 in the input
(item "The program" above). Fix: let `auto` use facts in scope through
`omega` (`0 < d`, or `1 ≤ d`, proves `d ≠ 0`) and unfold a definition one
step.

Fixed: `auto` proves `d ≠ 0` from a fact `0 < d`, `1 ≤ d` or `k + 1 ≤ d` in
scope, and, in a module that loads `omega`'s library (any that uses `omega`,
`rewrite` or `cases`, or a std file that does), proves an arithmetic goal it
can't decide by `omega` over the facts in scope, with a small search budget
(`h: a < b` gives `b - a ≠ 0`). Unfolding needed nothing new: `auto` already
unfolds a definition to match a decision procedure, and what was missing was
one for powers, `Nat.decPowSuccNotZero` (`Nat.pow (Succ b) e ≠ 0`). The
program's `placeValueNonzero` and its two `let nonzero` lines are gone.

### 3. Missing std

- `Nat.digitCount` (or a place value): `(Nat.digits n).length` is written
  out here and as `digitCount` in 2025 day 2's proofs. With it, a lemma
  `Nat.digitCountPowPos` (`Nat.pow 10 (Nat.digitCount n) ≠ 0`) would have
  avoided item 2. `Nat.powSuccPos` needs the base written as `Succ 9`.
- No power operator: `Nat.pow 10 k`, where Scala has `math.pow` (on
  `Double`), Haskell `10 ^ k`, Lean `10 ^ k`.
- List lemmas written here: `anyFlatMap`, `anyOr` (`any` of an `||`),
  `anyComm` (two `any`s swap), `reverseReverse`, `reverseCons`
  (`(Cons x xs).reverse = xs.reverse.append [x]`, via `reverseOntoAppend`),
  and `sumFilterMore` (a filter that keeps more has at least the sum). Lean
  core has `List.reverse_reverse` and `List.any_flatMap`
  (<https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Lemmas.html>).
- Nat had what concatenation needed: `Nat.fromDigitsAppend`,
  `Nat.fromDigitsDigits`, `Nat.ltPowTenDigits`, `Nat.divUnique`,
  `Nat.modUnique`, `Nat.divModEq`. Mathlib's counterparts
  are `Nat.ofDigits_append` and `Nat.lt_base_pow_length_digits`
  (<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Digits/Defs.html>),
  little-endian where std's digits are most significant first.

Fixed: std has `Nat.digitCount` with `Nat.digitCountPos` (`0 < Nat.digitCount
n`), used here and in 2025 day 2's proofs in place of their own; and
`List.anyFlatMap`, `List.anyOr`, `List.anyComm`, `List.reverseReverse`,
`List.reverseCons` (with `List.reverseOntoTwice` and `List.reverseOntoAppend`)
and `List.sumByFilterMono`, which the proofs now use. The power operator is
still missing.

### 4. Holes left for the proof argument

```stitchwort
List.sumByLe xs _ _ (x => match kept: keep1 x with
  | True => rewrite included x kept in Nat.leRefl (value x)
  | False => Nat.zeroLe _)
```

The two `_`s should come from the goal (after `rewrite List.sumByFilter`, it
is `sumBy xs (x => if keep1 x …) ≤ sumBy xs (x => if keep2 x …)`), but they
were still unsolved inside the lambda:

```text
[E-REWRITE-NOTHING] Error: `rewrite` found no `keep2 x` in the goal
  Note 1: goal: `?14 a keep1 keep2 value xs included x ≤ ?13 a keep1 keep2 value xs included x`
[E-UNSOLVED] Error: can't work out an implicit argument
    | False => Nat.zeroLe _)
```

Day 1's item 4 again. Written out, both functions, and `Nat.zeroLe`'s
argument, it checked. Fix: unify the result type with the goal before
checking the arguments.

Fixed, as far as it can be: the two `_`s were already filled (the lambda is
checked again once the call's type meets the goal); the `rewrite` error was
left over from the first try against `?14 … ≤ ?13 …`, which was undone but
its arm's error kept, and is no longer reported. The `E-UNSOLVED` was the
real failure: `0 ≤ n` computes to `True = True` whatever `n` is, so the
goal says nothing about `Nat.zeroLe`'s argument, which stays written out.
`sumFilterMore` now leaves both functions as `_`.

### 5. Goals unfold too far, and a `match` in a statement is opaque

- The concatenation goal showed `List.foldLeft (List.append (Nat.digits
  value) (Nat.digits last)) 0 (acc digit => acc * 10 + digit)` where the
  spec says `concatenate value last`, and a mutation's error showed one
  list as `List.reverse earlier` on one side and `List.reverseOnto earlier
  []` on the other. Day 2's item 3 (keep definitions folded) again.
- A lemma stated about the program's `match operator with …` (copied from
  `canMake`) had the goal `Aoc.Year2024.Day07.Proofs.undoCorrect.%match1
  operators first last earlier target operator = …`: the `match` was lifted
  out under an internal name, so nothing could be proved about it by name.
  What worked: splitting on the operator inside `canMakeReaches`, where each
  arm's goal computed to the program's branch. Fix: show and compare lifted
  matches by their bodies.

### 6. Smaller

- `type Operator = Add | Multiply | Concatenate` is an `E-PARSE`: a sum type
  needs a `|` before its first constructor. The message says so. Haskell
  (`data Op = Add | Mul`) doesn't; Scala 3 writes `enum Op { case Add, Mul }`.
  Fix: accept the first constructor without `|`.
- What went well: `rewrite` through `List.anyCong`, `match` on `last` that
  made the program's `if last != 0` compute in each arm, `omega` on the
  `undoAdd` cases, and the counterexample search on a wrong program.

### Performance

`stitchwort run` on the input takes 0.44 to 0.70 s, of which about 0.35 s
is the same run on the example (loading and checking the program); the
machine (`machine aoc_agrees`) runs it in 0.14 s. The same backwards search
in CPython takes 0.04 s of user time. Nothing needed tuning.

For comparison, the spec itself (every operator sequence, concatenation
through digit lists) as a test on the real input took 91 s for both parts,
against 5.6 s of user time for a Python script that tries every sequence
with string concatenation: about 16 times slower, in line with day 6's
factor of 12. Not kept: the proofs cover it.

### Size and time

Release build, on a machine busy with other work:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day07.Proofs` | 1.1 s |
| `stitchwort check --no-cache Aoc.Year2024.Day07` | 1.3 s |
| `stitchwort test --no-cache Aoc.Year2024.Day07` (30 tests) | 1.9 s |
| `stitchwort test Aoc.Year2024.Day07` (warm) | 0.6 s |
| `stitchwort run Aoc.Year2024.Day07.main` on the input | 0.44 to 0.70 s |
| `stitchwort check --no-cache` (whole project) | 15 s |

79 lines of program, 47 of spec, 290 of proofs, 79 of tests.

### Ranked

1. `auto` can't prove `d ≠ 0` from facts in scope (item 2). Fix: `omega`
   over the facts in scope, and unfold one step.
2. Holes not solved from the goal before the proof argument (item 4). Fix:
   unify the result type first.
3. Lifted `match`es in goals and goals unfolded too far (item 5). Fix: fold
   definitions in goals; show lifted matches by their bodies.
4. Missing std (item 3). Fix: `Nat.digitCount` with its positivity lemma,
   and the six list lemmas, in std.
5. No power operator (item 3). Fix: `^` for `Nat.pow`.
6. Sum types need a leading `|` (item 6). Fix: accept it without.
7. Parser and value names clash (item 1). Fix: a `Line` suffix convention in
   the guide.

## Day 8: Resonant Collinearity

A map of antennas, each a letter or digit naming its frequency. Part 1:
"an antinode occurs at any point that is perfectly in line with two antennas
of the same frequency - but only when one of the antennas is twice as far
away as the other"; count the "unique locations within the bounds of the
map". Part 2: "an antinode occurs at any grid position exactly in line with
at least two antennas of the same frequency, regardless of distance" (part
2's wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-08/README.txt>).
Answers on Matt's input: 344 and 1182 (cross-checked with a Python script,
`/usr/bin/python3 -I`, that tests every cell against every pair with the
cross product and squared distances; the example gives 14 and 34).
Compiler built from `main` at 99e1e770, 28 October 2026.

The input is 50 by 50 with 207 antennas of 54 frequencies, at least two of
each (a test checks every antenna has a partner).

### The puzzle's rule has a third case

Read literally, "in line, one antenna twice as far as the other" also holds
between two antennas, a third of the way along, when their offset is a
multiple of 3 in both directions: with antennas at (0, 0) and (3, 3), the
point (1, 1) is in line, 2√2 from one and √2 from the other. The puzzle
then says "for any pair of antennas with the same frequency, there are two
antinodes, one on either side of them", which leaves those out. The spec
follows the rule, so the program adds the point between when it is a grid
point; a test shows a pair that has them (`antinodes between two
antennas`), and another that no pair in Matt's input does, so both
readings give 344 there.

### The program

The parser and the solver:

```stitchwort
def cell(): {Parse} (Option Char) :=
  let char := Parse.satisfy "'.', a letter or a digit" (char => char == '.' || char.isAsciiAlphanumeric)
  if char == '.' then None else Some char

def parseCity (input: Text): {Fail} City :=
  let rows := Parse.all input (() => Parse.grid cell)
  let width := rows.headOr [] |> .length
  let antennas :=
    rows.withIndex.flatMap (((row, cells)) =>
      Fail.ensure (cells.length == width) "line ${row + 1}: expected ${width} characters, as on the first line, got ${cells.length}"
      cells.withIndex.filterMap (((column, cell)) =>
        cell.map (frequency => ({ frequency, position = { row = row.toInt, column = column.toInt } }: Antenna))))
  { height = rows.length, width, antennas }

def antinodesOf (far: Position) (near: Position): List Position :=
  let difference := near.minus far
  let past := near.plus difference
  if difference.row % 3 == 0 && difference.column % 3 == 0 then
    [past, near.minus { row = difference.row / 3, column = difference.column / 3 }]
  else [past]

def stepToward (start: Position) (end: Position): Position :=
  let difference := end.minus start
  difference.divideBy (Nat.gcd difference.row.natAbs difference.column.natAbs)

def City.harmonics (city: City) (start: Position) (end: Position): List Position :=
  let step := stepToward start end
  List.range (Nat.max city.height city.width)
    |> .flatMap (count => [start.plus (step.times count.toInt), start.minus (step.times count.toInt)])

def solvePart1 (city: City): Nat :=
  city.antennaPairs |> .flatMap (((far, near)) => antinodesOf far near) |> city.locations |> .size

def solvePart2 (city: City): Nat :=
  city.antennaPairs |> .flatMap (((start, end)) => city.harmonics start end) |> city.locations |> .size
```

`Position` has `Int` coordinates, since antinodes can fall off the map;
`City.locations` keeps those on the map, in a `Set`. `antennaPairs` is
every ordered pair of antennas with the same frequency at different places.
Part 2 steps from an antenna by the offset to the other divided by the gcd
of its parts, both ways, as many steps as the map is high or wide. It
printed the right answers on the first run.

`Parse.grid` fitted: a one-character grammar per cell, and a check that
every row is as long as the first, which `Parse.grid` leaves to the caller
("Rows may differ in length"). The error for a bad character is
`line 1, column 3: expected '.', a letter or a digit or a line break or the end`.

### Proved, for every city

The spec (`Spec/Spec.sw`) is in the puzzle's words: `inLine point first
second` is a zero cross product of the directions from `point` to the two
antennas; `twiceAsFar point far near` compares squared distances
(`|point→far|² = 4 |point→near|²`); `twoAntennas` is "two antennas of the
same frequency", at different places, either way round; and the answer is
the size of the set of map locations (every row and column) where the
test holds.

- `part1Correct`: `solvePart1 city = part1 city`, for every city. The core
  is `twiceAsFarCases`: with `u` and `v` the directions to the two
  antennas, `u × v = 0` and `|u|² = 4|v|²` give `u = 2v` or `u = -2v`. By
  Lagrange's identity, `(u·v)² = |u|²|v|² - (u×v)² = (2|v|²)²`, so
  `u·v = ±2|v|²`, and then `|u ∓ 2v|² = 0`. `u = 2v` is the point past the
  near antenna; `u = -2v` is `3 p = far + 2 near`, the point a third of the
  way, which is a grid point exactly when 3 divides the offset
  (`thirdOf`, `thirdBack`). `antinodesOfCorrect` puts these together for
  the program's `antinodesOf`.
- `part2Correct`: `solvePart2 city = part2 city`, for every city whose
  antennas are on the map. `stepFacts`: the offset between the antennas is
  a nonzero multiple of `stepToward`'s step, and the step's parts are
  coprime: `s * er + t * ec = 1` for some integers, from Bézout's identity
  for `Nat.gcd` (`gcdBezout`) and the gcd dividing both parts
  (`gcdDivides`). Then `crossOnLine` (a whole number of steps is in line)
  and `onLineOfCross`: a point in line is `s * (pr - fr) + t * (pc - fc)`
  steps from the antenna, since the cross product makes its offset
  parallel to the step. `stepsBound`: on the map that is fewer steps than
  the map is high (or wide, if the step doesn't move rows), so `harmonics`
  reaches it (`harmonicsCorrect`).
- `locationsCorrect`, shared by both: when a pair's points are exactly the
  map locations where the spec's test holds for that pair, the program's
  set of locations is the spec's (by `Set.ext`).
- `part2IncludesPart1`: the spec's part 1 locations are a subset of part
  2's, for every city.
- `antennasAreAntinodes`: "some of the new antinodes will occur at the
  position of each antenna (unless that antenna is the only one of its
  frequency)": an antenna with a partner is a part 2 location.

About 620 lines of proof; `Quot.sound` is the only axiom, through
`Set.ext` (`harmonicsCorrect`, `antinodesOfCorrect` and the gcd lemmas use
none). Changing `harmonics` to step only `Nat.min city.height city.width`
times makes `harmonicsOfSteps` fail with a counterexample (a map 0 high
and 1 wide).

Not proved: the parser (tested); that `solvePart1 city ≤ solvePart2 city`
(the subset is proved, but std has no lemma that a subset is no bigger,
item 4); and part 2 without the hypothesis that antennas are on the map,
which would be false: antennas at rows -100 and -99 of column 0 are in line
with (0, 0), 100 steps away, more than `harmonics` takes on a small map.
The parser only makes antennas on the map.

### 1. `omega` doesn't work on `Int`

Every inequality and most equations here are about `Int`s, and `omega`
stops at the first:

```text
[E-OMEGA] Error: `omega` can't prove `x + 1 ≤ y`
  ╰──── unsupported structure: this goal isn't linear arithmetic on `Nat`
```

(syntax.md lists `Int` under "Not yet".) What I did instead: equations by
`ring`, and anything with an order or a remainder by cases on the
constructors down to `Nat`, where `omega` works. That is all of
`Proofs/Ints.sw`: `a - b = 0` gives `a = b`, no zero divisors, cancelling a
nonzero factor, two squares summing to 0, equal squares, `(3 * k) / 3 = k`,
and in `Part2.sw` exact division, `|x * y| = |x| * |y|`, and two numbers
below `n` being less than `n` apart. Each is a few lines once split; in
Lean, `omega` is "for resolving integer and natural linear arithmetic
problems"
(<https://lean-lang.org/doc/api/Lean/Elab/Tactic/Omega/Frontend.html>).
Fix: `Int` atoms in `omega` (the certificate format already has them).

Fixed: `omega` works on `Int` (`+`, `-`, negation, multiplication and
`/`, `%` by a number, `n.toInt`, `≤ < = ≠`). `subEqZero`, `negOfNatZero`,
`thirdOf` and `thirdBack` are now `omega`; `modThreeMul`, `divThreeMul`
and `thirdBackOf` (the workaround for finding 3) are gone, and two
`omega [Int.ofNatInjective …]` are plain `omega`. `Proofs/` went from 625
lines to 601 (`Ints.sw` 86 to 71, `Part1.sw` 155 to 147, `Part2.sw` 239 to
238). What stays by cases is about products of unknowns, `Int.natAbs` and
`Int.sign`, which `omega` treats as unknowns.

### 2. `ring [h]` adds each hypothesis once

`ring [h1, h2]` checks that the goal's two sides differ by exactly
`(l1 - r1) + (l2 - r2)`. A proof that needs `4 * h1` or `x * h2` has to
build it with `Eq.cong ((x: Int) => 4 * x) h1`, and a hypothesis that
counts negatively has to be flipped with `Eq.sym`. Lagrange's identity
step needed the cross product's equation squared and turned round
(`0 = (u × v) * (u × v)`) and the distance equation multiplied by `|v|²`.
The error says how it combined them, which made the orientation easy to
fix:

```text
Note 1: with the hypotheses `l = r` added, the left side plus every `r` against the right side plus every `l`:
```

What went well: once oriented, `ring` proved every polynomial step here,
including the degree-4 identity. Mathlib's `linear_combination` takes the
coefficients: `linear_combination (h1 + h2) / 2`
(<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html>).
Fix: coefficients in `ring [4 * h1 - x * h2]`.

Fixed: `ring [4 * h1, -h2, x * h3]` takes coefficients, any `Int` or `Nat`
expression, and a failure shows what is left over. Every
`Eq.cong ((x: Int) => c * x) h` is now `c * h`, the squared cross product
is `(ur * vc - uc * vr) * cross`, and the `Eq.sym`s went (a hypothesis
without a `-` is still tried both ways round). `Proofs/` went from 601
lines to 592 (`Part1.sw` 147 to 145, `Part2.sw` 238 to 231, `Gcd.sw` 37,
the same length with shorter lines).

### 3. Terms that print the same but aren't, around `/` and `%`

`(n - f) % 3` carries a hidden proof that 3 isn't 0. With
`Int.divAddMod (n - f) 3` as a hypothesis, `ring` failed with sides that
are the same polynomial as printed:

```text
[E-RING] Error: `ring` can't prove `f - p = 0 - (2 * (n - p))`
  Note 2: left:  2 * p + n + ((n - f) % 3)
  Note 3: right: 2 * p + n + 3 * ((n - f) / 3) + ((n - f) % 3) - 3 * ((n - f) / 3)
  Note 4: the left side has `((n - f) % 3) + 3 * ((n - f) / 3)` more and `3 * ((n - f) / 3) + ((n - f) % 3)` less
```

Restating the law's type with a `let` didn't help. What worked: the same
lemma over plain variables `quotient` and `remainder` (`thirdBackOf`),
applied to the real terms, where the kernel's conversion accepted them.

Related, and silent: `match c: <the program's if condition> with` didn't
replace the condition in the goal, written as the program writes it or as
the goal shows it (`near.row + Int.neg far.row`, since goals show `-`
unfolded). I am not sure which of the two (the hidden proof, or the
unfolded `-`) stops it. A lemma `ifSplit` taking the condition as a
variable didn't help either, because unification doesn't unfold
`antinodesOf` to find the `if`:

```text
expected `point ∈ antinodesOf far near ↔ …`, but this has type `point ∈ (if Decidable.toBool (DecEq.%decide … … …) && Decidable.toBool (DecEq.%decide … … …) then ?2 far near point else ?3 far near point) ↔ …`
```

What worked: `antinodesOfUnfold`, the program restated with the condition
written out, proved by `rfl`, then a lemma about that `if` with the
condition as a variable (`antinodesIff`). Fix: compare atoms and match
scrutinees up to proofs (proof irrelevance), and print hidden arguments
when two printed terms differ.

### 4. Missing std

- `Nat.gcd`: added to std (`Nat/Divides.sw`, Euclid's algorithm with
  `decreasing`), with a test. Its facts are written here (`Proofs/Gcd.sw`,
  37 lines): `gcdDivides` and `gcdBezout`, by the generated
  `Nat.gcd.unfold`. Lean core has `Nat.gcd` with `Nat.gcd_dvd_left`
  (<https://lean-lang.org/doc/api/Init/Data/Nat/Gcd.html>), Mathlib
  `Nat.gcd_eq_gcd_ab` (Bézout,
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Int/GCD.html>),
  and Haskell's Prelude exports `gcd`
  (<https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Prelude.html>).
- `Char.isAsciiLetter` and `Char.isAsciiAlphanumeric`: added to std
  (`Text/Text.sw`), with tests; std had `digitValue` and the whitespace
  tests only.
- Integer vectors: `Position.plus`, `minus`, `times` and `divideBy` are
  written in the program. Fine as program code, but every grid day with
  directions writes them again.
- The `Int` lemmas of item 1.
- No lemma that a subset is no bigger (`Set.isSubset a b = True →
  a.size ≤ b.size`), so part 2 ⊇ part 1 is stated on the sets, not on the
  counts.
- `List.each` (run an effect on each element) and `List.contains`:

  ```text
  [E-UNKNOWN-FIELD] Error: `List` has no field or function `each`
  [E-UNKNOWN-FIELD] Error: `List` has no field or function `contains`
  ```

  What I did instead: the row-length check inside the `flatMap` that
  builds the antennas, and `.any (== position)`.

### 5. A lifted `match` can't be named

`stepToward` first had the `match` on the gcd inline. A lemma restating it
with the `match` as a helper failed, with a clear note:

```text
Note 3: `(match …)` is a `match` written inside `Aoc.Year2024.Day08.stepToward`, marked "this `match`" above; the compiler turned it into a function that source can't name. The same `match` written again is another such function, equal to it only if neither calls the definition it's written in. To state a lemma about it, make it a local `def` in its arm and refer to it as `owner.name` …
```

What I did instead: moved it into `Position.divideBy`, which reads as well.
Day 7's item 5 again. Fix: let `rfl` see two lifted matches with the same
body as equal.

### 6. Inference

- A lambda's parameter type isn't taken from a later argument when the
  lambda is the function of `Eq.cong`: `Eq.cong (x => 4 * x) h` failed with

  ```text
  [E-TYPE-MISMATCH] Error: type mismatch
    expected `?9 ur uc vr vc cross distance same = ?10 ur uc vr vc cross distance same`, but this has type `2 * (vr * vr + (vc * vc)) = ur * vr + (uc * vc)`
  ```

  and `Eq.cong ((x: Int) => 4 * x) h` worked. The message doesn't say the
  lambda is the problem. The same for `List.memFlatMapIntro (count => …)`
  (`can't tell what count is, so can't look up .toInt`) and
  `List.anyElim (other => … other.position …)`.
- `let columnMoves := (z: step.column = 0) => omega [...]` is
  "`omega` needs to know what it proves"; written
  `let columnMoves: Not (step.column = 0) := z => omega [...]` it worked.
- In the program, `auto` doesn't see `Nat.toInt g ≠ 0` from `g != 0`:

  ```text
  [E-AUTO-STUCK] Error: can't decide `Nat.toInt g ≠ 0` here
  ```

  What I did instead: match the gcd against `Succ below` and divide by
  `(Succ below).toInt`, which `auto` decides. Fix: `auto` could carry
  `≠ 0` through `Nat.toInt`.

### 7. Smaller

- `if h: … then … else …` can't have proofs as branches
  (`[E-UNIVERSE] Error: if can't choose between proofs yet`; the note says
  to `match` on the `Bool`, which worked).
- `cases` is a keyword, so not a parameter name.
- `rewrite … in` followed by a `let` on the next line is
  `a block must end with an expression, not let` (day 4's item 8). Moved
  the `let` before the `rewrite`.
- A well-founded definition doesn't unfold by `rfl`
  (`computing the right side gives Nat.gcd (Succ c) (a - (Nat.divFuel a a (Succ c) * Succ c))`);
  `rewrite Nat.gcd.unfold a (Succ c) in rfl` did it, as the guide says.
- What went well: `locationsCorrect`, the set-equality plumbing over
  `flatMap`, `filter` and `Set.fromList`, checked on the first try;
  `omega` closed `Int` constructor cases with `/` and `%` by 3 once they
  were `Nat` (`Eq.cong OfNat (omega)`); pattern-matching `{ row = OfNat
  row, column = NegSucc column }` split the on-map cases neatly.

### Performance

`stitchwort run` on the input takes 0.67 s of user time, of which about
0.58 s is the same run on the example (loading and checking); the Python
cross-check, which tests every cell against every pair, 0.31 s. The spec as
a test on the real input (2,500 locations, each against all 207 × 207
pairs of antennas) wasn't run.

### Size and time

Release build, on a machine busy with other work:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day08.Proofs` | 2.6 s |
| `stitchwort check --no-cache Aoc.Year2024.Day08` | 1.8 s |
| `stitchwort test --no-cache Aoc.Year2024.Day08` (28 tests) | 4.2 s |
| `stitchwort test Aoc.Year2024.Day08` (warm) | 2.1 s |
| `stitchwort run Aoc.Year2024.Day08.main` on the input | 0.67 s |
| `stitchwort check --no-cache` (whole project) | 14 s |

101 lines of program, 55 of spec, 625 of proofs, 149 of tests.

### Ranked

1. `omega` has no `Int` (item 1). Fix: `Int` atoms in `omega`.
2. Terms that print the same but differ by a hidden proof, and a silent
   `match` that doesn't abstract (item 3). Fix: compare up to proofs, and
   print hidden arguments when printed terms are equal.
3. `ring [h]` without coefficients (item 2). Fix: `ring [4 * h1 - x * h2]`.
4. Missing std (item 4). Fix: `Nat.gcd`'s divisibility and Bézout lemmas,
   the `Int` lemmas, `Set.size` of a subset, and `List.each`/`contains`.
5. Lambda parameter types not taken from the proof argument (item 6). Fix:
   check the other arguments first, and name the lambda in the message.
6. Lifted `match`es (item 5). Fix: `rfl` across lifted matches with the
   same body.
7. `auto` and `Nat.toInt` (item 6). Fix: carry `≠ 0` through `Nat.toInt`.
8. The puzzle's rule has a third case (above). Not a language issue: the
   spec follows the rule, and a test shows the input doesn't hit it.

## Day 9: Disk Fragmenter

One line of 19,999 digits, a "disk map" whose digits alternate between the
length of a file and the length of the free space after it; the files are
numbered 0, 1, 2, … in order. Part 1 moves "file blocks one at a time from
the end of the disk to the leftmost free space block (until there are no
gaps remaining between file blocks)"; part 2 moves "whole files to the
leftmost span of free space blocks that could fit the file", "each file
exactly once in order of decreasing file ID number", and a file with no such
span to its left doesn't move (part 2's wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-09/README.txt>).
Each answer is the checksum: the sum of each file block's position times its
file's number.
Answers on Matt's input: 6242766523059 and 6272188244509 (cross-checked with
two independent Python scripts, `/usr/bin/python3 -I`: a literal one that
moves one block, or one file, at a time over a list of blocks, and a fast one
with a heap of free starts per length; the example gives 1928 and 2858, and
"12345" gives 60 and 132). Compiler built from `main` at 2c21d65c, 28
October 2026.

The disk has 10,000 files, 94,500 blocks (49,556 of them file blocks) and 984
free spans of length 0; no file has length 0 (tests check both).

### The program

```stitchwort
def diskMapLine(): {Parse} (List Nat) := many1 (() => digit().toNat)

def parseDiskMap (input: Text): {Fail} (List Nat) := Parse.all input diskMapLine

def fillFront: (blocks: List (Option Nat)) → (moving: List Nat) → (count: Nat) → List (Option Nat)
  | blocks, moving, Zero => List.replicate blocks.length None
  | Nil, moving, Succ count => Nil
  | Cons (Some id) rest, moving, Succ count => Cons (Some id) (fillFront rest moving count)
  | Cons None rest, Nil, Succ count => Cons None (fillFront rest Nil count)
  | Cons None rest, Cons id moving, Succ count => Cons (Some id) (fillFront rest moving count)

def compactBlocks (blocks: List (Option Nat)): List (Option Nat) :=
  let files := fileBlocks blocks
  fillFront blocks files.reverse files.length

def solvePart1 (diskMap: List Nat): Nat := blocks diskMap |> compactBlocks |> checksum

def moveFile (free: FreeSpace) (file: File): (FreeSpace, File) :=
  match free.leftmostFit file.span.length file.span.start with
    | None => (free, file)
    | Some span =>
      let rest: Span := { start = span.start + file.span.length, length = span.length - file.span.length }
      (free.remove span |> .add rest, { file | span = { file.span | start = span.start } })

def compactFiles (diskMap: List Nat): List File :=
  let layout := layoutFrom 0 0 diskMap
  layout.fst.reverse.mapAccumLeft (FreeSpace.of (joinTouching layout.snd)) moveFile |> .snd

def solvePart2 (diskMap: List Nat): Nat := compactFiles diskMap |> .sumBy fileChecksum
```

The domain model is the disk map's lengths; a block is `Option Nat`, `Some
id` for a block of file `id` and `None` for free space.

Part 1 needs no moves at all: when it ends, the first `n` blocks (`n` the
number of file blocks) are files, each keeping its own file block or, where
it was free, taking the next file block from the end. `fillFront` is that,
one walk front to back with the file blocks reversed as the supply: linear,
on lists, with no array or second pointer.

Part 2 keeps `FreeSpace`, the starts of the free spans of each length
(`Map Nat (Set Nat)`). `leftmostFit` takes the least start of every length
at least the file's (at most 9), the least of those, and keeps it if it is
before the file. A moved file fills the front of its span and the rest goes
back under its new length. The space a file leaves is never added, since
every file still to move is to its left. `mapAccumLeft` threads the map
through the files, highest number first.

A file of length 0 makes two free spans that touch, where the spec sees one
run, so a file that fits the run fit neither span (`"11023"` is `0...222`;
file 2 fits at block 1). `joinTouching` joins them. The real input has no
such file, so the answers were right without it; without `joinTouching` two
of the spec-agreement tests on small disks fail.

### Proved, for every disk map

The spec (`Spec/Spec.sw`) is the puzzle's, block by block, over the
program's `blocks` (the expansion, `"00...111...2..."`): `moveLastBlock`
passes the file blocks at the front and gives the first free block the last
file block, if there is one after it; `hasGap` is a free block with a file
block after it; `compactOneAtATime moves` repeats the move while there is a
gap, at most `moves` times; `part1` uses the disk's length as `moves`, then
`filesystemChecksum`, which skips free blocks ("If a block contains free
space, skip it instead"). For part 2, `moveWholeFile` finds the file's first
block and its length, the first start, left to right, that is free for that
length and ends before the file, and writes the file there and frees its old
blocks; `compactWholeFiles` folds it over the file numbers from the highest
down.

Part 1, all of it (`Proofs/Part1.sw`, 214 lines):

- `part1Correct`: `solvePart1 diskMap = part1 diskMap`.
- `part1NoGapsLeft`: after the disk's length in moves no gap is left, so the
  bound in the spec never cuts it short.
- `stepsFill`: with at least as many moves as blocks, the moves give
  `compactBlocks`. Induction on the disk's length (`decreasing
  blocks.length`), since after a move at a free front block the rest is the
  same length with its last file block freed. The steps: `compactFile` (a
  file block at the front stays), `compactGap` (a free one takes the last
  file block, and the rest compacts with that block freed), `compactFree`
  (no file block after it: nothing moves), `stepsPastFile` (moves happen
  behind a file block at the front). `compactGap` rests on `fillFront` never
  looking past its first `count` blocks (`fillFrontFreeLast`) or using more
  than `count` of the blocks it moves (`fillFrontAppend`).
- `checksumCorrect`: the program's checksum (a `sumBy`, 0 for free blocks)
  is the spec's `filterMap` then `sum` (`sumFilterMap`).

Changing the program to `fillFront blocks files files.length` (no reverse)
makes `compactFile` and `compactGap` fail, each with a counterexample.

Part 2, in part (`Proofs/Part2.sw`, 142 lines):

- `eachFileOnce`: the moved files are the disk map's files, each once,
  highest number first, with their numbers and lengths (through std's
  `mapAccumLeftList` and `mapZipWithScanLeft`).
- `filesMoveLeft`: zipped with the files they came from, each moved file
  starts at or before where it was (`MovedLeft`; `fitBefore` reads it from
  `leftmostFit`'s `.filter`).
- `part2KeepsBlocks`: the moved files' blocks are a permutation
  (`List.Perm`) of the disk's file blocks (`layoutBlocks`: the files' blocks
  are `fileBlocks (blocks diskMap)`; `permFlatMapReverse`).
- `fileChecksumCorrect`: a file's part of the checksum is the spec's
  `filesystemChecksum` of a disk holding just that file, where it is.

Not proved: `solvePart2 = part2`. What it needs, and the proofs lack:
(1) an invariant that the `FreeSpace` map holds exactly the maximal free
runs left of the files still to move, as the spec's disk has them at that
step: specs of `Map.alter`, `Map.adjust`, `Set.insert`, `Set.remove` and
`Set.min` together, and of `joinTouching`; (2) that `leftmostFit` finds the
spec's first fitting start (the least start over the lengths that fit is the
leftmost long-enough run); (3) that moved files don't overlap, so the sum of
`fileChecksum`s is one disk's checksum; (4) the spec's `moveWholeFile` read
back as "the file is at `start`, `length` blocks", which needs it contiguous
before each move. Items 1 and 4 are most of the work: the spec's disk is
index-based (`findIndex`, `drop`/`take`, `mapWithIndex`) and the program's is
spans, and the invariant joins the two. I'd guess a day 6–sized proof
(around 1,000 lines). The tests check agreement instead: the example's moves
picture by picture, 14 small disks (the zero-length cases among them) and
the first 99 digits of the real input, both parts against the spec.

### 1. Std.Parse: little friction, one confusing column

`many1 (() => digit().toNat)` and `Parse.all` read the line, and the
messages were right, with one exception. The first version used
`Parse.line` (one final line break allowed). On `"12\n34\n"` it said

```text
column 4: expected the end of the line, got '3'
```

The `3` is at line 2, column 1: `Parse.line` counts columns on past the line
break and gives no line. `Parse.all` says `line 2, column 1: expected the end
of the input, got '3'`, so I used it. It also names the same end two ways:
`line 1, column 3: expected a digit or the end of the line, got 'x'`, but
`line 1, column 1: expected a digit, got the end of the input`. Fix:
`Parse.line` reports what follows its line break as line 2, or says
"expected nothing after the line break".

### 2. An ability's operations are in scope without importing them

With `import Std (…, Parse, …)` and `import Std.Parse (digit, many1)`, a
lambda `(span joined => …)` in a `foldRight` got

```text
[W-LAMBDA-SHADOW] Warning: this lambda's first parameter `span` hides the function `span`
  Note: if you meant to pass a lambda to `span`, put it in brackets: `span (joined => …)`; otherwise rename the parameter
```

The `span` is `Parse`'s operation (`(Char → Bool) → {Parse} (List Char)`):
importing the ability brings its operations in unqualified, while
`takeWhile`, a function, wasn't in scope. With a type `Span` and a field
`span` in the file it was puzzling until a probe (`def probe: Nat := span`)
showed the type. Renamed to `earlier`. Fix: name it in full in the warning
(`Parse.span`), and import operations by name, as functions are.

### 3. Inference: record literals and lambdas before what fixes their type

- `Cons { id, span = … } later.fst` is an `E-PARSE` ("braces after `Cons`
  name its fields, and take no further arguments"), day 1's item 7 again;
  the note's `Cons ({ … }) …` works.
- `.map (start => { start, length = entry.fst })` in a pipeline ending in
  `Option Span` got `[E-CANNOT-INFER] Error: can't tell which record type
  this record literal is`, and so did `let rest := { start = …, length = …
  }`. Both needed `: Span`.
- In a proof, `Option.filterEqSome _ (found => found.start < before) span
  fit`, where `span: Span` is the next argument, got ``can't tell what
  `found` is, so can't look up `.start` ``. It needed `(found: Span)`.

Fix: check lambda and record-literal arguments after a call's other
arguments.

### 4. A confusing error: `Effect.CompD`

`blocks.map (…) |> .joinWith ""`, to join a `List Text`, got

```text
[E-UNKNOWN-FIELD] Error: `List` has no field or function `joinWith`
  looked in `Effect.CompD` or `List`
```

`Text.joinWith` takes the list first, but a `List` receiver looks only in
`List`, and `Effect.CompD` is an internal name. Wrote
`Text.joinWith (blocks.map …) ""`. Haskell's `Data.List` has
`intercalate :: [a] -> [[a]] -> [a]`
(<https://hackage-content.haskell.org/package/base/docs/Data-List.html>).
Fix: keep internal namespaces out of the message; add `List.joinWith` for
texts, or suggest `Text.joinWith`.

### 5. Missing std

- List lemmas written again: `lengthReverse`, `reverseCons`, `reverseSnoc`
  (`(xs ++ [x]).reverse = Cons x xs.reverse`), `reverseOntoAppend` (day 7
  has it too), `lengthSnoc`, and the permutation of a `flatMap` over the
  reversed list (`permFlatMapReverse`). Lean's core has
  `List.length_reverse`, `List.reverse_append` and `List.reverse_flatMap`
  (<https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Lemmas.html>).
- `sumFilterMap`: the sum of a `filterMap` is a `sumBy` with 0 for `None`.
- `filterMap` over `List.replicate n (Some x)` and `List.replicate n None`.
- `List.joinWith` for texts (item 4).

None added. Fix: the reverse lemmas (now needed on two days) and
`sumFilterMap` in `List/Toolkit.sw`.

### 6. Proofs: `rewrite` misses a term the goal has unfolded, again

`rewrite compactFile id rest in …` on the goal
`hasGap (compactBlocks (Cons (Some id) rest)) = False`:

```text
[E-REWRITE-NOTHING] Error: `rewrite` found no `compactBlocks (Cons (Some id) rest)` in the goal
  Note 2: the search compares what terms compute to: it looked for `Cons (Some id) (fillFront rest (List.reverseOnto (List.filterMap rest (block => block)) [id]) (List.length (List.filterMap rest (block => block))))`, what `compactBlocks (Cons (Some id) rest)` computes to, in what the goal computes to
```

`hasGap` had already taken its step on the leading `Cons (Some id)`, so the
computed goal had no `Cons` left to find. Wrote
`Eq.trans (Eq.cong hasGap (compactFile id rest)) …`. Day 2's item 3 and day
3's item 8 again. Fix: look in the goal as written before what it computes
to.

### 7. Proofs: `decreasing` needs proofs even of structural steps

`stepsFill` and `fillNoGaps` recurse on a list of the same length (the rest
with its last file block freed), so they say `decreasing blocks.length`.
Then every recursive call needs `[decreasing := omega]`, the plain one on
`rest` too:

```text
[E-DECREASING] Error: can't show `List.length rest < Succ (List.length rest)` here, which `decreasing Succ (List.length rest)` needs for this call
```

and the measure must use a parameter named in the header (``E-DECREASING:
`fillNoGapsByLength`'s measure needs the parameters it uses named in its
header``), so the theorem `match`es instead of using arms. The first version
passed a `size` bound instead, as day 6 passes a budget; `decreasing` with
`[decreasing := omega]` is shorter. Lean's default termination tactic,
`decreasing_trivial`, tries `simp_arith` and `omega` itself
(<https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>).
Fix: try `omega`, with the facts in scope, on measure goals.

### 8. What went well

Every part 1 lemma but one checked on its first try, and every part 2 one.
`match later: lastFile rest with` rewrites the hypotheses as well as the
goal, so contradictions were just `Void.exfalso (Option.someNotNone id
none)`, and `Void.exfalso (omega)` closed the impossible length cases.
Std's `mapAccumLeftList` and `mapZipWithScanLeft` made "each file moved
once" one line. Rewriting the spec's first `takeLastFileBlock` (returning an
`Option` of a pair) as `lastFile` and `freeLastFileBlock` before the proofs
avoided reasoning about a pair inside an `Option`.

### Performance

`stitchwort run` on the input takes 0.85 s, against 0.53 s on the example
(loading and checking): about 0.16 s for part 1 and 0.15 s for part 2.
Plain recursion over the 94,500-block lists (`fillFront`, `blocksFrom`) had
no stack trouble. The machine (`machine aoc_agrees`, which passed, with all
423 AoC tests agreeing) runs `main` on the input in 1.0 s, more than `run`'s
0.3 s of work after loading, where day 7's was faster on the machine
(0.14 s); I didn't look into why. The fast Python takes 0.04 s user, the
literal Python (a block at a time over a list) 24 s.

The spec is far slower, since each move walks the disk and part 1 makes
23,434 moves. Both parts against the spec on the first 99 digits (454
blocks) add 0.35 s to the tests; on the first 999 digits (4,739 blocks) it
ran over 2 minutes before I stopped it. So the spec is compared on small
disks only.

### Size and time

Release build, on a machine with a load average around 30:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day09.Proofs` | 1.6 s |
| `stitchwort check --no-cache Aoc.Year2024.Day09` | 1.5 s |
| `stitchwort test --no-cache Aoc.Year2024.Day09` (32 tests) | 1.9 s |
| `stitchwort test Aoc.Year2024.Day09` (warm) | 0.5 s |
| `stitchwort run Aoc.Year2024.Day09.main` on the input | 0.85 s |
| `stitchwort check --no-cache` (whole project) | 13.5 s |
| `main` on the input, on the machine (`machine aoc_agrees`) | 1.0 s |

131 lines of program, 86 of spec, 356 of proofs, 92 of tests.

### Ranked

1. Part 2's equivalence with the spec is out of reach without
   specifications for a map of sets threaded through a fold ("Not proved").
   Fix: std lemmas tying `Map.alter`/`Map.adjust`, `Set.insert`/`Set.remove`
   and `Set.min` to a list model, so an invariant can be stated on lists.
2. `rewrite` misses terms the goal has already unfolded (item 6). Fix: look
   in the goal as written first.
3. Lambdas and record literals checked before the argument that fixes their
   type (item 3). Fix: check them last in a call.
4. `decreasing` needs a hand proof even for structural calls (item 7). Fix:
   try `omega` on measure goals.
5. Ability operations in scope unimported, and a warning that doesn't say
   which `span` (item 2). Fix: qualify the name; import operations by name.
6. Missing list lemmas, two for the second time (item 5). Fix: add the
   reverse lemmas and `sumFilterMap` to std.
7. `Effect.CompD` in an unknown-field error, and no `joinWith` on a list of
   texts (item 4). Fix: hide internal namespaces; add `List.joinWith`.
8. `Parse.line` counts columns past the line break (item 1). Fix: report
   line 2.

## Day 10: Hoof It

A 40 by 40 topographic map of heights 0 to 9. "A hiking trail is any path
that starts at height 0, ends at height 9, and always increases by a height
of exactly 1 at each step", with no diagonal steps. A trailhead is "any
position that starts one or more hiking trails". Part 1 sums each
trailhead's score, "the number of 9-height positions reachable from that
trailhead via a hiking trail"; part 2 sums each trailhead's rating, "the
number of distinct hiking trails which begin at that trailhead" (part 2's
wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-10/README.txt>).
The small examples have impassable `.` tiles; the real map has none.
Answers on Matt's input: 461 and 875 (cross-checked with an independent
Python script, `/usr/bin/python3 -I`, that lists every trail by depth-first
search and counts distinct (start, end) pairs and distinct trails; it also
gives 36 and 81 on the larger example, and 13 and 227 on the rating
examples). The map has 175 trailheads. Compiler built from `main` at
b3ceb57e, 28 October 2026.

### The program

```stitchwort
def tile(): {Parse} (Option Nat) :=
  Parse.oneOf [
    () => Some digit().toNat,
    () =>
      char '.'
      None
  ]

def parseMap (input: Text): {Fail} TopographicMap :=
  let rows := Parse.all input (() => Parse.grid tile)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .map (((row, tiles)) =>
    Fail.ensure (tiles.length == width) "line ${row + 1}: expected ${width} tiles, as on the first line, got ${tiles.length}")
  { rows }

def TopographicMap.uphill (map: TopographicMap) (position: Position): List Position :=
  position.neighbours |> .filter (map.isOneHigher position)

def TopographicMap.trailEnds (map: TopographicMap): (steps: Nat) → (position: Position) → List Position
  | Zero, position => if map.heightAt position == Some 9 then [position] else Nil
  | Succ steps, position => map.uphill position |> .flatMap (map.trailEnds steps)

def TopographicMap.score (map: TopographicMap) (trailhead: Position): Nat := map.trailEnds 9 trailhead |> .distinct |> .length

def TopographicMap.rating (map: TopographicMap) (trailhead: Position): Nat := map.trailEnds 9 trailhead |> .length

def solvePart1 (map: TopographicMap): Nat := map.trailheads |> .sumBy map.score

def solvePart2 (map: TopographicMap): Nat := map.trailheads |> .sumBy map.rating
```

The domain model is the rows of heights, `Option Nat` per tile (`None` for
`.`); `heightAt` is `None` off the map too. `trailEnds` is a plain search:
from a trailhead it takes nine steps, each to a neighbour one higher, and
gives the end of every trail, once per trail. A score is the number of
distinct ends, a rating the number of ends. Since every trail has exactly
ten positions, the step count is the recursion's measure and termination is
structural. No memoisation was needed: the search only follows trails, and
the whole input has 875 of them.

`neighbours` is up, left, right and down, with none above row 0 or left of
column 0 (`Position` is `Nat`s). It is split into `above`, `leftOf` and
`rightAndBelow` so the proofs can name the parts (item 4).

### Proved, for every map

The spec (`Spec/Spec.sw`) is the puzzle's words over the program's
`heightAt` and `positions`. `isOrthogonalStep` is one column apart in the
same row or one row apart in the same column; `increasesByOne` is the next
height being the last plus 1; `isHikingTrail path` is "starts at height 0"
(`path.head`), "ends at height 9" (`path.last`) and every step of
`path.zipWithNext` both. To count trails the spec needs a finite set of
candidates: `pathsOf map n` is every list of `n` positions on the map, and
`trailsFrom start` is `start` followed by each of `pathsOf map 9`, kept if
`isHikingTrail`. `trailheads` keeps the positions with at least one trail,
`score` counts the positions at height 9 that some trail from the
trailhead ends at, and `rating` is `trailsFrom`'s length.

Proved (`Proofs/Proofs.sw`, 257 lines, and `Proofs/Steps.sw`, 169 lines):

- `part1Correct`: `solvePart1 map = part1 map`.
- `part2Correct`: `solvePart2 map = part2 map`.
- `trailsAreCandidates`: every hiking trail starts at a position on the map
  and is in `trailsFrom` of its start, so the spec's ten positions miss
  none; `emptyIsNoTrail` covers the empty path.
- `pathsDistinct`: `pathsOf` lists each path once, so the spec counts
  distinct trails.

The steps:

- `memUphill`: a position is in `uphill from` exactly when it is on the map
  and `isStep from` it (`neighbourOrthogonal` and `orthogonalNeighbour`, by
  cases on the edges); `uphillPerm`: `uphill` is the spec's steps among
  `positions`, in another order (std's `permOfSameMembers`, with
  `neighboursDistinct` and `positionsDistinct`).
- `positionsComplete`: every position with a height is in `positions`.
- `trailCons`: `isHikingTrail (Cons start rest)` is a height-0 start and
  `climbs start rest`, a recursive form of the rest of the check
  (`endsAndSteps`).
- `countTrailEnds`: the number of `pathsOf map steps` that climb from a
  position is the number of ends the search finds; induction on `steps`,
  through `countSumBy`, `sumByFlatMap`, `sumByFilter`, the permutation
  (`sumByPerm`) and a `lengthFlatMap`.
- `memTrailEnds`: a position is a search end exactly when some climb ends
  there.
- `scoreCorrect` and `ratingCorrect` per trailhead, then
  `sumOverTrailheads`: the program sums over the 0s, the spec over the
  positions with a trail; a 0 with no trail adds 0 to both.

Breaking the program (ends at height 8, or `.take 3` of `uphill`) makes
the proofs fail. Nothing is unproved. The spec itself can't run on any map
with a trail (item 5), so the tests check `isHikingTrail` on the puzzle's
drawn trails instead.

### 1. Std.Parse: none

`Parse.grid tile` with `Parse.oneOf` read the map first time, and the
messages read well: `line 2, column 3: expected a digit or '.' or the end
of the line, got 'x'`, and on empty input `line 1, column 1: expected a
digit or '.', got the end of the input`. The row-length check is outside
the grammar, as on day 8, so its message has no column.

### 2. Missing std

- `List.forEach` (or any way to run a `{Fail}` check on each element):
  `parseMap` checks each row with `rows.withIndex |> .map (… =>
  Fail.ensure …)` and drops the `List ()`, with no warning. Scala has
  `List.foreach`
  (<https://www.scala-lang.org/api/current/scala/collection/immutable/List.html>),
  Haskell `mapM_`
  (<https://hackage.haskell.org/package/base/docs/Data-Foldable.html#v:mapM_>).
- Lemmas written here: `lengthFlatMap` (length of a `flatMap` is the
  `sumBy` of the lengths), `lengthFilter` (length of a `filter` is the
  `count`), `countNone` and `countFalse` (a count where nothing passes is
  0), `anyEmpty`. Lean's core has `List.length_flatMap`
  (<https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Lemmas.lean>),
  `List.countP_eq_length_filter` and `List.countP_eq_zero`
  (<https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Count.lean>).

None added (the `List/Toolkit.sw` split is in progress in another lane).
Fix: add the five lemmas and `List.forEach` to std.

Fixed: std has `List.forEach` (`f` on each element for what it performs,
returning `()`), which `parseMap` now uses, and `List.lengthFlatMap`,
`List.lengthFilter`, `List.countFalse`, `List.countNone` and
`List.anyEmpty` (List/Lemmas.sw); the local copies are gone.

### 3. Proofs: `omega` reads neither `||`, `==` nor a literal record's field

`isOrthogonalStep` is `&&`, `||` and `==` on `Nat`s. Once the positions
were concrete, `omega` couldn't prove it:

```text
[E-OMEGA] Error: `omega` can't prove `((Decidable.toBool (Nat.decEq (Succ (previous + 1)) previous) || Decidable.toBool (Nat.decEq (previous + 1) (Succ previous))) || Decidable.toBool (Nat.decEq (Succ previous) previous) && False) = True`
  unsupported structure: this goal isn't linear arithmetic on `Nat`
```

And with `Not (first.row = second.row)`, the positions literal records,
it treats the projections as unknowns:

```text
[E-OMEGA] Error: `omega` can't prove `Void`
  an integer model of the arithmetic abstraction satisfies the facts
  Note 1: facts: `{ row = 1, column = 0 }.row = { row = 0, column = 1 }.row` (h)
```

So `Orthogonal`, a `Prop` copy of the spec's step, with `orthogonalIntro`
and `orthogonalElim` to convert (about 30 lines of `Bool.orElim`,
`Bool.andLeft` and `DecEq.sound`), and `rowsApart`/`columnsApart` take the
four `Nat`s rather than two positions. Lean's `omega` splits disjunctions
in the context (its `splitDisjunctions` option, on by default;
<https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean>).
Fix: let `omega` read `||` and `Nat` `==` in `Bool` goals and facts, and
reduce projections of record literals before abstracting atoms.

Fixed: `omega` splits disjunctions among the facts (`Or`, `||`, a `False`
`&&`), proves disjunctive goals by cases, reads `||` and `not`, and computes
a field of a record that became known after the goal (docs/proposals/omega.md,
"As built: disjunctions, `Bool` logic and record fields").
`neighbourOrthogonal` now proves `isOrthogonalStep` itself (`rewrite <- same
in omega` per arm); `eqTrue`, `orthogonalIntro` and `orthogonalElim` are gone,
`orthogonalNeighbour`'s `Orthogonal` comes from `omega`, and `rowsApart` and
`columnsApart` take two positions. `Orthogonal` stays only as the four
directions `orthogonalNeighbour` matches on. `Proofs/Steps.sw` went from 169
lines to 140 (proofs 426 to 397).

### 4. Proofs: membership in a list the checker hasn't unfolded

`orthogonalNeighbour` shows a position is in `from.neighbours`, which was
`above ++ left ++ [right, below]` written with local `let … := match …`.
`List.memAppendRight _ _ _ (List.memAppendRight _ _ _ (Inl rfl))` got

```text
[E-TYPE-MISMATCH] Error: type mismatch
  `rfl` proves an equation, but the expected type is `?10 row column toRow toColumn rows right`
```

The holes for the lists weren't filled from the goal, so `∈` didn't
unfold to `Or`. Naming the parts as definitions (`above`, `leftOf`,
`rightAndBelow`) and passing them explicitly worked. Then a `match` on
`toColumn + 1` (after `rewrite`) didn't reduce, since `+ 1` isn't `Succ`
to the matcher; the arm was split on `Zero` and `Succ previous` instead,
with `omega` for `previous = toColumn`. Fix: solve list holes from the
goal by unfolding it; reduce `n + 1` to `Succ n` when matching.

### 5. The spec can't run

`pathsOf map 9` is every list of nine positions: for the 8 by 8 example,
64^9. So `part1` and `part2` were never run, unlike day 9's spec, and an
error in them would only show in a proof. The tests check `isHikingTrail`
on the three trails drawn in the puzzle and on near misses, and
`pathsOf map 2` on a two-tile map. Laziness wouldn't help, since the spec
filters every candidate. What I did instead: the proof of
`trailsAreCandidates` and `pathsDistinct`, which show the candidates are
neither too few nor repeated. Fix: none needed in the language; noting
that a literal spec of "count distinct paths" is a proof-only object.

### 6. Inference and elaboration

- `if (trailsFrom map start).length >= 1 then … else Add.zero` in a lambda
  elaborated as a decidable `Prop` (`Decidable.elim (Nat.decLessThan 0 …)`),
  while the same `>= 1` in the spec's `.filter` is a `Bool`, so
  `List.sumByFilter`'s statement didn't match my `sumByCong` lambda; the
  message elided both sides with `…`. Named it `startsTrail`, a `Bool`
  `def`.
- `List.sumByZero xs : List.sumBy xs (x => Add.zero) = Add.zero` doesn't
  check as `List.sumBy xs (x => 0) = 0`:

  ```text
  [E-TYPE-MISMATCH] Error: type mismatch
    expected `List.sumBy xs (x => 0) = 0`, but this has type `List.sumBy xs (x => Add.zero) = Add.zero`
  ```

  though `(Add.zero: Nat) = 0` is `rfl` (both checked in a probe). Perhaps
  the instance is still unknown when the types are compared (speculative).
  Used `List.sumByZeroIntro`.
- `Ok { rows = … }` in a test is an `E-UNKNOWN-FIELD` (`` `Ok` has no
  field `rows` ``), day 1's item 7 again; the message now says to write
  `Ok ({ … })`, which worked.
- A multi-line `rewrite a, b, c` with `in` alone on the next line is
  `[E-PARSE] Error: expected an expression, but found `in``; `in` must end
  the last rule's line.

Fix: elaborate `if` on a `Bool`-valued comparison as `Bool`; unfold
instance fields when comparing; allow `in` on its own line.

Fixed: an `if` on a decided proposition whose branches don't use its proof
is the `Bool` `if` on the decision's `Bool`, the same term `.filter` gets,
so `List.sumByFilter`'s statement matches `if (trailsFrom map start).length
>= 1 then … else Add.zero`. Where a branch uses the proof (an `auto`
argument such as `Fin.ofNat i` under `if i < n`) it stays a decided `if`.

Fixed: `List.sumByZero xs` checks as `List.sumBy xs (x => 0) = 0`. The
cause wasn't the instance field: the lemma's `Add c` dictionary is fixed
only by the expected type, and two calls of one definition are compared by
their arguments only when that solves nothing, so the comparison went into
the unfoldings (`Add.zero ?add` against `0`), failed, and was undone, `c`
with it, leaving the dictionary unready. A failed comparison now keeps what
it learnt, finds the dictionaries that made ready, and compares again,
undoing all of it if that fails too.

Fixed: `in` may start a line of its own after a `rewrite`'s rules, at the
`rewrite`'s column or right of it.

### 7. What went well

The proofs took about an hour and a half and were mostly right first
time: `positionsComplete`, `memUphill`, `uphillPerm`, `scoreCorrect` and
`climbsPaths` checked on their first run. Std had what the counting
needed: `permOfSameMembers` (two lists without repeats and the same
members are a permutation), `sumByPerm`, `distinctFlatMap`,
`sumByFilter`, `memDistinct` and `distinctNoRepeats`. `match step: isStep
map from next with` substitutes into the goal, so the arms needed no
`rewrite` (one I added anyway was an `E-REWRITE-NOTHING` whose note said
the goal already held by computing). `rewrite … at hypothesis` was the easy
way to move between `trail` and `Cons start rest`.

### Performance

`stitchwort run` on the input takes 0.77 s, against 0.62 s on the example
(loading and checking), so about 0.15 s of work. The Python script takes
0.04 s. The machine (`machine aoc_agrees`, which passed, with all 476 AoC
tests agreeing) runs `main` on the input in 0.57 s, more than `run`'s
0.15 s of work after loading, as on day 9; I didn't look into why.

### Size and time

Release build, on a machine with a load average around 22:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day10.Proofs` | 2.8 s |
| `stitchwort check --no-cache Aoc.Year2024.Day10` | 1.7 s |
| `stitchwort test --no-cache Aoc.Year2024.Day10` (34 tests) | 2.6 s |
| `stitchwort test Aoc.Year2024.Day10` (warm) | 2.2 s |
| `stitchwort run Aoc.Year2024.Day10.main` on the input | 1.4 s (0.77 s user) |
| `stitchwort check --no-cache` (whole project) | 20 s |
| `main` on the input, on the machine (`machine aoc_agrees`) | 0.57 s |

99 lines of program, 60 of spec, 426 of proofs, 173 of tests.

### Ranked

1. `omega` can't read `||`, `Nat` `==`, or a literal record's fields
   (item 3). Fix: support them, as Lean's `omega` splits disjunctions.
2. Membership proofs in lists the checker won't unfold, and matches stuck
   on `n + 1` (item 4). Fix: fill list holes by unfolding the goal; reduce
   `n + 1` to `Succ n`.
3. `if` on a comparison is a `Prop`, `filter`'s is a `Bool`; `Add.zero`
   and `0` don't match inside a lemma's type (item 6). Fix: elaborate
   comparisons in `if` as `Bool`; unfold instances when comparing.
4. Missing `length`/`count` lemmas and `List.forEach` (item 2). Fix: add
   them to std.
5. The literal spec can't run (item 5). Fix: none; the candidate theorems
   stand in for running it.
6. `in` can't start a line after a multi-line `rewrite` (item 6). Fix:
   allow it.

## Day 11: Plutonian Pebbles

A line of numbered stones. "Every time you blink, the stones each
simultaneously change according to the first applicable rule": 0 becomes 1;
"a number that has an even number of digits ... is replaced by two stones.
The left half of the digits are engraved on the new left stone, and the
right half of the digits are engraved on the new right stone. (The new
numbers don't keep extra leading zeroes: 1000 would become stones 10 and
0.)"; otherwise the number is multiplied by 2024. "No matter how the stones
change, their order is preserved". Part 1: "How many stones will you have
after blinking 25 times?"; part 2: "How many stones would you have after
blinking a total of 75 times?" (part 2's wording from the public copy at
<https://github.com/RobUrsem/AdventOfCode2024/blob/1d92fdb7a5c926295cff6a8bfee6e262cfd56bf6/11/day11.txt>).

**The real input is pending from Matt.** `mdr/aoc-2024` stops at day 10
(its last commit, 17 December 2024, is "day 10"; there is no
`Aoc2024/Day11`), so there is no day 11 input of his yet. Until it comes,
day 11 has no `aoc/inputs/2024/day11.txt`, no real-input tests and no entry
in `crates/cli/tests/aoc_answers.rs` or `crates/rt/tests/machine.rs`; when
it does, add the file, a `Tests/Input.sw` as other days have, and those two
entries.

The example's answers are checked: its six lines, 55312 after 25 blinks,
and 65601038650482 after 75, all agreeing with an independent Python script
(`/usr/bin/python3 -I`) that splits the decimal string and counts with a
`Counter`. The timings below are on a generated line of 8 stones
(`4186027 69222 0 8 977 8629 632510 81`, not committed), on which the
program and the Python script agree (199514 and 236970341363826); after 75
blinks its 237 trillion stones show only 3764 different numbers. Compiler
built from `main` at 64fbe366, 28 October 2026.

### The program

```stitchwort
def parseStones (input: Text): {Fail} (List Nat) := Parse.all input (() => sepBy1 nat spaces1)

def changeStone (stone: Nat): List Nat :=
  if stone == 0 then [1]
  else
    let digitCount := stone.digitCount
    if digitCount % 2 == 0 then
      let place := Nat.pow 10 (digitCount / 2)
      [stone / place, stone % place]
    else [stone * 2024]

def addStones (counts: Map Nat Nat) (stones: List Nat) (count: Nat): Map Nat Nat :=
  stones.foldLeft counts (counts stone => counts.insertWith stone count Nat.add)

def blinkCounts (counts: Map Nat Nat): Map Nat Nat :=
  counts.foldLeft Map.empty (blinked stone count => addStones blinked (changeStone stone) count)

def countAfter (blinks: Nat) (stones: List Nat): Nat :=
  blinks.iterate blinkCounts (Map.counts stones) |> .values |> .sum

def solvePart1 (stones: List Nat): Nat := countAfter 25 stones

def solvePart2 (stones: List Nat): Nat := countAfter 75 stones
```

The domain model is the list of numbers. The line grows by about half
again per blink, so part 2's literal list would have over 10^14 elements;
the program never builds it. It keeps how many stones show each number
(`Map Nat Nat`, starting from std's `Map.counts`), and a blink changes each
number once and adds its count to whatever it becomes. Splitting divides by
10 to the half of `Nat.digitCount` (std); the spec instead takes the halves
of the digit list, and the proofs show the two agree.

### Proved, for every line of stones

The spec (`Spec/Spec.sw`) is the puzzle's words: `change` takes
`Nat.digits stone`, and for an even count makes two stones from
`Nat.fromDigits` of its `take` and `drop` at half (which is what drops the
right half's leading zeros); `blink` is `flatMap change`, keeping the
order; `blinkTimes n` is `n` blinks; `part1` and `part2` are
`(blinkTimes 25 stones).length` and `(blinkTimes 75 stones).length`. The
spec runs: the tests check it against the example's six lines and 55312.

Proved (`Proofs/`, 224 lines in four files):

- `part1Correct`, `part2Correct`: `solvePart1 stones = part1 stones`, and
  the same for part 2, both from
- `countCorrect`: `countAfter blinks stones = (blinkTimes blinks
  stones).length`, for every number of blinks (Counting.sw). The invariant
  is `Represents counts stones`: for every weight `w: Nat → Nat`, the
  map's entries weigh (count times `w` of the number) what the list's
  `sumBy w` does. `weighInsertWith` follows `Map.Spec.insertWith` (std
  states `Map.insertWith` on the sorted entry list), `weighAddStones` and
  `weighFold` follow the folds, and `representsBlink` instantiates the
  invariant at `w' x = (change x).sumBy w`, which is what makes one blink
  of the counts stand for one blink of the line, through std's
  `sumByFlatMap`. At the end, the weight 1 gives the sum of the counts on
  one side and the length on the other.
- `orderIrrelevant`, `countOrderIrrelevant`: lines that are permutations
  of each other (`List.Perm`) are still permutations after any number of
  blinks (`blinkTimesPerm`), so they end with as many stones, by the spec
  and by the program (Order.sw; std's `sumByPerm` does the work).
- `changeAgrees`: `changeStone stone = change stone`, the lists equal, for
  every stone (Split.sw). It rests on `recombine`: `fromDigits (left half) *
  10^(length of right half) + fromDigits (right half) = stone`, for any
  split point, from std's `fromDigitsAppend` and `fromDigitsDigits`. With
  an even digit count the right half has half the digits
  (`rightHalfLength`, `omega` with `/ 2` and `% 2`) and is below 10 to
  that (`rightHalfSmall`), so std's `divUnique` and `modUnique` give
  `splitLeft` (`stone / place` is the left half) and `splitRight`
  (`stone % place` is the right half).
- `leftStoneDigits`: for a stone of at least 1 with an even digit count,
  `Nat.digits (stone / place)` is exactly the left half of the digits: the
  left stone loses no digits, since its first one isn't 0.

Breaking the program (`* 2023`, the halves swapped, or `count + 1` in
`blinkCounts`) makes the proofs fail. `countCorrect` and
`countOrderIrrelevant` use `Quot.sound` (through `Map`); `changeAgrees`
uses no axioms.

Not proved: the right stone's digits are the right half's with leading
zeros dropped (`Nat.digits (stone % place)` against a `dropWhile`). The
spec already says it with `fromDigits`, which is what the puzzle's
"1000 would become stones 10 and 0" means, so I stopped at the numbers.

### 1. Std.Parse: none

`Parse.all input (() => sepBy1 nat spaces1)` read the line first time, and
the messages were the ones I guessed in the tests before running them:
`line 1, column 1: expected a number, got the end of the input` and
`line 1, column 4: expected a number, got 'x'`. Two spaces between numbers
are allowed (`spaces1`).

### 2. Missing std

- No `List.appendTakeDrop` (`take xs n ++ drop xs n = xs`) for lists; only
  `Text.takeDropChars` for characters. Added to `List/Lemmas.sw`.
- `Nat.digitsTake` but no `Nat.digitsDrop` (a suffix of digits is
  digits). Added next to it in `Nat/Digits.sw`.
- No `occurrencesFlatMap` (`(xs.flatMap f).occurrences p = xs.sumBy (x =>
  (f x).occurrences p)`) or `List.permFlatMap`, and no `sumBy (x => 1) =
  length`; day 10 wrote a `lengthFlatMap` of its own too. Written in the
  proofs, not std, since `sumByPerm` lives in `List/Sort.sw`, which another
  lane is splitting.

  Fixed: std has `List.occurrencesFlatMap` and `List.sumByOne` (`sumBy (x
  => 1) = length`) in `List/Lemmas.sw`, and `List.permFlatMap` (for a
  `DecEq` element type, as `sumByPerm` needs) in `List/SortLemmas.sw`;
  `blinkPerm` is `List.permFlatMap`, and the local copies are gone.
- Nothing about a `Map`'s values summed after `insertWith`. `weigh` and
  `weighInsertWith` (13 lines over `Map.Spec.insertWith`) did it; std's
  `Map.toListInsertWith` and `Map.foldLeftToList` made it a list proof.

### 3. Confusing errors

- A `def` whose body is a function type counts as more arguments when it
  is a theorem's result. `representsAfter: ... → Represents counts stones
  → Represents (...) (...)`, where `Represents` is `(weight: Nat → Nat) →
  ...`, and `blinkTimesPerm` ending in `List.Perm ...`, both gave:

  ```text
  [E-ARITY] Error: this arm has 4 pattern(s), but `representsAfter` takes more arguments after the colon
  ```

  Nothing says the extra argument comes from unfolding `Represents`. I
  added a fifth pattern (`weight`, or `p` for `Perm`) to every arm and
  applied the hypothesis to it.

  Fixed: the error has a note naming the definition and the arguments it
  adds, as in "the result `List.Perm xs xs` unfolds to a function type,
  since `List.Perm` is defined as one, and so it adds 1 argument(s) to
  match: `p: Nat → Bool`".
- `DecEq.sound _ _ even` on a `Nat` `==`:

  ```text
  [E-TYPE-MISMATCH] Error: type mismatch
    expected `Decidable.toBool (DecEq.%decide (?4 stone zero even) (Nat.digitCount stone % 2) 0) = True`, but this has type `Decidable.toBool (Nat.decEq (Nat.digitCount stone % 2) 0) = True`
  ```

  The note blamed the `match` ("a term written out inside a branch ...
  isn't refined by the `match`") and suggested `_` for the arguments,
  which I had written. The real cause is the unsolved instance `?4`:
  writing the arguments, `DecEq.sound (stone.digitCount % 2) 0 even`,
  worked.

  Fixed: `DecEq.sound _ _ even` is accepted. Day 10's fix (a dictionary
  that only the comparison with the expected type fixes is found, and the
  types compared again) finds the `DecEq Nat` instance here too; with that
  step turned off, the same error and note come back.
- `W-LAMBDA-SHADOW`: a lambda parameter called `next` "hides the function
  `next`", which is the `Parse` ability's operation, in scope from
  `import Std (Parse)` though the file imports only `nat`, `sepBy1` and
  `spaces1` from `Std.Parse` (day 9's item 2 again). Renamed it `blinked`.

### 4. Inference

Nothing went wrong. `Map.empty` as `foldLeft`'s start and the
three-parameter lambda (`blinked stone count => ...`) needed no
annotations, and `blinks.iterate blinkCounts (Map.counts stones) |>
.values |> .sum` inferred `Map Nat Nat` throughout.

### 5. Performance

All on the generated line of 8 stones (user time). Interpreted, `run`
takes 1.52 s, against 0.54 s on the example (loading and checking), and
0.54 s for parsing alone; part 1 alone is 0.58 s. So part 1 is about
0.04 s of work and part 2 about 0.95 s. The Python script does both, and a
second count, in 0.09 s. A version with the digits counted by repeated
multiplication instead of `Nat.digitCount`'s digit list ran part 2 alone in
1.43 s against about 1.5 s, so the time is the map: 75 blinks of up to
about 3800 numbers is some 500,000 `insertWith`s, nearly 2 µs each,
through a balanced tree that compares through the `Ord` instance. `--js`
takes 0.86 s, Node's start included. On the machine, a `stitchwort build`
executable (no loading) takes 1.13 to 1.18 s, against 0.02 s on the
example: slower than the interpreter's 0.95 s of work, which I didn't look
into. `machine aoc_agrees` passed (496 AoC tests agree), but day 11 has no
entry in its answer list, so it ran neither day 11's `main` nor its
timing.

What I did instead: nothing; 1.5 s is fine. A hash map, or an `IntMap`
(Haskell's `Data.IntMap`) keyed by `Nat`, would be the fix if a day needs
it.

### 6. Proofs

The proofs took about an hour, and most checked first time:
`weighInsertWith`, the folds, `countCorrect`, `blinkPerm` and
`digitsOfLeading` all did. The difficulty was choosing the invariant, not
proving it. The obvious one, "the map's count at each number is the list's
count of that number", says nothing about the sum of the values without
facts about distinct keys, and turning per-number counts into a sum of
`(change x).sumBy w` over the line needs the counts for every function,
not every predicate. Quantifying over weights (`Represents`) makes the
blink step one instantiation. The friction was elsewhere:

- `rewrite <- rightHalfLength stone even` (`length (drop half) = half`)
  rewrote `half` inside the `drop half` too:

  ```text
  [E-TYPE-MISMATCH] Error: type mismatch
    expected `List.foldLeft (List.drop (Nat.digitsAcc stone []) (List.length (List.drop (Nat.digits stone) (… / 2)))) 0 (acc digit => acc * 10 + digit) < …`
  ```

  `Nat.ltCongRight` and `Eq.cong` at the one place worked. Lean's answer
  to a `rw` that hits the wrong place is conversion mode, "a more precise
  tool", which focuses on one part of the goal first
  (<https://lean-lang.org/theorem_proving_in_lean4/conv.html>).
- In `changeAgrees`, `rewrite splitLeft ..., splitRight ...` failed on the
  second rule:

  ```text
  [E-REWRITE-NOTHING] Error: `rewrite` found no `stone % Nat.pow 10 (Nat.digitCount stone / 2)` in the goal
    Note 1: goal after the rule before this one: `[Nat.fromDigits (List.take … …), stone - (… * …)] = …`
  ```

  `%` computes to `stone - (stone / place) * place`, and the first rule
  rewrote the `/` inside it. Rewriting `%` first worked. The notes say
  what happened (the goal after the first rule shows the `-`), so this was
  quick to fix.
- `omega` handled `/ 2` and `% 2` by literals (`rightHalfLength`, `1 ≤
  half`) and a power as an atom (`powTenNotZero`), as Lean's `omega` does.

### 7. Comparisons

- Haskell's `Data.Map.Strict.insertWith` ("Insert with a function,
  combining new value and old value") and `fromListWith` are the same
  operations as `Map.insertWith` and `Map.counts`
  (<https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Map-Strict.html>);
  the program reads the same in Haskell.
- Scala's `groupMapReduce(key)(f)(reduce)` counts in one call,
  `stones.groupMapReduce(identity)(_ => 1L)(_ + _)`
  (<https://www.scala-lang.org/api/3.1.0/scala/collection/IterableOps.html>);
  Stitchwort's `Map.counts` covers the start, but a blink is a fold.
- Lean defines `List.Perm` inductively (`Init/Data/List/Basic`) and proves
  `List.perm_iff_count`: `l₁.Perm l₂ ↔ ∀ a, count a l₁ = count a l₂`
  (<https://lean-lang.org/doc/api/Init/Data/List/Perm.html>). Stitchwort's
  `List.Perm` is defined by counting (`occurrences` of every predicate), so
  `blinkPerm` was two rewrites and `sumByPerm`.
- Mathlib's `Nat.digits` is little-endian ("the digits, in little-endian
  order"), with `Nat.ofDigits_digits` as the round trip
  (<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Digits/Defs.html>).
  Std's are most significant first, so "the left half" is `take`, which
  suited this puzzle.

### Size and time

Release build, on a machine with a load average around 25:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day11.Proofs` | 2.0 s |
| `stitchwort check --no-cache Aoc.Year2024.Day11` | 1.7 s |
| `stitchwort test --no-cache Aoc.Year2024.Day11` (20 tests) | 1.9 s |
| `stitchwort run Aoc.Year2024.Day11.main` on the generated line | 1.52 s |
| `stitchwort check --no-cache` (whole project) | 15 s |
| `main` on the generated line, on the machine (`stitchwort build`) | 1.13 s |

49 lines of program, 40 of spec, 224 of proofs, 49 of tests.

### Ranked

1. The real input is pending: Matt's repository has no day 11. Fix: add
   his input, its tests and its two answer entries when he has it.
2. A `def` that unfolds to a function type adds arguments to a theorem's
   arms, and `E-ARITY` doesn't say so (item 3). Fix: name the definition
   that unfolded and the extra argument in the message.
3. `rewrite` changes every occurrence, including inside the term being
   protected, and inside what `%` computes to (item 6). Fix: an occurrence
   selector (`rewrite ... at 1`) or a `conv`-like focus.
4. `DecEq.sound _ _ h` fails on an unsolved instance with a note about the
   `match` (item 3). Fix: solve the instance from `h`'s type, or say the
   instance is unknown.
5. Part 2 spends about 1.6 µs per `Map.insertWith` (item 5). Fix: a
   `Nat`-keyed map (as Haskell's `IntMap`), or cheaper `Ord` dispatch.
6. Missing `occurrencesFlatMap`, `permFlatMap`, `sumBy (x => 1) = length`
   (item 2). Fix: add them to std's `List/Lemmas.sw` once `List/Sort.sw`
   is split.
7. The `Parse` ability's `next` shadows a lambda parameter without an
   import (item 3). Fix: as day 9's item 2, scope ability operations by
   import.

## Day 12: Garden Groups

A map of garden plots, one letter (plant) each. "When multiple garden plots
are growing the same type of plant and are touching (horizontally or
vertically), they form a region." "The area of a region is simply the number
of garden plots the region contains", and "the perimeter of a region is the
number of sides of garden plots in the region that do not touch another
garden plot in the same region". Part 1 sums area times perimeter over the
regions. Part 2 uses "the number of sides each region has. Each straight
section of fence counts as a side, regardless of how long it is" (part 2's
wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-12/README.txt>).

**The real input is pending from Matt**: his repository
(<https://github.com/mdr/aoc-2024>) stops at day 10, so there is no
`inputs/2024/day12.txt`, no `Tests/Input.sw`, and the day isn't registered in
`aoc_answers.rs` or `machine.rs` yet. The tests are the puzzle's examples:
140, 772 and 1930 for part 1; 80, 436, 236, 368 and 1206 for part 2, all
cross-checked with an independent Python script (`/usr/bin/python3 -I`: a
breadth-first fill per region, and sides found by joining fence segments
into straight runs, not by counting corners). For performance, the same
script wrote a random 140 by 140 grid of letter blobs (1115 regions); the
program and Python agree on it (859142 and 554456). Compiler built from
`main` at 3117ab0b, 28 October 2026.

### The program

```stitchwort
def plantLetter(): {Parse} Char := Parse.satisfy "a letter" (char => char.isAsciiLetter)

def parseGarden (input: Text): {Fail} Garden :=
  let rows := Parse.all input (() => Parse.grid plantLetter)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .map (((row, plants)) =>
    Fail.ensure (plants.length == width) "line ${row + 1}: expected ${width} plots, as on the first line, got ${plants.length}")
  let plots :=
    rows.withIndex
      |> .flatMap (((row, plants)) => plants.withIndex |> .map (((column, plant)) => (({ row, column }: Position), plant)))
  { plots = Map.fromList plots }

def Garden.fill (garden: Garden) (plant: Char) (stack: List Position) (visited: Set Position) (members: List Position): List Position
    decreasing (garden.unvisited visited, stack.length)
:=
  match stack with
    | Nil => members
    | Cons position rest =>
      if fresh: visited.contains position = False then
        if grows: garden.plantAt position = Some plant then
          Garden.fill garden plant (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members)
            [decreasing := Nat.LexLess.First (garden.unvisitedInsert visited position plant grows fresh)]
        else Garden.fill garden plant rest visited members [decreasing := Nat.LexLess.Second rfl (omega)]
      else Garden.fill garden plant rest visited members [decreasing := Nat.LexLess.Second rfl (omega)]

def Garden.regionsFrom (garden: Garden): (starts: List Position) → (seen: Set Position) → List (List Position)
  | Nil, seen => Nil
  | Cons start rest, seen =>
    if seen.contains start then garden.regionsFrom rest seen
    else
      let region := garden.regionOf start
      Cons region (garden.regionsFrom rest (region.foldLeft seen Set.insert))

def Garden.isCorner (garden: Garden) (position: Position) (vertical: Direction) (horizontal: Direction): Bool :=
  match garden.sameAcross position vertical, garden.sameAcross position horizontal with
    | False, False => True
    | True, True => (position.diagonal vertical horizontal |> .flatMap garden.plantAt) != garden.plantAt position
    | _, _ => False

def solvePart1 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.length * garden.perimeter region)

def solvePart2 (garden: Garden): Nat := garden.regions |> .sumBy (region => region.length * garden.sides region)
```

The domain model is a `Map Position Char`, the plant at each plot.
`regions` walks the plots in order and starts a flood fill at each one not
yet in a region; the fill is depth-first, with a stack and a `Set` of
visited plots. A plot's fences are its sides not facing the same plant
(`fences`, summed to `perimeter`); its corners (`isCorner`, counted per
plot by `cornerCount` and summed to `sides`) are outside corners, where
neither the vertical nor the horizontal neighbour grows the same plant, and
inside corners, where both do but the plot diagonally across doesn't. A
region has as many sides as corners.

The fill terminates without fuel: `decreasing (garden.unvisited visited,
stack.length)`, lexicographic. Taking a plot shrinks the number of plots not
yet visited (`unvisitedInsert`, with `countFewer` and `positionsComplete`);
dropping a visited plot, or one growing another plant, keeps it and shrinks
the stack. Those three lemmas (45 lines) are in the program file, since the
program's termination needs them. Std's pigeonhole and iterate-repeat
lemmas weren't needed.

### Proved, for every map

The spec (`Spec/Spec.sw`) is in the puzzle's words over the program's
`plantAt` and `step` (the grid point one step in a direction).
`isOrthogonalStep` is arithmetic on rows and columns, as on day 10;
`touches` is that and `growSame`; `Joined plot other` is a chain of touching
plots from one to the other (`Exists` a list, checked by `isChain`);
`IsRegion garden plot region` says the list holds exactly the plots joined
to `plot`. `perimeter` counts the sides of the region's plots whose `step`
isn't a plot of the region. A side is "a straight section of fence";
`sides` counts each at its first section (`isFirstSection`): a fence
segment with no fence on the same side of the plot before it along the line
(left of it for a fence above or below, above it for one left or right).
`totalPrice regions measure` sums area times `measure`.

Proved (`Proofs/`, 1372 lines in 8 files):

- `regionOfIsRegion`: from a plot growing a plant, the fill lists every
  plot joined to it, and nothing else; `regionOfDistinct`: each once.
  `fillCorrect` carries an invariant through the fill's own `decreasing`
  measure: `visited` has exactly the members, members are distinct, grow
  the plant and are joined to the start, so is everything on the stack, and
  each neighbour a member pushed is a member or still on the stack (Fill.sw).
  Joined plots: reflexive, symmetric, transitive, and keep the plant
  (Joined.sw); `step` is the spec's orthogonal step (Steps.sw).
- `regionsAreRegions`: each of the program's regions is `IsRegion` of one
  of its plots, with no repeats; `inOneRegion`: every plot is in exactly
  one of them (Regions.sw).
- `part1Correct`: `solvePart1 garden = totalPrice garden.regions
  perimeter`; per region, `perimeterCorrect` (a side faces the same plant
  exactly when it touches a plot of the region, `sameAcrossFaces`).
- `part2Correct`: `solvePart2 garden = totalPrice garden.regions sides`;
  per region, `sidesCorrect`: the program's corner count is the spec's
  count of sides.

The corners-equal-sides step is `cornersEqualSides` (Corners.sw, 488 lines),
over a region as a grid of booleans with nothing at row or column
`Succ last`. Each corner is the end of exactly one run of fence along a row
(`rowEndsSplit`, a 16-case truth table): an outside corner is the end of
the plot's own fence above or below it; an inside corner is the end of the
neighbour's. Shifting a sum by one column (`totalLater`, `totalEarlier`)
lines these up (`rowCorners`), and along any line as many runs start as end
(`telescope`, `startsEqualEnds`). So the corners are twice the runs along
rows, and, by the same argument down columns (`columnCorners`), twice the
runs along columns: their number is the sum, the sides. Sides.sw connects
the program and the spec to the grid: per plot by cases on row and column
0 (`programCornersCell`, `specSidesCell`), and a sum over the region's plots
is a sum over a square big enough to hold it (`sumOverGrid`, through a
permutation, as on day 10).

Breaking the program (outside corners not counted, or a neighbour left out
of the fill) makes the proofs fail. Nothing is unproved; what the theorems
don't say is that the order of the regions is anything in particular, which
the price doesn't depend on. The spec runs on the program's regions, so
the tests also check `totalPrice regions perimeter` and `sides` against the
examples.

### 1. Std.Parse: none

`Parse.grid plantLetter` with `Parse.satisfy "a letter"` read the map first
time, and the messages read well: `line 2, column 2: expected a letter or
the end of the line, got '.'`; on empty input `line 1, column 1: expected a
letter, got the end of the input`. The row-length check is outside the
grammar, as on days 8 and 10, so its message has no column. Turning rows
into a `Map Position Char` is a `withIndex`/`flatMap` by hand; std has
`Map.byPosition` for one list (`crates/elab/src/std/Map/ByPosition.sw`) but
nothing for a grid. Fix: a
`Map.byGridPosition` (or `Parse.gridMap`).

Fixed: std has `List.gridCells` (`std/List/Grid.sw`), every cell of a list of
rows with its `(row, column)`, and `List.memGridCells`; `parseGarden` maps
it to `Position`s, and day 6's `parseLab` does the same.

### 2. Missing std

- `List.contains` with `DecEq`: tests and the spec write
  `region.any (member => member == plot)`. Scala has `contains`
  (<https://www.scala-lang.org/api/current/scala/collection/immutable/List.html>),
  Haskell `elem`
  (<https://hackage.haskell.org/package/base/docs/Data-List.html#v:elem>).
- Lemmas written here: `countLe` and `countFewer` (a count is monotone in
  its predicate, strictly when one member passes only the larger;
  in the program file, for termination), `sumByCongMem` (sums agree when
  terms agree on members), `memLeSumBy` (a member's term is at most the
  sum), `anyEqual` (`any (== x)` is membership), `notEqualNot` (item 3).
  Lean's core has `List.countP_mono_left` and `List.countP_congr`
  (<https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Count.lean>).
- A connected-components function: Haskell's containers has
  `components :: Graph -> [Tree Vertex]`
  (<https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Graph.html>);
  Mathlib defines `SimpleGraph.Reachable` ("a walk between them") and
  `ConnectedComponent` as its quotient, with `reachable_is_equivalence`
  (<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.html>).
  `Joined` and its lemmas here are that, for one grid.

None added to std (`List/Lemmas.sw` is another lane's). Fix: add
`List.contains`, the count and sum lemmas, and a grid-to-map builder.

Fixed: std has `List.contains` (List/Toolkit.sw, by `DecEq`) with
`List.memContains`, its membership `Iff` (List/Lemmas.sw), which replaces
`anyEqual`; the spec, proofs and tests use `region.contains plot`.
`sumByCongMem` and `memLeSumBy` are `List.sumByCongMem` and
`List.memLeSumBy` (List/Lemmas.sw, without `omega`); `countLe` was std's
`List.countLeMem`, and `countFewer` is `List.countLtMem` beside it
(List/SortLemmas.sw), both with the implication needed only on the
list's elements. `notEqualNot` stays, as `!=` is unchanged. The
grid-to-map builder isn't added.

### 3. Confusing errors

- `!=` and `!` in a theorem's statement are the `Prop` ones. Stating
  `(a != b) = Bool.not d` gave

  ```text
  [E-NOT-A-TYPE] Error: expected a type
    this has type `Bool`, so it isn't a type
    Note: `not` here is on propositions; for a `Bool` `b`, the proposition that it's true is `b = True`
  ```

  pointing into the right-hand side, not at the `!=` on the left (with
  `!d` on the right it pointed at that). Ascribing
  `((a != b): Bool)` worked. Then `!=` on `Bool` is
  `Decidable.toBool (Decidable.not d)`, not `!(a == b)`, so `rfl` failed
  between them and a lemma (`notEqualNot`, a `match` on the decision) was
  needed. Fix: point at the operator, and define `!=` as `!` of `==`.

  Fixed: the error is now at the `!=`: "in a statement, `!=` is the
  proposition, not a `Bool`", labelled "this `!=` is `Not (… = …)`, a
  proposition, so this `=` compares propositions", with the other side
  labelled "but this isn't a proposition", and the note "for the `Bool`
  that `!=` computes, ascribe it: `((x != y): Bool)`; or compare with `==`
  instead, as `(x == y) = False`". What `!=` means is unchanged.
- A function's `.unfold` couldn't be used when the program matched a `Bool`
  with an equation that a `decreasing` proof used (`match taken:
  visited.contains position with`): every way of stepping through it failed,
  `rewrite … , taken` with

  ```text
  [E-REWRITE-MOTIVE] Error: replacing `Set.contains visited position` everywhere in the goal doesn't give a valid proposition
  ```

  and `match c: visited.contains position with` with

  ```text
  [E-MATCH-MOTIVE] generalising this match's scrutinee makes its type ill-formed … rfl can't prove this
  ```

  What I did instead: rewrote the program with `if fresh:
  visited.contains position = False then`, a `Prop` `if`, and proved each
  step with std's `Decidable.elimEq`. Fix: generate step equations
  for each arm, as Lean does, or make the dependent `Bool`
  match generalise its equation too.
- "write this recursive call as `Aoc.Year2024.Day12.Garden.fill …`, not
  with a dot" — clear, but a
  surprise: `garden.fill …` works everywhere else. Fix: allow dot calls.


  Fixed: a recursive dot call passes `[decreasing := …]` as the prefix
  call does (`garden.fill plant … [decreasing := …]`, which `Garden.fill`
  now uses), and a wrong proof is reported at the proof, as for the prefix
  form. The old message remains only where the prefix form can't stand
  for the dot call (a piped receiver, say).
- `ring` is a keyword: "`ring` is a keyword, so it can't be used as a
  name". Clear; renamed the test's variable `loop`.
- A lambda parameter `plot` drew a `W-LAMBDA-SHADOW` warning for hiding the
  grammar `plot()`; renamed the grammar `plantLetter`.

### 4. Inference

- Holes aren't solved from the expected type for a higher-order argument:
  `Eq.trans (countDirections _) rfl` gave `expected `List.count directions
  (side => …) = …`, but this has type `List.count directions (?4 region) =
  …``, and `rewrite countDirections` found nothing. Named the spec's
  lambda `isFirstSection` and passed it.
- A `let` of a lambda proving an equation needs its type: `rfl proves an
  equation, but the expected type is `?11 garden start …``. Annotated.
- `Some { position | row = above }` is a parse error whose note gives the
  fix, `Some ({ … })` (day 1's item 7 again).

### 5. Performance

On the generated 140 by 140 grid `stitchwort run` takes 3.75 s user against
0.61 s on the 10 by 10 example (loading), so about 3.1 s of work: parsing
0.2 s, the regions 0.6 s, perimeters 0.45 s, corners 1.9 s (measured with
throwaway mains). Python takes 0.05 s. The first version kept the rows as
lists and looked plots up with `getOr` (two list walks per lookup): 6 s of
work; a `Map Position Char` halved it. Corners cost most: four quadrants of
two or three `Map` lookups each per plot. Not pursued further.

### 6. Proofs

- `n + 1` isn't `Succ n` by computation (day 4's item 2): with `step Down`
  written `position.row + 1`, the grid lemmas didn't compute. The program
  says `Succ position.row` instead, which reads less naturally.
- No decision procedure for `Bool`: the two 16-case truth tables in
  Corners.sw are 16 `rfl` clauses each, generated. And a wildcard in a
  `match` on three `Bool`s left `s ∧ False` stuck, so `omega` failed until
  every case was written out. Lean has `decide` for closed decidable goals
  (listed under Decision Procedures in
  <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>).
  Fix: a `decide` for `Bool` identities over variables (by cases).
- `omega` computes `total (Succ last) f` to `f 0 + total last …`, so facts
  had to be stated for every named sum separately (`totalAdd4` per corner
  kind) before `omega` could combine 23 of them in `rowCorners`; its
  listing of facts and atoms made this quick to see. It matched atoms by
  computing, which made the per-plot identities one `omega` each.
- No eta for records (day 5): lambdas over `Position` match
  `{ row, column }` first so the grid lemmas apply.

### 7. What went well

The fill, regions and perimeter proofs (Fill, Joined, Regions, Fences,
Steps; about 620 lines) mostly checked first time.
Lexicographic `decreasing` gave a fuel-free fill whose proof follows the
same measure. In the corner argument (Corners.sw, Sides.sw), once the sums were in one form, `cornersEqualSides` checked first
time. Lean's `termination_by` is the same idea, with tuples ordered
lexicographically
(<https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion>).

### Size and time

Release build, load average around 22:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day12.Proofs` | 2.7 s user (5.3 s) |
| `stitchwort check --no-cache Aoc.Year2024.Day12` | 1.9 s user (4.2 s) |
| `stitchwort test --no-cache Aoc.Year2024.Day12` (33 tests) | 3.1 s user (6.3 s) |
| `stitchwort test Aoc.Year2024.Day12` (warm) | 1.1 s user (2.3 s) |
| `stitchwort run Aoc.Year2024.Day12.main` on the larger example | 0.61 s user |
| `stitchwort run Aoc.Year2024.Day12.main` on a generated 140 by 140 grid | 3.75 s user |
| `stitchwort check --no-cache` (whole aoc project, 83 namespaces) | 16.5 s user (19 s) |

179 lines of program (45 of them termination lemmas), 77 of spec, 1372 of
proofs, 158 of tests.

### Ranked

1. `.unfold` unusable through a dependent `Bool` match (item 3). Fix:
   per-arm equations, or generalise the equation with the scrutinee.
2. `!=`/`!` in statements are `Prop`, the error points elsewhere, and
   `!=` isn't `!` of `==` (item 3). Fix: point at the operator; define `!=`
   as `!(==)`.
3. No `Bool` decision procedure; wildcards leave `x ∧ False` stuck (item
   6). Fix: a `decide` that splits `Bool` variables.
4. `n + 1` isn't `Succ n` (item 6). Fix: reduce `n + 1` to `Succ n`.
5. Holes not solved for higher-order arguments (item 4). Fix: unify
   against the expected type first.
6. Missing `List.contains`, count and sum lemmas, grid-to-map (items 1, 2).
   Fix: add them.
7. Corners cost 1.9 s on a 140 by 140 grid (item 5). Fix: none needed
   yet; a faster `Map` lookup on records would help.
8. Dot calls refused with `[decreasing := …]` (item 3). Fix: allow them.

## Day 13: Claw Contraption

Claw machines, each with two buttons. "It costs 3 tokens to push the A
button and 1 token to push the B button", each button moves the claw "a
specific amount to the right (along the X axis) and a specific amount
forward (along the Y axis)", and "to win the prize, the claw must be
positioned exactly above the prize on both the X and Y axes". Part 1:
"each button would need to be pressed no more than 100 times to win a
prize ... What is the fewest tokens you would have to spend to win all
possible prizes?" Part 2: "the position of every prize is actually
10000000000000 higher on both the X and Y axis!", with the same question
and no limit on presses (part 2's wording from the public copy at
<https://github.com/RobUrsem/AdventOfCode2024/blob/902b2370d8aaf06d7190ce4a64d870a30fdbcf47/13/day13.txt>).
Part 1 calls the limit an estimate ("You estimate that..."); the spec
takes it as the rule, as part 1's answer needs.

**The real input is pending from Matt.** `mdr/aoc-2024` stops at day 10,
so day 13 has no `aoc/inputs/2024/day13.txt`, no `Tests/Input.sw` and no
entry in `crates/cli/tests/aoc_answers.rs` or `crates/rt/tests/machine.rs`;
add those when the input comes.

The example's answers are checked: 480 for part 1 (280 and 200 for the
first and third machines), and for part 2 only the second and fourth
machines can be won, for 875318608908. Both agree with an independent
Python script (`/usr/bin/python3 -I`): part 1 by trying every press count
from 0 to 100, part 2 by Cramer's rule in exact fractions (`Fraction`).
The timings below are on 320 machines that script generated (buttons 10
to 99 along each axis, a third with prizes reachable in part 1, a third
reachable in part 2; not committed), on which the program and the script
agree: 20815 and 15537437117353. Compiler built from `main` at 880db192,
28 October 2026.

### The program

```stitchwort
type Offset = { x: Int, y: Int }

type Machine = { buttonA: Offset, buttonB: Offset, prize: Offset }

def offset (sign: Text): {Parse} Offset :=
  text "X${sign}"
  let x := nat()
  text ", Y${sign}"
  let y := nat()
  { x = x.toInt, y = y.toInt }

def clawMachine(): {Parse} Machine :=
  text "Button A: "
  let buttonA := offset "+"
  newline()
  text "Button B: "
  let buttonB := offset "+"
  newline()
  text "Prize: "
  let prize := offset "="
  { buttonA, buttonB, prize }

def parseMachines (input: Text): {Fail} (List Machine) := Parse.all input (() => sections clawMachine)

def onlyPresses (machine: Machine) (nonzero: determinant machine ≠ 0): Option (Nat, Nat) :=
  let prize := machine.prize
  let aPresses := (prize.x * machine.buttonB.y - prize.y * machine.buttonB.x) / determinant machine
  let bPresses := (machine.buttonA.x * prize.y - machine.buttonA.y * prize.x) / determinant machine
  Option.map2 (a b => (a, b)) aPresses.toNatChecked bPresses.toNatChecked |> .filter (((a, b)) => wins machine a b)

def fewestTokensWithin (limit: Nat) (machine: Machine): Option Nat :=
  if nonzero: determinant machine ≠ 0 then
    onlyPresses machine nonzero
      |> .filter (((aPresses, bPresses)) => aPresses ≤ limit && bPresses ≤ limit)
      |> .map (((aPresses, bPresses)) => tokens aPresses bPresses)
  else searchTokens limit machine

def fewestTokens (machine: Machine): Option Nat :=
  if nonzero: determinant machine ≠ 0 then
    onlyPresses machine nonzero |> .map (((aPresses, bPresses)) => tokens aPresses bPresses)
  else collinearTokens machine

def solvePart1 (machines: List Machine): Nat := machines.sumBy (machine => fewestTokensWithin 100 machine |> .getOrElse 0)

def solvePart2 (machines: List Machine): Nat := machines.sumBy (machine => corrected machine |> fewestTokens |> .getOrElse 0)
```

`main` is `parseMachines IO.readAll()` and the two prints. The domain
model is `Int` throughout: Cramer's rule subtracts. With a nonzero
determinant `ax * by - ay * bx` the two equations have one solution, and
`onlyPresses` divides for it and checks it: the check (`wins`) is what
rejects a solution that isn't whole, since `/` rounds; `toNatChecked`
rejects a negative one. `/` found the `nonzero` parameter as its proof
with nothing written.

The determinant is 0 when the buttons move the claw along the same line
(or one doesn't move it), and the puzzle doesn't rule that out. Then a
prize on that line can have many winning press counts. Part 1 tries every
count up to 100 (`searchTokens`, the spec's own search). Part 2 can't, so
`collinearTokens` uses a swap: if `p` presses of A move the claw as far
as `q` of B, swapping them keeps a win and changes the cost by `q - 3p`,
so the cheapest win presses A fewer than `p` times or B fewer than `q`
times, and `p` is at most B's larger coordinate (and `q` A's). It tries
those counts of one button and works out the other (`pressesToCover`),
about 200 tries per machine. That reasoning isn't proved; it is tested
against `searchTokens` on twelve machines along the same line, including
zero buttons, a prize off the line, and either button cheaper per step.

### Proved

The spec (`Spec/Spec.sw`) is the puzzle's words: `cost` is 3 per A press
and 1 per B press, `winsPrize` is the two equations, and `winningCosts`
lists the cost of every winning pair of press counts from 0 to 100 (a
`flatMap` over `List.range 101`), whose `minimum` is `fewestTokens` and
whose sum over the machines, with 0 for those that can't be won, is
`part1`. Part 2 has infinitely many press counts, so its spec is a
statement: `Fewest machine tokens` says some presses win for `tokens` and
no winning presses cost less, `Unwinnable` that no presses win, and
`Part2Answer machines answer` that `answer` is the sum, over the machines
with their prizes moved (`correctedMachine`), of what some function that
is right about every machine says each costs.

Proved (`Proofs/`, 289 lines in five files), with no axioms
(`stitchwort axioms`):

- `part1Correct`: `solvePart1 machines = part1 machines`, for every list
  of machines, whatever their determinants, from `withinCorrect`
  (`fewestTokensWithin 100 machine = fewestTokens machine`, the spec's).
  With a zero determinant the program's search is the spec's
  (`searchIsSpec`, by `rfl`). Otherwise `cramerWithinCosts`: when Cramer's
  presses win within 100, every cost the spec lists is theirs and theirs
  is listed, so the minimum is theirs (`minimumAllEqual`); otherwise
  nothing is listed (`minimumEmpty`).
- `part2Correct`: `Part2Answer machines (solvePart2 machines)`, for
  machines whose determinants are all nonzero (an explicit hypothesis),
  from `fewestTokensCorrect`: `fewestTokens machine` is `Some` of the
  fewest tokens, or `None` and the machine can't be won.
- `part2AnswerUnique`: the spec's part 2 has one answer, so
  `part2Correct` pins `solvePart2` down (`fewestUnique` per machine).
- Under them (`Cramer.sw`): `onlyPressesFinds`, any presses that win are
  the ones `onlyPresses` finds, and `onlyPressesWins`, those win. The
  first is the algebra: `aTimesDeterminant` (A's presses times the
  determinant are Cramer's numerator) is `ring [by * alongX, bx *
  alongY]`, then `mulDivCancel` (`(d * a) / d = a` for `d ≠ 0`, in
  `Lemmas.sw`).

Breaking the program (B's numerator negated, `<` for `≤` at the limit, 2
tokens for A) makes the proofs fail.

Not proved: part 2 with a zero determinant. The proof would need the
swap argument above: that two wins differ by a multiple of `(p, -q)` with
`p` and `q` coprime, which is gcd reasoning (day 8 has some in
`Proofs/Gcd.sw`), and an induction swapping presses down to the cheapest.
I estimate 200 lines or more, against a case real inputs may never have,
so I stopped at the hypothesis and the tests. Whether Matt's input has
such a machine is unknown until it comes.

### 1. Std.Parse: one message

The grammar read the example first time, `text "X${sign}"` sharing the
offset grammar between "X+94" and "X=8400". A minus sign gives `line 1,
column 11: expected 'X+', got 'X-'`, and a missing prize `line 3, column 1:
expected 'Prize: ', got the end of the input`; both good. A missing blank
line between machines doesn't mention the blank line:

```text
line 4, column 1: expected the end of the input, got 'B'
```

for `...Prize: X=5, Y=6\nButton A: ...`. `sections` tries `blankLine`
after the prize line; it reads the line break and fails on 'B', but
`blankLine` is a `labelWhole`, so its expectation is placed where it
started, one character before `Parse.all`'s own "end of the input",
which is further and wins. What I did instead: nothing; the test records
the message.

Fixed: `labelWhole` reports its label at the furthest point its parser
read to, as Megaparsec keeps the error that got furthest, so a missing
blank line is `line 4, column 1: expected a blank line or the end of the
input, got 'B'`.

### 2. Missing std

- `(d * a) / d = a` for a nonzero `Int` `d`, Lean's
  `Int.mul_ediv_cancel_left` (`{a : Int} (b : Int) (H : a ≠ 0) : a * b /
  a = b`, <https://lean-lang.org/doc/api/Init/Data/Int/DivMod/Bootstrap.html>).
  `Lemmas.sw` proves it from `Int.divAddMod` and the remainder's bounds:
  `quotientOfMultiple` and `smallMultiple` (a multiple of `d` from 0 to
  below `|d|` is 0), 20 lines.
- Day 8's `natAbsMul` and `natAbsZero` are in `Aoc.Year2024.Day08.Proofs`;
  day 13 imports them from there (it checks day 8's proofs too, 2.7 s
  without the cache).
- No lemmas about `List.minimum`: `minimumAllEqual` (a list holding
  `least` and nothing else has least `least`) and `minimumEmpty` are in
  `Lemmas.sw`, with `minSelf` (`Ord.min n n = n`, by `cases`).
- No `import ... as`: the spec's `fewestTokens` and the program's clash in
  the tests, and `import Aoc.Year2024.Day13.Spec as Spec` gives `[E-PARSE]
  Error: expected `(` and the names to import, but found `as``. I wrote
  `Aoc.Year2024.Day13.Spec.fewestTokens` in full.

No std file was changed.

Fixed: std has `Int.mulDivCancel`, `Int.natAbsMul` and `Int.natAbsZero`
(Int/Lemmas.sw), and `List.minimumAllEqual` and `List.minimumEmpty` for
any `Ord` (List/Lemmas.sw), with `Ord.minSelf`. `Proofs/Lemmas.sw` is gone,
and days 8 and 13 use std's.

### 3. Confusing errors

- `ring` said two equal-looking atoms differ:

  ```text
  [E-RING] Error: `ring` can't prove `d * a % d = d * (a - (d * a / d))`
    Note 5: left over: `d * (d * a / d) - d * (d * a / d) + (d * a % d) - (d * a % d)`, the goal's left minus its right, minus each coefficient times its hypothesis's `l - r`; it has to be 0
  ```

  for `ring [Int.divAddMod (d * a) d]`, whose `d * (d * a / d) + d * a %
  d = d * a` is what the goal needs. Probably (not checked in the
  compiler) the `/` in `divAddMod`'s statement carries its own `auto`
  proof of `d ≠ 0` and mine carries `nonzero`, and `ring` compares atoms
  with their proofs. The evidence: the same step with the quotient and
  remainder as variables (`quotientOfMultiple`) checked first time. The
  message should say the atoms differ in a hidden argument.
- Elaborating `List.anyElim _ _ (List.range 101) ...` unfolded `List.Any`
  over the concrete 101-element range:

  ```text
  [E-TYPE-MISMATCH] Error: type mismatch
    expected `?14 machine tokensSpent listed 0 ∨ ?14 machine tokensSpent listed 1 ∨ ?14 machine tokensSpent listed 2 ∨ … ∨ …`, but this has type `List.Any (x => tokensSpent ∈ List.map (List.filter (List.range 101) ...
  ```

  I gave the predicate and the goal explicitly (`WinWithin`, a `def` for
  the existential, and `costsAfter` for the inner list).
- `match` on an expression written as in the program didn't find it in
  the goal: `match aChecked: Int.toNatChecked ((prize.x * ... - ...) /
  determinant machine) with` left the goal unchanged in every arm,
  because the goal shows `determinant` unfolded and `-` as `+ Int.neg`.
  No error said the scrutinee wasn't found; only the goals did. `cases`
  then gave `[E-CASES] Error: `cases` found nothing to split on, and
  nothing closes the goal` for the implication, and on the `if`,
  `[E-CASES-BUDGET] Error: `cases` made more than 64 cases without closing
  them all`, having split on the buttons' coordinates. What I did instead
  is under item 6.
- `rewrite withinCorrect machine` inside `sumByCong`'s function:
  `[E-REWRITE-BUDGET] Error: `rewrite` couldn't decide whether a part of
  the goal is the rule's left side`, "comparing them by computing ran out
  of budget". `Eq.cong (result => Option.getOrElse result 0)
  (withinCorrect machine)` worked.
- `W-LAMBDA-SHADOW`: the parser `machine` "hides" every `machine =>`
  lambda in the proofs (imported by `(..)`). Renamed it `clawMachine`.

Fixed: a named `match` whose expression is in neither the goal nor a
hypothesis, and whose arms don't use its equation, warns
(`W-MATCH-NOT-FOUND`), showing the goal as the search saw it.

### 4. Inference

Nothing went wrong in the program: it checked first time, including the
`auto` proof for `/ determinant machine` from the `nonzero` parameter,
`Option.map2 (a b => (a, b))`, and the record update `{ machine | prize =
... }`. In the proofs, `_` for a `List.Any` predicate or a motive failed
as in item 3; `DecEq.sound _ _ (Bool.andLeft _ _ won)` on an `Int` `==`
worked, unlike day 11's `Nat` case.

### 5. Performance

Running is all loading: `run` on the 320 generated machines takes 0.29 s
(user), the same as on the example (0.33 s); the Python script takes
0.16 s. Part 2's numbers reach about 10^15, and `Int` is arbitrary
precision, so nothing overflows; Cramer's rule is a few multiplications
per machine.

Checking the proofs was the slow part: 25 s at first, all in `Part1.sw`.
A `match` in a proof whose goal mentions `winningCosts machine` makes the
goal compute, and the spec's list unfolds to 101 `filterStep`s (the goals
showed `List.filterStep 0 (List.filterStep 1 (...`). Stating the lemmas
for any list `costs` with the two membership facts (`cramerWithinCosts`,
`withinCosts`), and applying them to `winningCosts` once at the end,
brought it to 7 s.

### 6. Proofs

The algebra was easy; the plumbing around `if` and `match` was not.

- `ring` with coefficients did Cramer's elimination first time:
  `aTimesDeterminant` is `ring [machine.buttonB.y * alongX,
  machine.buttonB.x * alongY]`, the second hypothesis needing a minus,
  which `ring` found itself ("also tried the other way round"). This is
  Lean's `linear_combination` ("attempts to prove an (in)equality goal by
  exhibiting it as a specified linear combination",
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html>).
- `omega` handled `Int.natAbs` and `Nat.toInt` as atoms with their facts:
  `smallMultiple`'s steps, `ofNatAbs`'s impossible case, and the press
  bounds from `List.memRangeFrom`.
- No proof irrelevance by computation. The program's `if nonzero: ...`
  passes the proof into `onlyPresses`, so a lemma "an `if h: p` takes its
  first branch" can't be `rfl`:

  ```text
  [E-REFL] Error: `rfl` can't prove this
    `yes y` and `yes h` aren't equal
  ```

  In Lean "any two proofs of the same proposition are completely
  interchangeable"
  (<https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/>).
  What worked: `match Int.decEq (determinant machine) 0 with`, which is
  the `if`'s own decision, so the goal computes into the right branch,
  with the proof inside it. Every Cramer lemma takes the proof as a
  parameter, so whichever proof arrives is fine.
- Taking apart `onlyPresses`'s result: its first version was a `match`
  on the pair of `toNatChecked`s and an `if wins`, and I found no way to
  invert `onlyPresses machine nonzero = Some (a, b)` (item 3). I rewrote
  it as `Option.map2 ... |> .filter (... => wins machine a b)`, so std's
  `Option.filterEqSome` gives the win in one line. The new form reads as
  well, but this is reshaping the program for the proof: a way to invert
  a `match` in a hypothesis would remove the need. In Lean, "split at h
  will split the hypothesis h"
  (<https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>).

### 7. Comparisons

- Lean's `linear_combination` and `ring [c * h]`: item 6.
- Lean's `Int.mul_ediv_cancel_left`: item 2.
- Lean's definitional proof irrelevance and `split at h`: item 6.

### Size and time

Release build, on a machine with a load average around 25 to 30:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day13.Proofs` | 7.2 s |
| `stitchwort check --no-cache Aoc.Year2024.Day13` | 0.6 s |
| `stitchwort test --no-cache Aoc.Year2024.Day13` (25 tests) | 7.7 s |
| `stitchwort run Aoc.Year2024.Day13.main` on the example | 0.33 s |
| `stitchwort run Aoc.Year2024.Day13.main` on 320 generated machines | 0.29 s |
| `stitchwort check` (whole project, cached) | 8.1 s |

126 lines of program, 62 of spec, 289 of proofs, 95 of tests.

### Ranked

1. The real input is pending: Matt's repository has no day 13. Fix: add
   his input, its tests and its two answer entries when he has it.
2. Part 2 is proved only for nonzero determinants, which the puzzle
   doesn't promise (Proved). Fix: prove the swap argument over day 8's
   gcd lemmas, or, if Matt's input has none, leave the hypothesis.
3. A `match` in a proof computes the whole goal, unfolding a concrete
   spec list into 101 steps: 25 s of checking (item 5). Fix: refine only
   the scrutinee's occurrences without normalising the rest.
4. No proof irrelevance by computation, and no way to invert a `match` in
   a hypothesis (item 6). Fix: make proofs of a proposition
   definitionally equal, and add a `split at h`.
5. Unification unfolds `List.Any` over a concrete list into a disjunction
   (item 3). Fix: don't unfold a definition over a literal list while
   solving a metavariable.
6. `ring` reports equal-looking atoms as different (item 3). Fix: say
   the atoms differ in a hidden argument, or compare proofs as equal.
7. `match` on an expression not in the goal says nothing (item 3). Fix:
   warn when a named `match` replaces nothing.
8. Missing `Int.mulDivCancel`, `List.minimum` lemmas, and day 8's `Int`
   lemmas live in day 8 (item 2). Fix: move them to std's `Int` and
   `List` files.
9. `sections` doesn't name the missing blank line (item 1). Fix: let a
   `labelWhole` expectation count at the furthest point its parser
   reached.
10. No `import ... as` for clashing names (item 2). Fix: add an alias form.

## Day 14: Restroom Redoubt

Robots, each with a position `p=x,y` and a velocity `v=x,y` in "tiles per
second", in "a space which is 101 tiles wide and 103 tiles tall" (11 by 7
in the example). "When a robot would run into an edge of the space they're
in, they instead teleport to the other side, effectively wrapping around
the edges." Part 1: "count the number of robots in each quadrant after 100
seconds. Robots that are exactly in the middle (horizontally or vertically)
don't count as being in any quadrant", and multiply the four counts (the
"safety factor"). Part 2: the robots "should have a hard-coded Easter egg:
very rarely, most of the robots should arrange themselves into a picture of
a Christmas tree. What is the fewest number of seconds that must elapse for
the robots to display the Easter egg?" (part 2's wording from the public
copy at
<https://github.com/gchan/advent-of-code-ruby/blob/main/2024/day-14/README.txt>).

**The real input is pending from Matt.** `mdr/aoc-2024` stops at day 10,
so there is no `aoc/inputs/2024/day14.txt`, no `Tests/Input.sw` and no
entry in `crates/cli/tests/aoc_answers.rs` or `crates/rt/tests/machine.rs`;
when the input comes, add those.

**Part 2's criterion is a choice.** The puzzle doesn't say what the picture
looks like. This solution takes it to be every robot on a different tile,
a heuristic other solvers used ("look for all unique positions? Which
works somehow?", <https://elixirforum.com/t/advent-of-code-2024-day-14/68091>).
The proofs are about
that criterion: the answer is the least second at which no two robots share
a tile. Nothing proves that this is the picture of a tree.

The example's answers are 12 and 1 (two robots share `3,0` at second 0;
none share a tile at second 1), on 11 by 7, agreeing with an independent
Python script (`/usr/bin/python3 -I`, positions `(x + t*vx) % w` and a
`set` per second). `main` uses the puzzle's 101 by 103; `mainExample` uses
11 by 7, since a program can't take arguments:

```
$ stitchwort run Aoc.Year2024.Day14.mainExample < examples/2024/day14.txt
Part 1: 12
Part 2: 1
```

The timings are on a generated input of 500 robots on 101 by 103 (not
committed), built in Python with all positions distinct first at second
7037; the program and the Python script agree (213181710 and 7037).
Compiler built from `main` at c17208db, 28 October 2026.

### The program

```stitchwort
type Position = { x: Nat, y: Nat }
type Velocity = { x: Int, y: Int }
type Robot = { position: Position, velocity: Velocity }
type Space = { width: Nat, height: Nat, widthPositive: width ≠ 0, heightPositive: height ≠ 0 }

def robotLine(): {Parse} Robot :=
  text "p="
  let x := nat()
  text ","
  let y := nat()
  text " v="
  let dx := int()
  text ","
  let dy := int()
  { position = { x, y }, velocity = { x = dx, y = dy } }

def parseRobots (input: Text): {Fail} (List Robot) := Parse.eachLine input robotLine

def wrap (size: Nat) [auto ok: size ≠ 0] (coordinate: Int): Nat := Int.modNat coordinate size

def Space.positionAfter (space: Space) (seconds: Nat) (robot: Robot): Position := {
  x = wrap space.width [ok := space.widthPositive] (robot.position.x.toInt + seconds.toInt * robot.velocity.x),
  y = wrap space.height [ok := space.heightPositive] (robot.position.y.toInt + seconds.toInt * robot.velocity.y)
}

def Space.quadrantOf (space: Space) (position: Position): Option Quadrant :=
  let middleColumn := space.width / 2
  let middleRow := space.height / 2
  if position.x == middleColumn || position.y == middleRow then None
  else if position.y < middleRow then Some (if position.x < middleColumn then TopLeft else TopRight)
  else Some (if position.x < middleColumn then BottomLeft else BottomRight)

def Space.safetyFactor (space: Space) (positions: List Position): Nat :=
  let inQuadrants := positions.filterMap space.quadrantOf
  quadrants.map (quadrant => inQuadrants.count (== quadrant)) |> .product

def solvePart1 (space: Space) (robots: List Robot): Nat := space.positionsAfter 100 robots |> space.safetyFactor

def noOverlapFrom (seen: Set Position): List Position → Bool
  | Nil => True
  | Cons position rest => if seen.contains position then False else noOverlapFrom (seen.insert position) rest

def solvePart2 (space: Space) (robots: List Robot): Option Nat :=
  List.range space.period |> .find (seconds => space.positionsAfter seconds robots |> noOverlap)
```

Positions are `Nat`s, velocities `Int`s. A robot jumps straight to
`position + seconds * velocity`, wrapped with std's `Int.modNat` (the
Euclidean remainder as a `Nat`), so the program never steps. The space
carries the proofs that its sides aren't 0, which `Int.modNat` needs;
`Space.of 101 103` finds them by `auto`. Part 2 tries the seconds from 0
to `width * height - 1` (`Space.period`, 10403 for the puzzle) and stops at
the first with no shared tile; the overlap check stops at the first
repeat. `main` also fails on a robot outside the space (`line 2: the robot
starts outside the space`), which the proofs assume.

### Proved, for every list of robots that start inside the space

The spec (`Spec/Spec.sw`) is the puzzle's words, run literally: `forward`
and `backward` move one tile, teleporting at the edges; `move` takes
`|v|` such tiles one at a time; `second` moves both coordinates; `after`
iterates seconds. A tile is in the left half when more tiles lie to its
right than to its left (`x < width - 1 - x`), in the right half when fewer
do, and the middle column has as many each side; the same for rows. The
safety factor multiplies the four counts. `isPicture` is the criterion:
`List.Distinct` of the robots' positions after that many seconds.

Proved (`Proofs/`, 303 lines in six files):

- `afterCorrect`: `after space seconds robot = space.positionAfter seconds
  robot`: moving one tile at a time for `seconds` seconds is the jump, with
  wrap-around, for negative velocities and velocities past the width too
  (Moves.sw). It rests on `forwardWrap` and `backwardWrap` (one tile is
  `+ 1` or `- 1`, then `Int.modNat`) and `iterateWrap` (a step that adds
  `d` and wraps, taken `n` times, adds `n * d` and wraps), whose induction
  is std's `Int.modNatModAdd` plus a `ring` step (Lemmas.sw).
- `periodic`: `positionAfter (seconds + width * height) = positionAfter
  seconds`, and `periodicLaps` for any number of laps: std's
  `Int.modNatAddMulInt` after `ring` regroups `(t + w*h) * v` as `t*v + w *
  (h*v)`. The period is `width * height`, which for coprime sides such as
  101 and 103 is their lcm, 10403; it holds for any sides.
- `part1Correct`: `solvePart1 space robots = part1 space robots` for spaces
  of odd width and height, as the puzzle's are. It goes through
  `safetyFactorCorrect` (Quadrants.sw): each quadrant's agreement
  (`topLeftAgrees` and three more) is one `cases`, splitting the `if`s and
  closing 16 cases by `omega` with `/ 2` and `% 2`; `countQuadrant` turns
  the program's count over `filterMap` into the spec's filtered length.
- `part2First`: if `solvePart2` gives `Some found`, the spec's robots are
  all on different tiles after `found` seconds, and at no earlier second.
  `noOverlapCorrect` shows the `Set` loop decides `List.Distinct`
  (Overlap.sw); `findRangeSome` shows `List.find` over `List.range` finds
  the least (Search.sw).
- `part2Never`: if it gives `None`, no second at all has them on different
  tiles: second `s` looks like second `s % (width * height)`, which was
  searched.

Breaking the program (forgetting the middle row, `+ 1` on a move,
searching one second fewer) makes the proofs fail. The odd sizes matter:
for an even width the program leaves column `width / 2` out of the right
half, while the spec has no middle column (`topLeftAgrees` still checks
without the hypothesis; the right and bottom halves need it). Not proved,
as above: anything about a tree.

### 1. Std.Parse: none

`text "p="`, `nat()`, `int()` (std has `Parse.int`, an optional `-` then
digits) under `Parse.eachLine` read the example first time. The messages
are good: `line 1, column 3: expected a number, got '-'` for a negative
position, `line 1, column 6: expected ' v=', got the end of the line` for a
missing velocity.

### 2. Missing std

- No program arguments: `IO` has `readAll` and friends but no `args`, so
  the space's size can't be given on the command line. Two mains,
  `main` (101 by 103) and `mainExample` (11 by 7). Haskell has `getArgs ::
  IO [String]`
  (<https://hackage.haskell.org/package/base/docs/System-Environment.html>).
- No `Bool` test for "no repeats": `List.Distinct` is a `Prop`, and
  `List.distinct` builds the list without repeats (comparing lengths would
  not stop early). Lean has `List.Nodup` with a `Decidable` instance,
  `List.nodupDecidable`
  (<https://lean-lang.org/doc/api/Init/Data/List/Basic.html>). Wrote
  `noOverlapFrom` with a `Set` and its three lemmas (Overlap.sw, 42 lines,
  following std's `List.distinctLoopFrom`).
- Nothing says `List.find` over `List.range` finds the least: std's
  `List.findSome` gives membership only. `findRangeFirst`, `findRangeSome`
  and `findRangeNone` (Search.sw, 31 lines).
- Smaller: `count (filterMap f xs) (== q) = count xs (x => f x == Some q)`
  (`countFilterMap`), `a ≠ 0 → b ≠ 0 → a * b ≠ 0` (`mulNeZero`) and
  `Int.modNat x.toInt size = x` below `size` (`modNatSmall`), in
  Lemmas.sw. Not added to std: another lane is adding count lemmas to
  `List/Lemmas.sw`, and the other two are one-liners.

Fixed: `IO.args()` gives the arguments after `--`, on every runner and in
built executables: `stitchwort run Aoc.Year2024.Day14.main -- 11 7` runs
the example, and `main` without arguments uses 101 by 103; `mainExample`
is gone. std has `List.allDistinct` with `List.allDistinctCorrect`
(List/Distinct.sw), which replace `noOverlap` and `Overlap.sw`, and
`List.findRangeFirst`, `List.findRangeSome` and `List.findRangeNone`
(List/Lemmas.sw), which replace `Search.sw`.

### 3. Confusing errors

- A proof of `List.Distinct Nil`, which computes to `Unit`, written `()`:

  ```text
  [E-TYPE-MISMATCH] Error: type mismatch
     │   | seen, Nil, ok => ()
     │                      ─┬
     │                       ╰── expected `Unit`, but this has type `()`
  ```

  `()` is the unit value in programs; in a proof it has to be `Trivial`.
  The message reads as if the two were different things with the same
  meaning.
- `omega` computed `Nat.toInt (Succ x) - 1` into std's internals before
  looking at it:

  ```text
  [E-OMEGA] Error: `omega` can't prove `Int.subNatNatFrom (Succ x) 1 (0 - x) = x.toInt`
     │ Note 2: atoms: `Int.subNatNatFrom (Succ x) 1 (0 - x)`, `x`, `n`
  ```

  The same statement about a variable `y` with `0 < y` is one `omega`
  (`toIntPred`), applied to `Succ x`.
- `rewrite <- negSuccIs steps` (`NegSucc steps = (Succ steps).toInt * -1`)
  found nothing, because the goal's `x.toInt + NegSucc steps` had been
  computed to `Int.subNatNatFrom x (Succ steps) (Succ steps - x)`:

  ```text
  [E-REWRITE-NOTHING] Error: `rewrite` found no `Nat.toInt (Succ steps) * -1` in the goal
     │ Note 2: the search compares what terms compute to: it looked for `NegSucc (steps * 1)`, what `Nat.toInt (Succ steps) * -1` computes to, in what the goal computes to
  ```

  `Eq.trans` with an `Eq.cong` over the distance did it.
- Hypotheses are shown computed, so after a `match` on
  `seen.contains next` the hypothesis `ok` showed `Set.insert` unfolded:
  `ok: noOverlapFrom { items = { raw = Quot.lift (rawMap => Quot.mk {
  tree = Map.Tree.insertWith (new old => new) next () rawMap.tree, ...`
  for 400 characters, instead of `noOverlapFrom (seen.insert next) rest`.
- `.sortBy (position => position.y * 11 + position.x)` (Scala's `sortBy`
  takes a key) gave `` `+` gives a `Nat` or an `Int` ... but `Position →
  Ordering` is expected here ``, pointing at the key's arithmetic.
  Stitchwort's `sortBy` takes a comparison and `sortOn` the key, as in
  Haskell; nothing pointed at `sortOn`. Used `sortOn`.
- A theorem ending in `a * b ≠ 0` takes one more argument, the proof of
  `a * b = 0` (day 11's item 3 again): `this arm has 4 pattern(s), but
  `mulNeZero` takes more arguments after the colon`.

Fixed: `()` where a proof of `Unit` is expected is `Trivial`.

### 4. Inference

- `auto` doesn't look into the fields of a record in scope:
  `Int.modNat coordinate space.width` couldn't find `space.widthPositive`,
  so every use says `[ok := space.widthPositive]`; the program and proofs
  have 14 such `[ok := …]` annotations, and the lemmas take the proof as
  an explicit parameter.
- `seconds % space.period` in a theorem's statement: `can't decide
  `Space.period space ≠ 0` here`. A `let ok: space.period ≠ 0 :=
  periodPositive space` before it, or a parameter, fixed it.
- `f a -1` is `f a - 1`, as in Haskell; `(-1)` needed.
- `test` is a keyword, so a predicate parameter can't be called `test`;
  the message says so.

### 5. Performance

On the generated 500 robots (user time): `stitchwort run` 4.81 s, of which
about 0.5 s is loading (the example takes 0.51 s), so about 4.3 s for 7037
seconds of searching (3.5 million robot moves and up to as many `Set`
insertions, stopping at the first repeat each second). Python takes 0.32 s.
Not pursued: the jump formula already avoids stepping, and the time is
spread over the moves and the set.

### 6. Proofs

- `Int` modulo by a variable size: `omega` handles `%` only by a constant,
  so every step about wrapping went through std's lemmas, which were
  there: `Int.modNatModAdd` (wrapping before adding changes nothing) and
  `Int.modNatAddMulInt` (adding a multiple of the size, negative too,
  changes nothing). They are in `Mod/Mod.sw` though they are about `Int`,
  and are for `Int.modNat` with a `Nat` size; there are none for `Int %
  Int` with a variable divisor. Lean's core has the `%` forms,
  `Int.emod_add_emod` and `Int.add_mul_emod_self_right`
  (<https://lean-lang.org/doc/api/Init/Data/Int/DivMod/Bootstrap.html>).
  Using `Int.modNat` was the right call: positions stay `Nat`s, and
  `Int.modNat x (Succ n)` computes, so `forwardWrap` is `Nat.modSelf` and
  `Nat.modSmall` after matching the size against `Succ n`.
- `ring` did the `Int` regrouping with `Nat.toInt` of sums and products
  inside (`(t + w*h).toInt * v = t.toInt * v + w.toInt * (h.toInt * v)`),
  first time.
- `cases` proved each quadrant agreement alone (16 cases: 8 by computation,
  the rest by `omega` with `/ 2` and `% 2`).
- The periodicity, the least-second search and its `None` case went
  through as planned, most lemmas first or second time; the friction was
  in items 3 and 4, not in the mathematics.

Fixed: the `Int.modNat` lemmas (`Int.modNatModAdd`, `Int.modNatAddMulInt`
and the rest) are in `Int/Int.sw`, beside `Int.modNatAddMul`, and
Int/Lemmas.sw has the `%` forms for any nonzero divisor, `Int.modModAdd`
and `Int.modAddMul`, through `Int.divModUnique`.

### 7. Comparisons

- Stitchwort's `Int` `%` is Euclidean, never negative for a nonzero
  divisor, as Lean's is (`Int.emod`,
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Integers/>), so
  `(x + t * v) % width` needs no fixing up. Scala's `%` is Java's
  truncating remainder, `-4 % 3 == -1`, and needs `Math.floorMod`
  (<https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Math.html>);
  Haskell needs `mod` (flooring), not `rem`
  (<https://hackage.haskell.org/package/base/docs/Prelude.html>).
- Lean's `List.Nodup` is decidable in core; Stitchwort's `List.Distinct`
  is not (item 2).

### Size and time

Release build, load average around 12:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day14.Proofs` | 2.0 s user (2.7 s) |
| `stitchwort check --no-cache Aoc.Year2024.Day14` | 1.8 s user (2.3 s) |
| `stitchwort test --no-cache Aoc.Year2024.Day14` (37 tests) | 1.9 s user (2.0 s) |
| `stitchwort run Aoc.Year2024.Day14.mainExample` on the example | 0.51 s user |
| `stitchwort run Aoc.Year2024.Day14.main` on 500 generated robots | 4.81 s user |
| `stitchwort check` (whole aoc project, 91 namespaces) | 15.0 s user (15.5 s) |

112 lines of program, 70 of spec, 303 of proofs, 222 of tests.

### Ranked

1. No program arguments (item 2). Fix: `IO.args`.
2. `()` refused where `Unit` is expected in proofs (item 3). Fix: accept
   `()` as `Trivial`, or say "write `Trivial`".
3. `omega` and `rewrite` see std's internals for `Succ x` and `NegSucc`
   arithmetic (item 3). Fix: normalise `Nat.toInt (Succ x)` to `x.toInt
   + 1` and `NegSucc n` to `-(n.toInt) - 1` before abstracting atoms.
4. No `Bool` "no repeats" with its `Prop` (item 2). Fix:
   `List.allDistinct` with `allDistinct xs = True ↔ List.Distinct xs`.
5. `auto` ignores proof fields of records in scope (item 4). Fix: search
   the fields of local records.
6. `Int.modNat` lemmas live in `Mod/Mod.sw`; no `Int %` lemmas for a
   variable divisor (item 6). Fix: move them to `Int/`, add `%` versions.
7. Hypotheses shown fully computed, `Set.insert` as `Quot.lift …` (item
   3). Fix: show hypotheses as refined but not computed.
8. No least-element lemma for `List.find` over `List.range` (item 2). Fix:
   add `findRangeSome` and `findRangeNone` to std.

## Day 15: Warehouse Woes

A warehouse map of walls `#`, boxes `O` and a robot `@`, then the moves
it "will attempt to make (`^` for up, `v` for down, `<` for left, `>` for
right)", over several lines, which "form a single giant sequence". "If
there are any boxes (O) in the way, the robot will also attempt to push
those boxes. However, if this action would cause the robot or a box to
move into a wall (#), nothing moves instead, including the robot." Part
1: "what is the sum of all boxes' GPS coordinates?", a box's being "100
times its distance from the top edge of the map plus its distance from
the left edge". Part 2: "everything except the robot is twice as wide":
`#` becomes `##`, `O` becomes `[]`, `.` becomes `..` and `@` becomes
`@.`, and "boxes can be aligned such that they directly push two other
boxes at once"; the GPS of a wide box is measured to "the closest edge of
the box" (part 2's wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/main/2024/day-15/README.txt>).

**The real input is pending from Matt.** `mdr/aoc-2024` stops at day 10,
so day 15 has no `aoc/inputs/2024/day15.txt`, no `Tests/Input.sw` and no
entry in `crates/cli/tests/aoc_answers.rs` or `crates/rt/tests/machine.rs`;
add those when the input comes.

The examples' answers are checked: 2028 for the small example and 10092
for the larger one in part 1, and 9021 for the larger one in part 2, with
the maps the puzzle draws after the moves (each move of the small
example, the final map of the larger, the widened map, and the small part
2 example's moves). An independent Python script (`/usr/bin/python3 -I`,
sets of positions and a worklist for part 2) agrees on all of them, and
on a generated 50 by 50 warehouse with 20,000 moves (8% walls, 32% boxes,
moves in lines of 1000; not committed): 1887456 and 1919660. Compiler
built from `main` at 4ff1b07f, 28 October 2026.

### The program

```stitchwort
type Position = { row: Int, column: Int }

type Warehouse = { walls: Set Position, boxes: Set Position, robot: Position }

type Document = { warehouse: Warehouse, moves: List Direction }

def tile(): {Parse} Tile := pick [("#", Wall), ("O", Box), ("@", Robot), (".", Floor)]

def move(): {Parse} Direction := pick [("^", Up), ("v", Down), ("<", Left), (">", Right)]

def document(): {Parse} (List (List Tile), List Direction) :=
  let rows := section (() => many1 tile)
  let moves := lines (() => many1 move) |> .concat
  (rows, moves)

def parseDocument (input: Text): {Fail} Document :=
  let (rows, moves) := Parse.all input document
  let robot :=
    match positionsOf rows Robot with
      | [start] => start
      | [] => Fail.fail "expected a robot (@) on the map, found none"
      | _ => Fail.fail "expected one robot (@) on the map, found several"
  let warehouse: Warehouse := { walls = Set.fromList (positionsOf rows Wall), boxes = Set.fromList (positionsOf rows Box), robot }
  { warehouse, moves }

def firstFree (boxes: Set Position) (direction: Direction) (position: Position): (fuel: Nat) → Option Position
  | Zero => None
  | Succ fuel => if boxes.contains position then firstFree boxes direction (position.step direction) fuel else Some position

def Warehouse.move (warehouse: Warehouse) (direction: Direction): Warehouse :=
  let next := warehouse.robot.step direction
  match firstFree warehouse.boxes direction next (warehouse.boxes.size + 1) with
    | Some free =>
      if warehouse.walls.contains free then warehouse
      else { warehouse | boxes = warehouse.boxes.insert free |> .remove next, robot = next }
    | None => warehouse

def solvePart1 (document: Document): Int := document.warehouse.moveAll document.moves |> .gpsSum

def Warehouse.gather (warehouse: Warehouse) (direction: Direction) (group: Set Position): (pending: List Position) → (fuel: Nat) → Option (Set Position)
  | Nil, fuel => Some group
  | Cons cell rest, Zero => None
  | Cons cell rest, Succ fuel =>
    if warehouse.walls.contains cell then None
    else
      let found := warehouse.boxesAt cell |> .filter (box => !group.contains box)
      warehouse.gather direction (found.foldLeft group Set.insert) (found.flatMap (box => frontOf box direction) ++ rest) fuel

def Warehouse.moveWide (warehouse: Warehouse) (direction: Direction): Warehouse :=
  let next := warehouse.robot.step direction
  match warehouse.gather direction Set.empty [next] (2 * warehouse.boxes.size + 1) with
    | Some group =>
      let moved := group.map (box => box.step direction)
      { warehouse | boxes = moved.union (group.foldLeft warehouse.boxes Set.remove), robot = next }
    | None => warehouse

def solvePart2 (document: Document): Int := document.warehouse.widen.moveAllWide document.moves |> .gpsSum
```

`main` is `parseDocument IO.readAll()` and the two prints. Positions are
`Int`s, so a step is always defined and the proofs need no edge cases;
the map's walls keep the robot inside. Part 1 never moves a whole line:
moving its first box to the free position past the last leaves the same
set of boxes, and with no box in front, inserting and removing the free
position changes nothing, so one expression covers both. Part 2's
warehouse uses the same type, a box being where its `[` is: `cellsOf box`
is `[box, box.step Right]`, `boxesAt cell` the boxes covering a cell, and
`frontOf box direction` the cells a moving box moves into other than its
own (one cell for left and right, two for up and down). `gather` is a
worklist over cells to empty: a wall fails the move, and each new box
covering the cell joins the group and adds its front cells. The fuel is
the number of boxes plus one (part 1) and twice that plus one (part 2),
enough since a box joins once and adds at most two cells; running out
moves nothing.

### Proved, for every warehouse and every move

The spec (`Spec/Spec.sw`, 90 lines) is in the puzzle's terms over the
program's `Warehouse` and `Position.step`. `ahead position direction n`
is `n` steps on. `LineOfBoxes warehouse direction length` is "any boxes
in the way": the `length` positions in front of the robot hold boxes and
the one after doesn't. `BoxAfterPush` says there is a box at a position
after the push when a box of the line moved one step to it, or a box not
in the line was already there. `Separate` says nothing overlaps (no box on
a wall, the robot on neither). For part 2, `wideTile` draws a cell as the
puzzle does (`#`, `[`, `]`, `@`, `.`) and `Whole` says every `[` has its
`]` to the right and every `]` its `[`; `WideSeparate` says no box covers
a wall or another box's cells, and neither covers the robot. `MustMove`
is the boxes in every set `Closed` under "the robot walks into it, or a
pushed box walks into it", and `Blocked` is "the robot or a box that must
move would move into a wall".

Proved (`Proofs/`, 893 lines in five files), with one axiom, `Quot.sound`
(`stitchwort axioms`; it comes from std's `Map`, a quotient):

- Part 1, `Part1.sw`: `moveWalls` (a move never moves a wall),
  `moveCount` (never changes the number of boxes: inserting the free
  position adds one, removing the next position takes one away),
  `moveSeparate` (with nothing overlapping before, nothing overlaps after:
  the robot never ends on a wall or a box), and the literal rule:
  `lineExists` (every move meets a line of boxes, maybe of none),
  `pushBlocked` (a wall past the line: nothing moves) and `pushMoves`
  (else the robot steps forward, and a position holds a box exactly when
  `BoxAfterPush` says). `part1Moves` (`Proofs.sw`) carries the first three
  through every list of moves.
- Part 2, `Part2.sw`: `gatherOk`, `gather`'s invariant: the group it
  returns holds only boxes, every cell they move into is free (not a wall,
  and every box covering it is in the group), and so is the robot's next
  cell. From it, `blockedMovesNothing` (with nothing overlapping, a
  `Blocked` move leaves the warehouse as it was), `moveWideSeparate`
  (nothing overlaps after a move if nothing did before), `wholeOfSeparate`
  (with nothing overlapping, every box is whole), and `moveAllWideWalls`.
  `Widen.sw`: `widenSeparate` (widening a warehouse where nothing overlaps
  gives a wide one where nothing overlaps) and `part2Whole`: from such a
  warehouse, after every move the robot is on no wall or box and every
  box is whole.

The part 1 proofs needed one counting fact: a line of boxes is no longer
than the boxes there are (`lineAtMostBoxes`, from `countAtMostSize`, a
pigeonhole for sets: `count` different positions in a set make its size
at least `count`). That makes `firstFree`'s fuel enough, so the program's
trick is the literal push for every warehouse, not only small ones.
Breaking the program (not removing the next position's box in part 1;
not adding a gathered box's front cells in part 2) makes the proofs fail.

Not proved:

- That part 2 keeps the number of boxes. The new set is the union of the
  group moved one step and the boxes not in it. The facts are proved
  (the moved boxes are distinct, since a step is injective, and none lands
  on a box that stayed, from `gatherOk`), but std has no size lemmas for
  `Set.union`, `Set.map` or removing a subset, and building them from
  `Set.toList` lengths and `List.Perm` is about 150 lines (item 2).
  Fixed: proved with the new std size lemmas: `moveWideCount` (with
  nothing overlapping, a move keeps the number of boxes),
  `moveAllWideCount`, and `part2Count` (widening a warehouse where nothing
  overlaps, then every move, keeps its number of boxes;
  `Set.sizeMapInjective` covers the widening).
- That an unblocked part 2 move moves exactly the `MustMove` boxes.
  `gatherOk` gives one direction (every box that must move is gathered);
  the other needs a second invariant (every gathered box is reached from
  the robot through covered front cells) and that the fuel suffices, a
  pigeonhole over the cells `gather` visits. The tests check the trees of
  boxes against the puzzle's drawings instead.
- That the parsed warehouse is `Separate`: parsing isn't proved, as on
  other days. Each position gets one tile, so it holds by construction.

### 1. Std.Parse: none

`section (() => many1 tile)` then `lines (() => many1 move) |> .concat`
read both examples first time, with `pick` for the tiles and moves. The
messages are good: a bad tile is `line 1, column 3: expected '#' or 'O'
or '@' or '.' or a line break or a blank line, got 'x'`, and a missing
move section `line 2, column 1: expected '#' or 'O' or '@' or '.' or a
blank line, got the end of the input`. The one check outside the grammar,
exactly one robot, is a `Fail` after the parse, so its message has no
line; a robot count isn't a property of one line, so that is right.

Days 6, 12 and 15 all number a grid's cells by hand
(`rows.withIndex |> .flatMap (... tiles.withIndex ...)`). What I did:
`positionsOf rows wanted` in the program, 8 lines.

Fixed: std has `List.gridCells` (`std/List/Grid.sw`), each cell with its
`(row, column)`, and `List.memGridCells`; `positionsOf` is a filter and a
map over it, and days 6 and 12 use it too.

### 2. Missing std

- No size lemmas for sets beyond `Map.sizeInsert` and `Map.sizeRemove`:
  nothing for `Set.union` of disjoint sets, `Set.map` with an injective
  function, removing a subset, or "a set holding `n` different elements
  has at least `n`". Mathlib has `Finset.card_disjUnion` (`(s.disjUnion t
  h).card = s.card + t.card`), `Finset.card_image_of_injective` (`(image f
  s).card = s.card`) and `Finset.card_erase_of_mem`
  (<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html>).
  `Lemmas.sw` proves the last one I needed (`countAtMostSize`, 14 lines);
  part 2's count is unproved for want of the others.
- No membership lemmas for `Set.map` or `Set.foldLeft`. `Lemmas.sw` has
  `setFoldLeftIsList` (a set's fold is its list's fold), `containsMap`,
  `containsFoldRemove` and `containsFoldInsertMap`, 70 lines.
- No `Set.removeAll` (`Map.removeAll` filters the whole map). The program
  folds `Set.remove` over the group.
- `(cellsOf box).contains cell` is "`List` has no field or function
  `contains`"; `cell ∉ cellsOf box` works, decided. `Text.concat` doesn't
  exist ("no function `concat` in `Text`"); the tests' map drawing builds
  `Char`s and uses `Text.fromList`.

No std file was changed.

Fixed: `Set/Spec.sw` has the size lemmas `Set.sizeUnionDisjoint`,
`Set.sizeMapInjective`, `Set.sizeDifferenceSubset` (with `Set.sizeSubset`),
`Set.sizeInsertNew`, `Set.sizeRemovePresent`, `Set.sizePositive` and the
pigeonhole `Set.countAtMostSize`, all through a new `Set.induction`; and
the membership lemmas `Set.foldLeftToList`, `Set.memToList`,
`Set.containsMap`, `Set.mapInsert`, `Set.containsFoldRemove`,
`Set.containsFoldInsertMap` and `Set.containsInsertElim`. Day 15's local
copies are gone (`Lemmas.sw` keeps only facts about positions), and
`Bool.falseOfNotTrue` replaces its `falseOf`. `Set.difference` is the
`removeAll`, now fast when the set removed is small (item 5), so the
program uses it again.

### 3. Confusing errors

- Goals are shown computed down to internals, which for sets is
  unreadable. In `gatherOk`, `group.contains box = True` shows as
  `Map.contains.%match1 () (Map.get group.items box) = True`, a set after
  an insert as a `Quot.lift (rawMap => Quot.mk { tree =
  Map.Tree.insertWith ...` term of 600 characters, and `frontOf` as its
  whole decision procedure. And a binder that shadows a pattern variable
  isn't renamed: my statement's `(cell: Position) → cell ∈ pending → ...`,
  with `pending` matched as `Cons cell rest`, showed as

  ```text
  ((cell: Position) → cell = cell ∨ List.Any (y => y = cell) rest → ...
  ```

  where the first `cell` is the list's head and the second the bound one.
  What I did: wrote the statements
  of `GatherInvariant` and `Clear` as definitions, and worked from them
  rather than the goal.
- `match c: e` replaces `e` in hypotheses too, which is useful, but the
  messages don't say so. `rewrite c at found` after it says

  ```text
  [E-REWRITE-NOTHING] Error: `rewrite` found no `Set.contains boxes start` in the type of `found`
  ```

  with `found`: `Some start = Some free`, already rewritten. A lemma bound
  with `let` before the `match` is refined too, so its premise
  `boxes.contains position = True` became `True = True`, and passing the
  match's own equation failed: "expected `True = True`, but this has type
  `Set.contains warehouse.boxes position = True`". The note explains the
  opposite case (a term written inside the branch isn't refined). What I
  did: used `found` as it was and passed `rfl`.

  Fixed: the `rewrite` error labels the `match` ("this `match` replaced
  `isBig n` with `False`") and says the hypothesis is already refined; the
  mismatch for a refined lemma labels it too, says the `match`'s own
  equation isn't refined, and that `rfl` proves the premise when both
  sides are the same. The lemma doesn't accept the equation: in the branch
  `e` and `True` aren't the same by computing, only by the equation, as in
  Lean's `match h : e with`.
- A `_` was solved to make a lemma vacuous: `positionEq _ position rfl
  (omega)` for `(position.step Right).step Left = position` gave "expected
  `{ position | column = position.column + 1 - 1 } = position`, but this
  has type `position = position`". What I did: wrote the argument out.
- The first check printed each of its two errors twice.

  Not a bug: the command was `stitchwort check … | head -40 && stitchwort
  run …`, and both commands printed the two errors.

### 4. Inference

- `let warehouse := { walls = ..., boxes = ..., robot }` is "[E-CANNOT-INFER]
  Error: can't tell which record type this literal is ... nothing here
  says what type it should have", though `Warehouse` is the only record
  with those fields and the next line puts it in a `Document`. What I
  did: `let warehouse: Warehouse := ...`.
- `falseOf _ (...)` with `_` for `position == warehouse.robot` failed:
  "expected `Decidable.toBool (Aoc.Year2024.Day15.Position.%decEq position
  warehouse.robot) = False`, but this has type `Decidable.toBool
  (DecEq.%decide … position …) = False`", the same `==` reached through
  the instance and directly. What I did: wrote the argument out.

  Fixed: solving the `_` outside the lambda pruned `DecEq.sound`'s
  dictionary to a new unknown with no obligation, so the instance was never
  looked for. Pruned dictionaries are now looked for; `wholeOfSeparate`
  writes `Bool.falseOfNotTrue _`.

### 5. Performance

Part 2 first moved the group with `boxes.difference group |> .union
moved`. On the generated warehouse (753 boxes, 20,000 moves) part 2 took
19.8 s of CPU; with `moved.union (group.foldLeft boxes Set.remove)` it
takes 0.97 s. `Map.Raw.difference a b` walks the whole of `a` unless `a`
is the small one (`if Map.Raw.isSmall a b then ... else Map.Raw.merge`),
and `union` folds only when its first argument is small, so a few boxes
taken from hundreds cost hundreds of steps each move. Haskell's
`Data.Set.difference` and `union` are both "O(m log(n/m + 1)), 0 < m ≤ n",
m being the smaller set's size
(<https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Set.html>).
What I did: the fold and the argument order above; part 1 needed nothing.

Fixed: `Map.Raw.unionWith` and `Map.Raw.difference` also work key by key
when the second map is the much smaller one (inserting or removing its
entries in the first), so both are O(n log m) for a small side n either
way. The program is back to `warehouse.boxes.difference group |> .union
moved`. On a regenerated 50 by 50 warehouse with 20,000 moves (same
recipe; 753 boxes), the whole run took 19.95 s of CPU with that form
before the change and 1.12 s after (the fold form: 1.25 s). A 1,000,000-key
`Set Nat` minus a 10-key set, 20 times, went from about 13 s to too little
to measure beside the 9 s it takes to build the big set.

### 6. Proofs

Most of the proofs went through first time, and three tools carried
them: `omega` over a `progress` function (how far along a direction a
position is) proved that steps along a line never revisit a position;
`cases` proved `moveWalls` and `moveWideWalls` alone; and `match c: e`
refining the hypotheses saved many rewrites. The friction:

- `i + 1` doesn't compute to `Succ i`: `+` recurses on its first
  argument (core's `Nat.addSucc` is a theorem). The spec says `ahead
  robot direction (i + 1)`, and every use needed `Nat.addOne` or
  `aheadAddOne` rewritten in by hand, with errors such as "`rewrite`
  found no `Succ i` in the goal" when the goal had computed past it, and
  "expected `(match …) () (Map.get warehouse.boxes.items (Position.step
  (ahead warehouse.robot direction i) direction)) = True`, but this has
  type `Set.contains warehouse.boxes (ahead warehouse.robot direction (i +
  1)) = True`". In Lean `Nat.add` recurses on the second argument (`| a,
  Nat.succ b => Nat.succ (Nat.add a b)`,
  <https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean>),
  so `n + 1` is `Nat.succ n` by computation. What I did: `aheadAddOne`
  and `rewrite ... at` on hypotheses instead of goals.
- Membership in a literal list is `List.Any (y => y = x)`, so `x ∈ [a,
  b]` is `a = x ∨ (b = x ∨ Void)`, the other way round from what I wrote
  each time; several `Eq.sym`s.
- An `if` on a `Bool` inside a `let`-ascribed proof isn't decided by an
  enclosing `match` on that `Bool`: `rfl` failed with "`if
  Decidable.toBool (Aoc.Year2024.Day15.Position.%decEq ...) then WideRobot
  else BoxRight` and `BoxRight` aren't equal" until the match's equation
  was added to the `rewrite`.
- Constructors of a type aren't known to differ: refuting `WideRobot =
  BoxLeft` needed a `tileCode` function, `Eq.cong` and `omega`
  (`tilesDiffer`).

  Fixed: `cases` already closed such a case (a hypothesis equating two
  different constructors), and each of the eight is now `cases`;
  `tileCode` and `tilesDiffer` are gone. `()` now matches an equation of
  two different constructors too (`| ()` for `Robot = BoxLeft -> Void`),
  where it said the equation "has values".

### 7. Comparisons

- Lean's `Nat.add` recursing on its second argument: item 6.
- Mathlib's `Finset` cardinality lemmas: item 2.
- Haskell's `Data.Set` complexities: item 5.

### Size and time

Release build, on a machine with a load average around 30 to 40 (wall
time, then CPU):

| command | wall | CPU |
| --- | --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day15.Proofs` | 8.1 s | 2.8 s |
| `stitchwort check --no-cache Aoc.Year2024.Day15` | 4.8 s | 1.9 s |
| `stitchwort test --no-cache Aoc.Year2024.Day15` (34 tests) | 7.8 s | 3.4 s |
| `stitchwort run Aoc.Year2024.Day15.main` on the larger example | 1.4 s | 0.65 s |
| the same on the generated 50 by 50 warehouse, 20,000 moves | 2.8 s | 1.4 s |
| the same, part 2 with `difference` and `union` (before) | 21.7 s | 19.9 s |
| `stitchwort check` (whole project) | 45.5 s | 23.5 s |

157 lines of program, 90 of spec, 893 of proofs, 232 of tests. Python
takes 0.19 s of CPU on the generated warehouse.

### Ranked

1. The real input is pending: Matt's repository has no day 15. Fix: add
   his input, its tests and its two answer entries when he has it.
2. `Set.difference` and `Set.union` are linear in the larger set when the
   other is small: part 2 was 20 times slower (item 5). Fix: in
   `Map.Raw.difference`, fold `remove` over a small second argument, and
   let `union` fold whichever side is small.
3. Part 2's box count and the exactness of its push are unproved, for
   want of set size lemmas (Proved, item 2). Fix: add size lemmas for
   disjoint union, injective `map`, removing a subset, and the pigeonhole
   (`countAtMostSize`) to `Set/Spec.sw`.
4. `n + 1` doesn't compute to `Succ n` (item 6). Fix: define `+` by
   recursion on its second argument, as Lean does.
5. Goals are shown computed into internals, and a bound name captured a
   free one in the display (item 3). Fix: show goals with definitions such
   as `Set.contains` folded back, and rename clashing binders.
6. `match c: e` refines hypotheses and `let`-bound lemmas without saying
   so, and `rewrite` then reports finding nothing (item 3). Fix: when a
   rule's left side is absent because a `match` replaced it, say that.
7. A record literal's type isn't inferred from its fields or its later
   use (item 4). Fix: infer it when one record type has exactly those
   fields.
8. Unification doesn't see `==` through the instance and directly as the
   same, and a `_` can be solved to a trivial instance (items 3 and 4).
   Fix: unfold instance projections when unifying.
9. Constructors aren't known to differ (item 6). Fix: let `cases`, or a
   `noConfusion`-style lemma per type, close `C1 = C2` hypotheses.
10. Grids are numbered by hand on three days, and `Set.map`/`foldLeft`
    have no membership lemmas (items 1 and 2). Fix: a std function for a
    grid's cells with their positions, and the membership lemmas in
    `Set/Spec.sw`.

## Day 16: Reindeer Maze

A maze of walls (`#`) and open tiles. "The Reindeer start on the Start
Tile (marked S) facing East and need to reach the End Tile (marked E).
They can move forward one tile at a time (increasing their score by 1
point), but never into a wall (#). They can also rotate clockwise or
counterclockwise 90 degrees at a time (increasing their score by 1000
points)." Part 1: "What is the lowest score a Reindeer could possibly
get?" Part 2: "you'll need to determine which tiles are part of any best
path through the maze, including the S and E tiles ... How many tiles are
part of at least one of the best paths through the maze?" (part 2's
wording from the public copy at
<https://gitea.baerentsen.space/FrederikBaerentsen/AdventOfCode/src/branch/master/2024/16/16.md>).

**The real input is pending from Matt**: his repository
(<https://github.com/mdr/aoc-2024>) stops at day 10, so there is no
`inputs/2024/day16.txt`, no `Tests/Input.sw`, and the day isn't registered
in `aoc_answers.rs` or `machine.rs` yet. `examples/2024/day16.txt` is the
second example. The tests are the puzzle's two examples (7036 and 45;
11048 and 64) and edge cases, all cross-checked with an independent Python
script (`/usr/bin/python3 -I`: `heapq` Dijkstra over (row, column,
direction), part 2 by walking back along predecessor edges whose costs add
up, not by a second search). For performance, a second script generated a
141 by 141 maze (a recursive-backtracker maze with 1500 random walls
knocked out, so there are many paths; not committed); the program and
Python agree on it (116428 and 444). This is the first shortest-path day.
Compiler built from `main` at f06e8931, 28 October 2026.

### The program

```stitchwort
def tile(): {Parse} Tile :=
  Parse.pick [("#", Wall), (".", Floor), ("S", Start), ("E", End)]

def parseMaze (input: Text): {Fail} Maze :=
  let rows := Parse.all input (() => Parse.grid tile)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .forEach (((row, tiles)) =>
    Fail.ensure (tiles.length == width) "line ${row + 1}: expected ${width} tiles, as on the first line, got ${tiles.length}")
  let tiles :=
    rows.withIndex
      |> .flatMap (((row, line)) => line.withIndex |> .map (((column, kind)) => (({ row, column }: Position), kind)))
  {
    openTiles = tiles.filter (entry => entry.snd != Wall) |> .map (entry => entry.fst) |> Set.fromList,
    start = onlyTile tiles Start "S",
    end = onlyTile tiles End "E"
  }

type Graph (s: Type) = {
  edges: s → List (s, Nat),
  within: s → Bool,
  states: List s,
  listed: (state: s) → within state = True → state ∈ states
}

def Graph.searchFrom [auto ord: Ord s] (graph: Graph s) (queue: Set (Nat, s)) (settled: Map s Nat): (popped: Option (Nat, s)) →
    queue.min = popped → Map s Nat
    decreasing (graph.unsettled settled, queue.size)
  | None, found => settled
  | Some (cost, state), found =>
    let rest := queue.remove (cost, state)
    if fresh: settled.contains state = False then
      if within: graph.within state = True then
        let pushed := pushEdges cost (graph.edges state) rest
        Graph.searchFrom graph pushed (settled.insert state cost) pushed.min rfl
          [decreasing := Nat.LexLess.First (unsettledInsert graph settled state cost (graph.listed state within) fresh)]
      else Graph.searchFrom graph rest settled rest.min rfl [decreasing := Nat.LexLess.Second rfl (sizeRemoveMin queue (cost, state) found)]
    else Graph.searchFrom graph rest settled rest.min rfl [decreasing := Nat.LexLess.Second rfl (sizeRemoveMin queue (cost, state) found)]

def Maze.fromStart (maze: Maze): Map Reindeer Nat := (maze.graph False).distances [(maze.startReindeer, 0)]

def Maze.toEnd (maze: Maze): Map Reindeer Nat := (maze.graph True).distances (maze.endReindeer |> .map (reindeer => (reindeer, 0)))

def Maze.lowestScore (maze: Maze) (fromStart: Map Reindeer Nat): Option Nat := maze.endReindeer.filterMap fromStart.get |> .minimum

def tilesScoring (fromStart: Map Reindeer Nat) (toEnd: Map Reindeer Nat) (best: Nat): Set Position :=
  fromStart.toList
    |> .filter (entry => toEnd.get entry.fst |> .map (rest => entry.snd + rest == best) |> .getOrElse False)
    |> .map (entry => entry.fst.position)
    |> Set.fromList

def solvePart1 (maze: Maze): Nat := maze.lowestScore maze.fromStart |> .getOrElse 0

def solvePart2 (maze: Maze): Nat := maze.bestTiles.size
```

The domain model is the set of open tiles (S, E and `.`), the start and
the end. A state is a `Reindeer`: a position and the direction it faces.
`Maze.after` lists the moves out of a state with their costs (forward
onto an open tile for 1, each quarter turn for 1000); `Maze.before` lists
the moves into one, the forward move undone by a step the opposite way.

The search is Dijkstra's algorithm over any `Graph`, written once and
used twice: forward from S, and backward from the four ways of standing on
E. The priority queue is a `Set (Nat, s)` of (cost, state) pairs: `Set.min`
is the next pair to look at, since pairs order by cost first. A popped
state already settled is dropped (lazy deletion, no decrease-key). Part 1
is the least forward score over the four ways of standing on E. Part 2
counts the tiles where, standing some way, the forward score and the
backward score add up to part 1's answer.

The search terminates without fuel: `decreasing (graph.unsettled settled,
queue.size)`, lexicographic. Settling a state shrinks the number of states
not yet settled; dropping a popped pair shrinks the queue. The first needs
the graph's states to be finite, so `Graph` carries a list of its states
and a quick test for them, with a proof field tying the two; the search
checks `within` at run time, a check only the termination proof needs
(the correctness proof shows it never fails). `queue.min` is passed in
with its equation (`popped`, `found`) rather than matched inside, so
proofs can step through the search (item 3). The termination lemmas, 73
lines, are in the program file.

### Proved, for every maze whose S and E are open tiles

The spec (`Spec/Spec.sw`) is in the puzzle's words over the program's
`isOpen`, `step` and quarter turns: a `Move` is `Forward`, `Clockwise` or
`Counterclockwise` with its points; `move` is `None` into a wall; `follow`
lists how the reindeer stands before each move and after the last;
`score` is the sum of the points. `IsPath maze moves standings` is moves
from S facing east, never into a wall, ending on E. `IsLowestScore maze
best`: some path scores `best` and none scores less. `OnBestPath maze best
tile`: some path scoring `best` stands on the tile. `CountsBestTiles maze
best count`: a set of exactly those tiles has `count` members.

Proved (`Proofs/`, 1035 lines in 6 files):

- `distancesCorrect` (Search.sw), for any graph, any sources and any
  property `reach` that holds at each source and along each edge: every
  state the search settles is `reach`ed for its cost (soundness), each
  source is settled for no more than its starting cost, and each edge out
  of a settled state leads to a state settled for no more than the two
  costs together (closure, from which optimality follows by induction on
  any path). The invariant (`SearchState`) has five parts: queued pairs
  and settled states are reached; each source and each edge out of a
  settled state is pending (queued, or its end settled for no more);
  nothing settled costs more than anything queued; and queued states are
  within the graph. `skipKeeps` and `settleKeeps` show each step keeps it,
  the second through `minLeast`: the least pair costs no more than any
  other (from `Map.toListSorted`).
- Moves.sw: the forward graph's edges are exactly the puzzle's moves with
  their points (`afterSound`, `afterComplete`), and the backward graph's
  are the moves into a state from an open tile (`beforeSound`,
  `beforeComplete`).
- `part1Correct` (Part1.sw): with some path from S to E, `IsLowestScore
  maze (solvePart1 maze)`. Soundness: the least is the score of moves the
  search reached, which `follow` turns into a path. Optimality
  (`boundAlong`): along any moves the search's bound grows by at most
  their score.
- `part2Correct` (Part2.sw): with lowest score `best`, `CountsBestTiles
  maze best (solvePart2 maze)`. A counted tile has a path through it,
  joined from moves to it and moves from it (`joinedPath`); a tile on a
  best path splits that path where the reindeer stands there
  (`followSplits`), its forward and backward scores are at most the two
  parts' (`boundAlong`, `boundToEnd`) and at least `best` together, so
  they add up to it.

Breaking the program (a turn costing 999 in `turns`, queued pairs costing
one more in `pushEdges`, or `>=` for `==` in `tilesScoring`) makes the
proofs fail. Not proved: parsing (as on other days), and that S and E are
open, which `parseMaze` ensures since neither is a wall; the theorems take
both as hypotheses. With no path to E the spec has no lowest score, so
part 1 assumes one; the program answers 0 then (tested).

### 1. Std.Parse: none

`Parse.grid tile` with a `Parse.pick` of the four tiles read the maze
first time, and the message is good: `line 2, column 3: expected '#' or
'.' or 'S' or 'E' or the end of the line, got 'x'`. As on days 8, 10 and
12, the row-length check and turning rows into positions are by hand;
finding the one S and the one E is a helper (`onlyTile`). Fix: a
grid-to-map builder (day 12's `Map.byGridPosition`).

### 2. Missing std

- **A priority queue.** `Set (Nat, s)` with `Set.min` and `Set.remove`
  worked, as `Data.Set` does in Haskell, whose `minView` "retrieves the
  minimal key of the set, and the set stripped of that element"
  (<https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Set.html>).
  Std has no `Set.popMin` (one call for `min` and `remove`), no
  decrease-key queue such as Haskell's `psqueues`, whose stated uses
  include "Pathfinding algorithms, such as Dijkstra's and A*"
  (<https://hackage.haskell.org/package/psqueues>), and no heap: Scala has
  `mutable.PriorityQueue`
  (<https://www.scala-lang.org/api/current/scala/collection/mutable/PriorityQueue.html>),
  Rust's `BinaryHeap` documentation has a Dijkstra example
  (<https://doc.rust-lang.org/std/collections/binary_heap/index.html>),
  and Lean's Batteries has a max-heap `BinaryHeap`
  (<https://github.com/leanprover-community/batteries/blob/main/Batteries/Data/BinaryHeap/Basic.lean>).
- **Graph search.** No shortest paths, nor breadth-first search (day 12's
  fill was by hand too). `Graph`, `searchFrom` and `distancesCorrect` here
  are generic and could move to std as they are, with the proof: callers
  supply only their `reach` and its two closure properties.
- **Lemmas about `Set.min`**: that it is in the set (`containsMin`), no
  greater than any member (`minLeast`), `None` only for an empty set
  (`missingOfMinNone`), and that removing it shrinks the set
  (`sizeRemoveMin`). Std's `Set.minToList` and `Map.toListSorted` were
  enough to prove them, in about 60 lines.
- **`Map` membership after `insert`** (`containsInsertSame`,
  `containsInsertKeeps`, `getInsertCases`, `getInsertKeeps`,
  `getOfContains`): std has `Set.containsInsertMono` but not the `Map`
  forms.
- **`List.minimum` lemmas** (`minimumLeast`, `minimumMember`,
  `minimumSome`; day 13 wanted them too), **`memMapElim`** (a member of a
  mapped list is an image) and **`anyMember`** (`List.Any` gives a
  member). `countLe` and `countFewer` are copied from day 12's program for
  the termination measure.

None added to std (the `List` lemma files are another lane's). Fix: add
`Set.popMin` and the `Set.min` lemmas, the `Map` insert lemmas, the
`List.minimum` lemmas and `memMapElim`, and move the generic search.

Fixed: std has `Set.popMin` and `Map.popMin`, the least key (entry) and
the rest in one walk down the left spine, as `Data.Set.minView`, with
`Set.popMinSpec` (`popMin` is `min` and `remove` together),
`Set.popMinSome`, `Set.popMinNone`, `Set.sizePopMin`, `Set.containsMin`
and `Map.popMinSpec`. The search pops with it: `searchFrom` takes
`queue.popMin` and its equation, and the program's `containsMin` and
`sizeRemoveMin` are gone.

### 3. Confusing errors

- A dependent `match` on `queue.min` inside the search couldn't be stepped
  through in a proof. The first program matched `match popped: queue.min
  with` and used `popped` in its `decreasing` proofs; a proof that unfolds
  it and matches the same way gave

  ```text
  [E-MATCH-MOTIVE] Error: generalising this `match`'s scrutinee makes its type ill-formed
    Note 1: a top-level helper with a written signature can always do what this `match` would: define one and call it
    Note 2: checking the type it would have: `rfl` can't prove this
  ```

  The note is right, and is what I did: `searchFrom` takes the popped pair
  and its equation as arguments, matches on the argument, and each
  recursive call passes `pushed.min rfl`. Then each step was a three-line
  lemma (`searchEmpty`, `searchSkip`, `searchSettle`). Day 12 met the
  same wall with a `Bool`. Fix: generalise the equation with the
  scrutinee, or generate per-arm equations as Lean does.
- A `match` refines the goal and hypotheses, but not terms that appear
  later, so an equation can come out half refined. In `followSplits`,
  after `rewrite <- here` in a branch, the goal was

  ```text
  expected `(match …) maze rest (move maze reindeer way) = final maze next rest`, but this has type `final maze next rest = (match …) maze rest (move maze reindeer way)`
  ```

  The right-hand side, from the theorem's statement, had been refined;
  the left, put there by the `rewrite`, had not. I bridged with a lemma,
  `finalCons`, in whichever direction the error showed. Fix: refine terms
  produced inside the branch too, or say which side is unrefined.

  Not fixed: the unrefined side isn't the `rewrite`'s. `final maze middle
  after` has `after` bound by the `Exists` until `Witness (Cons way rest)`
  fills it in; only then does it compute to a `match` on `move maze
  reindeer way`, long after the `match` replaced that expression in the
  goal. So neither the `match` nor the `rewrite` ever sees it; refining it
  would mean comparing terms up to the arm's equation (`moved`) everywhere
  in the arm, which the kernel's comparison doesn't do. `rewrite moved in
  rfl` in place of `finalCons` works, since `rewrite` searches what terms
  compute to (`examples/accept/match-equation-rewrites-later-terms.sw`;
  `examples/reject/match-refines-goal-once.sw` is the failure, with no
  `rewrite` in it).
- Constructors aren't imported by name: `import Aoc.Year2024.Day16.Spec
  (Clockwise, Counterclockwise, Forward, Move, …)` gave ``[E-IMPORT-UNKNOWN]
  Error: `Aoc.Year2024.Day16.Spec` has no `Clockwise` `` for each;
  importing `Move` brings them. Fix: a note saying a constructor comes
  with its type.

  Fixed: the error has the note ``Note: `Clockwise` is a constructor of
  `Move`, and constructors come with their type: import `Move` instead, as
  in `import Turns (Move)` `` (`examples/projects/reject/import-constructor`).
- A type written on a `let` is computed before `rewrite` sees it:
  `let member: List.Mem x (List.map (Cons (key, unit) rest) Pair.fst) :=
  rewrite <- entries in …` gave ``[E-REWRITE-NOTHING] Error: `rewrite`
  found no `Cons (key, unit) rest` in the goal`` with ``goal: `key =
  (other, otherState) ∨ List.Any …` ``. What I did: `rewrite entries at
  member` on the hypothesis instead. Fix: rewrite the type as written.
- Clear ones: ``[E-STD-NAMESPACE] Error: `Map` is a namespace of the
  standard library, which a program can't add to`` (I named the lemmas
  without the prefix), and ``[E-UNIVERSE] Error: `if` can't choose between
  proofs yet``, whose note says to `match` on the `Bool` instead.

### 4. Inference

- A lambda before the argument that fixes its type:
  `memMapElim (entry => entry.fst.position) tile (fromStart.toList.filter
  passes) listed` gave ``can't tell what `entry` is, so can't look up
  `.fst` ``. Annotated `(entry: (Reindeer, Nat))`, three times.

  Fixed: a lambda whose parameter type isn't known yet, and that fails
  where it is, is checked after the later arguments also when a later
  parameter's type mentions it (here `y ∈ xs.map f`): that type holds a
  placeholder for the lambda, which `listed`'s type solves. The three
  annotations are gone (`examples/accept/lambda-postponed-dependent-argument.sw`).
- `_` for a predicate isn't solved from a hypothesis's type: `anyMember _
  maze.endReindeer (List.memFilterMapElim …)` gave ``expected `… ∨ … ∨
  …`, but this has type `List.Any (x => Map.get (Maze.fromStart maze) x =
  Some best) (Maze.endReindeer maze)` ``: the expected `List.Any ?p` over
  four literals was unfolded into a disjunction before `?p` was solved
  (day 13's item 3). Wrote the predicate out.
- `ring` is a keyword again (renamed a test's maze `loop`).

### 5. Performance

On the generated 141 by 141 maze (10141 open tiles, 40564 states)
`stitchwort run` takes 10.7 s user; Python takes 0.07 s. Loading is 0.6
s, parsing 0.35 s, and one search about 2.2 s (throwaway mains, not
committed). Part 1 runs one search; part 2 runs the search from S again
and the one back from E, then filters the 40564 settled states, since
each part takes the parsed maze alone. Each pop is a `Set.min`, a
`Set.remove` and a `Map.contains`; each settle three `Set.insert`s and a
`Map.insert`, all balanced-tree operations on records compared field by
field. Not pursued further. Fix: a `Set.popMin` (one walk instead of
two), and let `main` share the forward search between the parts.

Fixed: both. `main` searches forward once and passes the scores to
`part1From` and `part2From` (`solvePart1` and `solvePart2`, which the
proofs are about, are those with `maze.fromStart`). On a regenerated 141
by 141 maze (the same recipe with another seed; 45284 and 329, as Python
says), load average about 10: 13.5 s user before, 10.7 s with `popMin`,
6.3 s with the search shared too.

### 6. Proofs

Proving Dijkstra correct was smaller than feared: Search.sw is 213 lines
and its invariant checked almost first time. What made it work:

- Proving it once, generically, for any `reach` closed under the sources
  and the edges. Soundness then needs nothing about the maze but its two
  closure properties, and optimality is an induction on any path using
  only the closure the search returns. The same proof serves the search
  back from E. Isabelle's AFP has a verified Dijkstra (Nordhoff and
  Lammich, 2012), built on a refinement framework
  (<https://www.isa-afp.org/entries/Dijkstra_Shortest_Path.html>); here
  the invariant is proved directly about the program.
- Day 12's lexicographic measure, `(unsettled, queue size)`. The
  correctness proof recurses with the program's own measure and the same
  `decreasing` proofs. Lean's `termination_by` is the same idea
  (<https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#well-founded-recursion>).
  What's awkward is finiteness: the measure needs a list of every state,
  so `Graph` carries one with a proof field, and the program checks
  `within` at run time only so the measure can drop. A std notion of a
  finite universe, or a measure on `Set` size bounded by a universe
  `Set`, would remove both.
- The std lemmas that would have made it easier: the `Set.min` lemmas
  (item 2), the only reasoning about the queue's order; the pair-order
  fact that `Ordering.andThen first second = Less` means `first` isn't
  `Greater` (`notGreaterOfThen`); and a `Set.popMin` with a lemma that
  its rest holds exactly the other members, which would replace
  `containsOfRemove` and `containsRemoveKeeps`.
- No record eta (day 5): every lemma about a `Reindeer` matches `{
  position, facing }` first so `{ reindeer | position = … }` computes.
- `rewrite … at h` on a hypothesis, then `match`, was the reliable way to
  use `Map.toList` equations (item 3).

### Size and time

Release build, load average around 40:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day16.Proofs` | 2.9 s user (3.5 s) |
| `stitchwort check --no-cache Aoc.Year2024.Day16` | 1.6 s user (1.7 s) |
| `stitchwort test --no-cache Aoc.Year2024.Day16` (24 tests) | 3.3 s user (4.7 s) |
| `stitchwort test Aoc.Year2024.Day16` (warm) | 0.8 s user (1.0 s) |
| `stitchwort run Aoc.Year2024.Day16.main` on the second example | 0.71 s user |
| `stitchwort run Aoc.Year2024.Day16.main` on a generated 141 by 141 maze | 10.7 s user |

289 lines of program (73 of them termination lemmas), 69 of spec, 1035 of
proofs, 134 of tests.

### Ranked

1. The real input is pending: Matt's repository has no day 16. Fix: add
   his input, its tests and its two answer entries when he has it.
2. No priority queue or graph search in std (item 2). Fix: add
   `Set.popMin`, and move this day's generic `Graph` search and its proof
   to std.
3. A dependent `match` on `queue.min` can't be stepped through in a proof
   (item 3). Fix: generalise the equation with the scrutinee, or generate
   per-arm equations.
4. 10.7 s on a 141 by 141 maze against Python's 0.07 s, with the forward
   search run twice (item 5). Fix: `Set.popMin`, and share the search
   between the parts.
5. Half-refined equations inside a `match` branch (item 3). Fix: refine
   terms produced in the branch too.
6. Missing `Set.min`, `Map` insert and `List.minimum` lemmas (item 2).
   Fix: add them to std's `Set`, `Map` and `List` files.
7. Termination needs a list of every state and a run-time `within` check
   (item 6). Fix: a std finite-universe measure.
8. Lambdas before the argument fixing their type, and `_` predicates
   unsolved against a literal list (item 4). Fix: elaborate lambdas after
   the other arguments; don't unfold `List.Any` while solving.
9. Constructor imports say only "has no `Clockwise`" (item 3). Fix: note
   that constructors come with their type.

## Day 17: Chronospatial Computer

"A 3-bit computer: its program is a list of 3-bit numbers (0 through 7)",
with "three registers named A, B, and C" that "can hold any integer", and
eight instructions, each an opcode and "the 3-bit number after it" as its
operand, read as a literal or a combo operand (0 to 3 themselves, 4 to 6
the registers, 7 "reserved and will not appear in valid programs"). "If the
computer tries to read an opcode past the end of the program, it instead
halts." Part 1: run the program; "what do you get if you use commas to join
the values it output into a single string?" Part 2: the program "is
supposed to output another copy of the program", so "what is the lowest
positive initial value for register A that causes the program to output a
copy of itself?" (part 1 from <https://adventofcode.com/2024/day/17>; part
2's wording from the public copy at
<https://tgragnato.it/2024/12/17/Chronospatial-Computer.html>).

**The real input is pending from Matt.** `mdr/aoc-2024` stops at day 10,
so day 17 has no `aoc/inputs/2024/day17.txt`, no `Tests/Input.sw` and no
entry in `crates/cli/tests/aoc_answers.rs` or `crates/rt/tests/machine.rs`;
add those when the input comes.

The examples are checked: part 1's `4,6,3,5,6,3,5,2,1,0`, part 2's 117440
for `0,3,5,4,3,0`, and all five examples of instruction operation
(registers after, and outputs). Part 2's search is tested on three
programs of the real inputs' shape that I wrote (`2,4,1,1,7,5,1,5,4,0,5,5,
0,3,3,0` gives 164279024971453; two others shift A before the output), one
of that shape with no copy, and shorter targets. An independent Python
script (`/usr/bin/python3 -I`, not committed) agrees on all of them, and
brute force over every A below 8^(n+1) agrees on the short targets.
Compiler built from `main` at 429d61b8, 28 October 2026.

### The program

```stitchwort
type Registers = { a: Nat, b: Nat, c: Nat }

type Debugger = { registers: Registers, program: List Nat }

type Combo =
  | Value (value: Nat)
  | RegisterA
  | RegisterB
  | RegisterC

type Instruction =
  | Adv (operand: Combo)
  | Bxl (operand: Nat)
  ...
  | Cdv (operand: Combo)

def threeBit(): {Parse} Nat :=
  let start := Parse.mark()
  let value := natDigits 1 1
  Parse.ensureAt start (value < 8) "expected a 3-bit number (0 to 7)"
  value

def register (name: Text): {Parse} Nat :=
  text "Register ${name}: "
  nat()

def debugger(): {Parse} Debugger :=
  let a := register "A"
  newline()
  let b := register "B"
  newline()
  let c := register "C"
  blankLine()
  text "Program: "
  let program := sepBy1 threeBit (() => char ',')
  { registers = { a, b, c }, program }

def parseDebugger (input: Text): {Fail} Debugger := Parse.all input debugger

def main(): {IO, Fail} () :=
  let debugger := parseDebugger IO.readAll()
  IO.print "Part 1: ${solvePart1 debugger}"
  let lowest :=
    match solvePart2 debugger with
      | Some a => "${a}"
      | None => "none: no initial value of A outputs the program"
  IO.print "Part 2: ${lowest}"
```

The program stays a list of numbers, since `jnz` may jump to any
position, odd ones included; `decode opcode operand` turns the pair at the
pointer into an `Instruction` (`None` for a reserved combo operand or an
opcode above 7). `Machine.step` returns `Halt`, `Fault` or `Next machine
printed`, and `Machine.run` takes at most `fuel` steps, ending `Finished
output`, `Faulted` or `OutOfFuel`. The fuel is `(A + 1) * (length + 1)`,
enough for a loop that shifts A right on every pass; part 1 fails with
"the program didn't halt" if it runs out. The example's part 2 prints
"none": no A makes `0,1,5,4,3,0` output itself (brute force agrees).

Part 2 builds A three bits at a time from the end of the target:

```stitchwort
def candidates (output: Nat → List Nat): (target: List Nat) → List Nat
  | Nil => [0]
  | Cons value rest =>
    candidates output rest
      |> .flatMap (high => List.range 8 |> .map (low => high * 8 + low))
      |> .filter (a => output a == Cons value rest)

def lowestOutputting (output: Nat → List Nat) (target: List Nat): Option Nat :=
  candidates output target
    |> .filter (a => 0 < a ∧ output a == target)
    |> .minimum
```

It keeps every candidate at each level rather than stopping at the first
(a depth-first search would need its visiting order proved), and the
final filter checks again, so soundness doesn't depend on the shape.

### Proved, for every program and all initial register values

The spec (`Spec/Spec.sw`, 117 lines) quotes each instruction.
`comboValue` is the combo operand table. `BitwiseXor x y result` is the
bitwise XOR: bit `i` of `result` (`n / 2^i % 2 == 1`) is set when exactly
one of `x` and `y` has it set. `Executes opcode operand machine step` says
what each opcode does, with adv, bdv and cdv dividing by `Nat.pow 2
value`, and `StepMatches program machine step` adds the halt past the end.
`Halts program machine output` is the inductive relation "runs to a halt,
outputting `output`, every step as `StepMatches` says". `OutputsItself
debugger a` is `Halts` from A = `a` with the program as the output.
`LoopShape output` is the assumption part 2 needs (below).

Proved (`Proofs/`, 423 lines in six files):

- `stepMatches` (Step.sw): `Machine.step` takes the step `StepMatches`
  describes, for every program, machine, opcode and operand, including
  the reserved operand and opcodes above 7. `xorBitwise`: `Nat.xor` is the
  spec's `BitwiseXor`; `Nat.shiftRightDiv` makes the shifts the divisions.
- `outcomeHalts`, `runHalts` (Run.sw): a run that finishes is a `Halts`
  run with the same output; `runMoreFuel`: more fuel finishes the same way.
- `stepUnique`, `haltsUnique` (Unique.sw): the puzzle's computer is
  deterministic, so `part1Output`: part 1's output is the only output any
  halting run from the given registers has.
- `part2Sound` (Proofs.sw): what `solvePart2` returns is positive and
  `OutputsItself`, for every program, with no assumption.
- `candidatesComplete`, `part2Least`, `part2Complete` (Search.sw,
  Proofs.sw): if the program's output (`Debugger.outputFor`) has the loop
  shape, every A that outputs a target is among its candidates, so the
  search returns a value whenever a positive one outputs the program, and
  returns the least.

The assumption, exactly: `LoopShape output` is `(a: Nat) → ∃ first =>
output a = Cons first (if a < 8 then Nil else output (a / 8))`: what A
outputs is one number, then what A / 8 outputs unless A / 8 is 0. Real
inputs are a loop that sets B and C from A, outputs B, shifts A right by
3 and jumps to 0 unless A is 0, which has this shape (the initial B and C
are overwritten). The tests check it for A below 600 on each written
program, and that the part 1 example, which shifts by 1, doesn't have it.

Not proved:

- That any particular program has the loop shape. It is a statement about
  every A for a run with fuel, so it needs symbolic execution of the loop
  body and a bound on steps per pass: a proof per program, and there is no
  program yet.
- That `part2Least` covers every A the puzzle counts. It is stated over
  `Debugger.outputFor`, whose runs have `fuelFor` steps; an A whose run
  halts with the program as output, but only after more steps, isn't
  covered. A program of the loop shape halts within the fuel (its passes
  are at most the octal digits of A), but proving that is the same
  per-program proof.
- Parsing, as on other days.

Breaking the program makes the proofs fail: bxl as `b + operand`, or bst
without its `% 8`, fails `executesDecode`; trying only 7 low values per
level fails `candidatesComplete`.

### 1. Std.Parse

`text`, `nat`, `newline`, `blankLine` and `sepBy1` read the example first
time. Two messages read oddly:

- `natDigits 1 1` on "10" gives `line 5, column 12: expected a number of
  1 digits, got '1'`: "1 digits", and what was found is one character of
  the two-digit number it rejected.
- A missing blank line gives `line 3, column 14: expected a blank line,
  got the end of the line`. A line end is there; the next line isn't
  blank.

What I did: kept them, with tests that pin the messages. There is no
"digit in a range" piece, so `threeBit` is `natDigits 1 1` then
`Parse.ensureAt` for below 8.

Fixed: `natDigits` says "expected a 1-digit number" for one count and
"expected a number of 2 to 5 digits" for a range (a lower bound of 0 is
shown as 1, since it reads at least one digit).

### 2. Missing std

- No bitwise operations on `Nat` (only `Bool.xor`). Added
  `std/Nat/Bits.sw` (131 lines, registered in `library.rs`):
  `Nat.shiftRight` (stops once the number is 0, so a shift by a register
  holding 10^12 is cheap, where `Nat.pow 2 count` would not be),
  `Nat.testBit`, `Nat.xor` (by `decreasing m + n`, halving both), and the
  lemmas `Nat.shiftRightDiv` (`n` shifted by `k` is `n / 2^k`),
  `Nat.testBitXor`, `Nat.eqOfTestBit` (bit extensionality) and
  `Nat.halfDivPow`. Still missing: and, or, shift left, and a general
  `Nat.divDiv` (`n / a / b = n / (a * b)`).
- `List.minimum` has no lemmas, and `List.memFilter` has no converse.
  What I did: `minLeLeft`, `minLeRight`, `minEither`, the fold lemmas,
  `minimumSome`, `minimumExists` and `memFilterIntro` in
  `Proofs/Lemmas.sw` (80 lines), over `Nat` only: the general `Ord`
  versions need the `flip` law case by case.
- `Text.joinWith` takes the list first and lives in `Text`, so it doesn't
  pipe: `Text.joinWith (output.map (value => "${value}")) ","`. Scala's
  `mkString(sep)` is a method of the collection
  (<https://www.scala-lang.org/api/current/scala/collection/IterableOnceOps.html>).

Fixed: `std/Nat/Bits.sw` has `Nat.and`, `Nat.or` and `Nat.shiftLeft`,
with `Nat.testBitAnd`, `Nat.testBitOr`, `Nat.shiftLeftMul` (`n * 2^k`)
and `Nat.shiftRightShiftLeft`. std has `Ord.leRefl`, `Ord.minLeLeft`,
`Ord.minLeRight` and `Ord.minEither` (`Ord/Ord.sw`), and
`List.foldMinLeStart`, `List.foldMinLeMember`, `List.foldMinMember`,
`List.minimumSome` and `List.minimumExists` (`List/Lemmas.sw`), over any
`Ord`; `memFilterIntro` was already there as `List.memFilterIntro`.
`Proofs/Lemmas.sw` is gone. `List.joinWith` takes the list first, so
part 1 is `output.map (value => "${value}") |> .joinWith ","`.

### 3. Confusing errors

- A `[decreasing := …]` written after `Nat.xor (m / 2) (n / 2) * 2`
  attached to the `2`: "this function has no parameter named
  `decreasing`", with the note "its parameters have no names". True, but
  it doesn't say the bracket went to the last argument of `*`. Then,
  because the definition failed, each `Nat.xor.unfold` gave "`Nat.xor` is
  a function, which has no namespace to look `.unfold` up in", a cascade
  that hides the cause. What I did: moved the bracket before `* 2`.
- `auto` couldn't prove `Nat.pow 2 (Succ k) ≠ 0` for a `/`: "can't decide
  `Nat.pow 2 k * 2 ≠ 0` here", and elsewhere "can't decide `Nat.pow 2
  count + (Nat.pow 2 count + 0) ≠ 0` here". std's instance decides
  `Nat.pow (Succ b) e ≠ 0`, but `auto` computes the power one step before
  trying it. What I did: an `[auto whole: Nat.pow 2 (Succ k) ≠ 0]`
  parameter on `Nat.halfDivPow`, passed explicitly as `[whole :=
  Nat.nonzeroOfPos …]`.
- `ring` failed once a `rewrite` had put `n / a` inside `n % a`, which is
  `n - n / a * a`: the goal showed `Nat.divFuel …` terms and "`n / a % b`
  is an unknown to `ring`: truncated subtraction isn't a ring operation".
  What I did: the regrouping as its own lemma over plain variables
  (`Nat.regroupHalf`), instantiated.
- `output.map … |> .joinWith ","`: "`List` has no field or function
  `joinWith`", with the note "`Text.joinWith` takes a `List` first: write
  `Text.joinWith %3 …`". The `%3` is an internal placeholder leaking into
  the suggestion.
- A lemma restating one step of `Machine.run` (`runSucc … := rfl`) fails:
  the inner `match` is a generated function, and "the same `match` written
  again is another such function, equal to it only if neither calls the
  definition it's written in". The message explains it well and points at
  docs/syntax.md. What I did: no lemma; `match moved: machine.step program
  with` refines the hypothesis directly.

Fixed: `auto` tries the decision procedures again on a goal it couldn't
decide, as written, with a call matched by its arguments before it
computes, so `Nat.pow (Succ b) e ≠ 0` decides `Nat.pow 2 (Succ k) ≠ 0`;
`Nat.halfDivPow` has no `whole` parameter now. `f.unfold` (or any `f.x`)
for a definition `f` that failed reports nothing beyond `f`'s own errors.
A suggestion shows `…` (`write |> Text.joinWith …`) where the receiver is
a value the compiler bound, not `%3`.

### 4. Inference

- A record literal needs its type: `({ registers, pointer = 0 }:
  Machine).run …` ("can't tell which record type this literal is"), as on
  day 15.
- Otherwise none: `_` for the lists and predicates in the search proofs
  was solved every time, and `.map (.b)` on an `Option Registers` worked.

### 5. Performance

Part 2 on a 16-number program takes 0.92 s of CPU, 0.36 s of it start-up
(the example takes that long), against 0.06 s for the Python script's
same level-by-level search. Each candidate costs a full run from the
start, so the search is quadratic in the program's length; reusing the
previous level's run would make it linear, but the proofs are simpler
this way and it's fast enough. `Nat.xor` goes through the `decreasing`
fuel, one step per bit (about 50), with built-in division.

### 6. Proofs

Less friction than earlier days. `match fetched: program.get
machine.pointer with` refined goals through `Machine.step` without
lemmas; literal patterns `| 0 => … | 7 => …` with a `Succ (Succ …)`
catch-all made each opcode's case compute to `rfl`; the indexed
inductive `Halts` and a nine-arm match on two derivations (`haltsUnique`)
checked first time.

Friction:

- `auto` and powers of 2, and `ring` with divisions (item 3).
- The spec's XOR. A function (the sum of `2^i` over the bits that differ)
  would need a proof that the sum is `Nat.xor`; stating it bit by bit
  (`BitwiseXor`) made `stepMatches` easy, but then determinism needs bit
  extensionality (`Nat.eqOfTestBit`), by `decreasing` recursion on `m + n`.
- Constructors aren't known to differ (as on day 15): `Faulted = Finished
  output`, `Halt = Next …` and `Next a None = Next b (Some v)` each needed
  a discriminating function (`isFinished`, `isHalt`, `printedOf`) and
  `Eq.cong`.
- The least-A theorem is about a run with fuel, not the puzzle's runs
  (Not proved, above): a fuel-free statement needs a bound on steps for
  each program.

### 7. Comparisons

- Lean's `Nat` has `xor`, `>>>` and `testBit` in core, with
  `Nat.shiftRight_eq_div_pow`, `Nat.testBit_xor` and
  `Nat.eq_of_testBit_eq`
  (<https://github.com/leanprover/lean4/blob/master/src/Init/Data/Nat/Bitwise/Basic.lean>,
  <https://github.com/leanprover/lean4/blob/master/src/Init/Data/Nat/Bitwise/Lemmas.lean>).
  The new std file has the same three facts.
- Haskell's `Data.Bits` class has `xor`, `shiftR` and `testBit`, with an
  `Integer` instance
  (<https://hackage.haskell.org/package/base/docs/Data-Bits.html>), and
  Scala's `BigInt` has `^`, `>>` and `testBit`
  (<https://www.scala-lang.org/api/current/scala/math/BigInt.html>).
  Neither comes with lemmas.

### Size and time

Release build, on a machine with a load average around 30 to 40 (wall
time, then CPU):

| command | wall | CPU |
| --- | --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day17` | 1.4 s | 0.84 s |
| `stitchwort check --no-cache Aoc.Year2024.Day17.Proofs` | 0.9 s | 0.79 s |
| `stitchwort test --no-cache Aoc.Year2024.Day17` (37 tests) | 5.3 s | 2.8 s |
| `stitchwort run Aoc.Year2024.Day17.main` on the example | 0.47 s | 0.36 s |
| the same on `2,4,1,1,7,5,1,5,4,0,5,5,0,3,3,0` | 1.0 s | 0.92 s |

192 lines of program, 117 of spec, 423 of proofs, 105 of tests, and 131
of std (`Nat/Bits.sw`).

### Ranked

1. The real input is pending: Matt's repository has no day 17. Fix: add
   his input, its tests and its two answer entries when he has it, and a
   test that checks `LoopShape` on it.
2. No bitwise operations on `Nat` (item 2). Fix: xor, shift right and
   testBit are now in `std/Nat/Bits.sw`; add and, or and shift left with
   their `testBit` lemmas.
3. `auto` computes `Nat.pow 2 (Succ k)` past the instance that decides it
   (item 3). Fix: try instances before computing the goal, or teach `auto`
   that powers of a positive base aren't 0.
4. Part 2's least-A theorem depends on fuel (Not proved). Fix: a std
   lemma that a fuelled run with at least as much fuel as a "halts in n
   steps" derivation finishes, so per-program step bounds plug in.
5. A failed definition's `.unfold` is reported as "has no namespace", and
   `%3` leaks into a suggestion (item 3). Fix: skip references to
   definitions that failed, and print the placeholder as `…`.
6. Constructors aren't known to differ (item 6, as on day 15). Fix: a
   `noConfusion`-style lemma per type, or `cases` closing `C1 = C2`.
7. `List.minimum` and `filter` lack lemmas (item 2). Fix: add
   `minimumSome`, `minimumExists` and `memFilterIntro`, over `Ord`, to
   `List/Lemmas.sw`.
8. Parse messages: "a number of 1 digits", and "expected a blank line,
   got the end of the line" (item 1). Fix: "a 1-digit number", and show
   what the next line holds.
9. `Text.joinWith` doesn't pipe from a list (item 2). Fix: a
   `List.joinWith` taking the list first.

## Day 18: RAM Run

Bytes fall one at a time onto a square memory space; "Your memory space
is a two-dimensional grid with coordinates that range from 0 to 70 both
horizontally and vertically" (0 to 6 in the example). "Corrupted memory
coordinates cannot be entered by you or The Historians"; "You can step
up, down, left, or right", from the top left corner (0,0) to the exit in
the bottom right. Part 1: "Simulate the first kilobyte (1024 bytes)
falling onto your memory space ... what is the minimum number of steps
needed to reach the exit?" (12 bytes in the example). Part 2: "What are
the coordinates of the first byte that will prevent the exit from being
reachable from your starting position?" (part 2's wording from the public
copy at <https://tgragnato.it/2024/12/18/RAM-Run.html>).

**The real input is pending from Matt**: his repository
(<https://github.com/mdr/aoc-2024>) stops at day 10, so there is no
`inputs/2024/day18.txt`, no `Tests/Input.sw`, and the day isn't registered
in `aoc_answers.rs` or `machine.rs` yet. `examples/2024/day18.txt` is the
puzzle's example (22 and `6,1`). The tests are the example and edge cases,
cross-checked with an independent Python script (`/usr/bin/python3 -I`: a
`deque` breadth-first search, and part 2 by trying every prefix in turn,
not by a binary search). For performance the same script generated a 71
by 71 input of 3450 random distinct positions, never (0,0) or (70,70)
(not committed); the program and Python agree on it (140 and `67,67`).
This is the first day to reuse another day's code. Compiler built from
`main` at 9e19c790, 28 October 2026.

### The program

```stitchwort
import Aoc.Year2024.Day16 (Graph)

def main(): {IO, Fail} () := solveIn 71 1024

def mainExample(): {IO, Fail} () := solveIn 7 12

def byte(): {Parse} Position :=
  let x := nat()
  text ","
  let y := nat()
  { x, y }

def parseBytes (input: Text): {Fail} (List Position) := Parse.eachLine input byte

type MemorySpace = { size: Nat, corrupted: Set Position }

def MemorySpace.after (size: Nat) (bytes: List Position) (fallen: Nat): MemorySpace := { size, corrupted = bytes.take fallen |> Set.fromList }

def MemorySpace.move (memory: MemorySpace) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if memory.isSafe next then Some next else None
    | None => None

def MemorySpace.graph (memory: MemorySpace): Graph Position := {
  edges = memory.edges,
  within = memory.isSafe,
  states = memory.positions,
  listed = position => memory.safeListed position
}

def MemorySpace.fromStart (memory: MemorySpace): Map Position Nat :=
  if memory.isSafe start then memory.graph.distances [(start, 0)] else Map.empty

opaque def reachable (size: Nat) (bytes: List Position) (fallen: Nat): Bool := (MemorySpace.after size bytes fallen).fewestSteps.isSome

def firstBlocked (blocked: Nat → Bool) (low: Nat) (high: Nat): Nat
    decreasing high - low :=
  if apart: Succ low < high then
    let middle := (low + high) / 2
    if blocked middle then firstBlocked blocked low middle [decreasing := omega [apart]]
    else firstBlocked blocked middle high [decreasing := omega [apart]]
  else high

def solvePart1 (size: Nat) (fallen: Nat) (bytes: List Position): Option Nat := (MemorySpace.after size bytes fallen).fewestSteps

def solvePart2 (size: Nat) (bytes: List Position): Option Position :=
  let blocked := (fallen: Nat) => !reachable size bytes fallen
  if blocked 0 || !blocked bytes.length then None else bytes.get (firstBlocked blocked 0 bytes.length - 1)
```

The domain model is the list of byte positions; `MemorySpace.after`
turns its first `fallen` into a corrupted set. Part 1 is day 16's
Dijkstra search over a `Graph Position` whose edges each cost 1: with unit
costs it settles positions in breadth-first order. Part 1 returns `Option
Nat`, `None` when the exit can't be reached (printed as `none`); day 16
answered 0 there.

Part 2 is a binary search over the number of bytes fallen, not union-find
in reverse. Union-find would answer in one pass, but std has no union-find
and its proof would need a new invariant (each set is the positions
connected once the later bytes are removed), while the binary search
reuses part 1 and its proof unchanged and needs one new fact,
monotonicity (more bytes, fewer paths), a short induction. It runs about
13 searches for 3450 bytes. `firstBlocked` keeps `blocked low = False` and
`blocked high = True` and stops when the two are adjacent; `solvePart2`
answers `None` when the exit is cut off before any byte falls, or still
reachable after all have.

The grid size and byte count differ between the example and the real
input; std has no `IO.args` yet, so as on day 14 there are two entry
points, `main` (71, 1024) and `mainExample` (7, 12).

### Proved, for every size and list of bytes

The spec (`Spec/Spec.sw`) is in the puzzle's words over the program's
`Position.step`: `isSafe size fallen position` (inside the grid and not
in the `fallen` list, a `List`, not the program's `Set`); `stepTo`, one
step, `None` out of the grid or onto a corrupted position; `walk`, where
a list of steps ends. `IsPath size fallen steps`: the start is safe and
the steps walk from (0,0) to (`size - 1`, `size - 1`). `IsFewestSteps
size fallen fewest`: some path has `fewest` steps and none has fewer.
`HasPath size bytes count`: some path with the first `count` bytes
fallen. `IsFirstBlocking size bytes byte`: the byte at some index, with no
path once it has fallen and a path for every count up to its index.

Proved (`Proofs/`, 385 lines in 4 files; each theorem's only axiom is
`Quot.sound`, through `Set`):

- Steps.sw: the program's safety check and moves are the spec's
  (`safeAgrees`, `moveAgrees`, through `Set.containsFromList`), and the
  graph's edges are exactly the moves, each costing 1 (`edgesSound`,
  `edgesComplete`). `walkFewer`: a walk with more bytes fallen is a walk
  with fewer.
- `part1Some` (Part1.sw): `solvePart1 size fallen bytes = Some fewest` →
  `IsFewestSteps size (bytes.take fallen) fewest`. `part1None`: `None` →
  no path. Both from day 16's `distancesCorrect`, with `reach` "some walk
  from the start ends here in this many steps", and a `boundAlong` over
  walks. Then `reachableSound` and `reachableComplete`: `reachable` is
  `True` exactly when there is a path.
- `hasPathFewer` (Part2.sw), monotonicity: a path with `more` bytes
  fallen is one with `fewer ≤ more` (`walkFewer`, `safeFewer`, and
  `containsTakeMono` in Lemmas.sw).
- `firstBlockedCorrect`: from a `low` not blocked to a `high > low`
  blocked, the search returns `r` with `low < r ≤ high`, `r` blocked and
  `r - 1` not. This needs no monotonicity.
- `part2Some`: `solvePart2 size bytes = Some byte` → `IsFirstBlocking
  size bytes byte`; its "every earlier count has a path" half is where
  monotonicity comes in. `part2None`: `None` → no byte is the first to
  block.

Breaking the program (`firstBlocked … - 1` without the `- 1`, `!blocked
middle` for `blocked middle`, `<=` for `<` in `isSafe`, or edges costing
2) makes the proofs fail. Not proved: parsing (as on other days).

### 1. Std.Parse: none

`nat`, `text ","` and `nat` under `Parse.eachLine` read the bytes first
time, and the messages are good: `line 1, column 2: expected ',', got ' '`
and `line 1, column 1: expected a number, got '-'`.

### 2. Missing std

- **Graph search, again.** Day 16's `Graph` search was imported, not
  rewritten (item 6). Breadth-first search would be cheaper than Dijkstra
  with a `Set` queue, but std has neither. Haskell's `Data.Graph` has
  `reachable` and `path` ("Returns True if the second vertex reachable
  from the first") but no distances
  (<https://hackage-content.haskell.org/package/containers-0.8.1/docs/Data-Graph.html>).
- **Binary search over a monotone predicate.** Written by hand
  (`firstBlocked`). Rust's `partition_point` is this search; its
  documentation says "The slice is assumed to be partitioned according to
  the given predicate" and, if not, "the returned result is unspecified
  and meaningless" (<https://doc.rust-lang.org/std/primitive.slice.html>).
  Mathlib's `Nat.find` is "the smallest natural number satisfying `p`",
  with `Nat.find_spec` and `Nat.find_min'` proving it so, found by
  counting up, not halving
  (<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Find.html>).
- **`IO.args`**: not in std yet (another lane is adding it), so two entry
  points.
- **Lemmas**: `List.contains` over `take` is monotone in the count
  (`containsTakeMono`, Lemmas.sw), and `(Set.fromList xs).contains x =
  xs.contains x` took `Set.containsFromList`, `Map.Spec.sameKeyDecide` and
  `List.anyCong` together (`safeAgrees`). Not added to std (the `List`
  lemma files are another lane's).

Fix: move day 16's search to std with a breadth-first search beside it;
add a `Nat.partitionPoint` with `firstBlockedCorrect` as its lemma,
`List.containsTakeMono`, and `Set.containsFromList` stated with
`List.contains`.

### 3. Confusing errors

- A pattern `let` on a proof inside a definition stays in its unfolding
  equation. The first `firstBlocked` took `halfBounds` apart with `let
  (Both below above) := halfBounds (high - low)` for its `decreasing`
  proofs; then a lemma stating one step of it as written gave

  ```text
  expected `Aoc.Year2024.Day18.firstBlocked.%step blocked low high (blocked low high [auto decreasing: _] => firstBlocked blocked low high) = (if blocked (low + half …) then firstBlocked blocked low (low + half …) else firstBlocked blocked (low + half …) high)`, but this has type `Decidable.elim (Nat.decLessThan (Succ low) high) (x => ?8 blocked low high apart) (?7 blocked low high apart) = ?8 blocked low high apart`
  ```

  A scratch file showed the cause: the same function with `let bounds :=
  halfBounds …` and `And.left bounds` in its proofs unfolds as written;
  the pattern `let` leaves a `match` on a proof that can't compute. The
  message names an internal `%step` and doesn't say what is stuck. What I
  did: no pattern `let` in the body (and then `/ 2`, item 6). Fix: erase
  matches on proofs in `f.unfold`, or say which `match` is stuck.
- Before that, `rewrite apart in rfl` on the same goal gave
  ``[E-REWRITE-MOTIVE] Error: replacing `Succ low < high` everywhere in the
  goal doesn't give a valid proposition`` (`apart` was written `Nat.leq
  (Succ (Succ low)) high = True`, shown as `Succ low < high`). Its note 2
  explains it (the `if` carries the proof); `Decidable.elimEq`, as on day
  12, worked.
- `if apart: Succ low < high = True then` is ``[E-PARSE] Error: expected
  `then`, but found `=` ``, and `if apart: (Succ low < high) = True then`
  is ``expected `Prop`, but this has type `Bool` `` with "this comparison
  is on `Prop` because of this": in an `if` guard, `<` is the
  proposition. `if apart: Succ low < high then` works, but neither error
  says so. Fix: a note suggesting the guard without `= True`.
- A `match` refines hypotheses through definitions, so a term built later
  in the branch no longer fits. With `answer: solvePart1 … = Some fewest`,
  `match startSafe: memory.isSafe start with` turned `answer` (and a `let`
  restating it) into ``Map.get (Aoc.Year2024.Day16.Graph.searchFrom { edges
  = …, … } …) { x = size - 1, y = size - 1 } = Some fewest``, and
  `reachedAll memory.exit fewest found`, from a lemma about
  `memory.fromStart`, then gave ``expected `Map.get (MemorySpace.fromStart
  (MemorySpace.after size bytes fallen)) (MemorySpace.exit (MemorySpace.after
  size bytes fallen)) = Some fewest`, but this has type `Map.get
  (Aoc.Year2024.Day16.Graph.searchFrom { edges = …, within = …, states = …,
  listed = … } { items = … } { raw = … } (Some …) rfl) { x = size - 1, y =
  size - 1 } = Some fewest` ``. The note ("Write `_` for such an argument")
  is right: I stated the lemma about `graph.distances` (what the refined
  term computes to) and passed `_`. In the `False` branch the refinement
  helped: `answer` became `Map.get` of the empty map `= Some fewest`,
  refuted directly.
- Internal names in messages: ``Decidable.toBool (DecEq.%decide eq x
  wanted)``, `Position.%decEq`, `Position.%instOrd`. Readable once known.

### 4. Inference: none new

`_` for the arguments a hypothesis fixes worked everywhere I used it
(`Bool.andLeft _ _ safe`, `Option.someInjective _ _ moved`). The one type
on a lambda, `(fallen: Nat) => …`, I wrote before trying without.

### 5. Performance

On the generated 71 by 71 input (3450 bytes) `stitchwort run` takes 2.6 s
user; Python's breadth-first search with the same binary search takes
0.02 s (13 searches), and Python trying every prefix 2.9 s. The program
runs 16 searches (part 1, the two ends, 13 halvings). The example's whole
run takes 0.66 s, mostly loading, so one search over at most 5041
positions is roughly 0.12 s (an estimate from these totals, not measured
alone), against Python's 1.5 ms. Each step is day 16's `Set (Nat,
Position)` queue and `Map` of settled positions, balanced trees compared
field by field. Not pursued. Fix: a breadth-first search in std with a
plain queue.

Checking was the surprise: `check --no-cache Aoc.Year2024.Day18.Proofs`
took 12.9 s user, about 10 s of it in the two part 2 theorems (2.7 s with
them removed). Making `reachable` an `opaque def`, with `unfolding
reachable` on the two theorems that look inside it, brought the whole
check to 2.8 s, so the time went on the checker computing through
`reachable`, which is the whole search, while comparing terms. Day 16's
proofs take 3.0 s. Fix: compare by name before unfolding a large
definition, or report what a slow check spent its time on.

### 6. Proofs

Reusing day 16's proof worked better than reusing its code. Day 16's
`distancesCorrect` applied as it is: day 18 supplied its `reach` and the
four facts it needs (sources reached and within, edges keep `reach` and
`within`), about 25 lines. What got in the way, for moving it to std:

- **Day 16's `boundAlong` is about the maze.** Optimality is an
  induction along a path, and day 16's is over its own moves; I wrote it
  again over walks (17 lines). A generic one over a list of edges would
  serve both, leaving each day to turn its paths into edge lists.
- **`Bound`, `SearchResult`, `boundWeaken` and `anyMember` live in day
  16's `Proofs` namespace**, beside maze lemmas, so the import names day
  16 (`import Aoc.Year2024.Day16.Proofs (Bound, SearchResult, boundWeaken,
  distancesCorrect)`). The program's `import Aoc.Year2024.Day16 (Graph)`
  brings day 16's maze code with it into every check. Importing `Graph`
  did bring its methods (`.distances`), so the program reads naturally.
- **Finiteness.** `Graph` wants a list of all states and a proof that
  `within` implies membership: a list of every grid position and a
  9-line `safeListed` (`List.memFlatMapIntro`, `List.memRangeFromIntro`,
  `List.memMap`). Day 16's item 7 again.
- **Sources must be within.** `distancesCorrect` assumes each source is
  in the graph, so the program checks the start is safe before searching
  (`fromStart`); a corrupted start gets `Map.empty`.

Monotonicity was easy: about 45 lines, an induction on the walk with
`containsTakeMono`. Stating the spec over the fallen `List` rather than
the program's `Set` cost one lemma (`safeAgrees`). The binary search's
lemma needed `f.unfold` and `Decidable.elimEq` (item 3). `omega` handles
`(low + high) / 2` directly, so the first version's hand-written `half`
and its bounds lemma went. Part 2's case splits are on `Bool` arguments
with their equations (`part2SomeCases`, `part2NoneCases`) rather than
`match`, so `answer` keeps the shape that `part2Search` and friends
rewrite.

### 7. Comparisons

- Rust's `partition_point` and Mathlib's `Nat.find`: item 2. Rust states
  the monotonicity precondition in prose and leaves the result
  meaningless without it; here `firstBlockedCorrect` holds without it,
  and `hasPathFewer` supplies it where "first" needs it.
- Haskell's `Data.Graph` decides reachability (`path`) but gives no
  distances: item 2.

### Size and time

Release build, load average around 20 to 36:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day18.Proofs` | 2.8 s user |
| `stitchwort check --no-cache Aoc.Year2024.Day18` | 1.8 s user |
| `stitchwort test --no-cache Aoc.Year2024.Day18` (24 tests) | 3.2 s user |
| `stitchwort run Aoc.Year2024.Day18.mainExample` on the example | 0.66 s user |
| `stitchwort run Aoc.Year2024.Day18.main` on a generated 71 by 71 input | 2.6 s user |

138 lines of program, 55 of spec, 385 of proofs, 93 of tests.

### Ranked

1. The real input is pending: Matt's repository has no day 18. Fix: add
   his input, its tests and its two answer entries when he has it.
2. Checking spent 10 s computing through `reachable` until it was made
   opaque (item 5). Fix: compare by name before unfolding a large
   definition, or report what a slow check spent its time on.
3. Day 16's search reused well, but its optimality induction, its helper
   lemmas and its finiteness list don't travel (item 6). Fix: move
   `Graph`, `distancesCorrect`, a generic `boundAlong` over edge lists,
   `Bound` and `anyMember` to std, beside a breadth-first search.
4. 2.6 s against Python's 0.02 s, roughly 0.12 s a search (item 5). Fix:
   a breadth-first search in std with a plain queue.
5. A pattern `let` on a proof makes a definition's unfolding equation
   unusable, with a message naming `%step` (item 3). Fix: erase matches
   on proofs in `f.unfold`, or name the stuck `match`.
6. No binary search over a monotone predicate (item 2). Fix: a std
   `Nat.partitionPoint` with `firstBlockedCorrect` as its lemma.
7. `if h: a < b = True` fails to parse, and with brackets says `Prop`
   isn't `Bool` (item 3). Fix: a note suggesting the guard without `=
   True`.
8. No `IO.args` yet, so two entry points (item 2). Fix: the lane adding
   it.
9. Small missing lemmas: `containsTakeMono`, and `Set.fromList` against
   `List.contains` (item 2). Fix: add them to std.

## Day 19: Linen Layout

Towel patterns, each a sequence of coloured stripes ("white (w), blue (u),
black (b), red (r), or green (g)"), on one line separated by commas; a
blank line; then the designs, one per line. "You can use any towels you
want, but all of the towels' stripes must exactly match the desired
design." Part 1: "How many designs are possible?" Part 2: "What do you get
if you add up the number of different ways you could make each design?"
(part 2's wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-19/README.txt>).

**The real input is pending from Matt**: his repository
(<https://github.com/mdr/aoc-2024>) stops at day 10, so there is no
`inputs/2024/day19.txt`, no `Tests/Input.sw`, and the day isn't registered
in `aoc_answers.rs` or `machine.rs` yet. `examples/2024/day19.txt` is the
puzzle's example (6 and 16). The tests are the example and edge cases, all
cross-checked with an independent Python script (`/usr/bin/python3 -I`: a
memoised recursion from the front of each design with
`str.startswith(pattern, start)`, not a table of suffixes). For
performance, a second script generated 450 patterns (every w-free pattern
of up to four stripes, and random ones with w only inside and never
doubled, so a design containing "ww" is impossible) and 400 designs of 60
to 64 stripes (not committed). The program and Python agree on it (266 and
136028840268015961186, past 2^64; `Nat` is arbitrary precision). This is
the first dynamic-programming day. Compiler built from `main` at a34721f9,
28 October 2026.

### The program

```stitchwort
def stripe(): {Parse} Stripe := pick [("w", White), ("u", Blue), ("b", Black), ("r", Red), ("g", Green)]

def onsen(): {Parse} Onsen :=
  let patterns := sepBy1 (() => many1 stripe) (() => text ", ")
  blankLine()
  let designs := lines (() => many1 stripe)
  { patterns, designs }

def parseOnsen (input: Text): {Fail} Onsen := Parse.all input onsen

def startsWith [auto decEq: DecEq a]: (whole: List a) → (start: List a) → Bool
  | whole, Nil => True
  | Nil, Cons first rest => False
  | Cons wholeFirst wholeRest, Cons first rest => wholeFirst == first && startsWith wholeRest rest

def waysForSuffixes (patterns: List Pattern): (design: Design) → List Nat
  | Nil => [1]
  | Cons first rest =>
    let later := waysForSuffixes patterns rest
    let ways := patterns.sumBy (pattern =>
      if startsWith (Cons first rest) pattern then later.getOr (pattern.length - 1) 0 else 0)
    Cons ways later

def waysToMake (patterns: List Pattern) (design: Design): Nat := waysForSuffixes patterns design |> .headOr 0

def solvePart1 (onsen: Onsen): Nat := onsen.designs.count (design => waysToMake onsen.patterns design > 0)

def solvePart2 (onsen: Onsen): Nat := onsen.designs.sumBy (waysToMake onsen.patterns)
```

The domain model is a `Stripe` type of five colours; a `Pattern` and a
`Design` are lists of stripes, so the proofs reason about lists rather
than `Text`. The memo is the table itself: `waysForSuffixes` recurses down
the design and returns the number of ways for every suffix, longest first,
ending with the empty suffix's one way. A suffix's count adds up, over the
patterns it starts with, the count of what follows that pattern, which is
already in the table `pattern.length - 1` entries along. No `Map`, no
state, no fuel: plain structural recursion, a fold from the end in all but
name. Part 1 counts the designs with a positive count.

### Proved, for every onsen whose patterns each have a stripe

The spec (`Spec/Spec.sw`) is the literal reading. `towelLists patterns
count` is every list of at most `count` towels, each with any of the
patterns. `arrangements patterns design` keeps those whose stripes, laid
end to end (`towels.concat`), are the design, among lists of up to
`design.length` towels. `possible` is "some arrangement", `ways` the
number of arrangements; `part1` counts the possible designs and `part2`
sums the ways.

Proved (`Proofs/`, 261 lines in 6 files):

- `matchingSucc` (Counting.sw): the lists of at most `count + 1` towels
  making a design are the empty list, if the design is empty, and, for
  each pattern the design starts with, that towel followed by a list of at
  most `count` towels making the rest. This is the classic recurrence,
  derived from the spec's enumeration rather than assumed.
- `tableCorrect` (Table.sw): entry `index` of the program's table is the
  number of lists of at most `count` towels making the suffix after
  `index` stripes, for any `count` at least that suffix's length. From it,
  `waysCorrect`: `waysToMake patterns design = ways patterns design`.
- `part1Correct` and `part2Correct` (Proofs.sw): `solvePart1 onsen =
  part1 onsen` and `solvePart2 onsen = part2 onsen`.
- `possibleIff` (Possible.sw): `possible patterns design = True` exactly
  when some list of towels of the patterns, of any length, makes the
  design. This justifies the spec's bound: every towel has a stripe, so no
  arrangement has more towels than the design has stripes.

All take `Striped patterns` (every pattern has at least one stripe). With
an empty pattern the puzzle's count is infinite (any number of empty
towels can be slipped in), and the program would be wrong; the puzzle has
none, and the parser can't produce one (`many1 stripe`), though parsing
isn't proved, as on other days. Breaking the program (`[0]` for the empty
suffix, `pattern.length` for `pattern.length - 1`, or `> 1` in part 1)
makes the proofs fail. Nothing asked for is left unproved.

### 1. Std.Parse: none

`sepBy1`, `many1`, `pick`, `text ", "`, `blankLine` and `lines` composed
first time, and the messages are good: `"r, x"` gives `line 1, column 4:
expected 'w' or 'u' or 'b' or 'r' or 'g', got 'x'`, and no designs gives
`line 3, column 1: expected 'w' or 'u' or 'b' or 'r' or 'g', got the end
of the input`. A missing blank line (`"r, wr\nrwr\n"`) gives `line 2,
column 1: expected a blank line, got 'r'`, without offering `, ` (more
patterns) at the end of line 1. Fine as it is.

### 2. Missing std

- No prefix test on lists. `Text` has `startsWith` and `stripPrefix`, but
  `List` has neither (Haskell's `Data.List` has `isPrefixOf` and
  `stripPrefix`,
  <https://hackage.haskell.org/package/base/docs/Data-List.html#v:isPrefixOf>;
  Scala has `Seq.startsWith`,
  <https://github.com/scala/scala/blob/2.13.x/src/library/scala/collection/Seq.scala>;
  Lean has `List.isPrefixOf`,
  <https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.isPrefixOf>).
  What I did: a generic `startsWith` in the program, with its lemmas in
  `Proofs/Lemmas.sw` (`startsWithAppend`, `startsWithSplit`,
  `startsWithLength`, and the `==`-on-`append` facts `appendEqDrop` and
  `appendNotEq`). Not added to std, to keep this lane off the std hashes.
- No `List.isEmpty`: `!(arrangements patterns design).isEmpty` gave
  ``[E-UNKNOWN-FIELD] Error: `List` has no field or function `isEmpty` ``
  (`Text.isEmpty` exists; Haskell has `null`, Scala `isEmpty`). Wrote `!=
  []`.
- Missing list lemmas: `(start ++ rest).drop start.length = rest`
  (`dropAppend`) and counting over a `flatMap` (`countFlatMap`, the
  `count` twin of `List.lengthFlatMap`). Both in Lemmas.sw.
- No memo table needed: the table of suffix counts is the recursion's
  result, so neither a `Map` memo nor a `State` effect came up. In Scala
  the usual memo is `mutable.Map.getOrElseUpdate`
  (<https://github.com/scala/scala/blob/2.13.x/src/library/scala/collection/mutable/Map.scala>);
  here the pure table is as short, and it is what the proof is about.
- Naming: `Map.getOr` beside `Option.getOrElse`. In throwaway timing code
  I wrote `getOrElse` on a `Map` and got ``[E-UNKNOWN-FIELD] Error: `Map`
  has no field or function `getOrElse` ``.

### 3. Confusing errors

- `!=` means two things: in a theorem's statement, `(xs.length > 0) = (xs
  != [])` elaborated `>` as a `Bool` but `!=` as the `Prop` `xs ≠ []`, so
  `rfl` on `Nil` gave ``[E-REFL] Error: `rfl` can't prove this``, ``
  `0 < List.length xs` and `xs ≠ []` aren't equal``, with ``Note 1:
  computing both sides gives `False = True` and `[] ≠ []` ``, which reads
  as if one side computed to `False = True`. The spec's `!=`, in a `def`
  returning `Bool`, is the `Bool`, so the lemma couldn't be applied to it
  either: ``expected `(1 <= ways onsen.patterns design) =
  Decidable.toBool (Decidable.not (List.decEq (x y => List.decEq (x y => …)
  x y) (List.filter …) []))` ``, the spec's `!=` shown fully unfolded. What
  I did: stated the lemma about `possible` itself (`possibleWays`, a
  `match` on `arrangements patterns design`), and in Possible.sw named the
  test (`hasSome lists := lists != []`) so lemma types match the spec's by
  unfolding. Fix: read `!=` as a `Bool` wherever `==` would be one, or say
  which reading was chosen.
- `if` isn't an operand of `=` in a theorem's type: `… = if startsWith
  design pattern then … else 0 :=` gave ``[E-PARSE] Error: expected an
  expression, but found `if` ``. Bracketed it. Fix: allow it, or say to
  bracket an `if` that is an operand.
- Clear ones: ``unknown name `Eq.cong` `` with ``Note: `Eq` is `Std.Eq`;
  add `import Std (Eq)` ``, and ``[E-REWRITE-NO-GOAL] Error: `rewrite`
  needs to know what it has to prove`` on an unannotated `let`, whose note
  suggests the ascription.

### 4. Inference: none

`Bool.andLeft _ _ starts` and `DecEq.sound _ _ made` were solved, the
derived `DecEq` for `List Stripe` was found by `auto`, and every lambda's
parameter type was known.

### 5. Performance

On the generated input (450 patterns, 400 designs of 60 to 64 stripes),
`stitchwort run` takes 8.1 s user; Python takes 0.21 s. Throwaway mains
(not committed) split it: loading and parsing 0.87 s; part 2 alone 4.45
s, so each part spends about 3.6 s, and both build the same tables, since
each part takes the parsed onsen alone. The work is 400 × 62 × 450, about
11 million calls of the `sumBy` lambda, most failing `startsWith` on the
first stripe: about 0.33 µs each. A `Stripe`-only `startsWith` by `match`
instead of the generic `DecEq` one was no faster (4.34 s), so the
dictionary isn't the cost. Grouping the patterns by first stripe in a
`Map Stripe (List Pattern)` halved part 2 (2.21 s); not adopted, to keep
the program the puzzle's shape and the proof short. The `Nat` sums past
2^64 cost nothing visible. Fix: faster calls of small closures in the
evaluator, and let `main` share work between the parts.

### 6. Proofs

Smaller and easier than expected: 261 lines, and every file checked on
the first or second try; most errors were missing imports. What made it
work:

- A spec whose enumeration has the recurrence's shape. `towelLists` adds
  one towel at the front per step, so counting over it splits by the first
  towel (`countFlatMap`, `List.countMap`), and `matchingSucc` is the
  recurrence. The bound is the design's length, and Possible.sw proves it
  loses nothing.
- Proving the table for every `count` at least the suffix's length, not
  exactly the length, so the induction never needs "lists longer than the
  design make nothing". Plain structural recursion on the design was
  enough, including the recursive call inside the `List.sumByCongMem`
  lambda.
- `match starts: startsWith (Cons first rest) (Cons stripe others) with`
  refined the `if` in the goal, so the `False` arm is `rfl`.

Friction: the `!=` reading (item 3), and `Striped` as a hypothesis on
every theorem, because `List Pattern` can hold an empty pattern. A
non-empty list type (Haskell's `NonEmpty`,
<https://hackage.haskell.org/package/base/docs/Data-List-NonEmpty.html>)
would make that a fact of the type; Stitchwort's std has none.

### Size and time

Release build, load average around 20:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day19.Proofs` | 1.0 s user (1.7 s) |
| `stitchwort check --no-cache Aoc.Year2024.Day19` | 0.8 s user (0.9 s) |
| `stitchwort test --no-cache Aoc.Year2024.Day19` (19 tests) | 1.1 s user (1.3 s) |
| `stitchwort test Aoc.Year2024.Day19` (warm) | 0.4 s user (0.4 s) |
| `stitchwort run Aoc.Year2024.Day19.main` on the example | 0.36 s user |
| `stitchwort run Aoc.Year2024.Day19.main` on the generated input | 8.1 s user |

72 lines of program, 34 of spec, 261 of proofs, 64 of tests.

### Ranked

1. The real input is pending: Matt's repository has no day 19. Fix: add
   his input, its tests and its two answer entries when he has it.
2. `!=` is a `Prop` in a theorem's statement and a `Bool` in a `def`, and
   the error shows it unfolded (item 3). Fix: one reading, the `Bool`,
   wherever `==` is a `Bool`.
3. 8.1 s against Python's 0.21 s, with both parts building the same
   tables (item 5). Fix: faster small-closure calls in the evaluator;
   share work between the parts in `main`.
4. No `List.startsWith`, `List.stripPrefix` or `List.isEmpty` (item 2).
   Fix: add them to std's List toolkit, with the prefix lemmas from
   Lemmas.sw.
5. `dropAppend` and `countFlatMap` missing from std (item 2). Fix: add
   them beside `List.lengthFlatMap`.
6. Every theorem assumes `Striped patterns` (item 6). Fix: a std non-empty
   list type that `many1` could return.
7. `= if …` is a parse error (item 3). Fix: parse `if` as an operand, or
   name the fix in the message.
8. `Map.getOr` beside `Option.getOrElse` (item 2). Fix: one name for both.

## Day 20: Race Condition

A racetrack of track (`.`, with `S` and `E`) and walls (`#`). "Exactly
once during a race, a program may disable collision for up to 2
picoseconds. This allows the program to pass through walls as if they
were regular track. At the end of the cheat, the program must be back on
normal track again"; "cheats are uniquely identified by their start
position and end position". Part 1: "How many cheats would save you at
least 100 picoseconds?" Part 2: the same, but "The latest version of the
cheating rule permits a single cheat that instead lasts at most 20
picoseconds" (part 2's wording from the public copy at
<https://github.com/gchan/advent-of-code-ruby/blob/master/2024/day-20/README.txt>).

**The real input is pending from Matt**: his repository
(<https://github.com/mdr/aoc-2024>) stops at day 10, so there is no
`inputs/2024/day20.txt`, no `Tests/Input.sw`, and the day isn't registered
in `aoc_answers.rs` or `machine.rs` yet. `examples/2024/day20.txt` is the
puzzle's example. The example lists the cheats by saving rather than one
answer, so `main` takes the least saving from its arguments (`-- 50`),
100 by default; on the example, part 1 counts 44 cheats saving at least 1
and part 2 counts 285 saving at least 50, and both count 0 at 100. The
tests check every per-saving count the puzzle lists, for both parts, all
cross-checked with an independent Python script (`/usr/bin/python3 -I`:
breadth-first search from S and from E, then every pair of track
positions, not a diamond of offsets). For performance a second script
generated a 141 by 141 single-path track of 9,400 steps (a random
Hamiltonian path on the 70 by 70 lattice of odd positions, by backbite
moves, cut to 4,701 cells; not committed). The program and Python agree on
it: 1953 and 1084640. Compiler built from `main` at 5f463d1a, 28 October
2026.

### The program

```stitchwort
def tile(): {Parse} Tile := pick [("#", Wall), (".", Track), ("S", Start), ("E", End)]

def parseRacetrack (input: Text): {Fail} Racetrack :=
  let tiles :=
    Parse.all input (() => grid tile)
      |> .gridCells
      |> .map ((((row, column), kind)) => (({ row, column }: Position), kind))
  {
    track = tiles.filter (entry => entry.snd != Wall) |> .map (entry => entry.fst) |> Set.fromList,
    start = onlyTile tiles Start "S",
    end = onlyTile tiles End "E"
  }

def Racetrack.fromStart (racetrack: Racetrack): Map Position Nat := racetrack.graph.distances [(racetrack.start, 0)]

def Racetrack.toEnd (racetrack: Racetrack): Map Position Nat := racetrack.graph.distances [(racetrack.end, 0)]

def Position.around (position: Position) (length: Nat): List Position :=
  List.between (position.row - length) (position.row + length)
    |> .flatMap (row =>
      let spare := length - Nat.absDiff row position.row
      List.between (position.column - spare) (position.column + spare) |> .map (column => ({ row, column }: Position)))

def savesFrom (toEnd: Map Position Nat) (honest: Nat) (threshold: Nat) (start: Position) (before: Nat) (end: Position): Bool :=
  match toEnd.get end with
    | Some after => before + start.distance end + after + threshold ≤ honest
    | None => False

def cheatsFrom (fromStart: Map Position Nat) (toEnd: Map Position Nat) (honest: Nat) (length: Nat) (threshold: Nat) (start: Position): Nat :=
  match fromStart.get start with
    | Some before => start.around length |> .count (savesFrom toEnd honest threshold start before)
    | None => 0

def countCheats (length: Nat) (threshold: Nat) (racetrack: Racetrack): Nat :=
  let fromStart := racetrack.fromStart
  match fromStart.get racetrack.end with
    | Some honest => racetrack.track.toList |> .sumBy (cheatsFrom fromStart racetrack.toEnd honest length threshold)
    | None => 0

def solvePart1 (threshold: Nat) (racetrack: Racetrack): Nat := countCheats 2 threshold racetrack

def solvePart2 (threshold: Nat) (racetrack: Racetrack): Nat := countCheats 20 threshold racetrack
```

`main` is `thresholdFrom IO.args()`, `parseRacetrack IO.readAll()`, and
the two parts printed. The racetrack's graph is day 18's shape: the track
positions, each a step from its track neighbours, imported as day 16's
`Graph`.

**Walk or search.** The track is a single path, so walking it from S and
numbering the positions would give the times. I used day 16's search
instead, from S and from E: the times are then proved fastest for any
track, from day 16's `distancesCorrect`, with no single-path assumption to
state, check or prove anything under. A walk would have needed the
assumption made precise (every track position has at most two track
neighbours, and the walk reaches all of them) and a proof that a
numbering along a path is the fastest time, which day 16's theorem already
gives. Each search takes about 0.25 s on the generated track; the four
(two per part) are about 1 s of the 23 s.

A cheat's saving is the fastest race without it minus the race with it:
the fastest time to its start, its own time (the Manhattan distance), then
the fastest time from its end. On a single path this is the brief's
"distance along the track minus the cheat's time"; in general it is what
"save" means. For each track position reached from S, the program counts
the positions in the diamond of rows plus columns at most `length` away
(841 for 20, fewer at the edges) whose time to E makes the race short
enough; a wall has no time to E, so the lookup is also the "ends on track"
test.

### Proved, for every racetrack whose S and E are track

The spec (`Spec/Spec.sw`) is the literal reading. `race` makes moves up,
down, left or right, each onto track; `IsFastest r from to time` is some
race from `from` to `to` taking `time`, and none faster. A `Cheat` is a
start and an end; `IsCheat` puts both on track with `cheatTime` (rows plus
columns between them) at most `length`; `SavesAtLeast` adds that the
fastest time to the start, plus the cheat, plus the fastest time from the
end, plus the threshold, is at most the fastest race. `IsCount r length
threshold count` says there is a list of cheats, each once, holding
exactly the cheats saving at least the threshold, `count` long.

Proved (`Proofs/`, 505 lines in 4 files):

- `fromStartFastest` and `fastestFromStart` (Times.sw): the search from S
  settles a position for `time` exactly when `time` is the fastest race
  there. `toEndFastest` and `fastestToEnd`: the same for the search from E,
  for races from a position on track to E. The second pair needs every
  move taken back (`moveBack`: a step the opposite way returns), since the
  search runs from E over the same graph.
- `aroundSound`, `aroundComplete`, `distinctAround` (Around.sw): the
  diamond lists exactly the positions at most `length` away, each once.
- `countCheatsCorrect` (Count.sw): `IsCount racetrack length threshold
  (countCheats length threshold racetrack)`, with the witness list the
  cheats the program counts, start by start (`counted`); and
  `part1Correct`, `part2Correct` for lengths 2 and 20.

The hypotheses are that S and E are track, which the parser guarantees
(both are kept as track) but which isn't proved, as parsing isn't on other
days. Breaking the program (`<` for `≤` in `savesFrom`, or one more column
either side in `around`) makes the proofs fail.

Not proved: that the fewest moves through walls from a cheat's start to
its end is the Manhattan distance. The spec defines a cheat's time that
way, as the brief asked, rather than as a list of moves through anything;
proving it would be a lemma that a monotone list of moves exists and no
list is shorter. Nothing else asked for is left unproved.

### 1. Std.Parse: none

`grid tile` and `List.gridCells` composed first time. `#S.x#` gives
`line 1, column 4: expected '#' or '.' or 'S' or 'E' or the end of the
line, got 'x'`. `grid` accepts rows of different lengths; a short row
reads as walls beyond its end, which a test checks, so the program doesn't
check the rectangle as day 16's does.

### 2. Missing std

- A grid position. Nine 2024 days now define their own `Position` (days
  6, 8, 10, 12, 14, 15, 16, 18 and 20), most with the same `step` in four
  directions, its `Zero` cases, and the "step back" lemma (day 16's
  `stepBack`, copied here for `Up`/`Down`/`Left`/`Right`). What I did:
  wrote them again. A std `Grid.Position` with `step`, `opposite`,
  `stepBack` and the Manhattan distance would remove about 60 lines a day.
- No array with constant-time indexing. The part 2 inner loop is 7.5
  million `Map Position Nat` lookups (see item 5). Haskell has
  `Data.Array`, whose documentation says "a programmer may reasonably
  expect rapid access to the components"
  (<https://hackage.haskell.org/package/array/docs/Data-Array.html>).
  What I did: kept the `Map`.
- No finite cardinality to state "the number of cheats". Lean's Mathlib
  has `Finset.card`, "the number of elements of `s`"
  (<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html>).
  What I did: the spec says a list exists holding each such cheat once
  (`List.Distinct`, with membership an `Iff`), and its length is the count.
  `List.distinctFlatMap`, `distinctMap`, `distinctFilter` and
  `Map.keysDistinct` made that cheap.
- `Nat.absDiff` exists, and the `- n` saturating subtraction made the
  diamond's clipping at row and column 0 free.

### 3. Confusing errors

- An effect in an argument runs whether or not it's used. `saving.toNat
  |> .fold (Fail.fail usage) (least => least)` type-checks, and fails
  every time, even for `-- 50`: the program printed ``error: expected no
  arguments, or the least saving to count, such as `50` `` with no
  diagnostic. Arguments are evaluated first, and `Fail.fail usage` is an
  argument. Scala's `Option.fold` and `getOrElse` take the default by
  name (`ifEmpty: => B`,
  <https://github.com/scala/scala/blob/2.13.x/src/library/scala/Option.scala>),
  so the Scala habit is wrong here. What I did: `Fail.need saving.toNat
  usage`. Fix: warn on an effectful argument to a parameter of a pure
  function type (`b`, not `() → {e} b`), or give `Option.fold` a thunk
  for the default.
- `List.length` of a long list runs out of stack. `(racetrack.cheats
  20).length` on the generated track (about 3.5 million cheats, an
  earlier version of the program) gave ``[E-RESOURCE] Error: ran out of
  resources: it recursed more deeply than allowed`` with ``Note 2: the
  recursion was deepest in `Std.List.length` (1999999 frames pending)``,
  after 18 s. `List.count` on the same list was fine. What I did: counted
  start by start without building the list. Fix: make `List.length` a
  loop, as `count` is.
- `rewrite` with an unfolding lemma after a `match` has already refined
  the goal: `match honestFound: racetrack.fromStart.get racetrack.end
  with | Some honest => rewrite countCheatsSome … in …` gave
  ``[E-REWRITE-NOTHING] Error: `rewrite` found no `countCheats length
  threshold racetrack` in the goal``. Its Note 1 shows the goal already
  rewritten (`… = List.sumBy (Set.toList …) (cheatsFrom … … honest length
  threshold)`), so it can be worked out, and the `match` refining through
  `countCheats`'s own inner `match` is a pleasant surprise; in one case
  the error even says ``the goal already holds by computing, so `rfl`
  proves it without a `rewrite` ``. What I did: deleted six unfolding
  lemmas and their rewrites. Fix: say "the `match` on line N already
  replaced this" when the rewritten form is already there.
- Clear ones: `.all` at the start of a line gave ``[E-PARSE] Error: a
  line can't start with a method section`` with a note suggesting `|>
  .all`; `rewrite omega […] in got` gave ``[E-OMEGA] Error: `omega`
  needs to know what it proves`` with ``give it a type: `(omega: a <=
  b)` ``.

### 4. Inference: none

`_` for the function in `List.memFlatMapElim`, `List.anyElim` and day
16's `memMapElim`, and for `Option.someInjective`'s arguments, were all
solved; the `(cheat => { forward = …, backward = … })` `Iff` record was
checked against the spec's `Iff` with no annotation.

### 5. Performance

On the generated track (9,401 track positions), `stitchwort run` takes
23.1 s user; Python takes 0.64 s. Throwaway mains (not committed) split
it: parsing 0.83 s; the two searches about 0.5 s; part 1 about 0.8 s;
part 2 about 18 s, of which building the diamonds (7.5 million positions)
is about 5 s and the `toEnd` lookups (one per diamond position, about 1.7
µs each) the rest. Each part runs its own two searches, as each part takes
the parsed racetrack alone. Part 2's work is the brief's n × 840: 9,401 ×
841 = 7.9 million candidate ends before clipping.

Two things cost more than the work:

- **A `let` used in a `match` arm inside a lambda is recomputed on every
  call.** My first version wrote the counting inline:

  ```stitchwort
  let toEnd := racetrack.toEnd
  ...
  racetrack.track.toList |> .sumBy (start =>
    match fromStart.get start with
      | None => 0
      | Some before => start.around length |> .count (end => match toEnd.get end with …))
  ```

  On a 999-position track it took 28.4 s user, against 2.6 s for the same
  code with the two lambdas made top-level functions (`cheatsFrom`,
  `savesFrom`), the program above. A minimal pair on the generated track,
  each summing 20 numbers: `List.range 20 |> .sumBy (i => match
  racetrack.track.toList.head with | Some first => fromStart.size + i |
  None => 0)` after `let fromStart := racetrack.fromStart` takes 5.9 s;
  the same with `fromStart` only in the scrutinee, or with a lambda instead
  of the `match`, takes 1.1 s. The 4.8 s difference is 20 searches of
  about 0.25 s. The lifted `match` helper "re-creates" the `let`s it uses
  (the comment on `Draft::lets`, `crates/elab/src/lift.rs`), so the
  search is redone each time the helper is called. What I did: top-level
  functions taking the maps as arguments. Fix: pass a `let`'s value to
  the helper as a capture instead of re-creating its definition, at least
  when the helper is called from inside a lambda.
- **Building the list of cheats.** A version that listed every `Cheat`
  (`flatMap` over the track, `filter` of the diamond to track positions)
  and counted the ones saving enough took 36.6 s; counting start by start
  without the list, 23.1 s.

Fix, beyond those: an array with constant-time indexing for grids (item
2), and let `main` share the searches between the parts.

### 6. Proofs

Easy: 505 lines, and each file checked on the first to third try. Times
(160 lines) is day 18's `boundAlong` and day 16's `boundToEnd` adapted,
and gets the fastest times from S and to E for any track from day 16's
`distancesCorrect`. This is the third day to use that theorem, and the
first to use it twice. What made it work:

- The reach predicates put "on track" in (`FromStart`, `ToEnd`), so a
  position the search settles is on track, which the spec's cheat end
  needs and a race (which checks only where it moves to) doesn't give.
- A `match` on `fromStart.get start` refined both the goal and the
  hypotheses through the program's own `match`es (`countedFrom`,
  `savesFrom`, `countCheats`), so no unfolding lemmas were needed where a
  `match` was possible; two remain where the fact comes from a lemma
  (`countedFromSome`, `savesFromSome`).
- `omega` with `Nat.absDiff` unfolded by `rfl` equations (`rowDistance`
  and so on) proved the diamond's bounds both ways.

Friction: stating "the number of cheats" without a cardinality (item 2),
and spelling out each `Nat.absDiff` as `(a - b) + (b - a)` for `omega`,
four `let`s per proof. Lean's `omega` front end rewrites `Int.natAbs`
itself (the ``Int.natAbs`` case in
<https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Omega/Frontend.lean>).

### Size and time

Release build, load average 25 to 44:

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2024.Day20.Proofs` | 4.4 s user (10.1 s) |
| `stitchwort check --no-cache Aoc.Year2024.Day20` | 2.0 s user (3.3 s) |
| `stitchwort test --no-cache Aoc.Year2024.Day20` (23 tests) | 6.8 s user (12.9 s) |
| `stitchwort test Aoc.Year2024.Day20` (warm) | 1.2 s user |
| `stitchwort run Aoc.Year2024.Day20.main -- 50` on the example | 0.73 s user |
| `stitchwort run Aoc.Year2024.Day20.main` on the generated track | 23.1 s user |
| Python on the generated track | 0.64 s user |

150 lines of program, 77 of spec, 505 of proofs, 93 of tests.

### Ranked

1. A `let` used in a `match` arm inside a lambda is recomputed on every
   call: 10 times slower here, silently (item 5). Fix: pass the `let`'s
   value into the lifted `match` helper as a capture.
2. The real input is pending: Matt's repository has no day 20. Fix: add
   his input, its tests and its two answer entries when he has it.
3. 23 s against Python's 0.64 s, mostly 7.5 million `Map` lookups and
   building the diamonds (item 5). Fix: an array with constant-time
   indexing in std; share the searches between the parts in `main`.
4. An effectful argument runs even where it isn't used:
   `.fold (Fail.fail usage) …` always fails (item 3). Fix: warn on an
   effectful argument for a pure parameter, or a thunk default for
   `Option.fold`.
5. `List.length` recurses and runs out of stack at 2 million frames
   (item 3). Fix: a loop, as `List.count` is.
6. Nine days define their own grid `Position`, `step` and `stepBack`
   (item 2). Fix: a std grid-position module with the Manhattan distance.
7. No cardinality for "the number of cheats"; the spec uses a distinct
   list (item 2). Fix: a std `Set.card` with `Iff`-based lemmas, or keep
   the distinct-list idiom and document it.
8. `rewrite` after a refining `match` says "found nothing" (item 3). Fix:
   name the `match` that already rewrote it.
9. `omega` needs `Nat.absDiff` unfolded by hand (item 6). Fix: teach
   `omega` `Nat.absDiff`.
