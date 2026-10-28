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
