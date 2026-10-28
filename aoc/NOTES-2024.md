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

### 4. Missing `List.all`/`any` lemmas

Proved locally, each a few lines: `allTrue` (every element passes), `anyFalse`,
`allAnd` (`xs.all (x => p x && q x) = (xs.all p && xs.all q)`), and
`noneRelated` (`xs.all (x => !(ys.any (related x)))` is the same read with
`ys` outside). Fix: move them to std's toolkit.

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
