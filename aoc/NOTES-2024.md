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
