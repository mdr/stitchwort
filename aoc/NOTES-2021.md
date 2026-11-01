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
theorems about the parsed input with no hypothesis left. Days 5, 6 and 8
do; day 9's answers need no promise at all, and its parser's guarantees
(digits, a rectangle) are proved anyway. The pattern:

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
