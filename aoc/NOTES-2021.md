# Friction report: Advent of Code 2021 in Stitchwort

What was awkward, missing or surprising while writing 2021's days (in
`aoc/src/Aoc/Year2021/`), day by day, in the format of
[NOTES-2024.md](NOTES-2024.md). The inputs are Matt's, from his Scala
repository (github.com/mdr/aoc, `src/main/resources/aoc2021/`), committed in
`aoc/inputs/2021/`; the expected answers are his Scala solution's.

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
