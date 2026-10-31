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
  parser checks it, but no theorem says the parser's output satisfies it.
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
