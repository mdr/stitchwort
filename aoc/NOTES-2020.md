# Friction report: Advent of Code 2020 in Stitchwort

What was awkward, missing or surprising while writing 2020's days (in
`aoc/src/Aoc/Year2020/`), day by day, in the format of
[NOTES-2024.md](NOTES-2024.md). The inputs are Matt's, from his Scala
repository (github.com/mdr/aoc, `2020/src/main/resources/`), committed in
`aoc/inputs/2020/`; the expected answers are his Scala solution's. The point
of the track is to battle-test the language, std and `Aoc.Common` before
December, so each day records what got in the way, with code.

## Day 1: Report Repair

An expense report, one number per line. Part 1 multiplies the two entries
that sum to 2020, part 2 the three. Answers on Matt's input: 1016619
(1069 × 951) and 218767230 (473 × 405 × 1142); the example gives 514579 and
241861950. All four match Matt's Scala (`sbt "runMain aoc.day1.Day1"`, run on
a copy of his repository), and a brute-force `awk` over the input finds
exactly one pair and one triple.

The program came out right on the first run, and so did all 14 tests,
including the guessed text of a parse error:

```stitchwort
def findPairAfter (target: Nat) (seen: Set Nat): List Nat → Option (Nat, Nat)
  | Nil => None
  | Cons x rest =>
    if x <= target ∧ seen.contains (target - x) then Some (target - x, x)
    else findPairAfter target (seen.insert x) rest

def findTriple (target: Nat): List Nat → Option (Nat, Nat, Nat)
  | Nil => None
  | Cons x rest =>
    match (if x <= target then findPair (target - x) rest else None) with
      | Some (b, c) => Some (x, b, c)
      | None => findTriple target rest
```

Part 1 is one pass with a set of the entries seen so far (O(n log n)); part 2
runs part 1's search after each entry (O(n² log n)) rather than trying n³
triples. The spec (`Spec/Spec.sw`) is the brute force: `List.pairs`, and a
`triples` written the same way, filtered by their sum. Run on the real input
the spec agrees: 19,701 pairs and 1,293,699 triples, about 1 s for the
triples in `stitchwort test`.

Proved, for every list of entries and every target (`Aoc.Year2020.Day01.Proofs`):

- `findPairSound`, `findTripleSound`: what the program finds are entries at
  different positions, in order (`(a, b) ∈ entries.pairs`,
  `(a, b, c) ∈ triples entries`), summing to the target.
- `findPairComplete`, `findTripleComplete`: it finds something whenever the
  spec has such a pair or triple.
- `part1Sound`, `part1Complete`, `part2Sound`, `part2Complete`: so the
  answer is one of the spec's (`part1Answers`, `part2Answers`), and `None`
  only when the spec has none.
- `part1Correct`, `part2Correct`: when the spec's answer is unique (the
  puzzle's promise, "the two entries"), the program's answer is it.

The invariant of the one-pass search is a small proposition,
`PairAhead before rest a b`: `a` already passed and `b` still to come, or
both still to come. Soundness and completeness are one induction each over
the list, with `seen` related to `before` by one direction of membership
each. 208 lines of proofs for 52 of program, written in about 25 minutes;
most proofs checked on the first or second try, the rest once the error
messages said what to change.

Breaking the program made the proofs fail: returning `(x, c, b)` instead of
`(x, b, c)` from `findTriple` fails `findTripleSound`, with the counterexample
`target = 1, entries = [0, 1, 0]`; returning `x + 1` as part 1's second entry
fails `findPairAfterSound` at `x = b`.

### 1. No `List.combinations`, so the spec writes `triples`

Part 1's spec is `entries.pairs`; for part 2 std has nothing, so the spec has
its own:

```stitchwort
def triples: List Nat → List (Nat, Nat, Nat)
  | Nil => Nil
  | Cons x rest => (rest.pairs |> .map (((y, z)) => (x, y, z))) ++ triples rest
```

Scala's `entries.combinations(3)` (Matt's solution uses it for both parts),
Haskell's `subsequences` filtered by length, and Python's
`itertools.combinations` all have it. A std `List.combinations (k: Nat):
List a → List (List a)` (every choice of `k` elements, in order) would make
both parts' specs one line, and come up again for any "choose k of these"
day. With it, a membership lemma (`ys ∈ xs.combinations k` iff `ys` is a
sublist of length `k`) so proofs can use it.

### 2. No lemmas about membership in `List.pairs` of a `Cons`

Std has `List.memPairs` (both halves of a pair are in the list) and
`List.lengthPairs`, but nothing that takes a pair of `pairs (Cons x rest)`
apart or puts one together. Every step of the search needs exactly that, so
the proofs do it by hand from the definition, `List.memAppend`,
`List.memMapElim` and `Pair.mkInjectiveFst`/`Snd`:

```stitchwort
    | Inr inPairs =>
      match List.memAppend (a, b) (List.map rest (y => (x, y))) (List.pairs rest) inPairs with
        | Inl inMap =>
          match List.memMapElim (y => (x, y)) (a, b) rest inMap with
            | Witness y (Both yIn made) =>
              let xIs: x = a := Pair.mkInjectiveFst _ _ _ _ made
              let yIs: y = b := Pair.mkInjectiveSnd _ _ _ _ made
              Inr (Inl (Both (Inl xIs) (rewrite <- yIs in yIn)))
        | Inr inRest => Inr (Inr inRest)
```

`findTripleComplete` repeats the same dance for `triples`. Std candidates,
beside `memPairs` in `List/Lemmas.sw`:

```stitchwort
theorem List.memPairsCons (p: (a, a)) (x: a) (rest: List a):
    Iff (p ∈ List.pairs (Cons x rest)) (Or (And (p.fst = x) (p.snd ∈ rest)) (p ∈ List.pairs rest))
```

and the more general `List.memMapPair`: `(x, y) ∈ xs.map (z => (c, z))` iff
`x = c` and `y ∈ xs`.

### 3. `let f (y: Nat) …` is a parse error that doesn't point at `def`

A helper for one case of a proof, written the obvious way:

```stitchwort
        let passedNow (y: Nat) (contained: Set.contains (Set.insert seen x) y = True): y ∈ Cons x before :=
          if h: y = x then Inl (Eq.sym h) else Inr (passed y …)
```

```
[E-PARSE] Error: expected `:=`, but found `(`
 44 │         let passedNow (y: Nat) (contained: Set.contains (Set.insert seen x) y = True): y ∈ Cons x before :=
    │                       ╰── expected `:=`, but found `(`
```

The language has local definitions for this (`def passedNow (y: Nat) …`
inside the block, syntax.md "Local definitions"), and the error message for
`rewrite` even recommends them, but this message doesn't say so. I wrote the
lambda form instead, `let passedNow: (y: Nat) → … := y contained => …`, which
restates every parameter's type in the arrow. Fix: when a `let` name is
followed by a parameter, say "a `let` binds a value; for a function write a
local `def passedNow (y: Nat) …: T := …`, or `let passedNow := (y: Nat) => …`".

### 4. `Exists` isn't in the prelude, `And` and `Or` are

Taking apart the `Exists` that `List.memMapElim` returns:

```
[E-UNKNOWN-NAME] Error: unknown name `Witness`
    │ Note: the library has `Std.Exists.Witness`: write it in full, or `import Std (Exists)`, or `import Std.Exists (Witness)`
```

The message is good and the fix is one import. It is a small surprise all
the same: `And` (`Both`) and `Or` (`Inl`, `Inr`) are in the prelude, and
std's membership lemmas hand back an `Exists` as often as an `Or`, so any
proof that uses `memMapElim` or `memFilterMapElim` needs `import Std
(Exists)`. Putting `Exists` in the prelude beside `And` and `Or` would
remove it.

### 5. The counterexample search can't satisfy `found = Some answer`

`stitchwort audit Aoc.Year2020.Day01` warns about two theorems:

```
! Aoc.Year2020.Day01.Proofs.part1Sound
    warn: no input made the hypotheses true (0 of 10000 cases): if they contradict each other, the theorem is vacuous
! Aoc.Year2020.Day01.Proofs.part2Sound
    warn: no input made the hypotheses true (0 of 7956 cases): if they contradict each other, the theorem is vacuous
audited 29 theorems: 0 failed, 2 with warnings, 27 passed
```

The hypothesis is `solvePart1 entries = Some answer`: random lists of small
numbers almost never have two entries summing to 2020, and an independent
random `answer` would have to be their product as well. The hypotheses are
narrow, not contradictory; the real input satisfies them (the tests). With
`--counterexamples --verbose`, 6 of the 16 theorems gave up this way,
including `findTripleSound` until the program was broken (then it found the
counterexample quickly, with `target = 1`). A hypothesis of the form
`f x = y` with `y` a variable could be satisfied by computing `y := f x`
after generating `x`, and one of the form `f x = Some y` the same way when it
is `Some`; that would turn these warnings into real evidence. The days that
search for something summing to a fixed target will keep hitting this.

### 6. Smaller things

- **Refined hypotheses.** Inside `match c: (x <= target && …) with | True
  =>`, I first wrote `rewrite c at found in found` to get the `if` in
  `found` to compute. It is unnecessary, since a `match` refines the
  hypotheses as well as the goal, and the `E-REWRITE-NOTHING` says so in its
  fifth note ("so `found` is already refined: use it as it is"). That is the
  right fix, but it comes after four notes about how the search compares
  terms and a sixth about the inner `match` of `Map.contains`, with a
  source excerpt from `std/Map/Map.sw`. When the scrutinee is the `match`'s
  own, the refinement note should come first, or alone. The proving guide's
  `match` advice doesn't mention it either.
- **Goals list pattern variables after hypotheses that use them.** In the
  `Cons x rest` arm of `findPairAfterSound`, the goal shows `found: (if x <=
  target && …)` and only then `x: Nat`, `rest: List Nat`: the arm's pattern
  variables come after the hypothesis whose type mentions them, as if they
  were bound later. Reading the goal, `x` looks free in `found`.
- **A pair pattern is needed to compute a nested `match`.** In
  `findTripleNoneCons`, `match pair: findPair … with | Some found =>` leaves
  the hypothesis stuck at `(match …) target x rest (Some found) = None`,
  because `findTriple`'s `match` has the arm `Some (b, c)`; writing `| Some
  (p, q) =>` computes it. Fair (pairs have no eta), and the message shows
  the stuck `(match …)`, but it took a moment to see why.
- **Proofs restate the program's condition.** `match c: (x <= target &&
  Set.contains seen (target - x))` copies the program's `if`, so changing
  the condition (`x <= target + 1`) breaks the proofs with type mismatches
  rather than a counterexample. The generated `findPairAfter.eq2.ifTrue`
  restates it too. An `if` that a proof could split by name
  (`cases findPairAfter.eq2` on the condition, without writing it) would
  keep proofs about a program from repeating its text.
- **`Option` answers print as numbers.** `main` prints
  `(solvePart1 entries).orFail "no two entries sum to 2020"` inside the
  string interpolation, and the tests compare with `Ok (Some 1016619)`. Both
  read well.

### After SW-1235 (Matt, 4 Nov 2026)

- **Item 1:** `Aoc.Common.Grid` carries a proof that its first row has a
  cell, `nonEmpty: (firstWidth rows == 0) = False` (an equation, so grids
  keep `==` and the counterexample search can make them), and
  `Grid.widthNonZero: grid.width ≠ 0` follows. `auto` doesn't search a
  record's fields, but it does use a `let`-bound proof in scope, so
  `let nonZero := map.widthNonZero` and then `step * slope.right % map.width`
  checks, with no `wrap`. `parseGrid` refuses an empty map ("expected a grid,
  got no cells"); a literal grid is `Grid.of rows`, which finds the proof.
  `Cave` (2021 day 15) carries the same field, and `Cave.of`.
- **Item 3:** `Grid.isRectangle: Bool` with `isRectangleIff`; `treesOnSpec`,
  `part1Correct` and `part2Correct` take `map.isRectangle = True` (the same
  statement, by `isRectangleIff`), and `check --counterexamples` now searches
  them (none found in about 5000 cases; with `List.rangeFrom map.height 0`
  it finds `map = { rows = [[Tree]], nonEmpty = rfl }, slope = { right = 0,
  down = 1 }` at once).
- **Item 4:** `List.takeWhileMap` and `List.takeWhileRangeCutoff` are in std
  (List/Lemmas.sw), `checkGridRows` is in `Aoc.Common.Proofs`; both
  messages are improved (a note on a `Bool` function found as a `Prop`
  function; no "build it by its fields" suggestion for a constructor with no
  fields). `<=` for `<` in `treesOn` is no bug (the extra step looks up a
  square off the map, which is `Open`), though the proof fails on the shape.

### Size and time

CPU time (the machine had a load average near 100 while this was measured,
so wall-clock times meant nothing):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day01.Proofs` | 4.9 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day01` | 3.1 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day01` (14 tests) | 5.9 s user |
| `stitchwort audit Aoc.Year2020.Day01` (29 theorems) | 3.1 s user |
| `stitchwort run Aoc.Year2020.Day01.main` on the input | 0.5 s user |

52 lines of program, 22 of spec, 208 of proofs, 53 of tests. About 30
minutes from reading the puzzle to the proofs checking.

### Ranked

1. The counterexample search gives up on hypotheses like `solvePart1 entries
   = Some answer` (item 5), so the audit warns on sound theorems and can't
   find a counterexample to them. Missing feature; medium (compute
   equation-defined variables from the others in the generator, a day or
   two).
2. No `List.combinations` (item 1). Missing library; small (the function,
   a test, length and membership lemmas: an hour or two).
3. No membership lemmas for `List.pairs` of a `Cons` (item 2). Missing
   library; small (two lemmas, under an hour).
4. `let f (y: Nat) …` gives a bare `E-PARSE` with no pointer to local
   `def` (item 3). Error message; small (a note on the parse error).
5. `E-REWRITE-NOTHING` buries "already refined by the `match`" as its fifth
   note (item 6). Error message; small.
6. Goals list an arm's pattern variables after the hypotheses that mention
   them (item 6). Bug in goal display; small.
7. `Exists` isn't in the prelude beside `And` and `Or` (item 4). Missing
   feature; small (a prelude entry).

## Day 2: Password Philosophy

A password database, one entry per line: `1-3 a: abcde`. Part 1 reads the
policy as the fewest and most times the letter may appear in the password,
part 2 as two positions counting from 1, exactly one of which must hold the
letter; each counts the passwords that keep their policy. Answers on Matt's
input: 603 and 404; the example gives 2 and 1. All four match Matt's Scala
(`sbt "runMain aoc.day2.Day2"`, run on a copy of his repository), and an
`awk` one-liner over the input agrees.

The program is a parser and two checks on a record:

```stitchwort
type Entry = { low: Nat, high: Nat, letter: Char, password: Text }

def line(): {Parse} Entry :=
  let low := nat()
  char '-'
  let high := nat()
  char ' '
  let letter := satisfy "a lowercase letter" Char.isAsciiLowercase
  text ": "
  let password := takeWhile1 "a password" Char.isAsciiLowercase
  { low, high, letter, password }

def Entry.letterAt (entry: Entry) (position: Nat): Bool :=
  match position with
    | Zero => False
    | Succ index => entry.password.toList.get index == Some entry.letter

def Entry.validByPosition (entry: Entry): Bool := entry.letterAt entry.low != entry.letterAt entry.high
```

It ran right the first time, and so did all 17 tests, including three
guessed parse errors (`"line 1, column 8: expected a password, got the end of
the line"`). The spec (`Spec/Spec.sw`) says each policy in the puzzle's
words: part 1 counts with `filter` and `length` where the program uses
`List.count`; part 2 numbers the characters from 1 with `List.withIndexFrom
1` and asks whether `[low, high].filter (holdsLetter entry)` has exactly one
element, where the program indexes with `get (position - 1)` and compares
two `Bool`s.

Here the program is close to the spec, so the theorems are about what could
go wrong: counting from 1, "exactly one", and the parser. Proved
(`Aoc.Year2020.Day02.Proofs`):

- `validByCountSpec`, `validByPositionSpec`: each check is the spec's, for
  every entry, including positions 0 and past the end of the password and
  `low = high` (which the spec's `[low, high]` counts twice, so never
  "exactly one", as the program's `!=` says).
- `part1Correct`, `part2Correct`: so the answers are the spec's, for every
  list of entries.
- `letterAtSpec`: indexing from 1 by `get` is the spec's numbered
  characters (from `holdsGet` and `holdsNothingBefore`, inductions over the
  password with the start of the numbering general).
- `parseWritten`: if `parseEntries` reads the input as `entries`, there is
  one entry per line, and each line is its entry written out: digits whose
  value is `low`, `-`, digits for `high`, a space, the letter (lowercase), `:
  `, and the password (one or more lowercase letters). Nothing is dropped,
  added or changed. Digits rather than `Nat.toText`, since `01-3 a: abc`
  parses too.

Not proved: that every well-formed line parses (std's `Parse.Reads` is
soundness only). 59 lines of program, 27 of spec, 114 of proofs, 57 of
tests. Breaking the program made the proofs fail: `entry.low < times` fails
`validByCountSpec` with the counterexample `{ low = 0, high = 0, letter =
'a', password = "" }`; `get (Succ index)` (counting from 0) fails
`letterAtSpec`, `validByPositionSpec` and `part2Correct`, with
counterexamples; `text ":"` fails `readsLine`.

### 1. A named parser has to be restated in its proof

The proof that `line` reads `Written` text chains std's lemmas with
`Parse.readsBind`, one per step. Inside the chain every parser and
continuation is inferred from the expected type, but not at the top, where
the expected type is `Parse.Reads line Written`:

```stitchwort
theorem readsLine: Parse.Reads line Written :=
  Parse.readsWeaken line _ _
    (Parse.readsBind _ _ _ _ Parse.readsNat (low => …
```

```
[E-TYPE-MISMATCH] Error: type mismatch
 29 │       _ _ Parse.readsNat (low =>
    │           ╰──────── expected `(state: Parse.State) → (value: Nat) → (after: Parse.Mark) → state.at.left = List.length state.at.rest → Parse.runFrom state (arg => …) = Ok (value, after) → ∃ (read: List Char) => … = … ∧ … ∧ …`, but this has type `Parse.Reads Parse.nat (read n => …)`
```

Unifying `line` with `() => ?j (?p())` needs `line` unfolded, and it isn't.
The fix is to write the continuation out, the parser's body less its first
line, eight lines copied from the program:

```stitchwort
    (Parse.readsBind Parse.nat
      (low =>
        Parse.char '-'
        let high := Parse.nat()
        …
        { low, high, letter, password })
      _ _ Parse.readsNat (low =>
      Parse.readsBind _ _ _ _ (Parse.readsChar '-') (u1 =>
      …
```

Without `line` as `readsWeaken`'s first argument it fails the same way, one
level up (`Parse.Reads ?1 Written`). Two costs: the program's text is in the
proof, so changing the parser breaks the proof with a type mismatch at the
copy, not at what became false (`text ":"` did exactly that); and the
message shows both sides as unfolded `Reads` with `…`, never saying that the
named parser is what didn't unfold. Day 16 of 2021 copies its parser the
same way. Unfolding a definition's body when a higher-order pattern
(`() => ?j (?p())`) meets its name would remove it; failing that, a note on
the mismatch ("`line` would have to be unfolded: give `readsBind` the parser
and its continuation").

Once past that, the rest went better than expected: the chain inferred
every spec, and the proof that the nested `Parse.Then` is `Written`, seven
levels of `Witness` taken apart and one `rewrite` of all the splits, checked
the first time.

### 2. `Text` has no `count` or `get`

Both checks go through the characters:

```stitchwort
  let times := entry.password.toList.count (== entry.letter)
  …
    | Succ index => entry.password.toList.get index == Some entry.letter
```

Scala's `password.count(_ == c)` and `password(i)` work on the string. std's
`Text` has `length`, `take`, `drop`, `contains` and the splitters, but not
`count`, `get` (or `charAt`), `any`, `all` or `filter`, so any day that looks
at characters writes `.toList` first. Cheap at run time and harmless in
proofs (`Text.toList (Text.fromList cs)` computes), but it reads as
plumbing. `Text.count`, `Text.get` and `Text.any`/`Text.all`, defined
through `toList` with a lemma each saying so, would cover it.

### 3. Searching for `(a == a) = True` at `Nat` misses `DecEq.refl`

Looking for the lemma that `start == start` is `True`:

```
$ stitchwort search '((?a: Nat) == ?a) = True'
 1. Aoc.Year2025.Day07.Proofs.natEqSelf  theorem · instance · conclusion
 2. Aoc.Common.Proofs.equalOf  theorem · instance · conclusion
 3. Aoc.Year2024.Day12.Proofs.eqTrue  theorem · instance · conclusion
```

and `Std.DecEq.refl` isn't among the 34 lines at all; `stitchwort search '(x
== x) = True'` ranks it first. At `Nat` the pattern's `==` is
`Nat.decEq`, and `DecEq.refl`'s is the instance argument, which the search
doesn't fill in. Three projects' local copies suggest the others missed it
the same way. (In the end `cases` closed the goal without it.)

### 4. Smaller things

- **`cases` did the Boolean bookkeeping.** `exactlyOne (p: Nat → Bool) (x:
  Nat) (y: Nat): ((p x != p y): Bool) = (([x, y].filter p).length == 1) :=
  cases` split on `p x` and `p y` and closed all four; `holdsGet`'s cases
  closed `(start == start && c == letter || …) = (Some c == Some letter)` and
  `start == start + index + 1` being `False` without a lemma.
- **`!=` in a statement is the proposition.** I first wrote `(p x != p y) =
  (…)`; the `E-NOT-A-TYPE` says exactly what to write
  (`((x != y): Bool)`). Good message; a small trap all the same, since in the
  program the same `!=` is the `Bool`.
- **A parser named `entry` made every `entry =>` warn.** With the parser
  first called `entry`, `List.countCongMem entries _ _ (entry m => …)` in the
  proofs gave `W-LAMBDA-SHADOW` ("hides the function
  `Aoc.Year2020.Day02.entry`"), through the `import Aoc.Year2020.Day02 (..)`.
  I renamed the parser `line`. The warning is aimed at `entry m => …` meant
  as `entry (m => …)`, which can't be meant when `entry` takes no arguments.
- **No `Nat.ltSuccSelf` or `Nat.zeroLtSucc`.** I guessed both names; the
  `E-UNKNOWN-NAME` suggested `leqSuccSelf` and `zeroNotSucc`. `omega` was the
  answer for each, as the proving guide says.
- **Weak evidence again.** `holdsGet` takes `position = start + index`, and
  the counterexample search gives it "weak evidence" (hypotheses true only
  up to size 9); the same shape as day 1's item 5, a variable defined by an
  equation, which the generator could compute instead of guessing.
- **The parser proof is most of the check.** `stitchwort check --no-cache
  Aoc.Year2020.Day02.Proofs` takes 5.8 s user, 4.6 s of it `readsLine`
  (1.2 s without `Parse.sw`): seven `readsBind`s on a seven-step parser.
- **Row types without brackets.** `def parseEntries (input: Text): {Fail}
  List Entry` (D2307) reads well, and `stitchwort fmt` leaves it alone.

### Size and time

CPU time (load average over 100, so wall-clock times meant nothing):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day02.Proofs` | 5.8 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day02` | 1.2 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day02` (17 tests) | 5.7 s user |
| `stitchwort audit Aoc.Year2020.Day02` (13 theorems) | 1.2 s user |
| `stitchwort run Aoc.Year2020.Day02.main` on the input | 0.4 s user |

About 15 minutes in all, from reading the puzzle to the proofs checking,
besides a 3-minute build of the CLI.

### Ranked

1. A proof about a named parser has to restate its body for
   `Parse.readsBind` (item 1), so parser proofs copy the program and break
   at the copy. Missing feature (unfold a definition when a higher-order
   pattern meets it), medium; or an error message, small: say which name
   didn't unfold and what to pass.
2. `Text` has no `count`, `get`, `any`, `all` (item 2). Missing library;
   small (four definitions through `toList`, a lemma each, an hour).
3. `stitchwort search` at `Nat` misses the generic `DecEq.refl` (item 3),
   and projects grow copies of it. Bug in search; small to medium (match a
   concrete `decEq` against an instance argument).
4. `W-LAMBDA-SHADOW` fires for a function that takes no arguments, through
   an `(..)` import (item 4). Error message; small (warn only when the
   shadowed function could take the lambda).
5. The counterexample search guesses equation-defined variables (item 4,
   and day 1's item 5). Missing feature; medium, as on day 1.
6. `readsLine` is 4.6 s of a 5.8 s check (item 4). Performance; unknown
   size, worth a profile before the bigger parsers of later days.

## Day 3: Toboggan Trajectory

A map of open squares (`.`) and trees (`#`) that repeats to the right
without end. A toboggan starts at the top left and moves on a slope, so many
columns right and rows down at each step, until it goes past the bottom.
Part 1 counts the trees met on the slope right 3, down 1; part 2 multiplies
the counts on five slopes. Answers on Matt's input: 276 and 7812180000
(100 × 276 × 85 × 90 × 37); the example gives 7 and 336. All four match
Matt's Scala (`sbt "runMain aoc.day3.Day3"`, run on a copy of his
repository), and an `awk` brute force over the input agrees slope by slope.

The program parses with `Aoc.Common.parseGrid` and counts steps, looking
squares up through `Grid.lookupOr`, with the column wrapped to the map's
width by `%` (a `Grid` has a column, `Grid.widthNonZero`, SW-1235):

```stitchwort
def treesOn (map: Grid Square) (slope: Slope): Nat :=
  let nonZero := map.widthNonZero
  let find := map.lookupOr Open
  List.rangeFrom map.height 1
    |> .takeWhile (step => step * slope.down < map.height)
    |> .count (step => find { row = step * slope.down, column = step * slope.right % map.width } == Tree)
```

(The first version matched on the width in a `wrap` helper; items 1, 3 and 4
below were fixed afterwards, see "After SW-1235".)

It printed the right answers on the first run, and 15 of the 16 tests passed
the first time (the one that didn't guessed a parse error's wording). The
spec (`Spec/Spec.sw`) has no `%`: a row of the endless map is its pattern,
and past the pattern's end the square is the one a pattern's width to the
left (`repeatingAt`, a `decreasing` recursion); the path is the start moved
along the slope, then moved again "from there, and so on" (`path`, written
with a list spread, `[next, ..path slope next more]`), cut where it goes
past the bottom with `takeWhile`; the count is `filter` and `length`.

Proved (`Aoc.Year2020.Day03.Proofs`):

- `treesOnSpec`: on every rectangular map, for every slope, `treesOn` is the
  spec's count, including slopes that go 0 rows down or 0 columns right, and
  maps with no columns (no longer: a map has a column, SW-1235).
  `part1Correct`, `part2Correct` follow.
- `repeatingAtMod` (and, in the first version, `repeatingAtWrap`; now
  dropped with `wrap`): the repeating row is the pattern at
  the column's remainder, so `wrap` is right; `lookupSquareAt`: the
  program's lookup at the wrapped column is the spec's square.
- `pathRange`: the spec's path, step after step, is the start plus 1, 2, …
  steps, which is what the program counts.
- `visitedEnough`: the spec's own bound loses nothing. It takes as many
  steps as the map has rows before cutting at the bottom; on any slope that
  goes down, more steps visit the same positions.
- `parseWritten`: if `parseMap` reads the input as `map`, each line is its
  row written with `.` and `#`, nothing dropped, added or changed;
  `answersCorrect`: on any input the parser reads, both answers are the
  puzzle's (the parsed map is a rectangle, by `Aoc.Common`'s
  `parseGridRectangle`).

Not proved: that every well-formed map parses (`Parse.Reads` is soundness
only, as on day 2). The theorems take `map.Rectangle` because the spec
repeats each row by its own length and the program wraps by the first row's;
on a ragged map they differ, and the puzzle's maps are rectangles. With
`slope.down = 0` both sides stop after as many steps as the map has rows,
which the puzzle never asks for (`visitedEnough` needs `0 < slope.down`).

Breaking the program made the proofs fail: `step * slope.down <= map.height`
and `List.rangeFrom map.height 0` (counting the start) both fail
`treesOnSpec` with a type mismatch; `wrap` as `(column + 1) % Succ less`
fails `repeatingAtWrap` with the counterexample `pattern = [Open, Tree],
column = 0`.

Most proofs checked on the first try. 60 lines of program, 60 of spec, 155
of proofs, 64 of tests; about 30 minutes from reading the puzzle to the
audit, besides a 2-minute build of the CLI.

### 1. `%` by the map's width needs a proof, and an `if h:` around the program loses its equation

`x % map.width` doesn't check: `E-AUTO-STUCK`, since nothing says the width
isn't 0. The obvious fix, in the program:

```stitchwort
def treesOn (map: Grid Square) (slope: Slope): Nat :=
  if nonEmpty: map.width ≠ 0 then
    …
      |> .count (step => find { row = …, column = step * slope.right % map.width } == Tree)
  else 0
```

checks and runs, but then can't be proved about:

```
Not generated:
  Aoc.Year2020.Day03.treesOn.eq.ifTrue  its branch uses the proof `h` of a condition that isn't an equation in a type with `DecEq` (or a comparison): two proofs of it aren't known to be equal without proof irrelevance (D2180)
```

The branch's `%` holds the `if`'s proof, so a lemma stated with its own
`nonEmpty` is about a different term, and matching on `map.width` in the
proof computes the `if` but leaves the program's proof inside the `%`. The
way out was a `wrap` that matches on the width, so the `%` is by `Succ less`
and `auto` proves it by computing. It reads as plumbing in the program, and
its doc has to explain why it is there. Three fixes, any of which would
have done: `%` total, with `x % 0 = x` as in Lean (a language decision);
a std `Nat.wrap`-like function with this definition and its lemmas; or a
`Grid` whose width is known not to be 0 (`parseGrid` already proves it,
`parseGridRectangle`, but the type doesn't carry it).

### 2. The same parser written two ways isn't the same term

`square` was first written as day 2's parser was:

```stitchwort
def square(): {Parse} Square :=
  let char := Parse.satisfy "'.' or '#'" (char => char == '.' || char == '#')
  if char == '#' then Tree else Open
```

Its proof restates the parser for `Parse.readsMap`, as on day 2 (item 1
there), as `() => f (p())` with `f` the `if`. That fails:

```
[E-TYPE-MISMATCH] Error: type mismatch
    │ ╰── expected `(state: Parse.State) → (value: Square) → … → Parse.runFrom state (arg => …) = Ok (value, after) → ∃ (read: List Char) => … = … ∧ … ∧ …`, but this has type `Parse.Reads (arg => Std.Effect.bind (Parse.satisfy "'.' or '#'" (char => … || …)) (x => Done (if … then … else …))) (read value => …)`
     ├─[ std/Parse/Parse.sw:135:18 ]
    │     Note 2: `(match …)` is a `match` written inside `Parse.runFrom`, marked "this `match`" above; … To state a lemma about it, make it a local `def` …
```

The same parser written `Square.ofChar (Parse.satisfy …)`, or `(char => if
… then Tree else Open) (Parse.satisfy …)`, checks, with the `||` lambda
inline too. So it is the `let` followed by an `if` in an effectful body
that elaborates to something other than `f (p())` (presumably the `Done`
goes into each branch). Nothing in the message says that: it shows both
sides as unfolded `Reads` with the difference elided, and its note points
at a `match` in std's `Parse.runFrom`, which is a red herring. I renamed the
pieces (`isSquare`, `Square.ofChar`) and wrote `square` as one application,
so the program's shape is chosen for its proof. Day 2's item 1 (unfold a
named parser when a higher-order pattern meets it) would remove this too;
failing that, a note on the mismatch naming the first place the two terms
differ.

### 3. `Grid.Rectangle` makes the main theorems unsearchable for counterexamples

`Grid.Rectangle` is a `Prop` over membership (`(row: List a) → row ∈
grid.rows → row.length = grid.width`), so the counterexample search can't
decide it, and every theorem that takes it is "not applicable":

```
  - Aoc.Year2020.Day03.Proofs.treesOnSpec   not applicable: nothing decides `(row: List Aoc.Year2020.Day03.Square) → row ∈ map.rows → Std.List.length row = …`
```

So breaking `treesOn` (`<=` for `<`) gives only a type mismatch, whose two
sides differ in the elided part:

```
expected `List.foldLeft (List.takeWhile (List.rangeFrom … 1) (step => …)) 0 (n x => Nat.succIf n …) = List.count (List.takeWhile (List.rangeFrom … 1) (x => …)) (x => Std.Decidable.toBool …)`, but this has type `List.count (List.takeWhile (List.rangeFrom … 1) (step => …)) (x => …) = List.count (List.takeWhile (List.rangeFrom … 1) (step => …)) (x => …)`
```

The breakage that went through a theorem without `Rectangle`
(`repeatingAtWrap`) got a counterexample at once. A decision procedure for
a `∀` over list membership (the list is finite), or a `Bool`
`Grid.isRectangle` beside the `Prop`, would make these searchable. Separately,
a mismatch message could show where its two sides first differ, as the
test runner does ("first difference at …").

### 4. Smaller things

- **Std lacks `List.takeWhileMap`.** `(xs.map f).takeWhile p =
  (xs.takeWhile (x => p (f x))).map f`, four lines by induction and `cases`;
  a std candidate beside `List.countMap`. So does the lemma that a
  `takeWhile` over `List.rangeFrom` stops at a cutoff past which nothing
  passes (`takeWhileRangeCutoff`, used by `visitedEnough`).
- **`checkGrid` keeps its rows, but `Aoc.Common.Proofs` doesn't say so.**
  `checkGridOk` proves the grid is a rectangle and uses `rows = grid.rows`
  inside; the parser proof needs that fact, so `checkGridRows` restates it
  (ten lines). An `Aoc.Common.Proofs` candidate, or better a
  `parseGridReads` that hands on the rows' `Parse.Each` for any cell spec.
- **A lambda with `<` is a `Prop` without an annotation.** `let below :=
  (position: Position) => position.row < map.height` made `takeWhileMap
  onPath below …` fail with "expected `Position → Bool`, but this has type
  `Position → Prop`"; `let below: Position → Bool := …` fixed it. Fair, but
  the message could say that the comparison is the `Prop` because nothing
  asked for a `Bool`, and suggest the annotation.
- **Braces after a nullary constructor.** `map.lookupOr Open { row = …,
  column = … }` is "braces after `Open` as an argument need brackets",
  suggesting `(Open { … })` among the fixes, though `Open` has no fields.
  `Ok { rows = … }` in a test got a better one: `E-UNKNOWN-FIELD`, "to
  build the `Aoc.Common.Grid` it holds, write `Ok ({ … })`".
- **The audit warns on `answersCorrect`** ("no input made the hypotheses
  true"), since random text almost never parses as a map: day 1's item 5
  again, for parse hypotheses. The real input satisfies it (the tests).
- **What went well.** List spreads in patterns and expressions read like the
  puzzle (`[next, ..path slope next more]`, `| [x, ..rest] =>`), and goals
  print them the same way. `stitchwort doc repeatingAt` listed the
  `decreasing` definition's `eq.ifTrue` / `eq.ifFalse.ifTrue` /
  `eq.ifFalse.ifFalse`, which proved `repeatingAtMod` on the first try.
  `stitchwort search` found `List.countFalse`, `Nat.modAddMod`,
  `Nat.leMulPos`, `DecEq.sound` and `Bool.falseOfNotTrue` as its first
  result each time. `Aoc.Common`'s `parseGrid`, `lookupOr`, `lookupOrAt` and
  `parseGridRectangle` fitted without change; the one thing a day like this
  might want from it is a wrapping lookup, and once is not enough to add it.
  The new `Text.get`/`count`/`any`/`all` weren't needed: the grid parser
  does the reading.

### Size and time

CPU time (load average about 70, so wall-clock times meant nothing):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day03.Proofs` | 7.9 s user |
| the same without `Proofs/Parse.sw` | 5.0 s user |
| `stitchwort check --no-cache Aoc.Common` (included in each of these) | 4.7 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day03` | 4.8 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day03` (16 tests) | 8.4 s user |
| `stitchwort audit Aoc.Year2020.Day03` (35 theorems) | 4.2 s user |
| `stitchwort check --counterexamples --verbose Aoc.Year2020.Day03.Proofs` | 2.6 s user |
| `stitchwort run Aoc.Year2020.Day03.main` on the input | 0.6 s user |

So the day's own proofs take about 0.3 s, the parser proof about 2.9 s, and
a cold check of `Aoc.Common`, which every Grid day pays, 4.7 s.

### Ranked

1. `%` by a width not known to be non-zero needs a proof, and an `if h:`
   around the program then has no `ifTrue` equation (item 1), so the
   program grows a `wrap` helper for its proofs. Missing feature or
   library; small for a std `Nat.wrap` with lemmas (an hour), medium for a
   `Grid` that carries its width, a language decision for a total `%`.
2. A parser written `let x := p(); if … then … else …` isn't the term
   `f (p())` its proof restates, and the message points at std (item 2).
   Error message, small (name the first difference); the real fix is day
   2's item 1, medium.
3. `Grid.Rectangle` is undecidable, so the counterexample search skips the
   main theorems, and a broken program gives only a mismatch with the
   difference elided (item 3). Missing feature, small to medium (a decision
   procedure for `∀` over list membership, or a `Bool` rectangle check);
   error message, small (show the first difference).
4. No `List.takeWhileMap` or `takeWhile` cutoff lemma in std; no
   `checkGrid` keeps-its-rows lemma in `Aoc.Common.Proofs` (item 4).
   Missing library; small (under an hour together).
5. A lambda with `<` infers `Prop`, and the mismatch doesn't suggest the
   annotation (item 4). Error message; small.
6. "Braces after `Open` … need brackets" suggests building a nullary
   constructor by its fields (item 4). Error message; small.
7. A cold check of `Aoc.Common` is 4.7 s of every Grid day's check (Size and
   time). Performance; unknown size, worth a profile.

## Day 4: Passport Processing

A batch file of passports: `key:value` fields separated by spaces or line
breaks, a blank line between passports. Part 1 counts the passports with
all eight fields, or all but `cid`; part 2 those whose values also keep a
rule for each field (`byr` four digits from 1920 to 2002, `hgt` a number
then `cm` or `in` in a range, `hcl` a `#` and six of 0-9 a-f, and so on).
Answers on Matt's input: 200 and 116; the example gives 2 and 2 (part 2's
four invalid and four valid examples give 0 and 4). All match Matt's Scala
(`sbt "runMain aoc.day4.Day4"`, run on a copy of his repository), and an
`awk` with the puzzle's rules as regular expressions agrees. The input has
no duplicate keys and no keys outside the eight.

The program parses each field's key into an enumeration with `Parse.pick`,
keeps the value as `Text`, and checks the values with `Text` functions:

```stitchwort
def field(): {Parse} Field :=
  let key := Parse.pick (keys.map (key => (key.code, key)))
  Parse.char ':'
  let value := Parse.takeWhile1 "a value" isValueChar
  { key, value }

def fieldBreak(): {Parse} () := Parse.oneOf [() => Parse.char ' ', Parse.newline]
def passport(): {Parse} Passport := { fields = Parse.sepBy1 field fieldBreak }
def parsePassports (input: Text): {Fail} List Passport := Parse.all input (() => Parse.sections passport)

def heightValid (value: Text): Bool :=
  match value.stripSuffix "cm" with
    | Some number => between 150 193 number.toNat
    | None =>
      match value.stripSuffix "in" with
        | Some number => between 59 76 number.toNat
        | None => False
```

It printed the right answers on the first run; 23 of the 25 tests passed the
first time (the two that didn't guessed parse errors' wording, items 3 and
4). The spec (`Spec/Spec.sw`) is about the fields as written, key by its
three letters: part 1 lists the eight expected keys and asks whether the
missing ones are none or just `cid`, where the program checks the seven
required keys; part 2's rules dispatch on the key's text and read each
value as characters: "four digits" is a length and `Parse.isDigit`, the
height splits off its last two characters with `take` and `drop` where the
program uses `stripSuffix` and `Text.toNat`, "exactly one of" the eye
colours is a `filter` of length 1 where the program uses `contains`.

Proved (`Aoc.Year2020.Day04.Proofs`):

- `validSpec`: each key's check is the puzzle's rule for that key's three
  letters, for every value, from one theorem per rule: `yearSpec` (for all
  bounds), `heightSpec`, `hairColorSpec`, `eyeColorSpec`, `passportIdSpec`,
  and `cid` by `rfl`. A key given the wrong code, or a rule attached to the
  wrong key, fails it.
- `hasRequiredSpec`: having the seven required keys is "all eight, or all
  but cid" (`allButCid`, for any `Key → Bool`, by `cases`), through
  `missingHas` and `codeEq` (no two keys share a code, by `Finite.check` on
  pairs of keys).
- `part1Correct`, `part2Correct`: so both answers are the spec's, for every
  list of passports.
- `toNatDigits`: `Text.toNat` is `Some` of the digits' value exactly when the
  text is one or more digits; `stripSuffixTwo`: removing a two-character
  suffix is `take`/`drop` of all but the last two characters, when those are
  the suffix.
- `parseWritten`: if `parsePassports` reads the input as `passports`, the
  input is the passports written out with a blank line between each two,
  then only line breaks; each passport is its fields with a space or a line
  break between each two, each field its key's code, `:`, and its value (one
  or more characters, none of them whitespace). Nothing dropped, added or
  changed.

Not proved: that every well-formed batch file parses (`Parse.Reads` is
soundness only, as on days 2 and 3). The spec counts a passport valid in
part 2 when every field it has keeps its rule, as the program does; the
puzzle doesn't say what a repeated key means, and the input has none.
Unknown keys don't parse, so neither side meets one.

Breaking the program made the proofs fail: `between 151 193` for the
centimetre range fails `heightChars` (at a `rewrite` that names `150 193`,
not with a counterexample: item 6); dropping `PassportId` from `required`
fails `allButCid` with the open case `has PassportId = False`; `char <= 'g'`
in `isHexDigit` fails `hairColorChars` with `E-REFL`.

114 lines of program, 75 of spec, 239 of proofs, 113 of tests. About 20
minutes from reading the puzzle to the proofs checking, by the clock, plus
a 3-minute build of the CLI; the proofs mostly went through on the first or
second try.

### 1. `Text.toNat` and `Text.stripSuffix` have no lemmas, and `stripSuffix` compares by `sameChar`

Part 2 is checks on text, and the natural program uses `Text.toNat`,
`Text.stripSuffix` and `Text.length`. std proves nothing about the first
two. `toNatDigits` needed the loop's own lemma first:

```stitchwort
theorem readDigitsAll: (acc: Nat) → (chars: List Char) →
    Text.readDigits acc chars = (if chars.all Parse.isDigit then Some (List.foldLeft (chars.map (digit => digit.digitValue.getOrElse 0)) acc (acc digit => acc * 10 + digit)) else None)
```

(it checked first time, 7 lines). `Parse.digitsValue` and `Parse.readsNat`
already say what `Parse.nat` reads, but nothing ties `Text.toNat` to them.

`stripSuffix` took seven lemmas, 45 lines: it reverses both texts and runs
`stripPrefixChars`, which compares characters with `Text.sameChar` (a
`Nat.equal` on the codes), not `==`, so a statement in the spec's terms
needs `sameCharEq: Text.sameChar c d = (c == d)` first, then a two-element
list's `==` taken apart (`pairEq`), then the reversal (`reverseTwo`,
`List.reverseReverse`) and `take`/`drop` of an append (`dropTwo`,
`takeTwo`). Along the way std had no "the heads of equal lists are equal"
(`List.consInjective` is for the tails); `Eq.cong (list => (list.get
0).getOrElse x)` did it. A std `Text.toNatSome` (as `toNatDigits` here) and
`Text.stripSuffixSome: text.stripSuffix suffix = Some rest ↔ text = rest ++
suffix`, with `stripPrefix`/`stripSuffix` defined through `==` (or a
`sameChar` lemma beside them), would have made part 2's proofs a few
rewrites.

### 2. `cases` after a `rewrite`, in an arm, can fail with `E-MATCH-MOTIVE` and the kernel's "`rfl` can't prove this"

In `yearChars` the goal after `rewrite betweenToNat …` is a Bool identity,
`(len == 4 ∧ True ∧ allDigits ∧ low <= n ∧ n <= high) = ((len == 4 ∧
allDigits) ∧ low <= n ∧ n <= high)`, with `n` a fold over `[char, ..rest]`:

```
[E-MATCH-MOTIVE] Error: this `match` can't be given a type: generalising its scrutinee makes the types it depends on ill-formed
 31 │   | [char, ..rest] => rewrite betweenToNat low high [char, ..rest] in cases
    │                                                                       ╰──── this `match`
    │ Note 1: the kernel's reason: `rfl` can't prove this
    │ Note 2: a top-level helper with a written signature can always do what this `match` would: define one and call it
```

The same proof, `cases` on the four Booleans as a lemma of its own
(`andShape (a b c d: Bool): (a ∧ True ∧ b ∧ c ∧ d) = ((a ∧ b) ∧ c ∧ d) :=
cases`), checked, and so did `passportIdChars` with `andIsSome`. In
`heightChars` the same `rewrite … in cases` shape worked. Presumably `cases`
split something stuck inside the fold (the head character's `48 <= Char.toNat
char`) whose generalisation breaks the term; the message doesn't say what it
split, and "this `match`" points at `cases`, which the reader didn't write
as a match. `cases` could skip a split it can't type and try the next, or
say what it was splitting.

### 3. A failure after a blank line is reported past it, as "expected the end of the input"

With a second blank line between two passports:

```stitchwort
test "two blank lines" := parsed "cid:1\n\n\ncid:2" == Err "line 4, column 1: expected the end of the input, got 'c'"
```

The mistake is line 3, an empty line where a passport should start. The
sections stop at the failed passport, `Parse.all`'s final line breaks take
all three, and the end is expected where `cid:2` starts. A batch file edited
by hand will have exactly this. The furthest failure (line 3, a key
expected) was nearer the start than where the final line breaks stopped,
so it lost. `Parse.all` could prefer a failure inside the last section, or
add "after a blank line, another section" as an expectation there.

### 4. `pick`'s message lists eight keys with seven "or"s

```
line 1, column 10: expected 'byr' or 'iyr' or 'eyr' or 'hgt' or 'hcl' or 'ecl' or 'pid' or 'cid', got 'abc'
```

I had guessed "expected 'byr', 'iyr', …, 'pid' or 'cid'", as English lists
them. Small, but every enumeration parsed with `pick` reads this way.

### 5. `BirthYear.valid "2002"` is "not in scope"

In the tests, `BirthYear.valid "2002"` (Scala's `BirthYear.validate(…)`) is

```
[E-UNKNOWN-NAME] Error: unknown name `BirthYear.valid`
 75 │ test "byr" := BirthYear.valid "2002" ∧ not (BirthYear.valid "2003")
    │               ╰───────── not in scope
```

with no note. It needs `Key.valid BirthYear "2002"`. A constructor name
followed by a field could resolve as dot notation on the constructor's
value, or the note could say "`BirthYear` is a `Key`: write `Key.valid
BirthYear`". The program itself had the same trap the other way:
`Passport.mk (…)` for a record is `E-UNKNOWN-NAME` ("has no `mk`"), printed
three times over for the one use; `{ fields = … }` is the way.

### 6. The counterexample search can't reach the height rule, and the audit warns on generated equations

With the centimetre range broken (`between 151 193`), `check
--counterexamples` finds nothing: "0 false, 29 with none found". Random
texts never spell `150cm`, so `heightSpec` and `validSpec` look fine. The
proof failed at a `rewrite` whose rule names `150 193`, which is luck: a
proof written with `betweenToNat _ _ …` would have failed in some less
direct way. The search could seed text generators with the literals in the
definitions it is checking (`"cm"`, `"byr"`, the bounds).

The same blindness gives the audit 11 warnings, all on compiler-generated
equations: `heightValid.eq.some` (hypothesis `value.stripSuffix "cm" = Some
number`), `hairColorValid.eq.alt1`, and the seven `Spec.validValue.eq.if…`
(hypotheses `(key == "byr") = True`, …), each "no input made the hypotheses
true … the theorem is vacuous". None is vacuous. Day 3 had one such warning,
on a theorem of its own; here they are 11 of 11, and they bury anything
real. The audit could leave generated equations out of the vacuity check,
or seed the search as above.

### 7. Smaller things

- **`readsThen` composes the whole parser proof.** Day 2's item 1 is gone:
  `readsField` is a `readsThen` chain over `Parse.readsPickBy`,
  `readsChar` and `readsTakeWhile1` that inferred every spec, and the
  passport, sections and `Parse.all` steps are one std lemma each
  (`readsSepBy1`, `readsSections`, `allReads`, `readsOneOf` for the field
  break). Two goals were left, a `rfl` and the `()` that ends a `List.All`.
  `readsPickBy` turned "the key read is in the table" into "the key's code
  was read", which is what the spec needed. 44 lines for the parser proof.
- **`cases` on two keys splits the codes, not the keys.** `codeEq (a b:
  Key): (a.code == b.code) = (a == b) := cases` is `E-CASES-BUDGET`: it
  split `a`, then `List.decEq … ['b', 'y', 'r'] (Text.toList (Key.code b))`
  and three more such comparisons before `b`. Splitting `b` first would
  have closed each of the 64 cases by computing. `Finite.check` on the pair
  did it in one line, as the note suggested, plus `DecEq.sound` to turn
  the `Bool` back into the equation.
- **"Exactly one of" seven colours took seven nested matches.**
  `eyeColorSpec` matches `"amb" == value`, `"blu" == value`, …, rewriting
  `value` in each `True` branch. A std lemma that on a list of distinct
  values `contains` is "filter has length 1" (or `count` is at most 1)
  would replace it. The last branch needed no rewrite: the earlier
  matches had already made the goal compute, and the `E-REWRITE-NOTHING`
  said so ("the goal already holds by computing").
- **No text patterns.** `hcl` matches `value.toList` against `['#',
  ..digits]`; a pattern like `"#" ++ digits` on `Text` would read as the
  puzzle does. And the two `match value.toList` (program and spec) are
  different hidden functions, so `hairColorSpec` is `rfl` only after
  matching the characters by the same pattern in the proof; the `E-REFL`
  note says exactly this.
- **An inner `match` hides the second `stripSuffix` from `rewrite`.**
  `rewrite stripSuffixTwo 'c' 'm' chars, stripSuffixTwo 'i' 'n' chars in …`
  found no `"in"` suffix, because it sits in the `None` arm's hidden match
  function; the note said so. Matching on the `cm` case first, then
  rewriting in its `False` arm, worked.
- **The first `stitchwort search` in a fresh worktree took over two minutes
  of wall clock** (`'List.filter (List.map _ _) _ = _'`; the shell's
  2-minute limit moved it to the background). The same search again took
  3.4 s user. It found `List.filterOfMap` first, which `missingHas` used.
- **The Text API helped where it existed.** `Text.length`, `Text.all` and
  `Text.toNat` read well in the program; the spec still writes
  `value.toList` for `take`, `drop` and patterns.

### Size and time

CPU time (load average about 70, so wall-clock times meant nothing):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day04.Proofs` | 4.5 s user |
| the same without `Proofs/Parse.sw` | 4.3 s user |
| the same with only `Proofs/Parse.sw` | 3.7 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day04` | 1.1 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day04` (25 tests) | 4.5 s user |
| `stitchwort check --counterexamples Aoc.Year2020.Day04.Proofs` | 4.3 s user |
| `task audit:touched -- Aoc.Year2020.Day04` (69 theorems) | 6.9 s user |
| `stitchwort run Aoc.Year2020.Day04.main` on the input | 0.5 s user |

So most of a cold check is shared: the rules and the parser proof each add
well under a second to about 3.5 s that either alone pays (day 2's
`readsLine` alone was 4.6 s; `readsThen` chains seem cheaper).

### Ranked

1. No lemmas for `Text.toNat` or `Text.stripSuffix`, and `stripSuffix`
   compares by `sameChar`, so part 2's proofs grew 50 lines of text
   plumbing (item 1). Missing library; small (two lemmas and a `sameChar`
   bridge in std, an hour or two; this day's `toNatDigits` and
   `stripSuffixTwo` are candidates).
2. The counterexample search never builds texts like `150cm` or `byr`, so it
   misses a broken text rule, and the audit gives 11 false vacuity warnings
   on generated equations (item 6). Missing feature (seed generators with
   literals from the definitions), medium; the audit filter, small.
3. A parse failure after an extra blank line is reported a line later as
   "expected the end of the input" (item 3). Error message; small to
   medium (which failure `Parse.all` keeps).
4. `rewrite … in cases` in an arm fails with `E-MATCH-MOTIVE` and the
   kernel's "`rfl` can't prove this", where the same `cases` as a lemma
   works (item 2). Bug in `cases`; medium (needs a repro; skip splits it
   can't type, or say what it split).
5. `cases` on two enumeration values splits stuck comparisons before the
   second variable, and runs past 64 cases (item 7). Missing feature
   (heuristic); small.
6. `BirthYear.valid` is "not in scope" with no note, and `Passport.mk`'s
   error is printed three times (item 5). Error message, small; the
   repeated diagnostic is a bug, small.
7. `pick`'s expectation reads "'a' or 'b' or … or 'h'" (item 4). Error
   message; small.
8. No std lemma for `contains` on a list of distinct values, or for the
   heads of equal lists (items 1, 7). Missing library; small.
9. The first `stitchwort search` in a new worktree took over two minutes of
   wall clock (item 7). Performance; unknown size, worth timing on an idle
   machine.

## Day 5: Binary Boarding

Boarding passes, ten letters each: the first seven halve the plane's 128
rows (`F` keeps the front half, `B` the back), the last three its 8
columns (`L`, `R`), until one seat is left; its ID is row × 8 + column.
Part 1 is the highest ID on a pass; part 2 is your seat, the one ID not on
a pass whose neighbours either side are. Answers on Matt's input (807
passes): 813 and 612; the examples give 357, 567, 119 and 820. Both
answers, and the first example's 357, match Matt's Scala (`sbt "runMain
aoc.day5.Day5"`, run on a copy of his repository).

The program reads a pass as one 10-bit binary number, `B` and `R` for 1,
with `Nat.fromBits` from std; part 2 sorts the IDs and takes the first gap
of two:

```stitchwort
def half (lower: Char) (upper: Char): {Parse} Bool :=
  Parse.satisfy "'${lower}' or '${upper}'" (letter => letter == lower || letter == upper) == upper

def pass(): {Parse} List Bool :=
  let row := Parse.repeat 7 7 frontBack
  let column := Parse.repeat 3 3 leftRight
  row ++ column

def seatId (pass: List Bool): Nat := Nat.fromBits pass

def gap: List Nat → Option Nat
  | [low, high, ..rest] => if high == low + 2 then Some (low + 1) else gap [high, ..rest]
  | _ => None
```

It printed the right answers on the first run, and 16 of the 17 tests
passed the first time (the one that didn't was my line count: the input
has no final line break). The spec (`Spec/Spec.sw`) is the puzzle's
procedure on the letters as written: a `Region` is "rows 0 through 127" as
`first` and `last`, `lowerHalf` and `upperHalf` keep a half, `narrow`
halves letter by letter (any letter but the two is no pass), and
`Region.only` is "until you're left with exactly one row". A pass is 10
letters, the row from the first 7 and the column from the last 3. Part 1 is
the `maximum` of the IDs; part 2 is every ID of the 128 × 8 seats that
isn't on a pass while the IDs either side are (`part2Answers`), and the
spec test checks that on the input that is exactly `[612]`.

Proved (`Aoc.Year2020.Day05.Proofs`):

- `narrowBits`: halving a region of 2^n rows by n letters ends at its first
  row plus the number the letters spell in binary, for any two different
  letters and any region of that size. `seatIdSpec`: so a pass of 7 row
  bits and 3 column bits, written out, is the spec's seat, and its seat ID
  is `Nat.fromBits` of all ten bits (`fromBitsAppend`: row × 2^3 + column).
- `parseWritten`: if `parsePasses` reads the input, each line is its pass
  written out, 7 letters `F`/`B` then 3 `L`/`R`, one per bit.
  `idsWritten`: the spec's seat IDs of the lines are the program's.
- `part1Correct`: part 1 is the spec's highest seat ID, for every input
  the parser reads.
- `gapSound`, `gapComplete`: on a sorted list, `gap` finds only numbers
  missing with both neighbours present, and finds one whenever there is
  one. `part2Sound`: part 2's answer could be your seat;
  `part2Complete`: part 2 finds a seat whenever one could be yours;
  `part2Correct`: when exactly one seat could be yours (the puzzle's
  promise), part 2 is it.

Not proved: that every well-formed input parses (`Parse.Reads` is
soundness only, as on days 2 to 4). `part2Correct` takes the puzzle's
promise as a hypothesis, `part2Answers … = [seat]`; it holds on the input
by a test, not by a proof. Without it the puzzle has no single answer:
`part2Sound` and `part2Complete` say what part 2 does then.

Breaking the program made the proofs fail: `Some low` for `Some (low + 1)`
in `gap` fails `gapSound` and `gapComplete` (a type mismatch and `E-REFL`);
`high == low + 3` fails the same two, structurally, since the proofs
match on that comparison; `== lower` in `half` fails `readsHalf`, at the
parser it restates; `Parse.repeat 6 7` for the row fails `readsPass`, with
a message that hides why (item 5). The counterexample search found none of
these (item 4).

48 lines of program, 67 of spec, 248 of proofs, 47 of tests. About 20
minutes from reading the puzzle to the proofs checking, by the clock
(20:28 to 20:46, counting a 1-minute CLI build), then 10 minutes on check
speed (item 3). Most proofs checked on the first try: `narrowBits`, the
seat, the parser and `gapSound` each needed at most two edits.

### 1. std's bits were there and right; the missing two lemmas are already duplicated

`Nat.fromBits` (most significant first) with `Nat.fromBitsCons`,
`Nat.fromBitsFrom` and `Nat.fromBitsFlipped` were exactly what the proofs
needed: `narrowBits` is an induction that closes each step with `omega
[Nat.fromBitsCons bit rest]`, 13 lines. Two lemmas were missing:

```stitchwort
theorem fromBitsAppend (high: List Bool) (low: List Bool): Nat.fromBits (high ++ low) = Nat.fromBits high * Nat.pow 2 low.length + Nat.fromBits low :=
  Eq.trans (List.foldLeftAppend high 0 low (acc bit => acc * 2 + Bool.toNat bit)) (Nat.fromBitsFrom (Nat.fromBits high) low)

theorem fromBitsBelow (bits: List Bool): Nat.fromBits bits < Nat.pow 2 bits.length := omega [Nat.fromBitsFlipped bits]
```

`stitchwort search 'Nat.fromBits (_ ++ _) = _'` then showed that 2021 day
16 has `fromBitsSnoc` (the one-bit case of `fromBitsAppend`) and a
`fromBitsBelow` identical to this one, character for character, and its own
`bitsOf`/`fromBitsOf` the other way; 2024 day 24 defines its own `fromBits`,
least significant first. All are std candidates: `Nat.fromBitsAppend`,
`Nat.fromBitsBelow`, and a `Nat.toBits width n` with its round trip. Std
has nothing linking `fromBits` to `testBit`; this day didn't need it.

### 2. Moving a fact along an equation: `rewrite` ran out of budget, and std has no `Eq.subst`

`part2Sound` has a membership in the spec's candidates, `seat ∈
part2Answers lines`, and `idsWritten: seatIds lines = passes.map seatId`.
`rewrite idsWritten input passes parsed in …` failed:

```
[E-REWRITE-BUDGET] Error: `rewrite` couldn't decide whether a part of the goal is the rule's left side
 122 │       rewrite idsWritten input passes parsed in
     │ Note 1: the part of the goal, as it computes: `List.filterMap (List.map (Text.linesFrom [] [] (Text.toList input)) Text.toList) (pass => Option.map (if Std.Decidable.toBool (Nat.decEq … 10) then (match …) (…, …) else None) Seat.id)`
     │ Note 2: the rule's left side: `seatIds (List.map (Text.lines input) Text.toList)`
     │ Note 5: state the step with `calc`, or rewrite with a more specific equation
```

The goal had unfolded `seatIds` and `Text.lines`, so the left side was no
longer there to find, and comparing the unfolded forms ran out. `calc`
doesn't fit a membership. What worked was the eliminator by hand, with the
motive written out:

```stitchwort
J (written same => seat ∈ (List.range (128 * 8)).filter (isYourSeat written)) (…) (Eq.sym (idsWritten input passes parsed))
```

(three times, in `part2Sound`, `part2Complete` and `part2Correct`). Std has
`Eq.cong`, `Eq.sym` and `Eq.trans`, nothing like Lean's `▸` or
`Eq.subst`/`Eq.mp`. An `Eq.subst (motive) (h) (proof)` with the motive
inferred from the expected type, or a `rewrite` that matched the rule's
left side as written before unfolding it, would have done it in one line;
the note could also suggest it.

Twice I wrote `rewrite only at (sound found made) in …`, which is
`E-REWRITE-TARGET` ("needs a local name after `at`"), with a clear note
to `let` it first.

### 3. A concrete `128 * 8` made proofs slow, and a smaller lemma for any count fixed it

The first full version took 7.7 s to check cold. `STITCHWORT_TIMINGS=1`
showed it at once:

```
declaration                                 elab ms   kernel ms         steps       nodes
Aoc.Year2020.Day05.Proofs.part2Sound         1707.9      1241.9      55040922      507691
Aoc.Year2020.Day05.Proofs.part2Correct       1152.5        18.7      26532660         853
Aoc.Year2020.Day05.Proofs.part2Complete       396.6        10.0       9409056         668
```

`part2Sound`'s term had half a million nodes. Moving its argument into a
lemma, `gapYours`, still with `128 * 8`, brought it to 98,647 nodes, and
making that lemma take any `count` made it vanish from the list; the same
for `part2Complete` (`yoursGap`) and `part2Correct` (`onlyAnswer`, about
any list of answers). The cold check went from 7.7 s to 3.2 s, of which
about 3 s is the parser proofs' std. What in the term was so large wasn't
established (`STITCHWORT_TIMINGS` names the declaration, not the part);
replacing parts with `?` doesn't help, as a declaration with a `?` never
reaches the kernel, so its numbers drop for that reason alone. The
guide's §2 item 3 ("a lemma over any …, then instantiated") was the right
remedy; a hint naming the large subterm would have saved the bisecting.

### 4. The counterexample search can't look at `gap`: `List.Sorted` isn't decidable

`gapSound` and `gapComplete` take `List.Sorted Nat.leq ids`, and the search
says "not applicable: nothing decides `Std.List.Sorted Std.Nat.leq ids`".
So breaking `gap` (`Some low` for `Some (low + 1)`) was caught by the proofs
only, and since the proofs follow `gap`'s shape, by a type mismatch at a
`match`, not by a counterexample. The end-to-end theorems are "not
applicable: the statement's normal form has more than 100000 nodes" (the
1024 seats). A `Decidable` instance for `List.Sorted le` with a `Bool` `le`
(it is a `LeHead` chain) would let the search test every sorted-list lemma
in std and AoC.

### 5. Smaller things

- **`Some { row, column }` is the constructor's own fields.** In the spec,
  `| (Some row, Some column) => Some { row, column }` is `E-UNKNOWN-FIELD`
  "`Some` has no field `row`", with a note saying exactly what to write,
  `Some ({ … })`. Clear, but it bit twice (spec and test), and the reading
  "`Some` applied to a record literal" is the only one that typechecks
  here.
- **Impossible `All2` arms must be written.** `seatIdsWritten` matches on
  two lists and their `List.All2`; the cases with one list empty and the
  other not have `Void` as the third argument's type, but are still
  `E-NONEXHAUSTIVE` ("no arm matches 2 patterns"), so each lemma over
  `All2` gets two `| [], [_, .._], impossible => Void.exfalso impossible`
  arms. The coverage check could accept them as missing when the type
  computes to `Void`.
- **`omega` won't prove a non-arithmetic goal from contradictory facts.**
  With `seat + 1 = low` and `low ≤ seat - 1` in scope, `omega` for the goal
  `Succ seat ∈ rest` is "unsupported structure: this goal isn't linear
  arithmetic"; `Void.exfalso (omega)` works. Lean's `omega` proves any goal
  when the facts contradict; at least the note could suggest this.
- **The audit's one warning is on a generated equation again.**
  `Spec.seat.eq.ifTrue.alt1` is "no input made the hypotheses true (0 of
  10000 cases)": random lists of characters are never 10 letters of `F`,
  `B`, `L` and `R`. It isn't vacuous (the example is such a pass). Day 4's
  SW-1261 (generated equations out of the vacuity check) would remove it;
  it is the only warning.
- **The first `stitchwort search` in this worktree took 84 s of wall clock**
  (65 s user) and found nothing in std for `((?a && ?b) = True) ↔ _`; later
  searches took 3 s. That is day 4's SW-1267 again. Grepping
  `crates/elab/src/std` found `Bool.andLeft`, `Bool.andRight` and
  `Bool.notTrue`, which `yourSeatMembers` used.
- **A parser proof that needed no restating.** `readsHalf` restates
  `half`'s `satisfy`, interpolated message and all, and it matched;
  `Parse.readsRepeat` gave the 7 and 3 lengths directly, and `readsPass`
  is one `readsThen` chain. The whole parser proof is 45 lines and checked
  on the first try. `Parse.repeat 7 7` reads oddly for "exactly 7"; a
  `Parse.count 7` would read as the puzzle does.
- **A wrong length in the parser is reported as an unsolved spec.** With
  `Parse.repeat 6 7 frontBack` (so a row can be 6 letters), `readsPass`
  fails at the `rfl` that starts the witness:

  ```
  [E-TYPE-MISMATCH] Error: type mismatch
   39 │         (Witness row (Witness column (Both rfl (Both (omega) (Both (omega)
      │                                            ╰─── `rfl` proves an equation, but the expected type is `?25 rowRead row rowEach rowLeast rowMost columnRead column columnEach columnLeast columnMost`
  ```

  The real failure is the `omega` two steps on (`row.length = 7` from `6 ≤
  row.length ≤ 7`). `readsThen`'s spec is a `_` solved from the last step,
  and that step failing left it unsolved, so the first error is about the
  hole. Reporting the `omega`, or saying the expected type is an unsolved
  spec, would point at the cause.
- **Day 4's tickets.** SW-1260's text lemmas weren't needed (no text
  values here); SW-1261 would have removed the one audit warning; SW-1267
  is the slow first search above. Nothing from day 4's `cases` items
  (SW-1263, SW-1264) came up: the one `cases` here closed at once.

### Size and time

CPU time (load average about 33):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day05.Proofs` | 3.3 s user |
| the same, first version (item 3) | 7.7 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day05` | 1.1 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day05` (17 tests) | 3.4 s user |
| `stitchwort check --counterexamples Aoc.Year2020.Day05.Proofs` | 2.2 s user |
| `task audit:touched -- Aoc.Year2020.Day05` (46 theorems) | 3.3 s user |
| `stitchwort run Aoc.Year2020.Day05.main` on the input | 0.4 s user |
| the first `stitchwort search` in the worktree | 65 s user, 84 s wall |

### Ranked

1. Std lacks `Nat.fromBitsAppend` and `Nat.fromBitsBelow` (and a
   `toBits` with its round trip), and two AoC days already carry copies
   (item 1). Missing library; small (move them, under an hour).
2. Moving a fact along an equation needs `J` by hand: `rewrite` hit its
   budget on a goal that had unfolded the rule's left side, and std has no
   `Eq.subst` (item 2). Missing library (`Eq.subst` with an inferred
   motive), small; `rewrite` matching before unfolding, medium.
3. A concrete `128 * 8` in a proof's context gave a 500,000-node term and
   2.9 s of checking, cured by a lemma over any count (item 3).
   Performance; unknown size (find what was large); a timings note naming
   the large subterm, medium.
4. The counterexample search can't test anything about sorted lists, as
   `List.Sorted` isn't decidable (item 4). Missing library (a `Decidable`
   instance); small.
5. The first `stitchwort search` in a fresh worktree took 84 s wall (item
   5), as on day 4. Performance; SW-1267.
6. A false vacuity warning on a generated equation (item 5), as on day 4.
   SW-1261.
7. Impossible `All2` arms have to be written out (item 5). Missing feature
   (coverage sees `Void`-typed arguments); medium.
8. `omega` doesn't prove a non-arithmetic goal from contradictory facts
   (item 5). Missing feature, small; or a note suggesting `Void.exfalso
   (omega)`, smaller.
9. A wrong count in a `readsThen` chain is reported as `rfl` against an
   unsolved `?25 …` rather than the `omega` that fails (item 5). Error
   message; medium (needs a repro).
10. `Some { … }` is read as `Some`'s own fields (item 5). Error message
   already good; small, if a record literal could be tried when the
   constructor's fields don't match.

## Day 6: Custom Customs

Customs forms: each person writes the letters `a` to `z` of the questions
they answered "yes" to, one line each; the people travelling together are a
group, with a blank line between groups. Part 1 sums, over the groups, the
number of questions anyone in the group answered "yes" to; part 2 the number
everyone did. Answers on Matt's input (483 groups, 1713 people): 6630 and
3437; the example (5 groups) gives 11 and 6. I did not run Matt's Scala
(`Day6.scala`, no `sbt` run); I read it (set union and intersection per
group, `split("\n\n")`) and checked both answers and the example with an
independent Python script (`set.union`/`set.intersection` per group), which
agree.

The domain types are the puzzle's nouns: a `Person` has the `Set Char` of
the questions they answered "yes" to, a `Group` its `people`, with
`Group.anyone` (the union) and `Group.everyone` (the intersection, from the
set of all 26 questions, so no empty-group case). The parser reads every
line (`Parse.eachLine`, as day 5) as a person's or blank (`Option Person`),
and the groups are what lies between the blank lines (`List.splitBy`):

```stitchwort
def line(): {Parse} (Option Person) := Parse.oneOf [answers, blank]

def groupsOf (lines: List (Option Person)): List Group :=
  (lines.splitBy .isNone).map (people => { people = people.filterMap (answers => answers) })

def Group.anyone (group: Group): Set Char := Set.unions (group.people.map .answers)

def solvePart1 (groups: List Group): Nat := groups.sumBy (.anyone.size)
```

It printed the right answers on the first run. The spec (`Spec/Spec.sw`)
is the puzzle in its own terms, on the input text: `groupsOf input` splits
`input.lines` at the blank lines (nothing but spaces and tabs) into groups
of lines; `anyone group question` is "some line has the letter", `everyone`
"every line has it", `count yes group` is the number of the 26 `questions`
for which `yes` holds, and `part1Answer input` / `part2Answer input` are
the sums of those over the groups. The spec test gives (6630, 3437) on the
input.

Proved (`Aoc.Year2020.Day06.Proofs`):

- `parseWritten`: if `parseLines` reads `input`, each line of it is a
  person's or blank (`LineWritten`): a person's has at least one letter,
  all questions, and the person's answer set has exactly the line's
  letters.
- `splitByRel` (Split.sw, general): `List.splitBy` on two lists whose
  elements correspond and agree on which are separators gives corresponding
  groups. With `blankAgrees` (the spec's blank line is the parser's) and
  `groupLines`, the parser's groups are the spec's `groupsOf input`, line
  by line (`groupsWritten`).
- `unionContains`, `intersectContains`: folding the people's sets by union
  (intersection) holds what the accumulator holds or some line has (and
  what every line has). `anyQuestion`: whatever a line has is a question.
- `sizeCount` (since SW-1298 std's `Set.sizeOfMembers`, with `Set.containsUnionAll` and `Set.containsFoldIntersect` replacing `unionContains` and the fold half of `intersectContains`): a set of questions has as many members as there are of the
  26 questions it holds (the set's key list and the filtered `questions` are
  both distinct with the same members, so they are a permutation).
- `anyoneCount`, `everyoneCount`: a group's `anyone.size` (`everyone.size`)
  is the spec's `count anyone` (`count everyone`) of its lines.
- `part1Correct`, `part2Correct`: for every input the parser reads,
  `solvePart1 groups = Spec.part1Answer input` and likewise part 2.

Not proved: that every well-formed input parses (`Parse.Reads` is
soundness only, as on days 2 to 5). The spec's blank line is the parser's
(spaces and tabs only); an input with other whitespace on a "blank" line
fails to parse (a test), so nothing is claimed for it.

Breaking the program made the proofs fail: `common.union` for
`common.intersect` in `Group.everyone` fails `everyoneCount` at
`intersectContains` (E-TYPE-MISMATCH, naming both folds); `splitBy (line =>
False)` for `splitBy .isNone` fails `groupsWritten` at `groupLines`.

### 1. `Parse.SepBy` doesn't tie the first value to the first read

My first version parsed with `Parse.sections group` over `Parse.lines
person`, as day 4. Its format theorem rests on `Parse.SepBy`, which is

```stitchwort
def Parse.SepBy (spec: List Char → a → Prop) (separator: List Char → () → Prop) (read: List Char) (values: List a): Prop :=
  ∃ (first: a) => ∃ (rest: List a) => values = [first, ..rest] ∧ Parse.Then spec (v => Parse.Each (Parse.Then separator (u => spec))) read rest
```

where `Parse.Then`'s first value is existential and `v` is ignored, so the
`first` of `values = [first, ..rest]` is not the value `spec` holds of the
first read. This checks:

```stitchwort
theorem weak: Parse.SepBy (read value => read = ['a'] ∧ value = 1) (read u => read = []) ['a'] [2] :=
  Witness 2 (Witness [] (Both rfl (Witness ['a'] (Witness [] (Witness 1 (Both rfl (Both (Both rfl rfl) rfl)))))))
```

So every format theorem stated with `Parse.SepBy` (day 4's `parseWritten`,
for the first passport and the first field) says nothing about the first
element. I found it when `sepByReads` couldn't be proved, worked around it
with a local `SepBy` and a copy of `readsSepBy1`'s proof, and then dropped
both: tying the parse to the input text meant relating `Text.lines` to the
parser's reads (no lemmas about `Text.lines` in std, and the final
`ending` of `Parse.allReads` may be any run of `\n` and `\r`, so a stray `\r`
would join a line), so I changed the program to parse each line with
`Parse.eachLine` (whose `eachLineReads` gives the lines directly) and
split the groups at the blank lines with `List.splitBy`, which has a
lemma set. A side effect: blank lines before, between and after groups
(several in a row) are accepted. The lesson for std: `Parse.SepBy` needs
the fix below; and a `Parse.sections` reads theorem that speaks of the
input's lines (as `eachLineReads` does) would let a day-4-style format
parse reach a spec on text.

Fixed in SW-1298: `Parse.SepBy` now says the first value is the one `spec` holds of the first read (`readsSepBy1` and `readsSection` carry it), so day 4's `parseWritten` covers the first passport and its first field too; `firstPassportWritten` states it for the first passport.

### 2. Set reasoning in std: the membership laws were there, the size and the folds weren't

Most of the proof was std lemmas used as they are: `Set.containsUnion`,
`Set.containsIntersect`, `Set.containsFromListIff`, `Set.memToList`,
`Set.sizeToList`, `Map.keysDistinct`, `List.permOfSameMembers`,
`List.distinctFilter`, `List.permLength`, `Bool.eqOf`, `byDecision`. Missing:

- `Set.size` of a set from its members: `sizeCount` (a set with the members
  of `questions.filter yes` has that length, 13 lines) is what any "count
  the distinct things that …" needs. Candidate: `Set.sizeEqLength` for a
  `Distinct` list with the same members as `set.toList`, or
  `Set.sizeOfMembers`.
- Folds: `Set.unions` is a `foldLeft` of `Set.union` and `everyone` one of
  `Set.intersect`, and each needed an induction (`unionContains`,
  `intersectContains`, 8 lines each) to reach `Set.containsUnion`. Std has
  `Set.containsFoldInsert` for `fromList`; a `Set.containsUnionAll` and the
  intersection fold would remove them.
- `Bool.andAssoc` (there is `orAssoc`); `andAssoc` is a 3-line local
  theorem in `Sets.sw`.
- `Set.contains Set.empty key = False` was `rfl`, good.

### 3. Names: `questions` in the program and in the spec

The program has `questions` and `Spec` has its own (the spec must not
depend on the program). A proof file importing both `(..)` and the spec
needs `import Aoc.Year2020.Day06 (Spec)` and writes `Spec.questions`; the
error without it (`E-UNKNOWN-NAME`, with a note naming the import to add)
was clear. The two are equal by `rfl`, which the kernel accepted wherever
the proofs mixed them (`isQuestion` from the program against
`Spec.questions.contains`).

### 4. `byDecision` for 26 distinct letters is the biggest proof cost

`questionsDistinct: List.Distinct Spec.questions := byDecision` took 324 ms
elab and 71 ms kernel, 2.5 million steps, a 36,800-node term
(`STITCHWORT_TIMINGS=1`): more than almost every other declaration
(the end-to-end theorem, which only assembles the pieces).
That is `decDistinct` comparing each of 26 letters with those after it
through `Char`'s `DecEq`. `List.allDistinctCorrect` (the `Ord`-based test
in `List/Distinct.sw`) would be cheaper; not tried.

### 5. Smaller things

- **A second blank line is no longer an error.** With the parser reading
  each line as a person's or blank, `ab\n\n\nac` and a blank first line
  parse (the first version said "got the end of the line" at line 3, which
  didn't name the cause). `ab\nA` is now "line 2, column 1: expected a
  question, 'a' to 'z' or the end of the line, got 'A'" (the end of the
  line because a blank line is also a line). The `sections` messages of
  today ("a blank line before this line") weren't reached either way.
- **`rewrite <- rule` failed on the direction.** I wrote `rewrite <- meet
  question in found` where `found` had the left side; the error was
  `E-REWRITE-NOTHING` with six notes, two of them (5 and 6) about hidden
  `match` functions in `Map.contains` that had nothing to do with the
  mistake. Note 4 ("to replace the left side by the right, write the rule
  without `<-`") was the one needed; it was last.
- **The `Parse.Reads` proof was short.** `readsPerson` is a `readsThen` of
  `readsMany1`/`readsSatisfy` and one lemma on the result (`eachLetters`,
  `Each` of single letters is the letters); `readsLine` is `readsOneOf`
  over two `readsThen` chains. `Parse.sw` is 56 lines and checked on the
  first try; `Proofs.sw` needed about six edits (imports, a `match` that
  already replaced its scrutinee, `NonSep` computing past the head).
- **Domain types.** `Person`/`Group` with `Group.anyone`/`everyone` as
  methods read as the puzzle does and made the spec relation
  (`GroupLines lines group`) a one-line `List.All2`; I didn't need a
  `Person.answered` method. The proofs reach into `group.people` and
  `person.answers`, never past the records.
- **Today's std additions.** Text lemmas (SW-1260) and `List.maximumOf`
  weren't needed (no `Text` values, sums not maxima); `List.sumBy` with
  `List.sumByCons` made the sum over groups a four-line induction
  (`sumCounts`) over any per-group count, as day 5's `onlyAnswer` was over
  any answers. `List.splitBy` was in std and I wrote `groupsOf` by hand
  first; it replaced a `foldRight` with a `match` in the test.
- **Audit.** 36 theorems, 0 failed, 0 warnings: no vacuity warning on
  generated equations this time (no spec equation with a 10-letter guard).

### Size and time

69 lines of program, 33 of spec, 267 of proofs (Parse 56, Sets 61, Split
39, Proofs 110), 52 of tests (+1 answer test in `aoc_answers.rs`). The first
version took about 25 minutes by the clock from reading the puzzle to the
proofs checking, plus 10 on the spec test, break checks and notes; the
review's change (the headline theorem about the input) took about 35 more,
of which the `splitBy` lemmas (`Split.sw`, 39 lines) and the rework of the
parser were most.

CPU time (load average about 50):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day06.Proofs` | 6.9 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day06` | 2.5 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day06` (17 tests) | 7.4 s user |
| `task audit:touched -- Aoc.Year2020.Day06` (36 theorems) | 2.2 s user |
| `stitchwort run Aoc.Year2020.Day06.main` on the input | 0.7 s user |
| `task test:one -- year2020_day06` | 7.3 s wall |

### Ranked

1. `Parse.SepBy` doesn't relate the first value to the first read, so
   every format theorem built on it (day 4, 6) is silent about the first
   element (item 1). Soundness of a std statement; small (one definition
   and a proof), but touches day 4's proofs.
2. `Set.size` from members (`sizeCount`), and membership through the folds
   `Set.unions` and `intersect` (item 2). Missing library; small each.
3. `List.Distinct` of 26 letters by `byDecision` is a 36,800-node proof
   (item 4). Performance; small (use `allDistinctCorrect`, or a lemma on
   `Char`).
4. `rewrite <- …` mistakes bury the useful note under hidden-`match` notes
   (item 5). Error message; small.
5. `Bool.andAssoc` (item 2). Missing library; trivial.
6. No lemmas about `Text.lines` (and `Parse.allReads` leaves the ending any
   run of `\n`/`\r`), so a `Parse.sections` parse can't be joined to a spec
   on the input text (item 1). Missing library; medium.

## Day 7: Handy Haversacks

Luggage rules, one per line: "light red bags contain 1 bright white bag, 2
muted yellow bags." or "faded blue bags contain no other bags." Part 1
counts the colours that can eventually contain a shiny gold bag; part 2
counts the bags a shiny gold bag must hold in all. Answers on Matt's input
(594 rules): 126 and 220149; the first example gives 4 and 32, the second
0 and 126. I did not run Matt's Scala (`Day7.scala`, no `sbt` run); I read
it (a depth-first walk over the inverted rules, and the plain recursion for
part 2) and checked both answers and the examples with an independent Python
script (regex parse, recursive reachability, memoised total), which agree.

The domain types are the puzzle's nouns: a `Colour` (two words, `shade`
and `hue`), a `Content` ("2 muted yellow bags": `count` and `colour`), a
`Rule` (`colour` and its `contents`) and `Rules`, with the work as methods.
Part 1 walks outward from shiny gold with std's breadth-first search, on a
graph whose edges go from a bag to the bags whose rules list it (the rules
read backwards, built once with `Map.groupBy`); the colours it finds are the
answer. Part 2 follows the rules inward, through an index of the rules by
colour, at most one level deeper than there are rules:

```stitchwort
def Rules.graph (rules: Rules): Graph Colour :=
  let index := holdersIndex rules.all
  {
    edges = colour => holdersIn index colour |> .map (holder => (holder, 1)),
    states = rules.all.map .colour,
    listed = colour holder weight edge => …
  }

def Rules.outside (rules: Rules) (colour: Colour): Map Colour Nat :=
  let graph := rules.graph
  graph.breadthFirst (graph.edges colour |> .map Pair.fst)

def bagsInside (index: Map Colour (NonEmptyList Rule)): (depth: Nat) → (colour: Colour) → Option Nat
  | 0, colour => None
  | Succ depth, colour =>
    contentsIn index colour
      |> .map (content => bagsInside index depth content.colour |> .map (inside => content.count * (1 + inside)))
      |> List.allSome
      |> .map List.sum
```

The search starts from shiny gold's direct holders, not from shiny gold,
so a cycle back through shiny gold counts it, as the puzzle's words say
(a test); Matt's Scala and my Python both remove shiny gold instead, which
agrees on any input without such a cycle. A cycle below shiny gold makes
part 2 fail with "the rules for shiny gold bags go round in a cycle" (a
test); a cycle elsewhere doesn't matter (a test).

It printed the right answers on the first run. The spec (`Spec/Spec.sw`)
has the format, a line at a time (`RuleWritten`: the colour's two words of
`a` to `z`, " bags contain ", "no other bags" or the contents with ", "
between, each a decimal count, a colour, and "bag" for one and "bags"
otherwise, then "."), and the two questions: `Directly rules outer inner`
(a rule for `outer` lists `inner`), `Outward` (a chain of bags each
directly inside the next), `CanContain`, and `Part1 rules answer`: there
is a list of colours, none twice, holding exactly those that can eventually
contain shiny gold, and `answer` is its length. Part 2's `bagsWithin rules
depth colour` is the puzzle's recursion ("count bags of that colour, and the
bags inside each"), `None` when the rules go deeper than `depth`; `Part2
rules total` says some depth settles it at `total`. The spec test runs part
2's spec on the input (220149 at depth 30); part 1's is a proposition, so
nothing runs it.

Proved (`Aoc.Year2020.Day07.Proofs`):

- `readsColour`, `readsContent`, `readsContents`, `readsRule`: each parser
  reads its phrase as the spec writes it. `parseWritten`: if `parseRules`
  reads `input`, each line of it is its rule written out.
- `holderDirectly`: a colour's holders in the program's index are exactly
  the colours whose rules list it; `walkOutward`, `outwardWalk`: a walk on
  the graph is a chain outward, and back.
- `outsideCanContain`: the search finds exactly the colours that can
  eventually contain the start colour (from `Graph.breadthFirstShortest`);
  `part1Rules`: part 1 is `Spec.Part1` for any rules.
- `contentsAgree`, `bagsAgree`: the index gives each colour the spec's
  contents, so the program's count is `bagsWithin` at every depth;
  `part2Rules`: when part 2 gives an answer, it is `Spec.Part2`.
- `bagsWithinDeeper`, `part2Unique`: a total settled at one depth stays
  the same at every greater one, so `Part2` names one total.
- `part1Correct`, `part2Correct`: for every input the parser reads, its
  lines are the rules written out and the answers are the spec's for them.

Not proved: that every well-formed input parses (`Parse.Reads` is
soundness only, as on days 2 to 6). That part 2 never reports a cycle
wrongly: when the spec settles the total at some depth, the program's depth
(rules + 1) is enough. That needs the pigeonhole argument (a chain inward
of more bags than there are rules repeats a colour, and a repeated colour
can be gone round for ever), which I didn't write (item 4); the input's
answer is by a test. Part 2's spec recursion is the program's, apart from
the index and the depth: the proof says the index is right, not that the
recursion is the puzzle's, which is by reading.

Breaking the program made the proofs fail: listing the rule's own colour
as the inside in `Rule.insides` fails the program itself, at the graph's
`listed` proof; `content.count * inside` for `content.count * (1 +
inside)` fails `bagsAgree` (E-REWRITE-NOTHING, naming the changed
lambda); `" bag"` for every count fails `readsContent`; starting the search
from shiny gold itself fails `outsideCanContain`.

139 lines of program, 81 of spec, 247 of proofs (Parse 52, Part1 100,
Part2 76, Proofs 19), 81 of tests (+1 answer test in `aoc_answers.rs`).
By the clock, 11 minutes from reading the puzzle to the program and its
tests passing (14:37 to 14:48, `date` at each step), and 5 more to every
proof checking (14:53); then break checks, timings and these notes to
15:00. Nearly every proof checked on the first or second try.

### 1. A `readsThen` chain ending in `Witness` needs `readsDone`'s spec written out

`readsColour` ends `Parse.readsDone { shade, hue } _ (rewrite … in Both …)`
and checks. `readsContent` and `readsRule`, ending the same way but with a
`Witness` (the spec is "there are digits and a colour such that …"), fail:

```
[E-TYPE-MISMATCH] Error: type mismatch
 44 │               (Both (rfl) (Both written listed))))))))
    │                      ╰─── `rfl` proves an equation, but the expected type is `?39 colourRead colour written containRead u✝ contain contentsRead contents listed stopRead u stop`
```

With `rewrite` there instead of `rfl` it is E-REWRITE-NOTHING with the goal
`?40 digitsRead count nonEmpty …`. The `_` (readsDone's spec) is solved from
the expected type, but `Witness` was elaborated first, against an unknown
type, so its parts became fresh holes. Writing the spec out,
`Parse.readsDone { colour, contents } (read made => RuleWritten (colourRead
++ (containRead ++ (contentsRead ++ (stopRead ++ read)))) made)`, fixed both.
Day 5's item 5 ("a wrong length in the parser is reported as an unsolved
spec") is the same hole seen from a failing step. Either solving `_` from
the expected type before checking the last argument, or a message saying
"the expected type here is an unsolved hole (`_` at …)", would have saved
the bisecting.

### 2. An inline `oneOf` alternative over `readsMap` won't check; named, it does

`contents` was first `Parse.oneOf [() => Parse.before [] "no other bags", ()
=> Parse.sepBy1 content (() => Parse.text ", ") |> .toList]`, and the second
alternative's proof, `Parse.readsWeaken (Parse.readsMap (() => Parse.sepBy1
…) NonEmptyList.toList _ (Parse.readsSepBy1 …)) (…)`, failed with

```
[E-TYPE-MISMATCH] Error: type mismatch
    │ expected `(state: Parse.State) → (value: List Content) → … → Parse.runFrom state (arg => …) = Ok (value, after) → …`, but this has type `Parse.Reads (arg => Std.Effect.bind (Parse.sepBy1 content (arg1 => …)) (x => Done …)) (…)`
    │ Note 1: they first differ at `?22 ()` against `Std.Effect.bind (Std.Effect.bind (Std.Effect.bind … …) (first => …)) (x => Done …)`
```

even with the alternatives written out in `readsOneOf`'s list (the first
version had `_`). The expected `Parse.Reads ?22 …` had been unfolded to its
definition before `?22` was solved, so the two sides no longer matched
argument by argument. Naming the alternative (`def contentList()`) and
proving `readsContentList` on its own checked at once, and the
`readsWeaken` became `(read found listed => Inr listed)`. The message
showed both sides, but one unfolded and one not, which hides that they
are the same thing; a repro for a ticket is the first version above.

### 3. std's graph search fits, with three adapters a newcomer has to write

`Graph.breadthFirstShortest` did all of part 1's search reasoning: the
whole of `outsideCanContain` is 25 lines, with no induction over the
search. What the puzzle needed was "which states can reach this one", and
std's `Graph` is a weighted shortest-path graph, so:

- **Weights.** Every edge is `(holder, 1)`, and the proof needs `unit`
  (each weight is 1) and then the costs to be thrown away.
- **The `listed` proof in the program.** `Graph` has a proof field: every
  edge leads into `states`. The program can't build its graph without
  `holderListed` (8 lines, through `memMapElim`, `memFilter`,
  `memFlatMapElim`, `anyElim`), so a proof sits in `Day07.sw`, written before
  the program first ran. (It did catch a broken `insides` at once.)
- **From distances to membership.** The answer is the number of keys of
  the `Map Colour Nat` it returns, and `Shortest`'s "each cost is a walk's
  and no walk is shorter" had to be turned into "a colour is found iff some
  walk reaches it" (`outsideCanContain`).

A `Graph.reachable (edges: s → List s) (states: List s) … (sources: List
s): Set s` with `Graph.memReachable: x ∈ reachable … ↔ ∃ source path,
source ∈ sources ∧ Walk …` would have made part 1 the call and one lemma.
And a way to build a graph whose `listed` holds by construction (keep only
edges into `states`, or take `states` from the edges) would keep proofs
out of the program; Day 20 of 2024 has the same `listed` field, proved by
hand too.

### 4. Part 2's recursion: fuel and a cycle error, and the depth bound (proved in SW-1405)

The natural part 2 is `bagsInside colour = (contentsOf colour).sumBy
(content => content.count * (1 + bagsInside content.colour))`. On a scratch
file that is

```
[E-TERMINATION] Error: can't show that `bagsInside` terminates
  ╰── this recursive call might not terminate: the 1st argument stays the same
  Note 2: non-terminating definitions are rejected unless they're partial: `{Partial}` in the result type. A depth limit keeps it total and provable: an extra `fuel: Nat` argument that decreases on each call, failing (or returning a default) when it runs out
```

and `{Partial}` would make the program unprovable. What works is fuel: the
program recurses at most `rules.all.length + 1` deep and fails with a cycle
message when that runs out; the spec says "some depth settles it". Proving
that the program's depth is enough whenever some depth is (so the cycle
error is never wrong) is the pigeonhole principle on a chain of colours,
and std has only part of it. `Nat.pigeonhole` (std/Nat/Pigeonhole.sw,
used by 2024 day 6's `Bound.sw`) is there, for a function into the numbers
below `n` (found by grep while writing these notes, after I had left the
bound unproved); it needs the colours numbered (each by its rule's
position) and the chain turned into a `Nat → Nat`. There is no list form ("a list longer than the
distinct values it draws from repeats one"), no notion of an acyclic
relation, and no recursion over one. A `List.pigeonhole` over `List.Mem`
and, further, a memoised fold over a finite acyclic graph (a topological
order with its proof) would cover the AoC days that count over a DAG. The
E-TERMINATION note now mentions fuel, which is what a proof needs, next to
`{Partial}`.

SW-1405 closed the bound: `List.pigeonhole` (`¬List.Distinct xs` for a list
drawn from a shorter one) and `List.repeatSplit` (the repeat as
`before ++ [x, ..(between ++ [x, ..after])]`) are in std, and
`Proofs/Depth.sw` proves `part2Complete`: any depth that settles the rules
means the program's `rules.all.length + 1` does, to the same total. The proof
is a chain predicate (`Deep`, `Walk`) rather than `Nat.pigeonhole` on a
numbering: the colours needn't be numbered, and the split gives the loop to
repeat directly. `settledNotDeep` and `noDeepSettled` say a depth settles
exactly where no chain is that long. `allSomeEach`/`allSomeOfEach` (a
`List.allSome` of a `map` is `Some` iff each element's is) are local to day 7
and would do in std.

### 5. Inverting a relation: `Map.groupBy` of pairs, then a filter lemma

The holders index is `Map.groupBy (rules.flatMap .insides) Pair.fst`, a
`Map Colour (NonEmptyList (Colour, Colour))`; reading it needs a `match` on
`get` (`Map.getOr` wants a `NonEmptyList` fallback) and `.map Pair.snd`.
`Map.getGroupBy` turned that into a filter, and `holdersInIndex` (5 lines)
into `((rules.flatMap .insides).filter …).map Pair.snd`. A `Map.groupMap
xs key value: Map k (List v)` (Scala's `groupMap`) with its `get` lemma
would have been the one-liner; std has `groupBy` and `indexBy` only.

### 6. Membership through `map`, `filter` and `flatMap` is long-hand

`holderDirectly`, "a holder in the index is a colour whose rule lists
it", is 30 lines, nearly all `List.memMapElim` (gives `Exists`),
`List.memFilter`, `List.memFlatMapElim` (gives `List.Any`, so then
`List.anyElim`), their `…Intro` forms going back, and `Map.Spec.sameKey`
to `==` to `=` (`sameKeySound`, `sameKeyDecide`, `DecEq.refl`, `DecEq.sound`).
Each step was found at once (by grep), and each checked; there are just
many. `List.memFilterMap` is an `↔` with an `∃`; `memFlatMap` has no `↔`,
and its elimination returns `List.Any` where `memMapElim` returns `∃`.
A `List.memFlatMap: y ∈ xs.flatMap f ↔ ∃ (x: a) => x ∈ xs ∧ y ∈ f x`
would make the forward and backward halves line up.

### 7. Smaller things

- **The counts' digits.** The spec writes a count as decimal digits with
  `Parse.digitsValue` (as day 4's spec does), not as `"${count}"`: nothing
  links `Nat`'s `Show` to `digitsValue`, so a spec that prints the number
  couldn't be met by `Parse.nat`'s reads. So the spec allows leading zeros.
- **Part 1's spec doesn't run.** `CanContain` is an `∃` over chains, so
  the spec test covers part 2 only, and the audit's counterexample search
  says nothing about part 1's theorems.
- **`rewrite Nat.addSucc` wasn't needed.** In `bagsWithinLater`, `depth +
  Succ more` had already computed to `Succ (depth + more)`, so the rewrite
  was E-REWRITE-NOTHING, with the goal shown fully unfolded (the whole of
  `bagsWithin`'s body) and no note that the term without the rewrite would
  check. In `readsRule` the same error did say "the goal already holds by
  computing", which was right.
- **`parseRules` wraps the parse in a record**, so `parseWritten` needs
  `Fail.toResultThen`, a `match` and `Result.okInjective` (5 lines) before
  `Parse.eachLineReads` applies.
- **Domain types.** `Colour`, `Content`, `Rule` and `Rules` read as the
  puzzle; `Colour.name` prints "shiny gold" for the cycle message (the
  derived `Show` prints the record). The spec imports the three record
  types from the program, as day 4's imports `Passport`.
- **Audit.** 40 theorems, 0 failed, 0 warnings.

### Size and time

CPU time (load average about 40):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day07.Proofs` | 9.4 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day07` | 4.9 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day07` (20 tests) | 9.9 s user |
| `task audit:touched -- Aoc.Year2020.Day07` (40 theorems) | 3.5 s user |
| `stitchwort run Aoc.Year2020.Day07.main` on the input | 0.5 s user |
| `task test:one -- year2020_day07` | 4.9 s for the test, after a 1 min 48 s build |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 1.5 s of elaboration,
`outsideCanContain` the largest declaration (467 ms, 3.6 million steps);
the rest of the cold time is std's modules (the program's 4.9 s against day
6's 2.5 s is presumably `Std.Graph` and `Map`; not broken down).

### Ranked

1. Part 2's cycle bound is unproved: std's pigeonhole is `Nat.pigeonhole`
   on numbered values only, with no list form, no acyclic relation and no
   recursion over one, so programs use fuel and leave "the fuel is enough"
   open (item 4). Missing library; medium (a list pigeonhole small, an
   acyclic fold larger). The E-TERMINATION note now mentions fuel.
2. `readsDone x _ (Witness …)` elaborates the `Witness` before `_` is
   solved and reports a goal `?39 …` (item 1), as day 5's item 5. Elaborator
   or error message; medium (repro in item 1).
3. std's `Graph` is a weighted shortest-path graph with a `listed` proof
   field, so a reachability question needs unit weights, a proof in the
   program and a distances-to-membership lemma (item 3). Missing library
   (`Graph.reachable` returning a `Set`, with its `↔` lemma; a graph built
   with `listed` by construction); small to medium.
4. An inline `oneOf` alternative proved by `readsWeaken (readsMap …)` fails
   with the expected type unfolded and a `?22 ()` hole; naming it works
   (item 2). Elaborator (unification order); medium, repro in item 2.
5. No `List.memFlatMap` `↔`, and `memFlatMapElim` returns `List.Any` while
   `memMapElim` returns `∃` (item 6). Missing library; small.
6. No `Map.groupMap` for inverting a relation (item 5). Missing library;
   small.
7. E-REWRITE-NOTHING on a rule whose left side already computed away
   doesn't say the term checks without it (item 7). Error message; small.
8. Nothing links `Nat`'s `Show` to `Parse.digitsValue` (item 7). Missing
   library; small.

## Day 8: Handheld Halting

A handheld console's boot code, one instruction a line: an operation
(`acc`, `jmp` or `nop`) and a signed argument, "jmp -4". Part 1 is the
accumulator just before any instruction runs a second time; part 2 repairs
the one corrupted instruction (a `jmp` that should be a `nop`, or the other
way round) so that the program terminates, by running into the position
just after its last instruction, and gives the accumulator then. Answers
on Matt's input (626 instructions): 1832 and 662; the example gives 5 and
8. I did not run Matt's Scala (`Day8.scala`, no `sbt` run); I read it (a
mutable machine with a visited set, and each `jmp`/`nop` swapped in turn)
and checked both answers and the example with an independent Python script
(the same simulation over a list), which agree. On the input exactly one
repair terminates (a test).

The domain types are the puzzle's nouns: an `Operation` (`Acc`, `Jmp`,
`Nop`), an `Instruction` (`operation` and `argument: Int`), a `Program`, a
machine `State` (`next`, the position of the instruction to run next, an
`Int` because a jump can go below 0, and the `accumulator`), and an
`Outcome` (`Loops`, `Terminates`, `JumpsAway`, each with the accumulator).
The program indexes the code once (`Map.byPosition`) and runs it keeping
the set of positions not yet run, which is also its termination measure:

```stitchwort
def Code.runFrom (code: Code) (unvisited: Set Nat) (state: State): Outcome
    decreasing unvisited.size
:=
  match state.next.toNatChecked with
    | None => JumpsAway state.accumulator
    | Some position =>
      match code.byPosition.get position with
        | None => if position == code.length then Terminates state.accumulator else JumpsAway state.accumulator
        | Some instruction =>
          if fresh: unvisited.contains position = True then
            Code.runFrom code (unvisited.remove position) (instruction.execute state)
              [decreasing := omega [Set.sizeRemovePresent unvisited position fresh, Set.sizePositive unvisited position fresh]]
          else Loops state.accumulator
```

Part 2 tries each `jmp` and `nop` swapped with one `Map.insert` into the
indexed code (`Code.terminatesRepaired`), and takes the first that
terminates (`List.findMap` over `withIndex`). It printed the right
answers on the first run, in 1.0 s for both parts.

The spec (`Spec/Spec.sw`) has the format (`InstructionWritten`: the
operation's word, a space, then `+` or `-` and decimal digits) and the
machine in the puzzle's words: `Executes instruction before after` (what
`acc`, `jmp` and `nop` do, quoted), `Step program before after` (the
console executes the instruction at its position), and `Runs program state
positions last` (from `state` it executes the instructions at `positions`,
in order, and is then at `last`). Then `Part1 program answer`: some run
from the start has executed no position twice (`List.Distinct
positions`) and is at one it has executed, with `answer` in the
accumulator; `Terminates program accumulator`: some run from the start
reaches the position just past the last instruction; `Repair program index
repaired`: the same length, every other instruction the same, and the one
at `index` a `jmp` made a `nop` or the other way round, with its argument;
and `Part2 program answer`: some repair terminates with `answer`. All are
propositions, so there is no spec test; the answers' tests are on the
program.

Proved (`Aoc.Year2020.Day08.Proofs`):

- `readsOperation`, `readsArgument`, `readsInstruction`: each parser reads
  its piece as the spec writes it. `parseWritten`: if `parseProgram` reads
  `input`, each line of it is its instruction written out.
- `runFromRuns` (Run.sw): for any `Code` holding a program's instructions
  (`Holds`), a run of `Code.runFrom` from any state, after positions `done`
  that it hasn't revisited, is a spec run whose positions, after `done`,
  are distinct, and it stops as its outcome says (`Ended`): at a position
  already executed for `Loops`, at the length for `Terminates`. Its
  induction follows `runFrom`'s own measure, `unvisited.size`.
- `getByPosition` (Map.get on `Map.byPosition` is `List.get`; std has it
  for `getOr` only), `codeHolds`, `unvisitedAll`, `runRuns`: the same from
  the start, for the program's own code.
- `part1Rules`: when part 1 gives an answer, it is `Spec.Part1`.
- `replaceAt` and its three lemmas, `repairedHolds` (the code with one
  `Map.insert` holds the program with one instruction replaced), `repairIs`
  (that program is a `Spec.Repair`), `repairTerminates`, `findMapFound`;
  `part2Rules`: when part 2 gives an answer, it is `Spec.Part2`.
- `part1Correct`, `part2Correct`: for every input the parser reads, its
  lines are the instructions written out and the answers are the spec's.

Not proved: that every well-formed input parses (as on days 2 to 7). That
the program always answers when the puzzle has an answer (completeness:
a `Loops` outcome whenever `Part1` holds, and a terminating repair found
whenever `Part2` holds); with the run deterministic, both are true and
within reach (`runFromRuns` gives the run, and two runs from the start
agree), but I didn't write them. That `Part1` names one answer (the same
determinism). `Part2` names one answer only if exactly one repair
terminates, which the puzzle promises and a test checks on the input;
the program takes the first.

Termination needed no unproved bound this time: the simulation is
`decreasing unvisited.size`, and two std lemmas (`Set.sizeRemovePresent`,
`Set.sizePositive`) prove each step smaller, so there is no fuel and no
"out of steps" outcome that a proof would have to rule out. Day 7's gap
(item 4 there) was a recursion over a relation, which has no such set to
shrink; a simulation that marks what it has visited does.

Breaking the program made the proofs fail: `position == code.length + 1`
for the end test fails `runFromRuns` (E-TYPE-MISMATCH, at the
`Terminates` case); starting with `1 ..< code.length` unvisited fails
`runRuns` (the initial `Unvisited`); repairing a `jmp` to a `jmp` fails
`repairIs` (E-REWRITE-NOTHING); `acc` subtracting fails `executeSteps`
(E-REFL).

### 1. A method named like another type's method makes `decreasing` see mutual recursion

My first `Code.runFrom` called `instruction.run state` (`Instruction.run`)
and failed:

```
[E-DECREASING] Error: `decreasing` isn't supported for definitions that call each other yet
 84 │     decreasing unvisited.size
    │ Note: `Code.runFrom`, `Code.run` call each other; give them a fuel argument for now
```

They don't: `Code.run` calls `Code.runFrom`, which calls `Instruction.run`.
Renaming it `Instruction.execute` fixed it. The call graph seems to resolve
`.run` by its short name. A repro (file mode):

```stitchwort
type Step = { by: Nat }
type Counter = { limit: Nat }

def Step.run (step: Step) (n: Nat): Nat := n + step.by

def Counter.runFrom (counter: Counter) (left: Nat) (n: Nat): Nat
    decreasing left
:=
  if h: 0 < left then Counter.runFrom counter (left - 1) (({ by = 1 }: Step).run n) [decreasing := omega] else n

def Counter.run (counter: Counter): Nat := counter.runFrom counter.limit 0
```

gives the same error, naming `Counter.runFrom` and `Counter.run`. A
newcomer would believe the note and add fuel, which is what the day
avoided. Compiler bug; `run`, `step` and `next` are the names a simulation
reaches for.

### 2. The index lemmas are for `getOr`; the program's lookups are `get`

The natural lookups are `Option`s: `Map.get` on the indexed code, and the
spec's `program.instructions.get index`. Std's lemmas are nearly all about
`getOr`: `Map.getOrByPosition` but no `Map.getByPosition` (I wrote
`getByPosition` with a copy of `Map.lookupLastWithIndex`'s induction, 17
lines), and no `List.get xs i = Some x → i < xs.length` (`getLength`, 4
lines; `stitchwort search` found only mine). There is no `List.set` /
`updated` either (Scala's `instructions.updated(index, …)` is what Matt's
solution uses), so the proof defines `replaceAt` with `lengthReplaceAt`,
`getReplaceAt` and `getReplaceAtOther` (20 lines); the program avoids it
by `Map.insert`. And `List.findMap` has only `findMapIsHeadFilterMap`: the
membership form (`findMapFound`, "what it finds comes from some `x ∈ xs`")
is mine, and 2024 day 24 has a weaker copy (`findMapSome`). Candidates:
`Map.getByPosition`, `List.getLength` (or `getSomeLt`), `List.set` with
`get`/`length` lemmas, `List.memOfFindMap`.

### 3. `Parse.int` doesn't read a leading `+`

Every argument here has a sign, `+0` included. `Parse.int` reads only an
optional `-`, so `"+3"` fails. I wrote `argument()` with `Parse.pick
[("+", False), ("-", True)]`, `Parse.nat()` and `Int.signed`, and its
reads proof by hand (13 lines, with `Pair.mkInjectiveFst`/`Snd` on the
`pick` membership). A `Parse.signedInt` (sign required, or an optional
`+`) with an `IntRead`-style spec would make it one call; `Parse.IntRead`
itself is close to what the spec says.

### 4. A proof can't follow the program's `if fresh:` with its own

In the proof, `if fresh: unvisited.contains position = True then ?` left
the goal holding `Decidable.elim (Bool.decEq (Set.contains unvisited
position) True) (fresh => Code.runFrom …) (fresh => Loops …)`: the
proof's decision is another term, so the program's `if` doesn't compute.
`match c: unvisited.contains position with | True | False` did (the
program's `Bool.decEq True True` then computes). That's reasonable once
seen, but the goal shows the elaborated `Decidable.elim`, not the `if` I
wrote, and nothing says to match on the `Bool`. A note on such a goal, or
the guide's §3 saying "to follow a program's `if h: b = True`, `match c:
b`", would have saved a round.

### 5. Messages

- **`Eq.symm`** (it is `Eq.sym`) with `import Std (Eq)` in place gave
  "unknown name `Eq.symm`; `Eq` is `Std.Eq`; add `import Std (Eq)`": the
  import was there, so the note is wrong; the name is. "did you mean
  `Eq.sym`" is what would help (Lean's is `Eq.symm`, so this will recur).
- **`rewrite` with an `↔`** is E-REWRITE-RULE ("isn't an equation"). I
  wanted `rewrite Set.containsFromListIff … in` and wrote the two
  directions by hand. Fine as a rule; the message could point at
  `.forward`/`.backward`.
- **`rewrite r at made` after `match r:`** was E-REWRITE-NOTHING with note 1
  "`made` is already refined: use it as it is", which was exactly right
  (day 6's complaint about the useful note coming last is fixed here).
- **`Some { instruction | operation = Nop }`** is E-PARSE with a note to
  bracket it; `Some { operation = Jmp, argument }` in the spec likewise
  (E-UNKNOWN-FIELD, then the note). Both clear; both cost a round trip.
- **`rewrite … at (term) in …`** (E-REWRITE-TARGET) says to drop `in` or
  name the term: clear.

### 6. Smaller things

- **Int support was enough.** `Int.toNatChecked` turned the position into
  an index with a `match`, `Nat.toInt`, `Int.signed` and
  `Int.ofNatInjective` were all there, and `State` arithmetic (`next +
  argument`) needed no lemmas, since the proofs never reason about
  positions as numbers, only as keys. `Int.ofNatInjective (m n: Nat)`
  takes its two numbers explicitly, though the hypothesis fixes them (an
  implicit-parameter candidate under D2422).
- **The new syntax.** `0 ..< code.length` read well in the program, and
  `List.memRange` (stated as `a ≤ x < b`) gave `unvisitedAll` at once.
  Ranges are `Nat` only, which is right here (the positions are an `Int`
  only until they're checked). Chained comparisons, `List.groupBy` and
  omega's range facts weren't needed; implicit lemma parameters
  (`Option.someInjective`, `DecEq.sound`, `Pair.mkInjectiveFst`) kept every
  call to its hypothesis.
- **`Set` lemmas were all there**: `containsRemove`, `containsRemoveOther`,
  `containsFromListIff`, `sizeRemovePresent`, `sizePositive`. So were
  `Map.getInsert`/`getInsertOther` and `List.memWithIndex`.
- **Record updates in the spec's arms.** `Instruction.execute` uses `{
  state | next = … }`; `Executes` matched it with `Both rfl rfl` per
  operation (record updates on records compute).
- **Audit.** 68 theorems, 0 failed, 1 warning: the generated equation
  `Code.runFrom.eq.some.some.ifTrue`, whose hypotheses (a position, an
  instruction there, still unvisited) held in none of 1500 random cases.
  They don't contradict each other (the tests run that arm on every step);
  random maps and sets just rarely line up.
- **Domain types.** `Instruction.execute`, `Instruction.repaired`,
  `Program.code`, `Code.run` and `Code.terminatesRepaired` read as the
  puzzle; the proofs state everything about `Program`, `State` and
  `Outcome`, and `Holds code program` is the one bridge.

### Size and time

126 lines of program, 92 of spec, 330 of proofs (Parse 44, Run 112,
Part1 52, Part2 101, Proofs 21), 63 of tests (+1 answer test in
`aoc_answers.rs`). By the clock, 5 minutes from reading the puzzle to the
program and its tests passing (16:20 to 16:25), and 9 more to every proof
checking (16:34); then audit, break checks and these notes. Nearly every
proof checked on the first or second try; the longest detours were items
1 and 4.

CPU time (load not measured):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day08.Proofs` | 7.2 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day08` | 3.4 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day08` (20 tests) | 8.8 s user |
| `task audit:touched -- Aoc.Year2020.Day08` (68 theorems) | 2.0 s user |
| `stitchwort run Aoc.Year2020.Day08.main` on the input | 1.0 s user |
| `task test:one -- year2020_day08` | 4.8 s for the test |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 152 ms of
elaboration; the rest of the cold time is std's modules.

### Ranked

1. A method with the same short name as another type's (`Instruction.run`
   beside `Code.run`) makes `decreasing` report mutual recursion that
   isn't there, and its note says to add fuel (item 1). Compiler bug;
   small to medium, repro in item 1.
2. Lookup lemmas are for `getOr`, not `get`: no `Map.getByPosition`, no
   `List.get … = Some x → i < length`, no `List.set`/`updated` with its
   lemmas, no `List.findMap` membership lemma (2024 day 24 has a weaker
   copy) (item 2). Missing library; small each.
3. `Parse.int` doesn't read `+`; no signed-number parser for a required
   sign (item 3). Missing library; small.
4. A proof's `if h:` doesn't follow the program's; `match c:` on the
   `Bool` does, and the goal shows `Decidable.elim` without saying so
   (item 4). Error message or guide; small.
5. `Eq.symm` gets a wrong "add `import Std (Eq)`" note instead of "did
   you mean `Eq.sym`" (item 5). Error message; small.
6. Completeness and uniqueness of both parts are unproved, though true
   and within reach (Not proved, above). Proof work; small to medium.
7. `rewrite` with an `↔` could point at `.forward`/`.backward` (item 5).
   Error message; trivial.
8. `Int.ofNatInjective` takes explicit numbers its hypothesis fixes
   (item 6). Library (D2422 sweep); trivial.

## Day 9: Encoding Error

XMAS-encrypted data, one number a line. After a preamble (25 numbers in
the puzzle, 5 in its example), each number should be the sum of two
different numbers among the preamble's worth just before it. Part 1 is
the first number that isn't; part 2 finds a contiguous run of at least two
numbers summing to it and adds the run's smallest and largest (the
"encryption weakness"). Answers on Matt's input (1000 numbers, up to about
6.4 × 10^13): 373803594 and 51152360; the example gives 127 and 62. I did
not run Matt's Scala (`Day9.scala`; I read it: `sliding(windowSize + 1)`
with `combinations(2)`, and every run of each length summed); an
independent Python script (a quadratic scan of every window and every run)
agrees on both answers and the example, finds exactly one run summing to
part 1's answer, and finds no window with a repeated value, so "different
numbers" read as different values (the puzzle: "The two numbers will have
different values") or as different positions (Scala's `combinations`) give
the same answers here. The spec takes values, as the puzzle says.

The domain types are `XmasData` (the numbers) and `Window` (the numbers
before one), with `window.sumsTo number`, `data.firstInvalid preamble` and
`data.weakness invalid`; the preamble is a parameter throughout, so the
example's tests say `(preamble := 5)` and `main` says `(preamble := 25)`.
Part 1 walks the list once, keeping it as `front` (the numbers from the
current window's start), and checks each number against
`Set.fromList` of the window, O(n · k log k). Part 2 is a two-pointer
sliding window over the same list, without arrays or indices: the window
is the first `count` numbers of `front`, and `rest` is what follows it.

```stitchwort
def runFrom (target: Nat) (front: List Nat) (count: Nat) (sum: Nat) (rest: List Nat): Option (List Nat)
    decreasing front.length + rest.length
:=
  if target < sum then
    match front with
      | [] => None
      | [first, ..later] => runFrom target later (count - 1) (sum - first) rest
  else if sum == target && 2 <= count then Some (front.take count)
  else
    match rest with
      | [] => None
      | [next, ..more] => runFrom target front (count + 1) (sum + next) more
```

Each step moves one end, so it is linear, and `decreasing front.length +
rest.length` needed no proof at all: the obligations in both arms were
discharged by themselves, in the program and in the two theorems that
recurse the same way. The weakness is `data.runSumming invalid |> .flatMap
List.nonEmpty |> .map (run => run.minimum + run.maximum)`, so the minimum
and maximum need no `Option`. The program, its 19 example and edge-case
tests and the 3 input tests all passed on the first run; `main` takes 0.5 s
user on the input.

**Is a 1D prefix sum or sliding window in std?** Partly. Std has
`List.scanLeft` (`xs.scanLeft 0 Nat.add` is the 1D prefix sums, with
`List.getOrScanLeft`), `List.windows` (fixed-size windows, Scala's
`sliding(n)`, with length lemmas), and `List.pairs`. Nothing finds a
contiguous run with a given sum; `Aoc.Common.PrefixSums` is the 2D table
(`runningSums` is `scanLeft` per row). The sliding window above needed no
library beyond `take`, `drop` and `sum`; a Common version would only pay
if another day needs it (item 5).

The spec (`Spec/Spec.sw`) has `NumberWritten` (decimal digits),
`SumOfTwo previous number` ("the sum of any two of the 25 immediately
previous numbers. The two numbers will have different values": some `a ≠
b`, both in `previous`, with `a + b = number`), `previous numbers preamble
position` (`numbers.drop (position - preamble) |> .take preamble`),
`Part1` ("the first number in the list (after the preamble) which is not
the sum of two of the 25 numbers before it": at some `position` after the
preamble, not a `SumOfTwo`, and every number between the preamble and it
is one), `Contiguous numbers run` (`(numbers.drop start).take length` for
some `start` and `length`), `Weakness numbers invalid answer` (a
contiguous run, `2 ≤ run.length`, summing to `invalid`, with `answer =
smallest + largest` for a `smallest` and `largest` in the run that bound
every `x ∈ run`, `smallest ≤ x ≤ largest`), and `Part2` (a weakness for
some `invalid` with `Part1`).

Proved (`Aoc.Year2020.Day09.Proofs`):

- `parseWritten` (Parse.sw): if `parseData` reads `input`, each line is
  its number written in decimal (6 lines: `Parse.eachLineReads` with
  `Parse.readsNat`, whose spec `NumberWritten` copies).
- `sumsToSound`, `sumsToComplete` (Window.sw): `window.sumsTo number` is
  `True` exactly when `SumOfTwo window.numbers number`.
- `walkAt`, `walkSound`, `part1Rules` (Part1.sw): when part 1 gives an
  answer, it is `Spec.Part1`'s. `walkComplete`, `part1Complete`: whenever
  `Spec.Part1` holds, part 1 gives that answer. `part1Unique`: `Part1`
  names one number ("the first" is one number), from completeness and the
  program being a function.
- `takeOneMore`, `runFromSound`, `toListNonEmpty`, `weaknessRules`
  (Part2.sw): when part 2 gives an answer, it is a `Spec.Weakness` of the
  invalid number.
- `sumTakeLe`, `sumDropTakeLe`, `shrinksInside`, `growsInside`,
  `runFromComplete`, `runSummingComplete`, `takeOwnLength`,
  `weaknessComplete` (Complete.sw): whenever some weakness exists, part 2
  finds one. The invariant is the textbook one: the window never starts
  after the run's start (at the start it would sum to at most the target,
  so it doesn't shrink) and never ends after the run's end (ending there it
  would sum to at least the target, and be as long as the run, so it is
  the answer).
- `part1Correct`, `part2Correct`, `part1Exactly` (an `↔`),
  `part2Complete` (Proofs.sw): for every input the parser reads, its lines
  are the numbers written out and the answers are the spec's; part 1
  answers exactly when the spec has an answer, and part 2 answers whenever
  the spec has one.

Not proved: that every well-formed input parses (as on days 2 to 8). That
`Part2` names one answer: two runs summing to the invalid number can have
different weaknesses, and the program takes the one it meets first; the
puzzle expects one, and on the input only one run exists (the Python
check, not a test). Everything holds for any preamble, 0 included.

Breaking the program made the proofs fail: dropping `a + a != number`
from `sumsTo` fails `sumsToSound` and `sumsToComplete`; `1 <= count`
instead of `2 <= count` fails `runFromSound`; checking against `front.take
(preamble - 1)` fails `walkSound` and `walkComplete`; `run.minimum +
run.minimum` fails `weaknessRules`; `target <= sum` (shrinking at an
exact sum, which is sound but finds nothing) fails the proofs that follow
the program's `if`; and starting the search at `data.numbers.drop 1`
(sound, but misses runs at the start) fails `runSummingComplete` and
`weaknessComplete`.

### 1. A proof can't follow `if a && b` with one `match`

`runFrom`'s middle test is `if sum == target && 2 <= count`. Day 8 (item 4
there) found that a proof follows a program's `if` by `match c:` on its
`Bool`. Here that doesn't work: after `match e: sum == target && 2 <=
count with | True => …`, the hypothesis about the call still read

```
Std.Decidable.elim (Std.Decidable.andThen (Bool.decTrue (Std.Decidable.toBool (Nat.decEq sum target))) (_ => Bool.decTrue (2 <= count))) (_ => Some (List.take front count)) (_ => None) = Some run
```

because an `if` on `a && b` decides `Decidable.andThen` of the two parts,
not the `Bool` `a && b`. Matching on `sum == target`, then on `2 <=
count`, does compute it, but the "grow" branch is then reached twice (when
the sum differs, and when it is right but the window is too short), so
`runFromSound` and `runFromComplete` each write it out twice (9 lines
each time). A newcomer who learnt day 8's trick would be stuck at the
goal above, which names neither `&&` nor what to match on. Fixes: make a
`match` on `a && b` also refine the `andThen` decision, or note on such a
goal that the condition splits into its parts.

### 2. `omega`'s atoms are compared as written, not as they compute

In `shrinksInside` I first had `within: (front.take count).sum ≤ (front.take
length).sum` and gave `omega [rewrite at, same at within in within]`. It
failed with a model where two atoms differ that are one value:

```
List.foldLeft (List.take (List.drop numbers start) count) 0 Nat.add
List.foldLeft (List.take (List.drop numbers start) length) Add.zero Add.add
```

The rewritten fact came out computed (`0`, `Nat.add`), the hypothesis
`sums` as written (`List.sum`, through the `Add` instance's fields), and
`omega` treats them as two unknowns. Stating each fact with its type
written out (`let windowSum: sum = ((numbers.drop start).take count).sum
:= rewrite <- same, <- at in total`) fixed it, and the same in
`growsInside`. The note listing the atoms is what showed it; `omega`
identifying atoms that compute to the same term (or at least unfolding
`Add.zero`/`Add.add` of a known instance) would remove the trap. It will
recur wherever a sum or a fold goes through `rewrite … at`.

*Correction (SW-1435):* `omega` already identifies atoms by a bounded
conversion check, and the two atoms above (`take … count` and `take …
length`) are different values. The model was real: the facts never linked
`sum` to the window (`total` was about `front`, not rewritten). The
annotated `windowSum` supplied that missing fact; with
`rewrite at, same at total in total` the annotations aren't needed
(`examples/accept/omega-atoms-by-conversion.sw`).

### 3. List lemmas: take, drop and sums over a run

Std's `take`/`drop` lemmas covered most steps (`List.dropAdd`,
`List.getDrop`, `List.lengthTake`, `List.lengthDrop`, `List.dropPast`,
`List.takeAll`, `List.sumCons`, `List.sumAppend`), but I wrote six:

- `takeOneMore`: `xs.drop k = [y, ..ys] → xs.take (k + 1) = xs.take k ++
  [y] ∧ k < xs.length` (6 lines). Std's `List.takeSucc` is the same step
  through `getOr` with a default, and needs `k < length` first; the
  program's own facts are about `drop`.
- `takeOwnLength`: `xs.take (xs.take n).length = xs.take n` and `(xs.take
  n).length ≤ xs.length` (6 lines). No `List.lengthTakeLe`.
- `sumTakeLe` and `sumDropTakeLe`: a shorter prefix, or a later slice,
  sums to no more (Nat only; 10 lines).
- `toListNonEmpty`: `xs.nonEmpty = Some ys → ys.toList = xs` (3 lines).
  Std has `List.nonEmptyToNonEmpty` the other way.
- There is no `List.takeNil` (`[].take n = []` for an unknown `n`), though
  `List.dropNil` exists; `rfl` fails on it since `take` matches the count
  first. `List.takeAll [] n (omega)` stands in.

Candidates: `List.takeOfDropCons`, `List.lengthTakeLe`, `List.takeNil`,
`List.sumTakeMono`, `List.toListOfNonEmpty`.

### 4. `!=` in a statement, and `DecEq.neTrue`'s converse

`let unequal: (a + a != number) = True` is E-NOT-A-TYPE: in a statement
`!=` is the proposition. The note says exactly what to write
(`((a + a != number): Bool) = True`), so it cost one round, but it reads
naturally and every proof about a program's `!=` will meet it. Then
proving that `Bool` from `a + a ≠ number`: std has `DecEq.neTrue`
(`(x != y) = True → x ≠ y`, with `x` and `y` explicit though the
hypothesis fixes them) but not its converse; `stitchwort search '(?x: Nat)
≠ ?y → ((?x != ?y): Bool) = True'` found `Decidable.toBoolOf` first,
which does it (`Decidable.toBoolOf _ (same => differ (omega))`). A
`DecEq.neTrueOf` beside `neTrue` would be the obvious name to look for.
My first try, `match c: a + a == number` with `rewrite c` in the `False`
arm, was E-REWRITE-NOTHING, because `!=` isn't `not (a == b)` but the
decision `Decidable.not (Nat.decEq …)`; the message showed the goal in
that form, which made the reason clear.

### 5. Shared logic: a pair summing to a target, again

Day 1's `findPair` finds two entries at different positions summing to a
target, with soundness and completeness proved. Day 9's check is the same
question with different values instead of positions, over a window, and I
wrote it again (`Window.sumsTo`, 2 lines, and 20 lines of proof) since
`findPair` returns the first pair, which could be one of equal values when
another pair would do. An `Aoc.Common` "pair summing to" with the
distinctness as a parameter could serve both, but the two proofs are short
and differ in what they need; I'd leave it until a third day asks. The same
goes for the run search (part 2): a Common `runSumming` with its two
theorems would be about 150 lines to move, worth it only for reuse.

### 6. Smaller things

- **A dead arm, honestly warned.** `firstInvalidFrom` matches
  `front.drop preamble` first and then `front`, to recurse on its tail;
  the `front = []` arm under a non-empty drop can't happen. The audit's
  warning `firstInvalidFrom.eq.cons.ifTrue.nil` ("no input made the
  hypotheses true") is correct: its hypotheses contradict each other. An
  as-pattern (`front@[_, ..rest]`) or a match on both at once would avoid
  the arm; neither exists. The other warning, `…ifTrue.cons`, is narrow
  (random windows rarely pass `sumsTo`), not contradictory.
- **A `let` missing an argument.** `let reached := growsInside … unfinished`
  left out the last argument, so `reached` was a function, and the next
  `omega` failed without listing it among its facts. Annotating the `let`
  gave "this expression is a function still waiting for `long`", which is
  excellent; `omega` could say when a `let` in scope has a function type
  ending in a fact it might have wanted.
- **What helped.** `decreasing` over two lists' lengths with no proofs
  written; `NonEmptyList.minimum`/`maximum` with `minimumMem`,
  `minimumLe`, `maximumMem`, `maximumLe`, whose `<=` through `Ord` was
  `omega`'s `≤` on `Nat` with no bridge; chained comparisons in the spec
  (`preamble ≤ earlier < position`, `smallest ≤ x ≤ largest`), which
  `omega` used as two facts; `1 ..= 25` for the puzzle's own examples in
  the tests; implicit lemma parameters (`Bool.andLeft`, `Bool.andRight`,
  `Bool.andIntro`, `DecEq.sound`, `Option.someInjective`) in every call;
  `List.anyTrueElim`/`List.anyOfMem` and `Set.containsFromListIff` for the
  window; named arguments at call sites (`data.firstInvalid (preamble :=
  25)`). Clause lambdas (`match some`, `matches`) had nothing to do here.
- **Proofs checked early.** Nearly every theorem checked on the first or
  second try; the detours were items 1, 2 and 4, an unknown `Eq.trans`
  without `import Std (Eq)`, and two `rewrite … in` that needed `at`.

### Size and time

83 lines of program, 51 of spec, 390 of proofs (Parse 14, Window 23,
Part1 95, Part2 92, Complete 131, Proofs 35), 74 of tests (+1 answer test
in `aoc_answers.rs`). By the clock: 16:54 start; program and tests passing
at 16:59; soundness proofs checked at 17:05; completeness at 17:13; then
audit, break checks and these notes.

CPU time (the machine was loaded; user time is the figure to read):

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day09.Proofs` | 8.3 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day09` | 3.0 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day09` (22 tests) | 8.9 s user |
| `task audit:touched -- Aoc.Year2020.Day09` (33 theorems) | about 2 s |
| `stitchwort run Aoc.Year2020.Day09.main` on the input | 0.45 s user |
| `task test:one -- year2020_day09` | 10.1 s for the test |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 286 ms of
elaboration, `runFromSound` the largest at 123 ms; the rest of the cold
time is std's modules.

### Ranked

1. A proof can't follow a program's `if a && b` with one `match`: the
   `if` decides `Decidable.andThen`, and the goal shows it without saying
   to split; the workaround duplicates a branch (item 1). Elaborator or
   message; small to medium.
2. `omega` treats atoms that compute to the same term as different
   (`List.sum` as written and as `rewrite … at` leaves it), with a model
   that looks like a counterexample (item 2). Proof tooling; medium.
3. Missing list lemmas: `take` one more after a `drop`, `lengthTakeLe`,
   `takeNil`, sum monotonicity over prefixes and slices, `nonEmpty`'s
   `toList` (item 3). Library; small each.
4. No converse of `DecEq.neTrue` (`x ≠ y → (x != y) = True`), and
   `neTrue` takes explicit `x`, `y` (D2422 candidate) (item 4). Library;
   trivial.
5. No as-patterns, so the walk has a dead arm and the audit warns about
   it (item 6). Language; small.
6. `omega` silently skips a `let` whose type is a function ending in a
   fact (item 6). Message; small.
7. A "pair summing to target" (day 1, day 9) and a "contiguous run
   summing to target" could live in `Aoc.Common` once a third day needs
   them (item 5). Common; not yet.
8. `Part2` names one answer only when one run sums to the invalid
   number (Not proved, above). Puzzle's promise; not a gap.

## Day 10: Adapter Array

A bag of joltage adapters, one rating a line. An adapter takes an input 1,
2 or 3 jolts below its rating; the outlet is 0 and the device is 3 above
the highest adapter. Part 1 chains every adapter and multiplies the number
of 1-jolt differences by the number of 3-jolt ones; part 2 counts the
arrangements (choices of adapters) that still connect the outlet to the
device. Answers on Matt's input (104 adapters, all different, every
difference 1 or 3): 2376 and 129586085429248; the examples give 35 and 8,
and 220 and 19208, as the puzzle says. I didn't run Matt's Scala
(`Day10.scala`: sorted differences grouped with `groupBy` for part 1, and a
mutable `Map` from joltage to path count, filled from the top, for part 2);
an independent Python script (sorted differences, and the usual
`ways[x] = ways[x-1] + ways[x-2] + ways[x-3]`) agrees on all six answers.

The domain types are `Bag` (the ratings), `Chain` (joltages from the
outlet to the device, with `chain.fits` and `chain.differences`) and
`Onward` (an adapter and the number of ways on from it to the device), with
`bag.device`, `bag.chain device`, `bag.distribution` and
`bag.arrangements`; `canFeed lower higher` is the one rule. Part 2 is the
dynamic programme as a plain recursion over the sorted list, with no map
and no array: each adapter's onward count is computed from the counts of
the adapters above it, which the recursion has just built.

```stitchwort
def waysFrom (device: Nat) (joltage: Nat) (above: List Onward): Nat :=
  (if canFeed joltage device then 1 else 0)
    + (above.takeWhile (next => next.joltage <= joltage + 3)).sumBy (next => if canFeed joltage next.joltage then next.ways else 0)

def onwardFrom (device: Nat): (adapters: List Nat) → List Onward
  | [] => []
  | [adapter, ..higher] =>
    let above := onwardFrom device higher
    [{ joltage = adapter, ways = waysFrom device adapter above }, ..above]
```

The `takeWhile` makes it linear (it looks at the next few adapters only,
since they are sorted) and is the one place the proof needs sortedness.
The program and its 20 tests passed on the first run after two slips of
mine (an example text block whose last line ran into the closing `"""`, and
a test expecting two arrangements where there is one); `main` takes 0.35 s
user on the input.

The spec (`Spec/Spec.sw`) has `RatingWritten` (decimal digits), `Takes
input rating` ("can take an input 1, 2, or 3 jolts lower than its rating",
written as `[1, 2, 3].contains (rating - input)`), `Highest adapters
highest` (in the bag, and no adapter above it), `Connects adapters device`
(from 0 through `adapters` to the device, each takes the one before:
`[0, ..adapters, device].chain Takes`), `differencesOf joltages d` (how
many times the next joltage is `d` higher), `Part1` ("if you use every
adapter in your bag at once": some ordering `chain` of the bag, a
`List.Perm`, that connects, and the answer is its 1-differences times its
3-differences), `subsequences` (every way of keeping some elements in
order), and `Part2` ("the total number of distinct ways you can arrange the
adapters": the count of subsequences of the sorted bag that connect). Part
1's spec never mentions sorting: that the only ordering that connects is
the sorted one is proved (`connectsSorted` and std's
`List.sortOfSortedNat`). Part 2's does sort, since an arrangement can only
go up; two adapters with the same rating would count as different ones,
which no input has.

Proved (`Aoc.Year2020.Day10.Proofs`):

- `parseWritten` (Parse.sw): if `parseBag` reads `input`, each line is its
  rating written in decimal (as day 9's, 6 lines).
- `canFeedTakes`, `fitsConnects`, `deviceHighest`, `deviceOfHighest`,
  `differencesCount`, `connectsSorted` (Facts.sw): the program's rule is
  the spec's `Takes`; `chain.fits` is `Connects`; `bag.device` is the
  highest rating plus 3, both ways; counting `differences` equal to `d` is
  `differencesOf` for `d ≥ 1`; a chain that connects is sorted.
- `part1Rules`, `part1Complete` (Part1.sw): part 1's answer is a
  `Spec.Part1` answer, and whenever `Spec.Part1` holds, part 1 gives that
  answer.
- `connectingNil`, `connectingCons`, `sortedOnward`, `takeWhileKeep`,
  `takeWhileStop`, `cutAbove`, `waysFull`, `onwardCounts`, `part2Rules`,
  `part2Complete` (Part2.sw): the spec's count from a joltage over a list
  splits on its first adapter (left out, or gone through); on a sorted
  table the `takeWhile` cut loses nothing; the onward count from any
  joltage over sorted adapters is the spec's count; so part 2's answer is
  `Spec.Part2`'s, and part 2 answers whenever the spec does.
- `part1Correct`, `part2Correct`, `part1Exactly`, `part2Exactly` (both
  `↔`), `part1Unique` (Proofs.sw): for every input the parser reads, its
  lines are the ratings written out and the answers are the spec's; each
  part answers exactly when the spec has an answer (a non-empty bag, and
  for part 1 a bag that chains), and part 1's answer is the only one.
  Part 2's is a count, so it is one number by definition.

Not proved: that every well-formed input parses (as on days 2 to 9).
Nothing else: the dynamic programme equals the spec's exponential count in
full, for any bag, duplicates included.

Breaking the program made the proofs fail: `higher < lower + 3` in
`canFeed` fails `canFeedTakes` (E-CASES) and `connectingNil`; stopping the
`takeWhile` at `joltage + 2` fails `waysFull` (it would lose an adapter 3
up); counting `d == 2` for part 1 fails `part1Rules` and `part1Complete`;
running part 2 over the unsorted bag fails `part2Rules` and
`part2Complete` (`onwardCounts` needs sorted adapters); and a device 4
above the highest fails `deviceHighest` and `deviceOfHighest`. The audit
(with the counterexample search): `audited 35 theorems: 0 failed, 0 with
warnings, 35 passed`.

### 1. A `match` on a comparison rewrites it inside unfolded definitions too

My first `cutAbove` was about `onwardFrom device adapters` itself. In the
`[adapter, ..higher]` arm I split on `match near: adapter <= joltage + 3`
and stated the two `sumByCons` steps inside the arm. `rewrite` and then
`omega` both failed, on goals pages long. `omega`'s Note 3 said why,
correctly:

```
`List.foldLeft (onwardFrom device higher) (if joltage < adapter && False then …) …` and
`List.foldLeft (onwardFrom device higher) Add.zero (acc x => acc + through joltage x)`
differ only in `if joltage < adapter && False then (…) else 0` and `0`, and no fact connects them
```

The goal had computed `onwardFrom`, `waysFrom` and `canFeed joltage
adapter` (whose second half is the same `adapter <= joltage + 3`), so the
`match` refined that copy to `False`, and in the other arm to `if if
joltage < adapter then True else False`, while the facts I stated after
the `match` kept the original form. Two fixes together worked at once:
state the lemma for any table sorted by joltage (`List.Sorted lowerFirst
table`, with `onwardFrom`'s sortedness a separate 3-line lemma), so the
goal has no definitions to unfold; and split with `if h: first.joltage <=
joltage + 3`, which refines nothing, stepping `takeWhile` with two lemmas
(`takeWhileKeep`, `takeWhileStop`: `p x = True → [x, ..xs].takeWhile p =
[x, ..xs.takeWhile p]` and the `False` one, one line each, not in std).
The proving guide's "small lemmas over any list" (§2, 3) is the advice;
what was missing is a hint at the moment. `omega`'s Note 3 could say that
one of the two forms came from a `match` refinement, and suggest stating
the facts before the `match` or using `if h:`.

### 2. `omega` drops a fact whose `≤` is `Ord`'s, even when given

`deviceOfHighest` needs `highest = ordered.maximum` from two bounds.
`let below := NonEmptyList.maximumLe ordered highest high.left` has type
`highest <= ordered.maximum` through the `Ord` instance, and `omega`
ignored it: its note listed one fact (`above`), with a model where the two
differ. Annotating it (`let below: highest ≤ ordered.maximum := …`)
fixed it. On a scratch file, `omega [NonEmptyList.maximumLe xs h m]` drops
it the same way, silently, while `(le: a <= b)` on `Nat` works. Day 9
(item 6) used these lemmas where an expected type asked for `≤`, and the
`Ord` `<=` converted to it; `omega` takes a fact by its own type, so
nothing converts it. Fixes: `omega` reading
`Ord.le` (or `Ord.compare … ≠ Greater`) at the `Nat` and `Int` instances,
or at least a note naming a fact in scope it skipped (as day 9 item 6
wanted for function-typed `let`s), and certainly not dropping one passed
in `omega [...]` without a word.

### 3. No `subsequences` in std, and its counting lemma

Part 2's spec needs every subsequence of a list. Std has the
`List.Subsequence` relation but no function listing them; I wrote
`subsequences` in the spec (3 lines), and `connectingCons` (6 lines:
`List.countAppend`, `List.countMap`, `List.countFalse`) is the step every
proof about it needs: the count over the subsequences of `[x, ..xs]` is
those leaving `x` out plus those keeping it. Day 1 (item 1) asked for
`List.combinations k`; a `List.subsequences` with a membership lemma
(`s ∈ xs.subsequences ↔ List.Subsequence s xs`) and a `countSubsequences`
step lemma would serve both, and any "how many ways to choose" spec.

### 4. Lemmas a newcomer would look for

- `takeWhile` one step: std has `List.takeWhileAppend`,
  `List.takeWhileMap` and `List.takeWhileRangeCutoff` but not the cons
  step with the predicate's value (`takeWhileKeep`, `takeWhileStop`
  above); with them, cutting a sum at a `takeWhile` was 20 lines.
- A chain of a stronger relation is sorted: `connectsSorted` (10 lines)
  shows `[low, ..chain, device].chain Takes = True → List.Sorted Nat.leq
  chain`. Std has `List.sortedOfChain` (for the same relation),
  `List.chainCong`, `List.chainTail` and `List.chainInit`; a
  `List.chainMono` (`chain p → (p x y → q x y) → chain q`) would have
  made it three calls.
- `(if c then 1 else 0) + 0 = (if c then 1 else 0)` isn't `rfl` (`+`
  recurses on its first argument, which is stuck); `omega` closes it.
  Known, and the guide says so, but it is the first goal of most counting
  proofs.

### 5. Goals print folds and spreads in their computed forms

Every goal about `sumBy` showed `List.foldLeft … Add.zero [add :=
Nat.instAdd] (acc x => acc + …)`, and the spec's `[0, ..chain, highest +
3]` printed as `[0, ..List.append chain [highest + 3]]`, neither the
spread I wrote nor `chain ++ [highest + 3]`. syntax.md says `++` stays
`++` in goals; here it is `List.append` inside a spread. Folding `sumBy`,
`count` and `sum` back when printing, and printing a middle spread as
written, would make the goals of item 1 a few lines instead of pages.

### 6. Smaller things

- **What helped.** `cases` proved `canFeed lower higher = Takes lower
  higher` (`lower < higher && higher <= lower + 3` against `[1, 2,
  3].contains (higher - lower)`) and `(step.snd - step.fst == d) =
  (step.snd == step.fst + d)` for `1 ≤ d` on its own, so the spec could
  say "1, 2, or 3 jolts lower" literally. `omega` read `canFeed x y =
  True` through the definition, and proved `Bool` goals such as
  `(first.joltage <= joltage + 3) = True` directly. `List.sortOfSortedNat`
  and `List.sortPerm` made part 1's spec ("every adapter, in an order that
  connects") two lines away from the program's sorted chain.
  `List.chainCong` turned `fits` into `Connects` in one line.
  `match a: bag.adapters` refined `bag.device` in the hypothesis, so the
  empty bag was one `Void.exfalso`. Middle spreads (`[0, ..adapters,
  device]`) read like the puzzle. `onwardCounts`, the main induction, and
  `part2Rules` checked on the first try.
- **`Bool.toNat` needs `import Std (Bool)`.** The message said exactly
  that; I wrote `if … then 1 else 0` instead, which reads better anyway.
- **The DP needs no map.** Matt's Scala fills a mutable `Map`; the
  recursion over the sorted list, carrying the counts above, is both
  shorter and the shape the proof follows. A newcomer coming from Scala or
  Python would reach for the map first; a worked example of "dynamic
  programming over a sorted list" in the guide would point the other way.

### Size and time

73 lines of program, 53 of spec, 223 of proofs (Parse 14, Facts 46,
Part1 30, Part2 98, Proofs 35), 100 of tests (+1 answer test in
`aoc_answers.rs`). By the clock: 22:42 start; program and tests passing at
22:48; part 1 proved at 22:50; part 2 at 22:52 (item 1 was the only
detour); then the answer test (5 minutes, nearly all building the test
binaries in a new worktree), break checks and these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day10.Proofs` | 5.1 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day10` | 1.4 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day10` (20 tests) | 5.3 s user |
| `task audit:touched -- Aoc.Year2020.Day10` (35 theorems) | about 3 s |
| `stitchwort run Aoc.Year2020.Day10.main` on the input | 0.34 s user |
| `task test:one -- year2020_day10` | 1.6 s for the test |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 104 ms of
elaboration and 41 ms in the kernel; the rest of the cold time is std's
modules.

### Ranked

1. `omega` silently drops a fact whose `≤` is `Ord`'s `<=` (from
   `NonEmptyList.maximumLe`, `minimumLe` and the like), even when passed
   in `omega [...]` (item 2). Proof tooling; small to medium.
2. A `match` on a comparison refines its copies inside unfolded
   definitions, so facts stated after it no longer match the goal; the
   fix (generalise, `if h:`) is known only from the guide (item 1).
   Message; small.
3. No `List.subsequences` (with membership and a counting step), the
   spec of every "how many ways" puzzle, as day 1's `combinations` (item
   3). Library; small.
4. Missing lemmas: `takeWhile`'s cons step by the predicate's value,
   `List.chainMono` (item 4). Library; trivial each.
5. Goals print `sumBy` and `count` as their folds and a middle spread as
   `..List.append xs [y]` (item 5). Printing; small to medium.

## Day 11: Seating System

A waiting area's seat layout, a grid of floor (`.`), empty seats (`L`)
and occupied seats (`#`). In each round every seat changes at once: an
empty seat with no occupied seat in view fills, and an occupied seat with
too many occupied seats in view empties. The rounds go on until one changes
nothing, and the answer is how many seats are occupied then. In part 1 a
passenger looks at the eight positions around, and four occupied seats are
too many; in part 2 they look at the first seat in each of the eight
directions, past any floor, and five are too many. Answers on Matt's input
(91 rows of 99, 7264 seats): 2354 and 2072, settling after 75 and 83
rounds that change something; the example gives 37 and 26, as the puzzle
says. I didn't run Matt's Scala; an independent Python script (plain
loops over a list of lists) agrees on all four answers.

The domain types are `Seat` (`Floor`, `Empty`, `Occupied`, with
`seat.next occupiedInView tolerance` and `seat.isSeat`), `Layout` (a
`Grid Seat`, with `layout.occupied`, `layout.round plan`,
`layout.settle plan rounds` and `layout.settledOccupied rule`), `Rule`
(the positions a passenger looks at, given a lookup, and the tolerance:
`adjacentRule` and `layout.sightRule`) and `Plan` (a rule worked out once
for a floor plan, `rule.planFor layout`). Part 2's look is `firstSeat`, a
walk out along one of the eight `compass` offsets, `distance` steps at a
time, that stops at the first non-floor cell or the edge. The program and
its 22 tests passed on the first run, examples and input.

`main` took 42 s at first (16 s part 1, 26 s part 2), which is slow; item
1 says where the time goes. Floor never changes, so the seats each
passenger looks at are the same in every round: `Rule.planFor` works them
out once on the start layout (seats only, looking only at seats), which
halved it to 20 s (19.3 s user). That needed a proof that the rounds keep
the floor plan (`Plan.sw`), about 40 minutes and 81 lines.

The spec (`Spec/Spec.sw`) has `becomes` (the three rules as written:
"if a seat is empty (L) and there are no occupied seats adjacent to it,
the seat becomes occupied…"), `round` (every seat at once, from a count
per position), `occupiedSeats`, `Settles round start final` (some number of
rounds from `start` reaches `final`, and a round changes nothing there),
`occupiedAdjacent` (the layout's cells `touching` the seat that hold an
occupied seat), `adjacentRound`, `Part1` (some settled layout, and the
answer is its occupied seats), `directions` (the steps of at most one row
and one column that move), `cellAlong` and `lineOfSight` (the cells 1, 2,
3, … steps away, nearest first, up to the edge), `firstSeen` (the first
cell on the line of sight that isn't floor), `occupiedSeen`,
`sightRound`, `Part2`, and `symbol` and `RowWritten` for the input. The
spec is computable, so the tests run its rounds beside the program's on
the example (5 and 6 rounds); that checked the spec as much as the
program.

Proved (`Aoc.Year2020.Day11.Proofs`):

- `readsSeat`, `gridWritten`, `parseWritten` (Parse.sw): if `parseLayout`
  reads `input`, each line is its row of the layout, one character a
  position, and the layout is a rectangle. Day 3's proof, nearly word for
  word, with std's `Parse.readsPickBy`.
- `nextBecomes`, `lookupOccupied`, `roundSpec`, `aroundOccupied`
  (Rounds.sw): the program's seat change is the spec's `becomes`; a round
  whose count at every seat is the spec's count is the spec's round
  (floor cells needn't count); part 1's count over `at.around` with the
  table is `occupiedAdjacent`.
- `countFilterMap`, `firstSeatCong`, `walkSeen`, `anyLookup`,
  `seenOccupied`, `compassDirections`, `sightOccupied`, `roundShape`,
  `firstSeatPlan` (Sight.sw): the walk ends at an occupied seat exactly
  when the first seat on the spec's line of sight is occupied, for a reach
  of the height plus the width; the program's eight directions are the
  spec's; so part 2's count is `occupiedSeen`. The walk depends only on
  where the seats are.
- `SamePlan`, `becomesIsSeat`, `mapKeepsSeat`, `roundPlan`, `startSeat`,
  `occupiedSeat`, `planInView`, `planCount` (Plan.sw): a spec round keeps
  the floor plan, and on a layout with the start's floor plan a seat's
  planned view counts what the rule sees on the layout itself.
- `settleSound`, `settlesOfWithin`, `settledUnique`, `settleComplete`
  (Settle.sw), for any plan whose round is a spec round on the layouts
  reached: what `settle` stops at is reached by fewer spec rounds than it
  was given and a round leaves it alone; if the spec's rounds reach such a
  layout in fewer rounds than `settle` is given, `settle` stops there; and
  the rounds settle on at most one layout.
- `sameSight`, `adjacentAgrees`, `sightAgrees`, `adjacentKeeps`,
  `sightKeeps`, `keptStart`, `settledExactly`, `part1Exactly`,
  `part2Exactly` (both `↔`), `answerOfWithin`, `part1Rules`, `part2Rules`,
  `answerUnique`, `part1Unique`, `part2Unique` (Parts.sw): each part
  answers exactly when the spec's rounds settle within `roundLimit` (1000)
  rounds, with the occupied seats of the settled layout; that answer is a
  `Spec.Part1`/`Part2` answer, and those name one number.
- `part1Correct`, `part2Correct` (Proofs.sw): for every input the parser
  reads, its lines are the rows written out and the answers are the
  spec's.
- In `Aoc.Common.Proofs`: `countAround` (GridAround.sw: counting the
  positions `around` a cell whose cell passes `keep` counts the cells
  `touching` it that pass), and `mapCellsCongAt` (GridCells.sw:
  `mapCells` of functions equal at the rows' cells).

Not proved:

- That the rounds settle at all. Nothing in the rules gives a measure
  (seats go both ways), so `settle` has fuel, `roundLimit = 1000` rounds,
  and `part1Exactly`/`part2Exactly` say exactly what happens: an answer
  when the spec's rounds settle within the limit, none otherwise. On the
  input `settle` runs 76 and 84 rounds, the last changing nothing.
- That the spec's line of sight is long enough. `lineOfSight` looks
  `height + width` steps out, and its doc says a line leaves the layout
  within that; it is true on a rectangle (each step moves a row or a
  column), which every parsed layout is, but not proved. On a ragged layout
  the bound could cut a long row short; the program has the same bound, so
  the proofs hold either way.
- That every well-formed input parses (as on days 2 to 10).

Breaking the program made the proofs fail: `tolerance < occupiedInView`
fails `nextBecomes` (E-CASES); dropping the last compass direction fails
`compassDirections`; stopping the walk at floor fails `firstSeatCong`,
`walkSeen` and `firstSeatPlan`; planning only the empty seats in view
fails `planInView`; and `settle` returning the layout after the last round
fails `settleSound` and `settleComplete`. The audit (with the
counterexample search): `audited 74 theorems: 0 failed, 0 with warnings,
74 passed`; `Aoc.Common.Proofs`: `audited 159 theorems: 0 failed, 0 with
warnings, 159 passed`.

### 1. Slow: a round is 9,000 table lookups, at about 2 µs each

On the default runtime, a round of part 1 took 0.21 s: 0.12 s for the
72,000 `Grid.lookup` calls (eight per cell; each is two `Map.getOr`s, row
then column, about 1.7 µs together), 0.085 s for 9,000 `Position.around`
calls (about 10 µs each: two `List.range`s, a `flatMap`, a `filter` and
nine records, for eight positions), and under 0.01 s for `Grid.map`, the
table and the `==` that checks for a change. Part 2's walk made its rounds
0.31 s. Planning the views once brought both to about 0.12 s a round, all
lookups; `lookupOr Floor` instead of `lookup` saved another 8% (not kept:
it would change every proof's lookup). The same final program takes 4.1 s
under `--js` and 3.7 s under `--native`, against 19.3 s.

| version | default | `--js` | `--native` |
| --- | --- | --- | --- |
| a round's rule looked up each round | 41.9 s | 4.5 s | 9.7 s |
| views planned once | 19.3 s | 4.1 s | 3.7 s |

Std has no array with constant-time `get`: `Vec` is a list, and
`Map.byPosition` is the way to index, so every grid simulation pays a
`Map` walk per neighbour. Two things would make this day fast without
changing its proofs much: a persistent array (or `Grid` backed by one)
with `get`/`set` lemmas, and a cheaper `Position.around` in Aoc.Common
(eight offsets, not ranges and a filter), kept equal to today's by a
lemma so `aroundTouching` and the rest carry over. A newcomer who writes
the obvious program waits 40 s and has no profiler to ask why;
`STITCHWORT_TIMINGS` covers checking, not running. I found the split by
timing variants of `main`, 10 rounds each.

### 2. Aoc.Common has no eight directions and no ray

Part 1 was `at.around` and a count: Aoc.Common had it, and 2021 day 11's
proof showed how to tie it to `touching`. Part 2 needed what isn't there:
the eight directions as offsets (`compass`, 10 lines; `Direction` has four),
a walk along a ray to the first cell that passes a test (`firstSeat`), and
in the spec the cells along a ray up to the edge (`cellAlong`,
`lineOfSight`). The proof that the walk finds the spec's first seat
(`walkSeen` with `firstSeatCong`, `firstSeatPlan` and the counting lemmas,
70 lines) is generic in the lookup. A shared `Grid.ray at offset` (cells
along a line, nearest first, to the edge), `compass`, and a
`firstAlongRay` with the lemma that it is `(grid.ray at d).find keep`
would make part 2 a few lines; 2024 day 4 (XMAS in eight directions) and
day 6 (walking until the edge) would have used it.

I moved the counting lemma into Aoc.Common: `countAround` (any rows, any
`keep`) is 2021 day 11's `countAround` generalised, with the off-grid
case handled inside, so the next day needn't copy it. 2021 day 11 could
now use it. `mapCellsCongAt` (`mapCells` agrees when the functions agree
on the cells, not everywhere) was needed for `roundSpec`, where floor
cells needn't count.

### 3. "Run until stable" needs a fuelled loop and its lemmas

Std has `Nat.iterateUntilStable`, which needs a measure that shrinks at
every change; the seating rules have none I know (seats fill and empty).
So `settle` has fuel, and `Settle.sw` proves what it means (60 lines): what
it finds is a fixed point reached by rounds, it finds one whenever there is
one within the fuel, and the rounds settle on at most one layout. None of
it is about seats: it is any `step: a → a` with `DecEq`, and 2021 day 11's
`cascade` is the same shape. A std
`Nat.iterateUntilStableWithin fuel step x: Option a` with those three
lemmas (`…Sound`, `…Complete`, `…Unique`, the last from
`Nat.iterateFixedLater`) would have made Settle.sw a few calls.

### 4. A `match` refines the goal as written, not what it computes to next

`walkSeen` says the walk ends at an occupied seat exactly when the spec's
first seen seat is occupied. Its step splits on `match find next`, and
the arms for `Some Empty` and `Some Occupied` failed with `rfl`:

```
[E-REFL] Error: `rfl` can't prove this
   ╰─── `Std.Decidable.toBool (Option.decEq (x y => …) (find next) (Some Occupied))` and `False` aren't equal
```

The `match` had refined the walk's own `match find next` to `Some Empty`,
so the walk returned `Some next`; then `Option.any` applied the test,
`find next == Some Occupied`, a new occurrence the refinement never saw.
`match e: find next` and `rewrite e in rfl` fixed both. My first version
was about `layout.grid.at` rather than any `find`, and there `match
layout.grid.at next` refined nothing at all: the goal had computed
`Grid.at` into `cellAt`'s inner `match` on `rows.get next.row`. The note
pointed at `cellAt.eq.some`; generalising the lemma over the lookup
function was the fix, and is the better statement anyway. Day 10's item 1
was the other direction (a refinement reaching into unfolded definitions).
An E-REFL whose two sides differ only in a term a `match` of the same
proof split on could say so, and suggest `match e:` and `rewrite e`.

### 5. Messages

- **E-RESOURCE without a cause.** `settledExactly` first had the limit
  written as `roundLimit` (1000) and failed with:

  ```
  [E-RESOURCE] Error: ran out of resources: a value was too large to show
     Note 1: this isn't a type error or a failed test: there's no answer within the limits
     Note 2: it happened while checking `settledExactly`
  ```

  Replacing halves with `?` put it in the `forward` half, at `match found:
  start.settle rule roundLimit`: refining `solved`, whose type computes
  through `settledOccupied`, seems to unfold `settle` 1000 rounds deep
  (both arms of each stuck `if`). Stating the theorem for any `limit` and
  instantiating it fixed it at once. The guide says the last note names
  the definition being unfolded; here none did, and "too large to show"
  doesn't say what was being shown or why. Naming `settle` and suggesting
  a variable for the large literal would have saved the bisecting.
- **`at` after a rewrite rule.** `rewrite counts at in …`, with `at` a
  position, is a parse error: `at` is reserved after a rule. The message
  says exactly that, but Aoc.Common names positions `at` everywhere
  (`Position.around (at)`, `touching at other`), so a newcomer copies the
  name into proofs and meets it. Renaming to `position` fixed it.
- **`omega` with an unnamed comparison.** `match Nat.leq m n with | True =>
  … (omega)` failed with "facts: none in scope"; `match order: Nat.leq m
  n` worked. The note could say the `match` has no equation to give it.
- **Helped:** E-REWRITE-NOTHING's "the proof checks without this rewrite:
  the goal already computed past it; drop the `rewrite`" (on `compass`), and
  its "`passes` is already refined: use it as it is" (in `countAround`);
  each was the fix. The notes for missing imports (`Exists`, `Void`, `Nat`)
  and for an uppercase parameter name (`Keep`) were exact.

### 6. Smaller things

- **What helped.** `parseGrid`, `Parse.readsPickBy` and day 3's
  `parseWritten` made the parser and its proof a few minutes. `Grid.ext`,
  `Layout.ext`, `mapCellsCong`, `cellAtMapCells`, `lookupAt`,
  `lookupOrAt`, `mapWidth`, `Nat.iterateFixed` and
  `Nat.iterateFixedLater` were each the one call needed. `cases` proved
  `nextBecomes` (the program's `match` against the spec's `if … && …`) and
  `becomesIsSeat` alone. Generic lemmas (Settle.sw over any spec round
  and any kept property, `settledExactly` over any plan) made part 2 cost
  nothing once part 1 was done.
- **No `Result.isErr`.** Std has `Result.isOk`; tests read `not (parsed
  "L.X\n").isOk`.
- **An interpolation can't span lines.** `"${Nat.iterate 10 (x => …`
  broken over two lines is "this string isn't closed"; the message could
  say that `${…}` has to close on its line.
- **A `Grid` from new rows needs its proof.** Timing a round that zips the
  rows with the planned views, I couldn't build `Grid.lookupOr` on the new
  rows: `{ rows = x, nonEmpty = l.grid.nonEmpty }` doesn't check, as the
  proof is about the old rows. I inlined the table. A `Grid.zipWith` (two
  grids of one shape) carrying the proof would let a program zip a state
  with a plan, which is also faster than a lookup per cell.
- **The tests take as long as `main`.** `stitchwort test --no-cache` takes
  30 s user (55 s before the plan), nearly all of it the two real-input
  answers; day 10's takes 5 s.

### Size and time

130 lines of program, 106 of spec, 411 of proofs (Parse 42, Rounds 43,
Sight 140, Plan 81, Settle 70, Parts 113, Proofs 22), 159 of tests (+1
answer test in `aoc_answers.rs`), and 55 in Aoc.Common.Proofs
(`countAround`, `mapCellsCongAt`). By the clock: 23:01 start; program
and tests passing at 23:10; part 1's round proved at 23:12; part 2 and the
parts at 23:17 (item 5's E-RESOURCE the only detour); the floor plan
precomputation and its proofs at 23:24; then the audit, the break checks,
timing and these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day11.Proofs` | 10.6 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day11` | 5.5 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day11` (22 tests) | 29.9 s user |
| `task audit:touched -- Aoc.Year2020.Day11` (74 theorems) | about 10 s |
| `stitchwort run Aoc.Year2020.Day11.main` on the input | 19.3 s user |
| `task test:one -- year2020_day11` | 25.8 s for the test |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 432 ms of
elaboration and 73 ms in the kernel; the rest of the cold time is std's
modules and Aoc.Common.

### Ranked

1. `main` takes 20 s (42 s as first written): every neighbour is a `Map`
   walk, std has no constant-time array, and `Position.around` costs
   10 µs a call (item 1). Speed and library; medium (an array) or small
   (a cheaper `around` with a lemma).
2. Aoc.Common has no eight directions as offsets and no ray to the edge
   with a "first cell that passes" lemma; part 2's walk and its 70 lines
   of proof are generic (item 2). Aoc.Common; small.
3. No fuelled "iterate until stable" in std with soundness, completeness
   and uniqueness lemmas; Settle.sw is 60 generic lines, and 2021 day 11
   has the same shape (item 3). Library; small.
4. E-RESOURCE "a value was too large to show" names no definition when a
   `match` on a call with a large literal argument (`settle … 1000`)
   blows up; generalising the literal fixes it (item 5). Message; small.
5. A `match` doesn't refine an occurrence that only appears after the
   goal computes further; E-REFL could point at the `match` and suggest
   `match e:` with `rewrite e` (item 4). Message; small.
6. Smaller: `Result.isErr`; `at` as a name in Aoc.Common meeting
   `rewrite … at`; `omega` on an unnamed `match` comparison; interpolations
   over two lines; a `Grid.zipWith` (items 5, 6). Each trivial to small.

## Day 12: Rain Risk

A ferry's navigation instructions, one a line, each a letter and a value
("F10", "N3", "R90"). In part 1 N, S, E and W move the ship, L and R turn
it by the given degrees, and F moves it forward the way it faces; it starts
facing east. In part 2 N, S, E and W move a waypoint that starts 10 east
and 1 north of the ship, L and R rotate the waypoint about the ship, and F
moves the ship to the waypoint the given number of times. Each answer is
the ship's Manhattan distance from its start. Answers on Matt's input (783
instructions; every turn is 90, 180 or 270 degrees): 415 and 29401; the
example gives 25 and 286, as the puzzle says. Matt's Scala (`Day12.scala`)
rotates the waypoint with `cos` and `sin` of the angle in radians and
rounds; I didn't run it. An independent Python script (quarter turns,
`(x, y) → (y, -x)` clockwise) agrees on all four answers.

The domain types are `Heading` (`North`, `East`, `South`, `West`, with
`heading.clockwise` and `heading.turned quarters`), `Side` (`Left`,
`Right`), `Action` (`Move heading`, `Turn side`, `Forward`),
`Instruction` (an action and its value), `Route` (the instructions),
`Location` (`east` and `north` as `Int`s, with `moved`, `plus`, `times`,
`rotated` and `manhattan`), `Ship` (a location and a heading) and
`WaypointShip` (a location and a waypoint), each with `follow
instruction`; the answers are `route.shipDistance` and
`route.waypointDistance`, a `foldLeft` of `follow` from the start. The
one design decision is turning: the parser rejects a turn that isn't a
multiple of 90 degrees, and `clockwiseQuarters side degrees` reduces every
turn to 0 to 3 quarter turns clockwise (a left turn goes the rest of the
way round), so the waypoint's rotation is a `match` on four cases:

```stitchwort
def Location.rotated (location: Location) (quarters: Nat): Location :=
  match quarters with
    | 0 => location
    | 1 => { east = location.north, north = 0 - location.east }
    | 2 => { east = 0 - location.east, north = 0 - location.north }
    | _ => { east = 0 - location.north, north = location.east }
```

The program and its 22 tests passed on the first run (one test of mine
expected 782 instructions: the input has no final line break, so `wc -l`
counts one short); `main` takes 0.35 s user on the input.

The spec (`Spec/Spec.sw`) shares the program's data types (`Instruction`,
`Action`, `Heading`, `Location`) and none of its functions. It has
`ActionWritten` and `InstructionWritten` (the letter, then the value in
decimal, and a turn a multiple of 90: the ship only ever faces a compass
point, and every turn in the examples and the input is one), `unit` (a
step of one unit for each heading), `along` (some steps of a step from a
place), `quarterLeft` and `quarterRight` (turning a step about the start:
"east becomes north"), `turned side degrees` (`degrees / 90` quarter
turns that way), `manhattan` ("the sum of the absolute values of its
east/west position and its north/south position"), and for each part its
own ship: `Ship` (a position and the step it faces, `start` facing east),
`navigate` (the instructions as the puzzle words them), `Part1`;
`Steered` (a position and the waypoint), `steer` ("rotate the waypoint
around the ship left (counter-clockwise) the given number of degrees",
"move forward to the waypoint a number of times equal to the given
value"), `Part2`. Where the program faces a compass point the spec faces
a step, and turning is turning that step, so part 1's turns and part 2's
rotations are the same `turned`; the program has a heading in part 1 and
a four-case rotation in part 2. The spec is computable, and the tests run
it on the example (25 and 286).

Proved (`Aoc.Year2020.Day12.Proofs`):

- `readsAction`, `readsInstruction`, `parseWritten` (Parse.sw): if
  `parseRoute` reads `input`, each line is its instruction written out,
  every turn a multiple of 90.
- `iterateCycles`, `iterateMod`, `fullTurnLeft`, `fullTurnRight`,
  `leftIsRight`, `turnedClockwise`, `unitClockwise`, `headingTurned`,
  `rotatedQuarters`, `quartersSmall`, `rotatedTurned` (Turns.sw): a step
  that comes back after `period` steps needs only the remainder; four
  quarter turns either way are the identity; `r` quarter turns left are
  `(4 - r) % 4` right; so the spec's turn is `clockwiseQuarters` quarter
  turns right, turning a heading turns its step, and the program's
  `rotated` is the spec's `turned`.
- `foldLeftRelate`, `alongUnit`, `navigateFollows`, `steerFollows`,
  `part1Rules`, `part2Rules` (Parts.sw): a map that commutes with each
  step commutes with the fold; moving by a heading is moving along its
  unit step; each instruction does to the program's ship (seen as the
  spec's) what the spec says; so both answers are the spec's.
- `part1Correct`, `part2Correct`, `part1Exactly`, `part2Exactly` (both
  `↔`) (Proofs.sw): for every input the parser reads, its lines are the
  instructions written out and the answers are the spec's; each part's
  answer is the spec's and no other number is. Both parts answer on every
  route, so there is no "when it answers" to state. Uniqueness is free:
  `Part1` and `Part2` are equations, so each names one number.

Not proved: that every well-formed input parses (as on days 2 to 11).
Nothing else; there is no added hypothesis. The spec's `turned` reads a
turn as `degrees / 90` quarter turns, which is what the puzzle means for
every turn `InstructionWritten` allows; a turn of 45 degrees is no
instruction (the parser fails on it), and the program and the spec agree
on such a turn anyway (both round it down), so `part1Exactly` holds for
any route, parsed or not.

Breaking the program made the proofs fail: a left turn as many quarters
clockwise as it has degrees fails `turnedClockwise` (E-TYPE-MISMATCH,
`… (degrees / 90 % 4) …` against `… (4 - degrees / 90 % 4) % 4 …`); the
wrong sign in `rotated`'s quarter turn fails `rotatedQuarters`; `West`
turning clockwise to `South` fails `unitClockwise`; moving south adding
to `north` fails `alongUnit`; a waypoint starting 2 north fails
`part2Rules`; and the parser accepting turns of 45 degrees fails
`readsInstruction` (item 2: for an unhelpful reason). The audit (with the
counterexample search): `audited 79 theorems: 0 failed, 0 with warnings,
79 passed`.

### 1. Aoc.Common has nothing for a ship on open water

Every shared type is for a grid read from text: `Position` and `Point`
are `Nat`s from a corner, `Offset` is `Int` rows down and columns right,
and `Direction` is `Up`, `Right`, `Down`, `Left`, with `turnRight` and
`turnLeft`. A ship at sea needs coordinates that go negative, east and
north (the puzzle's words: "10 units east and 1 unit north"), compass
headings, turning a heading or a vector by quarter turns, and the
Manhattan distance; I wrote `Location` (6 functions, 30 lines) and
`Heading` (10 lines), and the spec its own `unit`, `along`,
`quarterLeft`, `quarterRight` and `manhattan`. `Offset` is closest, but
moving north is `rows = -1` in it, and it has no rotation and no length.
2024's day 20 has its own `Position.distance` (Manhattan, by `absDiff`).
A small shared `Vector` (`east`/`north` or `x`/`y` as `Int`s; `plus`,
`times`, `quarterLeft`, `quarterRight`, `rotated quarters`, `manhattan`)
with the lemmas Turns.sw proves (`fullTurnLeft`, `leftIsRight`, rotation
by the remainder) would make this day's program and Turns.sw a few calls,
and would serve 2024's day 14 (robots with velocities, done with
`Offset`). Whether compass headings are `Direction` renamed or a type
of their own is a naming question; `Direction`'s `turnRight` was
exactly `Heading.clockwise`.

### 2. A `match` on a condition the goal no longer has refines nothing, silently

`readsInstruction` follows the parser's `if action.isTurn && value % 90
!= 0` with `match whole: action.isTurn && value % 90 != 0`, which works.
Breaking the parser to `% 45` made the proof fail, as it should, but not
where the cause is:

```
[E-REWRITE-NOTHING] Error: `rewrite` found no `List.append digits []` in the goal
    Note 1: goal after the rule before this one: `?44 [letter] action letter single written digits value nonEmpty allDigits decimal whole`
[E-TYPE-MISMATCH] Error: type mismatch
 26 │         | True => Parse.readsFail "a turn has to be a multiple of 90 degrees" _
    ╰── expected `(state: Parse.State) → … → Std.Effect.runPure (Std.Effect.foldComp … … …) state = Ok (value1, after) → …`, but this has type `Parse.Reads (arg => Parse.fail "…") (?42 …)`
```

The `match` found no `… % 90 != 0` in the goal (it now says `% 45`), so
it refined nothing, the arms' goals stayed the whole `if`, and the
errors are about an unsolved spec (`?42`, `?44`) and the parser's
unfolded run. The real message is one line: "the `match` on `e` refines
nothing: `e` isn't in the goal (nor in a hypothesis)". The same would
have saved time on day 11 (item 4, a `match` on `layout.grid.at next`
that refined nothing). A warning when a `match e:` changes no goal or
hypothesis, at least when an arm then fails, would point at the cause.

### 3. Lemmas a newcomer would look for

- **A fold commutes with a map that commutes with each step.**
  `foldLeftRelate` (`relate (f x i) = g (relate x) i` for all `x`, `i`
  gives `relate (xs.foldLeft x f) = xs.foldLeft (relate x) g`, 4 lines)
  is every "the program's state is the spec's state seen another way"
  proof over a list of steps: both parts here. Std has `List.foldLeftMap`
  (mapping the list) but not this. A std `List.foldLeftRelate` (and a
  `Nat.iterate` one: `headingTurned` is that for `iterate`) would be one
  call each.
- **Iteration with a period.** `iterateCycles` and `iterateMod` (12
  lines): when `f` comes back after `period` steps, `iterate n f =
  iterate (n % period) f`. Std has `Nat.iterateAdd` and
  `Nat.iterateFixed` but not this; any puzzle that turns, cycles or
  wraps by repeated steps needs it.
- **`stitchwort doc` doesn't show a record's generated `ext`.** `doc
  Aoc.Year2020.Day12.Location` lists the fields, and `doc
  …Location.ext` is "no declaration named", though `Location.ext` is
  there and closed every vector identity here (`Location.ext _ _ (omega)
  (omega)`, 10 times). I knew of it from 2024's `Point.ext`; a newcomer
  would only find it in syntax.md. It also takes the two records
  explicitly, which the expected type always fixes, so every call writes
  `_ _` (D2422 would make them implicit).

### 4. `omega` doesn't read a `!=` in a `Bool` hypothesis

The `False` arm of item 2's `match` has `whole: (action.isTurn &&
Decidable.toBool (Decidable.not (Nat.decEq (value % 90) 0))) = False`
and, under a turn, `turn: action.isTurn = True`; the goal is `value % 90
= 0`. `omega` listed neither as a fact. `cases` proved it at once (it
split `value % 90 == 0`'s decision and `isTurn`). Day 9 (item 4) noted
`!=` in statements; here it is `omega` reading `a && b` conjunctions
(day 9 item 1, which it does for `<=`) but not a `!=`'s `Decidable.not`,
as a disequation. Small; `cases` is the workaround, and the error didn't
point at it.

### 5. Smaller things

- **What helped.** The proofs took six minutes: everything but
  `headingTurned` and one `omega` checked as first written. Record `ext`
  with `omega` on each field proved every `Int` vector identity (`0 - (0
  - x) = x` and the like), and a `match` on a `Nat` with arms `0`, `1`,
  `2`, `3` and `Succ (Succ (Succ (Succ more)))` closed by `omega` turned
  "for any `r < 4`" into four computations. `cases` proved the parser's
  turn condition. `Parse.readsPickBy`, `Parse.readsNat` and day 8's
  `parseWritten`, nearly word for word, made the parser's proof a
  minute. Writing both programs as a `foldLeft` of a `follow` method,
  and the spec as a `foldLeft` too, made one generic lemma prove both
  parts.
- **No `Result.getOr`.** A test that wanted the parsed instructions or
  `[]` wrote `.toOption |> .getOrElse []`; with day 11's missing
  `Result.isErr`, `Result` lacks the `Option`-like accessors a test
  reaches for. And `Option`'s is `getOrElse`, so `getOr` (the name
  `Map.getOr` and the index lemmas use) isn't there for either.
  (Correction, SW-1488: `Result.getOrElse` does exist, so the test
  could have written `.getOrElse []` directly; what remains is the
  naming split, `getOrElse` on `Option`/`Result` and `getOr` on `Map`.)
- **The puzzle doesn't say turns are quarter turns.** The program and
  the spec both need a reading of "turn left the given number of
  degrees" for a ship that faces N, S, E or W; Matt's Scala rounds
  `cos` and `sin`. Rejecting other turns in the parser and saying so in
  `InstructionWritten` kept the spec in the puzzle's words with no
  hypothesis on the theorems; a newcomer might instead model angles mod
  360 and pay for it in `%` arithmetic, which `omega` can't do (guide
  §3).

### Size and time

139 lines of program, 115 of spec, 198 of proofs (Parse 39, Turns 81,
Parts 51, Proofs 27), 65 of tests (+1 answer test in
`aoc_answers.rs`). By the clock: 23:37 start; program and tests passing
at 23:42; spec and all proofs at 23:46 (a minute on the parse
condition, item 4); then the break checks, the audit, timing and these
notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day12.Proofs` | 4.8 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day12` | 1.4 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day12` (22 tests) | 4.8 s user |
| `task audit:touched -- Aoc.Year2020.Day12` (79 theorems) | about 11 s user |
| `stitchwort run Aoc.Year2020.Day12.main` on the input | 0.35 s user |
| `task test:one -- year2020_day12` | 1.5 s for the test (2 min with building the test binaries in a new worktree) |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 86 ms of
elaboration and 12 ms in the kernel (`readsInstruction` the largest, 48
ms); the rest of the cold time is std's modules.

### Ranked

1. Aoc.Common has no `Int` vector with compass headings, quarter-turn
   rotation and Manhattan length, nor the lemmas that four quarter turns
   are none and a left turn is three right; this day wrote 40 lines of
   program and 80 of proof for them (item 1). Aoc.Common; small.
2. A `match e:` whose `e` isn't in the goal refines nothing without a
   word, and the arms then fail with messages about unsolved
   metavariables and unfolded parser runs (item 2). Message; small.
3. Std lacks `List.foldLeftRelate` (a fold commutes with a map that
   commutes with each step) and `Nat.iterateMod` (iteration with a
   period); both are generic and were half of the proofs (item 3).
   Library; trivial each.
4. `stitchwort doc` doesn't list or find a record's generated `T.ext`,
   and `T.ext` takes its two records explicitly (item 3). Tooling and
   D2422; trivial each.
5. Smaller: `omega` doesn't read a `!=` (`Decidable.not`) in a `Bool`
   hypothesis (item 4); no `Result.getOr` (item 5). Each small.

## Day 13: Shuttle Search

Your notes on the shuttle buses: the earliest time you could leave, then
the schedule, bus IDs and `x`s for buses out of service. A bus departs at
every multiple of its ID. Part 1: the earliest bus you can take, its ID
times the minutes you wait. Part 2: the earliest time `t` at which the
first listed bus departs and each later one departs as many minutes after
`t` as it is further down the list. Answers on Matt's input (9 buses in
service, all primes, the largest 977): 2165 and 534035653563227; the
example gives 295 and 1068781, and the five further schedules 3417,
754018, 779210, 1261476 and 1202161486, as the puzzle says. Matt's Scala
(`Day13.scala`) walks the clock minute by minute for part 1 and solves
part 2 by the Chinese remainder theorem with the extended Euclidean
algorithm, asserting the IDs are coprime; I didn't run it. An independent
Python script (the usual sieve, stepping by the product of the IDs so far)
agrees on all seven answers.

The domain types are `Slot` (`Listed id` or `OutOfService`), `Notes` (the
earliest time and the schedule), `Bus` (an ID and its offset down the
schedule, `notes.buses`) with `bus.nextDeparture from` and
`bus.departsAfter time`, and `Alignment` (a time and a period: the times
that suit the buses so far are that time and every period after it). Part
1 is `notes.earliestBus`: the smallest next departure (`minimumOf`), the
first bus that leaves then, its ID times the wait. Part 2 is
`notes.earliestLineUp`, a sieve, one bus at a time. The design decision is
the period. The textbook sieve multiplies it by each bus's ID, which is
right only when the IDs are pairwise coprime; this one measures it: after
finding the first suitable time for the new bus, it looks for the next,
and the distance between them is the new period (which is the lcm of the
IDs so far). Both searches look at most `id` periods ahead, since suiting
a bus with ID `id` comes round every `id` periods, so there is no
unbounded loop and no fuel:

```stitchwort
def Alignment.add (alignment: Alignment) (bus: Bus): Option Alignment :=
  let suits := (periods: Nat) => bus.departsAfter (alignment.time + periods * alignment.period)
  0 ..< bus.id |> .find suits |> .map (first =>
    let again := 0 ..< bus.id |> .find (more => suits (first + 1 + more)) |> .getOrElse 0
    { time = alignment.time + first * alignment.period, period = (again + 1) * alignment.period })
```

The program and its 23 tests passed on the first run once two test
expectations of mine were corrected (`4,6` can never line up, `4,x,6`
lines up at 4; I had them swapped); `main` takes 0.32 s user on the input.
The test `4,x,6,x,5` (answer 16) is the one that tells the two sieves
apart: stepping by the product of the IDs gives 76, skipping 16 because
4 and 6 share a factor. Every example and the input pass either way (and
Matt's Scala would stop on its coprimality assertion).

The spec (`Spec/Spec.sw`) shares the program's `Notes` and `Slot` and
none of its functions. It has `SlotWritten` and `NotesWritten` (the
timestamp in decimal, a line break, the entries separated by commas; an
ID is decimal and at least 1, since it is how often the bus leaves),
`Departs id time` ("the bus with ID 5 departs from the sea port at
timestamps 0, 5, 10, 15": `time` is some number of trips times `id`),
`Part1` (a listed bus departing at or after the earliest time, with no
listed bus departing at or after it any earlier, and the answer its ID
times the wait), `LinedUp schedule t` (walking the schedule: a listed bus
departs at `t`, then the rest line up from `t + 1`; "an x in the schedule
means there are no constraints") and `Part2` (lined up, and no earlier
time is). The spec isn't computable (`Departs` is an `∃`, `Part2` a
`∀`), so the tests don't run it.

Proved (`Aoc.Year2020.Day13.Proofs`):

- `readsSlot`, `readsNotes`, `parseWritten` (Parse.sw): if `parseNotes`
  reads `input`, the input is the notes written out, then any line
  breaks; `writtenPositive`: so every ID read is at least 1.
- `Describes`, `startDescribes`, `describesEarliest`, `suitsRound`,
  `periodDivides`, `suitsMultiple`, `stepDescribes`, `addDescribes`,
  `addNone`, `addAllDescribes`, `addAllNone` (Sieve.sw): an alignment
  describes a set of times when they are exactly its time plus whole
  periods; with no buses, the start does; suiting a bus comes round every
  `id` periods; once `p` and `p + d` periods both suit a bus, `d` periods
  are a multiple of its ID, and adding a multiple of `d` changes nothing;
  so adding a bus gives an alignment describing the times that also suit
  that bus, or none when no time does. Every bus's ID is positive: that is
  the only hypothesis.
- `departsAfterSpec`, `linedUpFrom`, `busesLinedUp`, `part2Rules`,
  `part2Never` (Part2.sw): the program's buses all depart at their
  offsets after `t` exactly when the schedule lines up at `t`; so the
  sieve's time is the spec's answer, and when it finds none, no time
  lines up.
- `memBusesFrom`, `busesFromHas`, `nextDepartureFirst`, `part1Rules`,
  `part1Answers` (Part1.sw): a bus's next departure is the first time at
  or after yours that it departs; the program's answer is the spec's; and
  it answers whenever a bus is in service.
- `part1Correct`, `part1AnswersIff`, `part2Correct`, `part2Exactly` (↔),
  `part2NoneIff` (↔) (Proofs.sw): for every input the parser reads, the
  input is the notes written out; part 1's answer is the spec's, and there
  is one exactly when some bus is in service; part 2's answer is the
  spec's earliest time and no other number is; and part 2 has no answer
  exactly when no time lines up.

Not proved: that every well-formed input parses (as on days 2 to 12). The
theorems about `Notes` take `IdsPositive notes` (every listed ID is at
least 1), which the parser establishes (`parsedPositive`), so the
theorems about the input have no added hypothesis. Part 1 has no `↔`: if
two buses first left at the same minute the puzzle wouldn't say which to
take, and `Part1` names either's answer; the program takes the first
listed. No coprimality is assumed anywhere.

Breaking the program made the proofs fail: a period of `(again + 2)`
periods, or a first time one period late, fails `addDescribes` (at its
call of `stepDescribes`); searching only `0 ..< bus.id - 1` fails
`addDescribes` and `addNone`; the next departure computed from `from + 1`
fails `nextDepartureIs`; an offset one too many in `departsAfter` fails
`departsAfterSpec` and `suitsMod`; and the textbook period, `bus.id *
alignment.period`, fails `addDescribes` (and two tests). The audit (with
the counterexample search): `audited 60 theorems: 0 failed, 0 with
warnings, 60 passed`.

### 1. No lcm, no coprimality, no simultaneous congruences in std

Part 2 is the Chinese remainder theorem, and a newcomer will reach for it
or for the sieve that steps by the product of the IDs. Std has
`Nat.gcd`, `Nat.gcdDivides` and `Nat.gcdBezout` (over `Int`; from 2024's
day 8), and nothing after them: no `Nat.lcm`, no "a common multiple of
`a` and `b` is a multiple of their lcm", no `Coprime`, no Euclid's lemma
(`a` coprime to `b` and dividing `b * c` divides `c`), no
`Nat.extendedGcd`, no congruence solver. Proving the textbook sieve
"earliest" needs exactly those: that stepping by the product (or the lcm)
skips no solution is the lcm's universal property, from Bézout over
`Int` and back to `Nat`. I measured the period instead, which turns the
proof into remainder arithmetic (Sieve.sw, 197 lines, 15 minutes); a
newcomer who wrote the textbook sieve would have had to stop at
soundness, or prove Euclid's lemma first. What would have made the step
a call: std `Nat.lcm` with `Nat.lcmDivides` (`a ∣ x → b ∣ x → lcm a b ∣
x`) and `Nat.coprimeMulDivides`, and a `Nat.solveCongruences: List (Nat,
Nat) → Option (Nat, Nat)` (each a remainder and a modulus; the earliest
solution and the period, or none) with this day's `Describes` as its
spec. 2016's day 15 is the same problem and 2023's day 8 needs an lcm;
2024's day 14 took `width * height` as its period, which is the lcm
only because its sides are coprime (NOTES-2024 day 14).

### 2. Divisibility is a `Bool`, and its lemmas are about `%`

The program says "departs" as `Nat.divides bus.id (time + bus.offset)`
(total: no `id ≠ 0` to supply), the spec as `∃ trips, time = trips * id`,
and the proofs work with `% id = 0` (whose lemmas need `[auto ok: id ≠
0]`). I wrote `dividesMod` (`Nat.divides m n = (n % m == 0)` for `m ≠
0`), `addMultiple` (`z % m = 0 → (x + z) % m = x % m`), `multipleMod`
(`z % m = 0 → q * z % m = 0`) and `departsAfterSpec` (`Nat.divides`
against the `∃`, through `Nat.dividesElim`'s continuation and
`Nat.dividesMul`). Each is three lines and generic. Std has
`Nat.modAddMul`, `Nat.addModMod` and `Nat.mulModMod` to build them from,
but no `Nat.dividesIff` (`Nat.divides d n = True ↔ ∃ t, n = t * d`), no
`Nat.dividesAdd`, `Nat.dividesMulLeft` or `Nat.dividesSub`, and no
divisibility proposition with `∣` notation, so a statement about
divisibility chooses between a `Bool`, an `∃` and a remainder each time.

### 3. No `List.minBy` lemmas

Part 1 wants `notes.buses.minBy departure`. Std has `List.minBy` and no
theorem about it (2024's day 21 proved its own `minByStepPasses`), so I
wrote `minimumOf` (the smallest departure) and then `find` (the first bus
leaving then): two passes, but `List.minimumSome` (member, and below
every member) and `List.findSome` made the proof direct. A
`List.minBySome` (the result is a member and its key is at most every
member's; the first such on a tie) would let the program say what it
means.

### 4. Messages

- **`ring [split * alignment.period]`** is `E-RING` "`ring` takes
  equations between `Nat`s, and this is `Nat`", underlining
  `alignment.period`: contradictory as worded. Note 2, "a coefficient goes
  before its hypothesis: `c * h`", is the fix (`ring [alignment.period *
  split]`); it should be the message.
- **A parameter that hides a function.** In `parseWritten (input: Text)
  (notes: Notes)`, `Parse.allReads input notes …` meant the parser
  function `notes` and got the parameter: "expected `() → {Parse} ?0
  input notes parsed`, but this has type `Notes`". A note "`notes` here is
  the parameter; the function is `Aoc.Year2020.Day13.notes`" would say
  why.
- **`stitchwort doc` and a definition's `if h:` equations.** `doc
  Bus.nextDeparture` lists `nextDeparture.eq.ifTrue` as `nextDeparture bus
  from = Nat.ceilDiv from bus.id * bus.id`, without its premise `bus.id ≠
  0` (it shows `ifFalse`'s), and `doc …nextDeparture.eq.ifTrue` is "no
  declaration named". I found the premise by calling it with one. (Day
  12 noted the same for a record's `ext`.)
- **What helped.** `E-REWRITE-NOTHING`'s "inside the `match`, … `added`
  is already refined: use it as it is" (three times, each exactly right);
  `E-ARITY`'s note that `id ≠ 0` "unfolds to a function type … and so it
  adds 1 argument(s) to match"; `E-REWRITE-TARGET` saying to name the
  term with `let`.

### 5. Smaller things

- **What helped.** The proofs took 15 minutes, nearly all of it Sieve.sw.
  `List.findRangeSome` and `List.findRangeNone` (what `find` over `0 ..<
  n` finds is the least that passes; finding nothing means none in range
  does) made both searches one call each, so bounded searches in the
  program cost nothing in the proofs. `ring [tIs, alignment.period *
  jIs]` closed the one non-linear step, and `omega [split]` with
  `Nat.divModEq` split `j - first` into whole periods and a remainder. A
  `match r with | Zero | Succ s` on a `let`-bound remainder refined the
  hypotheses that mentioned it. `Nat.ceilDivLe` and `Nat.leCeilDivMul`
  were the whole of part 1's "next departure". Parse.sw followed day 12's
  shape and checked on the first try.
- **`Some { … }`, again, four times.** `Some { id, offset }` in the
  program, `Ok { … }` and `Some { … }` in tests, `Witness { … } …` in a
  proof: each `E-UNKNOWN-FIELD` or `E-PARSE` with a note saying to bracket
  it. Days 5 and 8 reported it; it costs a round trip each time, and the
  bracketed reading is the only one that typechecks.
- **Arithmetic in `rewrite` depends on what computes.** `rewrite (omega:
  p + 1 + (bus.id - 1) = p + 1 * bus.id) in …` found no `Succ (p +
  (bus.id - 1))` in a goal that printed `p + (bus.id - 1) + 1`, and
  `rewrite (omega: first + (again + 1) = first + 1 + again)` was "the goal
  already computed past it". `Eq.cong (n => suits alignment bus n)
  (omega: …)` did it. Which side of a `+ 1` computes is guesswork until
  the message says.
- **The ID has to be positive in three places.** The program needs `if
  positive: bus.id ≠ 0` only to supply `Nat.ceilDiv`'s `auto` argument;
  the proofs thread `IdsPositive` from the parser. I didn't try a proof
  field in `Bus` (`positive: id ≠ 0`), which would carry it.

### Size and time

97 lines of program, 66 of spec, 469 of proofs (Parse 55, Sieve 197,
Part2 60, Part1 89, Proofs 68), 65 of tests (+1 answer test in
`aoc_answers.rs`). By the clock: 00:28 start; program and tests passing at
00:36; the sieve proved at 00:47, everything at 00:51; then the break
checks, the audit, timing and these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day13.Proofs` | 4.9 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day13` | 1.4 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day13.Tests` (23 tests) | 1.4 s user |
| `task audit:touched -- Aoc.Year2020.Day13` (60 theorems) | 3.1 s user |
| `stitchwort run Aoc.Year2020.Day13.main` on the input | 0.32 s user |
| `task test:one -- year2020_day13` | 3.2 s for the test |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 281 ms of elaboration
and 33 ms in the kernel (`readsNotes`, `stepDescribes` and `readsSlot` the
largest, about 60 ms each); the rest of the cold time is std's modules.

### Ranked

1. Std has `gcd` and Bézout but no `lcm`, coprimality, Euclid's lemma or
   congruence solver, so the textbook sieve's "earliest" was out of reach
   without proving them first; measuring the period avoided it (item 1).
   Library; medium (a `Nat.solveCongruences` with this day's proof,
   small).
2. No `Nat.dividesIff` or divisibility lemmas (`dividesAdd`,
   `dividesMul`), and no `∣` proposition; every day with divisibility
   writes the bridge between `Nat.divides`, `∃` and `%` (item 2).
   Library; small.
3. No `List.minBy` lemmas (item 3). Library; small.
4. `ring`'s message for a coefficient after its hypothesis reads as a
   contradiction (item 4). Message; trivial.
5. `stitchwort doc` shows `eq.ifTrue` without its premise and can't look
   it up (item 4); a parameter hiding a function gets no note (item 4);
   `Some { … }` again (item 5). Each small.

## Day 14: Docking Data

The ferry's initialization program, one instruction a line: `mask =`
and 36 characters of `0`, `1` and `X` (the most significant bit first),
or `mem[8] = 11`, a write of 11 to address 8. Memory holds 36-bit numbers
and starts as all 0s. Part 1: the mask's 0s and 1s overwrite the value's
bits, its Xs keep them. Part 2: the mask changes the address instead (0
keeps the bit, 1 sets it, X is floating: both values), and the value goes
to every address that results. Each answer is the sum of the values left
in memory. Answers on Matt's input (572 instructions, 100 masks with 4 to
9 Xs, 472 writes): 13496669152158 and 3278997609887; the examples give
165 (part 1) and 208 (part 2, the second example), as the puzzle says,
and the second example gives 51 for part 1. Matt's Scala (`Day14.scala`)
masks with `&` and `|` on `Long`s and expands the floating bits with
`floaters.subsets()`; I didn't run it. An independent Python script
(the same masks on `int`s, `itertools.product` over the floating bits)
agrees on all four answers.

The domain types are `MaskBit` (`Off`, `On`, `X`, with `symbol`,
`isOn` and `isFloating`), `Mask` (its bits, with `width`, `ones`,
`floating`, `applyTo value` and `decode address`), `Instruction`
(`SetMask mask` or `Write address value`), `Program` (the instructions)
and `Computer` (the mask last set and memory, a `Map Nat Nat`, with
`setMask`, `writeValue`, `writeDecoded`, `run` and `memorySum`); the
answers are `program.valueSum` and `program.decodedSum`, a `foldLeft` of
`run` with each part's write. Part 1 is the textbook `(value & floating)
| ones`, with std's `Nat.and` and `Nat.or`. Part 2 expands the floating
bits on the address's bit list, `Nat.toBits` of it beside the mask's
bits: an X doubles the list, so a write makes `2 ^ k` addresses for `k`
Xs. The input's masks have at most 9, so part 2 makes 83,520 writes
(80,123 addresses end up written), and `main` takes 1.7 s user. The
parser rejects a program whose first line isn't a mask, so the initial
mask (empty) never applies.

The program and its 18 tests passed on the first run, after one
`E-UNKNOWN-FIELD` for `SetMask { bits = … }` (item 6). The part 1
example can't be run through part 2: its mask has 34 Xs, so its first
write is to 2 ^ 34 addresses (my first cross-check script hung on it;
the puzzle gives no part 2 answer for it, and the tests don't ask).

The spec (`Spec/Spec.sw`) shares the program's data types (`MaskBit`,
`Mask`, `Instruction`, `Program`) and none of its functions. It has
`MaskBitWritten`, `DecimalWritten`, `InstructionWritten` ("mask = ",
then 36 mask characters; "mem[", the address in decimal, "] = ", the
value in decimal) and `ProgramWritten` (one instruction a line, the
first setting the mask); `Memory`, a function from address to value,
`empty` ("the entire 36-bit address space begins initialized to the
value 0"), and `SumOfMemory memory answer` ("the sum of all values left
in memory": the sum over some list of distinct addresses that includes
every address not holding 0); `Machine`, `step` and `run`, the program
read with a part's write (last write wins, since each write replaces
the function at what it writes); part 1's `overwrite` ("a 0 or 1
overwrites the corresponding bit in the value, while an X leaves the
bit in the value unchanged") and `masked` (the value's `Nat.toBits`
beside the mask, overwritten, read back with `Nat.fromBits`), and
`writeMasked`; part 2's `bitFits` and `allFit` (the puzzle's three rules
for an address bit, a floating bit fitting either), `Decodes mask
address target` (`target` is an address of the mask's width all of whose
bits fit) and `writeDecoded` (every target it decodes to holds the
value); `Part1` and `Part2`. Bits are lists of `Bool`s throughout, as
std's `Nat.toBits` writes them; the width is the mask's, which
`ProgramWritten` makes 36. The spec's memory is a function and its sum
an `∃`, so the tests don't run it.

Proved (`Aoc.Year2020.Day14.Proofs`):

- `readsMaskBit`, `readsInstruction`, `startsWritten`, `parseWritten`
  (Parse.sw): if `parseProgram` reads `input`, each line is its
  instruction written out, and the first sets the mask.
- `zipWithSnoc`, `lastBitAnd`, `lastBitOr`, `toBitsAnd`, `toBitsOr`,
  `lowBitAnd`, `andLe`, `orBelow`, `maskedBits`, `applyToMasked`
  (Bits.sw): the bits of `Nat.and m n` and `Nat.or m n` are the two
  numbers' bits zipped with `&&` and `||`; `Nat.and m n ≤ n`, and an
  `or` of numbers below `2 ^ k` is below it; so `mask.applyTo value` is
  `Spec.masked mask value` for every mask and value.
- `decodedFit`, `fitDecoded`, `decodeSound`, `decodeComplete`,
  `decodeContains` (Decode.sw): a list of bits is in `decodeBits` exactly
  when it has the mask's length and fits; so `target ∈ mask.decode
  address` exactly when `Spec.Decodes mask address target`.
- `getOrInsert`, `getOrInsertAll`, `entryValue`, `sumOfMap` (Memory.sw):
  reading the map after inserts, and that a function the map describes
  has the sum of the map's values as its `SumOfMemory`.
- `memOfRemoveFirst`, `memRemoveFirst`, `distinctRemoveFirst`,
  `sumsAgree`, `sumOfMemoryUnique` (Sum.sw): two lists of distinct
  addresses with the same addresses not holding 0 sum to the same, so
  `SumOfMemory` names one number.
- `Agrees`, `startAgrees`, `WritesAgree`, `stepAgrees`, `foldAgrees`,
  `writeValueAgrees`, `writeDecodedAgrees`, `part1Rules`, `part2Rules`
  (Parts.sw): the computer and the spec's machine agree (same mask; the
  map read with 0 for a missing address is the spec's memory) after each
  instruction, so each part's answer is its spec's sum.
- `part1Correct`, `part2Correct`, `part1Exactly`, `part2Exactly` (both
  `↔`) (Proofs.sw): for every input the parser reads, its lines are the
  program written out and each answer is the spec's; each answer is the
  spec's sum and no other number is. The `↔`s hold for every program,
  parsed or not.

Not proved: that every well-formed input parses (as on days 2 to 13).
Nothing else; there is no added hypothesis. The spec takes the width
from the mask, so the theorems hold for masks of any width, and values
and addresses wider than the mask are cut to it, as a 36-bit memory
would; every value and address in the input is below 2 ^ 36 (the
largest value is 1062419043). Part 1 writes to the address as given, so
an address of 2 ^ 36 or more would be its own cell there and not in part
2; the puzzle's addresses are 36-bit and the input's below 65536.

Breaking the program made the proofs fail: `ones` replaced by `floating`
in `applyTo` fails `applyToMasked`; an `Off` bit decoded as 1 fails
`decodedFit` and `fitDecoded`; an X decoded only as 0 fails `decodedFit`
and `fitDecoded`; part 1 writing the value unmasked fails
`writeValueAgrees`; and a sum one too big fails `part1Rules` and `part2Rules`. The parser reading 35 mask characters instead of 36 is item 4: the check ran for over five minutes without an answer, and I stopped it. The
audit (with the counterexample search): `audited 76 theorems: 0 failed,
0 with warnings, 76 passed`.

### 1. Std's bits are close; the bridge from `and`/`or` to `toBits` is missing

Std has more than I expected: `Nat.and`, `Nat.or`, `Nat.xor` and
`Nat.testBit` with `testBitAnd`/`testBitOr`, `Nat.fromBits` and
`Nat.toBits` with both round trips (`fromBitsToBits`, `toBitsFromBits`)
and `fromBitsBelow`. That made a bit-list spec the natural one and the
`and`/`or` program provable. Two halves don't meet, though: the
`testBit` lemmas speak of bit `i` of a number, the `toBits` lemmas of a
list, and nothing links them (no `testBit (fromBits bits) i`, no
`toBits` of an `and`). I wrote `toBitsAnd` and `toBitsOr` (the bits of
`Nat.and m n` are the bits of `m` and `n` zipped with `&&`; 7 lines
each, with `lastBitAnd` and `zipWithSnoc`), and the bounds `andLe`
(`Nat.and m n ≤ n`) and `orBelow` (an `or` of two numbers below `2 ^ k`
is below it); std has `xorBelow` but neither of these. Std also has no
complement or "clear these bits" (`Nat.not` within a width, or
`Nat.andNot`), which is what part 2's "X clears, then set" looks like
in the textbook solution, and no `Nat.setBit`/`clearBit`. Each of
`Nat.toBitsAnd`, `Nat.toBitsOr`, `Nat.toBitsXor`, `Nat.andLe` and
`Nat.orBelow` is generic and small; with them, Bits.sw would be
`maskedBits` and the 9-line `applyToMasked`.

### 2. "The sum of all values in memory" over a 2 ^ 36 address space

The puzzle's answer is a sum over every address, and the spec's memory
is a function, so the honest spec is a sum over its support: some list
of distinct addresses containing every address not holding 0
(`SumOfMemory`). That needs two things std doesn't have. The program's
side: `Map.values.sum` as a sum over `Map.keys` of `getOr` (I wrote
`entryValue` and `sumOfMap`, 25 lines, from `Map.memToList`,
`Map.keysDistinct` and `List.foldLeftMap`), and reading `getOr` after
`insert` (`getOrInsert`, `getOrInsertAll`: std has `Map.getInsert` and
`getInsertOther` on `get`, and `getOrFoldCount` for counting, but no
`getOr` form with an `if`). The spec's side: that the sum doesn't
depend on the list (`sumsAgree`, 45 lines, with `memOfRemoveFirst`,
`memRemoveFirst` and `distinctRemoveFirst`, which std lacks for
`removeFirst`; std has `sumByPerm` but no "distinct lists with the same
members are permutations"). A std `List.sumByDistinctSupport` (two
distinct lists that hold the same `x` with `f x ≠ 0` have the same
`sumBy f`) and `Map.sumValues` (`m.values.sum = m.keys.sumBy (k =>
m.getOr k 0)`) would make Memory.sw and Sum.sw two calls; any puzzle
whose answer sums a sparse grid or memory needs them.

### 3. No `zipWith` lemmas

`List.zipWith` has nothing proved about it beyond `zipWith3`'s and
`zipWith4`'s nil cases: no length, no append (`zipWithSnoc`, which I
wrote), no `map`, no membership. `Nat.toBits` builds its list from the
end, so every bit-by-bit fact goes through a snoc lemma.

### 4. A wrong literal in a parser makes the proof check run for minutes

Breaking the parser to read `Parse.exactly 35 maskBit` left
`readsInstruction` saying `Parse.readsExactly 36 maskBit …`. Checking
it ran at full CPU for over five minutes with no output, and I stopped
it. With the proof's hole in place of the length (`?`) it still didn't
finish in 90 s; with the proof saying 35 too, the real error
(`List.length bits = 36` against `= 35`) came in 0.7 s. So the time
goes on comparing `Parse.exactly 35 maskBit` with `Parse.exactly 36
maskBit`, which the checker apparently unfolds through the parser's
handler instead of comparing the two literals. A newcomer who changes
a number in a parser and not in its proof gets a hang, not an error;
a step limit with a message naming the two terms would say where.

### 5. A `rewrite` changed what the next one looked for, out of sight

In `toBitsAnd` the goal's last bit is `Nat.and m n % 2 == 1` and its
other bits are about `Nat.and m n / 2`. Rewriting with `Nat.andDiv`
first, then with the last-bit lemma, failed: "`rewrite` found no
`Nat.and m n % 2`", the goal shown with that bit elided as
`[Std.Decidable.toBool …]`. Rewriting the last bit first worked. The
`% 2` apparently computes to something containing the `/ 2`, which the
first rule then rewrote. The message's Note 1 ("goal after the 2 rules
before this one") was the right hint, but the elided `…` hid the place;
showing the subterm where the left side was expected would have said
it at once.

### 6. Smaller things

- **What helped.** The proofs took about 15 minutes, and nearly every
  lemma checked as first written. `Parse.readsExactly` made "36 mask
  characters" one call; `readsPickBy` with a `symbol` method, as on
  day 12, made each mask character one; `List.memMapElim`,
  `memAppend`, `memMap`, `memAppendLeft`/`Right` were all the decoder's
  proof needed; `cases` closed `maskedBits`' four-way Bool case and
  `getOrInsertAll`'s `if`s; `Map.keysDistinct` and `Map.memKeys` gave
  the program's addresses for `SumOfMemory` directly. Writing the
  spec's machine as a top-level `step` (not a `let` inside `run`) let
  one generic `foldAgrees` prove both parts.
- **`SetMask { bits = … }`, again.** `E-UNKNOWN-FIELD` with the note to
  write `SetMask ({ … })`: days 5, 8 and 13 reported it.
- **`rewrite … at <term>`** isn't allowed with `in`, and `E-REWRITE-TARGET`
  said exactly what to do ("drop `in …` to use the rewritten term
  directly"); without `in`, it is a neat way to restate a lemma.
- **The part 1 example is a trap for part 2.** Its 34 Xs mean `2 ^ 34`
  writes; a test that runs both parts on every example hangs. Nothing
  for Stitchwort to fix, but `stitchwort test` has no option for a
  per-test time limit (`--help` lists none) to turn the hang into a
  failure; I saw the problem in my Python first.

### Size and time

138 lines of program, 124 of spec, 457 of proofs (Parse 51, Bits 85,
Decode 95, Memory 45, Sum 89, Parts 61, Proofs 31), 66 of tests (+1
answer test in `aoc_answers.rs`). By the clock: 01:02 start; program and
tests passing at 01:12; the bit lemmas at 01:17, the decoder at 01:19,
memory and both parts at 01:21, the parser at 01:23, uniqueness and the
top-level theorems at 01:25; then the break checks (item 4 took most of
that), the audit, timing and these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day14.Proofs` | 6.5 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day14` | 2.6 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day14.Tests` (18 tests) | 3.8 s user |
| `stitchwort audit Aoc.Year2020.Day14` (76 theorems) | 6.3 s user |
| `stitchwort run Aoc.Year2020.Day14.main` on the input | 1.8 s user |
| `task test:one -- year2020_day14` | 9.2 s for the test (2 min 10 s with building the test binaries) |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 305 ms of
elaboration and 33 ms in the kernel (`readsInstruction` 203 ms of it,
2.4 million steps); the rest of the cold time is std's modules.

### Ranked

1. Checking a parser proof against a parser that differs in one literal
   (`exactly 35` against `exactly 36`) runs for minutes with no output
   instead of a type error (item 4). Checker; medium (find where the
   comparison unfolds the parser, and bound or short-cut it).
2. Std has no lemmas from `Nat.and`/`Nat.or` to `Nat.toBits`
   (`toBitsAnd`, `toBitsOr`), no `Nat.andLe`/`Nat.orBelow` bounds, no
   complement or `andNot`, and no `zipWith` lemmas (items 1, 3).
   Library; small.
3. A sum over a sparse memory: no `Map.sumValues` (values as a `sumBy`
   over keys), no `getOr` after `insert` with an `if`, no `removeFirst`
   membership lemmas, and no "distinct lists with the same nonzero
   members have the same `sumBy`"; 70 lines here (item 2). Library;
   small.
4. A `rewrite` that changes the subterm the next rule looks for shows
   the goal with that subterm elided (item 5). Message; small.
5. Smaller: `SetMask { … }` again; no per-test time limit in
   `stitchwort test` (item 6). Each small.

## Day 15: Rambunctious Recitation

The elves' memory game. The input is one line of starting numbers
separated by commas, read out one a turn; after them, each turn
considers the number spoken last: if that was its first time, the
player says 0, else how many turns apart it is from when it was spoken
before. Part 1: the 2020th number spoken; part 2: the 30,000,000th.
Answers on Matt's input (`15,12,0,14,3,1`): 249 and 41687; the example
`0,3,6` gives 436, and the six further starting lists give 1, 10, 27,
78, 438 and 1836, as the puzzle says. Matt's Scala (`Day15.scala`)
keeps an immutable `Map` from number to the turn it was last spoken,
as this program does; I didn't run it. An independent Python script
(a `dict`, the same loop) agrees on both answers and the example's part
1, in 7.2 s for part 2. Part 2 speaks 3,611,894 distinct numbers, the
largest 29,469,422.

The domain types are `Starting` (the starting numbers, a
`NonEmptyList Nat`, since the parser reads them with `sepBy1`) and
`Game` (the turn just taken, the number spoken on it, and `lastSeen`, a
`Map Nat Nat` from every number spoken before that turn to the latest
turn it was spoken), with `Game.begin first`, `game.say number`,
`game.reply` (0, or the turn minus the map's entry for the last
number), `starting.next game` (the next starting number while there is
one, else the reply), `starting.takeTurn game` (`game.say (starting.next
game)`) and `starting.numberSpoken turn`, `Nat.iterate` of `takeTurn`
from the first turn. Both parts are `numberSpoken` at their turn. The
program and its 12 tests passed on the first run.

The spec (`Spec/Spec.sw`) shares `Starting` and nothing else.
`NumberWritten` and `StartingWritten` (the numbers in decimal, separated
by commas); `turnsBack number older`, how many turns back `number` was
last spoken, looking over the numbers spoken before the latest, the most
recent first; `reply` ("If that was the first time the number has been
spoken, the current player says 0. Otherwise, … how many turns apart
the number is from when it was previously spoken"), `spoken starting
turns`, the numbers spoken in the first `turns` turns, the most recent
first (a starting number while there is one, then the `reply` to
everything before), `numberSpoken` (the head of that) and `Answer
starting turn answer`. The spec looks back over the whole game every
turn, so it is quadratic; the tests run it to turn 2020 on the example
and check it against the program for the first 300 turns of the input.

Proved (`Aoc.Year2020.Day15.Proofs`):

- `readsStarting`, `parseWritten` (Parse.sw): if `parseStarting` reads
  `input`, the input is the starting numbers written out, then any line
  breaks.
- `Tracks`, `turnsBackAtMost`, `beginTracks`, `mapShift`, `sayTracks`,
  `replyTracks` (Game.sw): the invariant is that a game tracks the spec's
  list of numbers spoken when its last number is the list's head, its
  turn is the list's length, and for every number its map holds what
  `turnsBack` gives over the rest of the list, as a turn (`game.turn -
  back`). `say` keeps it; under it, `game.reply` is `Spec.reply`.
- `Playing`, `beginPlaying`, `nextAgrees`, `takeTurnPlaying`,
  `lastTracks`, `iterateTurn`, `numberSpokenSpec` (Turns.sw): every
  turn the program takes is the spec's next turn, so for every starting
  list and every turn, `starting.numberSpoken turn = Spec.numberSpoken
  starting.numbers.toList turn`.
- `correct` (Proofs.sw): for every input the parser reads and every
  turn, the input is the starting numbers written out and
  `starting.numberSpoken turn` is the spec's `Answer` for that turn.
  Part 1 is turn 2020 and part 2 turn 30000000; the theorem isn't stated
  for those two turns (item 2).

Not proved: that every well-formed input parses (as on days 2 to 14);
that `main` asks for turns 2020 and 30000000 (it reads so). There is no
added hypothesis and no `opaque`.

Breaking the program made the proofs fail: the reply one too big fails
`replyTracks` (`omega`, with a model); the map recording the turn after
the one it should fails `sayTracks`; `<=` for `<` in `next` (a starting
number too many) fails `nextAgrees`; a new number answered with 1
instead of 0 fails `replyTracks`. The audit (with the counterexample
search): `audited 32 theorems: 0 failed, 0 with warnings, 32 passed`.

### 1. Slow: part 2 is 30,000,000 turns of a `Map` walk, about six minutes

`stitchwort run` takes 357 s of CPU for both parts (part 1 is 2020 turns
and takes no time), so `aoc_answers.rs` has the day's test `#[ignore]`d
(run it with `--ignored`) and leaves it out of its run over every day,
and the Stitchwort tests check part 1 on the input and part 2 not at
all. On each runtime, for the whole program:

| runtime | time (user) | per million turns | peak memory |
| --- | --- | --- | --- |
| `stitchwort run` | 357 s | 11.9 s (8.4 s for the first million) | 688 MB |
| `run --js` | 127 s (145 s real) | 4.2 s | 2.2 GB |
| `run --native` (a `task build` binary) | 84 s | 2.8 s | 726 MB |
| Python, a `dict` | 7.2 s | 0.24 s | |

The time is all the map. On `stitchwort run`, a million turns of the
same loop with a two-field record and no map take 0.1 s; with an insert
into a map of 4,096 keys each turn, 4.4 s. With 3.6 million keys the
weight-balanced tree is over 20 levels deep, and each level is a
comparison through the `Ord` dictionary (an `Ordering` value back), a
new node, and a balance check that multiplies sizes; a turn does a
`get` and an `insert`. Sampling the interpreter (macOS `sample`, 8 s
into a 3-million-turn run) puts 64% of the time in the machine's
dispatch loop, 10% in dropping values, 5% growing its value stacks and
about 4% in malloc and free; nothing in the samples names the
Stitchwort functions. Under `--js` every `Nat` is a `bigint` (the
tree's sizes too) and every node and `Ordering` an object, hence the
2.2 GB. There is no profiler for running programs (`STITCHWORT_TIMINGS`
covers checking), as on day 11; I found the split by timing variants of
`main`.

What would make this fast: a dense array from number to turn (the
numbers are below the turn count), which std doesn't have (SW-1473
asks for a persistent array; this day wants one updated in place, since
the old versions are never read again: a `State`-style mutable array, or
in-place update when the array is unshared). Short of that, a `Map`
specialised to `Nat` keys (a Patricia trie, Haskell's `IntMap`) would
drop the dictionary calls and the balance arithmetic. A newcomer writes
exactly this program (it is Matt's Scala), and waits six minutes with
nothing to say where the time goes.

### 2. The counterexample search never finishes on a theorem that names turn 30000000

As first written, Proofs.sw had `part1Correct` and `part2Correct`, each
ending in `Spec.Part2 starting (starting.numberSpoken 30000000)` (`Part2`
being `answer = Spec.numberSpoken starting.numbers.toList 30000000`).
Both checked at once. `stitchwort audit Aoc.Year2020.Day15` then ran at
full CPU until my 120 s timeout, and `audit Proofs.part2Correct` alone
until a 60 s one; `audit --no-search` passed in 0.5 s. `part1Correct`
came back (within 30 s) with "not applicable: the statement's normal
form has more than 100000 nodes". The search reads back each part of
the statement in normal form (`statement_part`,
crates/elab/src/counterexample/mod.rs:111), bounded by the number of
nodes but not by steps, and computing the spec's game 30 million turns
deep, quadratically, before the first node comes back never ends; the
2 s budget per theorem (`--counterexample-budget`) doesn't cover it. So
`task audit:touched`, which the merge verifier runs, would hang on this
day. I stated `correct` for every turn instead, which is stronger and
which the search handles (`numberSpokenSpec`: "none in 844 cases"), and
dropped `Part1`/`Part2` from the spec for one `Answer starting turn`.
A step budget on that read-back, giving "not applicable" as the node
limit does, would let a theorem say "the 30000000th".

### 3. `omega` made a proof that doesn't check

`numberSpokenSpec` needs the final game's turn: `iterateTurn` gives
`(Game.begin _).turn + later`, and I wrote

```stitchwort
let turns: final.turn = Succ later := rewrite iterateTurn starting later _ in omega
```

which is `E-OMEGA-INTERNAL`: "the quoted goal means `later + 1 = Succ
later`, not the goal `1 + later = Succ later`", with "this is a bug in
the compiler's `omega`". `rfl` there failed too ("`1 + later` and `Succ
later` aren't equal"), though in a scratch file `1 + c = Succ c` is
`rfl`. `Eq.trans (iterateTurn starting later _) (Nat.addComm 1 later)`
works. It reproduces in 11 lines with a two-field record, a `step`
that adds 1 to its turn, an `iterTurn` lemma like `iterateTurn` and the
same `let` (the scratch file is in the lane's report). The message was
right to blame itself, which saved time.

### 4. `Parse.readsWeaken` over `Parse.readsMap` needs both its implicits named

`starting()` builds a record from `sepBy1`, so its proof is
`readsWeaken (readsMap … (numbers => { numbers }) _ (readsSepBy1 …))
(…)`. As written, that is `E-TYPE-MISMATCH` pointing into `Parse.nat`'s
inner `match` ("they first differ at `Std.Effect.bind (…)` against `?1
()`", with Note 3 explaining compiler-made `match` functions), which is
about `readsWeaken`'s parser `p`, not `Parse.nat`. With `[p := starting]`
the next error was the `weaker` spec as `?2 read { numbers = numbers }`;
with `[weaker := StartingWritten]` too, it checked. The expected type
says both. A newcomer reading "differ at … `?1 ()`" in std's parser
wouldn't guess to name the parser; a note like "`?1` is `readsWeaken`'s
`p`; name it with `[p := …]`" would say it. Day 13's parsers ended in
`Parse.readsDone` and never met this.

### 5. Messages

- **A pipe into an effectful method.** In a `{IO, Fail}` function,
  `let turns := IO.args() |> .headOr "2020" |> .toNatOrFail` is
  `E-ABILITY`: "this may perform `Fail`, which isn't allowed here …
  `Fail` isn't in the abilities of the enclosing function or handler",
  which it is. `Text.toNatOrFail (IO.args().headOr "2020")` works, and so
  do `"2020" |> .toNatOrFail` and `["2020"] |> .headOr "1" |>
  .toNatOrFail`: it takes the pipe starting with an `IO` call. Four
  lines (`import Std (Fail, IO, List, Text)`, a `main` with that `let`
  and a print) reproduce it.
- **`∧` at the start of a line.** A theorem type split as `(∃ … =>`
  on one line, its body on the next, and `∧ Spec.Part1 …` on a third at
  the first line's column, is `E-PARSE` "expected an expression, but
  found `&&`". It wants the `∧` indented further; the message calls my
  `∧` `&&` and doesn't mention the column, which the `let` message
  does.
- **Good ones.** `E-IMPORT-CLASH` for importing the spec's `spoken`
  into a test namespace that defines its own said exactly what to do;
  `E-REWRITE-NOTHING`'s notes showed the goal had computed `spoken
  (Succ later)` away, which is what led to `lastTracks`.

### 6. Smaller things

- **What helped.** The proofs took about 10 minutes. `Nat.iterateKeeps`
  is the invariant argument in one call; `Map.getInsert` and
  `getInsertOther` were the whole map side; `readsSepBy1` and
  `readsNat` gave the format. The program's first `takeTurn`, `if …
  then game.say a else game.say game.reply`, didn't refine under
  `match below: game.turn < …` (the goal had already computed `<` into
  `<=` of the tail, as days 11 and 12 found); moving the `if` into
  `starting.next`, so a turn is one `say`, made the turn one rewrite
  with `replyTracks` and read better too.
- **`(1 ..= 10).toList`** is `E-UNKNOWN-FIELD` (a range is already a
  `List`); obvious once read, but `toList` on a range is what Scala and
  Kotlin readers write.
- **`List.findIndex`** exists, with no lemmas, and is built on
  `findIndexFrom start`, so a cons step needs the start generalised; the
  spec's `turnsBack` is its own three lines instead.
- **No way to mark a slow test.** `stitchwort test` has no tag or
  option to leave a test out by default, so part 2 isn't a Stitchwort
  test at all; in Rust it is `#[ignore]` plus a `SLOW` list for the
  every-day run.
- **`{ g | … }` in a lambda** for a benchmark needed `(g: Game) =>`;
  `E-CANNOT-INFER` said so.

### Size and time

60 lines of program, 53 of spec, 130 of proofs (Parse 19, Game 56,
Turns 36, Proofs 19), 50 of tests (+1 answer test in `aoc_answers.rs`,
ignored by default). By the clock: 02:29 start; program and tests
passing at 02:36; part 2 measured on three runtimes 02:37 to 03:02 in
the background; the game invariant at 02:41, the turn-by-turn proofs at
02:43, the parser at 02:45, the top theorem at 02:46; then item 2 (the
audit hang and the restatement), the break checks, the timings and
these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day15.Proofs` | 6.2 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day15` | 2.6 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day15.Tests` (17 tests) | 6.6 s user |
| `stitchwort audit Aoc.Year2020.Day15` (32 theorems) | 5.6 s user |
| `stitchwort run Aoc.Year2020.Day15.main` on the input | 357 s user |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 30 ms of
elaboration and 8 ms in the kernel; the rest of the cold time is std's.

### Ranked

1. Part 2 takes six minutes on `stitchwort run` (84 s native, 127 s JS,
   7 s in Python): 30 million `Map` gets and inserts on a 3.6-million-key
   tree, nearly all the time in the tree; no array to use instead, and
   no profiler for running programs (item 1). Library and runtime;
   large (a mutable or in-place array with lemmas), medium (a `Nat`-keyed
   map).
2. The counterexample search's read-back of a statement has no step
   limit, so `audit` (and `audit:touched` in the merge verifier) never
   finishes on a theorem naming turn 30000000 (item 2). Tool; small.
3. `E-OMEGA-INTERNAL` on `1 + later = Succ later` after a `rewrite`,
   with an 11-line repro (item 3). Checker; small to medium.
4. `IO.args() |> … |> .toNatOrFail` is a false `E-ABILITY` (item 5).
   Checker; small to medium.
5. `readsWeaken` over `readsMap` needs `[p := …]` and `[weaker := …]`,
   and the error points into `Parse.nat` (item 4). Message or std;
   small.
6. Smaller: `∧` continuation reported as `&&` without the column; no
   slow-test marker in `stitchwort test`; `findIndex` has no lemmas
   (items 5, 6). Each small.

## Day 16: Ticket Translation

The notes give a rule for each of 20 ticket fields (`departure location:
45-422 or 444-950`: two inclusive ranges), then your ticket, then 236
nearby tickets, each a line of comma-separated values in the same,
unknown, order of fields. Part 1: the sum of the nearby values valid for
no field (the ticket scanning error rate). Part 2: drop the tickets with
such a value, work out which position is which field, and multiply your
ticket's six `departure` values. Answers on Matt's input: 21071 and
3429967441937; the first example's error rate is 71 and the second's 0,
as the puzzle says, and both examples' order is row, class, seat. Matt's
Scala (`Day16.scala`) does the same elimination, a `MultiDict` of
candidates reassigned in a `while` loop; I didn't run it. An independent Python script
agrees on both answers and both examples. 190 of the 236 nearby tickets
are valid; the candidate sets at the 20 positions have sizes 1 to 20,
nested, so the elimination never has a choice.

The domain types are `Range` (`low`, `high`, with `range.contains`),
`Rule` (`field`, `first`, `second`, with `rule.allows value` and
`rule.isDeparture`), `Ticket` (`values`) and `Notes` (`rules`, `yours`,
`nearby`), with `notes.errorRate`, `notes.validTickets`,
`notes.candidates` (a fold of `narrow` over the valid tickets, from
every rule at every position: `narrow` is a `zipWith` that keeps, at each
position, the fields allowing the ticket's value there),
`notes.fieldOrder` and `notes.departureProduct`. The elimination works on
`Slot`s (a position's `candidates`, fixed, and the `field` settled there,
an `Option`): `settle` settles the first unsettled position with one
candidate left once the settled fields are left out (`slot.remaining`),
`allSettled` reads off the order when every position is settled, and
`eliminate` repeats `settle` for as many rounds as there are positions.
`fieldOrder` first checks that every valid ticket has one value per
field. The program and its 20 tests passed on the first run, in 0.5 s.

The spec (`Spec/Spec.sw`) shares the four data types and nothing else:
`NumberWritten`, `RangeWritten`, `RuleWritten`, `TicketWritten`,
`NotesWritten` (the rules a line each, a blank line, `your ticket:`, a
line break and your ticket, a blank line, `nearby tickets:` and the
nearby tickets a line each); `inRange`, `validFor`, `validForSomeField`,
`errorRate` (a `sumBy` over the nearby tickets of a `sumBy` over their
values, each counting itself if no field allows it, else 0) and
`Part1`; `ValidTicket`, `FieldOrder notes order` (as many positions as
rules, the order `Distinct`, each of its fields a rule, and on every
valid nearby ticket each value valid for the field at its position),
`departureProduct order values` (recursive over the two lists) and
`Part2 notes answer` (the departure product under some `FieldOrder`).
`FieldOrder` is a bijection between positions and rules by pigeonhole
(injective, into a set of the same size); it doesn't say "each rule at
exactly one position" in so many words. The puzzle's "the" order is not
in the spec: two fields with the same ranges could swap, and the
elimination then gets stuck (a test has such notes).

Proved (`Aoc.Year2020.Day16.Proofs`):

- `readsRange`, `readsRule`, `readsTicket`, `readsNotes`, `parseWritten`
  (Parse.sw): if `parseNotes` reads `input`, the input is the notes
  written out, then any line breaks.
- `errorTerm`, `errorRateSpec` (Part1.sw): for any notes,
  `notes.errorRate` is the spec's `errorRate`.
- `AllAllow`, `Within`, `all2Compose`, `all2Within`, `all2Replicate`,
  `narrowLength`, `narrowWithin`, `narrowAllows`, `withinTrans`,
  `allowWithin`, `foldNarrow`, `candidatesFit` (Candidates.sw): when every
  valid ticket has a value per field, `notes.candidates` has one list per
  field, each within the rules, and every field in a position's list
  allows every valid ticket's value there.
- `Sound`, `Keeps`, `Once`, `Step`, `Adds`, and `stepRefl`, `stepsRefl`,
  `keepsStep`, `settledCons`, `passSteps`, `settleSteps`,
  `notContainedCount`, `passAdds`, `settleAdds`, `settleOnce`,
  `allSettledFields`, `eliminateFinds` (Eliminate.sw): a round keeps
  every position's candidates and settles a position only with one of
  them, and adds one field to the settled ones, which wasn't among them;
  so the order `eliminate` returns has at each position a field among its
  candidates, and no field twice (each field's count at most 1).
- `distinctOfCounts`, `openSlot`, `keepsOpen`, `openSettled`, `onceOpen`,
  `validTicketValid`, `fieldOrderValid`, `departureProductSpec`,
  `departureProductValid` (Part2.sw): if `notes.fieldOrder = Some order`,
  then `Spec.FieldOrder notes order`; if `notes.departureProduct = Some
  answer`, then `Spec.Part2 notes answer`.
- `Agrees`, `settledIn`, `freshOf`, `passAgrees`, `settleAgrees`,
  `settledSame`, `eliminateOnly`, `narrowAgrees`, `foldAgrees`,
  `replicateAgrees`, `agreesOpen`, `fieldOrderOnly` (Unique.sw): any
  order satisfying `Spec.FieldOrder` has each position's field among its
  candidates; it agrees with every field a round settles, because that
  field is the position's only candidate not settled elsewhere and the
  order is `Distinct`; so if `notes.fieldOrder = Some order`, every
  `Spec.FieldOrder notes other` has `other = order`.
- `part1Correct`, `part2Exactly`, `part2Correct` (Proofs.sw): for every
  input the parser reads, the input is the notes written out and
  `notes.errorRate` is `Spec.Part1`'s answer; when
  `notes.departureProduct = Some answer`, `Spec.Part2 notes other ↔ other
  = answer`.

Not proved: that every well-formed input parses (as on days 2 to 15);
that the elimination succeeds whenever exactly one order fits (it is
complete only for notes it can solve one forced step at a time; a
puzzle needing a guess, or two fields with the same ranges, makes it
return `None`, and part 2 then fails at run time with a message); that
`main` prints what it reads. There is no added hypothesis and no
`opaque`: the answers' theorems are conditional on the program giving an
answer, which is what "if the elimination succeeds" means here, and on
the input it does (a test).

Breaking the program made the proofs fail: `value < range.high` in
`Range.contains` fails `errorTerm` (both `rfl`s), `validTicketValid`,
`fieldOrderValid` and `fieldOrderOnly`; `narrow` keeping every field
fails `narrowWithin`, `narrowAllows` and `narrowAgrees`; dropping
`fieldOrder`'s length check fails `fieldOrderValid` and
`fieldOrderOnly` (the first for a reason, the second only because its
case split follows the program's `if`); `remaining` not leaving out the
settled fields fails `settleSteps`, `settleAdds` and `settleAgrees`;
settling a position with *any* candidate left (`[field, ..others]` for
`[field]`) fails `settleAgrees` (the field is no longer forced), and the
case splits of `settleSteps` and `settleAdds`, though validity alone
would survive that change: a greedy pick of any fresh candidate still
gives a valid order when it finishes. The audit (with the counterexample search): `audited 75
theorems: 0 failed, 1 with warnings, 74 passed`; the warning is the
generated equation `eliminate.eq.none.succ.some` (hypotheses: no
position settled and `settle` finding one), which random slots rarely
meet: narrow, not vacuous (SW-1261, as on earlier days).

### 1. A lemma about `slot` doesn't fit inside `match field: slot.field`

`settle` matches on `slot.field`, then on `slot.remaining settled`, so
each proof about it does too, and three of the five arms ("pass this
position over") are the same: a helper lemma `passAdds settled slot
slots next found rest`. Called in the `Some existing` arm it is
`E-TYPE-MISMATCH`: the goal there has `Some existing` for `slot.field`
(the `match` refined it, after `settledFields [slot, ..slots]` computed
to `List.consSome slot.field …`), and the helper's type still has
`slot.field`. The note says "a term written out inside a branch … isn't
refined by the `match` … Write `_` for such an argument", which doesn't
apply: the mismatch is in the helper's result, not an argument. What
works, both found by trying:

```stitchwort
| Some existing =>
  let passed := passAdds settled slot slots next found (settleAdds settled slots)
  rewrite field at passed in passed
```

or binding the helper (as a function of `found`) in a `let` before the
`match`, since "the `let`-bound lemmas from before the `match` are
refined" (the earlier note said so, which is how I found it). Both are
idioms nobody would guess. A newcomer reaching for the obvious helper
lemma meets this on any `match` over a field of a variable they also pass
whole to a lemma; the fix might be for the `match` to refine the types
of terms in its arms too, or for the error to suggest the two idioms.

The same rule bit the other way three times: passing the `match`'s own
equation (`settledField: slot.field = Some x`) where the refined
hypothesis wants `Some x = Some x` is a mismatch, whose Note 2 rightly
says `rfl` proves it; but in `allSettledFields`, where the `slot.field`
appeared only after a `rewrite`, the equation was needed and `rfl`
failed ("`slot.field` and `Some rule` aren't equal"). Which one a place
needs depends on whether the occurrence was in the goal when the `match`
ran, which the source doesn't show. Accepting the equation wherever the
refined form is expected (they are equal by the equation) would remove
the guess.

SW-1538 fixed both: in a named `match`, a proof whose type has the
scrutinee where what's expected has the arm's value (or the other way
round) is rewritten along the `match`'s equation, so `passAdds …` is now
written directly in the three arms, and the equation fits where the
refined form is expected. Without a name, `E-TYPE-MISMATCH` says to add
one (or bind the lemma before the `match`); `E-REFL` names the equation
where it, not `rfl`, proves a premise.

### 2. Std's `List.All2` has almost no toolkit

`List.All2` has `all2Weaken`, `all2Length`, `all2Map`, `all2MapLeft` and
`all2WithIndex`. This day's proofs are chains of `All2` relations across
three lists (order against candidates against a ticket's values, slots
against candidates, candidates against the rules), and I wrote:
`all2Compose` (`All2 r xs ys → All2 s ys zs → All2 t xs zs` given a link
lemma; Candidates.sw:15), the reflexive `all2Within`, `all2Replicate`
(`All2 r xs (replicate n y) → x ∈ xs → r x y`), `replicateAgrees` (the
converse), `settledSame` (`All2` with a functional relation pins the
list), and four `zipWith` lemmas, each one induction over two or three
lists with four or six impossible cases: `narrowLength` (std's
`lengthZipWith` gives `Nat.min`, not "the length of either, when they're
equal"), `narrowWithin`, `narrowAllows`, `narrowAgrees` (what the
`zipWith` of a filter keeps, relative to each input). About 70 of the
day's 600 lines of proof are this generic list plumbing. Std candidates:
`List.all2Compose`, `List.all2Refl`, `List.all2ReplicateRight`,
`List.all2ZipWith` (a pointwise fact about `zipWith xs ys f` against `xs`
or `ys`), `List.lengthZipWithEq`.

### 3. No "distinct from counts", and two ways to count

`FieldOrder` asks for `order.Distinct`; the elimination's invariant is a
count (each field settled at most once), since a round adds one field in
the middle of the list. Std has `List.distinctOfOccurrences` (through a
key and `List.occurrences`) and `List.countEqDistinct` (the other
direction), but not `(∀ x, xs.count (== x) ≤ 1) → xs.Distinct`
(`distinctOfCounts`, Part2.sw:9, 15 lines), nor `xs.contains x = False →
xs.count (== x) = 0` (`notContainedCount`, Eliminate.sw). `List.count`
and `List.occurrences` are two names for counting, with `countOccurrences`
between them; a newcomer finds lemmas for one and needs the other.

### 4. The elimination belongs in Aoc.Common

Settling a position whose candidates are down to one, then removing that
choice everywhere else, is the whole of part 2, and 2020 day 21 (allergen
assessment) is the same algorithm over allergens and ingredients. The
proofs here are generic in all but name: `Slot`, `settle`, `allSettled`,
`eliminate`, the 12 lemmas of Eliminate.sw and the first seven of
Unique.sw use nothing of `Rule` but its `DecEq`. As `Aoc.Common.Elimination` over any type with
`DecEq`, with "the result is distinct and within the candidates" and "any
distinct choice within the candidates equals it" as its theorems, day
21 would be a call. I didn't move it in this lane.

### 5. A record of a pipe defeats `readsMap`

The program's first parser for a ticket was `{ values = Parse.sepBy1
Parse.nat (() => Parse.char ',') |> .toList }`. Its proof by
`Parse.readsWeaken [p := ticket] [weaker := TicketWritten]
(Parse.readsMap … (values => { values = values.toList }) _ (readsSepBy1
…))` is `E-TYPE-MISMATCH` pointing into `Parse.nat`'s inner `match`
("they first differ at `Std.Effect.bind ((match …) ….fst) …`"), with both
implicits named, which was day 15's fix (its item 4). Rewriting the
parser as `let values := …` then `{ values = values.toList }`, proved
with `readsThen` and `readsDone`, checked at once. So the program changed
shape for the proof, and the message points into std's parser rather
than at the `f` that didn't match.

### 6. Messages

- **A `Prop` method after `∧` in a lambda.** `List.All2 (slot fields =>
  slot.candidates = fields ∧ slot.Sound) …`, with `def Slot.Sound (slot:
  Slot): Prop`, is `E-TYPE-MISMATCH` "expected a proposition … this is a
  type of data, not a proposition", with "`&&` here is on propositions".
  `Slot.Sound slot` works, as do `slot.Sound` alone in the lambda and
  `slot.candidates = [] ∧ slot.sound` outside a lambda. Seven lines
  reproduce it (`type Slot`, `def Slot.sound … : Prop`, `def B (slots:
  List Slot): Prop := List.All (slot => slot.candidates = [] ∧
  slot.sound) slots`). The message is wrong about the cause, and calls
  `∧` `&&` (day 15 saw the same naming).
- **`rewrite Nat.oneMul in …`** is `E-REWRITE-RULE` "this equation's left
  side starts with an unknown function", with "give the implicit
  arguments explicitly". `Nat.oneMul` has one argument, explicit; given
  it (`Nat.oneMul (Spec.departureProduct order values)`), it works. Its
  left side `1 * n` computes to something headed by `n`, which is what
  "unknown function" means here; `rewrite List.countAppend` and
  `List.productCons value _` with open arguments were fine. The note
  should say which argument to give, and that it's explicit.
- **`Nat.succInjective (m) (n) (p: Succ m = Succ n)`** takes `m` and `n`
  explicitly, though `p` fixes them (D2422's rule): the first try,
  `Nat.succInjective same`, is "expected `Nat`, but this has type `Succ
  … = Succ …`".
- **A lambda's parameter hiding a local.** In `List.all2Weaken (rule slot
  unsettled isOpen => rewrite settledCons, … in …)` inside an arm that
  had its own `slot`, the rewrite went for the lambda's `slot`; the
  message showed the outer one as `slot✝`, which is the only clue.
  `W-LAMBDA-SHADOW` warns when a parameter hides a function (it caught my
  parameter `open`, hiding my `def open`), not a variable.
- **`Some { … }`, again**, twice in one test (`Ok (Some ({ … }))`);
  `E-UNKNOWN-FIELD`'s note gave the fix each time (days 5, 8, 13 and 14).
- **Good ones.** `E-REWRITE-NOTHING`'s "this `match` replaced
  `Notes.fitsSomeField notes value` with `True` … the proof checks
  without this rewrite"; the mismatch whose Note 2 says "both sides of
  what's expected are `Some after`, so `rfl` proves it"; and the one that
  said `Void.exfalso` needs `import Std (Void)`.

### 7. Smaller things

- **What helped.** All the proofs took about 25 minutes, and most lemmas
  checked as first written, including the 9-step `readsNotes` chain and
  the fold invariant `foldNarrow`. Designing the elimination for its
  proof decided that: the candidates never change, the settled fields
  are left out when a position is looked at (so a round changes one
  slot), and a slot is a record with an `Option` field. The Scala
  version, which removes each settled field from every other position's
  set in its `MultiDict`, has the same behaviour and a harder invariant
  (every set changes each round). `Parse.lines` followed by `Parse.blankLine` backtracked over
  the line break as hoped. `List.memFilter`/`memFilterIntro`,
  `countCons`, `countPositive`, `sumByFilter`, `sumByFlatMap` and
  `sumByCong` were each found by `stitchwort search` or a grep in one
  try.
- **`rewrite h at t in t`**, rewriting a `let`-bound proof into the
  refined goal's form, is a good trick that isn't in the proving guide.
- **No `List.countOf`.** Every count is `xs.count (field => field ==
  rule)`, written out ten times.
- **The spec's bijection.** "A field for each position, each field once"
  is `Distinct`, members of the rules and the same length: honest, but a
  reader has to supply the pigeonhole. `List.Perm order notes.rules` would
  say it directly, but needs the rules distinct, which the puzzle
  doesn't promise.

### Size and time

167 lines of program, 100 of spec, 604 of proofs (Parse 53, Part1 21,
Candidates 90, Eliminate 145, Part2 72, Unique 181, Proofs 42), 99 of
tests (+1 answer test in `aoc_answers.rs`).
By the clock: 03:36 start; Python answers at 03:40; program and tests
passing at 03:51; parser proof at 03:54; candidates at 03:57; the
elimination's validity at 03:59; part 2 valid at 04:00; uniqueness at
04:03; top-level theorems at 04:04; then the break checks, the audit,
the timings and these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day16.Proofs` | 5.1 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day16` | 1.4 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day16.Tests` (23 tests) | 5.1 s user |
| `stitchwort audit Aoc.Year2020.Day16` (75 theorems) | 1.0 s user (warm) |
| `stitchwort run Aoc.Year2020.Day16.main` on the input | 0.5 s user |
| `task test:one -- year2020_day16` | 2.0 s for the test (2 min 20 s with building the test binaries) |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 524 ms of
elaboration and 30 ms in the kernel (`readsNotes` 247 ms of it, 3.3
million steps); the rest of the cold time is std's modules.

### Ranked

1. A helper lemma about a variable doesn't fit inside a `match` on one of
   its fields, because the arm's goal is refined and the lemma's type
   isn't; the two working idioms (`rewrite e at h in h`, a `let` before
   the `match`) aren't suggested, and the suggested `_` doesn't apply;
   when to pass the `match`'s equation and when `rfl` can't be told from
   the source (item 1). Checker or message; medium.
2. `List.All2` lacks compose, reflexivity, replicate and `zipWith`
   lemmas, and `lengthZipWith` has no equal-lengths form: about 70 lines
   of plumbing here (item 2). Library; small.
3. The elimination (`settle`, `eliminate` and its validity and
   uniqueness theorems) is generic and day 21 needs it: move it to
   `Aoc.Common` (item 4). AoC library; small.
4. A `Prop` method after `∧` in a lambda is "a type of data, not a
   proposition", with a 7-line repro (item 6). Checker; small.
5. No `distinctOfCounts` or "absent means count 0"; `count` and
   `occurrences` both exist (item 3). Library; small.
6. `readsMap` over `{ field = p() |> f }` fails with an error inside
   `Parse.nat`, even with the implicits named (item 5). Message or std;
   small.
7. Smaller: `rewrite Nat.oneMul` blames implicit arguments;
   `Nat.succInjective`'s explicit `m n`; no warning for a lambda
   parameter hiding a local; `Some { … }` again; no `List.countOf`
   (items 6, 7). Each small.

## Day 17: Conway Cubes

A Game of Life in an infinite grid of cubes. The input is a flat slice
(`#` active, `.` inactive) at z = 0; every other cube starts inactive. In
a cycle every cube changes at once by its active neighbours (the cubes
within 1 in every coordinate, 26 of them in three dimensions): an active
cube stays active with 2 or 3, an inactive one becomes active with
exactly 3. Part 1: the active cubes after six cycles in three dimensions;
part 2: the same in four (80 neighbours). Answers on Matt's input (8 by
8): 289 and 2084; the example gives 112 and 848, and 11, 21, 38 active
cubes after its first three cycles (29 and 60 in four dimensions), as
the puzzle's pictures show. Matt's Scala (`Day17.scala`) checks every
cube of the bounding box each cycle, counting neighbours in the set; I
didn't run it. An independent Python script (a `Counter` of neighbour
hits, the same algorithm as here) agrees on both answers and the
example's, in 0.24 s for both. Part 2's last cycle has 2,628 active
cubes and 27,108 counted ones; the six cycles make 383,120 neighbour
hits.

The domain types are `CubeState` (`Active`, `Inactive`, with `symbol`),
`Slice` (the input, a `Grid CubeState` from `Aoc.Common.parseGrid`),
`Cube` (`coordinates`, a `List Int`, with an `Ord` by them, so one
program serves both parts) and `Pocket` (`active`, a `Set Cube`). A
cube's `neighbours` are `within1 coordinates` (every list within 1 in
each place, 3 ^ n of them) without itself; `Cube.inSlice dimensions at`
is the slice position's cube, padded with zeros; `slice.pocket
dimensions`, `pocket.cycle`, `pocket.boot` (`Nat.iterate 6`) and
`pocket.activeCount`. A cycle is `Map.counts` of every active cube's
neighbours (so only cubes next to an active one are looked at), then
`filter pocket.activeNext` (3, or 2 and active) and `keySet`: three
lines. The program and its 15 tests passed on the first run.

The spec (`Spec/Spec.sw`) shares the data types and `Cube`'s order (for
`Set Cube`) and nothing else. `symbol` and `RowWritten` (a line is its
row, a character a cube); `Starts slice dimensions start` (a cube is in
`start` exactly when it is `[x, y, 0, …]` for an active cube at column
`x`, row `y` of the slice); `within1` on two coordinate lists (as many
of each, each pair at most 1 apart) and `neighbours other cube` ("any of
the 26 other cubes where any of their coordinates differ by at most 1":
a different cube, `within1`); `activeNeighbours active cube`, a
`Set.count`; `activeAfter` (the puzzle's four sentences of rules);
`Cycle before after` (a cube is in `after` exactly when `activeAfter
before` says so: "all cubes simultaneously change their state"),
`Cycles`, and `Answer slice dimensions answer` (some `start` and `final`
with `Starts`, `Cycles 6` and `answer = final.size`). The spec never
lists a cube's neighbours: it counts the active cubes that are
neighbours, which reads as the puzzle does and is what the program's
counting adds up to, so no proof needs the relation's symmetry.

Proved (`Aoc.Year2020.Day17.Proofs`):

- `readsCubeState`, `gridWritten`, `parseWritten` (Parse.sw, day 11's
  three lemmas with the names changed): if `parseSlice` reads `input`,
  each line of the input is its row of the slice, and the slice is a
  rectangle.
- `equalCons`, `countPrefixed`, `countPrefixedNil`, `window`,
  `windowAnd`, `countWithin1`, `equalCubes`, `differentSelf`,
  `differentCubes`, `countNeighbours` (Neighbours.sw): `within1 xs` holds
  `ys` once if `Spec.within1 xs ys` and otherwise not at all, so for any
  cubes, `cube.neighbours.count (== other)` is 1 if `Spec.neighbours
  cube other` and 0 if not.
- `setCount`, `countsActive`, `containsFilter`, `activeNextRule`,
  `noneRule`, `cycleActive` (Cycle.sw): the count `Map.counts` keeps for
  a cube is `Spec.activeNeighbours` (0 when it has no entry), so for
  every pocket and cube, `pocket.cycle.active.contains cube =
  Spec.activeAfter pocket.active cube`.
- `startsPocket`, `cycles` (Boot.sw): `Spec.Starts slice dimensions
  (slice.pocket dimensions).active`, and `Spec.Cycles n pocket.active
  (Nat.iterate n Pocket.cycle pocket).active` for every `n`.
- `startsUnique`, `cyclesUnique`, `answerExactly`, `correct` (Proofs.sw):
  for every input the parser reads and any number of dimensions, the
  lines are the slice's rows, and `Spec.Answer slice dimensions answer ↔
  answer = (slice.pocket dimensions |> .boot |> .activeCount)`: the
  program's count is the answer and the only one.

Not proved: that every well-formed input parses (as on days 2 to 16);
that `main` asks for 3 and 4 dimensions (it reads so). There is no added
hypothesis and no `opaque`. The theorems hold in any number of
dimensions, including 0 and 1, where `Starts` pads nothing and the
slice's cubes still have two coordinates; the puzzle asks only for 3 and
4.

Breaking the program made the proofs fail: `count == 4` for `count == 3`
in `activeNext` fails `cycleActive` (`activeNextRule` no longer fits its
`Some` arm), as does `count == 1` for `count == 2`;
swapping `x` and `y` in `Cube.inSlice` fails `startsPocket`. Dropping
`coordinate + 1` from `within1`, or the filter that leaves a cube out of
its own neighbours, fails `countWithin1` and `countNeighbours`, but only
as `E-REWRITE-NOTHING`, since the proofs' rewrites follow the program's
shape. The audit (with the counterexample search): `audited 43
theorems: 0 failed, 0 with warnings, 43 passed`.

### 1. `cases` on three `Int` comparisons splits `Int`'s insides and gives up

The one fact about numbers the proof needs: of `x - 1`, `x` and `x + 1`,
`y` equals one exactly when it is within 1 of `x`, as a count. As

```stitchwort
theorem window (x: Int) (y: Int):
    (if x + (-1) == y then 1 else 0) + (if x == y then 1 else 0) + (if x + 1 == y then 1 else 0) = Bool.toNat (x + (-1) <= y && y <= x + 1) :=
  cases
```

it is `E-CASES-BUDGET`, and Note 1 lists what it split: "`x + (-1)`, `y`,
`Std.Nat.decEq n✝¹ n✝`, `x`, … `Int.subNatNat 1 (Succ n✝)`, …
`Int.subNatNatFrom 1 (Succ n✝) n✝`": it took `Int` apart into its
constructors instead of splitting the four `Bool` comparisons, each of
which `omega` reads (a `match a: x + (-1) == y` hands it `x - 1 = y` or
`x - 1 ≠ y`). What checks is a hand-written tree of `match`es on the
four comparisons, 16 arms each closed by `omega` (Neighbours.sw:31–53),
22 lines for a fact Lean's `omega` or `decide` would take in one. 2021
day 2's notes saw `cases` show `Int`'s insides in a failed case; here it
blocks a true lemma. If `cases` split comparisons of `Int`s (and `Nat`s)
as atoms and closed each case with `omega` before looking inside a
number, this would be `cases`; or `omega` could split `if`s on
comparisons itself.

### 2. `==` on a list or a record doesn't compute, and std has no lemmas for it

`Map.counts` counts with `== cube`, so the proof meets `[here, ..more]
== [y, ..ys]` (from the coordinates) and `{ coordinates = x } ==
other` (from `Cube`'s derived equality). Neither computes when the
parts are variables: the goal shows `Std.Decidable.toBool
(Std.Decidable.not (List.decEq (x y => Int.decEq x y) coordinates
here))` and `(Cube.%decEq …)`. I wrote `equalCons` (`([x, ..xs] == [y,
..ys]) = (x == y ∧ xs == ys)`), `equalCubes`, `differentCubes` (the same
for `!=`) and `differentSelf` (`(x != x) = False`), 25 lines, each a
`Bool.eqOf` over `DecEq.sound` and `DecEq.refl`. `stitchwort search
'(([?a, ..?b]: List _) == [?c, ..?d]) = _'` gave 348 results in the
relaxed pass, none about lists. Std candidates: `List.beqCons`,
`List.beqNilCons`, `DecEq.neSelf`; and for records, a generated
`T.beqMk` (`({ f = a }: T) == { f = b }` is `a == b`, for one field),
since every domain type with `DecEq` meets this the first time a proof
counts or looks one up.

### 3. A `Bool` `!=` on both sides of `=` is read as `≠`

`differentCubes` was first stated `(({ coordinates = here }: Cube) != {
coordinates = there }) = (here != there)`. It checked as a statement,
but as an equation of two propositions `≠`, and its proof's `DecEq.trueOfNe`
was "expected `({ coordinates = here } ≠ { coordinates = there }) =
(here ≠ there)`, but this has type `Std.Decidable.toBool … = True`";
used in a `rewrite`, it was `E-REWRITE-MOTIVE` ("expected `Decidable
x'`, but this has type `Decidable ({ coordinates = here } ≠ …)`"),
which says nothing about `Bool`. Writing `((a != b): Bool)` on each
side, as std does, fixed both. A statement whose `!=` is elaborated as
`≠` next to `=` could warn, or the mismatch note could say "this `!=`
was read as the proposition `≠`; write `((a != b): Bool)` for the
`Bool`".

### 4. `rewrite` with the program's answer: "a value was too large to show"

`answerExactly`'s backward half, given `same: answer =
(slice.pocket dimensions |> .boot |> .activeCount)`, was first `rewrite
same in activeCountAnswer slice dimensions` (the lemma that the
program's count satisfies `Answer`). That is `E-RESOURCE`, "a value was
too large to show … the value being shown was a call of
`Pocket.activeCount`, computed far enough to be very large", pointing at
the whole theorem. Passing `same` as the last component of the witness,
with no `rewrite`, checks at once; so does `Eq.trans counted (Eq.cong
Set.size finalSame)` for the forward half in place of `rewrite counted,
finalSame in rfl`, which failed the same way. Days 11 of 2020 and of
2021 met this message from a `match`; here the trigger is a `rewrite`
whose right side is six cycles of the program on an unknown slice.
Nothing needed showing, and the note doesn't say which `rewrite` it was
in; the guide's bisecting with `?` found it in two runs.

### 5. Smaller things

- **What helped.** All the proofs took about 20 minutes. `Map.counts`
  with `Map.getOrCounts` (`(Map.counts xs).getOr x 0 = xs.count (==
  x)`) made the key lemma, the count kept for a cube is its active
  neighbours, a five-step `calc` with `List.countFlatMap`,
  `List.sumByCong`, `List.countSumBy` and `Set.foldLeftToList`; I had
  expected to write the counting fold's invariant by hand. `Map.getFilter`,
  `Map.containsKeySet`, `Set.containsFromListIff`, `Set.ext`,
  `Set.extIff`, `List.memMapElim`, `List.countFilter`,
  `List.countFalse` and day 11's `memGridPositionsWhere` were each found
  by one grep. Stating `Cycle` as a relation, with `Set.ext` giving its
  uniqueness, gave the "the only answer" theorem in 20 lines.
- **Fast enough.** 8.4 s for both parts on `stitchwort run` (part 1 0.8
  s), 3.0 s `--native`, 1.4 s `--js`, 0.24 s in Python: 383,120
  `insertWith`s into maps of up to 27,108 `List Int` keys, about 20 µs
  each on the interpreter. No `#[ignore]`.
- **No `Int` ranges.** A test's box of cubes, `(-2 ..= 4)`, is "this is
  negative, but a `Nat` is expected here", with the good note "ranges
  exist for `Nat` only so far (`Int` is to come)"; `(0 ..= 6).map (n =>
  n.toInt - 2)` works. Every grid puzzle with negative coordinates wants
  `Int` ranges.
- **No record eta.** `startsPocket` had `slice.grid.at at = Some state`
  where `Starts` wants `slice.grid.at { row = at.row, column = at.column
  }`: a mismatch inside `cellAt`'s `match`. Matching `at` as `{ row,
  column }` first fixed it (the `match` refines the hypotheses). As day 1
  found for pairs; a record of `Nat`s could have eta.
- **A lemma about a `match` must not write one.** `containsFilter` first
  ended `= (match m.get key with | Some value => p key value | None =>
  False)`, and its use against the same `match` written in a `calc` step
  is a mismatch of two hidden functions; the note says exactly why.
  `(m.get key).any (p key)` says the same with a name. Std candidates:
  `Map.containsFilter` in that form, and `Set.countToList` (`set.count
  p = set.toList.count p`, `setCount` here, one line through
  `Set.foldLeftToList`, but not findable as a `count` lemma).
- **A Life step for `Aoc.Common`.** The cycle is generic in all but its
  neighbours: given `neighbours: p → List p` and the fact that each
  `neighbours q` holds `x` once exactly when some relation `R q x`
  holds, `Map.counts` gives each point's count of active `R`-neighbours
  (`countsActive` and `cycleActive` use nothing of `Cube` but that
  fact). 2020 day 24 part 2 is the same Life over hexagonal tiles, and
  day 11's rule is a cousin; `Aoc.Common.Life` with `step` and its two
  theorems would make day 24's proof a lemma about hex neighbours.

### Size and time

90 lines of program, 74 of spec, 274 of proofs (Parse 40, Neighbours
105, Cycle 58, Boot 29, Proofs 42), 70 of tests (+1 answer test in
`aoc_answers.rs`). By the clock: 04:18 start; program and example
answers at 04:27, input answers at 04:29 (9 s), tests passing at 04:32;
`countWithin1` at 04:38 (most of it item 1), `countNeighbours` at 04:40,
`cycleActive` at 04:42 (Cycle.sw and Boot.sw took four minutes), the
top theorems and the audit by 04:45; then the break checks, the timings
and these notes.

| command | time |
| --- | --- |
| `stitchwort check --no-cache Aoc.Year2020.Day17.Proofs` | 8.9 s user |
| `stitchwort check --no-cache Aoc.Year2020.Day17` | 4.9 s user |
| `stitchwort test --no-cache Aoc.Year2020.Day17.Tests` (15 tests) | 15.6 s user |
| `stitchwort audit Aoc.Year2020.Day17` (43 theorems) | 6.2 s user |
| `stitchwort run Aoc.Year2020.Day17.main` on the input | 8.4 s user (part 1 0.8 s) |
| `task test:one -- year2020_day17` | 12.5 s for the test (2 min 15 s with building the test binaries) |

`STITCHWORT_TIMINGS=1` puts the Proofs namespace at 138 ms of
elaboration and 24 ms in the kernel; the rest of the cold time is std's.

### Ranked

1. `cases` over three `Int` comparisons takes `Int` apart and runs out
   of cases, where splitting the comparisons and calling `omega` closes
   each; a 3-line fact took 22 lines of `match` (item 1). Tactic;
   medium.
2. `==` on a list with a head, or on a record, doesn't compute on
   variables, and std has no `beqCons`, `neSelf` or per-record `==`
   lemma: 25 lines of `Bool.eqOf` plumbing; `search` doesn't find
   anything for the pattern (item 2). Library (and generated lemmas);
   small.
3. A Life step with its two theorems belongs in `Aoc.Common` for 2020
   day 24 (item 5). AoC library; small.
4. A `Bool` `!=` beside `=` in a statement is read as `≠`, and the errors
   that follow are about `Decidable`, not `Bool` (item 3). Message;
   small.
5. `rewrite` with an equation whose side is the program's answer is
   E-RESOURCE "too large to show", naming no `rewrite` (item 4; day 11 of 2020 and of 2021
   from `match`). Checker or message; small to medium.
6. Smaller: no `Int` ranges; no record eta; `Map.containsFilter` and
   `Set.countToList` missing (item 5). Each small.
