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
- `sizeCount`: a set of questions has as many members as there are of the
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
  `Set.containsFoldInsert` for `fromList`; a `Set.containsUnions` and the
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
