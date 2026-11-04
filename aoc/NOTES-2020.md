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
