# `byFacts` outside the formatter: bars G1 to G4 measured

**Status:** measured 21 November 2026 (SW-4516, a Sonnet lane), on branch
`lane/SW-4516` from `main` at `382db8c1c`. Bars are Fable's, from
[SW-4483-byfacts-in-context.md](SW-4483-byfacts-in-context.md) §5.
Times are `check --timings=all` totals for one theorem, release binary, so
they are good to about 0.1 ms and, for the larger ones, 5%. SW-4515 pilots
`tools/fmt`; nothing there was committed from here.

## In plain words

`byFacts` clears G1 (it closes every goal `cases` failed on, as fast as
the hand term), G2 (six of the eight rows) and G3 (it takes 4.2% of the
proof lines of three files after today's tools, with check time between
1.0 and 1.2 times). It misses half of G4: every reject example fails in
under 5 ms, but a failing `byFacts` on row 34's arguments takes 290 to
360 ms, and one on AoC 2021 day 12 took 25 seconds.

One gap explains most of what did not convert and is worth fixing before
the pilot's verdict: **a fact or lemma whose conclusion is an `∧` or a
record of proofs is never used** (§ "Findings", 1). The gain is also
uneven: 7.8% of `Doc/Words.sw`, 4.3% of `Reach.sw`, 0.6% of AoC day 12.

## G1: the goals §1.2 marks as failing

Each goal is a theorem closed by `byFacts` and, beside it, by its hand
term. Scratch file, three runs, same numbers each time. Milliseconds,
elaboration plus kernel.

| Goal | `byFacts` | Hand term | Within 1 ms |
|---|---|---|---|
| `a → b` and `a` (plain `Prop`s) | 0.2 | 0.1 (`f x`) | yes |
| `a → b → c`, `a`, `b` | 0.1 | 0.1 (`f x y`) | yes |
| three chained implications | 0.1 | 0.1 (`k (g (f x))`) | yes |
| local `∀ x => p x → g x`, `p 3` | 0.2 | 0.1 (`step 3 a`) | yes |
| the same, two premises | 0.2 | 0.1 | yes |
| local `∀ x y`, unknown fixed by a fact | 0.1 | 0.1 | yes |
| `a ∧ b`, `a → c`, goal `c ∧ b` | 0.1 | 0.1 | yes |
| `a = b`, `f b = 0` gives `f a = 0` (`Nat`) | 0.2 | 0.1 (`rewrite e then h`) | yes |
| the same on `List` | 0.2 | 0.1 | yes |
| `∃ n => p n ∧ q n` gives `∃ n => q n` | 0.2 | 0.2 | yes |
| a named lemma, premise in scope (`byFacts [Std.Nat.lessTrans]`) | 0.3 | 0.2 | yes |

**G1 met.** The widest gap is 0.1 ms. All of them are also in
`examples/accept/facts-probes.sw`.

## G2: rows 7, 10, 17, 18, 20, 25, 34 and 37

Bar: at least five shorter, or the same length with fewer names spelled,
and checking. **Six qualify** (seven counting row 25's tie).

| Row | Theorem | Result | Lines | Check time |
|---|---|---|---|---|
| 7 | `List.allAppendLeft` | **qualifies.** The step is `\| [x, ..xs], _ => byFacts [List.allAppendLeft]`; no `Both h hxs`, no `p xs ys hxs`. The `[]` arm also closes with plain `byFacts`. Committed (std) | 4, same | 0.5 ms vs 0.3 |
| 10 | `Parse.runsOperatorsExample` | **qualifies.** `runsOperators … (byFacts) (byFacts [Parse.runsOne "a digit" … '9' 9, …])`. The review estimated 12 lines; it is 17 once formatted, the same as today's `cases` version (18) and 14 fewer than now (31). The item and value of each `runsOne` must be spelled: without them `byFacts` leaves the digit part open (its premise has an unknown nothing fixes). Committed (std) | 31 to 17 | 3.6 ms vs 2.3 (`cases`) |
| 17 | `goodStepsSnoc` (AoC 2020 day 18) | **qualifies.** The step is `byFacts [goodStepsSnoc]`, with no names of facts. Committed | 16 to 15 | 19.8 ms vs 2.2 |
| 18 | `part1FromInput` | **qualifies on 3 of 5 days.** Day 6, 12 and 14: `byFacts [part1Correct, parseXxx]` for `part1Correct x (parseXxx input x parsed)`, same lines, the `input`, `parsed` and argument names gone. Day 13 and 15 fail (`E-FACTS`, left parts open: their conclusions are `∃`/record types, finding 1). Committed for days 6, 12, 14 | 4, same | 1 to 3 ms, same order |
| 20 | `countedJoinAll` (AoC 2025 day 8) | **does not.** `byFacts [countedJoinAll, labelledJoin, countedJoin]` is `E-FACTS` with 3 parts open (`Counted` is a record: the goal is split into fields and the lemma, whose conclusion is the whole record, is never tried). Trying `byFacts [labelledJoin]` and `byFacts [countedJoin]` as the two arguments: the same, 5 parts open | | |
| 25 | `insideOf` (rogue) | **a tie.** `cases` already closes it (the review's "`cases` fails on the record" no longer holds on `main`); `byFacts` closes it too, 1.6 ms vs 2.2. Same length, no names to save. Not committed | 2, same | |
| 34 | `doc1Shape` (fmt) | **qualifies, slowly.** 14 lines of arguments become `isEq (plainDefIs …) (byFacts [plainDefShape keyword name colon result colonEq value])`; the theorem goes from 40 lines to 27. It checks in 520 ms against 24 ms by hand (21 times). Not committed (`tools/fmt` is SW-4515's); the edit is the one line above | 40 to 27 | 520 ms vs 24 |
| 37 | `viewsCons` (toy) | **qualifies.** Both arms are `byFacts` (the contradictory arm too). Committed | 10, same | 3.8 ms vs 3.6 |

Row 18's review text does not say which of the seven days' `part1FromInput`
was drawn; the five with a plain "two lemmas chained" shape were tried.

## G3: `Doc/Words.sw`, AoC 2021 day 12, `Reach.sw`

Choices: `crates/elab/src/std/Doc/Words.sw` (59 `Both` and projections, the
most hand-built conjunction proofs in `Doc/`; `Places.sw` has 52);
`aoc/src/Aoc/Year2021/Day12/Proofs/` (187 `Both`, the most of any day);
`games/rogue/src/Rogue/Proofs/Reach.sw`. "Proof lines" are a theorem's
statement and proof, to the next blank line (as `SW-4483/sample.py` counts),
after `stitchwort fmt`.

"Today" is today's tools. In `Words.sw` it found nothing to shorten: the arms
`byFacts` takes are `Both first others => (first, (lemma … others))` and
`eitherUniform _ (…) (…) restUniform restUniform`, and `cases` on them is
`E-CASES-BUDGET` after 64 cases (`rewrite … then cases` is fine only for the
four `(uniform, restUniform)` arms, one line each already). In `Reach.sw`,
`_` for the arguments a type fixes (`joinedTrans level _ (middleOf rooms 1) _
…`, `walkAppend level _ _ _ _ _ …`, a `let` pair for `reachTrans`) took 19
lines. In day 12, `cases` took two (`connectedNamed`'s `Both named.right
named.left`, `withinTwice`'s backward arm).

| File | Now | After today's tools | After `byFacts` | `byFacts` beyond today | Check time: now, today, `byFacts` |
|---|---|---|---|---|---|
| `Doc/Words.sw` | 818 | 818 | 754 | 64 (7.8%) | 1183 ms, same, 1185-1217 ms (1.0x) |
| AoC 2021 day 12 `Proofs/` | 849 | 847 | 842 | 5 (0.6%) | 685-702 ms, 741-750, 703-751 (1.0x of today, 1.06x of now) |
| `Reach.sw` | 344 | 325 | 311 | 14 (4.3%) | 76 ms, 74-76, 90 (1.2x) |
| **All three** | **2011** | **1990** | **1907** | **83 (4.2%)** | |

(Times: sum of the per-theorem totals in `--timings=all`, `--no-cache`, three
runs for the project namespaces; `Words.sw` through `check --std`, two or
three runs.)

**G3 met in aggregate: 4.2% against the 2% bar, with check time within 1.0
to 1.2 times (bar 1.5).** Not met by day 12 alone (0.6%).

What `byFacts` took:

- **`Words.sw`:** the tuple arms of `stackUniformAppend`, `printsUniform`,
  `fillSepsUniform`, `joinLinesUniform`, `headOrUniform` and their `Marked`
  twins, and in `stepUniform` and `stepMarked` every arm that built a
  conjunction from lemmas: `eitherUniform`/`eitherMarked` (4 to 7 lines
  each, now one), `pickUniform`, the `Concat` and `Fill` arms
  (`stackUniformAppend` over `printsUniform`/`joinLinesUniform`/
  `fillSepsUniform`) and the `Choice` arms: `rewrite flat then byFacts
  [stackUniformAppend, printsUniform, joinLinesUniform]`. About 35 edits, all
  of them checked the first time. The 81 theorems' total time is unchanged.
- **`Reach.sw`:** `walkAppend`, `walkEast`, `walkWest`, `walkSouth`,
  `walkNorth` (`rewrite shift then byFacts [walkEast]`, the local `floor`
  fact applied with its two `arithmetic` premises) and `joinedTrans`
  (`byFacts [reachTrans]`, a record goal). `walkAppend` costs 11.8 ms
  against 0.8 and is most of the 1.2x.
- **Day 12:** `withinTwice`'s forward arm (`byFacts` closes the two
  `arithmetic` conjuncts, 13 ms against 7; `cases` fails there after 275 ms),
  `routesFollow`'s two `Both member …` arms, and day 12's `part1FromInput`.
  Everything else in these files is `rewrite` with a local `∀` equation
  (`rewrite same c small then …`), `Decidable.elimProof` and a lemma whose
  conclusion is a record. Whole-body `byFacts [lemmas it calls]` was tried on
  all 30 theorems of day 12's four files and `Reach.sw` that mention `Both`, `.left`, `.right` or
  `Witness` (a script, `E-FACTS` on every one, the failures took 1 to 46 ms).

What was tried and left: `walkWithin`, `reachTrans`, `reachWithin` and
`goalReachable` (the goal is an `∃` or needs a witness `byFacts` won't
invent), `completesCons`/`followsCompletes` arms (record conclusions).

## G4: failing fast

- **Reject examples: met.** Each `examples/reject/facts-*.sw` fails in 0.1
  to 0.3 ms, except `facts-attempt-limit.sw`'s `tooMany` (the attempt limit
  hit on purpose, 512 ways) at **4.0 ms** (3.8 to 4.1 over five runs): under
  the bar, with little room. `facts-keyword-name.sw` is a parse error and
  never reaches `byFacts`.
- **Row 34's arguments with a part removed: not met.** `doc1Shape` with
  `byFacts [plainDefShape …]` and one hypothesis dropped from the statement
  (a scratch copy; reverted): without `nonCloser` 360 ms, without `homed`
  331 ms, without `sound` 286 ms, each `E-FACTS`, against 24 ms for the hand
  proof. (Without `within` it took 13 s, but that is the neighbouring `| _
  => cases` arm, not `byFacts`: `E-CASES-BUDGET`.) The statement has twelve
  hypothesis parts and big goals; the cost is mostly in `byFacts`.
- A worse one, outside the bar's list: `byFacts [completesCons,
  followsCompletes, tracksAgain]` in AoC 2021 day 12's `followsCompletes`
  failed in **25.6 s** (`tracksBig` 0.85 s, `tracksFresh` 0.98 s, the
  `finishWithin` arm 2.5 s), with 16 facts in scope. The same call in the
  right shape succeeds in milliseconds.

## Findings

1. **A fact or lemma whose conclusion is an `∧` or a record is never used,
   even as a whole.** `(mk: r n → p n ∧ q n) (c: r n)` does not prove `p n`,
   `q n` or `p n ∧ q n` by `byFacts [mk]`; `mk: r n → p n ∨ q n` proves
   `p n ∨ q n`. Phase 1 splits the goal into `p n` and `q n`, and
   nothing concludes either. Its cost here: row 20, day 12's
   `completesCons` chain and `followsCompletes` arms, day 13's and 15's
   `part1FromInput`, any lemma ending in `Counted`, `Completes`, `Labelled`,
   `Part1Answer`. Fix: index an `∧` or record conclusion by its parts as
   well as whole (what Lean's `solve_by_elim` does by `apply`ing it).
   Probe: scratch `probe_whole2.sw` in the lane's scratch folder (four
   one-line theorems).
2. **Failing `byFacts` is slow when many facts are in scope** (G4 above:
   290 to 360 ms on row 34's arguments, 25 s on `followsCompletes`). Reject
   examples fail in under 5 ms because they are tiny. Worth a bound on
   facts tried, or on terms built, besides the attempt limit.
3. **`byFacts` unfolds a goal's definition before matching a lemma
   about it.** `part1FromInput` for day 15: the goal `Part1Answer cave n`
   becomes an `∃`, the lemma concluding `Part1Answer …` is not tried
   (same root as 1).
4. **A `runsOne` listed with fewer arguments than its premise needs
   leaves the premise's item unknown** (row 10): fixing it takes spelling
   the item and value, which the hand term also spelled. Not a bug: the
   unknowns rule working; it caps row 10's gain at today's `cases` form.
5. **`cases` found nothing in many arms `byFacts` closes** (`E-CASES-BUDGET`
   after 64 cases, `E-CASES` slowly: 275 ms to 5.4 s). Not a defect but the
   case for G3's "today's tools" baseline being weak on `Both`/lemma code.

## Commits and what was not done

Edits committed: `Doc/Words.sw` (G3), `List/Append.sw` (row 7),
`Parse/RunsOperators.sw` (row 10), AoC 2020 day 18 `Complete.sw` (row 17),
AoC 2021 days 6 and 14 `Parse.sw` (row 18), day 12's `Neighbours.sw`,
`Parts.sw`, `Routes.sw` (G3, and day 12's row 18), `Reach.sw` (G3),
`tools/toyfmt/.../SpellProofs.sw` (row 37). Statements are unchanged and
every namespace checks. Std changed, so the `hash_stability::prelude` snapshot was re-recorded
(29 lines moved, the changed std theorems' hashes). `task test:example
NAME=facts` passes (7 of 7).

Not done: G5 (uptake, no threshold, four weeks on); `tools/fmt` (SW-4515);
row 34's byFacts form is measured but not committed; today's-tools pass on
`Places.sw`, the other `Doc/` candidate; `--expand-facts` was not exercised.

## Working friction

- None that cost real time. One snag: `check --only NS.thm` on a project
  needs the namespace named too, and reports "checked 101 of 126" (it checks
  the theorems the target needs): on `tools/fmt` the first run took 100 s
  cold. A line in the brief ("a cold `tools/fmt` check is about 2 min") would
  have saved a guess.
