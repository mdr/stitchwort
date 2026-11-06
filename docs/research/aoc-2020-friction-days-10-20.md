# AoC 2020 friction, days 10 to 20: what recurs and what to do next

A synthesis of the friction notes for 2020 days 10 to 20, written overnight
5 to 6 Nov 2026 (the "Day 10" to "Day 20" sections of
[aoc/NOTES-2020.md](../../aoc/NOTES-2020.md), cited below as `N:line`), and
of the tickets filed from them (SW-1465 to SW-1593). Analysis only (SW-1598,
6 Nov 2026); no code was run. Ticket status is as on the board at
`5cb60a492`. It builds on two earlier reviews:
[aoc-corpus-review.md](aoc-corpus-review.md) (1 Nov: library reuse,
weighted counts, iteration toolkits) and
[language-productivity.md](language-productivity.md) (1 Nov: what to borrow
from other languages).

The eleven days in numbers: 1,378 lines of program, 951 of spec and 4,411
of proofs; between 9 minutes (day 12) and 45 minutes (day 20) from start to
the last theorem. Every day ended with its answers proved to be the spec's,
and from day 13 on, the only answer.

## 1. In plain words

Five changes would remove most of what got in the way:

1. **Let proofs follow the source, not the computed goal.** The problem: a
   `match` or `rewrite` in a proof acts on the goal after it has computed,
   which the source doesn't show, so a step that looks right refines
   nothing or finds nothing, and the error points elsewhere. It hit 10 of
   the 11 days (all but day 17). The cost is detours, not lines: helper
   lemmas written only to dodge it, a program changed to suit a proof (day
   20, whose theorem still takes 2.7 s of the namespace's 3.6 s to check),
   and bisecting with `?`. The change: first, warn when a `match` refines
   nothing (small, two tickets); then a design note on having `rewrite` and
   `match` look at the goal as written before the computed form.
2. **Fast lookups.** The problem: every table is a balanced tree `Map`, at
   about 2 µs a lookup. Day 15 part 2 takes 357 s against Python's 7.2 s,
   so its answer isn't tested by default; day 11 took 42 s as first written
   and still takes 19.3 s after 40 minutes and 81 lines of proof spent
   only on speed; days 17 and 19 are 20 to 35 times slower than Python. And
   nobody can see where the time goes: there is no profiler for running
   programs. The change: the array SW-1473 is designing, and a profiler
   (SW-1528).
3. **Parser completeness on every day.** The problem: on all 19 days from
   day 2 to day 20, the proofs say what a parsed input means but not that
   a well-formed input parses (`N:2526`, `N:4725`, and each day's "Not
   proved"). Day 18 needed it for "the only answer" and paid 370 lines for
   a second parser at first. The overnight `Parse.Runs` lemmas (SW-1563,
   SW-1583) now make it possible for the program's own parser. The change:
   the remaining combinators (SW-1584), then a sweep over the days.
4. **Grid and geometry in Aoc.Common.** The problem: days 11, 12 and 20
   each wrote general geometry from scratch: eight directions and a ray to
   the edge (about 80 lines, day 11), an integer vector with quarter turns
   (40 lines of program and 80 of proof, day 12), and rotating and flipping
   a grid (120 lines of transpose lemmas, day 20). The change: five open
   tickets, two lanes.
5. **Counting by a proposition, and loops that stop.** The problem: "how
   many items satisfy the puzzle's condition" has no std form when the
   condition is a relation (day 19, 25 lines; day 20, 30 more, and it
   imported day 19's proofs to get them), and "repeat until nothing
   changes" or "match with enough fuel" have no library with their lemmas
   (day 11, 60 lines; day 19, about 100 of 337 lines of proof). The change:
   std `NumberWith`/`Kept` (two duplicate tickets), a fuelled
   `iterateUntilStableWithin`, and an `Aoc.Common.Grammar` for day 19's
   kind of matcher.

Much else was fixed overnight: `omega` reads `Ord`'s `≤` and `!=` (SW-1465,
SW-1488), `cases` splits `Int` comparisons (SW-1550), a lemma fits inside
a `match` on a field (SW-1538), a parser off by one literal no longer hangs
the checker (SW-1506), `Parse.chainLeft` (SW-1567), parser completeness
lemmas (SW-1563, SW-1583), the elimination and the Life step in Aoc.Common
(SW-1540, SW-1552), and about a dozen std lemma sets (bits, `zipWith`,
`All2`, `==`, divisibility, `minBy`, sparse sums). Of the 129 tickets
numbered SW-1465 to SW-1593, 61 are done; about 40 of those came from the
days' findings (the rest are the days themselves, and editor and
playground work). The open ones are below.

## 2. Themes

Each theme lists the days that hit it, the cost, its tickets and what the
overnight fixes cover.

### A. The proof acts on the computed goal, which the source doesn't show

The problem, in one sentence: when a goal mentions a definition, the
checker computes it before a `match` or `rewrite` looks, so the term the
proof names may no longer be there, or may be there twice in different
forms.

- Day 10: a `match` on `adapter <= joltage + 3` also refined a copy inside
  the unfolded `canFeed`, so facts stated after it no longer matched; fixed
  by restating the lemma over any sorted table and splitting with `if h:`
  (`N:2540`).
- Day 11: a `match` didn't refine an occurrence that only appeared after
  the goal computed further (E-REFL), and a `match` on `layout.grid.at`
  refined nothing because the goal had computed into `cellAt` (`N:2870`).
  An E-RESOURCE from a `match` on `settle … 1000`, which unfolds 1000
  rounds (`N:2896`).
- Day 12: a `match` whose condition the goal no longer had (`% 90` after a
  break to `% 45`) refined nothing, and the errors were about unsolved
  `?42` and the parser's unfolded run (`N:3128`).
- Day 13: which side of a `+ 1` computes in a `rewrite` is "guesswork
  until the message says"; `Eq.cong` did it (`N:3464`).
- Day 14: one `rewrite` changed the subterm the next looked for, shown
  elided (`N:3692`).
- Day 15: the first `takeTurn` didn't refine under `match below:` because
  the goal had computed `<` into `<=` (`N:3967`).
- Day 16: a helper lemma about `slot` didn't fit inside `match field:
  slot.field`; the workarounds were `rewrite field at passed in passed` or
  a `let` before the `match` (`N:4152`). **Fixed by SW-1538.**
- Day 18: `rewrite shifted` found no `Succ (fuel + steps)` because the
  arm's patterns had computed the goal past it (`N:4779`).
- Day 19: `match found: sequences.map (rules.chainThrough more) |>
  .maximum` refined nothing, as the goal had the lambda eta-expanded
  (`N:5087`).
- Day 20: a hypothesis whose type had computed couldn't be rewritten with
  the rule it was stated with; needed a `memEq` helper, `Eq.trans` chains,
  and a program change for a `rewrite` that hit its budget (`N:5365`).

Earlier days had it too: day 4's `cases` after a `rewrite` (`N:861`), day
5's `rewrite` out of budget on an unfolded left side (`N:1144`), day 8's
`if h:` and day 9's `if a && b` that a proof couldn't follow (`N:2024`,
`N:2257`), and day 9's `omega` atoms compared as written, not as computed
(`N:2278`). This is the most common friction of the track: 14 of 20 days.

**Cost.** Rarely lines; mostly minutes and misdirection. Day 10's was the
only detour that day; day 11's E-RESOURCE needed bisecting with `?`; day
20's needed a helper, a program change and still costs 2.7 s of checking.
The messages help when they name the cause (E-REWRITE-NOTHING's "already
computed past it" and "already refined" were praised on days 11, 13, 16,
19 and 20) and mislead when they don't (day 12).

**Tickets.**

| Ticket | What | Status |
| --- | --- | --- |
| SW-1466 | `omega` note: an atom differs because a `match` refined it | done |
| SW-1538 | match-equation transport for a lemma inside a `match` on a field | done |
| SW-1554, SW-1572 | E-RESOURCE inside a `rewrite` labelled as such | done, but not naming the definition |
| SW-1562 | transport fires only when the scrutinee appears literally | open |
| SW-1485 | warn when `match e:` refines nothing (day 12) | open |
| SW-1575 | warn when `match h: e` refines nothing, show the goal's form or match up to eta (day 19) | open, duplicate of SW-1485 |
| SW-1478 | E-REFL after a `match`: suggest `match e:` and `rewrite e` | open |
| SW-1477 | E-RESOURCE names no definition (match on `settle … 1000`) | open |
| SW-1570 | `rewrite` after a `match` computed the goal past the term: suggest `Eq.trans`/`Eq.cong` | open |
| SW-1511 | `rewrite` found nothing: show the subterm, not `…` | open |
| SW-1589 | rewrite a hypothesis by its stated type (as Lean's `▸`) | open |
| SW-706 | `rewrite` looks for the left side as written first (D1422, from 28 Oct) | open |
| SW-1546 | proving guide: the `rewrite h at h in h` idiom | open |

**What the overnight fixes cover.** SW-1538 removed day 16's case (a
lemma about the scrutinee's owner), and the `omega` and E-REWRITE notes
now say more. The general problem, that the proof's steps work on a form
the reader can't see, is untouched. Two parts are separable: the
**messages** (SW-1485/1575, 1478, 1477, 1570, 1511) are small and would
turn every silent case into a pointed one; the **behaviour** (SW-706,
SW-1589, SW-1562) is a design question about when `rewrite` and `match`
see the goal folded, which touches proof generation and needs a note
(Q1). language-productivity.md §5.1 (generated equations and induction
for the function being proved) is the other half of the same wish: let
the proof's shape be the program's.

### B. Running speed: tables, and no way to see where time goes

- Day 11: 9,000 `Grid.lookup`s a round at about 2 µs each, and
  `Position.around` at 10 µs a call; `main` 42 s as written, 19.3 s after
  precomputing the views (40 minutes, 81 lines of `Plan.sw` proof, only
  for speed); 4.1 s under `--js` (`N:2806`).
- Day 15: 30 million `Map` gets and inserts on a 3.6-million-key tree:
  357 s interpreted, 127 s `--js` (2.2 GB), 84 s native, Python 7.2 s; the
  answer test is `#[ignore]`d and part 2 isn't a Stitchwort test
  (`N:3846`).
- Day 17: 8.4 s against Python's 0.24 s, about 20 µs an `insertWith`
  (`N:4554`); acceptable.
- Day 19: 6.5 s against 0.3 s; a record method that built a `Map` was
  rebuilt on every call and took the run past two minutes (`N:5103`).
- Day 20: 5.9 s (`N:5483`).

Both days 11 and 15 found the split only by timing variants of `main`
(`N:2831`, `N:3873`).

**Tickets.** SW-1473 (persistent array, Opus design note in progress,
D2450), SW-1474 (cheaper `Position.around`, open), SW-1528 (runtime
profiler, open), SW-1576 (guide or lint for a derived table rebuilt per
call, open), SW-1579 (day 19's matcher, open), and from before the track
SW-112 (array type, open, superseded by SW-1473), SW-814 (fused balance
or a `Nat`-keyed `IntMap`, open), SW-1163 (in-place reuse plan,
undecided). Nothing in this theme was fixed overnight. Day 15 wants an
array updated in place (old versions are never read), which is where
SW-1473 meets SW-1163's in-place reuse.

### C. Parser proofs: completeness, and friction in the soundness proofs

- **Completeness.** Every day from 2 to 20 says "Not proved: that every
  well-formed input parses" (`N:1102` to `N:5323`, 19 times). Day 18
  needed it for "a line means one expression": a second, pure parser,
  370 lines, and a test that it agreed with the program's (`N:4747`).
  SW-1563 and SW-1583 added `Parse.Runs` lemmas, and day 18 now proves
  uniqueness about its own parser (466 lines, not fewer, `N:4787`).
- **Soundness friction.** `readsWeaken` over `readsMap` needed both
  implicits named, and the error pointed into `Parse.nat` (day 15,
  `N:3928`); a record built from a pipe defeats `readsMap` even with them
  named (day 16, `N:4243`); a pure `foldLeft` in a `{Parse}` function
  became an effect (day 18, `N:4803`); `readsDone`'s `_` spec wasn't
  worked out after a `let` (day 18, `N:4837`); arms for a theorem whose
  result is `Parse.Reads` need its hidden arrows (day 18, `N:4848`); a
  wrong literal in a parser made the check run for minutes (day 14,
  `N:3678`).
- **What helped**: `readsPickBy`, `readsSepBy1`, `readsMany1`,
  `readsSections` and earlier days' `parseWritten`, copied nearly word for
  word, made most parser proofs a few minutes (days 11, 12, 13, 17, 20).

**Tickets.** Done: SW-1506 and SW-1521 (the hang), SW-1529 (which
implicit failed), SW-1563, SW-1583 (`Runs`), SW-1564 (pure `foldLeft`),
SW-1565 (passing a parser method), SW-1567 (`chainLeft`). Open: SW-1584
(`Runs` for `many1`, `sepBy`, `lines`, `sections` and ten more), SW-1585
(`runsChainLeft` innermost-first), SW-1543 (record of a pipe), SW-1566
(`readsDone`'s `_`; overlaps SW-1316 from day 7), SW-1568 (arms for
`Parse.Reads`), SW-1522 (point at the differing literal), SW-1229
(design note on parser completeness, from 4 Nov, D2345: now largely
overtaken by SW-1563). No ticket proves completeness for the days
themselves (Q2).

### D. Geometry and shared AoC libraries

- Day 11: no eight directions as offsets and no ray to the edge; the
  walk's proof is 70 generic lines, plus `compass` (10) (`N:2835`).
  `countAround` moved to Aoc.Common in the lane.
- Day 12: no `Int` vector with compass headings, quarter turns and
  Manhattan length; `Location` and `Heading` (40 lines) and Turns.sw (81)
  (`N:3106`).
- Day 16: the elimination (145 lines of Eliminate.sw) was generic
  (`N:4231`). **Done: SW-1540.**
- Day 17: the Life step was generic, for day 24 (`N:4576`). **Done:
  SW-1552.**
- Day 19: a grammar matcher with soundness and completeness under a
  checkable "productive" condition, for days 18, 19 and 2015 day 19
  (`N:5077`).
- Day 20: no rotate, flip, orientations, edges or crop; `Grid`'s
  `nonEmpty` proof had to be re-proved for every turned grid, so the day
  didn't use `Grid` at all; 120 of Orientations.sw's 309 lines are
  general transpose and `reverse`/`last` lemmas (`N:5341`). No `Ord
  Position`, so a set of positions is a `Set (List Nat)` (`N:5412`).

**Tickets.** Open: SW-1474 (`around`), SW-1475 (compass, ray), SW-1484
(vector), SW-1587 (orientations), SW-1588 (std transpose lemmas), SW-1592
(`Ord Position`), SW-1574 (grammar), SW-1482 (2021 day 11 onto
`countAround`), SW-1479 (`Grid.zipWith`, with `Result.isErr`). Day 12's
naming question (are compass headings `Direction` or a type of their own,
`N:3124`) is Matt's (Q4).

### E. Counting and filtering by a proposition

- Day 10: part 2's spec counts subsequences that connect; no
  `List.subsequences` or its counting step (`N:2587`); day 1 asked for
  `combinations` (done, SW-1208).
- Day 16: two ways to count, `count` and `occurrences`, with lemmas split
  between them; no "distinct from counts" (`N:4219`; done, SW-1542).
- Day 19: `NumberWith p items answer` and `numberWithCount` (25 lines):
  "how many satisfy `p`" when `p` is a relation (`N:5120`).
- Day 20: the same, imported from day 19's spec and proofs, plus `Kept`
  and `keptFilter` (30 lines) for "the tiles that are corners" (`N:5402`).

**Tickets.** SW-1577 (day 19: count of a proposition, and `List.lookup`
lemmas) and SW-1591 (day 20: filter and count by a proposition), both
open and duplicates; SW-1467 (`subsequences`), open; SW-1542 done.

### F. Loops with fuel, and the lemmas a stopping loop needs

- Day 11: "run until stable" has no measure (seats fill and empty), so
  `settle` has fuel 1000, and Settle.sw is 60 generic lines of sound,
  complete and unique (`N:2857`).
- Day 13 avoided fuel by searching at most `id` periods ahead (`N:3288`).
- Day 19: the matcher needs fuel, and completeness needs a rank for the
  rules, a program to compute it and a proof that it is one: about 100 of
  337 lines (`N:5062`). The note suggests `decreasing` on a measure that
  mentions a hypothesis.
- Day 7 (before the track's second half) had the same "the fuel is
  enough" gap, since fixed with a list pigeonhole (SW-1405).

**Tickets.** SW-1476 (`iterateUntilStableWithin`), SW-1574 (grammar),
SW-1486 (`foldLeftRelate`, `iterateMod`), all open. SW-199 (well-founded
recursion) has no item for a measure that depends on a hypothesis.
aoc-corpus-review.md L4 noted `Nat.iterateUntilStable` exists; it needs a
measure, which day 11's rules don't have, so SW-1476 is new, not a
duplicate.

### G. Std lemma gaps

Most of this theme was done overnight, and fast (7 to 17 minutes a
lane): bits and `zipWith` (day 14, SW-1507, SW-1508), sparse sums and
`getOr` after `insert` (day 14, SW-1509, SW-1510, about 70 lines on the
day), divisibility (day 13, SW-1494), `minBy` (day 13, SW-1495), `All2`
(day 16, SW-1539, about 70 of 600 lines), `==` on lists and records (day
17, SW-1551, 25 lines), `Map.containsFilter` and `Set.countToList`
(SW-1555).

Open: SW-1467 (`subsequences`), SW-1468 (`takeWhile` step, `chainMono`),
SW-1476, SW-1486, SW-1493 (`lcm`, coprimality, Euclid's lemma, a
congruence solver: day 13's sieve proof is 197 lines because the textbook
sieve's "earliest" was out of reach, `N:3371`), SW-1531 (`findIndex`),
SW-1577/1591, SW-1588 (transpose), SW-1559 (generated `T.beqMk`), SW-1560
(D2422 sweep).

### H. Proof tactics: `omega`, `cases`, `ring`

Nearly all fixed overnight: `omega` reads `Ord`'s `≤` and names facts it
can't use (day 10, SW-1465, SW-1472), reads a `!=` in a `Bool` hypothesis
(day 12, SW-1488), and no longer builds a proof that doesn't check (day
15, SW-1526, SW-1532); `cases` keeps `Int` comparisons as atoms (day 17,
22 lines to 1, SW-1550, SW-1573). Open: SW-1496 (`ring`'s message when a
coefficient follows its hypothesis), SW-1515 (`omega`: `m*n` and `n*m` as
one atom), and `omega` after an unnamed `match` comparison (in SW-1478).

### I. Messages and names

Each small, but together on every day:

- **The name `at`** is the target marker of `rewrite … at`, and
  Aoc.Common names positions `at` everywhere: day 11 a parse error
  (`N:2913`), day 20 silently read as a target (`N:5389`); SW-990 (1 Nov)
  reported it first. Tickets SW-1480, SW-1590, part of SW-990.
- **A bracket after a constructor**: `Some { … }`, `Ok { … }`,
  `SetMask { … }` need `Some ({ … })`: days 5, 8, 13 (four times), 14 and
  16 (`N:1216`, `N:2050`, `N:3459`, `N:3717`, `N:4287`). "It costs a
  round trip each time, and the bracketed reading is the only one that
  typechecks." The note is good (SW-828); the rule stands from SW-606. No
  open ticket (Q3).
- **Hiding**: a parameter hiding a function (day 13, SW-1498), a lambda
  parameter hiding a local (day 16, SW-1545).
- **Unknown names without suggestions**: `Char.isAlpha` (day 19, in
  SW-1578), `Text.concat` (day 20, untracked), `(1 ..= 10).toList` (day
  15, untracked).
- **Line breaks**: an interpolation over two lines (SW-1481), a `: T`
  ascription starting a line (SW-1569); a leading `∧` (done, SW-1513).
- **Others open**: `And`'s fields and `n + 1` patterns (SW-1593); a
  `Prop` method after `∧` (done, SW-1541); `Bool != ` read as `≠` (done,
  SW-1553); `rewrite Nat.oneMul` (done, SW-1544); a false E-ABILITY (done,
  SW-1527, SW-1533); goals printing `sumBy` and middle spreads in computed
  form (day 10, SW-1469).

### J. Tooling: doc, test, audit

- `stitchwort doc` doesn't list a record's `T.ext` (day 12) or an `if h:`
  equation's premise (day 13): SW-1487, SW-1497, open.
- `stitchwort test` has no per-test time limit (day 14) and no way to
  mark a slow test (day 15): SW-1512, SW-1530, open.
- The counterexample search hung on a theorem naming turn 30000000 (day
  15): done, SW-1525; the checker's own evaluation of such a statement is
  SW-1534, parked by D2448 (SW-1596).

### K. Records

No record eta (day 17, `N:4563`; day 20, `N:5452`; also day 1 for pairs):
fixed each time by `T.ext` or by matching the record. It is SW-789
(D1426, "kernel record eta or a generated `T.ext`", 1 Nov) and SW-55,
both open. Proof irrelevance stage 1 (SW-93), which D1981 made a
precondition, is done, so SW-789 can be decided (Q5). Related: SW-1487
(`T.ext` implicit), SW-1559 (`T.beqMk`).

## 3. Duplicates, overlaps and untracked findings

### Pairs to merge

| Keep | Merge into it | Why |
| --- | --- | --- |
| SW-1485 | SW-1575 | both: warn when `match e:` refines nothing (1575 adds "show the goal's form, or match up to eta") |
| SW-1577 | SW-1591 | both: count (and filter) by a proposition; 1577's `List.lookup` lemmas could split off |
| SW-1480 | SW-1590, and SW-990 item 3 | the name `at` against `rewrite … at` (1480: rename in Common; 1590: parse or say so) |
| SW-1360 | SW-1556 | `Int` ranges: 1360 is the agreed ranges step 4 (D2409) |
| SW-1473 | SW-112 | the array; SW-112 is the 20 Oct ticket for the same thing |
| SW-1477 | the "not done" parts of SW-1554 and SW-1572 | E-RESOURCE naming the definition whose unfolding blew up |
| SW-1566 | SW-1316 | `readsDone`/`readsThen` with an unsolved `_` spec, reported against `?N` |
| SW-1474 | SW-1475 | not duplicates, but the same Aoc.Common file and proofs: one lane |
| SW-1512 | SW-1530 | the same runner option family: per-test limit and a slow marker |
| SW-1578 | SW-1593 | two bundles of small messages from days 19 and 20; one DeepSeek run |

Overlapping, to plan together rather than merge: SW-706, SW-1589 and
SW-1562 (when `rewrite` and transport see the goal as written; one
design note, Q1), and SW-1570 with SW-1511 (two notes for the same
`rewrite`-found-nothing error). SW-1229's design note on parser
completeness is largely overtaken by SW-1563's `Runs`; close it or
rewrite it as the sweep's plan (Q2).

### Findings with no ticket

1. **Parser completeness on the days.** Nineteen days say "not proved:
   every well-formed input parses"; SW-1584 adds the std lemmas, but no
   ticket proves it for the days (Q2).
2. **`C { … }` for a constructor with one record argument** (days 5, 8,
   13, 14, 16); deliberately not a ticket since SW-606, but the cost
   recurs (Q3).
3. **`decreasing` on a measure that depends on a hypothesis** (day 19,
   `N:5082`): not an item of SW-199.
4. **`getOrElse` on `Option` and `Result`, `getOr` on `Map`** (day 12,
   `N:3206`): a naming split, noted in the SW-1488 correction, no ticket.
5. **A worked example of dynamic programming over a sorted list** in the
   guide (day 10, `N:2644`): the recursion is shorter and provable, and a
   newcomer reaches for a mutable map first.
6. **Unknown-name suggestions** beyond `Char.isAlpha`: `Text.concat`
   (day 20, `N:5436`) and `(1 ..= 10).toList` saying a range is already a
   `List` (day 15, `N:3976`). Add to SW-1578.
7. **`foldLeft`'s mismatch doesn't name `initial`** (day 18, `N:4861`).
8. **"A lemma about a `match` must not write one"** (day 17, `N:4568`):
   a proving-guide note, with `(m.get key).any (p key)` as the named form.
9. **`Grid`'s `nonEmpty` field** has to be re-proved for every turned or
   cropped grid, so day 20 didn't use `Grid` (`N:5345`); belongs in
   SW-1587's scope, which doesn't say so.
10. **Proof follow-ups left open on the days**: day 11's line-of-sight
    bound on a rectangle (`N:2788`), day 19's `productive` on the real
    input (`N:5039`, needs the input parsed in the checker), day 20's
    assembly and monster orientation (`N:5310`). As SW-1426 does for day
    8, these could be one ticket each when wanted; none is a tool gap.
11. **`Nat.andNot`, `setBit`, `clearBit`** (day 14, `N:3643`): SW-1507
    did the `toBits` bridges but not these.

## 4. Recommended order

Small lanes first, so friction drops on the next days (21 to 25) while
the designs are written. Models follow CLAUDE.md: Sonnet for std lemmas,
AoC follow-ups and work near proof generation; DeepSeek for bounded
messages, sweeps and mechanical work; Opus for design notes and anything
that changes what `rewrite` or `match` generate.

**Now: small, independent, parallel.**

1. SW-1485 + SW-1575: warn when a `match` refines nothing. DeepSeek (a
   diagnostic with a clear repro in `N:3128` and `N:5087`), about 30 min.
2. SW-1577 + SW-1591: std count and filter by a proposition, moved from
   days 19 and 20; with SW-1467 (`subsequences`) and SW-1468. Sonnet,
   about 45 min. Needs snap:hashes.
3. SW-1474 + SW-1475, then SW-1484 and SW-1592: Aoc.Common geometry, after
   Q4. Sonnet, two lanes of about 45 min.
4. SW-1476 + SW-1486: std iteration lemmas, moved from days 11 and 12.
   Sonnet, about 40 min.
5. Messages bundle for DeepSeek: SW-1578 + SW-1593 (with the untracked
   item 6), SW-1481, SW-1496, SW-1498, SW-1569; then SW-1480 (rename `at`
   in Aoc.Common) with SW-1590's message, not a syntax change.

**Next: medium.**

6. SW-1584: the remaining `Parse.Runs` lemmas. Sonnet, about 60 min. Then
   a pilot of parser completeness on two days (one line-based, one
   section-based), Sonnet; then a DeepSeek sweep over the rest if Q2 says
   so.
7. SW-1587 + SW-1588: grid orientations and std transpose lemmas, moved
   from day 20 (with the `nonEmpty` question, untracked item 9). Sonnet,
   about 60 min.
8. SW-1528: a profiler for `stitchwort run`. Sonnet if it is a sampling
   of the interpreter's call stack by function name; a short note first
   if it touches the runtime's hot loop. Q6.
9. SW-1493: `lcm`, coprimality, Euclid's lemma and `solveCongruences`.
   Sonnet, about 60 min.
10. SW-1477 (absorbing SW-1554/1572's remainder), SW-1478, SW-1570 +
    SW-1511: the `match`/`rewrite` messages. Sonnet (they read the
    elaborator's refinement state), one lane.
11. SW-1574: Aoc.Common.Grammar, from day 19. Sonnet, about 60 min;
    before 2020 day 19's kind recurs.

**Design notes (Opus).**

12. Proofs that follow the source: SW-706, SW-1589, SW-1562 together
    (Q1). Opus, as it changes what `rewrite` and transport generate.
13. SW-1473's array note is in progress; its implementation, and whether
    day 15 wants in-place update (SW-1163), follow Matt's decisions on it.
14. SW-789, record eta, if Q5 says yes.

### Questions for Matt

- **Q1.** Should Opus write one design note on making `rewrite` and
  `match` work on the goal as written before its computed form (SW-706,
  SW-1589, SW-1562), the most frequent friction of the track (14 of 20
  days)? [rec: yes; run the small warning SW-1485/1575 now, as it doesn't
  wait on the note]
- **Q2.** Should the days prove "every well-formed input parses" (19
  days), now that `Parse.Runs` exists: SW-1584, a two-day pilot, then a
  sweep; and close SW-1229 as overtaken? [rec: yes to SW-1584 and the
  pilot; decide the sweep from the pilot's cost per day]
- **Q3.** Should `Some { … }` mean `Some ({ … })` when the constructor's
  argument is a record, rather than an error with a note? It cost a round
  trip on five days, and the bracketed reading is the only one that
  typechecks. [rec: yes, as a small syntax proposal; the note stays for
  the ambiguous cases]
- **Q4.** Compass headings and the ship's vector (day 12): extend
  Aoc.Common's `Direction` and `Offset`, or add a `Vector` with
  `east`/`north` and its own headings? [rec: a new `Vector` (east/north,
  `Int`) with `quarterLeft`/`quarterRight`/`manhattan`, and headings as
  `Direction` with `turnRight`, which was exactly `Heading.clockwise`]
- **Q5.** Decide SW-789 (D1426) now that proof irrelevance stage 1 is
  done: kernel record eta, or keep the generated `T.ext`? It recurred on
  days 17 and 20. [rec: an Opus design note on kernel eta for records
  with a non-proof field, as D1981 requires]
- **Q6.** Schedule the runtime profiler (SW-1528) now, beside the array
  design? Days 11 and 15 found their hot spots only by timing variants of
  `main`. [rec: yes, Sonnet, after a short scope check of the
  interpreter's dispatch loop]
