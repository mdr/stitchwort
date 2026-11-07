# AoC friction across every year: what recurs, what's fixed, what to do next

A synthesis of the friction notes for every Advent of Code day outside
2020 days 10 to 20 (SW-1988, 7 Nov 2026), and a check of SW-1598's
findings against the board. Analysis only: nothing was built or run.
Ticket statuses are as on the board at `345675d8b`.

It builds on [aoc-2020-friction-days-10-20.md](aoc-2020-friction-days-10-20.md)
(SW-1598, 6 Nov), cited as S1598, and doesn't repeat its per-day detail.
Sources, cited as `KEY:line`:

| Key | File | Days |
| --- | --- | --- |
| N20 | [aoc/NOTES-2020.md](../../aoc/NOTES-2020.md) | 2020 days 1–9 (days 10–20 are S1598's) |
| N21 | [aoc/NOTES-2021.md](../../aoc/NOTES-2021.md) | 2021 days 1–18 |
| N24 | [aoc/NOTES-2024.md](../../aoc/NOTES-2024.md) | 2024 days 1–24 |
| A25 | [docs/aoc-2025.md](../aoc-2025.md) | 2025 days 1–9 (§9, the per-day "Friction" paragraphs, and "Pain points") |

2025 has no `NOTES-2025.md`. Its days (16 to 24 Oct) came before the
friction-note format, and their friction is in `docs/aoc-2025.md`.

**Method and confidence.** Each day's notes end with a ranked list
("Ranked"). I read all of those, plus every item heading, and the full
text where a ranked item cited a cost. So the day counts below are
**lower bounds**: a friction a day mentioned only in passing may be
missing from its count. I checked a status in the code wherever I call a
gap fixed (file:line given), and on the board otherwise. Where a status
comes from a ticket title alone, I say so. The 2024 notes (27 and 28 Oct)
and the 2021 notes (31 Oct and 1 Nov) predate most of the fixes, so many of
their items are now done. Every theme below says which.

## 1. In plain words

Across 71 days in four years, the same few problems come up again and
again. Five matter most now:

1. **Proof steps act on a goal the reader can't see.** You write
   `rewrite lemma` or `match x:`, and it acts on the goal after the
   checker has computed it further. The term you named may be gone, or
   the branch's goal may differ from the one you wrote. At least **35 of
   71 days** hit this (14 of 2020's 20, 6 of 2021's, 12 of 2024's, 3 of
   2025's). It costs detours more than lines. A goal-as-written epic is
   about halfway through: `rewrite` and `match` now look at the goal as
   written first (SW-706, SW-1628). The rest, `rewrite`, `match` and
   `cases` under one rule (SW-1839, SW-1840), is planned and not started.
2. **A slow or hung check doesn't say what it is computing.** A wrong
   literal in a parser, a `match` on a 1000-round loop, or a 130,000-item
   list in a spec makes the checker run for minutes in silence. Then you
   bisect by hand. It hit at least **17 days**: 2020 day 14 ran five
   minutes and was stopped (N20:3850), and 2024 day 22's spec had to give
   up its `part2` name (N24:7346). The per-declaration timing table exists
   now (`STITCHWORT_TIMINGS`, `crates/cli/tests/tools/timings.rs:1`), but
   only for a check that finishes. Tickets: SW-1537 (say what's still
   being checked), SW-1477 (name the definition), SW-1534 (keep a large
   closed statement folded); all open.
3. **Programs run 20 to 200 times slower than Python.** Map-heavy and
   bit-heavy days are slow: 2020 day 15 took 357 s, 2024 day 22 took
   138 s (4.3 µs per `Nat.xor`, N24:7193) and 2024 day 16 took 10.7 s
   against Python's 0.07 s (N24:5198). That's at least **19 days**.
   Arrays (SW-1637) and the profiler (SW-1528) are done. Native `Map`
   (SW-1824 to SW-1827) and interpreter speed (SW-813) are planned.
   Native bit operations have no ticket of their own; they sit in a day
   bundle (SW-808).
4. **A day writes the generic lemmas it needs, then std gets them
   later.** Nearly every day's notes list missing std lemmas. They were
   fixed quickly, day by day (SW-983, SW-1208, SW-1260, SW-1298 and about
   twenty more). But each day pays first: 2020 day 16 spent most of its
   600 lines of proof on generic list facts (N20:4409). Asking every day's
   lane to move its generic lemmas before it finishes would end the
   pattern (D2831).
5. **Functions with an inner `match` or a `decreasing` measure are hard
   to prove things about.** You can't step a proof through a
   `match found:` inside a definition (2024 day 23, N24:7585), a
   dependent `match` on `queue.min` (2024 day 16), or a lifted `match` in
   a recursive search (2021 day 12, N21:3038). Days worked around it with
   depth bounds, fuel, or programs reshaped to suit the proof. At least
   **13 days** for the `match`, and **15** for termination and fuel.
   Per-arm equations (SW-802) and `Finite` (SW-807) are done. SW-809 (the
   `match found:` case), SW-1073 (`f.induct` gaps), SW-199 (well-founded
   recursion) and SW-1476 (a fuelled loop's lemmas) are open.

What's largely solved since the notes were written: parser proofs
(soundness lemmas, then completeness on all 2020 days, SW-1624 to
SW-1626), shared grid and geometry code (SW-984, SW-992, SW-1484), `+`
computing on either side (SW-787, `docs/proposals/nat-add-recursion.md`),
constructor clashes refuted by `cases` and `()`
(`crates/elab/src/cases.rs:747`), finite enumeration (SW-807), braces
after a constructor (SW-1632), `omega` on `Int` and `||`
(`crates/elab/src/std/Omega/Omega.sw:9`, SW-997), the pigeonhole
principle (SW-1405, `std/Nat/Pigeonhole.sw`), `Set` `↔` forms
(`std/Set/Spec.sw:291-433`), and most of elaboration order (postponement
stages, SW-988, SW-1010). Each of these hit 6 to 23 days and now rarely
appears in new notes.

## 2. SW-1598's findings, one day later

SW-1598 cited 83 tickets. Today 36 are done, 2 are `next` and 45 are in
the backlog.

### Its five headline changes

| # | Finding | Now | Evidence |
| --- | --- | --- | --- |
| 1 | Proofs follow the source, not the computed goal | **In progress.** The design note is merged (`f5b4063ab`). SW-706, SW-1562, SW-1485 and SW-1575 are done. SW-1478, SW-1477, SW-1570, SW-1511 and SW-1589 are open, and so are the bounded-readback stages 6a/6b (SW-1839, SW-1840). | board; epic `goal-as-written` (30 open, 29 done) |
| 2 | Fast lookups and a profiler | **Partly fixed.** The array is done (SW-1473, SW-1637), and so is the profiler (SW-1528). The `Map` speed plan is open (SW-1824 to SW-1827, SW-814), as are 2020 day 15's per-turn costs (SW-1602, SW-1672) and the array copy on pop (SW-1678). | board |
| 3 | Parser completeness on every day | **Fixed.** The pilot SW-1612, then D2497, then the sweeps SW-1624, SW-1625 and SW-1626. Every 2020 day from 2 to 20 has `Runs` proofs. The 2021 and 2024/2025 parser guarantees are open (SW-1649, SW-1020). | `aoc/src/Aoc/Year2020/Day*/Proofs` |
| 4 | Grid and geometry in Aoc.Common | **Partly fixed.** The plane library is done (SW-1484). Open: SW-1474 (`around`), SW-1475 (compass and ray), SW-1587 (orientations), SW-1588 (transpose lemmas), and SW-1592 with its staleness check SW-1618. | board |
| 5 | Counting by a proposition; loops that stop | **Half fixed.** SW-1591 (`Kept`, `NumberWith`) is done. SW-1577 (the `List.lookup` remainder), SW-1467 (`subsequences`), SW-1476 (`iterateUntilStableWithin`) and SW-1486 are open. | board |

### Its questions

| Q | Now |
| --- | --- |
| Q1, a design note on goal as written | Answered and written (`f5b4063ab`); its stages are the epic above |
| Q2, completeness on the days | Answered yes (D2454, D2497), and done |
| Q3, `Some { … }` | Answered by the brace-syntax redesign: the declaration decides (SW-1632, D2481–D2485). A constructor not declared with braces, such as `Ok { … }`, still gets a note, not the bracket hint (2024 day 24, N24:8093 item 7; SW-1663 open) |
| Q4, compass headings | Done in the plane library (SW-1484) |
| Q5, record eta | Decided (SW-789), and being built: stage 1 is SW-1642 (doing) and SW-1667 (review). The epic `record-eta` reports a whole-AoC slowdown being fixed (SW-1829) |
| Q6, the runtime profiler | Done (SW-1528) |

### Its eleven untracked findings

| # | Finding | Now |
| --- | --- | --- |
| 1 | Completeness on the days | Done (sweeps above) |
| 2 | `C { … }` | Done (SW-1632) |
| 3 | `decreasing` on a measure that depends on a hypothesis | **Still untracked.** It recurs in 2021 day 16 (a recursive call's result can't justify the next call's decrease, N21:4173 item 5) and 2024 day 23 (the program carries a proof for its measure, N24:7696 item 7). See §5 |
| 4 | `getOrElse` against `getOr` | **Still untracked.** It recurs in 2024 day 19 (N24:6206 item 8). See §5 |
| 5 | A guide example of dynamic programming over a sorted list | Untracked; seen once only |
| 6 | Unknown-name suggestions | SW-1578, open |
| 7 | `foldLeft`'s mismatch doesn't name `initial` | Untracked; seen once only |
| 8 | Proving-guide note: a lemma about a `match` mustn't write one | Untracked; seen once only |
| 9 | `Grid`'s `nonEmpty` re-proved per turned grid | Not in SW-1587's title. Check its scope when that lane starts |
| 10 | Per-day proof follow-ups | Not tool gaps; SW-1426 (day 8) is the pattern |
| 11 | `Nat.andNot`, `setBit`, `clearBit` | Untracked. `Nat.and`, `or` and `shiftLeft` now exist (`std/Nat/Bits.sw:162,203,247`); fold the rest into the bit-operations ticket in §5 |

## 3. Themes across all the days

Each theme gives the days that hit it (lower bounds; `20`, `21`, `24`,
`25` are the years), the cost, its tickets and its status. The days of
2020 10–20 come from S1598.

### A. The proof acts on the computed goal (35+ days)

You name a term in a `rewrite` or `match`, and the checker looks for it
after computing the goal. In each branch of a `match` the goal has
already moved on.

- **Days.** 20: 4, 5, 7, 8, 9, 10–16, 18–20 (14). 21: 8, 11, 12, 16, 17,
  18 (6). 24: 2, 3, 6, 7, 9, 13, 14, 15, 16, 20, 22, 24 (12). 25: 1, 2, 5
  (3, A25:2392 items 3, 4, 7).
- **Cost.** Mostly time and misdirection. 2024 day 13: a `match` in a
  proof unfolded a concrete spec list into 101 steps, for 25 s of
  checking (N24:3986). 2025's `calc`s had to start at the computed form,
  with comments saying so (A25:2392 item 3). 2021 day 18: one surface
  `if c ≤ x` computed to two different terms (N21:4687 item 5). 2024
  days 2, 3 and 9 each rank "`rewrite` against an unfolded goal" in their
  top three.
- **Tickets.** Epic `goal-as-written`. Done: SW-706, SW-1628, SW-1562,
  SW-1485, SW-1575, SW-1694, SW-1719, and the bounded-readback stages 1
  and 1b. Open: SW-1839 and SW-1840 (rewrite, match and cases under
  D2542), SW-1631, SW-1589, SW-1654, SW-1478, SW-1570, SW-1511, SW-1477,
  SW-1546.
- **Status.** In progress. It's still the most common friction. It
  appeared in S1598's days, after SW-706 landed, so the done stages
  haven't removed it.

### B. Goals and messages printed in a form the source doesn't have (24+ days)

Goals print `==` as `Decidable.toBool (Nat.decEqFrom …)`, `%` as
`Nat.divFuel`, a lifted `match` as `f.%match1`, and two "different"
sides that print the same.

- **Days.** 20: 1, 3, 6, 10, 14 (5). 21: 1, 2, 4, 7, 9, 12, 14, 18 (8).
  24: 1, 2, 4, 8, 13, 14, 15, 17, 22, 23 (10). 25: pain point 4 (1).
- **Cost.** 2024 day 4's "`rfl` errors that print both sides the same"
  cost the most time that day (N24:838). 2024 day 2: "every goal read was
  slower for it" (N24:426 item 2). 2021 day 18: four of five printed
  goals weren't valid source, so `search --at` couldn't read them
  (N21:4689).
- **Tickets.** Bounded readback stages 1 and 1b and the stuck sums
  printed as written (SW-895) are done. So is proof irrelevance (SW-93,
  SW-1429), the cause of the equal-printing sides on 2024 day 8. Open:
  SW-1831 (the remaining output sites), SW-1004 (`%match` names),
  SW-1469 (spreads), SW-980 (a day bundle).
- **Status.** In progress, with the same epic as A.

### C. Elaboration order: holes, lambdas and record literals checked too early (23+ days)

A `_`, a lambda's parameter type or a record literal's type is fixed by
a later argument, but the earlier one is checked first, and the error
shows `?39` or lands on the wrong line.

- **Days.** 20: 5, 7, 15, 16 (4). 21: 1, 4, 5, 8, 10, 12, 13, 14 (8). 24:
  1, 3, 7, 8, 9, 12, 15, 16, 21, 23 (10). 25: §9 item 4 (1).
- **Cost.** 2021 day 12: a count couldn't be proved equal to a list's
  length, so the program listed and counted, 50% slower (N21:3038 item
  2). 2021 day 14: holes surfaced only inside a failing `omega` goal.
- **Tickets.** Mostly done: postponement stages 4 to 7 (SW-986, SW-987,
  SW-988, SW-1010), record literals wait (SW-817), SW-1406, SW-1007.
  Open: SW-1003, SW-1008, SW-1009, SW-1014, SW-859, SW-1316, SW-1543.
- **Status.** Largely fixed. After 1 Nov it appears only in 2020 days 15,
  16 and 18, all parser-lemma cases (SW-1543, SW-1316).

### D. Slow or hung checks that say nothing (17+ days)

The checker computes a large term, from a transparent definition on an
unknown, a big closed list or a wrong literal, for seconds or minutes.
Nothing says which declaration it's on, or what it's unfolding.

- **Days.** 20: 2, 3, 5, 6, 14, 15, 20 (7). 21: 8, 11, 16 (3). 24: 6,
  13, 18, 22, 23 (5). 25: 1, 2 (2).
- **Cost.** 2024 day 6: "a resource blow-up on a plain lemma
  application, with an unprintable error: cost the most time"
  (N24:1302). 2024 day 23: one 100-line theorem took 16 s, and 2 s once
  split (N24:7701). 2021 day 8: a small proof file took minutes
  (N21:1954). 2025 day 2: checking went from 0.5 s to 10 s, found by
  bisecting against a copy of the project (A25:2392 item 8). 2020 day 5:
  a concrete `128 * 8` made a 500,000-node term (SW-1274).
- **Tickets.** Done: the per-declaration timing table, SW-982 (a match
  on a bounded search), SW-1227 (lazy delta in the unifier), SW-1554.
  Open: SW-1537, SW-1477, SW-1534 (`next`), SW-1274, and SW-958 and
  SW-808 (bundles). The kernel conversion comparing large closed
  definitions unfolded (2024 days 18 and 22, 2025 day 2) has no ticket
  of its own; it's an item of SW-808.
- **Status.** Open. The timing table helps once a check finishes, but
  not while one hangs.

### E. Run speed (19+ days)

- **Days.** 20: 11, 15, 17, 19, 20 (5). 21: 9, 11, 15 (3). 24: 3, 11,
  12, 15, 16, 18, 19, 20, 22, and 6 by its timing table (10). 25: §9
  items 8 and 9 (1).
- **Cost.** Answer tests marked `#[ignore]` or tiered: 2020 day 15, and
  2021 day 15's test, a third of the merge tier (N21:3810). Programs
  rewritten for speed: 2020 day 11 spent 40 minutes and 81 lines. 2024
  day 22 took 138 s, mostly in `Nat.xor` (N24:7341 item 1). 2024 day 3's
  parser used 1.2 GB on a 180 KB input (N24:1269).
- **Tickets.** Done: arrays (SW-1637), the profiler (SW-1528), SW-1579,
  `Set.popMin` (`std/Set/Spec.sw:131`). Open: SW-1824 to SW-1827 (native
  `Map`), SW-813 (interpreter), SW-814, SW-1678, SW-1602, SW-1672,
  SW-771 (std Dijkstra and sharing searches). Native bit operations are
  only in SW-808.
- **Status.** Partly fixed. The plan exists; nothing has landed yet for
  `Map`.

### F. Missing generic lemmas, written in the day (every day)

- **Days.** All 71. Typical clusters: list `take`/`drop`/`count`/`filter`
  lemmas; `minimum`/`maximum`; `Set` size; `Text` parsing; `Int` and
  `%`; permutations (2024 day 1).
- **Cost.** It's the most lines of any theme. 2020 day 16: most of 600
  lines (N20:4409). 2020 day 4: 50 lines of text plumbing (N20:1054).
  2024 day 6: 120 lines for a pigeonhole (N24:1304). 2021 day 12 names
  `Bool.toNat b ≤ 1` "now in three days" (N21:3036 item 5).
- **Tickets.** Fixed in batches, usually within a day: SW-983, SW-1208,
  SW-1260, SW-1298, SW-1401, SW-1405, SW-1507 to SW-1510, SW-1539,
  SW-1551, SW-1555. The ones I spot-checked are in std now:
  `List.minimumSome` (`std/List/Lemmas.sw:1540`), `List.startsWith` and
  `isEmpty` (`std/List/Toolkit.sw:310-324`), and the `Set` `↔` forms.
  Open: SW-1467, SW-1468, SW-1493, SW-1531, SW-1577, SW-1588, SW-1215.
- **Status.** Fixed day by day, so the cost moves to the next day rather
  than going away. A process question (D2831).

### G. Termination, fuel and "the fuel is enough" (15+ days)

- **Days.** 20: 7, 8, 11, 19 (4). 21: 3, 12, 16 (3). 24: 2, 6, 9, 12, 16,
  17, 23 (7). 25: day 2's `Nat.digits` fuel (1, A25:1082).
- **Cost.** 2024 day 2: "nested-pattern recursion and its message: cost
  the most time" (N24:428). 2024 day 12 had 45 lines of termination
  lemmas in a 179-line program, and day 16 had 73 in 289 (N24:3622,
  N24:5185). 2020 day 19 had about 100 of its 337 proof lines on fuel.
  2024 day 17's least-A theorem depends on fuel (N24:5548 item 4).
- **Tickets.** Done: the pigeonhole (SW-1405), `Finite` (SW-807), the
  partition point (`std/Nat/PartitionPoint.sw`), and the `decreasing`
  stages. Open: SW-199 (`next`), SW-1476, SW-967 (a bundle). Two
  recurring items are untracked: a measure that uses a hypothesis or an
  earlier call's result (§2, item 3), and a lemma that a fuelled run
  with enough fuel finishes (2020 days 11 and 19, 2024 day 17).
- **Status.** Partly fixed.

### H. Comparisons as `Bool` or `Prop` (16+ days)

`a < b` is a proposition, and a `Bool` where one is expected. `!=` beside
`=` in a statement reads as `≠`. `if` on a comparison decides a `Prop`.
Each form needs a different lemma.

- **Days.** 20: 3, 8, 9, 12 (4). 21: 1, 4, 9, 18 (4). 24: 10, 12, 14,
  18, 19, 21 (6). 25: day 2 and pain point 5 (2).
- **Cost.** Mostly round trips; the messages pointed elsewhere (2024
  day 12, N24:3625 item 2). 2021 day 9: three lemma families for
  three spellings (N21:2189 item 3).
- **Tickets.** Done: a section is a `Bool` where nothing says otherwise
  (SW-930, `docs/syntax.md:1942`), an equation re-read with `Bool` sides
  (SW-944, `docs/syntax.md:1797`), the `!=` warning (SW-1553), SW-1488,
  SW-1694, SW-1719. Open: the note on 2024 day 21's parse error (no
  ticket found).
- **Status.** Largely fixed. The rule left to decide is whether `!=` in
  a statement should ever be read as `≠` (D2833).

### I. A `match` inside a definition blocks proofs about it (13+ days)

- **Days.** 20: 4, 17 (2). 21: 9, 12, 18 (3). 24: 7, 8, 12, 16, 18, 23,
  24 (7). 25: pain point 5 (1).
- **Cost.** 2021 day 12: proofs about the search were "out of reach",
  and a depth bound stood in (N21:3038). 2024 day 23: the note's advice
  didn't help (N24:7585). 2021 day 18 reshaped its program around a named
  helper (N21:4687 item 2).
- **Tickets.** Done: per-arm equations (SW-802, SW-1028), SW-1069,
  SW-1089. Open: SW-809 (`match found:`), SW-1073 (`next`), SW-1263,
  SW-967, SW-980.
- **Status.** Partly fixed.

### J. `search --at` (15 days, nearly all from 2021)

- **Days.** 21: 1, 3, 4, 5, 7, 8, 9, 11, 13, 14, 16, 17, 18 (13). 20: 2,
  4/5 (the cold first search).
- **Cost.** 41 to 71 s per search under load. It closed none of six
  goals on 2021 day 4 (N21:1221 item 3).
- **Tickets.** SW-952, SW-1041, SW-1267, SW-1491, SW-1239 (all open), and
  epic `proof-search`.
- **Status.** Open but quiet. S1598's days use the type search,
  `stitchwort search`, and found lemmas with it (N20:4503, N20:5426),
  but never `--at`. I take that to mean `--at` was dropped, not fixed
  (inferred).

### K. `omega`, `ring` and `cases` coverage (20+ days)

- **Days.** `omega` and `ring`: 20: 5, 9, 10, 12, 13, 15; 21: 6, 7, 17;
  24: 8, 10, 13, 14, 20, 22, 24. `cases`: 20: 4, 17; 21: 2, 3, 5, 6, 9,
  16; 24: 6, 15, 17.
- **Tickets.** Mostly done: SW-997, SW-1465, SW-1488, SW-1526, SW-1550,
  SW-1650, SW-975 (the panic), and constructor clashes
  (`crates/elab/src/cases.rs:747`, from `740993f1f`, 28 Oct). Open:
  SW-1515, SW-1690, SW-1837, SW-1936, SW-1264, SW-1496. `omega` on `% d`
  (2024 day 22) and `Nat.absDiff` (2024 day 20) are items of SW-808 and
  of a day-20 bundle; I didn't check whether they're fixed.
- **Status.** Largely fixed.

### L. Values recomputed on every call (6 days)

A value the program means to compute once, such as a `let` used inside a
lambda's `match` arm, a field read in a closure, or a record method that
builds a `Map`, is computed again on every call, silently.

- **Days.** 20: 15 (SW-1602), 19 (two minutes, S1598). 21: 9 (a
  `Graph`'s `states`, 4× slower, N21:2189), 15 (a field read, 2×,
  N21:3810). 24: 20 (10× slower, N24:6492). 25: day 1 (`run` computed a
  proof field, 4.2 s for 50 lines, A25:889).
- **Tickets.** Per site: SW-1576 (a guide note or lint), SW-1602, and
  SW-960 and SW-973 (bundles). SW-1814 hoists projections. No ticket
  covers the general fix: compute a closure's loop-invariant `let`s and
  field reads once, as captures.
- **Status.** Open, and untracked as a whole (§5).

### M. Names that clash or hide (10+ days)

- **Days.** 20: 8 (a method named like another type's makes `decreasing`
  see mutual recursion), 11, 13, 16, 20 (`at`, hiding). 24: 5 (`test`),
  5 and 7 (parser names against value names), 9 and 11 (ability
  operations in scope without an import), 24 (constructors named `And`
  and `Or`). 25: §9 item 1 (prelude names `add`, `L`, `R`).
- **Tickets.** Done: SW-1590, namespaces. Open: SW-1480, SW-1498,
  SW-1545, and SW-816 (a bundle). `import M as A` was decided against;
  the item form replaces it (`docs/syntax.md:390`). I found no ticket for
  ability operations being in scope without an import (2024 days 9 and
  11), and didn't check whether it's fixed.

### N. Bit operations (7 days)

- **Days.** 20: 5, 14. 21: 3, 16 (`bitsOf` doubles with each bit, 14 s
  of checking, N21:4178). 24: 17, 22, 24.
- **Tickets.** Lemmas done (SW-1507, `std/Nat/Bits.sw`). Runtime
  built-ins are only in SW-808, and so is `Nat.andNot`.
- **Status.** Lemmas done; speed untracked as a ticket of its own (§5).

### O. Sets and maps against a list model, and "the number of" (8 days)

- **Days.** 20: 6, 17. 24: 6, 9, 15, 16, 20, 23.
- **Cost.** 2024 day 9's part 2 is unproved for want of these, estimated
  at about 1,000 lines (SW-745). So are 2024 day 15's box count and
  2024 day 20's cheat count (N24:4754 item 3, N24:6587 item 7).
- **Tickets.** Done: SW-1298, SW-1555, the `↔` forms, `Set.sizePopMin`,
  below/above (`dc2894809`). Open: SW-745 (`next`), SW-812 (`Set.card`
  or the distinct-list idiom, backlog).

### P. Shared code: grids, graphs and parsers (fixed)

- **Grids.** 20: 3, 11, 12, 20. 21: 9, 11, 15. 24: 15, 20 ("nine days
  define their own grid `Position`", N24:6603). Done: SW-984, SW-991,
  SW-992, SW-1484.
- **Graph search.** 20: 7. 21: 9, 15. 24: 16, 18, 20. SW-1445 is done;
  SW-771 is open.
- **Parsers.** 20: 2–20. 21: 10. 24: 3, 5, 13, 17. Done (theme 3 above).
  Open: SW-1649, SW-1020, SW-1585, and 2024 day 3's `findAll` and
  bounded repetition (I didn't check whether they're done).

### Q. Smaller recurring items

- **Records.** Eta: 20: 1, 17, 20; 24: 5, 6; 25: pair eta (A25:693). Being
  built (epic `record-eta`).
- **Rewriting one occurrence only.** 21: 16 (`x/2` rewritten inside
  `x%2`). 24: 4 (the opposite: `_` rewrites one instance), 11. 25: pain
  point 1, where `J` was the only way. Only in SW-758, a bundle.
- **`E-ARITY` when a definition unfolds to a function type.** 24: 11,
  24. 25: day 2 (A25:1135). Only in SW-758 and SW-816.
- **Counterexample-search coverage.** 20: 1, 2, 3, 4, 5. 21: 14, 15, 18.
  24: 10. Done: SW-1210 (`f x = Some y`), `Decidable (List.Distinct xs)`
  (SW-983). Open: SW-1063, SW-1621.
- **Real inputs missing.** 2024 days 11 and 13 to 24 (12 days) run on
  examples only (SW-799, D1436, backlog). That's not a language gap, but
  it's the most repeated line in N24's rankings.

## 4. The top ten open gaps

The ranking weighs how many days a gap hit, what it cost (time lost,
lines, a day left unproved), and how much of it is still open. A gap
that's largely fixed (C, H, K, P) drops out however often it recurred.
Ranking by days alone would put C (23 days) third and P in the top ten,
but those need no new work. Ranking by lines alone would put F first
and A low, though A cost more time than any other.

| # | Gap | Days | Cost | The fix, in a sentence | Ticket |
| --- | --- | --- | --- | --- | --- |
| 1 | Proof steps act on the computed goal (A) | 35+ | Time, misdirection, programs reshaped | Finish the goal-as-written stages, so `rewrite`, `match` and `cases` work on the goal as written before its computed form | SW-1839, SW-1840 (then SW-1589, SW-1631) |
| 2 | Slow or hung checks say nothing (D) | 17+ | Minutes per hang; bisecting by hand; specs reshaped | While a declaration runs long, name it and the definition it's unfolding, and fail at a budget rather than run on | SW-1537 + SW-1477 (one lane); SW-1534 |
| 3 | Run speed of `Map`, bits and the interpreter (E, N) | 19+ | Tests ignored; programs rewritten for speed | Native `Map.Tree` operations, then built-in `Nat` bit operations, then interpreter dispatch | SW-1824–SW-1827; **new** (bit built-ins); SW-813 |
| 4 | Goals print a form the source lacks (B) | 24+ | Every goal read is slower; `search --at` can't parse goals | The remaining folded read-back sites, and `%match` helpers printed by their bodies | SW-1831, SW-1004, SW-1469 |
| 5 | Generic lemmas written in the day (F) | 71 | The most proof lines of any theme | Make "move the day's generic lemmas to std or Aoc.Common" part of every AoC lane's finish | process: D2831 |
| 6 | Proofs can't step through a definition's inner `match` (I) | 13+ | Proofs given up; programs reshaped | Generalise a lifted `match`'s equation proof over its scrutinee, so `rewrite f.eq` and `match` work through it | SW-809, SW-1073 |
| 7 | Termination and fuel (G) | 15+ | 45 to 100 lines a day; "enough fuel" left open | A fuelled-run kit (enough fuel finishes; a fixed point within n), and a `decreasing` measure that may use a hypothesis | SW-1476 (widened); **new** (measure with a hypothesis); SW-199 |
| 8 | Sets and maps against a list model; cardinality (O) | 8 | Three 2024 parts unproved | `Map`/`Set` operations tied to a list model, and one way to say "the number of" | SW-745; SW-812 (D2834) |
| 9 | Values recomputed on every call (L) | 6 | 2× to 60× slower, found only by timing | Compute a closure's loop-invariant `let`s and field reads once, as captures, or warn where that can't be done | **new** (Opus design); absorbs SW-1576, SW-1602 |
| 10 | Rewriting one occurrence, and `E-ARITY` through definitions (Q) | 4 and 3 | `J` by hand; arms that don't match the statement | `rewrite … at` with an occurrence choice, and an `E-ARITY` note naming the definition that unfolded | **new** (split from SW-758) |

## 5. Recurring gaps with no ticket of their own

Each of these hit at least two days. None has a ticket for itself:
either no ticket at all, or only an item inside a day bundle, where it
doesn't get scheduled.

1. **Built-in `Nat` bit operations in the runtime** (`xor`, `and`, `or`,
   the shifts, `andNot`). Hit 2024 days 17, 22 and 24, 2021 day 16, and
   2020 day 14. Today it's an item of SW-808.
2. **Report a declaration that runs long while it runs**, naming the
   definition being unfolded. Hit 17 days. SW-1537 and SW-1477 cover
   it, but as two backlog tickets that have never been scheduled
   together. Not new; they need joining and scheduling.
3. **The kernel's conversion keeps a large closed definition folded**,
   comparing by name before unfolding. Hit 2024 days 18 and 22, 2021
   day 8 and 2025 day 2. Today it's an item of SW-808, and near SW-1534.
4. **Loop-invariant values computed once.** Hit 2020 days 15 and 19,
   2021 days 9 and 15, 2024 day 20 and 2025 day 1. Only per-site tickets
   exist.
5. **A `decreasing` measure that uses a hypothesis or an earlier
   call's result.** Hit 2020 day 19, 2021 day 16 and 2024 day 23. Not an
   item of SW-199.
6. **"Enough fuel finishes"**, a std lemma that plugs a step bound into
   a fuelled run. Hit 2020 days 11 and 19 and 2024 day 17. SW-1476 has
   the fixed-point half only.
7. **Rewriting a chosen occurrence.** Hit 2021 day 16, 2024 days 4 and
   11, and 2025. Today it's an item of SW-758.
8. **An `E-ARITY` note naming the definition that unfolded to a function
   type.** Hit 2024 days 11 and 24 and 2025 day 2. Today it's an item of
   SW-758 and SW-816.
9. **`getOr` against `getOrElse`.** Hit 2020 day 12 and 2024 day 19. One
   name across `Map`, `Option` and `Result`.
10. **Ability operations in scope without an import.** Hit 2024 days 9
    and 11. Check first whether it's still true.
11. **Triage of the old day bundles** (SW-741, SW-745, SW-758, SW-762,
    SW-771, SW-808, SW-809, SW-816, SW-952 to SW-999). Epic `aoc-older`
    lists this as its next step, and no ticket exists. This report has
    already split out items 1, 3, 7 and 8.
12. **Notes housekeeping.** Some "Ranked" lists sit under the wrong
    day. In N24, day 3's list is under day 5 (N24:1264), day 6's is
    under day 5 (N24:1298), and days 4 and 5's are under day 6
    (N24:1633, N24:1651). In N21, day 6's list is under day 7
    (N21:1735). A reader looking for a day's summary finds another day's.

## 6. Questions for Matt

- **D2830.** Should the next goal-as-written work be stages 6a/6b
  (SW-1839, SW-1840), ahead of the remaining read-back sites (SW-1831)?
  [rec: yes. Theme A hits twice as many days as B, and 6a/6b remove the
  "found nothing" and "branch goal isn't what I wrote" cases at their
  source.]
- **D2831.** Should every AoC lane finish by moving the generic lemmas
  it wrote to std or Aoc.Common, with their tests and the snapshot, so
  the next day doesn't rebuild them? [rec: yes. It's the most lines of
  any theme, and the fixes were each 7 to 17 minutes when done
  separately (S1598 §G). A lemma only the day needs stays in the day.]
- **D2832.** Should a check that runs past a budget fail, naming the
  declaration and the definition it was unfolding, rather than run on?
  [rec: yes, as D2543 asks of limits ("limits fail, never choose"). The
  budget's size is an implementation detail for the lane.]
- **D2833.** In a statement, should `a != b` beside `=` keep reading as
  `≠` (today's rule, with SW-1553's warning), or always be the `Bool`?
  [rec: keep today's rule. Since SW-944 and SW-1553 it has recurred only
  as a message issue; changing the meaning would touch every proof that
  uses `≠`.]
- **D2834.** For "the number of …" in specs, should std get a `Set.card`
  with `↔` lemmas, or should the distinct-list idiom be documented as
  the way (SW-812)? [rec: document the idiom now, and add `Set.card` only
  if SW-745's list model wants it. Three days used the idiom
  successfully.]

## 7. Tickets to file

In order. Estimates are the lane's working time. Tests are the targeted
ones a brief would name.

1. **Join SW-1537 and SW-1477 into one lane:** while a declaration runs
   long, say which one it is and what it's unfolding, with a budget that
   fails as D2832 says. Opus (elaborator and kernel limits). 60 min.
   Tests: the E-RESOURCE examples under `examples/reject/`, and
   `task test:one -- timings`.
2. **New: built-in `Nat.xor`, `and`, `or`, `shiftLeft` and `shiftRight`
   in the runtime** (interpreter and JS), bound to the std definitions
   as the other natives are. Split from SW-808. Sonnet. 60 min. Tests:
   extract's `bound_to_the_prelude` tests, the hash snapshot, the 2024
   day 22 answer test (timed, before and after).
3. **New: a rewrite that chooses its occurrence** (`rewrite … at` with
   an occurrence number, or a focus). Split from SW-758. It starts as a
   short design note, since it's tactic syntax. Opus. 45 min for the
   note. Tests: none (note only).
4. **New: an `E-ARITY` note naming the definition that unfolded to a
   function type.** Split from SW-758 and SW-816. DeepSeek, with a repro
   from 2024 day 11. 30 min. Tests: a new reject example and its
   snapshot.
5. **Widen SW-1476 into a fuelled-run kit:** `iterateUntilStableWithin`,
   plus "a run with at least the fuel of an n-step derivation finishes".
   Sonnet. 60 min. Tests: the new lemmas' examples, `snap:hashes`, and
   `hash_stability`.
6. **New: a `decreasing` measure that uses a hypothesis or an earlier
   call's result**, a design item for SW-199's remaining stage 3. Opus.
   45 min for the note. Tests: none (note only).
7. **New: loop-invariant values computed once**, a design note in the
   performance epic, absorbing SW-1576 and SW-1602. Opus. 60 min.
   Tests: none (note only).
8. **New: one name for get-with-default** (`getOr` or `getOrElse`)
   across `Map`, `Option` and `Result`, with the old name a deprecated
   alias. Sonnet (std naming). 30 min. Tests: `snap:hashes`, the prelude
   hash snapshot, and the guide's examples that use either.
9. **New: triage the old day bundles** (SW-741 to SW-816, SW-952 to
   SW-999), as SW-808 was: close what's done, split what's left. This
   report's §3 gives most of the status. Sonnet, no build. 60 min.
   Tests: none.
10. **New: move the misplaced "Ranked" lists in NOTES-2024 (days 3 to
    6) and NOTES-2021 (day 6)** to their days. DeepSeek. 15 min. Tests:
    none.
11. **New, after a check: ability operations in scope without an
    import** (2024 days 9 and 11): reproduce it first, then fix or
    close. Sonnet. 30 min. Tests: a new reject or accept example.

The existing tickets these rank highest, so the orchestrator can
schedule them as they are: SW-1839/SW-1840 (D2830), SW-1824 (`Map` stage
0, the profile), SW-809, SW-745, SW-1831.
