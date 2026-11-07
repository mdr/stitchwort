# The AoC friction gaps: where each one stands, 7 Nov 2026

SW-2121. This checks the ten gaps that
[aoc-friction-synthesis.md](../research/aoc-friction-synthesis.md) §4 ranks
against the board at `3589a4ec7`, today's merges, and
[proposals/README.md](../proposals/README.md). Read only. The day counts are
the synthesis's, and they are lower bounds.

## Summary

Of the ten gaps, two are moving: functions with an inner `match`, and
termination (D2870 was answered today, and SW-2096 is in progress). Six have a
plan that is stuck on an open decision: the computed goal (D2610), hung checks
(D2832), `Map` speed (D2595/D2596), generic lemmas (D2831), "the number of"
(D2834) and compute-once (D2880). Two have tickets ready that nobody has
scheduled: built-in bit operations (SW-2010) and the `E-ARITY` note (SW-2012).
Three things have no plan at all: interpreter speed (SW-813 is a ticket with
no design), the "enough fuel finishes" lemma, and a brief for SW-745 (it has
been `next` since 28 Oct with an empty body).

**The next three pieces of work, by AoC impact for the cost:**

1. **Unblock the goal-as-written chain (35+ days).** This is the top gap, and
   since this morning's plan nothing in it has started, because D2610–D2614
   are still open. The digest ranks them its first decision
   ([open-decisions](open-decisions-2026-11-07.md):35). Answering them lets
   three lanes start side by side: 0c (SW-1830), 1c (SW-1831) and `rewrite f`
   (SW-1631). That's about 3¼ h. The whole chain to 6b (SW-1840) is about
   17 h. D2830 matters less than it looks: 1c runs beside 0c and R, off 6a's
   path (stage table, `bounded-readback-remaining.md:353-367`).
   *What it removes from AoC code:* mostly time and wrong turns rather than
   lines. After 6a, rules no longer have to be ordered around a copy
   hidden inside what a call computes to (2024 day 11, 2025 day 1, and
   `std/Nat/Bits.sw:439` from 2021 day 16; `rewrite-occurrence.md:66-68`).
   2025's `calc`s that start at the computed form, with comments explaining
   why, can go (A25:2392 item 3). It also
   covers the 24+ days of goals printed in forms the source lacks (1c,
   stage 5). The cost goes the other way in one place: stage M adds a step to
   seven proofs.
2. **A slow check says what it is computing (17+ days).** Answer D2832 and run
   SW-2009: one Opus lane, 90 min, joining SW-1537, SW-1477 and SW-1534.
   *Removes:* no source lines. It ends bisecting by hand: 2020 day 14 was
   stopped after five minutes, and 2025 day 2 was bisected against a copy of
   the project. Its second half is SW-1788 (waiting on D2568/D2569). That one
   removes 5.5 s of kernel time from two short 2024 day 22 proofs
   (`closed-type-values.md:22-35`) and the proving guide's §6 workaround.
3. **Generic lemmas move out of the days (all 71 days, the most lines).**
   Answer D2831 (a workflow rule, so it costs no lane) and run SW-2003 (Sonnet,
   60 min). *Removes:* lemmas that several days wrote for themselves (std
   review S3), for example:
   - `countFilterMap`, twice (2020 day 11 `Proofs/Sight.sw:17`, 2024 day 14
     `Proofs/Lemmas.sw:19`);
   - a `someMember` for `Set` and one for lists (2020 day 20
     `Monsters.sw:157`, 2024 day 19 `Possible.sw:54`);
   - the `takeWhile` step lemmas (2020 day 10 `Part2.sw:33,35`);
   - `mulNeZero` (2024 day 14 `Lemmas.sw:30`).

   With the rule in place, the next day won't write them again.

**Ready, with no decision needed (for a free slot):** SW-2010, built-in
`Nat` bit operations (Sonnet, 60 min). It's aimed at 2024 day 22's 138 s,
which is mostly `Nat.xor` at 4.3 µs each, and bits hit 7 days. SW-2012, the
`E-ARITY` note (DeepSeek, 30 min, 3 days).

**Worth a design next:** interpreter speed (SW-813), part of 19+ days. It's
the main cost behind `Map` too (`nat-map.md`: about 1,480 instructions per
insert), and it has no plan.

**Calls I made:** D2610–D2614 is ranked ahead of D2832 because it hits twice
as many days, and its first three lanes cost about as much as SW-2009 twice
over. Bits are left out of the top three only because nothing blocks them, so
the orchestrator can schedule them without asking.

## The detail

"Days" is the synthesis's count. "Stuck on" names an open D question, unless
it says otherwise. Statuses are the board's at `3589a4ec7`.

| # | Gap, in one sentence | Days | Done | Planned (tickets, notes, decisions) | No plan yet |
|---|---|---|---|---|---|
| 1 | `rewrite` and `match` act on a goal the checker has computed further than the one written | 35+ | Note `goal-as-written.md` (SW-706); stages 1–4 (SW-1627, SW-1628, SW-1629, SW-1630); bounded readback 0a, 0b, 1, 1b (SW-1740, SW-1747, SW-1746, SW-1748); SW-1782; today SW-2095 (the Proj arm in match's as-written check) | `bounded-readback-remaining.md`: 13 stages, SW-1830–SW-1841 and SW-1631, about 1,015 min; 6a/6b (SW-1839, SW-1840) are 5th and 6th in line. **Stuck on D2610–D2614**, and D2830. None started | SW-1589 (rewrite a hypothesis by its stated type) and the message tickets SW-1478, SW-1570, SW-1511: tickets outside the plan, never scheduled |
| 2 | A slow or hung check runs in silence, so you bisect by hand | 17+ | Timing table; SW-982, SW-1227, SW-1554; SW-1506 and SW-1521 (a parser lemma off by one fails in seconds); SW-1525 (audit read-back cap); SW-1730; note `closed-type-values.md` (SW-1787) | SW-2009, one Opus lane, 90 min (absorbs SW-1537, SW-1477, SW-1534): **stuck on D2832**. SW-1788 (the kernel keeps big closed statements glued): **stuck on D2568/D2569** | SW-1274 (`128 * 8` made 500,000 nodes): a ticket, no diagnosis |
| 3 | Programs run 20–200× slower than Python, worst on `Map` and bit-heavy days | 19+ (bits 7) | Arrays (SW-1637, SW-1638); profiler (SW-1528); SW-1657 (2020 day 15, 31 → 16 s); SW-1636 (2020 day 19, 7.6 → 2.3 s); note `nat-map.md` (SW-1603) | Native `Map`: SW-1824–SW-1827, **stuck on D2595/D2596**, and Matt said "may not get to this for a while". SW-2010 bits: **ready**, unscheduled. SW-1809, SW-1678 (in-place reuse) | **Interpreter speed (SW-813): no design.** SW-1672 (a closure call per `iterate` step), no design |
| 4 | Goals print forms the source doesn't have (`Nat.divFuel`, `f.%match1`) | 24+ | Bounded readback 1 and 1b; SW-1674 (dot calls, `++`); SW-1763 (Float operators); SW-895; SW-93, SW-1429 | SW-1831 (1c) and SW-1836 (stage 5), both in gap 1's plan, so **stuck on D2610** | SW-1004 (`%match` names) and SW-1469 (spreads, `sumBy`): tickets outside any plan. New since the synthesis: SW-2076, SW-2102 (record updates and expected types print unfolded after record eta) |
| 5 | Each day writes the generic lemmas it needs, and std gets them later | 71 | Lemma batches through 6 Nov (SW-1539, SW-1551, SW-1555, SW-1509, SW-1507, SW-1494, SW-1620; SW-1646/SW-1647 took 222 lines out of nine days) | SW-2003 (std lane C, from the std review's S3), plus SW-1577, SW-1468, SW-1493, SW-1531, SW-1588, SW-1215, SW-1467; the rule is **stuck on D2831** | Nothing stops the pattern until D2831 |
| 6 | Proofs can't step through a `match` inside a definition | 13+ | SW-802, SW-1028 (per-arm equations); SW-1538 (a named match's equation transports); SW-1999 note; today SW-2095 | SW-2030 (a match's equation reaches the decrease proof: 2021 day 12, 2024 day 23), **D2870 decided** today; SW-2096 (doing), SW-2097; SW-1073 (`next`) | SW-1263 (`cases` after `rewrite` in an arm); SW-809's leftover (a 100-line theorem takes 16 s) |
| 7 | Termination and fuel cost 45–100 proof lines a day | 15+ | SW-1405, SW-807, partition point, `decreasing` stages; note `decreasing-with-hypothesis.md` (SW-2013) | SW-2029–SW-2032, **D2870 decided** ("just proceed … as planned"), in the order 2029, 2030, 2032; SW-199 (`next`) | **"Enough fuel finishes"** (2020 days 11 and 19, 2024 day 17): SW-1476's title was widened, but there's no design, stage or estimate |
| 8 | `Set`/`Map` aren't tied to a list model, and specs have no "the number of" | 8 | SW-1298, SW-1555, the `↔` forms, `Set.sizePopMin` | SW-745, `next` since 28 Oct, est. 1,000 lines, **stalled: empty body, no brief**. SW-812, **stuck on D2834** | A brief for SW-745 |
| 9 | A value meant to be computed once is recomputed on every call, silently | 6 | Note `compute-once.md` (SW-2014); note `erase-proof-data.md` (SW-2028); SW-1657 | SW-2022–SW-2027, **stuck on D2880–D2885**; SW-2114 ranks it "not yet: the cheap parts now". Ghost data SW-2041–SW-2045 (D2900: park) | None: the plan covers it |
| 10 | You can't rewrite one chosen occurrence, and `E-ARITY` doesn't name the definition that unfolded | 4 and 3 | Note `rewrite-occurrence.md` (SW-2011) | `within`: SW-2033–SW-2035, **stuck on D2860**; the three hidden-copy cases (kind A) need only 6a. `E-ARITY`: SW-2012, **ready**, unscheduled | None |

**Sources.**
- The decisions' status is from
  [open-decisions-2026-11-07.md](open-decisions-2026-11-07.md) (D2610:60,
  D2830:65, D2832:136, D2595/D2596:180-181, D2831:231, D2834:221,
  D2860:205, D2880:187), with D2870's answer as recorded on SW-2029.
- The stage order and its estimates are from
  `bounded-readback-remaining.md` §5.1.
- The feature costs are from
  [parked-language-features.md](parked-language-features.md) (SW-2114).
- The synthesis's §5 items that had no ticket now do, all filed today:
  SW-2009, SW-2010, SW-2012, SW-2015, SW-2016, SW-2017, SW-2006 (`getOr`).
  None has started.
