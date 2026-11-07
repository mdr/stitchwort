# Overnight run, 6–7 November 2026

Matt, 6 Nov ~22:25: "focus on optimizing our test suites, our merge gates,
compile times, and that kind of stuff." The orchestrator rereads this file after
compaction and adds to its log.

## Limits

- **Usage (D2555, Matt):** stop automatically at 94% of the weekly allowance
  (`~/.claude/usage.json`, `seven_day.used_percentage`). No new lanes from 90%.
  At the start it was 75% used, 86.5% of the week gone, and it resets on 7 Nov at 21:00.
- **No daily tier** unless Matt agrees (D2556, open: one run at about 6am to
  measure the night's savings).
- **Checks stay short** (D2441). Lanes that time builds or tests run alone, or
  give their numbers with the machine's load noted.
- **Decisions:** the small and medium ones are the orchestrator's, listed in
  the morning. The large ones wait as D questions. D2551–D2554 are kept free
  for SW-1744.

## Focus: the Developer loop speed epic

Until they finish, these keep running: SW-1744 (record eta: trip-journal and the Float
hold), SW-1746 (bounded readback stage 1) and SW-1732/1733 (the slow AoC tests).
After them the Goals as written and Record eta work pauses.

The queue, best value first:

1. SW-1751: profile the merge tier and fix what's slow.
2. SW-1752: affected-test selection for lanes and verifiers.
3. SW-1753 (Opus): a design for caches that survive a compiler change
   (SW-1745); built if the design is clear.
4. SW-1754: compile time after incremental builds (test-profile settings, lld,
   SW-1738); timed alone.
5. SW-1735 (kache) and SW-1742 (mimalloc): measured on a quiet machine.
6. SW-1741 (the std cache filled once per run) and SW-1734 (heavy sweeps
   kept from overlapping).
7. Next slowest daily binaries: rewind, operators, extract, std_library.
8. Only if time is left: SW-1736 (one test binary per crate), and SW-1737 as a plan
   only.

## Morning summary

By epic: what merged, before and after numbers, what's running, what stopped
and why, open D questions, usage.

## Log

- 22:30: plan written; SW-1744, SW-1746 and SW-1732/1733 running.

## Backup queue, so work carries on until 8am (Matt: "make progress all the way through")

Take these in order, once the speed queue above is empty or blocked.

1. **More speed work.**
   - The findings from each speed lane become small fix lanes straight away.
   - The next slowest binaries in tonight's daily run: rewind 807 s, the web
     tests 613 s, extract 544 s, std_library 510 s, check_cache 376 s,
     run_js 332 s, operators 267 s.
   - `test:lane` areas that don't cover what they claim. The lsp features
     gap was SW-1686; look for others.
   - Lane rebuild time on a fresh worktree: kache, and copying a warm
     target folder.
2. **DeepSeek for the mechanical speed work.** SW-1736 (one test binary per
   crate) is mostly moving files. It costs none of the Claude allowance, so it
   stretches the night if usage gets close to 94%. DeepSeek has its own quota and may run out (Matt): if a run fails with a quota or rate error, fall back to GLM, then Sonnet, and write it in the log.
3. **Bounded readback, already approved (D2545):**
   - stage 1b (SW-1748);
   - SW-1743 and the swallowed-error sites;
   - SW-1749, the omega and ring atom comparison;
   - stage 4, and stage 5 (error notes, Sonnet or DeepSeek);
   - R, `rewrite f` (D1433, decided yes), on Opus.

   Only one lane at a time in elab's matching and unify code.
4. **Small fixes from the backlog** (Matt likes them), on Sonnet or
   DeepSeek: diagnostics, docs (SW-1616), std lemmas.
5. **Read-only analysis lanes** if the machine is busy timing things: reviews
   of merged work, syntheses and designs.
- 22:40: Matt: "crack on"; DeepSeek's quota may run out too, so fall back to GLM and then Sonnet.
- 22:31: SW-1744 in (report on main, prototype on its branch); D2551-D2553 left for Matt; SW-1751 started.
- 22:32: SW-1746 (stage 1) built, all its tests passed, 0 decide differences over 187 std decisions; its Opus review SW-1756 started (it hands terms to the kernel). Usage 76%.
- 22:41: Matt delegated D2551-D2553; all decided yes (see SW-1744). SW-1667 is queued to resume.
- 22:49: stage 1 merged, 23/23 on main. Goals as written paused.
- 23:00: SW-1732/1733 merged (web AoC test: its days phase went from ~125 s to ~20 s; aoc_answers runs on the bounded pool, gain not shown under load 40-80); its check is running. SW-1752 is done and waits for the next batch. SW-1667 resumed (Opus) and SW-1753 started (Opus). Lesson: three lanes timing builds and tests at once push the load to 40-80, so timing lanes should run fewer at a time.
- 23:07: SW-1732/1733 checked on main (aoc_answers 174 s, web 169 s); SW-1752 test:affected merged, its own selection 598/598 in 7 s. Verifiers start from test:affected from now on.
- 23:15: SW-1751 merged; merge tier on main passes 1094/1094 with 104 s of tests (153-172 s before). SW-1761 (toward 90 s) started.
- 23:16: SW-1753 note merged; I decided D2560 yes, D2561 yes and D2562 no (listed for the morning). SW-1741 started, with the dev-features fingerprint hole.
- 23:35: SW-1667 merge-ready apart from whole-AoC/roguelike (Matt's OK) and review; SW-1764 (Opus review) started; filed SW-1762, SW-1763.
- 23:54: SW-1741 merged; the scare in its first check was test:selected's 4 GB memguard (SW-1760). SW-1761 merged: merge tier 1094/1094 in 76 s of tests on main, cold. Filed SW-1765.
- 00:01: SW-1764 says merge after one fix (the cache drops no_eta); SW-1768 (Opus) started on lane/SW-1642.
- 00:09: SW-1765 merged (daily examples and hash sweeps cold: 111 s → 48 s), 699/699 on main. SW-1760 started.
- 00:23: SW-1760 merged. Filed SW-1769.
- 00:25: SW-1768 done; record eta is ready to merge once Matt OKs the whole-AoC/roguelike run.
- 01:00: found that SW-1754 had a worktree since 23:48 but no agent (I created the worktree and never launched it); started it now. Lesson: check ListAgents against the board's doing list at each heartbeat. Usage 76%.
- 01:21: SW-1770 merged; the five slow daily binaries now use about half the CPU; 723/723 on main. SW-1771/1772 started.
- 01:26: SW-1734 held in review (merge tier neutral; daily wall unmeasurable under load; wants a quiet daily run). Filed SW-1774. SW-1769 started.
- 01:57: SW-1771/1772 merged (with a threshold fixup of mine), SW-1769 merged (lsp memory tests 1.7 → 0.45 GB). SW-1774's SIGTERMs likely from lane pkills.
- 02:00: SW-1774 merged (dev/stop-mine); lane briefs now forbid pkill. Morning: CLAUDE.md line.
- 02:08: SW-1754 on main (lld). SW-1737 merged: don't split elab (D2563, D2564 mine). SW-1776 started; SW-1777 filed.
- 02:10: SW-1777 merged (analysis: cranelift isn't on the critical path; no change).
- 02:19: SW-1775 merged (84 binaries were reached by no rule; now 6, listed); inventory refreshed on main. Filed SW-1778.
- 02:27: SW-1763 (DeepSeek, 9 min) merged: Float sums print as x + y.
- 02:28: SW-1776 held in review (three edits per new elab unit test vs an unmeasured ~25 s per clean build): D2565 for the morning. SW-1763 merged. SW-1743 started.
- 02:34: SW-1778 merged; merge tier 1148/1148 in 78 s.
- 02:40: measured SW-1776: clean build 164 → 144 s, CPU -134 s. D2565 stands.
- 02:40: SW-1748 (stage 1b, Opus) started. SW-1742 (mimalloc) and SW-1735 (kache) wait for an idle machine: run them when lanes stop (from 90% or near 8am).
- 02:54: SW-1743 not merged: its fix is a choosing cap, against D2543; back to backlog for stage 4. Filed SW-1779.
- 03:07: SW-1767 done on lane/SW-1642.
- 03:21: SW-1736 pilot merged (rt 13 → 3 binaries); SW-1780 (core, DeepSeek) started; SW-1781 filed.
- 03:22: SW-1766 merged (keep accessor calls); D2566 for the morning.
- 03:23: SW-1748 in review: Opus review SW-1784 started; whole AoC needs Matt. Filed SW-1782 (determinism), SW-1783.
- 03:26: SW-1783 merged (the cut keeps the changed crate's tests).
- 03:28: SW-1780 merged (core 21 → 2 binaries); SW-1781 (DeepSeek) started.
- 03:43: SW-1748 merged (stage 1b); 777/777 and hash_stability 9/9 on main.
- 03:47: SW-1779 in review (SW-1786): AoC 18% fewer steps, day 6 proofs 2.9 s → 0.1 s. Filed SW-1787. Inventory refreshed on main (merged binaries).
- 04:02: SW-1779 merged (AoC -18% steps) after SW-1786; 1007/1007 on main.
- 04:02: SW-1787 merged (closed type values proposal; D2568-D2570). SW-1788 filed, waiting on Matt. SW-1782 started.
- 04:29: SW-1781 merged (4 crates' binaries 23 → 8); fixup for rt's state_match. Filed SW-1789 (fmt fuzz case), SW-1790 (cli/driver).
- 04:51: SW-1782 in review (SW-1791): cached unfoldings record their mode; 317 hash moves under instrumentation → 0. Filed SW-1792. AoC dump comparison waits for Matt.
- 05:09: SW-1782 merged (determinism). SW-1789 and SW-1790 merged as a batch: merge tier 1151/1151 on main. Test binaries now ~35.
- 05:11: SW-1793 merged (test:areas retired). Filed SW-1794.
- 05:17: SW-1794 merged; it caught my emptied epic next list (board test 24), fixed.
- 05:33: SW-1773: leave check_cache sweeps as they are (D2571 mine); doc brought to main.
- 05:37: SW-1795 measured, not merged: raising lsp-sessions saves only cold time and eats the memory guard's margin.
- 05:48: SW-1792 merged (bench examples 11 → 2 min). Filed SW-1797 (step counts vary between runs).
- 06:04: SW-1796 merged (lsp tests 228 → 74 s warm). Filed SW-1798 (editor replays std per search request).
- 06:19: SW-1797 diagnosed: dot.rs caches failures by expression address (latent wrong-hit hazard). SW-1800 (Opus) started. Filed SW-1799 (code action panic).
- 06:24: SW-1798 merged (editor completion 480 ms → 1 ms warm); verified.
- 06:36: SW-1799 merged (printer crash on unapplied Succ/Cons).
