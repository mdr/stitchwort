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
