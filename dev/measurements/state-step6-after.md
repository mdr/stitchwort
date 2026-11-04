# Step 6, "after" measurements (SW-1177, elaborator-state.md section 4.8.7)

- Commit measured: `2987550a` = main `d5a7c3cb` (steps 6a, 6b, 6c merged) plus only the harness changes below. Release build. The "before" is `state-step6-before.md` (commit `3706f183`).
- Run: 00:25-00:51 GMT, 4 Nov 2026, 26 minutes, `dev/measure-state state-step6-after-raw` (raw log: `state-step6-after.raw.md`). Same cycle counts and modes as the before run: aoc 10 early / 100 middle / 300 late (410 cycles), rogue 50 / 150 / 250 (450), CLI 2 runs per mode, mark/rewind 2 runs.
- Load averages (1/5/15 min): start 11.2/8.8/12.4; aoc loop start 10.8/8.8/12.3, end 8.9/13.0/14.2; rogue loop end 3.3/6.2/10.3; CLI part 3.3 to 3.3 (quiet); rewind part 3.3 to 2.7 (quiet); finish 2.7/3.9/7.5. Another lane (SW-1178) was building and testing during the loops, so loop latencies are noisy (load 9-13 against the before run's 25-35 for the aoc loop). The CLI and rewind runs were on a quiet machine, as before's were (load 3-5).
- **Harness changes** (needed for these numbers, and a source change outside the brief's letter): (1) `state_edit_loop` waits for each opened file's `publishDiagnostics` (900 s timeout), times the first check and samples after it as cycle 0; (2) `Options` in `crates/cli/src/lsp.rs` gets a `journal` cell that the server fills with `Elaborator::journal_stats()` after each check, which `print_journal_stats` prints every 10 cycles (the session is private to the server thread, so there was no other path); no elab or driver source changed. `STITCHWORT_TIMINGS` prints no journal lines on the CLI (a command-line check takes no marks, so the journal logs nothing there); not added.
- **First-check figures exist for after only**: the before run's were invalid (harness bug), so "first check" below has no before column.

## Summary of the success criteria (heap terms, per the orchestrator)

| | Criterion | Result | Verdict |
|---|---|---|---|
| (a) | Heap after 300 cycles within 10% of after the first check | aoc: 553.4 MB at cycle 290, 567.5 MB at 300 (the move to the late file), 554.2 MB at 410, against 557.7 MB at cycle 10 (-0.6% at the end; the largest excursion +1.7%). The cycle 0 sample, taken at the end of the first check, is 1265 MB: the end figure is 56% below it. Rogue: 308 MB at cycle 10, 334.9 MB at 450 (+8.7%, one step up at cycle 60 when the loop moved to `Proofs/Loop.sw`, flat after: 334.4 to 334.9 over cycles 60-450) | **Met** (against cycle 10, the baseline the before run used; against cycle 0 the heap fell) |
| (b) | Heap at least 100 MB below before on aoc | before 408 MB at the end (363 MB at cycle 10); after 554 MB at the end (558 MB at cycle 10): **+146 MB (+36%) at the end, +195 MB at cycle 10** | **Not met; heap is higher, not lower** |
| (c) | Edit latency p95 no worse than +10% | Better or equal in all six cells (table below); medians too | **Met** (load noise is in before's favour: after ran at lower load) |
| (d) | CLI cold and warm CPU no slower than 2% | cold `--no-cache` 58.47 to 60.99 s (+4.3%), cold with an empty cache folder 59.81 to 62.20 s (+4.0%); warm 2.895 to 2.645 s (-8.6%), mixed 3.065 to 2.92 s (-4.7%) | **Cold not met (+4%); warm met** |

## Language server memory

Heap is live bytes from the counting allocator; RSS is the whole test process. Cycle 0 is after the first check (new), cycle 10 is what the before run called "after first check".

| Project | | before | after | change |
|---|---|---|---|---|
| aoc | heap, after first check (cycle 0) | not measured | 1265 MB | |
| aoc | heap, cycle 10 | 363 MB | 558 MB | +195 MB |
| aoc | heap, end (cycle 410) | 408 MB | 554 MB | +146 MB (+36%) |
| aoc | RSS, cycle 0 / cycle 10 | not measured / 1.82 GB | 4.02 GB / 4.13 GB | |
| aoc | RSS, peak sampled | 2.35 GB | 4.56 GB | +2.2 GB |
| aoc | RSS, end | 0.69 GB | 4.04 GB | |
| rogue | heap, cycle 0 | not measured | 338 MB | |
| rogue | heap, cycle 10 | 319 MB | 308 MB | -11 MB |
| rogue | heap, end (cycle 450) | 334 MB | 335 MB | +1 MB |
| rogue | RSS, cycle 10 / peak / end | 1.74 / 2.00 / 1.94 GB | 1.74 / 2.10 / 1.84 GB | about the same |

- **Heap stabilises** on both projects: aoc is 553-562 MB for cycles 10-410 apart from transients of up to +20 MB while the late file is being rechecked; rogue 308 MB at cycles 10-50, then 334-335 MB from cycle 60 (the loop moved to a larger file, as before).
- **The aoc first check leaves 1265 MB live**, 700 MB more than the steady state: the first rewind (cycle 1) frees it. Open checkpoints at cycle 0 are 208 (one per namespace, held until the first rewind to an older mark drops them), and the journal holds 322k entries (27 MB). So between the first check and the first edit, the server holds about 2.3x its steady-state heap. Before had no such measure, so it's unknown whether the peak is new.
- **aoc heap is 146-195 MB higher than before**, and the journal accounts for only about 27 MB of it (`bytes_held`, which doesn't shrink: see below). The rest isn't attributed. Step 6 changed what is held per namespace (6b: the scope's maps, `instances`, `helper_keys` and the copied maps are logged instead of copied; 6c: cache entries from write-sets), and these should have reduced it, so the increase is a finding to investigate, not an expectation met. Rogue's end heap is level (335 vs 334 MB), so what grows is specific to aoc's size (208 namespaces, library files).
- **RSS is not comparable**: it is 2x higher on aoc (4.0-4.56 GB against 1.2-2.35 GB), consistent with the 1.27 GB heap at cycle 0 whose pages the allocator keeps, and the machine's load was much lower here (9-13 against 25-35), so the OS reclaimed little. RSS didn't fall after the first rewind. Not used for a verdict.

## Edit latency (didChange to publishDiagnostics)

| File (position) | before edit med / p95 | after edit med / p95 | before undo med / p95 | after undo med / p95 |
|---|---|---|---|---|
| aoc `Aoc/Common/Range.sw` (early; 5+5) | 769 ms / 28.3 s (included the first check) | 282 / 461 ms | 1070 / 1592 ms | 222 / 236 ms |
| aoc `Year2024/Day10/Day10.sw` (middle; 50+50) | 317 / 422 ms | 239 / 257 ms | 299 / 393 ms | 230 / 248 ms |
| aoc `Year2025/Day09/Proofs/Part2.sw` (late; 150+150) | 2091 / 6400 ms | 1928 / 3469 ms | 256 / 874 ms | 226 / 393 ms |
| rogue `Rogue/Model.sw` (early; 25+25) | 775 / 1655 ms | 467 / 474 ms | 3182 / 5808 ms | 144 / 152 ms |
| rogue `Rogue/Proofs/Loop.sw` (middle; 75+75) | 2240 / 5730 ms | 2150 / 2247 ms | 301 / 563 ms | 196 / 205 ms |
| rogue `Rogue/Tests/PlayThrough.sw` (late; 125+125) | 1315 / 1351 ms | 1326 / 1333 ms | 135 / 139 ms | 134 / 143 ms |

Every cell is at or below before's; the large gains are mostly where before ran at load 25-35 (aoc late file, rogue early and middle) or included the first check (aoc early edit p95), so they say "no worse", not "much better". The cells that were quiet in both (rogue `PlayThrough.sw`, aoc middle) are level to 25% better. The first check on aoc took 201 s here (34 s to the late file's diagnostics, the rest at 201 s) at load 11; on rogue 22 s at load 9. An earlier smoke of before's harness saw 119 s on aoc at load 9, so the first check may be slower after step 6 (journaling every namespace with 208 open checkpoints), or just noisier: one run each, not a verdict.

## Command line, `stitchwort check` on aoc (2 runs each)

| Mode | before user CPU s | after user CPU s | change | wall s before / after | peak RSS MB before / after |
|---|---|---|---|---|---|
| cold `--no-cache` | 58.52, 58.42 (58.47) | 61.01, 60.96 (60.99) | **+4.3%** | 59.1 / 61.9 | 1535 / 1536 |
| cold, empty cache folder | 59.66, 59.96 (59.81) | 62.21, 62.19 (62.20) | **+4.0%** | 60.6 / 63.2 | 1570 / 1569 |
| warm (all hits) | 2.92, 2.87 (2.895) | 2.65, 2.64 (2.645) | -8.6% | 3.2 / 2.78 | 669 / 669 |
| mixed (Aoc.Year2024.Day10 edited) | 3.09, 3.04 (3.065) | 2.91, 2.93 (2.92) | -4.7% | 3.25 / 3.1 | 671 / 671 |

Run-to-run spread is again under 0.1% within the after run, and the machine was quiet for both, so +4% on cold is probably real, not load. The cold check takes no marks, so the journal logs nothing there; what costs on a cold run is outside the journal (ownership tagging at unit changes in 6a, the write-set bookkeeping, or machine drift between 22:00 and 00:45 on 3-4 Nov, which can't be told apart from two runs). Both built with the same release profile, but the before and after binaries ran hours apart. Next step, if it matters: build `3706f183` and the after commit side by side and alternate 4 cold runs each.

## Mark and rewind on aoc (`mark_and_rewind_cost`, 2 runs)

| | before | after |
|---|---|---|
| mark | 1.05, 1.13 ms | 0.25, 0.23 ms |
| rewind to the mark | 1.43, 1.32 ms | 0.29, 0.24 ms |
| rewind to the start | 248, 241 ms | 237, 249 ms |
| ten marks (new) | | 1.61-1.74 ms, resident set 19-21 MB more (1.9-2.1 MB a mark) |

The mark is 4-5x cheaper (a checkpoint, not `touched`'s O(capacity) scan); the rewind to the start is level.

## Journal statistics (`JournalStats`, from the language server, every 10 cycles; full lines in the raw log)

aoc:

| cycle | entries | peak_entries | held | bytes_held | distinct_keys | open | rewinds | undone | checkpoints | transactions |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 (after the first check) | 580,346 | 322,334 | 322,334 | 26,975,232 | 322,313 | 208 | 1 | 0 | 208 | 273 |
| 10 | 608,792 | 322,334 | 8,726 | 26,975,232 | 8,726 | 5 | 20 | 342,054 | 227 | 292 |
| 100 | 661,442 | 322,334 | 9,124 | 26,975,232 | 9,124 | 6 | 199 | 394,306 | 407 | 472 |
| 200 | 1,127,741 | 322,334 | 8,726 | 26,975,232 | 8,726 | 5 | 399 | 861,003 | 616 | 681 |
| 300 | 1,657,944 | 322,334 | 27,319 | 26,975,232 | 27,317 | 19 | 599 | 1,372,613 | 840 | 905 |
| 410 | 2,282,552 | 322,334 | 8,726 | 26,975,232 | 8,726 | 5 | 817 | 2,015,814 | 1,114 | 1,179 |

rogue: cycle 0: entries 283,166, peak 26,828, held 25,154, bytes 1,863,424, open 4; cycle 450: entries 4,050,411, peak 26,828, held 25,154, open 4, rewinds 635, undone 3,767,245, checkpoints 654, transactions 719.

- **The journal doesn't grow**: held entries and open checkpoints are constant per file (aoc 8.7k / 5 open in the middle; rogue 25k / 4 open) while the cumulative counters grow; peak entries are fixed at the first check's. Open checkpoints are released as designed (6b): 208 after the first check, 5 after the first edit.
- `undone / rewinds` is about 2,470 per rewind on aoc, 5,930 on rogue.
- `bytes_held` never changes (27.0 MB aoc, 1.86 MB rogue) though `held` drops from 322k to 8.7k: it follows the first check's capacity and isn't shrunk. It overstates what the journal holds in steady state by about 25 MB on aoc. A log that gives its capacity back after the first rewind would also account for part of the 195 MB if other vectors behave alike.
- Odd: `held` on aoc jumps to 27k (18-22 open) at some cycles in the late-file phase (300, 310, 330, 340) and returns to 8.7k, with the heap +12-19 MB at those samples: the sample caught a check in progress or its marks not yet released.
