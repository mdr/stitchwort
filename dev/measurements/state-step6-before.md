# Step 6, "before" measurements (SW-1172, elaborator-state.md section 4.8.7)

- Commit measured: `3706f183` (= main `be6cd930` plus only the measuring tools; no step 6 code). Release build.
- Run: 22:00-22:31 GMT, 3 Nov 2026, 31 minutes, `dev/measure-state state-step6-before`. Raw log: `state-step6-before.raw.md`.
- Load averages (1/5/15 min): start 34.1/17.7/15.4; after the aoc loop 28.0/25.6/22.5; after the rogue loop 4.6/13.9/19.2; end 5.1/7.7/13.8. Another lane was building during the aoc loop, so its latencies and RSS are noisy; the CLI and rewind runs were on a quiet machine (load 3-5).
- Cycles: aoc 10 early / 100 middle / 300 late (as briefed; 410 changes); rogue 50 / 150 / 250 (450). One cycle is one `didChange` (alternately a new `def stateLoopProbe` appended, and the file as it was); the edit and the undo are reported separately.

## Language server memory

RSS is the whole test process (client and server), which includes memory the allocator holds after freeing; heap is live bytes from the counting allocator.

| Project | after first check (cycle 10) | peak sampled | at end | heap after first check | heap at end |
|---|---|---|---|---|---|
| aoc | 1.82 GB | 2.35 GB | 0.69 GB (cycle 410) | 363 MB | 408 MB |
| rogue | 1.74 GB | 2.00 GB | 1.94 GB (cycle 450) | 319 MB | 334 MB |

- Live heap is flat: aoc 363 to 371 MB over cycles 10-110, then 402-408 MB for cycles 200-410 (one step up when the loop moved to the late file, not growth); rogue 333 MB from cycle 100 to 450, constant to within 0.1%. So heap bytes stabilise.
- RSS does not track heap. It wanders between 1.2 and 2.35 GB on aoc, and fell to 0.6 GB at cycle 360 with the heap unchanged: the OS reclaiming pages of a process under load (load was 25-35). RSS is not a reliable criterion on a loaded machine; heap is.
- The first-check figure is not in the log: see "Caveats".

## Edit latency (didChange to publishDiagnostics)

| File (position) | edit median | edit p95 | undo median | undo p95 |
|---|---|---|---|---|
| aoc `Aoc/Common/Range.sw` (early; n=5+5) | 769 ms | 28.3 s (includes the first check) | 1070 ms | 1592 ms |
| aoc `Year2024/Day10/Day10.sw` (middle; n=50+50) | 317 ms | 422 ms | 299 ms | 393 ms |
| aoc `Year2025/Day09/Proofs/Part2.sw` (late; n=150+150) | 2091 ms | 6400 ms | 256 ms | 874 ms |
| rogue `Rogue/Model.sw` (early; 25+25) | 775 ms | 1655 ms | 3182 ms | 5808 ms |
| rogue `Rogue/Proofs/Loop.sw` (middle; 75+75) | 2240 ms | 5730 ms | 301 ms | 563 ms |
| rogue `Rogue/Tests/PlayThrough.sw` (late; 125+125) | 1315 ms | 1351 ms | 135 ms | 139 ms |

The aoc early-file p95 is five edits plus the first check; its median is the usable figure. The aoc late-file edit p95 was taken while load was 25-35.
Early edits are not slower than late ones on aoc: the server rechecks the edited namespace and hits the cache for the rest, so the "about a minute for an early edit" in section 4.8.7's budget did not occur. The loop took 14 min on aoc and 9 min on rogue, not the 15-25 minutes budgeted for both.

## Command line, `stitchwort check` on aoc (2 runs each)

| Mode | user CPU s | wall s | peak RSS MB |
|---|---|---|---|
| cold `--no-cache` | 58.52, 58.42 | 59.2, 59.0 | 1535 |
| cold, empty cache folder | 59.66, 59.96 | 60.4, 60.7 | 1570 |
| warm (all hits) | 2.92, 2.87 | 3.3, 3.1 | 669 |
| mixed (Aoc.Year2024.Day10 edited) | 3.09, 3.04 | 3.3, 3.2 | 671 |

Run-to-run spread under 1% on CPU time. Success criterion to hold: cold and warm no more than 2% slower in user CPU (cold 58.5 s, warm 2.9 s here; the warm figure is small, so 2% is about 0.06 s, below the noise of a loaded machine: use the mean of more runs for it).

## Mark and rewind on aoc (`mark_and_rewind_cost`, 2 runs)

| mark | rewind to the mark | rewind to the start |
|---|---|---|
| 1.05, 1.13 ms | 1.43, 1.32 ms | 248, 241 ms |

## Journal statistics

Not measurable: `JournalStats` doesn't exist before 6a. `print_journal_stats` in `crates/cli/tests/lsp.rs` prints a placeholder line, and the script's CLI part already greps `STITCHWORT_TIMINGS` output for lines containing "journal".

## Caveats

- **The first check isn't timed or sampled.** My wait for the first check (open the files, then wait for 20 s of server silence) saw no messages, so the "first check: 0.0 s" line is wrong and the cycle 0 sample was taken while the first check was still running. The first edit's diagnostics only arrive once that check ends, so the cycle 10 sample is after the first check and is the baseline used above. An earlier smoke run measured the first check on aoc at 119 s (under load 9). Fix before the "after" run: wait for the first file's `publishDiagnostics` for each opened file, as `latency_on_aoc` does, with a timeout above 120 s.
- The success criterion "RSS after 300 cycles within 10% of after the first check, and at least 100 MB below today's" cannot be judged from RSS alone on a loaded machine (see above). Heap bytes are the stable figure: for step 6 to hit the 100 MB target, the after-run heap would have to be about 260 MB or less on aoc after the first check.
- Peak heap during the first check isn't recorded (the allocator keeps `LIVE`, and the peak only on the measured thread).
