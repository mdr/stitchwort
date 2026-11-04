# Step 6, the regressions looked into (SW-1179, elaborator-state.md section 4.8.12)

- Commits: "before" is `3706f183` (no step 6 code), built in a second checkout; "after" is the lane's base `da8a2d8f` (steps 6a-6c and step 7); "fix 1" adds the log and map shrink at a rewind, "fix 2" also empties the dot-call caches at a rewind instead of copying them at each mark. Release builds, the same profile, the same machine, 4 Nov 2026, 00:59-01:31 GMT.
- Load (1/5/min): 2.5-4 for the CLI runs and the 20-cycle loops; 4-17 for the in-process runs (a merge-tier verifier was running on main for part of the time). Heap bytes are counts, not times, so load doesn't change them; for CPU the runs alternated A and B.

## Language server heap, in process (`crates/cli/tests/live_memory.rs`, new)

A `LiveProject` on a copy of `aoc` with a warm check cache, set up as the server sets one up, checked to the end in one thread, then edited as `state_edit_loop` edits (4 cycles on `Aoc/Common/Range.sw`, each checked until its own namespace is, then 4 on `Year2025/Day09/Proofs/Part2.sw`, each checked to the end). Live heap from the counting allocator; one run each (the figures are deterministic to 0.1 MB: the cycles of a file all agree).

| State | before | after | after + fix 1 | after + fix 1 + 2 |
|---|---|---|---|---|
| libraries loaded (base mark) | 210.4 MB | 213.4 MB | 213.4 MB | 213.1 MB |
| first check done (208 marks open) | 1420.1 MB | 1096.7 MB | 1096.7 MB | **922.8 MB** |
| early file edited (2 marks open) | 364.7 MB | 373.0 MB | **346.4 MB** | 346.7 MB |
| late file edited, checked to the end (208 open) | 1251.6 MB | 927.0 MB | 927.2 MB | **872.2 MB** |
| journal `bytes_held`, early file edited | | 26,975,232 | 394,240 | 394,240 |
| time of a late cycle (about 160 namespaces again) | 5.5 s | 5.3 s | 5.2 s | 5.3 s |

JournalStats (after, all columns the same): libraries loaded: entries 258,012 (logged by the library files' cache transactions, dropped at each commit), held 0, open 1; first check: held 322,334, open 208; early file edited: held 2,683, open 2.

## The edit loop, one file open, 20 cycles (`state_edit_loop`, `STATE_LOOP_PLAN=src/Aoc/Common/Range.sw:20`)

The before checkout ran `2987550a`'s harness (the fixed first-check wait) with the journal line stubbed out; the after run is the lane's base, without fixes.

| | before | after |
|---|---|---|
| first diagnostics | 19.3 s | 18.8 s |
| heap, cycle 0 (3 s after; the rest of the first check still running) | 435.8 MB | 402.4 MB |
| heap, cycle 10 | 360.3 MB | 363.4 MB |
| heap, cycle 20 | 360.3 MB | 363.0 MB |
| journal at cycle 10 | | held 2,677, bytes_held 3,374,848, open 2 |

## Command line, `stitchwort check` on a copy of aoc, alternating (user CPU s)

| Mode | before | after | change |
|---|---|---|---|
| cold `--no-cache` (A B A B; after = lane base) | 60.61, 60.92 (60.77) | 60.81, 60.81 (60.81) | +0.07% |
| cold, empty cache folder (B A B A; after = with fixes 1 and 2) | 62.25, 62.21 (62.23) | 61.86, 62.04 (61.95) | -0.4% |

Wall times 61.3-63.2 s. SW-1177's +4% compared this before build's 58.5 s at 22:00 on 3 Nov with the after build's 61.0 s at 00:45: the before build is 60.8 s now.
