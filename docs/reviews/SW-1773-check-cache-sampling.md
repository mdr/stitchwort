# SW-1773: should the check cache's differential sweeps be sampled in daily?

7 Nov 2026. Measured on `lane/SW-1773` (from `main` ba03cbf99), release build,
one test at a time, `STITCHWORT_TIER` set as shown.

## Short answer

The examples sweep is already sampled in daily (every eighth example), and
the two whole-library tests cost about 33 s of one core each. There is little
left to save. The only cut worth offering is the whole-library run without
navigation, which saves about 33 s of CPU and no wall time. Recommendation:
leave as is; the prepared change is optional.

## 1. What each sweep guarantees

All three do the same thing: load a source fresh, then through an empty cache
(cold), then through the cache that run wrote (warm), and require identical
canonical dumps (every declaration, side table, the navigation index when on,
the diagnostics), plus counters (everything cacheable was a hit, nothing
replayed part way).

- **Whole library, no navigation** (`the_whole_library_loads_the_same_from_the_cache`):
  every std file's cache entry, in the configuration the CLI uses. Nothing
  else replays every std file through the cache and compares it with a fresh
  check. It is also what covers a std edit now that the key leaves out std's
  text (SW-1330: "once the check cache's differential test covers a std edit").
- **Whole library with navigation**: the same, plus the navigation tables
  and index in the entries. It compares a superset of the first test's dump.
- **Examples** (`the_cache_changes_nothing_for_the_examples`): project and
  single-file sources of every shape (accepted and rejected, soundness,
  extract, project namespaces), with navigation. This is the only place
  project-namespace entries (stage 2) are compared across a wide corpus.

Bugs they caught (board and git):
- SW-1072: an example (`derive-ord-own-deceq`) panicked on the cache round
  trip with navigation; the examples sweep found it in the full run. Its
  regression test (`the_cache_changes_nothing_for_derive_ord_own_deceq`)
  now runs in every tier.
- SW-1156 (glue missing from the key) and SW-1768 (`no_eta` not saved) each
  got a dedicated warm/cold test; the sweeps are what showed the dump must
  carry the field.
- SW-1128, SW-1135, SW-1140 (tables the cache dropped): the differential
  could not see them because the dump had the same gap. Found by review, and
  fixed by adding the tables to the dump. That is a limit of the sweeps, and
  sampling does not change it.
- SW-1354 (a namespace's result depended on unrelated loads) was found by an
  Opus review, not a sweep.

Most cache bugs since then have been found by review and then given a
targeted test; the sweeps' own catches are few and one was found only in
the full tier.

Other tests that compare fresh with something replayed:
- `rewind.rs` (SW-1770: rewind to a mark and recheck equals fresh, per
  namespace and after cancel): same dump, but rewinding, not the cache.
- The lsp tests (`features.rs`): navigation and diagnostics through a cached
  session (`cached_memory`), compared on what the editor sees.
- `hash_stability`, `std_library` (the daily sweeps replay std from the test
  cache and check results against checking from source for a few files).
- The targeted `the_cache_*` tests in check_cache.rs (opaque, extensions,
  defaults, tailrec, glue, derive-ord): fixed cases, every tier.
None of them compares every std file's cold and warm entries.

## 2. Cost now

Machine was busy (load average 13 to 27 at the starts), so the wall times
are noisy; the CPU is steadier.

| Test | Tier | Wall | CPU (user) |
|---|---|---|---|
| whole library, no nav | daily | 35 s | 34 s |
| whole library, no nav | full | 32 s | 34 s |
| whole library, with nav | daily | 30 s | 32 s |
| whole library, with nav | full | 31 s | 33 s |
| examples | daily (1 in 8) | 57 s | 250 s (4.3 cores) |
| examples | full (all) | 381 s | 1920 s |

So the "about 70 s" for the library is two tests of about 33 s, run side by
side (they were 55 s wall together with the examples sweep, which is the
longest of the three). The "92 s" for the examples no longer holds: daily
already takes 57 s wall, 250 s CPU. The library tests are single-threaded and
don't change with the tier.

## 3. Options

| Option | Saves (daily) | Misses |
|---|---|---|
| A. Leave as is | 0 | nothing new |
| B. Whole library without nav only in full (prepared) | 33 s CPU, no wall (it runs beside the others) | A bug that shows only without navigation. The nav test compares the same dump plus the index, so only an entry written without nav differing from a fresh no-nav run. Targeted tests and the CLI paths still cover no-nav use. The merge tier loses it too (it is skipped outside full). |
| C. Examples a quarter as often (stride 32 in daily; today's stride is 8) | about 190 s CPU, about 40 s wall | Project and file shapes in 3 of 4 samples now taken; rare-shape bugs like SW-1072 wait for the full tier |
| D. Examples to stride 4 ("a quarter of examples", more than today) | adds about 250 s CPU | Nothing; more cost |
| E. Drop the whole-library tests from daily altogether | 66 s CPU, no wall | A std edit that breaks replay of some file only shows in full; SW-1330 made this the cover for std edits. Not recommended. |

Note the ticket's wording "sample a quarter of examples" is already
exceeded: the sample is an eighth. If a quarter was meant as "four times less"
that is option C.

## 4. Prepared change (option B)

Commit on `lane/SW-1773`: `the_whole_library_loads_the_same_from_the_cache`
returns early unless `full_tier(...)`. Ran once: daily, the nav test passes
and the no-nav one is skipped (0.07 s); full, the no-nav one passes
(33 s). fmt checked. If Matt prefers A, merge the doc only (revert the one-test hunk in check_cache.rs).

## D2571

D2571: keep the check cache's differential sweeps as they are in daily?
[rec: yes, leave as is.] The examples sweep is already an eighth, and the
whole-library tests are 33 s CPU each, run side by side with it, so the
best cut (option B, in the prepared commit) saves about 33 s CPU and no wall
time, for a small loss of cover. Say B (merge the commit) or C (stride 32) if
CPU on the shared machine matters more than that cover.
