# Review of the test suites (SW-2036)

7 November 2026, Opus, by reading only: no build, no test run. Times come
from the tickets named, `target/test-inventory.json` and
`target/test-timings.json` in the main checkout (the fastest of each test's
last five runs, mostly from the daily run of 6 Nov 21:45, whose load isn't
recorded), `target/nextest/daily/junit.xml` and `dev/selector-log.tsv`. Read
the absolute numbers as "under some load". Compare them with each other.

## Summary

The suites are strong where it matters most. The kernel is tested on
hand-built terms and by fuzzing. Soundness fuzzing mutates real theorems and
looks for counterexamples. Almost every second implementation is checked
against the first: cache against fresh, rewound against fresh, lazy against
eager, machine against reference, JS against reference, native against
machine. The tier machinery is careful too: profiles generated from one
source, the selector's rules tested, memory caps, the order of long tests,
and a test std cache that one process fills. No finding here is a test that
lets a false theorem through.

The weaknesses are of three kinds:

- **Coverage.** Most of today's review findings would be caught by no test.
  The gaps cluster at the edges again: input shapes nobody generates,
  panics nobody injects, the undo nobody reaches, and every production
  setting the tests switch off. The counterexample search's clock is one;
  the distributed feature set is another.
- **Time.** The daily tier is about five times its budget. Its corpus-sweep
  group alone sets a floor of about 16 minutes on the 6 Nov run, so trimming
  can't bring it back to 5 minutes. The budget needs restating, and the
  trimming should go where checks overlap.
- **Wall-clock oracles.** A handful of tests decide pass or fail by how far
  a timed search got, or by a sleep. The two fixed flaky tests (SW-1168,
  SW-1224) were this kind, and the same pattern is still in the daily tier.

**Top five recommendations:**

1. **Restate the daily budget, then cut its overlaps** (D2910). Four tests
   check the whole AoC project from cold: the web test (417 s),
   `lsp::aoc_navigation_matches_check_index` (290 s), `aoc_answers`' whole
   check (160 s) and `search_at_aoc` (195 s). Give the web and LSP tests a
   sample of namespaces outside the full tier. That saves about 550 test-s
   and takes the tier's longest test from 417 s to under 200 s (T1, T2).
2. **Add `terminate-after` to every profile** (kernel-merge-gate ticket 3).
   Today a hang hangs the verifier. The deep-input corpus and the blowup
   tests need it to fail rather than stall (T4).
3. **Remove the wall clock from pass/fail.** The search benchmarks that
   assert hit rates should get a deterministic candidate budget, and the
   LSP cancel test a hook instead of a sleep (T6). Add one test of the timed
   counterexample path users actually get (T7).
4. **Make the sweeps' worker order reproducible** (T5). `par_map_with` hands
   items out by timing, and each worker carries a rewound session from item
   to item. A rewind leak then fails a different example on each run and
   never fails under `EXAMPLES=name`. Hand items out by fixed stripes and
   print a worker's earlier items when it fails.
5. **Check proofs where AoC is "tested" in the fast tiers** (D2912). The
   fixed core's day and the 14 merge days only `run main`. Have the fixed
   core's day check its `Proofs`, and share a library cache across the
   answer tests, which spend most of their 603 test-s re-checking std from
   source (T3, T9).

**Counts:** 0 high, 9 medium, 8 low.

## 1. What each tier runs

| Tier | Command | What it runs | Size and time | Risks it covers | What it can't see |
|---|---|---|---|---|---|
| lane | `task test:lane AREA=…` | `[profile.lane-AREA]`: 18 areas, a handful of tests each; corpus sweeps at a quarter of the daily sample (`STITCHWORT_TIER=lane`) | 2-12 s warm each (docs/testing.md table, 25 Oct); `lsp` 25 s cold | The edited area's own invariants: parser, kernel rules, one std slice, one backend | Anything another area owns; AoC proofs; the examples beyond a quarter |
| one | `task test:one -- F` | Tests by name or filterset, at the **daily** sample | Whatever is named | The tests a lane changed | — |
| selected (post-merge verifier, D2441) | `task test:affected -- --range …`, `task test:selected -- '<f>'` | `dev/test-affected.toml` rules, cut to the 90 s budget, plus the fixed core: all of `core` and `syntax` and `aoc_answers::year2024_day04` (`:69-77`); `STITCHWORT_TIER=merge`, the merge profile's settings | 104 logged runs: mean 64 s, 7 s to 332 s; 15 failures (`dev/selector-log.tsv`) | What a diff's paths map to: the changed code's tests first, then what reads it, then crate dependents | Library users reached by dot calls (the rules say so, `docs/testing.md:41`); AoC proofs; anything cut for the budget (it warns) |
| merge | `task test:merge` | Feature check, `cargo fmt --check`, then `[profile.merge]`: the lanes but `goals` and `web`, plus all of `core` and `native`, `hash_stability` and the cli examples on a quarter, 14 AoC answers, the JS snapshots | 1,151 tests, 1,394 test-s; about 110-120 s wall on 10 cores (SW-1090: 1,022 CPU-s at 841%) | A broad smoke test. Since D2441 it is the checkpoint before a push, not per merge | AoC proofs (T3); the daily-only sweeps; the fuzzers but syntax and kernel |
| daily | `task test:daily`, `nix flake check` | `web:pkg` (WebAssembly bundle if stale), fmt, `test:lanes-nonempty` (about 13 s), clippy `--release --all-targets`, `builtins::` in the **debug** profile beside nextest, `[profile.daily]` (all tests, sweeps at the daily sample, 8 threads, pools of 5), release doctests, the board's node tests | 2,185 tests, 9,271 test-s; **1,462 s of nextest wall time** on 6 Nov (`junit.xml`) against a 5-minute budget | Every test; the corpus sweeps on a fixed sample; whole-AoC checks through `check`, the web API and the language server; the elaborator and soundness fuzzers; bench counts | AoC's own `test`s but six days (T3); the full-only tests |
| full | `task test:full` | `[profile.full]` with every sweep over the whole corpus, 9 full-only tests (`full_tier(…)` guards), doctests, `test:verify-cache` (about 3 min) | Tens of minutes; 2 h 5 min on 4 Nov (SW-1175, docs/testing.md:91) | AoC `check_cache`, `rewind`, lazy loading, lowering and the machine on every day; the cached test results against a fresh run | A long-lived check cache against a fresh check (check-cache-trust §5 adds it) |

How the tiers relate: each lane profile is a subset of merge
(`dev/nextest-merge` generates it; `test-affected_test.py` fails when it's
stale), merge is a subset of daily, and daily of full. Most tests are the
same test in every tier; the sweeps scale with `tier_sample`
(`crates/driver/src/driver.rs:198-205`).

## 2. Findings

| # | Severity | Confidence | Where | What | Change (size) |
|---|---|---|---|---|---|
| T1 | medium | high | `.config/nextest.toml:9-17`, docs/testing.md:13 | Daily is about 5× its budget; the corpus-sweeps group alone is a 16-minute floor on the 6 Nov run, so no trimming reaches 5 minutes | Restate the budget from a quiet run (D2910); trim overlaps (T2) (S) |
| T2 | medium | high | `crates/web/src/project.rs:516-560`; `crates/cli/tests/server/lsp.rs` (`aoc_navigation_matches_check_index`) | Four daily tests each check the whole AoC project from cold; the web one (417 s) is the tier's longest test | Web: only the six days' targets; LSP: a sample of namespaces outside full (S-M) |
| T3 | medium | high | `crates/cli/tests/running/aoc_answers.rs:109-121`; `dev/test-affected.toml:76` | AoC proofs are checked by no test below daily; AoC's own `test`s run only in the full tier (but 2025 days 1-6 through the web test) | Fixed core's day: `check` with its `Proofs` (after SW-1915); see the corpus gate (D2912) (S) |
| T4 | medium | high | `.config/nextest.toml:33,42,53,75` | No `terminate-after`: a hang holds the verifier or a tier until someone stops it (kernel-merge-gate §8) | As kernel-merge-gate ticket 3; daily and full too (S) |
| T5 | medium | medium | `crates/driver/src/driver.rs:107-137` | `par_map_with` workers claim items by timing and keep a rewound session between items: a rewind leak fails different items on different runs, and never alone | Static stripes; on a failure, print the worker's earlier items (S) |
| T6 | medium | medium | `crates/driver/tests/search_at_aoc.rs:404,686`; `crates/driver/src/search_at.rs:67`; `crates/cli/tests/server/lsp.rs:1305-1325` | Pass/fail depends on the wall clock: hit-rate floors under the 10 s search deadline on a loaded pool; a sleep of a quarter of a measured check, then "exactly one cancellation" | A candidate or step budget for test searches; a blocking hook for the cancel test (S-M) |
| T7 | medium | high | `.cargo/config.toml` `[env]`; `crates/elab/src/state/options.rs:70-85` | Every test runs with untimed counterexample searches; the timed path users get (200 ms backstop) runs in no test | One test with the variable removed; moot if D2700 makes inputs the bound (S) |
| T8 | medium | high | summary §1-§4 and the crate reviews | Of the review findings, the two highs and most mediums would be caught by no test (§3's table) | The three proposals cover a third; tickets below for the rest (—) |
| T9 | medium | medium | `aoc_answers.rs:144-146` (`--no-cache`) | Every answers test re-checks the library files `main` needs from source: 57 tests, 603 test-s in daily, about 120 CPU-s in merge (SW-1090) | A shared library-only cache under `TestCacheTurn`, as `build` and `run_js` share one (SW-1761) (S-M) |
| T10 | low | high | `crates/cli/tests/running/run_js.rs:313-332`; `crates/driver/tests/projects/rewind.rs:615`; `crates/cli/tests/tools/doc.rs` | Slow tests that check little: 20,000,000 quadratic appends to see one message (58 s); a two-case toy project's rewind test at 155 s; six `doc` tests at about 25 s each in merge | Smaller inputs; measure `rewind`'s; merge keeps two `doc` tests (S each) |
| T11 | low | high | `crates/driver/tests/elaboration/named_arguments.rs:476-496`, `crates/driver/tests/library/fmt_hashes.rs` | Hash sweeps elaborate the original of each example again for a baseline `hash_stability`'s snapshots already hold | Compare with the snapshot where one exists (M) |
| T12 | low | high | `crates/driver/src/driver.rs:184-190` and 9 callers | Full-only tests pass silently elsewhere; a full-profile run with `STITCHWORT_TIER` unset passes all nine vacuously | `tier()` cross-checks `NEXTEST_PROFILE` (S) |
| T13 | low | medium | `Taskfile.yml:244-254`; elab-checking review F3 | SW-1903's premise is partly wrong: the daily debug `builtins::` run loads std from source twice with debug assertions on, so `queue.rs`'s checks do run, on std only | Correct SW-1903; its feature still adds AoC and the examples (—) |
| T14 | low | high | `crates/driver/tests/library/hash_stability.rs:8-9`; insta settings | 531 hash snapshots: an example that stops loading drops out silently, and an orphaned snapshot is never noticed; `hash_stability::projects` (51 s) is merge's second-slowest test | `projects` to daily; a daily orphan check (S) |
| T15 | low | high | `crates/driver/src/driver.rs:198-205` | `tier_sample` always takes items 0, 4, 8, …: three quarters of the examples never run in merge or the verifier, and one new file shifts the sample | Offset from the merge commit's hash in the verifier (D2911) (S) |
| T16 | low | high | `dev/run-selected:30-31` | 6 of the 15 logged failures have no failed test named (fmt, features, build or a memguard kill), and the log can't say which | A `stage` column (S) |
| T17 | low | medium | the test tasks; `.github/workflows/playground.yml:6-8` | Only aarch64-darwin with the dev feature set is ever tested: x86_64 native code, the Linux musl build and the distributed feature set run in no tier; CI is manual (1 Nov §5) | Say so in docs/testing.md; revisit with SW-47 (—) |

## 3. Coverage against today's reviews (T8)

"Caught by" means a test in some tier fails if the bug is there. Known gaps
from the brief are marked *(known)*.

| Risk (ticket) | Caught by a test today? | Why not, and what would |
|---|---|---|
| `"""` lexer panic (SW-1916, high) | No | The syntax fuzzer never generates `"""` or `${…}` *(known, SW-1875)*. Deep-input corpus §6.1 doesn't either: add a block-text shape |
| Checker-thread panic freezes the editor (SW-1948, high) | No | No test injects a panic into the checker thread. SW-1948's fix should come with a hook that panics on a marked file |
| Deep input outside the parser's guard (SW-1874, SW-1936, SW-1892, SW-1895) | No | `nesting.rs` has ten shapes, none of these. The deep-input corpus would catch all five |
| One lexical error drops the file and its importers (SW-1873) | No | No test checks that importers of a file with a lexical error still load |
| Replay undo leaves natives (SW-1925) | No | No test reaches the undo, and the dump omits most of `Builtins` *(known)*. check-cache-trust §4 adds both |
| Custom prelude keys on the standard core (SW-1919) | No | Driver L12. check-cache-trust ticket 2 adds the test |
| Nat natives bound by name and arity (SW-1885) | Partly | `natives.rs` checks the real prelude's natives against their definitions, on small, random and big numbers. A prelude that binds a different body of the same type is refused by nothing; `builtins_with_the_wrong_shape_are_refused` checks shapes only |
| Native code trusts its image (SW-1893) | No | Safe-code misuse, not reachable from a program; a type-level fix (D2711), not a test |
| Dot-call failures replayed (SW-1902, SW-1803) | No | The determinism test SW-1800 wrote, `a_postponed_dot_call_takes_the_same_steps_every_time`, is ignored. Bench `--jobs 8` agrees only to 1 part in 100,000 (docs/testing.md:244), which hides tens of steps |
| A code action replaces the wrong text (SW-1949) | No | `a_document_edited_during_a_search_gets_no_stale_edit` covers a new version, not a range that shifted on the same line |
| JS projection out of an array (SW-1943) | Probably not | The random differential tests reach only the shapes the extraction examples export; none projects an array field (inferred) |
| `Array.replicate` and text growth not charged (SW-1891, SW-1897) | No | No test compares step counts across backends on arrays *(known: no native array tests)* |
| Marks, `restore`, glue and `NO_ETA` not put back (SW-1886, SW-1901) | No | `resources`' `running_out_at_any_point_only_ever_means_no_answer` covers one program's budget semantics, not state left after a caught panic or a failed attempt |
| Counterexample search ends on the clock (SW-1937, D2700) | No, by construction | Tests are untimed (T7) |
| Queue invariants (SW-1903) | Partly | They run once a day, over std only (T13) |
| Unifier against the kernel (SW-1910) | No | Not written |
| `omega`/`ring` swallow internal errors (tactics F1), search's `catch_unwind` (F3) | No | No test injects an internal error under a sub-tactic |
| Failed library file stays `Loaded` (elab-rest F3) | No | Only std's own files are tested, and they all load |
| Unlistable source folder skipped (driver M2) | No | Driver L12 |
| `fmt DIR` follows symlinks and hidden folders (cli F4); `check a b c` keeps every session (F3) | No | No test of either |
| AoC proofs on a kernel branch (record eta) | Daily only | T3; the corpus gate puts it in kernel lanes |
| A hang | No | T4 *(known)* |
| Fuzzing barely reaches the parser (SW-1875) | — | *(known)*; the deep-input corpus takes its deep generators |

What is well covered, for contrast: unsound acceptance (kernel tests and
fuzzing, soundness fuzzing with counterexample search, `examples/soundness`),
evaluator agreement, cache and rewind equivalence on fresh caches, the JS
boundary, resource-limit semantics, the native backend's error exits and
frames.

## 4. Details

### T1. The daily tier can't be trimmed back to 5 minutes

The 6 Nov daily run took 1,462 s of nextest wall time for 2,179 tests. The
inventory gives 9,271 test-s for the daily profile. At 8 threads that is
1,159 s if packed perfectly. The 39 tests in `corpus-sweeps`, two at a
time, sum to 1,914 s, a chain of about 957 s however the rest is packed. The
5-minute budget would need about 7,000 test-s cut (75%), and the sweep
group about 1,300 of its 1,914.

SW-921 (31 Oct) measured 599 s under load, SW-1104 (2 Nov) 20.7 min before
its fixes, and SW-1095 is still open. The tier has never met its budget
since the corpus sweeps came in. The budget is stated for a 14-core Mac
(docs/testing.md:7), and the work moved to a 10-core M1 Pro (SW-1090).

**Recommendation.** Ask Matt (D2910) to restate the budget after one quiet
measured run, and to judge the cuts below by coverage, not by the budget.
The flake gate's job (a daily checkpoint) doesn't need 5 minutes. The
verifier's two minutes are what keep work flowing, and they are met (mean
64 s).

### T2. Four whole-AoC checks from cold in daily

- `web` `every_aoc_day_checks_passes_its_tests_and_runs_on_its_example`
  (417 s; priority 100) checks the whole project through the web API
  (`project.rs:549`), then each of 2025 days 1-6 by target, their tests and
  a run. Only the second part is the web API's own: outline, targeted
  check, test, run.
- `lsp` `aoc_navigation_matches_check_index` (290 s) compares the server's
  navigation with `check --index` over every namespace.
- `aoc_answers::every_day_from_the_whole_projects_cache` (160 s) runs a
  whole `check`, then every day from its cache.
- `search_at_aoc::search_at_on_aoc_goals` (195 s) loads AoC for its goals.

The whole-project check is the shared cost. `aoc_answers` is the one whose
point is the whole project (SW-255). **Change:** the web test drops the
whole check (line 549) and keeps the six days' targets. The LSP test takes
`Aoc.Common` and one day of each year outside the full tier. Saves roughly
330 + 230 test-s. The tier's longest test becomes `search_at_on_aoc_goals`
(195 s). The risk lost is a web-only or navigation-only failure in a
namespace outside the sample, until the full tier.

### T3. AoC proofs and AoC tests in the fast tiers

The kernel-merge-gate note covers the proofs: `aoc_answers` uses `run …main`
(`aoc_answers.rs:113-117`), which loads what `main` needs, so the 14 merge
days and the fixed core's day never check a `Proofs` namespace. What it
doesn't say: AoC's own `test` declarations run in no tier below full
(`machine::aoc_agrees` and `test:verify-cache` are full-only). The one
exception is the web test's 2025 days 1-6 (`project.rs:555`). `check` doesn't
run tests (`crates/cli/src/main.rs:111-115`). A change that breaks a day's
example test, with its answer still right, shows up only in the full tier.

**Change.** The fixed core's day, `year2024_day04`, becomes "check the day
with its `Proofs`, `Spec` and `Tests`, then run it" once SW-1915 makes
that one command: seconds. And a daily `stitchwort test` of AoC on a warm
cache: it reruns only tests whose hashes changed, and the test cache is
already trusted for this (D2379's verify-cache guards it in full). That
costs seconds after an application change and a full AoC test run after a
compiler change (each test's key holds the evaluation fingerprint). The
second needs measuring before it goes in.

### T4. No timeout ends a hung test

As kernel-merge-gate §8: `slow-timeout` only warns. Two more reasons to do
it now. The deep-input corpus (§6.1) counts "a hang past a time limit" as a
failure, which needs a limit. And a test in the `lsp-aoc-copy` or
`corpus-sweeps` group that hangs also holds up every test waiting for the
group. Set `terminate-after` per profile at about 3× the slowest test's
fastest time (merge: `pinned_hashes` 52 s, so `slow-timeout = 30s`,
`terminate-after = 6`; daily and full from their junit files). Add a
per-test override for the few long ones rather than a loose global limit.

### T5. Worker order in the sweeps

`par_map_with_at_most` (`driver.rs:107-137`) has each worker take the next
index from an atomic counter. Which items one worker sees, and in what
order, depends on timing. The sweeps that use `par_map_with` (`named_arguments`,
`hash_stability`, `std_library`'s sweeps and `extract`) keep one session per
worker and rewind it between items. That is deliberate (it cut `named_arguments` from
796 s to 3 s, docs/testing.md:288), and the rewind tests check that a rewound
session is fresh. But if a rewind ever leaves state behind, the item that
trips over it changes from run to run. Rerunning it with `EXAMPLES=` checks
it alone, in a fresh session, and passes. A panic does reset the worker's
state (`:132-135`), which is good.

**Change.** Hand out stripes: worker k takes items k, k + n, k + 2n, … for
n workers. Then each worker's sequence depends only on the thread count, and
`STITCHWORT_TEST_THREADS=N` reproduces it. When an item fails, print the
items that worker did before it. That loses a little packing at the end of
a sweep. If it's measurable, sort the items longest-first before striping.

### T6. Pass/fail by the wall clock

- `search_at_on_real_2021_goals` asserts a hit rate of at least 80% over 29
  goals (`search_at_aoc.rs:686`, 27 of 29 at the last count, so a margin of
  three) under `AtOptions::default()`'s 10 s deadline (`search_at.rs:67`),
  in the daily tier, on a `par_map` pool beside other tests. Its comment
  says "a goal near the time limit can miss under load".
  `search_at_on_aoc_goals` asserts 30% (`:404`) in the same way. SW-1168
  moved the `cli` `search` and driver `search_at` tests to a 120 s deadline
  and left these two (its own note).
- `lsp::a_newer_edit_cancels_the_check_running` (`lsp.rs:1305-1325`)
  measures one check, sleeps a quarter of that, edits again, and asserts
  exactly one cancellation. If the second check takes under a quarter of
  the first (a faster error path, a warmer cache, the machine's load
  dropping), nothing is cancelled and it fails. It is also the test SW-1094
  measured at 298 s and 8.4 GB.
- SW-1822 has a third (a code-action comparison under wall-clock limits).
- Bounds with a wide margin (`no_effect.rs:153` 10 s, `let_term.rs:513` 20 s,
  `resources.rs:445` 60 s, `search_at.rs:546` 5 s, `lsp.rs:2736` 10 s) are
  safe for now, but each stands in for "doesn't blow up", which a step
  growth test says exactly (kernel-merge-gate (c)).

**Change.** A test-only search budget counted in candidates tried, or in
steps, as the counterexample search already has (`untimed_counterexamples`).
The deadline test keeps the clock. For the cancel test, a check cache (the
`CancellingStore` pattern of `rewind.rs`) that blocks at its first lookup
until the second edit has been sent. That makes "the check is running" a
fact, not a guess.

### T7. The production counterexample path is untested

`.cargo/config.toml` sets `STITCHWORT_UNTIMED_COUNTEREXAMPLES=1` for every
cargo-run process, and the CLI children inherit it. That's the right choice
for snapshots (the note vanished under load). But no test removes it, so the
200 ms backstop, and the clock-before-`build_checker` bug of tactics F6,
run only for users and in `task audit`. **Change:** one test, with
`env_remove`, on a false theorem whose counterexample is found at once. It
checks that a note appears and that the run finishes well within a second.
If D2700 is taken (end by inputs, time only a backstop), the test checks
the backstop alone.

### T9. The answers tests check std from source each time

`check` passes `--no-cache` (`aoc_answers.rs:144-146`), so each of the 57
answers tests elaborates every library file its `main` reaches, from source,
before running. That's 603 test-s in daily and about 120 CPU-s, or 12%, of
the merge tier (SW-1090's "aoc_answers 122"). How much of it is std is
unknown (`STITCHWORT_TIMINGS` on one day would say). The SW-1761 pattern
applies: one `--cache-dir` holding only library entries, filled by one
process under `TestCacheTurn`. The day's own namespaces then still check
from source, and `every_day_from_the_whole_projects_cache` keeps testing
the from-cache path. Because the cache would hold the library only, this
stays a check of the day, not of the cache.

### T10. Slow tests that check little

- `run_js::running_out_of_stack_names_the_function` (58 s in daily, 145 s in
  a merge-profile selection): `build 20000000` by `List.append (build m)
  [n]` to see `[E-RESOURCE]` and the function's name. The overflow comes
  at a depth of thousands. If it takes a minute, the work before the
  overflow is the quadratic appends, or the JS backend's stack growth. A
  depth of 200,000 with a non-quadratic body checks the same thing.
- `rewind::repeated_edits_of_an_early_namespace_rewind_exactly` (155 s
  daily, 109 s merge-profile): two toy projects, three texts each. The time
  is likely the `outcome` dump of a navigable session that holds the whole
  library, compared at every step. Measure before changing (S).
- `doc::` in merge: six tests at about 25 s each (169 test-s in all, about
  20 s of the merge tier's wall time). Each `stitchwort doc NAME` with
  theorems replays the library and ranks its theorems in a new process.
  Keep `a_library_name_shows_header_doc_location_and_theorems` and
  `the_json_contract` in merge and the rest in `lane-search` and daily.

### T11. Sweeps that rebuild a baseline a snapshot holds

`named_arguments::named_calls_keep_every_hash` loads each file, rewinds,
loads it with named arguments, and compares the hashes
(`named_arguments.rs:476-496`). `fmt_hashes` compares each file's
hashes with its formatted text's (how it gets the "before" side not
checked). For the `accept` and `extract` files, the "before" side is exactly
what `hash_stability`'s snapshot pins. Reading the snapshot instead halves
those files' work. It also changes what a failure means ("differs from the
pinned hash" instead of "differs from this build's"). The two agree whenever
`hash_stability` passes, but a stale snapshot would then fail three tests
rather than one. A gain of about 40-55 test-s, at medium confidence about
how much of each sweep is `accept`/`extract`.

A wider version, a per-build store of each example's fresh dump for
`check_cache`, `rewind` and the lazy-loading sweeps to compare against, is
a design question, not a quick fix: the fresh side is the oracle, and
caching the oracle is the trust question of check-cache-trust in small.
Not recommended.

### T12. Full-only tests pass vacuously

Nine tests start `if !full_tier(…) { return; }`. In daily they count as
passed, which is intended. But `cargo nextest run --profile full` without
`STITCHWORT_TIER=full` (by hand; the tasks and the flake set it) passes
all nine and runs every sweep at the daily sample. nextest sets
`NEXTEST_PROFILE` in each test's environment. `tier()` can panic when the
profile is `full` and the tier isn't, or the profile is `merge` or a lane and
the tier is unset, naming both.

### T13. Debug assertions do run, once a day, on std

The elab-checking review says no tier runs a `debug_assert!`. But
`task test:daily` runs `cargo test -p stitchwort-driver --test library
builtins::` in the dev profile (`Taskfile.yml:244-254`), and dev keeps debug
assertions on (`Cargo.toml` has no `[profile.dev]` override for them). Its
tests load the whole library from source (`builtins.rs:25`, `:85`), which
goes through the elaborator's queue. So `queue.rs`'s 17 checks run over
std's elaboration once a day. They never run on AoC, the examples or the
queue's own unit tests. SW-1903's `invariants` feature is still the fix.
The ticket should just say the checks run daily on std (medium confidence
that every one of the 17 is reached by std).

### T14. Hash snapshots

531 snapshot files of hex hashes, one per example or project. They
catch exactly one thing, a declaration whose hash changed, which is the
point (a refactor that should leave terms alone). A reviewer can't judge a
hex diff, though, so on intended changes they get accepted wholesale.
Two smaller issues:

- `hash_stability.rs:8-9`: files that fail to load are skipped, computed
  rather than listed. An accepted example that stops loading drops out of
  the hash check without a word. `accepted_examples_check` catches the
  failure itself, so this is low.
- Nothing runs `cargo insta test --unreferenced=reject`, and the merge and
  lane tiers assert a quarter, so an orphaned `.snap` (a renamed example) is
  never reported. A small daily script comparing snapshot names with
  example files is enough.

`hash_stability::projects` (51 s) is the merge tier's second-slowest test.
The selector's rules don't pick it (they take `prelude` and `examples`,
`dev/test-affected.toml:89,216,322`), so the verifier never runs it anyway.
In the merge profile it only guards the checkpoint before a push. Moving
it to daily (and `lane-hashes`) saves about 6 s of merge wall time. The
risk: a change that moves only a project's hashes is seen a day later.

### T15. The sample never moves

`tier_sample` takes every n-th item from the first. That keeps runs
reproducible, but the same three quarters of the examples are never in the
merge tier or the verifier, between daily runs. **Change** (D2911): in the
verifier only, offset the sample by the merge commit's hash modulo the
stride (`STITCHWORT_SAMPLE_OFFSET`, printed in the log). Successive batches
then cover different quarters, and any one run can still be reproduced
from its log line. Daily and full don't change.

### T16. The selector log loses the reason

`dev/run-selected` takes failed test names from nextest's `FAIL`,
`SIGABRT`, `SIGSEGV` and `TIMEOUT` lines only. A build failure, a memguard
kill (exit 137), or a `fmt`/features failure in `test:selected`'s earlier
steps leaves the field empty. Six of the 15 failures are like that. Add a
column: `build`, `memguard`, `tests`, or the earlier step's name.

### T17. One platform, one feature set

The tiers run on this Mac, aarch64-darwin, with `crates/dev-features` on
(stack check, reference evaluator, allocation trace, native). The
distributed binary (`stitchwort-bin`), the x86_64 native backend (but
`frames.rs`' frame bound) and the Linux musl build (`Taskfile.yml:33`) are
never run by a test. docs/testing.md:50 measured that the features cost no
time, but not that they change no behaviour (`stack-check` panics where the
release build would overflow). The 1 Nov review's §5 (no automatic remote
gate) is still open: the one workflow is manual. Low, and it's a choice. It
should be written down in docs/testing.md as a known limit.

## 5. Fixed costs in each tier

| Cost | Where | Size | Notes |
|---|---|---|---|
| Rebuild after an edit | every task | about 20 s for a one-line `elab` edit, release, incremental (SW-1729, docs/testing.md:193); a first build about 2.5 min | kache in worktrees; the main checkout builds without it (D2200) |
| Process per test | nextest | about 5% of merge's CPU (SW-1090) | The price of isolation; no change recommended |
| Loading std | every test that loads the library | 0.6 s CPU replayed from the test std cache, 9-10 s from source (docs/testing.md:270) | SW-1095's "9 CPU-s per load, 136 tests" predates the cache; the from-source loads left are deliberate (`std_library`, `hash_stability::prelude`, `builtins`, `doc_links`) plus T9's answers tests |
| The cold std cache after a compiler change | the first test of a run | one process fills it (9-13 s), the rest wait holding slots, ordered by priority (SW-1751, SW-1765) | Already tuned; `pinned_hashes`' first test is the filler |
| `search-cache` fill | `doc`, `search`, search benchmarks | 13 s alone (SW-1751) | Ordered; T10 for the rest |
| `test:features` + `cargo fmt --check` | merge, selected | about 3 s + 1 s | Fine |
| `test:lanes-nonempty` | daily | about 13 s (1 s per profile) | Could be one `cargo nextest list --message-format json` with every profile's filter evaluated in a script: one listing instead of 18 (S, saves about 12 s) |
| clippy `--release --all-targets` | daily | a release-mode check of every target; minutes after a compiler change (not measured here) | Runs before nextest, in series. Running it beside nextest, as the debug `builtins` build is, would overlap it |
| Debug `builtins` | daily | 17 s build + 70-90 s of one core (`Taskfile.yml:244`) | Beside nextest already |
| `web:pkg` | daily | the WebAssembly build when stale (part of `test:browser`'s 35 s) | Needed for `STITCHWORT_REQUIRE_WASM` |
| Doctests | daily, full | `cargo test --release --doc --workspace` after nextest, in series | docs/testing.md:317 names three, in `partial-model`. If that is still all (check the other crates' doc blocks first: `js/src/lib.rs` has fenced blocks), `-p stitchwort-partial-model` skips the doctest pass of the other crates. A new doctest elsewhere would then need adding to the list (S) |

The largest fixed costs are already tuned: the std cache, the search cache,
priorities and the memory groups. What's left is small serial steps in the
daily task (lanes-nonempty, clippy, doctests) that could overlap or narrow,
worth perhaps 30-60 s of a run that is 25 minutes.

## 6. How the three proposals fit

**Kernel merge gate (kernel-merge-gate.md).** The right gap, at the right
place. The corpus gate is a tier of its own, "kernel lane", between the
selection and daily. It is the only check below daily that sees AoC proofs
(T3). Stage 2's step baselines are the deterministic oracle this review asks
for in T6, for the corpus. Once they exist, two daily costs become
redundant: the web test's whole-project check (T2) and the cold-AoC part of
`every_day_from_the_whole_projects_cache`, which then only needs to run
the days from a cache. Its ticket 3 (`terminate-after`) is T4; do it first,
since a step-ceiling gate that hangs is worse than one that fails. Its
growth tests (c) should also replace the wall-clock bounds of T6's last
bullet.

**Deep-input corpus (deep-input.md §6.1).** It fills the largest single
column of §3: four of the review findings, and SW-1875's deep half. Two
suggestions:

- Generate one `#[test]` per shape × consumer from the table (a macro), not
  one test with a child process per pair. nextest already gives each test
  its own process, so an abort fails one named test. `terminate-after`
  (T4) gives the hang limit. The selector, the timings store and
  `--estimate` see each pair. And the "shared `isolated` helper" becomes
  unnecessary.
- D2754's split (each shape once through four consumers in merge, the full
  table in daily) fits the tiers as they are. A deep-input change maps to
  the corpus's rows through `dev/test-affected.toml`, like the other rules.

**Check-cache trust (check-cache-trust.md).** Its §4 tests (forced refusal,
the dump at the undo point, a full `Builtins` dump) are cheap and belong in
the lanes and merge with the check-cache tests. The zero-refusal assertion
in the existing differential sweeps costs nothing. `check --verify-cache` in
the full tier is the first test of a cache *with history*. Every other cache
test starts from an empty folder. That is the right tier: its cost is a
cold whole-AoC check. One note: its §5 says the test std cache means "the
gates still run the kernel" no longer holds outside full. Every from-source
check left (`hash_stability::prelude`, `std_library`, `builtins`) is a std
check. So the kernel checks the examples and AoC as elaborated output in
every tier, but std's replay is trusted in all but those. That's fine, and
T13 adds a little: the debug `builtins` run is a from-source std check too.

## 7. Checked and sound

- **Profiles.** The merge filter is generated from the lanes and checked for
  staleness; `test:lanes-nonempty` catches an empty lane; a filter naming no
  binary is a nextest error; `run-selected` passes `--no-tests=fail`. The
  merge filter repeats `package(stitchwort-core)`, `package(stitchwort-native)`
  and `build::` beside narrower terms, which is harmless.
- **Isolation.** Shared file-system state is grouped (`lsp-aoc-copy`, the
  search cache, the test std cache under a lock with a fingerprint marker);
  temp folders are named by process id; `SPAWN` guards the pipe race within
  a process.
- **Hash order.** `clippy.toml` bans std's `HashMap`/`HashSet`; no test file
  uses them, nor keys anything by address. The address-keyed state left is
  in the compiler (SW-1803, core F11, SW-1822) and is ticketed.
- **Random tests** use fixed seeds and print the case and generator state on
  failure (syntax, formatter, elaborator, soundness and kernel fuzzers).
- **Sample scaling.** A sweep's coverage assertions scale with
  `tier_sample`, and filter parts that match nothing fail
  (`a_filter_part_that_matches_nothing_is_an_error`), so `EXAMPLES=` typos
  can't pass by sweeping nothing.
- **Snapshots** fail on a change in the flake (`INSTA_UPDATE=no`); the
  rejected examples check the error code as well as pinning the message, and
  every rejection has a nearby acceptance by rule.
- **Memory caps** per tier, with the measured peaks beside them.
- **Accepted examples** must also have no open goals and pass their tests
  (`examples.rs:233-252`), so an accepted example is checked as well as
  loaded.
- **Natives** agree with their definitions on the real prelude, at small,
  random and big numbers, and with unknowns (`natives.rs`).
- **The selector's rules** are tested (`dev/test-affected_test.py`, every
  binary reached or listed with a reason).

## 8. The 1 November review's findings on tests

| Finding (rust-codebase-review.md) | Status |
|---|---|
| §1.2 The test fingerprint omits the runtime; "test the collection of inputs" | **Fixed** (SW-1123). The collection is still not fully tested: a missing `EVALUATION_FILES` entry hashes as empty (driver review L3) |
| §2.2 The search JSON snapshot depends on a wall-clock deadline; use a work budget | **Changed**: the snapshot tests now pass a 120 s deadline (SW-1168), which makes them pass under load but still wall-clock. The two `search_at_aoc` benchmarks keep the 10 s default and assert hit rates (T6). Open |
| §2.2, §3.1 The canonical dump is kept by hand, so a new table can be left out of both the operation and the dump | **Open** and confirmed: the dump omits most of `Builtins` (elab-rest F10), the gap SW-1925 slips through. check-cache-trust ticket 1 destructures it |
| §1.1 Add an interpreter-based check of the ABI's Rust side (Miri) | The padding read is **fixed**; Miri is **open** (SW-1131, backlog) |
| §1.4 Tests for a document changing during a search, cancellation and repeated requests | **Fixed** (`a_document_edited_during_a_search_gets_no_stale_edit`, the cancel and pool tests in `lsp.rs`). A range that shifts on the same line isn't covered (SW-1949) |
| §4.2 Test abnormal exits through the native helpers | **Fixed** for error exits (`n2b`, `n4` error-exit traces); a Rust panic inside a helper is still untested |
| §5 No automatic remote regression gate | **Open**, by choice so far (T17) |

## 9. Tickets to file

Grouped into lanes. Measured times need tests beyond the lane rule; those
lanes say so.

1. **[DeepSeek] Small tier fixes** (45 min): T12 (`tier()` cross-checks
   `NEXTEST_PROFILE`), T16 (the log's stage column), T14's orphaned-snapshot
   script in `task test:daily`, and the doctests narrowed if §5's check
   holds. Tests: `task test:one -- tier`, `bash -n`,
   `python3 dev/test-inventory_test.py`.
2. **[DeepSeek] `terminate-after`**: kernel-merge-gate ticket 3, widened to
   daily and full from their junit times (T4). Already planned; no new
   ticket.
3. **[Sonnet] Daily overlaps** (60 min; after D2910): T2 (the web test's
   targets only, the LSP test's sample outside full), T10's `run_js` input
   and `doc` split, `hash_stability::projects` out of merge (T14), then
   `dev/nextest-merge`. Tests: each changed test once by name with
   `STITCHWORT_TIER=daily` (several minutes for the two AoC ones: needs
   Matt's agreement in the brief), `python3 dev/test-affected_test.py`.
4. **[Sonnet] Deterministic search tests** (60 min): T6, a test-only
   candidate budget in `AtOptions` used by `search_at_aoc` and
   `search_at_bench`; the LSP cancel test on a blocking check cache. Tests:
   the two `search_at_aoc` tests by name (daily-tier tests: agreed in the
   brief), `task test:one -- a_newer_edit_cancels`.
5. **[Sonnet] Reproducible sweep workers** (40 min): T5, striping and the
   failure report in `par_map_with_at_most`. Tests: `task test:lane
   AREA=hashes`, `task test:one -- named_calls_keep_every_hash`, and one
   sweep with `STITCHWORT_TEST_THREADS=1` and `=3` agreeing.
6. **[Sonnet] AoC answers with proofs and a library cache** (60 min; after
   SW-1915 and D2912): T3's fixed-core change, T9's shared library cache,
   and a measured `stitchwort test` of AoC on a warm cache to decide whether
   it joins daily. Tests: `task test:lane AREA=aoc`, the fixed core's day.
7. **[Sonnet] The timed counterexample path** (30 min): T7. Tests: the new
   test, `task test:one -- counterexamples`.
8. **[Sonnet] Growth tests for the wall-clock bounds** (45 min): T6's last
   bullet, `no_effect`'s 20 levels, `let_term`'s and `resources`' nested
   `let`s as `check_work`-style step growth, with the bounds kept as a
   backstop. Pairs with kernel-merge-gate ticket 2. Tests: the changed
   tests by name.
9. **[Sonnet] Measure, then fix, `rewind::repeated_edits_…`** (30 min): T10.
   Tests: the test by name.
10. **[Sonnet] Hash sweeps against the snapshots** (60 min): T11, after
    measuring the share of `accept`/`extract`. Tests: the two sweeps at the
    lane sample, `task test:lane AREA=hashes`.
11. **Fold into existing tickets:** SW-1903 (T13's correction); SW-1948
    (a hook that panics the checker on a marked file, so the fix is
    tested); SW-1916 and the deep-input corpus (a `"""`/`${…}` shape);
    SW-1800/SW-1803 (un-ignore `a_postponed_dot_call_takes_the_same_steps_every_time`
    in daily once SW-1803 makes it pass every time); SW-1095 (this note's
    T1 numbers replace its estimate).

## 10. Questions for Matt

- **D2910:** The daily tier took 1,462 s on 6 Nov against a 5-minute budget,
  and its corpus-sweep group alone needs about 16 minutes. Restate the
  budget from one quiet measured run after lane 3's cuts, rather than cut
  coverage to reach 5 minutes? [rec: yes, because reaching 5 minutes means
  cutting about 75% of the tier, and the check that keeps work flowing is the
  verifier's two minutes, which is met]
- **D2911:** Should the verifier's sample move with each batch, offset by
  the merge commit's hash and logged, so successive batches cover different
  quarters of the examples? [rec: yes, because today three quarters of the
  examples wait for the daily run every time, and a logged offset keeps each
  run reproducible]
- **D2912:** Should the fixed core's AoC day check its proofs as well as
  its answer (once SW-1915 makes that one command), and should AoC's own
  `test`s run in daily on a warm test cache if it measures under a minute?
  [rec: yes to both, because today no check below daily looks at an AoC
  proof, and AoC's tests run only in the full tier]
- **D2913:** Lanes 3 and 4 have to run a few daily-tier tests by name
  (the AoC web and LSP tests, the two `search_at_aoc` tests: several
  minutes each) to show the change. May their briefs allow that, run one at
  a time in the background? [rec: yes, because the alternative is changing
  slow tests without measuring them, and these runs are one test each, not
  a tier]
