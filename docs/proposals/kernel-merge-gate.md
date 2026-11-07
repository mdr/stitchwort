# A merge gate for kernel and core-language lanes (SW-1957)

Status: proposal, 7 Nov 2026. Questions D2760-D2763 for Matt. Analysis
only: nothing here was run. Run times are the ones recorded on the
tickets and in commit messages.

## In short

Record eta (SW-1642, stages 1 and 1b) broke two things that nothing ran
before the merge: AoC's proof checking went from about a minute to never
finishing (61.5 s → over 400 s), and six AoC proofs stopped checking. One
whole-AoC check on the branch, about 70 s, would have shown both. The
exponential slowdown was on the branch from 6 Nov 15:41, about 16 hours
before the merge. That check never ran because a whole-AoC run was treated
as a broad suite needing Matt's OK (D2507 put it after the merge). The
merge then waited about 7.5 hours for a question (D2575) that turned out
not to be needed.

**Recommendation.** Kernel and core-language lanes run a *corpus gate*
themselves, before review: AoC and the roguelike checked from cold, about
75 s, failing at a cap well below what a blowup takes (stage 1). Next, the
same run compares each AoC day's evaluation steps with a recorded
baseline. Steps are deterministic, so the run can stop a blowup at 3× and
name the day (stage 2). The check after a merge stays at D2441's two
minutes; the 70 s moves to the lane, where it runs once per branch and
waits on no one.

## 1. What happened, and when

From the commits on `main` and the branch (`git log --grep SW-1642`), and
the tickets:

| When | What |
|---|---|
| 6 Nov 12:16 | Stage 1: kernel projections, eta rules 1 and 2 (603b4acd6) |
| 6 Nov 15:41 | Stage 1b: fields of glued calls stay calls; `Frame::CallField` added (be69745c3). **The 2^n re-unfolding starts here** (SW-1829's fix commit 56b5aea0d names `CallField` as the cause) |
| 6 Nov 23:17 | main merged into the branch (fac0006fa) |
| 7 Nov 00:00-03:22 | Review SW-1764, fixes SW-1768 and SW-1767, design SW-1766: all on the branch; none ran AoC |
| 7 Nov 00:25 | Board: "record eta waits on the whole-AoC run" |
| 7 Nov 03:22 → 07:56 | Nothing on the branch; D2575 open; 189 commits land on main overnight |
| 7 Nov 07:56-08:10 | Merge lane (D2581): main into the branch, 14 min (est. 45) |
| 7 Nov 08:10 | Merged (319c28c0c); D2507's whole-AoC check starts |
| 7 Nov 08:11+ | Check killed at 360 s; SW-1829 opened. main held unpushed (D2586) |
| 7 Nov 09:10 | SW-1829 fixed (52 min): whole AoC 68.8 s. Six proof errors left: SW-1913 (est. 90 min) |

What the lanes did run: 175 core and 16 record-eta tests, std, the
roguelike (its +28% on `Rogue.Proofs` was seen and accepted), trip-journal,
2021 day 13 and its `audit:touched`, and `test:affected` (807 and 981
passed). All of these passed, and none of them checks the proofs of
2020 day 20, 2021 days 2, 11 and 15, or 2024 days 11 and 23.

The cost after the merge: an Opus lane of 52 min to find the 2^n by
bisecting in namespaces, then 90 min of proof fixes. Main also stayed
unpushed while a revert was open. On the branch the same work would have
been the same lanes without the hunt. SW-1829 had to find the namespace
first; on the branch a capped run names the day that didn't finish.

## 2. Which existing check would have caught each regression

There are two regressions. **A** is the 2^n: 2024 day 11's `part1Correct`
(25 levels) and `part2Correct` (75 levels) never finish. **B** is the six
broken proofs.

| Check | A (2^n) | B (six proofs) | When it runs | Why |
|---|---|---|---|---|
| `test:lane AREA=core`, the lane's targeted tests | no | no | in the lane | No AoC. No test had nested fields of folded calls (`eta_fields` was written by SW-1829 afterwards) |
| `test:affected` (lane and verifier) | no | no | lane, after merge | For a `crates/core` change: `lane-core`, all of `core`, the `hash_stability` sample (`dev/test-affected.toml:298-327`). The fixed core's one AoC day is `aoc_answers::year2024_day04` (`:69-77`), which is `stitchwort run …main` (`crates/cli/tests/running/aoc_answers.rs:105-121`): it loads what `main` needs and never checks the day's `Proofs` (SW-1915's trap; inferred from the command, not run) |
| merge tier (`task test:merge`) | no | no | daily checkpoint and before a push (D2441) | Its 14 AoC days (`.config/nextest.toml:98`) are answers via `run` again, and none of them is one of the broken days |
| bench step counts (`crates/bench/tests/baseline.rs`) | almost surely no | no | daily (most); `examples` full only | The benchmarks are the example corpus and micro-programs (`bench/baseline.toml`), not AoC. The example sweeps passed on the branch, so no example has the shape (inferred) |
| bench growth tests (`check_work.rs:208`, merge tier) | no | no | merge tier | The right *kind* of test (steps at 5, 7, 9, 11, growth must stay linear), but only for the shapes someone wrote, and nobody had written this one |
| `eta_fields` (written in SW-1829), the "deliberately slow test" | yes, but by hanging | no | merge (proofs binary) | Fixed at 24 levels; a regression makes it run for hours, not fail. No nextest profile has `terminate-after` (`.config/nextest.toml:33,42,53,75`: `slow-timeout` only warns), so a regression would hang the tier until someone stops it |
| `audit:touched Aoc.Year2021.Day13` | no | no | in the merge lane | That day was fine |
| daily tier (`task test:daily`) | yes, slowly | yes | daily checkpoint, with Matt's OK | `aoc_answers::every_day_from_the_whole_projects_cache` runs a whole `stitchwort check` of AoC first (`aoc_answers.rs:445-462`), and the `lsp` AoC tests do as well. B fails them. A makes each of them run 400+ s, with no cap, so the tier overruns its 5 minutes by a lot |
| full tier | yes, slowly | yes | when Matt asks | Also `check_cache`/`rewind` on AoC and `test:verify-cache` |
| D2507's whole AoC after the merge | **yes** | **yes** | minutes after the merge | This is what caught both, at 08:11 |
| whole AoC on the branch (never run) | **yes** | **yes** | any time from 6 Nov 15:41 | The same run as D2507's, about 16 hours earlier |

The cache can't make a kernel or elaborator branch's AoC check cheap,
because every check-cache entry is filed under `FINGERPRINT`, which hashes
the checker's crates (`docs/proposals/check-cache-key.md:22-35`). A
compiler change means a cold check, about 70 s, whoever runs it.

## 3. The cheapest check that would have caught both

Four candidates.

**(a) Whole AoC and the roguelike on the branch, cold, with a cap.**
`stitchwort check --no-cache` in `aoc/` (61.5-69 s on main this morning,
SW-1801 and SW-1829) and `games/rogue/` (5 s), failing if either errors or
runs past a cap. It catches A as "didn't finish within the cap" and B as six
errors. It costs about 75 s of the lane's time, once per branch, and needs
no new code. Its weakness is the wall clock: on a machine with three lanes
and load around 20 (SW-1751) the time wobbles, so the cap must be loose,
about 3× (200 s). That still catches A (over 400 s, really unbounded) but
not a 2× slowdown. When A hits the cap, the run gives no per-day report
(`STITCHWORT_TIMINGS` prints at the end of the run, `crates/cli/src/main.rs:575-577`).
So "which day" means a second run by namespace.

**(b) A per-day step baseline with a 3× ceiling.** The same run, counting
evaluation steps (`Budget::total_work`) per AoC namespace and comparing them
with a recorded file. Steps don't depend on load: the bench already relies
on this and checks it (`docs/testing.md:244`, `crates/bench/tests/repeat.rs`).
It can stop a day as soon as it passes 3× its baseline, naming the day and
its slowest declaration (`STITCHWORT_TIMINGS` already counts steps per
declaration, `crates/elab/src/timings.rs:11-16`). A 2^n then fails in
seconds, not minutes, and a slowdown like the roguelike's +28% shows up as a
number. It costs a few hours of work, a baseline file to keep up to date,
and the same 70 s per run.
Two risks to settle as it is built: whether everything `check` runs is
step-deterministic (the bench needs `Elaborator::untimed_counterexamples`
for its counterexample searches; whether `check` does any timed search on
a failed theorem needs confirming), and baseline churn. At 3× (fail) the
churn is rare. A softer warning at +25% is shown, never fails.

**(c) An exponential-growth test for the kernel.** A `check_work`-style
test (`crates/bench/tests/check_work.rs:208-240`) that checks the
`eta_fields` program at 6, 8, 10 and 12 levels and requires the step growth
to stay linear. It catches A in a second, in the merge tier and the lanes.
It catches only this shape, and it could only be written after the bug was
known. It's the right way to keep a fixed blowup fixed (better than today's
24-level `eta_fields`, which would hang rather than fail), but it doesn't
find the next one. It doesn't catch B.

**(d) Proof-check results recorded per day.** A snapshot of which AoC
declarations check. The plain check already fails on any error, so
recording adds no detection for B; it would only help a branch that is
*allowed* to break some proofs (D2498-D2505 accepted goals changing shape)
to list which. That's `stitchwort check`'s error list, so there's nothing
new to build.

**Cheapest that catches both: (a).** It has no build cost, it's 75 s, and
it would have caught both regressions 16 hours earlier. (b) is the same run
made exact. (c) is a habit for every blowup fixed. (d) isn't needed.

## 4. A gate by lane type

What decides the gate is whether the change can alter the verdict or cost
of proofs it doesn't touch.

| Lane type | Paths (examples) | Can it break distant proofs? | Gate before review (in the lane) |
|---|---|---|---|
| **Kernel and core language** | `crates/core/**`; the elaborator's unifier, conversion, `rewrite`, `match`, `cases`, automation (`auto`, `omega`, `decide`, `ring`); `crates/elab/src/std/core/**`; syntax that changes what elaborates | Yes: every proof goes through them | Targeted tests, `test:affected`, plus the **corpus gate**: AoC and roguelike cold, capped (stage 1), later with step ceilings (stage 2); a growth test for any new unfolding or caching path. Opus review per D2364 |
| **Elaborator, other** | diagnostics, error messages, navigation, the language server, goals display, `search` | Rarely: they don't decide verdicts | Targeted tests and `test:affected`. The corpus gate only if the lane says its change reaches elaboration results |
| **Std, non-core** | `std/**` lemmas and definitions | Yes, but through names, which the cache tracks | `test:affected` (std rules), `snap:hashes`; AoC with the *warm* cache, which rechecks only what depends on the changed files (seconds) |
| **Application code** | `aoc/**`, `games/rogue/**` | No: the compiler is unchanged, so only the namespaces that import the changed ones | `audit:touched` (D2043, as now); check of the touched day *with* its `Proofs`, `Spec` and `Tests` (SW-1915); if `Aoc.Common` changed, the whole of AoC on the warm cache (seconds) |

The kernel row is the new part. The paths that trigger it already line up
with `dev/test-affected.toml`'s rule groups (`crates/core/**`, `:298`; the
elaborator's rewrite, matching and automation rules, `:142-191`). I'll
have the selector print the gate for those paths as it prints its
`RUN BY HAND` checks today (`manual` lines, `docs/testing.md:41`): `GATE:
task gate:corpus`. The 70 s then never counts against the verifier's 90 s
budget, and no lane has to remember it. That's an implementation detail I
decided; it's stage 1 below.

## 5. How this fits D2441

D2441 is about the check *after a merge*: about two minutes, so the flow
of work doesn't stall, with regressions that slip past accepted as a risk.
This proposal doesn't add to that check. It moves one 70 s run *before* the
merge, into the lane, for one kind of lane:

- **The verifier stays at two minutes.** D2507's 6-minute whole-AoC run
  after a merge was a one-off for record eta. It's no longer needed for a
  lane that passed the gate *after merging main into its branch*: the tree
  checked is then `main` plus the lane, short only of its batch-mates.
  (D2761.)
- **The lane's cost.** One run of about 75 s. Kernel lanes run for 60-180
  min, so that's 1-2% of their time. It fits CLAUDE.md's test budget, where
  no single run goes over "a minute or two". What changes is that it stops
  counting as a "broader suite" that needs Matt's OK (D2760).
- **The flow.** Record eta lost about 7.5 hours waiting, and about 2.5
  hours of Opus lanes fixing things on a `main` that couldn't be pushed. The
  gate costs 75 s per kernel lane. Even if it catches something only once
  in twenty kernel lanes, the trade is lopsided.
- **The machine.** Three lanes may each run a cold whole-AoC check at the
  same time. The cap is loose (3×) for that reason, until stage 2 replaces
  it with step counts, which load doesn't affect. The gate's script prints
  `uptime` beside its times, as the verifier does, so a capped run under
  heavy load can be told from a real slowdown.

## 6. The stale-branch wait

The wait was not the cost of merging. The merge lane took 14 min (est. 45)
for 189 commits and about 46 snapshot conflicts. The cost was the
4.5 hours with nothing happening (03:22 → 07:56), on a branch that was ready
except for one 70 s check, while main moved on. Three causes, and the fix
for each:

1. **A check needed permission.** The lane test scope rule ("whole-AoC and
   roguelike checks need Matt's OK") made a 70 s run a question. D2507 then
   put it after the merge, and D2575 asked again before the merge (withdrawn
   at 08:00, since D2507 had already said yes). *Fix:* the corpus gate is
   part of the lane's own work for kernel lanes (D2760). A check that fits
   the test budget is never a D question.
2. **Merge-ready had no definition.** Nothing said "this branch meets its
   gate, so it merges in the next batch". *Fix:* the gate table (section 4)
   goes into `docs/workflow.md`. A lane that meets it merges in the next
   batch with no further question. Questions about checks are the
   orchestrator's to decide, as the decision-scope rule already says for
   sequencing (D2763).
3. **The branch waited unmerged.** *Fix:* a lane branch that waits on
   anything for more than about two hours merges main in before it runs its
   gate, so the gate runs on what will land. I'll write that into the
   workflow text in stage 1. A merge-in costs minutes (14 here), and doing it
   just before the gate is what makes the gate's result stand for the merge
   (D2761).

Merging record eta into `main` behind a flag, so it could land early and
be switched on later, would avoid the drift. I rejected that: it means two
kernels (with and without eta) both kept sound and tested, and hashes that
depend on the flag. That doubles the hardest part of the code to remove a
few hours' wait, which the three fixes above remove anyway.

## 7. Designs compared

| | Catches A | Catches B | Cost per kernel lane | Build cost | Says which day | Rules out |
|---|---|---|---|---|---|---|
| Today: D2507 after the merge | yes, after the merge | yes, after the merge | 0 in the lane; a dirty `main`, a held push, an hour's hunt | none | no | nothing, but every regression lands on `main` first |
| Daily tier on the branch | yes, in 5+ min | yes | 5+ min, needs Matt's OK | none | no | it's the tier Matt rations |
| **(a) Corpus gate, wall cap** | yes, at the cap | yes | ~75 s | a task and a selector line | by a second run | slowdowns under 3× go unseen |
| **(b) (a) with step ceilings** | yes, in seconds | yes | ~70 s | ~2 lanes | yes, and the declaration | none of the above; needs a baseline kept up to date |
| (c) Growth tests | this shape only, in 1 s | no | ~1 s (merge tier) | a test per shape | n/a | n/a: it complements (a)/(b) |

**Recommended: (a) now, then (b); (c) as a habit.** (a) is cheap and would
have caught both regressions. (b) makes the same run deterministic and
informative. It also lets the cap be tight without false failures from
load. (c) keeps each fixed blowup fixed in the cheap tiers.

**How other systems do this.** Lean 4 tests a core PR against Mathlib
before merging: a `lean-pr-testing-N` branch of Mathlib builds against the
PR. That's a downstream corpus gate, like (a). Rust runs crater (the
ecosystem) for language changes, and rustc-perf's `@rust-timer` runs for
cost. rustc-perf compares instruction counts rather than wall time because
they're stable, which is (b)'s reasoning. GHC's testsuite keeps performance
metrics per test (allocations, mostly) in git notes with an acceptance
window, and a commit that raises one past the window must say so
(`Metric Increase:` in its message). That's the model for keeping (b)'s
baseline honest: a lane that accepts a cost updates the baseline in a
commit that says why, as `bench/baseline.toml` already asks
(`docs/testing.md:255`).

**What it costs and rules out.** About 75 s per kernel lane, and later a
baseline file. It rules out kernel lanes that are "done" without having
checked the corpus, which record eta was. It doesn't catch what AoC and the
roguelike don't exercise. The example corpus is in the daily tier for that,
and the risk is accepted as D2441 accepts it.

## 8. Findings outside the gate

- **No nextest profile ends a hung test.** `slow-timeout` has no
  `terminate-after` (`.config/nextest.toml:33,42,53,75`), so a regression that
  makes a test run for hours, as `eta_fields` would, holds the lane, the
  verifier or the merge tier until someone stops it. A `terminate-after` in
  the merge and lane profiles (a few times their `slow-timeout`; the slowest
  merge tests need checking first) turns a hang into a failure.
- **`aoc_answers` never checks proofs.** It uses `run …main`
  (`aoc_answers.rs:113-117`), so the 14 merge-tier days and the fixed core's
  day test answers only. The whole-project test is daily only. This is what
  "the merge tier runs AoC" hides. SW-1915 is the same trap at the command
  line.
- **2024 days 11-24 have no answers test** (no committed inputs,
  `aoc/inputs/2024` ends at day 10; `ANSWERS` ends at 2024 day 10,
  `aoc_answers.rs:77`). Only their proofs are checked, and only by
  whole-project checks. That doesn't matter here, but it's a hole in the
  per-day tests.
- **SW-1903 is the same pattern.** `queue.rs`'s `debug_assert`s never run
  in any tier, so they catch nothing. A check that no gate runs is worth
  nothing. Neither of record eta's regressions was an invariant violation,
  though, so SW-1903 wouldn't have caught them.

## Questions for Matt

- **D2760:** Kernel and core-language lanes (`crates/core`; the unifier,
  conversion, `rewrite`, `match`, `cases` and the automation tactics; std
  core) run the corpus gate themselves before review: AoC and the roguelike
  checked from cold, about 75 s, failing at about 200 s. It counts as one of
  the lane's targeted tests, with no approval needed. Should they? [rec: yes,
  because it would have caught both of record eta's regressions 16 hours
  before the merge, for 1-2% of a kernel lane's time]
- **D2761:** A lane that passed the gate after merging main into its branch
  needs no whole-AoC run after the merge; D2507 was a one-off and is
  retired. The post-merge check stays at D2441's two minutes. Agreed? [rec:
  yes, because the gate checked the same tree but for batch-mates, and
  D2441's budget is the flow Matt asked to keep]
- **D2762:** Build the per-day step baseline (stage 2): the corpus gate
  counts evaluation steps per AoC namespace, fails at 3× a recorded
  baseline, and stops a blowup there, naming the day and declaration. The
  baseline is updated deliberately, with the reason in the commit, as
  `bench/baseline.toml` is. Should we build it? [rec: yes, after stage 1 has
  run on a few kernel lanes, because it removes the wall clock's noise and
  the hour-long hunt SW-1829 needed]
- **D2763:** "Merge-ready" means meeting the gate for the lane's type
  (section 4, written into `docs/workflow.md`). A lane that meets it merges
  in the next batch without a further question, and checks within the test
  budget are never D questions. Agreed? [rec: yes, because record eta's
  4.5-hour wait was a question about a check D2507 had already answered]

Decided by me, as implementation: the gate is a task (`gate:corpus`) that
the affected-test selector prints, like its manual checks, rather than a
selector command inside the verifier's budget. A branch waiting more than
about two hours merges main in before its gate. Each blowup that gets fixed
gets a growth-form test in `check_work`.

## Tickets to file

In order; stages 2 and 3 wait for D2762.

1. **[Sonnet] Corpus gate, stage 1** (45 min). `task gate:corpus`:
   `stitchwort check --no-cache` in `aoc/` and `games/rogue/`, each under a
   wall cap (200 s and 30 s, overridable), printing each wall time and
   `uptime` before and after, failing on any error or overrun. In
   `dev/test-affected.toml`, a `manual`-style gate line for the kernel and
   core-language paths of section 4, printed as `GATE:`. `docs/workflow.md`:
   the gate table, merge-ready (D2763), merge main in after a two-hour wait.
   `CLAUDE.md`: the lane test-budget line (after D2760). Tests:
   `python3 dev/test-affected_test.py`, `bash -n` on any script, one run of
   `task gate:corpus` on main (about 75 s).
2. **[Sonnet] Growth test for nested field calls** (30 min). Rewrite
   `crates/driver/tests/proofs/eta_fields.rs` (or add to
   `crates/bench/tests/check_work.rs`) as a growth test: 6, 8, 10 and 12
   levels, steps must grow linearly, with `growth` from `check_work.rs:208`.
   Show it failing with SW-1829's fix reverted locally. Tests: `task
   test:one -- eta_fields` and `-- check_work`.
3. **[DeepSeek] `terminate-after` in the merge and lane profiles** (30
   min). Read the slowest merge-tier tests' times from the inventory, then
   set `terminate-after` so the slowest has 2× room. Tests: `task
   test:lanes-nonempty`; `cargo nextest show-config` for the profiles.
4. **[Sonnet] Per-namespace step counts from `check`** (60-90 min; D2762).
   `stitchwort check --steps FILE`: the evaluation steps and visits per
   project namespace, as JSON, from the counters `STITCHWORT_TIMINGS` already
   keeps. First confirm, and if not, make, every search `check` runs
   step-bounded rather than timed, as the bench's untimed counterexamples
   are. Show that two runs give the same file. Tests: a CLI test on a small
   project (two runs equal); `task test:lane AREA=cli`.
5. **[Sonnet] Step baseline and ceiling** (60 min; after 4). Add
   `bench/aoc-steps.toml` (and the roguelike's) and a
   `task gate:corpus:update`. The gate compares each day with the baseline:
   it fails past 3×, prints days past +25%, and passes each namespace a
   step ceiling of 3× its baseline, so a blowup stops there with `E-RESOURCE`
   naming the declaration (a test-time limit that fails, as D2543 asks). A new
   day without a baseline gets the median day's ceiling × 10. Tests: the task
   on main; a fixture project whose baseline is set low, which must fail with
   the day named.
6. Already filed and relevant: **SW-1915** (a day's check should include its
   `Proofs`, `Spec` and `Tests`, for the application-lane gate). **SW-1903**
   is the same "a check no tier runs" pattern (section 8).

What this note doesn't cover: the example corpus as a gate for kernel lanes
(it's in the daily tier and the bench; a 4× sample is already in the merge
tier), and whether elaborator lanes outside section 4's list should take the
gate too. Their record is clean so far; the gate's `GATE:` line can widen
if one breaks AoC.
