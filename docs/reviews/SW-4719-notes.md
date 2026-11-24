# SW-4719: `check --jobs N`, stage 1 of parallel checking: reviewer's notes

Built from docs/proposals/parallel-checking.md §9 (SW-4718's design, D3730).
Opus lane, 24 Nov 2026. These notes are the checklist for the review the
design asks for (the driver's trust wording, and the scheduler's "written"
test), and say what the lane could not verify.

## What was built, where

| Part | File |
|---|---|
| `load_analysis_for` split into `prepare_analysis` (target, order, namespace sources) and `check_prepared` (the old body after that), behaviour unchanged | `crates/driver/src/project.rs` |
| The fill: `parallel::fill(files, project, target, &Jobs)`, the scheduler (`Board` behind one `Mutex` and `Condvar`), workers, the stop flag, the seeded pick | `crates/driver/src/parallel.rs` (new) |
| `MemoryStore` (the `--no-cache` store) and `Claims`/`ClaimStore` (the library claim table, with a bounded wait) | `crates/driver/src/check_cache.rs` |
| `--jobs N`, `-j N`, `STITCHWORT_JOBS`; the one-job rules; `PARALLEL_NO_CACHE` | `crates/cli/src/main.rs` (`check`, `fill_in_parallel`) |
| `--timings`: one `worker k: loading` row per worker, untimed `(cached)` rows dropped when the namespace has a real row or is listed twice, the wall line with jobs, and a line saying what the fill did or why one job ran | `crates/elab/src/timings.rs` |
| Tests | `crates/driver/tests/projects/parallel.rs` (new, five tests, fixture `parallel/par_project` copied from the design's `tests/`), one in `crates/cli/tests/server/check_cache.rs` |
| Docs | guide chapter 11 (performance notes), `docs/workflow.md` (lanes never pass `--jobs`), `docs/proposals/check-cache-trust.md` (what `--no-cache --jobs N` trusts), `docs/performance/log.md` |

Nothing in `crates/core` or `crates/elab/src/cache/` was edited. No term,
hash, key or entry format changed.

## The D3731 switch

`PARALLEL_NO_CACHE` in `crates/cli/src/main.rs` (a `const bool`, `true`
now). With `false`, `check --jobs N --no-cache` runs one job, quietly (with
`--timings` it says "one job: --no-cache"), and `MemoryStore` is unused. That
is the whole of it: `fill_in_parallel` is only reached through the one-job
rules, which read the constant.

## The exactness argument, as built

1. **Everything reported comes from the last pass.** `fill` returns before
   `load_project_counting` runs exactly as before, over the same store. The
   fill's own diagnostics are dropped. So a difference in messages can only
   come from a difference in which entries exist, which the cache already
   promises can't change a report (replay equals elaboration, and the
   "left out, then an error after it" rule reloads everything).
2. **A namespace is called filled only if an entry exists for it.** In
   `Worker::job`, `written` is true only if the session's
   `namespace_written` or `namespace_hits` rose while checking that one
   namespace (`check_project_namespace` on it alone). A hit means its entry
   was found and replayed; a write means `elaborate_namespace_cached` wrote
   it (clean, no goal, not cancelled, no failed dependency). Anything else
   rewinds the session to the mark taken just before, and the namespace and
   everything above it are `Left`. Reviewer: check that no other path sets
   `Status::Done` (only `Shared::finish` with `written`, and the plan's
   initial hits).
3. **Ready means every direct dependency is `Done`.** `Board::ready`. The
   plan's initial `Done` comes from `plan_namespace`, which only returns
   `Some` for an exact entry whose seal, key and library files fit.
4. **A worker's dependencies are loaded in canonical order** of the
   namespace's closure (`dependencies`), each by `check_project_namespace`,
   so each is a replay of an entry that exists (counted in `Fill::twice` if
   one had to be elaborated instead: 0 in every test).
5. **Workers share no values.** Each has its own session, analysis and
   store handle; the texts are read once on the caller's thread and copied.
   The store handles share only the directory (writes by rename) or the
   `MemoryStore`'s map behind a mutex.
6. **With the cache on** a wrong worker costs time, not correctness: its
   entry would be a miss or a refused replay in the last pass. With
   `--no-cache` the last pass trusts the workers' entries as it would a
   folder's: that is D3731's subject, written up in
   `check-cache-trust.md`'s new paragraph.

## Deviations from the design

- **The planner is worker 0.** The caller's thread makes the first worker's
  session, analyses, prepares and runs `plan_namespace` in it, then works as
  a worker on the same thread; so no extra session is made. Its `plan_namespace`
  calls record keys in that session's tables, which the job's own
  `check_project_namespace` calls overwrite.
- **The texts** are read with `project_sources` once, and each worker adds
  `stitchwort.yaml` to its own sources through `Files::config`, as
  `project_sources` would (the namespaces' keys hash it). The last pass
  reads the files again as today; a file changed mid-run makes its keys
  differ and the last pass elaborates it itself.
- **Above an open goal.** The design's failure test said "nothing above it
  has an entry". A one-job check does write an entry above a namespace with
  only an open goal (`failed_namespaces` holds errors only), so the test
  asserts the 4-job cache equals the 1-job cache, and that the fill left
  `Left` and `Top` to the last pass.
- **A panic** in a worker is caught, the fill stops, and the last pass runs.
  The panic hook still prints the worker's panic message, so a panic that
  only a worker meets adds that message to the output. Not tested.
- **A worker whose set-up fails** (it can't, given the caller's thread's
  succeeded on the same texts) just takes no jobs; the design had no rule.
- **Claims** wait at most 60 s (`CLAIM_PATIENCE`), then elaborate; counted
  in `Fill::claims_gave_up` (0 in the tests).
- **`--jobs auto`** is not built (orchestrator's call, D3730 notes).
- **One-job rules** are as §9.2; a file target never reaches the fill (it
  has its own branch). `--index` and `--counterexamples` fill and then load
  everything, as designed.
- **Cancellation**: the shared stop flag is each worker's budget's cancel
  flag, watched for the whole fill; set only after a panic.

## For the orchestrator after SW-4714 merges

`crates/elab/src/cache/mod.rs:22-24` says "`--no-cache` is the full check".
With `PARALLEL_NO_CACHE` it should read, say: "`--no-cache` with one job is
the full check; `check --jobs N --no-cache` passes the workers' entries
through a store in memory (D3731, `crates/driver/src/check_cache.rs`,
`MemoryStore`)". Not edited here: that file is SW-4714's.

## Tests run

- `package(stitchwort-driver) & binary(projects) & (test(/check_cache::(digest::|cache_)/) | test(/^parallel::/))`:
  26 passed, 41 s.
- `package(stitchwort-cli) & binary(server) & test(/caching::|check_cache::/)`:
  24 of 25 passed (the new `check_jobs_prints_what_one_job_does_and_one_job_for_recheck`
  among them), 77 s. `check_cache::a_library_edit_re_checks_what_it_can_change_and_nothing_else`
  fails at "a name added" (expects `Dep` re-elaborated); its steps, replayed by hand with
  main's release binary and with this branch's, give the same debug lines, so it fails on
  main too and is not this change.

## What I could not verify

- **The measure** (`docs/proposals/parallel-checking/measure_jobs.sh`) on
  `tools/fmt` and AoC: not a lane's. The script matches the flag as built
  (`--jobs N`, `--cache-dir`, `--no-cache`); its library fill (`check --std
  Std`) does give the project check hits (checked on `Std.Ord`, one file).
  Only `bash -n` and that spot check were run.
- **I2 for kept sessions** beyond the fixtures: 20 seeded schedules on an
  8-namespace project and the byte compare on three projects. The
  whole-project compare (Overmind's `--jobs 4` beside `--jobs 1`) is the
  real evidence.
- **Memory** at 4 and 8 jobs on large projects: each worker forgets its
  session at the end, and holds every closure it was given.
- **Signals in worker threads**: `catch_check_signals` blocks the signals
  before any thread starts, and threads inherit the mask, so the signal
  thread still gets Ctrl-C. Not exercised.
- **`E-RESOURCE` within a kept type's forcing cost of the limit** (§9.4 item
  4): unchanged from the design's statement; nothing here measures it.
- **The gain.** On `examples/projects/accept/trip-journal` (4 namespaces,
  mostly a chain, dominated by the library) the cold check went from 13.1 s
  to 9.0 s with 4 jobs, and `--no-cache` from 7.3 s to 8.0 s (no parallel
  work to do, plus three more sessions and entries encoded into memory);
  one run each on a loaded machine (load about 12). The project-sized figures
  are the measure's.

## After the Fable review (docs/reviews/SW-4719-fable-review.md)

- **F1.** `Fill::load_after`: when the fill left a namespace, the check after it loads
  everything (`Load::Everything`), so a namespace that fails is checked twice in all (worker,
  then the check), not three times. `parallel::a_failure_is_reported_as_with_one_job_and_the_rest_is_filled`
  counts `Par.Left`'s timings rows; without the fix the syntax-error case elaborated it twice
  after the fill. The guide now says the "still checking" notes can differ.
- **F2.** `progress::CURRENT` holds one label per thread; `current()` gives the one begun
  longest ago, so a worker finishing a quick declaration no longer erases another's.
- **F3.** `check-cache-trust.md`: the reference run passes `--jobs 1` explicitly, and the
  check after a `--no-cache` fill leaves most clean namespaces out on the entry's head.
  Overmind's rolling-check script is not in the repo: the orchestrator adds `--jobs 1` there.
- **F4.** `NO_ETA` is put back by a drop guard (`unify.rs`, in `first_order`'s argument
  pairing); a panic caught by worker 0 (the caller's thread) is raised again once the other
  workers stop, instead of checking on over that thread's state.
- The `--timings` fill line also gives the claim waits given up (the review's note).
