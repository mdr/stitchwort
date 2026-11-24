# SW-4719 (`check --jobs N`, parallel checking stage 1): Fable review

24 Nov 2026. Reviewed: `lane/SW-4719` at `435cf0696` (code `5a5ce5a78`) against its
merge base with `main`. I wrote the design (parallel-checking.md §9), so this is not an
independent read of the design, only of the build against it. Marks: **[ran]** I ran it
today with the lane's release binary on small projects in scratch; **[read]** I read the
code at the place named; **[argued]** reasoning from what I read, not exercised.

## Verdict

**Merge.** I found nothing that makes `--jobs N` report a different diagnostic, summary or
exit code from `--jobs 1`, write a different entry, or admit anything beyond what the trust
paragraph says. The "written" test is right: a namespace is called filled only when its
entry exists.

Four findings, none blocking; the first is worth fixing soon because it makes a failing
parallel check slower than a one-job check:

| # | Severity | Finding |
|---|---|---|
| F1 | medium (speed, stderr) | A namespace that fails is checked three times with `--jobs N` on a cold cache, once with `--jobs 1`; its "still checking" notes print three times |
| F2 | low (message) | Ctrl-C under `--jobs N` usually loses "while checking X" |
| F3 | low (trust wording, process) | `STITCHWORT_JOBS` in the environment silently turns `--no-cache` from the strict full check into the weaker one; the doc should say what the reference run must pass |
| F4 | low (never expected) | A panic caught in worker 0 leaves the reporting thread's thread-local state as the panic left it |

## Findings

### F1. A failing namespace is checked three times (medium)

**Repro [ran].** A five-namespace diamond plus one namespace whose only theorem computes
for 18 s and then fails:

    def countdown (acc: Nat): Nat → Nat
      | 0 => acc
      | Succ k => countdown (acc + 1) k

    theorem slow: countdown 0 30000000 = 1 := byComputing

| | wall | "still checking" notes | diagnostics, exit |
|---|---|---|---|
| `check --jobs 1`, cold cache | 18.9 s | 2 | `E-RESOURCE`, 3 |
| `check --jobs 4`, cold cache | 55.5 s | 6 (the same two, three times) | the same |

**Why [read].** (1) A worker checks the namespace, writes nothing, and it is left.
(2) The last pass now finds entries for the clean namespaces, so `check_prepared` plans to
leave some out (`plan_skips`, `crates/driver/src/project.rs`), checks the failing
namespace, sees an error after a left-out namespace, and (3) rewinds and checks everything
again with nothing left out. A cold one-job check has no entries, plans no skips, and
checks it once. (A warm one-job check with an error already pays twice; that is today's
behaviour.)

**What it costs.** For a project with an error, the failing namespaces' own time, times
three, on one core, after the fill. For an `E-RESOURCE` at the 10-billion-step limit that
is roughly three times five minutes. The diagnostics are still exactly the one-job ones;
the notes on stderr are not (the design said "the same notes as a sequential cold check
prints", which is wrong for a left namespace: my error in §9.2).

**Fix (small, in the CLI and driver).** The fill knows it: `Fill::left > 0`. When it is,
run the last pass with nothing left out (the same switch `Load::Everything` flips), so the
count is two. Getting to one needs the worker's diagnostics, which is the merged-reports
design §9.1 dropped; not worth it in stage 1. Until fixed, the guide's sentence "it prints
exactly what one job prints" should except the notes.

### F2. Ctrl-C loses "while checking X" (low)

**Repro [ran].** The same project, `timeout -s INT 4 stitchwort check --jobs J`:

    --jobs 1:  check stopped early: stopped by SIGINT, while checking Ex.Slow.slow
    --jobs 4:  check stopped early: stopped by SIGINT        (three runs of three)

**Why [read].** `progress::CURRENT` (`crates/elab/src/progress.rs:36`) is one global;
`end` sets it to `None` when any thread finishes any declaration, so a worker finishing a
quick declaration erases the slow one's label. §9.2 said "X is one of the declarations
being checked"; that needs one label per thread (a small map by thread id, reporting any).
The exit path and the cache left behind are fine: the interrupted run left the five clean
namespaces' entries and the library's, all whole.

### F3. `STITCHWORT_JOBS` changes what `--no-cache` means (low)

**[read]** `jobs_asked` takes `STITCHWORT_JOBS` when `--jobs` is absent, and with
`PARALLEL_NO_CACHE` a `check --no-cache` then runs the fill and reports from entries in
memory. So a shell or CI job that exports the variable no longer runs the strict full
check when it says `--no-cache`, with nothing printed to say so (only `--timings` shows the
jobs). The trust paragraph's last sentences are right but leave this to the reader. Add to
`check-cache-trust.md` and to the rolling check's script: **the reference run passes
`--jobs 1` explicitly**. This is part of what D3731 decides, so it belongs in what Matt is
shown.

One more sentence the paragraph should have: under `--no-cache --jobs N` a plain `check`
does not even replay most clean namespaces in the reporting session; it leaves them out on
the strength of the entry's head (`plan_namespace`), as a warm check does. "Replays those
entries trusted" understates it slightly.

Otherwise the paragraph is accurate **[read, ran]**: see "Trust" below.

### F4. A panic in worker 0 dirties the reporting thread (low; never expected)

**[read, argued]** Worker 0 runs on the caller's thread, the thread the last pass then
checks on. `catch_unwind` in `Worker::run` stops a panic there, and the last pass goes on
with whatever the panic left in that thread's thread-locals. Most are restored by drop
guards or reset per declaration (`TREE_MEMO` and `KNOWN_CALLS` empty when the outermost
comparison is dropped; `FAILED_USED` is emptied per component). One is not:
`unify.rs:2862-2864` sets `NO_ETA` and puts it back without a guard, so a panic inside
`first_order`'s argument pairing leaves record eta off for the whole last pass, which
could then elaborate differently from a one-job check. It needs a panic that worker 0 meets
and the last pass doesn't, inside that window, so it is remote; but it is the one way I
found for the fill to change what the last pass computes rather than what it finds in the
store. Cheapest cure: if worker 0 itself panicked, `resume_unwind` after the other workers
have stopped (the run fails as a one-job run meeting that panic would), instead of
carrying on. Worker threads are fine: their thread-locals die with them. The lane's note
that the panic path is untested stands.

## The five questions

### 1. Exactness

**[ran]** A 12-namespace project: a diamond, two errors in independent branches (each with
a namespace above it), an open goal with a namespace above it (`open-goals: warn`), a
syntax error with a namespace above it (so `W-AFTER-SYNTAX-ERROR` cites another
namespace), library files shared by siblings (`List`). For each of: no seed, seeds 1 to 6;
and for the clean six-namespace part: no seed, seeds 7, 11, 12, 13, a `Ex.Top` target, and
`--index`:

- stdout, stderr and exit code of `--jobs 4` equal `--jobs 1`'s, cache on and
  `--no-cache`;
- the cache folder after `--jobs 4` (given the one-job run's `header`, so the salts agree)
  is byte for byte the one-job folder (`diff -r`).

All equal. With `--timings` the fill line read "4 workers: 0 namespaces had entries, 5
filled, 7 left to the check after; 0 dependencies elaborated again, 0 entries refused, 0
late misses", so the fill really ran. The lane's five tests pass (27 s; below).

**[read]** The "written" test (`Worker::job`): `namespace_hits` rises only after a replay
returned `Ok` (`cache/mod.rs:1069`), `namespace_written` only after `store.write`
(`:1168`); both counters are the session's own and the call between the two reads checks
exactly one namespace, whose dependencies are already loaded. `Status::Done` is set in two
places only: the plan's `plan_namespace(..).is_some()` and `Shared::finish` with
`written`. `Board::leave` marks every waiting namespace with a left one in its closure, in
one pass, which is enough because the closure is transitive and order is canonical. A
running namespace can't be above a left one (it was ready, so its direct uses were done,
and done is never undone). One wrinkle, harmless: a replay that reports `E-CACHE-DIGEST`
still counts as a hit, so the namespace would be called done; that error only arises under
`--recheck`, which runs one job.

**Differences that exist:** F1 (note count), F2 (the stop message), `--timings`, and the
panic line the lane lists. Nothing else found.

**The claim table [read, ran].** A read that misses re-reads under the table's lock before
claiming, and the owner writes before releasing, so "no entry and no claim" does mean
nobody is making it. In the run above `std/List/Toolkit.sw` was elaborated by one worker
and replayed by another. Two things the doc comment's "no deadlock" doesn't cover, both
bounded by the 60 s patience and neither changing a result **[argued]**:

- A claim on a file that was elaborated but not written (uncacheable, or failed) lasts to
  the end of the holder's job. If the holder then needs a file another worker is
  elaborating, and that worker needs the unwritten file, each waits for the other until
  one's patience runs out. It needs a library file that checks but can't be stored;
  `Fill::stats.uncacheable` and `claims_gave_up` would show it. Releasing a claim when the
  file's elaboration ends without a write (in `cache_after`'s terms: the store sees no
  write, so this needs a hook, or a `ClaimStore` method called from the driver) closes it.
- A waiter doesn't look at the stop flag; after a panic it waits until the holder's job
  ends, which the cancelled budget makes prompt.

`claims_gave_up` is counted but not printed in the `--timings` line; it should be, since
it is the only sign of either case.

**Cancellation [read].** The stop flag is each worker's budget flag, watched for the whole
fill; a cancelled namespace or library file is not written (`cache/mod.rs:718`, `:1144`).
Only a panic sets it.

### 2. Trust

What `--no-cache --jobs N` admits that `--no-cache --jobs 1` doesn't, as built **[read]**:
the reporting session accepts a namespace (and a library file) on the strength of an entry
another session of the same process wrote, after that session's kernel accepted every
declaration in it. So a fault in encoding or replay (an entry that replays cleanly as
something other than what was checked) is no longer caught by the reporting session
re-checking. Nothing weaker than that: the entries carry this build's stamp and a salt
made for the run, are sealed and opened by the same code as a folder's, and are written
only on the paths that write a folder's.

Each session still elaborates the core itself (the `core` row appears once per session in
`--timings` **[ran]**): the core is never taken from an entry.

Lifetime **[read]**: `MemoryStore` is made in `fill_in_parallel`, held by the main
session's `Rc` and the workers' clones, and is in no static; it ends with the process.
Nothing reaches disk **[ran]**: after `--no-cache --jobs 4` runs the project folders held
only `src` and `stitchwort.yaml` (no `.stitchwort`), and `cache_dir` returns before it
creates anything when `--no-cache` is set.

A small thing: with `--no-cache --jobs N` the memory store is installed in the main
session before the fill decides whether to run, so when it doesn't (a one-namespace
project) the check still encodes entries into memory. Same output; a little wasted work.
Install it only when `fill.ran`.

The trust paragraph: accurate, with the two additions in F3.

### 3. The two departures

**The planning session is the first worker: sound**, apart from F4. **[read]** Its
`plan_namespace` calls leave keys (and digests for found entries) in the session's
`namespace_keys`; a job loads every namespace of the closure it lacks, in canonical order,
before checking, and each load overwrites that namespace's key and digest, so no job's key
is computed from a planned digest of something not loaded. Namespaces that were waiting at
plan time got no usable key (`planning` refuses a dependency without a digest). Sharing
the thread with the reporting session is the same situation as two sessions on one thread
anywhere else (the file-target loop, the tests); `progress::NAMES` is the one table that
carries over, and `refresh` detects another session by its last name (a coincidence there
would misname the definition in a note, nothing more).

**Above an open goal: sound, and the lane's test is the right one.** A namespace with a
goal writes no entry, so the fill leaves it and everything above it; the last pass checks
them as one job does and writes the entries above the goal, keyed to the goal namespace's
text (`namespace_cache_key`'s `text` branch) exactly as a one-job check keys them. In my
run the 4-job folder equalled the one-job folder with the goal present. The design's
"nothing above it has an entry" was wrong for goals; "the folders are equal" is the
correct assertion. The cost is only that the namespaces above a goal are not filled in
parallel.

### 4. Shared state across workers

Besides the store and the claim table **[read: every `static`, `thread_local!` and lazy
`env::var` in core, elab, driver, syntax]**:

- **Process-wide, mutable:** `NodeId`'s counter (`syntax/src/ast.rs:42`), so node ids
  interleave between workers. They are identities, used as keys of two lookup tables
  (`dot_heads`, `dot_failed`), with no order read from them that I found; a cold and a
  warm one-job check already see different ids. `timings`' rows (intended). `progress`'s
  sink (a `fn`, set once) and `CURRENT` (F2). `static_code`'s set of leaked diagnostic
  codes (a mutex; content-keyed). `nav`'s `DOCS`/`IMPORTS` parse caches (mutexes, keyed by
  file index and text, library files only, used for `--index`). `TEMP_FILE` (an atomic
  for temp names). Debug counters (`proof_counts`, `env_metrics`), off unless their
  variable is set.
- **Process-wide, read-only once set:** the library index and std text (`OnceLock`), the
  `LazyLock` names, the fingerprint stamp, the palette, and the env switches read through
  `OnceLock`. Env switches read at each use (`STITCHWORT_CACHE_DEBUG` and the like) are
  only read, and nothing in the process sets a variable.
- **Thread-local:** everything in `core::value`, `core::reference`, `core::budget`,
  `elab::unify`, `elab::module` and `syntax::source`. Per worker for workers 1 and up;
  shared between worker 0 and the last pass (question 3, F4).
- **The stop flag:** one `Arc<AtomicBool>`, each worker's budget flag.
- **Signals:** blocked in `main` before any thread starts, so workers inherit the mask and
  the signal thread still gets them **[ran: Ctrl-C stopped a 4-job run]**.

`BUILD_HASH` and the fingerprints are compile-time constants.

### 5. Load order (the design's not-verified item)

A worker loads each job's missing closure in canonical order, but across jobs its session
is not in canonical order, and library files arrive on demand in whatever order its jobs
need them; so every entry a worker writes rests on I2. **[read]** I found no walk in the
entry writer that the scheduler could reorder, but I did not read the encoder through;
this stays the item the evidence must carry.

What the 20-seed test covers: the pick order, on eight namespaces of one-line `Nat`
definitions with three jobs, comparing folders byte for byte. That exercises scheduling
and key agreement well. It does **not** exercise the places an order dependence would
live: instances declared in sibling namespaces and resolved above them, lifted `match`
helpers, theorems and sealed proofs, namespaces needing different, overlapping library
files (so library load order differs between workers), `+nav` entries. Thread timing adds
variation the seed doesn't control, so a failure may not reproduce from its seed. My 12
seeded runs on a slightly richer project (one shared library file) were equal, which adds
little. Recommend one richer fixture for the seeded test (ticket below); the real evidence
remains Overmind's `--jobs 4` beside `--jobs 1` on std, AoC and `tools/fmt`.

## Checked and sound

- The lane's tests: `package(stitchwort-driver) & binary(projects) & test(/parallel::/)`,
  5 passed, 27 s **[ran once]**.
- `prepare_analysis` / `check_prepared` is a mechanical split of `load_analysis_for`
  **[read the diff]**.
- Scheduler: no lost wake-up (`finish` and the `running == 0` exit both notify; waiters
  re-test under the lock); `workers = min(jobs, lacking)`; nothing filled when fewer than
  two namespaces lack an entry.
- The one-job rules read the same flags the session set-up reads; the `--expand` options
  never had a cache.
- Workers' keys agree with the main session's through the CLI (the last pass replayed
  what the workers wrote: `(cached)` rows, 0 refused, 0 late misses) **[ran]**.
- An interrupted `--jobs 4` run leaves a valid, partly filled cache **[ran]**.

## Not checked

- Anything large: `tools/fmt`, AoC, std; memory at 4 and 8 jobs; the gain. The measure's.
- The panic path (F4 and the lane's note) and the 60 s claim fallback: read, not run.
- `--index` output equality: both runs wrote the same path, so I compared only messages
  and the folder (which holds the `+nav` entries, equal).
- `--counterexamples` with `--jobs`.
- The entry encoder for order-dependent walks (question 5).
- `E-RESOURCE` near the limit (§9.4 item 4): unchanged from the design.
- The doc-link warning case: my fixture's doc comment did not produce one.

## Tickets

1. **F1**: last pass leaves nothing out when the fill left a namespace; guide sentence
   until then. Sonnet, small. Test: a fixture with an error and a counter of how often the
   failing namespace is elaborated (2, not 3).
2. **F2**: `progress::CURRENT` per thread. Small; test with two threads.
3. **F3**: trust paragraph additions; rolling check's reference run passes `--jobs 1`.
   With D3731.
4. **F4**: worker 0's panic is resumed after the fill stops; a guard on `NO_ETA`
   regardless (it is wrong for any caught panic). Plus a test of the panic path, which
   needs a test-only hook.
5. Claims: release on "elaborated, not written"; print `claims_gave_up` in the
   `--timings` line.
6. A richer fixture for the seeded test (instances in siblings, a lifted match, a
   theorem, different library files per branch, one `--index` run).
7. Install the memory store only when the fill ran.
